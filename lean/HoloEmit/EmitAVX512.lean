/-
  HoloEmit/EmitAVX512.lean

  Formal 16-lane `512`-bit `AVX-512` (`F/BW/VL/VPOPCNTDQ`) SIMD target machine semantics
  (`AVX512Insn`, `AVX512State`) and warning-free C11 `<immintrin.h>` intrinsic emitter
  for TigerLake (`i9-11900H`) / SapphireRapids / Zen4+.
-/

import HoloEmit.RegAlloc

namespace HoloEmit

/-- 16-lane 32-bit (`512`-bit `zmm`) vector value. -/
abbrev Vec16U32 := Fin 16 → UInt32

/-- 16-bit AVX-512 opmask register value (`__mmask16` `k1`). -/
abbrev Mask16 := Fin 16 → Bool

/-- Symbolic 16-lane `AVX-512` (`F + VPOPCNTDQ`) instruction set. -/
inductive AVX512Insn where
  | vpbroadcastdImm (dst : PReg) (imm : UInt32)
  | vmovdqa32       (dst src : PReg)
  | vpandd          (dst lhs rhs : PReg)
  | vpord           (dst lhs rhs : PReg)
  | vpxord          (dst lhs rhs : PReg)
  | vpslldImm       (dst src : PReg) (sh : UInt32)
  | vpsrldImm       (dst src : PReg) (sh : UInt32)
  | vpsllvd         (dst lhs rhs : PReg)
  | vpternlogd      (imm8 : UInt8) (dst a b c : PReg)
  | vpopcntd        (dst src : PReg)
  | vpcmpeqdMask    (lhs rhs : PReg)         -- `k1[i] := (lhs[i] == rhs[i])`
  | vptestmdMask    (src : PReg)             -- `k1[i] := (src[i] != 0)`
  | vpblendmd       (dst fVal tVal : PReg)   -- `_mm512_mask_blend_epi32(k1, fVal, tVal)`
  | vpblendmdImm01  (dst : PReg)             -- `_mm512_maskz_set1_epi32(k1, 1)`
  deriving Repr, DecidableEq

/-- 16-lane `AVX-512` architectural state (`zmm0..zmm31` + opmask `k1`). -/
structure AVX512State where
  zmm : PReg → Vec16U32
  k1  : Mask16

def writeZmm (z : PReg → Vec16U32) (r : PReg) (v : Vec16U32) : PReg → Vec16U32 :=
  fun r' => if r' = r then v else z r'

/-- Execute one 16-lane `AVX512Insn`. -/
def execAVX512Insn (insn : AVX512Insn) (st : AVX512State) : AVX512State :=
  match insn with
  | .vpbroadcastdImm dst imm =>
    { st with zmm := writeZmm st.zmm dst (fun _ => imm) }
  | .vmovdqa32 dst src =>
    { st with zmm := writeZmm st.zmm dst (st.zmm src) }
  | .vpandd dst l r =>
    { st with zmm := writeZmm st.zmm dst (fun i => st.zmm l i &&& st.zmm r i) }
  | .vpord dst l r =>
    { st with zmm := writeZmm st.zmm dst (fun i => st.zmm l i ||| st.zmm r i) }
  | .vpxord dst l r =>
    { st with zmm := writeZmm st.zmm dst (fun i => st.zmm l i ^^^ st.zmm r i) }
  | .vpslldImm dst s sh =>
    { st with zmm := writeZmm st.zmm dst (fun i => st.zmm s i <<< (sh &&& 31)) }
  | .vpsrldImm dst s sh =>
    { st with zmm := writeZmm st.zmm dst (fun i => st.zmm s i >>> (sh &&& 31)) }
  | .vpsllvd dst l r =>
    { st with zmm := writeZmm st.zmm dst (fun i => st.zmm l i <<< (st.zmm r i &&& 31)) }
  | .vpternlogd imm8 d a b c =>
    { st with zmm := writeZmm st.zmm d (fun i => evalLop3 imm8 (st.zmm a i) (st.zmm b i) (st.zmm c i)) }
  | .vpopcntd dst s =>
    { st with zmm := writeZmm st.zmm dst (fun i => popc32 (st.zmm s i)) }
  | .vpcmpeqdMask l r =>
    { st with k1 := fun i => u32Eq (st.zmm l i) (st.zmm r i) }
  | .vptestmdMask s =>
    { st with k1 := fun i => u32Ne (st.zmm s i) 0 }
  | .vpblendmd dst f t =>
    { st with zmm := writeZmm st.zmm dst (fun i => if st.k1 i then st.zmm t i else st.zmm f i) }
  | .vpblendmdImm01 dst =>
    { st with zmm := writeZmm st.zmm dst (fun i => if st.k1 i then 1 else 0) }

def execAVX512Insns : List AVX512Insn → AVX512State → AVX512State
  | [], st => st
  | i :: is, st => execAVX512Insns is (execAVX512Insn i st)

/-- Lower a single physical `HoloIR` instruction to 16-lane `AVX512Insn`s. -/
def lowerInsnAVX512 : Insn PReg → List AVX512Insn
  | .constU32 dst imm    => [.vpbroadcastdImm dst imm]
  | .mov dst src         => [.vmovdqa32 dst src]
  | .and32 dst l r       => [.vpandd dst l r]
  | .or32 dst l r        => [.vpord dst l r]
  | .xor32 dst l r       => [.vpxord dst l r]
  | .shlImm dst s sh     => [.vpslldImm dst s (sh &&& 31)]
  | .shrImm dst s sh     => [.vpsrldImm dst s (sh &&& 31)]
  | .shlReg dst l r      => [.vpsllvd dst l r]
  | .lop3 imm8 dst a b c => [.vpternlogd imm8 dst a b c]
  | .popc dst s          => [.vpopcntd dst s]
  | .cmpEq dst l r       => [.vpcmpeqdMask l r, .vpblendmdImm01 dst]
  | .selp dst c t f      => [.vptestmdMask c, .vpblendmd dst f t]

def lowerInsnsAVX512 : List (Insn PReg) → List AVX512Insn
  | [] => []
  | i :: is => lowerInsnAVX512 i ++ lowerInsnsAVX512 is

def bindParamsSIMD : List PReg → List Vec16U32 → (PReg → Vec16U32)
  | [], _ => fun _ _ => 0
  | p :: ps, [] => writeZmm (bindParamsSIMD ps []) p (fun _ => 0)
  | p :: ps, v :: vs => writeZmm (bindParamsSIMD ps vs) p v

def evalAVX512Prog (prog : HoloProg PReg) (vecArgs : List Vec16U32) : Vec16U32 :=
  let st0 : AVX512State := { zmm := bindParamsSIMD prog.params vecArgs, k1 := fun _ => false }
  let stF := execAVX512Insns (lowerInsnsAVX512 prog.body) st0
  stF.zmm prog.retReg

/-! ### Warning-Free C11 `<immintrin.h>` `AVX-512` Function Renderer -/

private def zmmVar (r : PReg) : String := s!"z{r.val}"

def formatAVX512Insn : AVX512Insn → String
  | .vpbroadcastdImm d imm => s!"  {zmmVar d} = _mm512_set1_epi32((int){imm.toNat}u);"
  | .vmovdqa32 d s         => s!"  {zmmVar d} = {zmmVar s};"
  | .vpandd d l r          => s!"  {zmmVar d} = _mm512_and_si512({zmmVar l}, {zmmVar r});"
  | .vpord d l r           => s!"  {zmmVar d} = _mm512_or_si512({zmmVar l}, {zmmVar r});"
  | .vpxord d l r          => s!"  {zmmVar d} = _mm512_xor_si512({zmmVar l}, {zmmVar r});"
  | .vpslldImm d s sh      => s!"  {zmmVar d} = _mm512_slli_epi32({zmmVar s}, {sh.toNat}u);"
  | .vpsrldImm d s sh      => s!"  {zmmVar d} = _mm512_srli_epi32({zmmVar s}, {sh.toNat}u);"
  | .vpsllvd d l r         =>
    s!"  {zmmVar d} = _mm512_sllv_epi32({zmmVar l}, _mm512_and_si512({zmmVar r}, _mm512_set1_epi32(31)));"
  | .vpternlogd imm d a b c =>
    s!"  {zmmVar d} = _mm512_ternarylogic_epi32({zmmVar a}, {zmmVar b}, {zmmVar c}, {imm.toNat});"
  | .vpopcntd d s          => s!"  {zmmVar d} = _mm512_popcnt_epi32({zmmVar s});"
  | .vpcmpeqdMask l r      => s!"  k1 = _mm512_cmpeq_epi32_mask({zmmVar l}, {zmmVar r});"
  | .vptestmdMask s        => s!"  k1 = _mm512_test_epi32_mask({zmmVar s}, {zmmVar s});"
  | .vpblendmd d f t       => s!"  {zmmVar d} = _mm512_mask_blend_epi32(k1, {zmmVar f}, {zmmVar t});"
  | .vpblendmdImm01 d      => s!"  {zmmVar d} = _mm512_maskz_set1_epi32(k1, 1);"

private def renderZmmDeclsAux : Nat → List String
  | 0 => []
  | k + 1 => renderZmmDeclsAux k ++ [s!"  __m512i z{k} = _mm512_setzero_si512();"]

private def renderCParams : Nat → List PReg → List String
  | _, [] => []
  | idx, _ :: ps => s!"__m512i arg_{idx}" :: renderCParams (idx + 1) ps

private def renderCParamBinds : Nat → List PReg → List String
  | _, [] => []
  | idx, p :: ps => s!"  {zmmVar p} = arg_{idx};" :: renderCParamBinds (idx + 1) ps

def renderAVX512Function (fnName : String) (maxRegs : Nat) (prog : HoloProg PReg) : String :=
  let cParams :=
    if prog.params.isEmpty then "void"
    else String.intercalate ", " (renderCParams 0 prog.params)
  let zDecls := renderZmmDeclsAux (min maxRegs 32)
  let pBinds := renderCParamBinds 0 prog.params
  let bodyLines := (lowerInsnsAVX512 prog.body).map formatAVX512Insn
  let suppressUnused :=
    (List.range (min maxRegs 32)).map fun k => s!"  (void)z{k};"
  let lines :=
    [ "__attribute__((target(\"avx512f,avx512bw,avx512vl,avx512vpopcntdq\")))"
    , s!"__m512i {fnName}({cParams}) \{"
    , "  __mmask16 k1 = 0;"
    , "  (void)k1;"
    ] ++ zDecls ++ pBinds ++ bodyLines ++ suppressUnused ++
    [ s!"  return {zmmVar prog.retReg};"
    , "}"
    ]
  String.intercalate "\n" lines

def renderAVX512Header (funcs : List (String × Nat × HoloProg PReg)) : String :=
  let hdr := "#include <immintrin.h>\n#include <stdint.h>\n\n"
  hdr ++ String.intercalate "\n\n" (funcs.map fun (nm, mr, prg) => renderAVX512Function nm mr prg) ++ "\n"

end HoloEmit
