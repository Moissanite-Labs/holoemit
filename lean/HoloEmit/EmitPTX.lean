/-
  HoloEmit/EmitPTX.lean

  Formal `sm_86` PTX 7.5 target machine semantics (`PTXInsn`, `PTXState`) and
  textual `.visible .entry` PTX emitter (`renderPTXModule`) directly assemblable
  offline by `ptxas -arch=sm_86 -v` with `0 B` stack frame and `0 B` spill.
  `%r31` (`ptxScratchReg`) is explicitly modeled as scratch in `shlB32Reg`, and
  all non-parameter general-purpose registers `%r0..%r30` are zero-initialized at entry.
-/

import HoloEmit.RegAlloc

namespace HoloEmit

/-- Symbolic NVIDIA `sm_86` PTX scalar + predicate instruction set. -/
inductive PTXInsn where
  | movU32Imm (dst : PReg) (imm : UInt32)
  | movU32    (dst src : PReg)
  | andB32    (dst lhs rhs : PReg)
  | orB32     (dst lhs rhs : PReg)
  | xorB32    (dst lhs rhs : PReg)
  | shlB32Imm (dst src : PReg) (sh : UInt32)
  | shrU32Imm (dst src : PReg) (sh : UInt32)
  | shlB32Reg (dst lhs rhs : PReg)
  | lop3B32   (imm8 : UInt8) (dst a b c : PReg)
  | popcB32   (dst src : PReg)
  | setpEqU32 (lhs rhs : PReg)        -- sets `%p0 := (lhs == rhs)`
  | setpNeU32 (src : PReg) (imm : UInt32) -- sets `%p0 := (src != imm)`
  | selpB32   (dst tVal fVal : PReg)  -- `dst := if %p0 then tVal else fVal`
  | selpB32Imm (dst : PReg) (tImm fImm : UInt32) -- `dst := if %p0 then tImm else fImm`
  deriving Repr, DecidableEq

/-- `sm_86` PTX thread register + predicate `%p0` machine state. -/
structure PTXState where
  regs : PReg → UInt32
  p0   : Bool
  deriving Inhabited

/-- Execute one `PTXInsn` on `PTXState`. -/
def execPTXInsn (insn : PTXInsn) (st : PTXState) : PTXState :=
  match insn with
  | .movU32Imm dst imm   => { st with regs := writeReg st.regs dst imm }
  | .movU32 dst src      => { st with regs := writeReg st.regs dst (st.regs src) }
  | .andB32 dst l r      => { st with regs := writeReg st.regs dst (st.regs l &&& st.regs r) }
  | .orB32 dst l r       => { st with regs := writeReg st.regs dst (st.regs l ||| st.regs r) }
  | .xorB32 dst l r      => { st with regs := writeReg st.regs dst (st.regs l ^^^ st.regs r) }
  | .shlB32Imm dst s sh  => { st with regs := writeReg st.regs dst (st.regs s <<< (sh &&& 31)) }
  | .shrU32Imm dst s sh  => { st with regs := writeReg st.regs dst (st.regs s >>> (sh &&& 31)) }
  | .shlB32Reg dst l r   =>
    let regs1 := writeReg st.regs ptxScratchReg (st.regs r &&& 31)
    { st with regs := writeReg regs1 dst (regs1 l <<< regs1 ptxScratchReg) }
  | .lop3B32 imm8 d a b c=> { st with regs := writeReg st.regs d (evalLop3 imm8 (st.regs a) (st.regs b) (st.regs c)) }
  | .popcB32 dst s       => { st with regs := writeReg st.regs dst (popc32 (st.regs s)) }
  | .setpEqU32 l r       => { st with p0 := u32Eq (st.regs l) (st.regs r) }
  | .setpNeU32 s imm     => { st with p0 := u32Ne (st.regs s) imm }
  | .selpB32 dst t f     => { st with regs := writeReg st.regs dst (if st.p0 then st.regs t else st.regs f) }
  | .selpB32Imm dst t f  => { st with regs := writeReg st.regs dst (if st.p0 then t else f) }

def execPTXInsns : List PTXInsn → PTXState → PTXState
  | [], st => st
  | i :: is, st => execPTXInsns is (execPTXInsn i st)

/-- Lower a single physical `HoloIR` instruction to `PTXInsn`s. -/
def lowerInsnPTX : Insn PReg → List PTXInsn
  | .constU32 dst imm    => [.movU32Imm dst imm]
  | .mov dst src         => [.movU32 dst src]
  | .and32 dst l r       => [.andB32 dst l r]
  | .or32 dst l r        => [.orB32 dst l r]
  | .xor32 dst l r       => [.xorB32 dst l r]
  | .shlImm dst s sh     => [.shlB32Imm dst s (sh &&& 31)]
  | .shrImm dst s sh     => [.shrU32Imm dst s (sh &&& 31)]
  | .shlReg dst l r      => [.shlB32Reg dst l r]
  | .lop3 imm8 dst a b c => [.lop3B32 imm8 dst a b c]
  | .popc dst s          => [.popcB32 dst s]
  | .cmpEq dst l r       => [.setpEqU32 l r, .selpB32Imm dst 1 0]
  | .selp dst c t f      => [.setpNeU32 c 0, .selpB32 dst t f]

def lowerInsnsPTX : List (Insn PReg) → List PTXInsn
  | [] => []
  | i :: is => lowerInsnPTX i ++ lowerInsnsPTX is

def evalPTXProg (prog : HoloProg PReg) (args : List UInt32) : UInt32 :=
  let st0 : PTXState := { regs := bindParams prog.params args, p0 := false }
  let stF := execPTXInsns (lowerInsnsPTX prog.body) st0
  stF.regs prog.retReg

/-! ### Syntactically Valid `sm_86` PTX 7.5 Text Renderer -/

private def ptxReg (r : PReg) : String := s!"%r{r.val}"

def formatPTXInsn : PTXInsn → String
  | .movU32Imm d imm   => s!"  mov.u32 {ptxReg d}, {imm.toNat};"
  | .movU32 d s        => s!"  mov.u32 {ptxReg d}, {ptxReg s};"
  | .andB32 d l r      => s!"  and.b32 {ptxReg d}, {ptxReg l}, {ptxReg r};"
  | .orB32 d l r       => s!"  or.b32 {ptxReg d}, {ptxReg l}, {ptxReg r};"
  | .xorB32 d l r      => s!"  xor.b32 {ptxReg d}, {ptxReg l}, {ptxReg r};"
  | .shlB32Imm d s sh  => s!"  shl.b32 {ptxReg d}, {ptxReg s}, {sh.toNat};"
  | .shrU32Imm d s sh  => s!"  shr.u32 {ptxReg d}, {ptxReg s}, {sh.toNat};"
  | .shlB32Reg d l r   => s!"  and.b32 %r31, {ptxReg r}, 31;\n  shl.b32 {ptxReg d}, {ptxReg l}, %r31;"
  | .lop3B32 imm d a b c => s!"  lop3.b32 {ptxReg d}, {ptxReg a}, {ptxReg b}, {ptxReg c}, {imm.toNat};"
  | .popcB32 d s       => s!"  popc.b32 {ptxReg d}, {ptxReg s};"
  | .setpEqU32 l r     => s!"  setp.eq.u32 %p0, {ptxReg l}, {ptxReg r};"
  | .setpNeU32 s imm   => s!"  setp.ne.u32 %p0, {ptxReg s}, {imm.toNat};"
  | .selpB32 d t f     => s!"  selp.b32 {ptxReg d}, {ptxReg t}, {ptxReg f}, %p0;"
  | .selpB32Imm d t f  => s!"  selp.b32 {ptxReg d}, {t.toNat}, {f.toNat}, %p0;"

private def renderParamDecl : Nat → List PReg → List String
  | _, [] => []
  | idx, _ :: ps => s!".param .b32 param_{idx}" :: renderParamDecl (idx + 1) ps

private def renderParamLoads : Nat → List PReg → List String
  | _, [] => []
  | idx, p :: ps => s!"  ld.param.u32 {ptxReg p}, [param_{idx}];" :: renderParamLoads (idx + 1) ps

/-- Render a complete standalone PTX 7.5 (`sm_86`) `.visible .entry` kernel
    so `ptxas -arch=sm_86 -v` compiles directly to `sm_86` SASS and reports exact hardware
    register count, `0 bytes stack frame`, and `0 bytes spill stores/loads`! -/
def renderPTXFunction (fnName : String) (prog : HoloProg PReg) : String :=
  let extraParams := renderParamDecl 0 prog.params
  let allDecls := String.intercalate ", " (".param .u64 out_ptr" :: extraParams)
  let zeroInits :=
    ((List.range 31).filter (fun k => !prog.params.any (fun p => Nat.beq p.val k))).map
      fun k => s!"  mov.u32 %r{k}, 0;"
  let paramLoads := renderParamLoads 0 prog.params
  let bodyLines := (lowerInsnsPTX prog.body).map formatPTXInsn
  let allLines :=
    [ s!".visible .entry {fnName}({allDecls}) \{"
    , "  .reg .b32 %r<32>;"
    , "  .reg .b64 %rd<1>;"
    , "  .reg .pred %p<1>;"
    , "  ld.param.u64 %rd0, [out_ptr];"
    ] ++ zeroInits ++ paramLoads ++ bodyLines ++
    [ s!"  st.global.u32 [%rd0], {ptxReg prog.retReg};"
    , "  ret;"
    , "}"
    ]
  String.intercalate "\n" allLines

def renderPTXModule (funcs : List (String × HoloProg PReg)) : String :=
  let hdr := ".version 7.5\n.target sm_86\n.address_size 64\n\n"
  hdr ++ String.intercalate "\n\n" (funcs.map fun (nm, prg) => renderPTXFunction nm prg) ++ "\n"

end HoloEmit
