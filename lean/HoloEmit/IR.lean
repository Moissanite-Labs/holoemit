/-
  HoloEmit/IR.lean

  Pure-Init register-parameterized straight-line / predicated SSA Intermediate
  Representation (`HoloIR`) for verified `sm_86` PTX and `AVX-512` micro-kernels.

  Zero Mathlib, zero `Std` tactics, zero `partial def`, zero heap in target IR.
-/

namespace HoloEmit

/-- Unbounded virtual SSA register index (`v0, v1, ...`). -/
abbrev VReg := Nat

/-- Bounded 32-register hardware bank (`%r0..%r31` in `sm_86` PTX, `zmm0..zmm31` in `AVX-512`). -/
abbrev PReg := Fin 32

/-- Dedicated NVIDIA `sm_86` PTX scratch register `%r31` reserved for masked variable shifts
    (`and.b32 %r31, r, 31; shl.b32 d, l, %r31`). General-purpose allocation uses `%r0..%r30`. -/
def ptxScratchReg : PReg := ⟨31, by decide⟩

/-- Constructive (`0`-axiom) equality test on `UInt8` via `Nat.beq`
    (avoids `Classical.choice` in `Init`'s `instBEqOfDecidableEq` on `UInt8`). -/
def u8Eq (x y : UInt8) : Bool :=
  Nat.beq x.toNat y.toNat

/-- Constructive (`0`-axiom) equality & inequality tests on `UInt32` via `Nat.beq`
    (avoids `Classical.choice` in `Init`'s `instBEqOfDecidableEq` on `UInt32`). -/
def u32Eq (x y : UInt32) : Bool :=
  Nat.beq x.toNat y.toNat

def u32Ne (x y : UInt32) : Bool :=
  !Nat.beq x.toNat y.toNat

/-- Exact 1-bit lookup into an 8-bit 3-input Boolean truth table `imm8` at index `(ba<<2)|(bb<<1)|bc`. -/
def evalLutBool (imm8 : UInt8) (ba bb bc : Bool) : Bool :=
  let idx : UInt8 :=
    (if ba then 4 else 0) ||| (if bb then 2 else 0) ||| (if bc then 1 else 0)
  u8Eq ((imm8 >>> idx) &&& 1) 1

/-- All-ones or all-zeros 32-bit mask from a `Bool`. -/
def mintermMask (bit : Bool) : UInt32 :=
  if bit then 0xFFFFFFFF else 0

/-- Exact 32-bit parallel 8-minterm Boolean LUT evaluation matching both NVIDIA `sm_86`
    `lop3.b32 d, a, b, c, imm8` and Intel `AVX-512` `vpternlogd d, a, b, c, imm8`. -/
def evalLop3 (imm8 : UInt8) (a b c : UInt32) : UInt32 :=
  let na := ~~~a
  let nb := ~~~b
  let nc := ~~~c
  (mintermMask (u8Eq ((imm8 >>> 0) &&& 1) 1) &&& na &&& nb &&& nc) |||
  (mintermMask (u8Eq ((imm8 >>> 1) &&& 1) 1) &&& na &&& nb &&& c)  |||
  (mintermMask (u8Eq ((imm8 >>> 2) &&& 1) 1) &&& na &&& b  &&& nc) |||
  (mintermMask (u8Eq ((imm8 >>> 3) &&& 1) 1) &&& na &&& b  &&& c)  |||
  (mintermMask (u8Eq ((imm8 >>> 4) &&& 1) 1) &&& a  &&& nb &&& nc) |||
  (mintermMask (u8Eq ((imm8 >>> 5) &&& 1) 1) &&& a  &&& nb &&& c)  |||
  (mintermMask (u8Eq ((imm8 >>> 6) &&& 1) 1) &&& a  &&& b  &&& nc) |||
  (mintermMask (u8Eq ((imm8 >>> 7) &&& 1) 1) &&& a  &&& b  &&& c)

/-- Count set bits among the lowest `k` bit positions of `x`. -/
def countBitsAux (x : UInt32) : Nat → Nat
  | 0 => 0
  | k + 1 => countBitsAux x k + (if u32Eq ((x >>> k.toUInt32) &&& 1) 1 then 1 else 0)

/-- Exact 32-bit population count (`popc.b32` / `vpopcntd`). -/
def popc32 (x : UInt32) : UInt32 :=
  (countBitsAux x 32).toUInt32

/-- Predicated, branchless scalar/SIMD instruction parameterized over register type `Reg`. -/
inductive Insn (Reg : Type) where
  | constU32 (dst : Reg) (imm : UInt32)
  | mov      (dst src : Reg)
  | and32    (dst lhs rhs : Reg)
  | or32     (dst lhs rhs : Reg)
  | xor32    (dst lhs rhs : Reg)
  | shlImm   (dst src : Reg) (sh : UInt32)
  | shrImm   (dst src : Reg) (sh : UInt32)
  | shlReg   (dst lhs rhs : Reg)
  | lop3     (imm8 : UInt8) (dst a b c : Reg)
  | popc     (dst src : Reg)
  | cmpEq    (dst lhs rhs : Reg)
  | selp     (dst cond tVal fVal : Reg)
  deriving Repr, DecidableEq

/-- Straight-line predicated `HoloIR` kernel with explicit input parameter registers and return register. -/
structure HoloProg (Reg : Type) where
  params : List Reg
  body   : List (Insn Reg)
  retReg : Reg
  deriving Repr, DecidableEq

/-- Destination register written by an instruction. -/
def Insn.defReg : Insn Reg → Reg
  | .constU32 dst _     => dst
  | .mov dst _          => dst
  | .and32 dst _ _      => dst
  | .or32 dst _ _       => dst
  | .xor32 dst _ _      => dst
  | .shlImm dst _ _     => dst
  | .shrImm dst _ _     => dst
  | .shlReg dst _ _     => dst
  | .lop3 _ dst _ _ _   => dst
  | .popc dst _         => dst
  | .cmpEq dst _ _      => dst
  | .selp dst _ _ _     => dst

/-- Source registers read by an instruction. -/
def Insn.usedRegs : Insn Reg → List Reg
  | .constU32 _ _       => []
  | .mov _ s            => [s]
  | .and32 _ l r        => [l, r]
  | .or32 _ l r         => [l, r]
  | .xor32 _ l r        => [l, r]
  | .shlImm _ s _       => [s]
  | .shrImm _ s _       => [s]
  | .shlReg _ l r       => [l, r]
  | .lop3 _ _ a b c     => [a, b, c]
  | .popc _ s           => [s]
  | .cmpEq _ l r        => [l, r]
  | .selp _ c t f       => [c, t, f]

/-- Pure functional register update `st[r := v]` using decidable equality (`0` `Classical.choice`). -/
def writeReg {Reg : Type} [DecidableEq Reg] (st : Reg → UInt32) (r : Reg) (v : UInt32) : Reg → UInt32 :=
  fun r' => if r' = r then v else st r'

/-- Pure expression evaluation of the RHS of `insn` in register state `st`. -/
def evalInsnRhs {Reg : Type} (insn : Insn Reg) (st : Reg → UInt32) : UInt32 :=
  match insn with
  | .constU32 _ imm     => imm
  | .mov _ s            => st s
  | .and32 _ l r        => st l &&& st r
  | .or32 _ l r         => st l ||| st r
  | .xor32 _ l r        => st l ^^^ st r
  | .shlImm _ s sh      => st s <<< (sh &&& 31)
  | .shrImm _ s sh      => st s >>> (sh &&& 31)
  | .shlReg _ l r       => st l <<< (st r &&& 31)
  | .lop3 imm8 _ a b c  => evalLop3 imm8 (st a) (st b) (st c)
  | .popc _ s           => popc32 (st s)
  | .cmpEq _ l r        => if u32Eq (st l) (st r) then 1 else 0
  | .selp _ c t f       => if u32Ne (st c) 0 then st t else st f

/-- Small-step semantics of one `HoloIR` instruction. -/
def evalInsn {Reg : Type} [DecidableEq Reg] (insn : Insn Reg) (st : Reg → UInt32) : Reg → UInt32 :=
  writeReg st insn.defReg (evalInsnRhs insn st)

/-- Sequential execution of a list of `HoloIR` instructions. -/
def evalInsns {Reg : Type} [DecidableEq Reg] : List (Insn Reg) → (Reg → UInt32) → (Reg → UInt32)
  | [], st => st
  | i :: is, st => evalInsns is (evalInsn i st)

/-- Bind argument values left-to-right onto `params` starting from the zero register state. -/
def bindParams {Reg : Type} [DecidableEq Reg] : List Reg → List UInt32 → (Reg → UInt32)
  | [], _ => fun _ => 0
  | p :: ps, [] => writeReg (bindParams ps []) p 0
  | p :: ps, v :: vs => writeReg (bindParams ps vs) p v

/-- End-to-end execution of a `HoloProg` on `args`. -/
def evalProg {Reg : Type} [DecidableEq Reg] (prog : HoloProg Reg) (args : List UInt32) : UInt32 :=
  let st0 := bindParams prog.params args
  let stF := evalInsns prog.body st0
  stF prog.retReg

/-! ### Canonical `[16, 11, 4]` `A_16` Extended Hamming SECDED Specifications & `HoloIR` Programs -/

/-- Pure reference spec for `razor_a16_folded_upper_parity` per-lane bit (`(w>>1)^(w>>2)^(w>>3)` & 1). -/
def foldedUpperParitySpec (w : UInt32) : UInt32 :=
  (((w >>> 1) ^^^ (w >>> 2) ^^^ (w >>> 3)) &&& 1)

/-- Pure reference spec for `razor_a16_secded_syndrome` (compatible with `Moissanite-Labs/holosphere` `include/razor_abi_4byte_sys.h:177-212`). -/
def a16SyndromeSpec (w16 : UInt32) : UInt32 :=
  let p0 := popc32 (w16 &&& 0xFFFF) &&& 1
  let p1 := popc32 (w16 &&& 0xAAAA) &&& 1
  let p2 := popc32 (w16 &&& 0xCCCC) &&& 1
  let p3 := popc32 (w16 &&& 0xF0F0) &&& 1
  let p4 := popc32 (w16 &&& 0xFF00) &&& 1
  p0 ||| (p1 <<< 1) ||| (p2 <<< 2) ||| (p3 <<< 3) ||| (p4 <<< 4)

/-- The 11 data-bit positions `{3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15}` of `[16, 11, 4]` Block-H4.
    Each generator word `a16GenWord r` has its single data bit set plus exact parity bits at `{0,1,2,4,8}`
    so that `a16SyndromeSpec (a16GenWord r) == 0`. -/
def a16BasisWord (dPos : UInt32) : UInt32 :=
  let dBit : UInt32 := (1 : UInt32) <<< dPos
  let p1 : UInt32 := if u32Ne (dPos &&& 1) 0 then 2 else 0
  let p2 : UInt32 := if u32Ne (dPos &&& 2) 0 then 4 else 0
  let p3 : UInt32 := if u32Ne (dPos &&& 4) 0 then 16 else 0
  let p4 : UInt32 := if u32Ne (dPos &&& 8) 0 then 256 else 0
  let core : UInt32 := dBit ^^^ p1 ^^^ p2 ^^^ p3 ^^^ p4
  let p0 : UInt32 := popc32 core &&& 1
  core ^^^ p0

/-- Systematic `[16, 11, 4]` `A_16` Extended Hamming encoder mapping an 11-bit message `msg`
    (`bits 0..10`) to its 16-bit SECDED codeword in `GF(2)^16`. -/
def encodeA16 (msg : UInt32) : UInt32 :=
  let g0  := if u32Eq ((msg >>> 0)  &&& 1) 1 then a16BasisWord 3  else 0
  let g1  := if u32Eq ((msg >>> 1)  &&& 1) 1 then a16BasisWord 5  else 0
  let g2  := if u32Eq ((msg >>> 2)  &&& 1) 1 then a16BasisWord 6  else 0
  let g3  := if u32Eq ((msg >>> 3)  &&& 1) 1 then a16BasisWord 7  else 0
  let g4  := if u32Eq ((msg >>> 4)  &&& 1) 1 then a16BasisWord 9  else 0
  let g5  := if u32Eq ((msg >>> 5)  &&& 1) 1 then a16BasisWord 10 else 0
  let g6  := if u32Eq ((msg >>> 6)  &&& 1) 1 then a16BasisWord 11 else 0
  let g7  := if u32Eq ((msg >>> 7)  &&& 1) 1 then a16BasisWord 12 else 0
  let g8  := if u32Eq ((msg >>> 8)  &&& 1) 1 then a16BasisWord 13 else 0
  let g9  := if u32Eq ((msg >>> 9)  &&& 1) 1 then a16BasisWord 14 else 0
  let g10 := if u32Eq ((msg >>> 10) &&& 1) 1 then a16BasisWord 15 else 0
  g0 ^^^ g1 ^^^ g2 ^^^ g3 ^^^ g4 ^^^ g5 ^^^ g6 ^^^ g7 ^^^ g8 ^^^ g9 ^^^ g10

/-- `HoloIR` kernel 1: Upper-bit folded parity `((w>>1) ^ (w>>2) ^ (w>>3)) & 1` via 1-insn `lop3 0x96`. -/
def a16FoldedParityIR : HoloProg VReg where
  params := [0]
  body := [
    .shrImm 1 0 1,
    .shrImm 2 0 2,
    .shrImm 3 0 3,
    .lop3 0x96 4 1 2 3,
    .constU32 5 1,
    .and32 6 4 5
  ]
  retReg := 6

/-- `HoloIR` kernel 2: `[16, 11, 4]` `A_16` 5-bit syndrome (`razor_a16_secded_syndrome`). -/
def a16SyndromeIR : HoloProg VReg where
  params := [0]
  body := [
    .constU32 1 1,
    .constU32 2 0xFFFF,
    .and32 3 0 2,
    .popc 4 3,
    .and32 5 4 1,           -- v5 = p0
    .constU32 6 0xAAAA,
    .and32 7 0 6,
    .popc 8 7,
    .and32 9 8 1,
    .shlImm 10 9 1,
    .or32 11 5 10,          -- v11 = p0 | (p1 << 1)
    .constU32 12 0xCCCC,
    .and32 13 0 12,
    .popc 14 13,
    .and32 15 14 1,
    .shlImm 16 15 2,
    .or32 17 11 16,         -- v17 = p0 | (p1 << 1) | (p2 << 2)
    .constU32 18 0xF0F0,
    .and32 19 0 18,
    .popc 20 19,
    .and32 21 20 1,
    .shlImm 22 21 3,
    .or32 23 17 22,         -- v23 = ... | (p3 << 3)
    .constU32 24 0xFF00,
    .and32 25 0 24,
    .popc 26 25,
    .and32 27 26 1,
    .shlImm 28 27 4,
    .or32 29 23 28          -- v29 = synd
  ]
  retReg := 29

/-- `HoloIR` kernel 3: Branchless `[16, 11, 4]` `A_16` SECDED syndrome + 1-bit heal + 2-bit DED flag.
    Input `v0 = w16` (`16`-bit received word in low 16 bits).
    Output `UInt32` packs `(isDed << 17) | (isSec << 16) | healed_w16`:
    - Clean (`synd == 0`):             `isDed = 0, isSec = 0, healed = w16 & 0xFFFF`
    - 1-bit error (`(synd & 1) == 1`): `isDed = 0, isSec = 1, healed = (w16 ^ (1 << ((synd>>1)&0xF))) & 0xFFFF`
    - 2-bit error (`synd != 0` even):  `isDed = 1, isSec = 0, healed = w16 & 0xFFFF` (zero miscorrection!) -/
def a16SecdedHealIR : HoloProg VReg where
  params := [0]
  body := a16SyndromeIR.body ++ [
    .constU32 30 0xFFFF,
    .and32 31 0 30,         -- v31 = w16_clean = w16 & 0xFFFF
    .and32 32 29 1,         -- v32 = isSec = synd & 1
    .shrImm 33 29 1,
    .constU32 34 0xF,
    .and32 35 33 34,        -- v35 = errIdx = (synd >> 1) & 0xF
    .shlReg 36 1 35,        -- v36 = 1 << errIdx
    .xor32 37 31 36,        -- v37 = flipped candidate
    .selp 38 32 37 31,      -- v38 = healed = if isSec != 0 then flipped else w16_clean
    .constU32 39 0,
    .cmpEq 40 29 39,        -- v40 = (synd == 0)
    .xor32 41 40 1,         -- v41 = (synd != 0)
    .xor32 42 32 1,         -- v42 = !isSec
    .and32 43 41 42,        -- v43 = isDed = (synd != 0) & (!isSec)
    .shlImm 44 32 16,       -- v44 = isSec << 16
    .shlImm 45 43 17,       -- v45 = isDed << 17
    .or32 46 38 44,
    .or32 47 46 45          -- v47 = (isDed << 17) | (isSec << 16) | healed
  ]
  retReg := 47

end HoloEmit
