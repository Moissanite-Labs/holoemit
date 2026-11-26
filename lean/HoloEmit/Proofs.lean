/-
  HoloEmit/Proofs.lean

  Pure-Init kernel-checked compiler & SECDED soundness proofs (`Lean 4.36.0`):
  - ZERO `Classical.choice` (`if h : ...` & structural `match`, `0` `by_cases` / `grind` / `beq_false_of_ne`)
  - ZERO `bv_decide` (`0` `_native.bv_decide.ax_*` native LRAT axioms!)
  - ZERO `native_decide` (`0` `Lean.ofReduceBool`)
  - ZERO `sorryAx` and ZERO custom axioms!
-/

import HoloEmit.IR
import HoloEmit.RegAlloc
import HoloEmit.EmitPTX
import HoloEmit.EmitAVX512

namespace HoloEmit

/-! ## 1. Exact 3-Input Boolean LUT (`lop3.b32` & `vpternlogd`) Soundness (`0` `bv_decide`) -/

private theorem bv32_allOnes_lsb : ∀ i : Fin 32, (BitVec.allOnes 32).getLsbD i.val = true := by
  decide

private theorem bv32_not_lsb (x : BitVec 32) (i : Nat) (hi : i < 32) :
    (~~~x).getLsbD i = !x.getLsbD i := by
  rw [BitVec.not_def, BitVec.getLsbD_xor, bv32_allOnes_lsb ⟨i, hi⟩]
  cases x.getLsbD i <;> rfl

private theorem mintermMask_getLsbD (bit : Bool) (i : Nat) (hi : i < 32) :
    (mintermMask bit).toBitVec.getLsbD i = bit := by
  cases bit
  · change (0 : BitVec 32).getLsbD i = false
    exact BitVec.getLsbD_zero
  · change (BitVec.ofNat 32 0xFFFFFFFF).getLsbD i = true
    have hall : BitVec.ofNat 32 0xFFFFFFFF = BitVec.allOnes 32 := by decide
    rw [hall]
    exact bv32_allOnes_lsb ⟨i, hi⟩

/-- Every 8-bit `imm8` opcode of the 8-minterm `evalLop3` silicon MUX matches per-bit `evalLutBool`
    across all 32 bit-lanes `i < 32` for ALL `a, b, c : UInt32`. -/
theorem evalLop3_getLsbD_eq_lutBool (imm8 : UInt8) (a b c : UInt32) (i : Nat) (hi : i < 32) :
    (evalLop3 imm8 a b c).toBitVec.getLsbD i =
      evalLutBool imm8 (a.toBitVec.getLsbD i) (b.toBitVec.getLsbD i) (c.toBitVec.getLsbD i) := by
  unfold evalLop3 evalLutBool
  change (_ : BitVec 32).getLsbD i = _
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_and, UInt32.toBitVec_not,
    BitVec.getLsbD_or, BitVec.getLsbD_and, bv32_not_lsb _ i hi,
    mintermMask_getLsbD _ i hi]
  cases ha : a.toBitVec.getLsbD i <;>
  cases hb : b.toBitVec.getLsbD i <;>
  cases hc : c.toBitVec.getLsbD i <;>
  simp only [Bool.not_false, Bool.not_true, Bool.and_true, Bool.and_false,
    Bool.or_false, Bool.false_or] <;>
  rfl

/-- Boolean truth-table identity: `0x96` (`0b10010110`) is exact 3-input XOR. -/
theorem evalLutBool_0x96_eq_xor (ba bb bc : Bool) :
    evalLutBool 0x96 ba bb bc = Bool.xor (Bool.xor ba bb) bc := by
  cases ba <;> cases bb <;> cases bc <;> rfl

/-- **THEOREM (`sm_86` `lop3.b32` `0x96` == Exact 32-Bit 3-Input XOR)**:
    Holds universally over all $2^{96}$ triples `(a, b, c) : UInt32³` with `0` `bv_decide`! -/
theorem lop3_0x96_exact (a b c : UInt32) :
    evalLop3 0x96 a b c = a ^^^ b ^^^ c := by
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [evalLop3_getLsbD_eq_lutBool 0x96 a b c i hi, evalLutBool_0x96_eq_xor]
  simp only [UInt32.toBitVec_xor, BitVec.getLsbD_xor]

/-- **THEOREM (`AVX-512` `vpternlogd` `0x96` == Exact 16-Lane 512-Bit 3-Input XOR)**:
    Holds universally across all 16 SIMD lanes and all `512`-bit vectors! -/
theorem vpternlogd_0x96_exact (za zb zc : Vec16U32) (lane : Fin 16) :
    evalLop3 0x96 (za lane) (zb lane) (zc lane) = za lane ^^^ zb lane ^^^ zc lane :=
  lop3_0x96_exact (za lane) (zb lane) (zc lane)

/-- **THEOREM (`lop3.b32` / `vpternlogd` `0xE8` == Exact 32-Bit 3-Input Majority)**:
    `(a & b) | (a & c) | (b & c)` in one single LUT instruction (`0` `bv_decide`)! -/
theorem lop3_0xE8_majority_exact (a b c : UInt32) :
    evalLop3 0xE8 a b c = (a &&& b) ||| (a &&& c) ||| (b &&& c) := by
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [evalLop3_getLsbD_eq_lutBool 0xE8 a b c i hi]
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_and, BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases c.toBitVec.getLsbD i <;> rfl

/-- **THEOREM (`lop3.b32` / `vpternlogd` `0xCA` == Exact 32-Bit Bitwise Multiplexer)**:
    `(a & b) | (~a & c)` in one single LUT instruction (`0` `bv_decide`)! -/
theorem lop3_0xCA_mux_exact (a b c : UInt32) :
    evalLop3 0xCA a b c = (a &&& b) ||| (~~~a &&& c) := by
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [evalLop3_getLsbD_eq_lutBool 0xCA a b c i hi]
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_and, UInt32.toBitVec_not,
    BitVec.getLsbD_or, BitVec.getLsbD_and, bv32_not_lsb _ i hi]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases c.toBitVec.getLsbD i <;> rfl

/-! ## 2. Fail-Closed Zero-Spill Register Allocator Certificate Soundness (`checkValidAlloc_sound`) -/

/-- State agreement invariant: every virtual register `v ∈ live` is mapped in `m` to `pv`
    and `stPhys pv = stVirt v`. -/
def AgreeOn (m : AllocMap) (live : List VReg) (stVirt : VReg → UInt32) (stPhys : PReg → UInt32) : Prop :=
  ∀ v, v ∈ live → ∃ pv, m.lookup v = some pv ∧ stPhys pv = stVirt v

private theorem nat_beq_true_iff : ∀ a b : Nat, Nat.beq a b = true ↔ a = b
  | 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | 0, _ + 1 => ⟨fun h => Bool.noConfusion h, fun h => Nat.noConfusion h⟩
  | _ + 1, 0 => ⟨fun h => Bool.noConfusion h, fun h => Nat.noConfusion h⟩
  | a + 1, b + 1 =>
    ⟨fun h => congrArg Nat.succ ((nat_beq_true_iff a b).mp h),
     fun h => (nat_beq_true_iff a b).mpr (Nat.succ.inj h)⟩

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd ((nat_beq_true_iff a b).mp hb) h

private theorem containsVReg_iff (v : VReg) (live : List VReg) :
    containsVReg v live = true ↔ v ∈ live := by
  induction live with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
  | cons x xs ih =>
    unfold containsVReg
    rw [Bool.or_eq_true, nat_beq_true_iff, ih]
    constructor
    · rintro (rfl | h)
      · exact .head _
      · exact .tail _ h
    · intro h
      cases h with
      | head => exact Or.inl rfl
      | tail _ hxs => exact Or.inr hxs

private theorem mem_insertLive {x v : VReg} {live : List VReg} :
    x ∈ insertLive v live ↔ x = v ∨ x ∈ live := by
  unfold insertLive
  cases hc : containsVReg v live
  · simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h
      cases h with
      | head => exact Or.inl rfl
      | tail _ hxs => exact Or.inr hxs
    · rintro (rfl | hxs)
      · exact .head _
      · exact .tail _ hxs
  · simp only [↓reduceIte]
    have hv : v ∈ live := (containsVReg_iff v live).mp hc
    constructor
    · intro hx; exact Or.inr hx
    · intro hor
      cases hor with
      | inl heq => rw [heq]; exact hv
      | inr hx => exact hx

private theorem subset_insertManyLive (us live : List VReg) :
    (∀ u, u ∈ us → u ∈ insertManyLive us live) ∧
    (∀ v, v ∈ live → v ∈ insertManyLive us live) := by
  induction us with
  | nil =>
    constructor
    · intro _ h; cases h
    · intro _ h; exact h
  | cons a rest ih =>
    simp only [insertManyLive]
    refine ⟨?_, ?_⟩
    · intro u hu
      cases hu with
      | head => exact (mem_insertLive).mpr (Or.inl rfl)
      | tail _ hmem => exact (mem_insertLive).mpr (Or.inr (ih.1 u hmem))
    · intro v hv
      exact (mem_insertLive).mpr (Or.inr (ih.2 v hv))

private theorem mem_eraseLive_of_ne {v d : VReg} {live : List VReg}
    (hv : v ∈ live) (hne : v ≠ d) : v ∈ eraseLive d live := by
  induction live with
  | nil => cases hv
  | cons x xs ih =>
    unfold eraseLive
    cases hxd : Nat.beq x d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hv with
      | head => exact List.Mem.head _
      | tail _ hxs => exact List.Mem.tail _ (ih hxs)
    · simp only [↓reduceIte]
      have heq : x = d := (nat_beq_true_iff x d).mp hxd
      cases hv with
      | head => exact absurd heq hne
      | tail _ hxs => exact ih hxs

private theorem checkNonInterfere_spec {m : AllocMap} {d : VReg} {pd : PReg} {live : List VReg}
    (hc : checkNonInterfere m d pd live = true) :
    ∀ v, v ∈ live → v ≠ d → ∀ pv, m.lookup v = some pv → pv ≠ pd := by
  induction live with
  | nil => intro _ h; cases h
  | cons x xs ih =>
    unfold checkNonInterfere at hc
    rw [Bool.and_eq_true] at hc
    intro v hv hne pv hpv
    cases hv with
    | head =>
      have hhead := hc.1
      rw [nat_beq_false_of_ne hne] at hhead
      simp only [Bool.false_eq_true, ↓reduceIte] at hhead
      rw [hpv] at hhead
      intro hpeq
      rw [hpeq] at hhead
      dsimp only at hhead
      have hrefl : Nat.beq pd.val pd.val = true := (nat_beq_true_iff pd.val pd.val).mpr rfl
      rw [hrefl] at hhead
      cases hhead
    | tail _ hxs =>
      exact ih hc.2 v hxs hne pv hpv

private theorem applyAllocInsn_eval_eq {m : AllocMap} {i : Insn VReg} {pi : Insn PReg}
    {stVirt : VReg → UInt32} {stPhys : PReg → UInt32}
    (happ : applyAllocInsn m i = some pi)
    (hused : ∀ u, u ∈ i.usedRegs → ∃ pu, m.lookup u = some pu ∧ stPhys pu = stVirt u) :
    m.lookup i.defReg = some pi.defReg ∧ evalInsnRhs pi stPhys = evalInsnRhs i stVirt := by
  have getU : ∀ u, u ∈ i.usedRegs → ∀ pu, m.lookup u = some pu → stPhys pu = stVirt u := by
    intro u hu pu hpu
    rcases hused u hu with ⟨pu', hpu', heq⟩
    rw [hpu] at hpu'
    injection hpu' with hsame
    rw [hsame]; exact heq
  cases i with
  | constU32 dst imm =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> rw [hd] at happ <;> try contradiction
    rename_i pd; injection happ with hpi; rw [← hpi]
    exact ⟨hd, rfl⟩
  | mov dst s =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hs : m.lookup s <;> rw [hd, hs] at happ <;> try contradiction
    rename_i pd ps; injection happ with hpi; rw [← hpi]
    exact ⟨hd, getU s (.head _) ps hs⟩
  | and32 dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU l (.head _) pl hl, getU r (.tail _ (.head _)) pr hr]
  | or32 dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU l (.head _) pl hl, getU r (.tail _ (.head _)) pr hr]
  | xor32 dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU l (.head _) pl hl, getU r (.tail _ (.head _)) pr hr]
  | shlImm dst s sh =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hs : m.lookup s <;> rw [hd, hs] at happ <;> try contradiction
    rename_i pd ps; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU s (.head _) ps hs]
  | shrImm dst s sh =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hs : m.lookup s <;> rw [hd, hs] at happ <;> try contradiction
    rename_i pd ps; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU s (.head _) ps hs]
  | shlReg dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU l (.head _) pl hl, getU r (.tail _ (.head _)) pr hr]
  | lop3 imm8 dst a b c =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases ha : m.lookup a <;> cases hb : m.lookup b <;> cases hc : m.lookup c <;>
      rw [hd, ha, hb, hc] at happ <;> try contradiction
    rename_i pd pa pb pc; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU a (.head _) pa ha, getU b (.tail _ (.head _)) pb hb,
      getU c (.tail _ (.tail _ (.head _))) pc hc]
  | popc dst s =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hs : m.lookup s <;> rw [hd, hs] at happ <;> try contradiction
    rename_i pd ps; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU s (.head _) ps hs]
  | cmpEq dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU l (.head _) pl hl, getU r (.tail _ (.head _)) pr hr]
  | selp dst c t f =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hc : m.lookup c <;> cases ht : m.lookup t <;> cases hf : m.lookup f <;>
      rw [hd, hc, ht, hf] at happ <;> try contradiction
    rename_i pd pc pt pf; injection happ with hpi; rw [← hpi]
    refine ⟨hd, ?_⟩
    simp only [evalInsnRhs, getU c (.head _) pc hc, getU t (.tail _ (.head _)) pt ht,
      getU f (.tail _ (.tail _ (.head _))) pf hf]

private theorem step_agree_sound {m : AllocMap} {i : Insn VReg} {liveAfter : List VReg}
    {stVirt : VReg → UInt32} {stPhys : PReg → UInt32}
    {pi : Insn PReg} {pd : PReg}
    (happ : applyAllocInsn m i = some pi)
    (hpd : m.lookup i.defReg = some pd)
    (hni : checkNonInterfere m i.defReg pd liveAfter = true)
    (hagree : AgreeOn m (liveBeforeInsn i liveAfter) stVirt stPhys) :
    AgreeOn m liveAfter (evalInsn i stVirt) (evalInsn pi stPhys) := by
  have hused : ∀ u, u ∈ i.usedRegs → ∃ pu, m.lookup u = some pu ∧ stPhys pu = stVirt u := by
    intro u hu
    exact hagree u ((subset_insertManyLive i.usedRegs (eraseLive i.defReg liveAfter)).1 u hu)
  rcases applyAllocInsn_eval_eq happ hused with ⟨hdef, hrhs⟩
  have hpdeq : pi.defReg = pd := by
    rw [hpd] at hdef; injection hdef with heq; exact heq.symm
  intro v hv
  if hvd : v = i.defReg then
    refine ⟨pd, ?_, ?_⟩
    · rw [hvd]; exact hpd
    · unfold evalInsn writeReg
      rw [hpdeq, hvd]
      simp [hrhs]
  else
    have hmem_erase : v ∈ eraseLive i.defReg liveAfter := mem_eraseLive_of_ne hv hvd
    have hmem_before : v ∈ liveBeforeInsn i liveAfter :=
      (subset_insertManyLive i.usedRegs (eraseLive i.defReg liveAfter)).2 v hmem_erase
    rcases hagree v hmem_before with ⟨pv, hpv, hval⟩
    have hpv_ne : pv ≠ pd := checkNonInterfere_spec hni v hv hvd pv hpv
    refine ⟨pv, hpv, ?_⟩
    unfold evalInsn writeReg
    rw [hpdeq]
    simp [hpv_ne, hvd, hval]

private theorem checkBodyStepsFast_snd (m : AllocMap) (body : List (Insn VReg)) (liveEnd : List VReg) :
    (checkBodyStepsFast m body liveEnd).2 = liveBeforeInsns body liveEnd := by
  induction body with
  | nil => rfl
  | cons i is ih =>
    dsimp only [checkBodyStepsFast, liveBeforeInsns]
    rw [ih]

private theorem body_steps_agree_sound (m : AllocMap) (body : List (Insn VReg)) (liveEnd : List VReg) :
    ∀ {stVirt : VReg → UInt32} {stPhys : PReg → UInt32},
      (checkBodyStepsFast m body liveEnd).1 = true →
      AgreeOn m (checkBodyStepsFast m body liveEnd).2 stVirt stPhys →
      ∃ pBody, applyAllocInsns m body = some pBody ∧
        AgreeOn m liveEnd (evalInsns body stVirt) (evalInsns pBody stPhys) := by
  induction body with
  | nil =>
    intro stVirt stPhys _ hagree
    exact ⟨[], rfl, hagree⟩
  | cons i is ih =>
    intro stVirt stPhys hchk hagree
    dsimp only [checkBodyStepsFast] at hchk hagree
    rw [Bool.and_eq_true] at hchk
    rcases hchk with ⟨hhead, htail⟩
    cases happ : applyAllocInsn m i <;> cases hpd : m.lookup i.defReg <;>
      rw [happ, hpd] at hhead <;> try contradiction
    rename_i pi pd
    have hagree1 := step_agree_sound happ hpd hhead hagree
    rcases ih htail hagree1 with ⟨pis, hpis, hagreeF⟩
    refine ⟨pi :: pis, ?_, hagreeF⟩
    unfold applyAllocInsns
    rw [happ, hpis]

private theorem checkAllMapped_spec {m : AllocMap} {vs : List VReg}
    (hc : checkAllMapped m vs = true) :
    ∀ v, v ∈ vs → ∃ pv, m.lookup v = some pv := by
  induction vs with
  | nil => intro _ h; cases h
  | cons x xs ih =>
    unfold checkAllMapped at hc
    cases hx : m.lookup x <;> rw [hx] at hc
    · cases hc
    · rename_i px
      intro v hv
      cases hv with
      | head => exact ⟨px, hx⟩
      | tail _ hxs => exact ih hc v hxs

private theorem bindParams_agree_sound (m : AllocMap) (params : List VReg) (liveEntry : List VReg)
    (hmapped : checkAllMapped m liveEntry = true) :
    ∀ (args : List UInt32),
      checkParamInjective m params liveEntry = true →
      ∃ pParams, applyAllocParams m params = some pParams ∧
        AgreeOn m liveEntry (bindParams params args) (bindParams pParams args) := by
  induction params with
  | nil =>
    intro _ _
    refine ⟨[], rfl, ?_⟩
    intro v hv
    rcases checkAllMapped_spec hmapped v hv with ⟨pv, hpv⟩
    exact ⟨pv, hpv, rfl⟩
  | cons p ps ih =>
    intro args hchk
    unfold checkParamInjective at hchk
    rw [Bool.and_eq_true] at hchk
    rcases hchk with ⟨hhead, htail⟩
    cases hp : m.lookup p <;> rw [hp] at hhead
    · cases hhead
    · rename_i pp
      rw [Bool.and_eq_true] at hhead
      rcases hhead with ⟨_, hni⟩
      cases args with
      | nil =>
        rcases ih [] htail with ⟨pps, hpps, hagreeTail⟩
        refine ⟨pp :: pps, ?_, ?_⟩
        · unfold applyAllocParams; rw [hp, hpps]
        · intro v hv
          if hvp : v = p then
            refine ⟨pp, by rw [hvp]; exact hp, ?_⟩
            dsimp only [bindParams]; unfold writeReg; rw [hvp]; simp
          else
            rcases hagreeTail v hv with ⟨pv, hpv, hval⟩
            have hv_union : v ∈ insertManyLive ps liveEntry :=
              (subset_insertManyLive ps liveEntry).2 v hv
            have hpv_ne : pv ≠ pp := checkNonInterfere_spec hni v hv_union hvp pv hpv
            refine ⟨pv, hpv, ?_⟩
            dsimp only [bindParams]; unfold writeReg
            simp [hpv_ne, hvp, hval]
      | cons a as =>
        rcases ih as htail with ⟨pps, hpps, hagreeTail⟩
        refine ⟨pp :: pps, ?_, ?_⟩
        · unfold applyAllocParams; rw [hp, hpps]
        · intro v hv
          if hvp : v = p then
            refine ⟨pp, by rw [hvp]; exact hp, ?_⟩
            dsimp only [bindParams]; unfold writeReg; rw [hvp]; simp
          else
            rcases hagreeTail v hv with ⟨pv, hpv, hval⟩
            have hv_union : v ∈ insertManyLive ps liveEntry :=
              (subset_insertManyLive ps liveEntry).2 v hv
            have hpv_ne : pv ≠ pp := checkNonInterfere_spec hni v hv_union hvp pv hpv
            refine ⟨pv, hpv, ?_⟩
            dsimp only [bindParams]; unfold writeReg
            simp [hpv_ne, hvp, hval]

/-- Zero-spill & physical-register budget guarantee of `checkValidAlloc` (`%r31` reserved scratch). -/
theorem checkValidAlloc_zero_spill (prog : HoloProg VReg) (m : AllocMap)
    (hvalid : checkValidAlloc prog m = true) :
    m.spillCount = 0 ∧ m.maxRegs ≤ 31 := by
  unfold checkValidAlloc at hvalid
  simp only [Bool.and_eq_true, nat_beq_true_iff, Nat.ble_eq] at hvalid
  exact ⟨hvalid.1.1.1.1.1.1, hvalid.1.1.1.1.1.2⟩

private theorem checkBudget_lookup_ne_scratch {maxRegs : Nat} {pairs : List (VReg × PReg)}
    (hb : checkBudget maxRegs pairs = true) :
    ∀ v p, lookupPhysPairs pairs v = some p → p ≠ ptxScratchReg := by
  induction pairs with
  | nil => intro _ _ h; cases h
  | cons hd rest ih =>
    rcases hd with ⟨k, q⟩
    unfold checkBudget at hb
    simp only [Bool.and_eq_true] at hb
    rcases hb with ⟨⟨_, hlt31⟩, hrest⟩
    intro v p hlook
    unfold lookupPhysPairs at hlook
    cases hvk : Nat.beq v k <;> rw [hvk] at hlook
    · simp only [Bool.false_eq_true, ↓reduceIte] at hlook
      exact ih hrest v p hlook
    · simp only [↓reduceIte] at hlook
      injection hlook with hpq
      intro hp31
      rw [hpq, hp31] at hlt31
      cases hlt31

private theorem mem1_prop {P : PReg → Prop} {a : PReg} (ha : P a) : ∀ u ∈ [a], P u := by
  intro u hu; cases hu with | head => exact ha | tail _ h => cases h

private theorem mem2_prop {P : PReg → Prop} {a b : PReg} (ha : P a) (hb : P b) : ∀ u ∈ [a, b], P u := by
  intro u hu; cases hu with | head => exact ha | tail _ h => exact mem1_prop hb u h

private theorem mem3_prop {P : PReg → Prop} {a b c : PReg} (ha : P a) (hb : P b) (hc : P c) : ∀ u ∈ [a, b, c], P u := by
  intro u hu; cases hu with | head => exact ha | tail _ h => exact mem2_prop hb hc u h

private theorem applyAllocInsn_noScratch {m : AllocMap} {i : Insn VReg} {pi : Insn PReg}
    (hb : checkBudget m.maxRegs m.physOf = true)
    (happ : applyAllocInsn m i = some pi) :
    pi.defReg ≠ ptxScratchReg ∧ ∀ u ∈ pi.usedRegs, u ≠ ptxScratchReg := by
  have ne31 := checkBudget_lookup_ne_scratch hb
  cases i with
  | constU32 dst imm =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> rw [hd] at happ <;> try contradiction
    rename_i pd; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, fun _ h => by cases h⟩
  | mov dst s =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hs : m.lookup s <;> rw [hd, hs] at happ <;> try contradiction
    rename_i pd ps; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem1_prop (ne31 s ps hs)⟩
  | and32 dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem2_prop (ne31 l pl hl) (ne31 r pr hr)⟩
  | or32 dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem2_prop (ne31 l pl hl) (ne31 r pr hr)⟩
  | xor32 dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem2_prop (ne31 l pl hl) (ne31 r pr hr)⟩
  | shlImm dst s sh =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hs : m.lookup s <;> rw [hd, hs] at happ <;> try contradiction
    rename_i pd ps; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem1_prop (ne31 s ps hs)⟩
  | shrImm dst s sh =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hs : m.lookup s <;> rw [hd, hs] at happ <;> try contradiction
    rename_i pd ps; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem1_prop (ne31 s ps hs)⟩
  | shlReg dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem2_prop (ne31 l pl hl) (ne31 r pr hr)⟩
  | lop3 imm8 dst a b c =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases ha : m.lookup a <;> cases hb1 : m.lookup b <;> cases hc : m.lookup c <;>
      rw [hd, ha, hb1, hc] at happ <;> try contradiction
    rename_i pd pa pb pc; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem3_prop (ne31 a pa ha) (ne31 b pb hb1) (ne31 c pc hc)⟩
  | popc dst s =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hs : m.lookup s <;> rw [hd, hs] at happ <;> try contradiction
    rename_i pd ps; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem1_prop (ne31 s ps hs)⟩
  | cmpEq dst l r =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hl : m.lookup l <;> cases hr : m.lookup r <;>
      rw [hd, hl, hr] at happ <;> try contradiction
    rename_i pd pl pr; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem2_prop (ne31 l pl hl) (ne31 r pr hr)⟩
  | selp dst c t f =>
    dsimp only [applyAllocInsn] at happ
    cases hd : m.lookup dst <;> cases hc : m.lookup c <;> cases ht : m.lookup t <;> cases hf : m.lookup f <;>
      rw [hd, hc, ht, hf] at happ <;> try contradiction
    rename_i pd pc pt pf; injection happ with hpi; rw [← hpi]
    exact ⟨ne31 dst pd hd, mem3_prop (ne31 c pc hc) (ne31 t pt ht) (ne31 f pf hf)⟩

private theorem applyAllocInsns_noScratch {m : AllocMap} {body : List (Insn VReg)} {pBody : List (Insn PReg)}
    (hb : checkBudget m.maxRegs m.physOf = true)
    (happ : applyAllocInsns m body = some pBody) :
    ∀ pi ∈ pBody, pi.defReg ≠ ptxScratchReg ∧ ∀ u ∈ pi.usedRegs, u ≠ ptxScratchReg := by
  induction body generalizing pBody with
  | nil =>
    injection happ with hp; rw [← hp]; intro _ h; cases h
  | cons i is ih =>
    unfold applyAllocInsns at happ
    cases hi : applyAllocInsn m i <;> cases his : applyAllocInsns m is <;>
      rw [hi, his] at happ <;> try contradiction
    rename_i pi pis; injection happ with hp; rw [← hp]
    intro q hq
    cases hq with
    | head => exact applyAllocInsn_noScratch hb hi
    | tail _ hqs => exact ih his q hqs

/-- **THEOREM (`checkValidAlloc_sound` — Closes Unverified `RegAlloc` TCB!)**:
    For EVERY `HoloIR` program `prog` and allocation map `m`, if `checkValidAlloc prog m = true`,
    then `m.spillCount = 0`, `applyAlloc prog m` succeeds, and physical-register execution on `PReg`
    produces the **exact same `UInt32` output** as unbounded virtual-register SSA execution on `VReg`
    for ALL input argument lists `args` (`0` `Classical.choice`, `0` `bv_decide`)! -/
theorem checkValidAlloc_sound (prog : HoloProg VReg) (m : AllocMap) (args : List UInt32)
    (hvalid : checkValidAlloc prog m = true) :
    ∃ physProg,
      m.spillCount = 0 ∧
      applyAlloc prog m = some physProg ∧
      evalProg physProg args = evalProg prog args := by
  unfold checkValidAlloc at hvalid
  simp only [Bool.and_eq_true, nat_beq_true_iff, Nat.ble_eq] at hvalid
  rcases hvalid with ⟨⟨⟨⟨⟨⟨hspill, _⟩, _⟩, hretSome⟩, hmapped⟩, hparams⟩, hbody⟩
  rcases bindParams_agree_sound m prog.params (checkBodyStepsFast m prog.body [prog.retReg]).2 hmapped args hparams
    with ⟨pParams, hpParams, hagree0⟩
  rcases body_steps_agree_sound m prog.body [prog.retReg] hbody hagree0
    with ⟨pBody, hpBody, hagreeF⟩
  cases hret : m.lookup prog.retReg
  · rw [hret] at hretSome; cases hretSome
  · rename_i pRet
    refine ⟨{ params := pParams, body := pBody, retReg := pRet }, hspill, ?_, ?_⟩
    · unfold applyAlloc; rw [hpParams, hpBody, hret]
    · rcases hagreeF prog.retReg (.head _) with ⟨pv, hpv, heq⟩
      rw [hret] at hpv; injection hpv with hsame
      rw [← hsame] at heq
      exact heq

/-! ## 3. Backend Lowering Soundness (`EmitPTX` & 16-Lane `EmitAVX512`) -/

private theorem execPTXInsns_append (xs ys : List PTXInsn) (st : PTXState) :
    execPTXInsns (xs ++ ys) st = execPTXInsns ys (execPTXInsns xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (execPTXInsn x st)

/-- Every physical `HoloIR` instruction avoiding reserved `%r31` (`ptxScratchReg`) preserves
    exact general-purpose register agreement with `evalInsn` across all `q ≠ ptxScratchReg`
    (with `%r31` scratch clobber explicitly modeled in `execPTXInsn`). -/
theorem lowerInsnPTX_sound (insn : Insn PReg) (st : PTXState) (stIR : PReg → UInt32)
    (hd : insn.defReg ≠ ptxScratchReg)
    (hu : ∀ u ∈ insn.usedRegs, u ≠ ptxScratchReg)
    (hagree : ∀ r : PReg, r ≠ ptxScratchReg → st.regs r = stIR r) :
    ∀ q : PReg, q ≠ ptxScratchReg →
      (execPTXInsns (lowerInsnPTX insn) st).regs q = evalInsn insn stIR q := by
  have hsh31 : ∀ sh : UInt32, ((sh &&& 31) &&& 31) = (sh &&& 31) := by
    intro sh; apply UInt32.eq_of_toBitVec_eq; simp [UInt32.toBitVec_and, BitVec.and_assoc]
  intro q hq
  have _ := hd
  cases insn with
  | constU32 d imm =>
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd] else simp [hqd, hagree q hq]
  | mov d s =>
    have hs := hagree s (hu s (.head _))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd, hs] else simp [hqd, hagree q hq]
  | and32 d l r =>
    have hl := hagree l (hu l (.head _))
    have hr := hagree r (hu r (.tail _ (.head _)))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd, hl, hr] else simp [hqd, hagree q hq]
  | or32 d l r =>
    have hl := hagree l (hu l (.head _))
    have hr := hagree r (hu r (.tail _ (.head _)))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd, hl, hr] else simp [hqd, hagree q hq]
  | xor32 d l r =>
    have hl := hagree l (hu l (.head _))
    have hr := hagree r (hu r (.tail _ (.head _)))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd, hl, hr] else simp [hqd, hagree q hq]
  | shlImm d s sh =>
    have hs := hagree s (hu s (.head _))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd, hs, hsh31 sh] else simp [hqd, hagree q hq]
  | shrImm d s sh =>
    have hs := hagree s (hu s (.head _))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd, hs, hsh31 sh] else simp [hqd, hagree q hq]
  | shlReg d l r =>
    have hl_ne : l ≠ ptxScratchReg := hu l (.head _)
    have hl := hagree l hl_ne
    have hr := hagree r (hu r (.tail _ (.head _)))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd, hl_ne, hl, hr] else simp [hqd, hq, hagree q hq]
  | lop3 imm8 d a b c =>
    have ha := hagree a (hu a (.head _))
    have hb := hagree b (hu b (.tail _ (.head _)))
    have hc := hagree c (hu c (.tail _ (.tail _ (.head _))))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd, ha, hb, hc] else simp [hqd, hagree q hq]
  | popc d s =>
    have hs := hagree s (hu s (.head _))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp [hqd, hs] else simp [hqd, hagree q hq]
  | cmpEq d l r =>
    have hl := hagree l (hu l (.head _))
    have hr := hagree r (hu r (.tail _ (.head _)))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp only [hqd, ↓reduceIte, hl, hr] else simp only [hqd, ↓reduceIte, hagree q hq]
  | selp d c t f =>
    have hc := hagree c (hu c (.head _))
    have ht := hagree t (hu t (.tail _ (.head _)))
    have hf := hagree f (hu f (.tail _ (.tail _ (.head _))))
    dsimp only [lowerInsnPTX, execPTXInsns, execPTXInsn, evalInsn, evalInsnRhs, Insn.defReg, writeReg]
    if hqd : q = d then simp only [hqd, ↓reduceIte, hc, ht, hf] else simp only [hqd, ↓reduceIte, hagree q hq]

private theorem lowerInsnsPTX_sound (body : List (Insn PReg)) (st : PTXState) (stIR : PReg → UInt32)
    (hno31 : ∀ pi ∈ body, pi.defReg ≠ ptxScratchReg ∧ ∀ u ∈ pi.usedRegs, u ≠ ptxScratchReg)
    (hagree : ∀ r : PReg, r ≠ ptxScratchReg → st.regs r = stIR r) :
    ∀ q : PReg, q ≠ ptxScratchReg →
      (execPTXInsns (lowerInsnsPTX body) st).regs q = evalInsns body stIR q := by
  induction body generalizing st stIR with
  | nil => exact hagree
  | cons i is ih =>
    unfold lowerInsnsPTX evalInsns
    rcases hno31 i (.head _) with ⟨hd, hu⟩
    have hstep := lowerInsnPTX_sound i st stIR hd hu hagree
    intro q hq
    rw [execPTXInsns_append]
    exact ih (execPTXInsns (lowerInsnPTX i) st) (evalInsn i stIR) (fun pi hpi => hno31 pi (.tail _ hpi)) hstep q hq

/-- **THEOREM (End-to-End `HoloIR -> RegAlloc -> sm_86 PTX` Soundness)**:
    Verified zero-spill compilation from `HoloProg VReg` to `PTXState` preserves exact semantics! -/
theorem compileToPTX_end_to_end_sound (prog : HoloProg VReg) (m : AllocMap) (args : List UInt32)
    (hvalid : checkValidAlloc prog m = true) :
    ∃ physProg,
      m.spillCount = 0 ∧
      applyAlloc prog m = some physProg ∧
      evalPTXProg physProg args = evalProg prog args := by
  have hbudget : checkBudget m.maxRegs m.physOf = true := by
    unfold checkValidAlloc at hvalid
    simp only [Bool.and_eq_true] at hvalid
    exact hvalid.1.1.1.1.2
  rcases checkValidAlloc_sound prog m args hvalid with ⟨physProg, hspill, happ, heval⟩
  refine ⟨physProg, hspill, happ, ?_⟩
  have happ' := happ
  unfold applyAlloc at happ'
  cases hpP : applyAllocParams m prog.params <;> cases hpB : applyAllocInsns m prog.body <;>
    cases hpR : m.lookup prog.retReg <;> rw [hpP, hpB, hpR] at happ' <;> try contradiction
  rename_i pParams pBody pRet
  injection happ' with hphys
  have hbody_no31 := applyAllocInsns_noScratch hbudget hpB
  have hret_no31 := checkBudget_lookup_ne_scratch hbudget prog.retReg pRet hpR
  rw [← hphys] at heval ⊢
  change (execPTXInsns (lowerInsnsPTX pBody) { regs := bindParams pParams args, p0 := false }).regs pRet =
    evalProg prog args
  have hrun := lowerInsnsPTX_sound pBody { regs := bindParams pParams args, p0 := false } (bindParams pParams args)
    hbody_no31 (fun _ _ => rfl) pRet hret_no31
  rw [hrun]
  exact heval

/-- **REGRESSION THEOREM (PTX `%r31` Scratch Clobber Rejected)**:
    1. Allocating `v0 ↦ %r31` on `[shlReg 2 0 1]` is rejected (`checkValidAlloc = false`) under BOTH `maxRegs = 32` AND `maxRegs = 31`,
    2. `allocateZeroSpill 32` rejects `maxRegs = 32` at entry, and
    3. `execPTXInsn` faithfully models hardware `%r31` scratch clobber (`64` when `lhs = %r31`). -/
theorem ptx_r31_scratch_clobber_rejected :
    let badProg : HoloProg VReg := { params := [0, 1], body := [.shlReg 2 0 1], retReg := 2 }
    let badMap32 : AllocMap :=
      { physOf := [(0, ⟨31, by decide⟩), (1, ⟨1, by decide⟩), (2, ⟨2, by decide⟩)]
      , spillCount := 0
      , maxRegs := 32 }
    let badMap31 : AllocMap := { badMap32 with maxRegs := 31 }
    let unverifiedPhys : HoloProg PReg :=
      { params := [⟨31, by decide⟩, ⟨1, by decide⟩]
      , body := [.shlReg ⟨2, by decide⟩ ⟨31, by decide⟩ ⟨1, by decide⟩]
      , retReg := ⟨2, by decide⟩ }
    checkValidAlloc badProg badMap32 = false ∧
    checkValidAlloc badProg badMap31 = false ∧
    (allocateZeroSpill 32 badProg).isOk = false ∧
    evalProg badProg [1, 4] = 16 ∧
    evalPTXProg unverifiedPhys [1, 4] = 64 := by
  decide

private theorem execAVX512Insns_append (xs ys : List AVX512Insn) (st : AVX512State) :
    execAVX512Insns (xs ++ ys) st = execAVX512Insns ys (execAVX512Insns xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (execAVX512Insn x st)

/-- Per-lane projection of `AVX512State` agrees instruction-by-instruction with scalar `evalInsn`. -/
theorem lowerInsnAVX512_lane_sound (insn : Insn PReg) (st : AVX512State) (lane : Fin 16) :
    (fun r => (execAVX512Insns (lowerInsnAVX512 insn) st).zmm r lane) =
      evalInsn insn (fun r => st.zmm r lane) := by
  have hsh31 : ∀ sh : UInt32, ((sh &&& 31) &&& 31) = (sh &&& 31) := by
    intro sh; apply UInt32.eq_of_toBitVec_eq; simp [UInt32.toBitVec_and, BitVec.and_assoc]
  funext r'
  cases insn with
  | constU32 d imm =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h] else simp [h]
  | mov d s =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h] else simp [h]
  | and32 d l r =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h] else simp [h]
  | or32 d l r =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h] else simp [h]
  | xor32 d l r =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h] else simp [h]
  | shlImm d s sh =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h, hsh31 sh] else simp [h]
  | shrImm d s sh =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h, hsh31 sh] else simp [h]
  | shlReg d l r =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h] else simp [h]
  | lop3 imm8 d a b c =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h] else simp [h]
  | popc d s =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp [h] else simp [h]
  | cmpEq d l r =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp only [h, ↓reduceIte]; rfl else simp only [h, ↓reduceIte]
  | selp d c t f =>
    dsimp only [lowerInsnAVX512, execAVX512Insns, execAVX512Insn, evalInsn, evalInsnRhs, Insn.defReg, writeZmm, writeReg]
    if h : r' = d then simp only [h, ↓reduceIte]; rfl else simp only [h, ↓reduceIte]

private theorem lowerInsnsAVX512_lane_sound (body : List (Insn PReg)) (st : AVX512State) (lane : Fin 16) :
    (fun r => (execAVX512Insns (lowerInsnsAVX512 body) st).zmm r lane) =
      evalInsns body (fun r => st.zmm r lane) := by
  induction body generalizing st with
  | nil => rfl
  | cons i is ih =>
    unfold lowerInsnsAVX512 evalInsns
    rw [execAVX512Insns_append, ih, lowerInsnAVX512_lane_sound]

private theorem bindParamsSIMD_lane_eq (params : List PReg) (vecArgs : List Vec16U32) (lane : Fin 16) :
    (fun r => bindParamsSIMD params vecArgs r lane) =
      bindParams params (vecArgs.map (fun v => v lane)) := by
  induction params generalizing vecArgs with
  | nil => rfl
  | cons p ps ih =>
    cases vecArgs with
    | nil =>
      funext r
      simp only [bindParamsSIMD, bindParams, List.map, writeZmm, writeReg]
      if h : r = p then
        simp [h]
      else
        simp only [h, ↓reduceIte]
        exact congrFun (ih []) r
    | cons v vs =>
      funext r
      simp only [bindParamsSIMD, bindParams, List.map, writeZmm, writeReg]
      if h : r = p then
        simp [h]
      else
        simp only [h, ↓reduceIte]
        exact congrFun (ih vs) r

/-- **THEOREM (End-to-End 16-Lane `HoloIR -> RegAlloc -> AVX-512` SIMD Vectorization Soundness)**:
    Every lane `lane : Fin 16` of the compiled 512-bit `AVX-512` program computes the exact same
    `UInt32` result as the virtual-register `HoloProg VReg` on that lane's scalar inputs! -/
theorem compileToAVX512_end_to_end_sound (prog : HoloProg VReg) (m : AllocMap)
    (vecArgs : List Vec16U32) (lane : Fin 16)
    (hvalid : checkValidAlloc prog m = true) :
    ∃ physProg,
      m.spillCount = 0 ∧
      applyAlloc prog m = some physProg ∧
      evalAVX512Prog physProg vecArgs lane = evalProg prog (vecArgs.map (fun v => v lane)) := by
  rcases checkValidAlloc_sound prog m (vecArgs.map (fun v => v lane)) hvalid with ⟨physProg, hspill, happ, heval⟩
  refine ⟨physProg, hspill, happ, ?_⟩
  unfold evalAVX512Prog evalProg
  have hlane := congrFun (lowerInsnsAVX512_lane_sound physProg.body
    { zmm := bindParamsSIMD physProg.params vecArgs, k1 := fun _ => false } lane) physProg.retReg
  dsimp only at hlane
  rw [hlane, bindParamsSIMD_lane_eq]
  exact heval

/-! ## 4. Concrete `[16, 11, 4]` `A_16` SECDED + Folded-Parity End-to-End Proofs (`0` `bv_decide`) -/

def foldedParityAlloc : AllocMap :=
  match allocateZeroSpill 8 a16FoldedParityIR with
  | .ok m => m
  | .error _ => { physOf := [], spillCount := 1, maxRegs := 0 }

def syndromeAlloc : AllocMap :=
  match allocateZeroSpill 8 a16SyndromeIR with
  | .ok m => m
  | .error _ => { physOf := [], spillCount := 1, maxRegs := 0 }

def secdedHealAlloc : AllocMap :=
  match allocateZeroSpill 12 a16SecdedHealIR with
  | .ok m => m
  | .error _ => { physOf := [], spillCount := 1, maxRegs := 0 }

theorem foldedParityAlloc_valid : checkValidAlloc a16FoldedParityIR foldedParityAlloc = true := by
  rfl

set_option maxRecDepth 4096 in
theorem syndromeAlloc_valid : checkValidAlloc a16SyndromeIR syndromeAlloc = true := by
  rfl

set_option maxRecDepth 4096 in
theorem secdedHealAlloc_valid : checkValidAlloc a16SecdedHealIR secdedHealAlloc = true := by
  rfl

def foldedParityPhys : HoloProg PReg :=
  match applyAlloc a16FoldedParityIR foldedParityAlloc with
  | some p => p
  | none => { params := [], body := [], retReg := ⟨0, by decide⟩ }

def syndromePhys : HoloProg PReg :=
  match applyAlloc a16SyndromeIR syndromeAlloc with
  | some p => p
  | none => { params := [], body := [], retReg := ⟨0, by decide⟩ }

def secdedHealPhys : HoloProg PReg :=
  match applyAlloc a16SecdedHealIR secdedHealAlloc with
  | some p => p
  | none => { params := [], body := [], retReg := ⟨0, by decide⟩ }

/-- **THEOREM (Compiled `a16FoldedParity` PTX & AVX-512 Soundness)**:
    Both `sm_86` PTX (`lop3.b32 0x96`) and `AVX-512` (`vpternlogd 0x96`) compute exact
    `((w >>> 1) ^^^ (w >>> 2) ^^^ (w >>> 3)) &&& 1` with `0` spills (`<= 8` regs)! -/
theorem a16FoldedParity_compiled_sound (w : UInt32) (zw : Vec16U32) (lane : Fin 16) :
    foldedParityAlloc.spillCount = 0 ∧
    evalPTXProg foldedParityPhys [w] = foldedUpperParitySpec w ∧
    evalAVX512Prog foldedParityPhys [zw] lane = foldedUpperParitySpec (zw lane) := by
  rcases compileToPTX_end_to_end_sound a16FoldedParityIR foldedParityAlloc [w] foldedParityAlloc_valid
    with ⟨p1, hsp, hap1, hptx⟩
  rcases compileToAVX512_end_to_end_sound a16FoldedParityIR foldedParityAlloc [zw] lane foldedParityAlloc_valid
    with ⟨p2, _, hap2, havx⟩
  have hp1 : foldedParityPhys = p1 := by unfold foldedParityPhys; rw [hap1]
  have hp2 : foldedParityPhys = p2 := by unfold foldedParityPhys; rw [hap2]
  have hir : ∀ x : UInt32, evalProg a16FoldedParityIR [x] = foldedUpperParitySpec x := by
    intro x
    simp [evalProg, a16FoldedParityIR, bindParams, evalInsns, evalInsn, evalInsnRhs, Insn.defReg,
      writeReg, foldedUpperParitySpec, lop3_0x96_exact]
  simp only [List.map] at havx
  refine ⟨hsp, ?_, ?_⟩
  · rw [hp1, hptx, hir w]
  · rw [hp2, havx, hir (zw lane)]

/-! ### Exact $GF(2)$ Linearity of `popc32 &&& 1` and `a16SyndromeSpec` (`0` `bv_decide`, `0` `Classical.choice`) -/

private theorem zero_lsb : ∀ j : Fin 32, (0 : UInt32).toBitVec.getLsbD j.val = false := by
  decide

private theorem one_lsb : ∀ j : Fin 32, (1 : UInt32).toBitVec.getLsbD j.val = Nat.beq j.val 0 := by
  decide

private theorem and1_zero_or_one (u : UInt32) : (u &&& 1) = 0 ∨ (u &&& 1) = 1 := by
  cases hb : u.toBitVec.getLsbD 0
  · refine Or.inl ?_
    apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h0 := zero_lsb ⟨j, hj⟩; dsimp only at h0
    have h1 := one_lsb ⟨j, hj⟩; dsimp only at h1
    rw [UInt32.toBitVec_and, BitVec.getLsbD_and, h0, h1]
    match j with
    | 0 => rw [hb]; rfl
    | _ + 1 => change (_ && false) = false; exact Bool.and_false _
  · refine Or.inr ?_
    apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h1 := one_lsb ⟨j, hj⟩; dsimp only at h1
    rw [UInt32.toBitVec_and, BitVec.getLsbD_and, h1]
    match j with
    | 0 => rw [hb]; rfl
    | _ + 1 => change (_ && false) = false; exact Bool.and_false _

private theorem u32_and1_eq_one_iff (u : UInt32) : u32Eq (u &&& 1) 1 = u.toBitVec.getLsbD 0 := by
  rcases and1_zero_or_one u with h0 | h1
  · have hb : (u &&& 1).toBitVec.getLsbD 0 = false := by rw [h0]; rfl
    rw [UInt32.toBitVec_and, BitVec.getLsbD_and] at hb
    have h10 : (1 : UInt32).toBitVec.getLsbD 0 = true := rfl
    rw [h10, Bool.and_true] at hb
    rw [h0, hb]; rfl
  · have hb : (u &&& 1).toBitVec.getLsbD 0 = true := by rw [h1]; rfl
    rw [UInt32.toBitVec_and, BitVec.getLsbD_and] at hb
    have h10 : (1 : UInt32).toBitVec.getLsbD 0 = true := rfl
    rw [h10, Bool.and_true] at hb
    rw [h1, hb]; rfl

private theorem shr_xor_distrib (x y s : UInt32) :
    ((x ^^^ y) >>> s) = ((x >>> s) ^^^ (y >>> s)) := by
  apply UInt32.eq_of_toBitVec_eq
  rw [UInt32.toBitVec_shiftRight, UInt32.toBitVec_xor, UInt32.toBitVec_xor,
      UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  let sh := (s.toBitVec % 32).toNat
  change ((x.toBitVec ^^^ y.toBitVec) >>> sh).getLsbD i =
    ((x.toBitVec >>> sh) ^^^ (y.toBitVec >>> sh)).getLsbD i
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]

private theorem shl_xor_distrib (x y s : UInt32) :
    ((x ^^^ y) <<< s) = ((x <<< s) ^^^ (y <<< s)) := by
  apply UInt32.eq_of_toBitVec_eq
  rw [UInt32.toBitVec_shiftLeft, UInt32.toBitVec_xor, UInt32.toBitVec_xor,
      UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftLeft]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  let sh := (s.toBitVec % 32).toNat
  change ((x.toBitVec ^^^ y.toBitVec) <<< sh).getLsbD i =
    ((x.toBitVec <<< sh) ^^^ (y.toBitVec <<< sh)).getLsbD i
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  cases decide (i < 32) <;> cases decide (i < sh) <;> rfl

private theorem shr_and1_xor (x y : UInt32) (k : Nat) :
    u32Eq (((x ^^^ y) >>> k.toUInt32) &&& 1) 1 =
      Bool.xor (u32Eq (((x >>> k.toUInt32) &&& 1)) 1) (u32Eq (((y >>> k.toUInt32) &&& 1)) 1) := by
  rw [shr_xor_distrib, u32_and1_eq_one_iff, u32_and1_eq_one_iff, u32_and1_eq_one_iff]
  rw [UInt32.toBitVec_xor, BitVec.getLsbD_xor]

private theorem countBitsAux_le (x : UInt32) : ∀ k, countBitsAux x k ≤ k
  | 0 => Nat.le_refl 0
  | k + 1 => by
    unfold countBitsAux
    have ih := countBitsAux_le x k
    cases u32Eq ((x >>> k.toUInt32) &&& 1) 1 <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem u32_and1_val_fin33 :
    ∀ n : Fin 33, ((n.val.toUInt32) &&& 1) = (if Nat.beq (n.val % 2) 1 then 1 else 0) := by
  decide

private theorem mod2_01 : ∀ a : Nat, a % 2 = 0 ∨ a % 2 = 1
  | 0 => Or.inl rfl
  | 1 => Or.inr rfl
  | n + 2 => by
    have heq : (n + 2) % 2 = n % 2 := Nat.add_mod_right n 2
    rw [heq]
    exact mod2_01 n

private theorem addBit_mod2 (a : Nat) (b : Bool) :
    Nat.beq ((a + (if b then 1 else 0)) % 2) 1 = Bool.xor (Nat.beq (a % 2) 1) b := by
  rcases mod2_01 a with ha0 | ha1
  · cases b
    · have hm : (a + 0) % 2 = 0 := by omega
      change Nat.beq ((a + 0) % 2) 1 = Bool.xor (Nat.beq (a % 2) 1) false
      rw [hm, ha0]; rfl
    · have hm : (a + 1) % 2 = 1 := by omega
      change Nat.beq ((a + 1) % 2) 1 = Bool.xor (Nat.beq (a % 2) 1) true
      rw [hm, ha0]; rfl
  · cases b
    · have hm : (a + 0) % 2 = 1 := by omega
      change Nat.beq ((a + 0) % 2) 1 = Bool.xor (Nat.beq (a % 2) 1) false
      rw [hm, ha1]; rfl
    · have hm : (a + 1) % 2 = 0 := by omega
      change Nat.beq ((a + 1) % 2) 1 = Bool.xor (Nat.beq (a % 2) 1) true
      rw [hm, ha1]; rfl

private theorem countBitsAux_mod2_xor (x y : UInt32) :
    ∀ k, Nat.beq (countBitsAux (x ^^^ y) k % 2) 1 =
      Bool.xor (Nat.beq (countBitsAux x k % 2) 1) (Nat.beq (countBitsAux y k % 2) 1)
  | 0 => rfl
  | k + 1 => by
    unfold countBitsAux
    rw [shr_and1_xor x y k, addBit_mod2, addBit_mod2, addBit_mod2, countBitsAux_mod2_xor x y k]
    cases Nat.beq (countBitsAux x k % 2) 1 <;>
    cases Nat.beq (countBitsAux y k % 2) 1 <;>
    cases u32Eq ((x >>> k.toUInt32) &&& 1) 1 <;>
    cases u32Eq ((y >>> k.toUInt32) &&& 1) 1 <;> rfl

/-- Exact parity homomorphism of `popc32`: `(popc32 (x ^^^ y) &&& 1) = (popc32 x &&& 1) ^^^ (popc32 y &&& 1)`. -/
theorem popc32_parity_xor (x y : UInt32) :
    (popc32 (x ^^^ y) &&& 1) = ((popc32 x &&& 1) ^^^ (popc32 y &&& 1)) := by
  have to01 : ∀ u : UInt32, (popc32 u &&& 1) = (if Nat.beq (countBitsAux u 32 % 2) 1 then 1 else 0) := by
    intro u
    have hle := countBitsAux_le u 32
    exact u32_and1_val_fin33 ⟨countBitsAux u 32, by omega⟩
  rw [to01 (x ^^^ y), to01 x, to01 y, countBitsAux_mod2_xor x y 32]
  cases Nat.beq (countBitsAux x 32 % 2) 1 <;> cases Nat.beq (countBitsAux y 32 % 2) 1 <;> rfl

private theorem u32_xor_and_distrib (x y m : UInt32) :
    ((x ^^^ y) &&& m) = ((x &&& m) ^^^ (y &&& m)) := by
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;> rfl

private theorem pack5_or_eq_xor (b0 b1 b2 b3 b4 : UInt32)
    (h0 : b0 = 0 ∨ b0 = 1) (h1 : b1 = 0 ∨ b1 = 1) (h2 : b2 = 0 ∨ b2 = 1)
    (h3 : b3 = 0 ∨ b3 = 1) (h4 : b4 = 0 ∨ b4 = 1) :
    (b0 ||| (b1 <<< 1) ||| (b2 <<< 2) ||| (b3 <<< 3) ||| (b4 <<< 4)) =
      (b0 ^^^ (b1 <<< 1) ^^^ (b2 <<< 2) ^^^ (b3 <<< 3) ^^^ (b4 <<< 4)) := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases h3 with rfl | rfl <;> rcases h4 with rfl | rfl <;> rfl

/-- **THEOREM (`a16SyndromeSpec` Exact $GF(2)$ Linearity)**:
    `a16SyndromeSpec (x ^^^ y) = a16SyndromeSpec x ^^^ a16SyndromeSpec y` for ALL `x, y : UInt32`! -/
theorem a16Syndrome_xor_linear (x y : UInt32) :
    a16SyndromeSpec (x ^^^ y) = a16SyndromeSpec x ^^^ a16SyndromeSpec y := by
  unfold a16SyndromeSpec
  dsimp only
  rw [pack5_or_eq_xor _ _ _ _ _ (and1_zero_or_one _) (and1_zero_or_one _) (and1_zero_or_one _) (and1_zero_or_one _) (and1_zero_or_one _),
      pack5_or_eq_xor _ _ _ _ _ (and1_zero_or_one _) (and1_zero_or_one _) (and1_zero_or_one _) (and1_zero_or_one _) (and1_zero_or_one _),
      pack5_or_eq_xor _ _ _ _ _ (and1_zero_or_one _) (and1_zero_or_one _) (and1_zero_or_one _) (and1_zero_or_one _) (and1_zero_or_one _)]
  simp only [u32_xor_and_distrib, popc32_parity_xor, shl_xor_distrib]
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt32.toBitVec_xor, BitVec.getLsbD_xor]
  cases (popc32 (x &&& 0xFFFF) &&& 1).toBitVec.getLsbD i <;>
  cases (popc32 (y &&& 0xFFFF) &&& 1).toBitVec.getLsbD i <;>
  cases ((popc32 (x &&& 0xAAAA) &&& 1) <<< 1).toBitVec.getLsbD i <;>
  cases ((popc32 (y &&& 0xAAAA) &&& 1) <<< 1).toBitVec.getLsbD i <;>
  cases ((popc32 (x &&& 0xCCCC) &&& 1) <<< 2).toBitVec.getLsbD i <;>
  cases ((popc32 (y &&& 0xCCCC) &&& 1) <<< 2).toBitVec.getLsbD i <;>
  cases ((popc32 (x &&& 0xF0F0) &&& 1) <<< 3).toBitVec.getLsbD i <;>
  cases ((popc32 (y &&& 0xF0F0) &&& 1) <<< 3).toBitVec.getLsbD i <;>
  cases ((popc32 (x &&& 0xFF00) &&& 1) <<< 4).toBitVec.getLsbD i <;>
  cases ((popc32 (y &&& 0xFF00) &&& 1) <<< 4).toBitVec.getLsbD i <;> rfl

private theorem encodeA16_syndrome_zero (msg : UInt32) :
    a16SyndromeSpec (encodeA16 msg) = 0 ∧ (encodeA16 msg &&& 0xFFFF) = encodeA16 msg := by
  have h0  : a16SyndromeSpec (a16BasisWord 3)  = 0 ∧ (a16BasisWord 3  &&& 0xFFFF) = a16BasisWord 3  := by decide
  have h1  : a16SyndromeSpec (a16BasisWord 5)  = 0 ∧ (a16BasisWord 5  &&& 0xFFFF) = a16BasisWord 5  := by decide
  have h2  : a16SyndromeSpec (a16BasisWord 6)  = 0 ∧ (a16BasisWord 6  &&& 0xFFFF) = a16BasisWord 6  := by decide
  have h3  : a16SyndromeSpec (a16BasisWord 7)  = 0 ∧ (a16BasisWord 7  &&& 0xFFFF) = a16BasisWord 7  := by decide
  have h4  : a16SyndromeSpec (a16BasisWord 9)  = 0 ∧ (a16BasisWord 9  &&& 0xFFFF) = a16BasisWord 9  := by decide
  have h5  : a16SyndromeSpec (a16BasisWord 10) = 0 ∧ (a16BasisWord 10 &&& 0xFFFF) = a16BasisWord 10 := by decide
  have h6  : a16SyndromeSpec (a16BasisWord 11) = 0 ∧ (a16BasisWord 11 &&& 0xFFFF) = a16BasisWord 11 := by decide
  have h7  : a16SyndromeSpec (a16BasisWord 12) = 0 ∧ (a16BasisWord 12 &&& 0xFFFF) = a16BasisWord 12 := by decide
  have h8  : a16SyndromeSpec (a16BasisWord 13) = 0 ∧ (a16BasisWord 13 &&& 0xFFFF) = a16BasisWord 13 := by decide
  have h9  : a16SyndromeSpec (a16BasisWord 14) = 0 ∧ (a16BasisWord 14 &&& 0xFFFF) = a16BasisWord 14 := by decide
  have h10 : a16SyndromeSpec (a16BasisWord 15) = 0 ∧ (a16BasisWord 15 &&& 0xFFFF) = a16BasisWord 15 := by decide
  have hzero : a16SyndromeSpec 0 = 0 ∧ ((0 : UInt32) &&& 0xFFFF) = 0 := by decide
  have step : ∀ {u v : UInt32},
      (a16SyndromeSpec u = 0 ∧ (u &&& 0xFFFF) = u) →
      (a16SyndromeSpec v = 0 ∧ (v &&& 0xFFFF) = v) →
      (a16SyndromeSpec (u ^^^ v) = 0 ∧ ((u ^^^ v) &&& 0xFFFF) = (u ^^^ v)) := by
    intro u v hu hv
    refine ⟨?_, ?_⟩
    · rw [a16Syndrome_xor_linear, hu.1, hv.1]; rfl
    · rw [u32_xor_and_distrib, hu.2, hv.2]
  have optStep : ∀ (cond : Bool) {w : UInt32},
      (a16SyndromeSpec w = 0 ∧ (w &&& 0xFFFF) = w) →
      (a16SyndromeSpec (if cond then w else 0) = 0 ∧ ((if cond then w else 0) &&& 0xFFFF) = (if cond then w else 0)) := by
    intro cond w hw
    cases cond
    · exact hzero
    · exact hw
  unfold encodeA16
  exact step (step (step (step (step (step (step (step (step (step
    (optStep _ h0) (optStep _ h1)) (optStep _ h2)) (optStep _ h3)) (optStep _ h4))
    (optStep _ h5)) (optStep _ h6)) (optStep _ h7)) (optStep _ h8)) (optStep _ h9)) (optStep _ h10)

private theorem single_bit_syndrome_exact :
    ∀ i : Fin 16,
      a16SyndromeSpec ((1 : UInt32) <<< i.val.toUInt32) = ((i.val.toUInt32 <<< 1) ||| 1) ∧
      (((1 : UInt32) <<< i.val.toUInt32) &&& 0xFFFF) = ((1 : UInt32) <<< i.val.toUInt32) := by
  decide

private theorem double_bit_syndrome_exact :
    ∀ i j : Fin 16,
      i ≠ j →
      let err := ((1 : UInt32) <<< i.val.toUInt32) ^^^ ((1 : UInt32) <<< j.val.toUInt32)
      u32Eq (a16SyndromeSpec err) 0 = false ∧
      (a16SyndromeSpec err &&& 1) = 0 ∧
      (err &&& 0xFFFF) = err := by
  decide

/-- Direct evaluation formula of `a16SecdedHealIR` in terms of `a16SyndromeSpec`. -/
theorem eval_a16SecdedHealIR_spec (w : UInt32) :
    evalProg a16SecdedHealIR [w] =
      let synd := a16SyndromeSpec w
      let wClean := w &&& 0xFFFF
      let isSec := synd &&& 1
      let errIdx := (synd >>> 1) &&& 0xF
      let healed := if u32Ne isSec 0 then wClean ^^^ ((1 : UInt32) <<< (errIdx &&& 31)) else wClean
      let isDed := (if u32Eq synd 0 then (0 : UInt32) else 1) &&& (isSec ^^^ 1)
      healed ||| (isSec <<< 16) ||| (isDed <<< 17) := by
  have hnot0 : ∀ b : Bool, ((if b then (1 : UInt32) else 0) ^^^ 1) = (if b then 0 else 1) := by
    intro b; cases b <;> rfl
  simp only [evalProg, a16SecdedHealIR, a16SyndromeIR, List.cons_append, List.nil_append,
    bindParams, evalInsns, evalInsn, evalInsnRhs, Insn.defReg, writeReg, a16SyndromeSpec,
    ↓reduceIte, Nat.reduceEqDiff, hnot0]
  rfl

/-- **THEOREM (Compiled `a16Syndrome` PTX & AVX-512 Soundness)**:
    Zero-spill `sm_86` PTX & 16-lane `AVX-512` `syndromePhys` match `razor_a16_secded_syndrome`
    for ALL `w : UInt32`! -/
theorem a16Syndrome_compiled_sound (w : UInt32) (zw : Vec16U32) (lane : Fin 16) :
    syndromeAlloc.spillCount = 0 ∧
    evalPTXProg syndromePhys [w] = a16SyndromeSpec w ∧
    evalAVX512Prog syndromePhys [zw] lane = a16SyndromeSpec (zw lane) := by
  rcases compileToPTX_end_to_end_sound a16SyndromeIR syndromeAlloc [w] syndromeAlloc_valid
    with ⟨p1, hsp, hap1, hptx⟩
  rcases compileToAVX512_end_to_end_sound a16SyndromeIR syndromeAlloc [zw] lane syndromeAlloc_valid
    with ⟨p2, _, hap2, havx⟩
  have hp1 : syndromePhys = p1 := by unfold syndromePhys; rw [hap1]
  have hp2 : syndromePhys = p2 := by unfold syndromePhys; rw [hap2]
  have hir : ∀ x : UInt32, evalProg a16SyndromeIR [x] = a16SyndromeSpec x := fun _ => rfl
  simp only [List.map] at havx
  refine ⟨hsp, ?_, ?_⟩
  · rw [hp1, hptx, hir w]
  · rw [hp2, havx, hir (zw lane)]

/-- **THEOREM 1 (Clean Codewords — 0 False Alarms, Exact Identity Across All 16 Lanes)**:
    For EVERY 11-bit message `msg : UInt32`, both compiled zero-spill `sm_86` PTX and 16-lane `AVX-512`
    `secdedHealPhys` return `isDed = 0`, `isSec = 0`, and exact `encodeA16 msg`! -/
theorem a16_clean_codeword_exact (msg : UInt32) :
    secdedHealAlloc.spillCount = 0 ∧
    evalPTXProg secdedHealPhys [encodeA16 msg] = encodeA16 msg ∧
    ∀ (zIn : Vec16U32) (lane : Fin 16),
      zIn lane = encodeA16 msg → evalAVX512Prog secdedHealPhys [zIn] lane = encodeA16 msg := by
  rcases compileToPTX_end_to_end_sound a16SecdedHealIR secdedHealAlloc [encodeA16 msg] secdedHealAlloc_valid
    with ⟨p1, hsp, hap1, hptx⟩
  have hp1 : secdedHealPhys = p1 := by unfold secdedHealPhys; rw [hap1]
  rcases encodeA16_syndrome_zero msg with ⟨hs0, hmask⟩
  have hir : evalProg a16SecdedHealIR [encodeA16 msg] = encodeA16 msg := by
    rw [eval_a16SecdedHealIR_spec]; dsimp only
    rw [hs0, hmask]
    change encodeA16 msg ||| 0 ||| 0 = encodeA16 msg
    rw [UInt32.or_zero, UInt32.or_zero]
  refine ⟨hsp, by rw [hp1, hptx, hir], ?_⟩
  intro zIn lane hlane
  rcases compileToAVX512_end_to_end_sound a16SecdedHealIR secdedHealAlloc [zIn] lane secdedHealAlloc_valid
    with ⟨p2, _, hap2, havx⟩
  have hp2 : secdedHealPhys = p2 := by unfold secdedHealPhys; rw [hap2]
  simp only [List.map, hlane] at havx
  rw [hp2, havx, hir]

/-- **THEOREM 2 (100% Single-Bit Error Correction Across All `2,048 × 16 = 32,768` States)**:
    For EVERY message `msg : UInt32` and EVERY bit flip `i : Fin 16`, both compiled zero-spill
    `sm_86` PTX and 16-lane `AVX-512` `secdedHealPhys` set `isSec = 1` (`bit 16`), `isDed = 0` (`bit 17`),
    and recover the **exact uncorrupted codeword `encodeA16 msg`** (`0` `bv_decide`, `0` `Classical.choice`)! -/
theorem a16_sec_100pct_exact_recovery (msg : UInt32) (i : Fin 16) :
    let cw := encodeA16 msg
    let faulted := cw ^^^ ((1 : UInt32) <<< i.val.toUInt32)
    let expected := cw ||| ((1 : UInt32) <<< 16)
    evalPTXProg secdedHealPhys [faulted] = expected ∧
    ∀ (zIn : Vec16U32) (lane : Fin 16),
      zIn lane = faulted → evalAVX512Prog secdedHealPhys [zIn] lane = expected := by
  intro cw faulted expected
  rcases encodeA16_syndrome_zero msg with ⟨hs0, hcwMask⟩
  rcases single_bit_syndrome_exact i with ⟨hsi, herrMask⟩
  have hsynd : a16SyndromeSpec faulted = ((i.val.toUInt32 <<< 1) ||| 1) := by
    dsimp only [faulted, cw]
    rw [a16Syndrome_xor_linear, hs0, hsi, UInt32.zero_xor]
  have hclean : (faulted &&& 0xFFFF) = faulted := by
    dsimp only [faulted, cw]
    rw [u32_xor_and_distrib, hcwMask, herrMask]
  have hidx : ∀ k : Fin 16,
      let s := ((k.val.toUInt32 <<< 1) ||| 1)
      (s &&& 1) = 1 ∧
      (((s >>> 1) &&& 0xF) &&& 31) = k.val.toUInt32 ∧
      u32Eq s 0 = false := by
    decide
  rcases hidx i with ⟨hisSec, herrIdx, hne0⟩
  have hcancel : ∀ a b : UInt32, (a ^^^ b) ^^^ b = a := by
    intro a b
    apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq
    intro j _; simp only [UInt32.toBitVec_xor, BitVec.getLsbD_xor]
    cases a.toBitVec.getLsbD j <;> cases b.toBitVec.getLsbD j <;> rfl
  have hir : evalProg a16SecdedHealIR [faulted] = expected := by
    rw [eval_a16SecdedHealIR_spec]; dsimp only
    rw [hsynd, hclean, hisSec, herrIdx, hne0]
    dsimp only [faulted, expected]
    have h1ne0 : u32Ne 1 0 = true := rfl
    rw [h1ne0]
    simp only [Bool.false_eq_true, ↓reduceIte, hcancel]
    have hded0 : ((((1 : UInt32) &&& ((1 : UInt32) ^^^ 1)) <<< 17)) = 0 := rfl
    rw [hded0, UInt32.or_zero]
  rcases compileToPTX_end_to_end_sound a16SecdedHealIR secdedHealAlloc [faulted] secdedHealAlloc_valid
    with ⟨p1, _, hap1, hptx⟩
  have hp1 : secdedHealPhys = p1 := by unfold secdedHealPhys; rw [hap1]
  refine ⟨by rw [hp1, hptx]; exact hir, ?_⟩
  intro zIn lane hlane
  rcases compileToAVX512_end_to_end_sound a16SecdedHealIR secdedHealAlloc [zIn] lane secdedHealAlloc_valid
    with ⟨p2, _, hap2, havx⟩
  have hp2 : secdedHealPhys = p2 := by unfold secdedHealPhys; rw [hap2]
  simp only [List.map, hlane] at havx
  rw [hp2, havx]
  exact hir

/-- **THEOREM 3 (100% Double-Bit Error Detection & ZERO Miscorrection Across All `2,048 × 120` States)**:
    For EVERY message `msg : UInt32` and EVERY distinct pair `i, j : Fin 16` (`i ≠ j`), both compiled
    zero-spill `sm_86` PTX and 16-lane `AVX-512` `secdedHealPhys` set `isDed = 1` (`bit 17`),
    `isSec = 0` (`bit 16`), and NEVER miscorrect (`healed = faulted`)! -/
theorem a16_ded_100pct_flagged_zero_miscorrect (msg : UInt32) (i j : Fin 16) (hne : i ≠ j) :
    let cw := encodeA16 msg
    let err := ((1 : UInt32) <<< i.val.toUInt32) ^^^ ((1 : UInt32) <<< j.val.toUInt32)
    let faulted := cw ^^^ err
    let expected := faulted ||| ((1 : UInt32) <<< 17)
    evalPTXProg secdedHealPhys [faulted] = expected ∧
    ∀ (zIn : Vec16U32) (lane : Fin 16),
      zIn lane = faulted → evalAVX512Prog secdedHealPhys [zIn] lane = expected := by
  intro cw err faulted expected
  rcases encodeA16_syndrome_zero msg with ⟨hs0, hcwMask⟩
  rcases double_bit_syndrome_exact i j hne with ⟨hsyEq0False, hsyEven, herrMask⟩
  have hsynd : a16SyndromeSpec faulted = a16SyndromeSpec err := by
    dsimp only [faulted, cw]
    rw [a16Syndrome_xor_linear, hs0, UInt32.zero_xor]
  have hclean : (faulted &&& 0xFFFF) = faulted := by
    dsimp only [faulted, cw]
    rw [u32_xor_and_distrib, hcwMask, herrMask]
  have hir : evalProg a16SecdedHealIR [faulted] = expected := by
    rw [eval_a16SecdedHealIR_spec]; dsimp only
    rw [hsynd, hclean, hsyEven, hsyEq0False]
    dsimp only [expected]
    have h0ne0 : u32Ne 0 0 = false := rfl
    have hsec0 : ((0 : UInt32) <<< 16) = 0 := rfl
    rw [h0ne0, hsec0]
    simp only [Bool.false_eq_true, ↓reduceIte, UInt32.or_zero]
    have hded1 : ((1 : UInt32) &&& ((0 : UInt32) ^^^ 1)) = 1 := rfl
    rw [hded1]
  rcases compileToPTX_end_to_end_sound a16SecdedHealIR secdedHealAlloc [faulted] secdedHealAlloc_valid
    with ⟨p1, _, hap1, hptx⟩
  have hp1 : secdedHealPhys = p1 := by unfold secdedHealPhys; rw [hap1]
  refine ⟨by rw [hp1, hptx]; exact hir, ?_⟩
  intro zIn lane hlane
  rcases compileToAVX512_end_to_end_sound a16SecdedHealIR secdedHealAlloc [zIn] lane secdedHealAlloc_valid
    with ⟨p2, _, hap2, havx⟩
  have hp2 : secdedHealPhys = p2 := by unfold secdedHealPhys; rw [hap2]
  simp only [List.map, hlane] at havx
  rw [hp2, havx]
  exact hir

end HoloEmit
