/-
  HoloEmit/RegAlloc.lean

  Fail-closed zero-spill linear-scan register allocator (`allocateZeroSpill`)
  paired with a kernel-transparent boolean certificate validator (`checkValidAlloc`).

  All lookup, membership, non-interference, and budget predicates use primitive
  boolean operations (`Nat.beq`, `Nat.blt`, `Nat.ble`) rather than unary propositional
  `Decidable` recursion so kernel `decide` reduces large programs in `< 50` stack frames.

  Whenever `checkValidAlloc prog m = true`:
  1. `m.spillCount = 0` and `m.maxRegs ≤ 31` (hard zero-spill gate; `%r31` reserved PTX scratch!).
  2. Every virtual register in `prog` maps to a physical register `< m.maxRegs` and `< 31`.
  3. Backward liveness non-interference holds at every instruction step, lifting
     directly to whole-program semantic equivalence (`checkValidAlloc_sound`).
-/

import HoloEmit.IR

namespace HoloEmit

/-- Physical register allocation certificate for a `HoloProg VReg`. -/
structure AllocMap where
  physOf     : List (VReg × PReg)
  spillCount : Nat
  maxRegs    : Nat
  deriving Repr, DecidableEq

/-- Total `O(N)` lookup of `v : VReg` in `AllocMap.physOf` using kernel-primitive `Nat.beq`. -/
def lookupPhysPairs : List (VReg × PReg) → VReg → Option PReg
  | [], _ => none
  | (k, p) :: rest, v => if Nat.beq v k then some p else lookupPhysPairs rest v

def AllocMap.lookup (m : AllocMap) (v : VReg) : Option PReg :=
  lookupPhysPairs m.physOf v

/-- Boolean membership on `List VReg` via primitive `Nat.beq`. -/
def containsVReg (v : VReg) : List VReg → Bool
  | [] => false
  | x :: xs => Nat.beq v x || containsVReg v xs

/-- Set-style membership-deduplicated insertion of `v` into a `List VReg`. -/
def insertLive (v : VReg) (live : List VReg) : List VReg :=
  if containsVReg v live then live else v :: live

def insertManyLive : List VReg → List VReg → List VReg
  | [], live => live
  | u :: us, live => insertLive u (insertManyLive us live)

def eraseLive (d : VReg) : List VReg → List VReg
  | [] => []
  | v :: vs => if Nat.beq v d then eraseLive d vs else v :: eraseLive d vs

/-- Exact backward liveness transfer across one instruction `insn`:
    `liveBefore = insn.usedRegs ∪ (liveAfter \ {insn.defReg})`. -/
def liveBeforeInsn (insn : Insn VReg) (liveAfter : List VReg) : List VReg :=
  insertManyLive insn.usedRegs (eraseLive insn.defReg liveAfter)

/-- Exact backward live-set at the entry of `body` given `liveEnd` at exit. -/
def liveBeforeInsns : List (Insn VReg) → List VReg → List VReg
  | [], liveEnd => liveEnd
  | i :: is, liveEnd => liveBeforeInsn i (liveBeforeInsns is liveEnd)

/-- Translate a single `Insn VReg` into `Insn PReg` if all registers are mapped in `m`. -/
def applyAllocInsn (m : AllocMap) (insn : Insn VReg) : Option (Insn PReg) :=
  match insn with
  | .constU32 dst imm =>
    match m.lookup dst with
    | some d => some (.constU32 d imm)
    | none => none
  | .mov dst src =>
    match m.lookup dst, m.lookup src with
    | some d, some s => some (.mov d s)
    | _, _ => none
  | .and32 dst l r =>
    match m.lookup dst, m.lookup l, m.lookup r with
    | some d, some pl, some pr => some (.and32 d pl pr)
    | _, _, _ => none
  | .or32 dst l r =>
    match m.lookup dst, m.lookup l, m.lookup r with
    | some d, some pl, some pr => some (.or32 d pl pr)
    | _, _, _ => none
  | .xor32 dst l r =>
    match m.lookup dst, m.lookup l, m.lookup r with
    | some d, some pl, some pr => some (.xor32 d pl pr)
    | _, _, _ => none
  | .shlImm dst s sh =>
    match m.lookup dst, m.lookup s with
    | some d, some ps => some (.shlImm d ps sh)
    | _, _ => none
  | .shrImm dst s sh =>
    match m.lookup dst, m.lookup s with
    | some d, some ps => some (.shrImm d ps sh)
    | _, _ => none
  | .shlReg dst l r =>
    match m.lookup dst, m.lookup l, m.lookup r with
    | some d, some pl, some pr => some (.shlReg d pl pr)
    | _, _, _ => none
  | .lop3 imm8 dst a b c =>
    match m.lookup dst, m.lookup a, m.lookup b, m.lookup c with
    | some d, some pa, some pb, some pc => some (.lop3 imm8 d pa pb pc)
    | _, _, _, _ => none
  | .popc dst s =>
    match m.lookup dst, m.lookup s with
    | some d, some ps => some (.popc d ps)
    | _, _ => none
  | .cmpEq dst l r =>
    match m.lookup dst, m.lookup l, m.lookup r with
    | some d, some pl, some pr => some (.cmpEq d pl pr)
    | _, _, _ => none
  | .selp dst c t f =>
    match m.lookup dst, m.lookup c, m.lookup t, m.lookup f with
    | some d, some pc, some pt, some pf => some (.selp d pc pt pf)
    | _, _, _, _ => none

def applyAllocInsns (m : AllocMap) : List (Insn VReg) → Option (List (Insn PReg))
  | [] => some []
  | i :: is =>
    match applyAllocInsn m i, applyAllocInsns m is with
    | some pi, some pis => some (pi :: pis)
    | _, _ => none

def applyAllocParams (m : AllocMap) : List VReg → Option (List PReg)
  | [] => some []
  | p :: ps =>
    match m.lookup p, applyAllocParams m ps with
    | some pp, some pps => some (pp :: pps)
    | _, _ => none

/-- Translate an entire `HoloProg VReg` into `HoloProg PReg` via `m`. -/
def applyAlloc (prog : HoloProg VReg) (m : AllocMap) : Option (HoloProg PReg) :=
  match applyAllocParams m prog.params, applyAllocInsns m prog.body, m.lookup prog.retReg with
  | some pParams, some pBody, some pRet =>
    some { params := pParams, body := pBody, retReg := pRet }
  | _, _, _ => none

/-- Check that every `v ∈ vs` has `m.lookup v = some pv` with `pv ≠ pd` whenever `v ≠ d`. -/
def checkNonInterfere (m : AllocMap) (d : VReg) (pd : PReg) : List VReg → Bool
  | [] => true
  | v :: vs =>
    let okHead : Bool :=
      if Nat.beq v d then true
      else
        match m.lookup v with
        | some pv => !Nat.beq pv.val pd.val
        | none => false
    okHead && checkNonInterfere m d pd vs

/-- Single-pass `O(N)` backward-liveness certificate check across `body`:
    Returns `(ok, liveBeforeBody)` without quadratic recomputation of `liveBeforeInsns`! -/
def checkBodyStepsFast (m : AllocMap) : List (Insn VReg) → List VReg → Bool × List VReg
  | [], liveEnd => (true, liveEnd)
  | i :: is, liveEnd =>
    let resTail := checkBodyStepsFast m is liveEnd
    let liveAfter := resTail.2
    let headOk : Bool :=
      match applyAllocInsn m i, m.lookup i.defReg with
      | some _, some pd => checkNonInterfere m i.defReg pd liveAfter
      | _, _ => false
    (headOk && resTail.1, liveBeforeInsn i liveAfter)

/-- Check that every live register at program entry that is NOT overwritten by later params
    avoids clobbering during `bindParams`. -/
def checkParamInjective (m : AllocMap) : List VReg → List VReg → Bool
  | [], _ => true
  | p :: ps, liveEntry =>
    let headOk : Bool :=
      match m.lookup p with
      | some pp =>
        !containsVReg p ps && checkNonInterfere m p pp (insertManyLive ps liveEntry)
      | none => false
    headOk && checkParamInjective m ps liveEntry

/-- Check that every mapped physical register in `m.physOf` satisfies `p.val < m.maxRegs`
    and `p.val < 31` (`%r31` is reserved as dedicated PTX scratch). -/
def checkBudget (maxRegs : Nat) : List (VReg × PReg) → Bool
  | [] => true
  | (_, p) :: rest => Nat.blt p.val maxRegs && Nat.blt p.val 31 && checkBudget maxRegs rest

/-- Check that every virtual register in `vs` is mapped in `m`. -/
def checkAllMapped (m : AllocMap) : List VReg → Bool
  | [] => true
  | v :: vs =>
    match m.lookup v with
    | some _ => checkAllMapped m vs
    | none => false

/-- Kernel-transparent boolean validator for zero-spill physical register allocation (`O(N)`). -/
def checkValidAlloc (prog : HoloProg VReg) (m : AllocMap) : Bool :=
  let liveEnd : List VReg := [prog.retReg]
  let (bodyOk, liveEntry) := checkBodyStepsFast m prog.body liveEnd
  Nat.beq m.spillCount 0 &&
  Nat.ble m.maxRegs 31 &&
  checkBudget m.maxRegs m.physOf &&
  (m.lookup prog.retReg).isSome &&
  checkAllMapped m liveEntry &&
  checkParamInjective m prog.params liveEntry &&
  bodyOk

/-! ### Executable Fail-Closed Zero-Spill Coalescing Register Allocator (`0` `partial def`) -/

private def allPRegs31 : List PReg :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
   ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩,
   ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩,
   ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩,
   ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩,
   ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩,
   ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩,
   ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩]

private def containsPReg (p : PReg) : List PReg → Bool
  | [] => false
  | q :: qs => Nat.beq p.val q.val || containsPReg p qs

private def findFreeRegList (budget : Nat) (busy : List PReg) : List PReg → Option PReg
  | [] => none
  | cand :: rest =>
    if !Nat.blt cand.val budget then none
    else if containsPReg cand busy then findFreeRegList budget busy rest
    else some cand

private def collectBusyRegs (pairs : List (VReg × PReg)) : List VReg → List PReg
  | [] => []
  | v :: vs =>
    match lookupPhysPairs pairs v with
    | some p => p :: collectBusyRegs pairs vs
    | none => collectBusyRegs pairs vs

/-- Precompute the exact `liveAfter` list for every instruction in `body` in one `O(N)` backward pass. -/
def precomputeLiveAfter : List (Insn VReg) → List VReg → List (Insn VReg × List VReg) × List VReg
  | [], liveEnd => ([], liveEnd)
  | i :: is, liveEnd =>
    let (stepsTail, liveAfter) := precomputeLiveAfter is liveEnd
    ((i, liveAfter) :: stepsTail, liveBeforeInsn i liveAfter)

private def allocLinearTagged (budget : Nat) :
    List (Insn VReg × List VReg) → List (VReg × PReg) → Option (List (VReg × PReg))
  | [], pairs => some pairs
  | (i, liveAfter) :: rest, pairs =>
    let d := i.defReg
    let pairs1? : Option (List (VReg × PReg)) :=
      match lookupPhysPairs pairs d with
      | some _ => some pairs
      | none =>
        let busy := collectBusyRegs pairs (eraseLive d liveAfter)
        let hint? : Option PReg :=
          match i.usedRegs with
          | src :: _ =>
            match lookupPhysPairs pairs src with
            | some ps => if containsPReg ps busy then none else some ps
            | none => none
          | [] => none
        match hint? with
        | some ph => some ((d, ph) :: pairs)
        | none =>
          match findFreeRegList budget busy allPRegs31 with
          | some pf => some ((d, pf) :: pairs)
          | none => none
    match pairs1? with
    | some pairs1 => allocLinearTagged budget rest pairs1
    | none => none

private def allocParams (budget : Nat) (liveEntry : List VReg) :
    List VReg → List (VReg × PReg) → Option (List (VReg × PReg))
  | [], pairs => some pairs
  | p :: ps, pairs =>
    let busy := collectBusyRegs pairs (insertManyLive ps liveEntry)
    match findFreeRegList budget busy allPRegs31 with
    | some pf => allocParams budget liveEntry ps ((p, pf) :: pairs)
    | none => none

private def pRegZero : PReg := ⟨0, by decide⟩

private def allocDeadDefaults (budget : Nat) :
    List VReg → List (VReg × PReg) → Option (List (VReg × PReg))
  | [], pairs => some pairs
  | v :: vs, pairs =>
    match lookupPhysPairs pairs v with
    | some _ => allocDeadDefaults budget vs pairs
    | none =>
      if Nat.blt 0 budget && Nat.ble budget 31 then
        allocDeadDefaults budget vs ((v, pRegZero) :: pairs)
      else none

/-- Fail-closed zero-spill register allocator: allocates `prog` within `maxRegs ≤ 31` registers
    (`%r0..%r30`, keeping `%r31` reserved as PTX scratch) with `spillCount = 0`,
    verifying `checkValidAlloc` before returning `.ok`. -/
def allocateZeroSpill (maxRegs : Nat) (prog : HoloProg VReg) : Except String AllocMap :=
  if Nat.beq maxRegs 0 || !Nat.ble maxRegs 31 then
    .error "INVALID_REGISTER_BUDGET"
  else
    let liveEnd := [prog.retReg]
    let (taggedBody, liveEntry) := precomputeLiveAfter prog.body liveEnd
    match allocParams maxRegs liveEntry prog.params [] with
    | none => .error "SPILL_FORBIDDEN_PARAMS"
    | some pairs0 =>
      match allocLinearTagged maxRegs taggedBody pairs0 with
      | none => .error "SPILL_FORBIDDEN_BODY"
      | some pairs1 =>
        match allocDeadDefaults maxRegs (prog.retReg :: liveEntry) pairs1 with
        | none => .error "SPILL_FORBIDDEN_DEFAULTS"
        | some pairsF =>
          let m : AllocMap := { physOf := pairsF, spillCount := 0, maxRegs := maxRegs }
          if checkValidAlloc prog m then .ok m
          else .error "ALLOC_CERT_REJECTED"

end HoloEmit
