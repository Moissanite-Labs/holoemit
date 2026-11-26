import HoloEmit

open HoloEmit

def main (args : List String) : IO UInt32 := do
  match args with
  | ["ptx"] =>
    IO.print (renderPTXModule [
      ("holo_a16_folded_parity", foldedParityPhys),
      ("holo_a16_syndrome", syndromePhys),
      ("holo_a16_secded_heal", secdedHealPhys)
    ])
    return 0
  | ["avx512"] =>
    IO.print (renderAVX512Header [
      ("holo_a16_folded_parity_avx512", foldedParityAlloc.maxRegs, foldedParityPhys),
      ("holo_a16_syndrome_avx512", syndromeAlloc.maxRegs, syndromePhys),
      ("holo_a16_secded_heal_avx512", secdedHealAlloc.maxRegs, secdedHealPhys)
    ])
    return 0
  | ["summary"] =>
    IO.println s!"folded_parity: spill={foldedParityAlloc.spillCount} maxRegs={foldedParityAlloc.maxRegs} insns={foldedParityPhys.body.length}"
    IO.println s!"syndrome:      spill={syndromeAlloc.spillCount} maxRegs={syndromeAlloc.maxRegs} insns={syndromePhys.body.length}"
    IO.println s!"secded_heal:   spill={secdedHealAlloc.spillCount} maxRegs={secdedHealAlloc.maxRegs} insns={secdedHealPhys.body.length}"
    return 0
  | _ =>
    IO.eprintln "usage: holoemit-dump [ptx|avx512|summary]"
    return 1
