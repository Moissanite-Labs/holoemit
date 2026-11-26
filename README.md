# HoloEmit

**Pure-`Init` `Lean 4.36.0` Zero-Spill `sm_86` PTX & 16-Lane `AVX-512` `[16, 11, 4]` `A_16` SECDED Micro-Compiler**

`HoloEmit` is a clean-room, dependency-free (`"packages": []` in `lake-manifest.json`) **`Lean 4.36.0` verified zero-spill micro-compiler** targeting both NVIDIA Ampere **`sm_86` PTX 7.5** (`lop3.b32`, `popc.b32`, `setp`, `selp.b32`) and Intel **`AVX-512` (`F/BW/VL/VPOPCNTDQ`)** 16-lane `512`-bit intrinsics (`_mm512_ternarylogic_epi32`, `_mm512_popcnt_epi32`, `_mm512_cmpeq_epi32_mask`, `_mm512_mask_blend_epi32`).

Every definition and theorem in `HoloEmit` reduces strictly inside Lean's logical kernel (`0` `Classical.choice`, `0` `Std.Tactic.BVDecide` / `_native.bv_decide.ax_*` compiled C LRAT axioms, `0` `native_decide` / `Lean.ofReduceBool`, `0` `sorryAx`, `0` `partial def`) and replays cleanly from scratch under `lake env leanchecker --fresh HoloEmit`.

---

## Architecture & Trust Boundary

1. **Zero-Spill Register Allocator Translation Validation (`HoloEmit/RegAlloc.lean`):**
   - Pairs an executable, total coalescing linear-scan allocator (`allocateZeroSpill`) over general-purpose physical registers `%r0..%r30` (`allPRegs31`) with a single-pass `O(N)` kernel-transparent boolean validator (`checkValidAlloc`) built exclusively from primitive `Nat.beq`/`Nat.blt`/`Nat.ble` predicates.
   - Reserves `%r31` (`ptxScratchReg`) exclusively for PTX variable-shift mask scratch (`p.val < 31`, `maxRegs ≤ 31`).
   - `checkValidAlloc_zero_spill` (`[propext]` only) proves `m.spillCount = 0 ∧ m.maxRegs ≤ 31`; `checkValidAlloc_sound` proves constructively that physical-register execution on `Fin 32` produces the exact same `UInt32` output as unbounded virtual-register SSA execution (`VReg = Nat`) for all input argument vectors.
2. **Scratch-Faithful Dual-Backend Lowering (`HoloEmit/EmitPTX.lean` & `HoloEmit/EmitAVX512.lean`):**
   - `EmitPTX.lean` explicitly models the `%r31` scratch write inside `execPTXInsn (.shlB32Reg dst l r)` (`regs1 := writeReg st.regs ptxScratchReg (st.regs r &&& 31)` followed by `writeReg regs1 dst (regs1 l <<< regs1 ptxScratchReg)`), matching the emitted `and.b32 %r31, r, 31; shl.b32 d, l, %r31;` PTX sequence, and zero-initializes all non-parameter general-purpose registers `%r0..%r30` (`mov.u32 %rK, 0;`) in `.visible .entry` prologues to match `bindParams` and `EmitAVX512`.
   - `compileToPTX_end_to_end_sound` and `compileToAVX512_end_to_end_sound` compose `checkValidAlloc_sound` with target instruction lowering across `PTXState` and all `16` SIMD lanes (`Fin 16`) of `AVX512State`.
   - `ptx_r31_scratch_clobber_rejected` formally proves that a forged `v0 ↦ %r31` `.shlReg` allocation is rejected by `checkValidAlloc` (under both `maxRegs = 32` and `maxRegs = 31`) and `allocateZeroSpill 32`, and exhibits the exact `64` vs `16` scratch-clobber divergence in `evalPTXProg`.
3. **Pure-Kernel `lop3` / `vpternlogd` & `[16, 11, 4]` `A_16` SECDED Proofs (`HoloEmit/Proofs.lean`):**
   - Proves exact 32-bit ternary truth-table opcodes **`0x96` (`a ^ b ^ c`)**, **`0xE8` (`(a & b) | (a & c) | (b & c)` majority)**, and **`0xCA` (`(a & b) | (~a & c)` mux)** via 8-case per-bit `BitVec.getLsbD` reflection.
   - Proves $GF(2)$ linearity of `popc32` parity (`popc32_parity_xor`) and the `[16, 11, 4]` `A_16` syndrome (`a16Syndrome_xor_linear`), lifting kernel `decide` on the 11 systematic basis words (`DATA_POSITIONS = {3,5,6,7,9,10,11,12,13,14,15}`, `SYNDROME_MASKS = {0xFFFF, 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00}`, compatible with `Moissanite-Labs/holosphere` `include/razor_abi_4byte_sys.h:177-212`) across all `16` SIMD lanes for **all $2^{11} = 2,048$ clean codewords**, **all $32,768$ 1-bit SEC recovery states**, and **all $245,760$ 2-bit DED zero-miscorrection states**.
4. **Explicit Pretty-Printer TCB Boundary:**
   - Symbolic target semantics (`PTXState`/`execPTXInsn` and `AVX512State`/`execAVX512Insn`) are kernel-verified end to end.
   - Textual serialization (`formatPTXInsn`/`renderPTXFunction`, `formatAVX512Insn`/`renderAVX512Function`, and `HoloEmitDump.lean`) forms a minimal syntactic pretty-printer TCB validated downstream by offline `ptxas -arch=sm_86 -v`, `cuobjdump -sass`, and live `gcc -O3 -std=c11 -Wall -Wextra -Werror` `65,536`-word `AVX-512` silicon execution.

---

## Complete 24-Theorem Catalog (`lean/HoloEmit/Proofs.lean`)

| # | Public Theorem | Axiom Footprint | Statement Summary |
| :--- | :--- | :--- | :--- |
| 1 | `evalLop3_getLsbD_eq_lutBool` | `[propext, Quot.sound]` | Every `imm8` of 8-minterm `evalLop3` matches per-bit `evalLutBool` for all `i < 32` |
| 2 | `evalLutBool_0x96_eq_xor` | `[propext, Quot.sound]` | `evalLutBool 0x96 ba bb bc = xor (xor ba bb) bc` |
| 3 | `lop3_0x96_exact` | `[propext, Quot.sound]` | `evalLop3 0x96 a b c = a ^^^ b ^^^ c` over all `UInt32^3` |
| 4 | `vpternlogd_0x96_exact` | `[propext, Quot.sound]` | 16-lane `512`-bit `vpternlogd 0x96` equals exact lane-wise 3-input XOR |
| 5 | `lop3_0xE8_majority_exact` | `[propext, Quot.sound]` | `evalLop3 0xE8 a b c = (a &&& b) \|\|\| (a &&& c) \|\|\| (b &&& c)` |
| 6 | `lop3_0xCA_mux_exact` | `[propext, Quot.sound]` | `evalLop3 0xCA a b c = (a &&& b) \|\|\| (~~~a &&& c)` |
| 7 | `checkValidAlloc_zero_spill` | `[propext]` | `checkValidAlloc prog m = true -> m.spillCount = 0 /\ m.maxRegs <= 31` |
| 8 | `checkValidAlloc_sound` | `[propext, Quot.sound]` | Whole-program `VReg -> Fin 32 PReg` semantic equivalence for any valid `AllocMap` |
| 9 | `lowerInsnPTX_sound` | `[propext, Quot.sound]` | Scratch-aware stepwise soundness of `Insn PReg -> List PTXInsn` on `q != %r31` |
| 10 | `compileToPTX_end_to_end_sound` | `[propext, Quot.sound]` | End-to-end `HoloProg VReg -> RegAlloc (<=31) -> sm_86 PTX` zero-spill soundness |
| 11 | `ptx_r31_scratch_clobber_rejected` | `[propext, Quot.sound]` | Rejects `v0 -> %r31` at `maxRegs=32/31` & `allocateZeroSpill 32`; proves `64` vs `16` clobber |
| 12 | `lowerInsnAVX512_lane_sound` | `[propext, Quot.sound]` | Per-lane soundness of `Insn PReg -> List AVX512Insn` across `Fin 16` |
| 13 | `compileToAVX512_end_to_end_sound` | `[propext, Quot.sound]` | End-to-end `HoloProg VReg -> RegAlloc -> 16-lane AVX-512` SIMD soundness |
| 14 | `foldedParityAlloc_valid` | `[propext]` | Kernel-checked zero-spill certificate (`maxRegs=8`) for `a16FoldedParityIR` |
| 15 | `syndromeAlloc_valid` | `[propext]` | Kernel-checked zero-spill certificate (`maxRegs=8`) for `a16SyndromeIR` |
| 16 | `secdedHealAlloc_valid` | `[propext]` | Kernel-checked zero-spill certificate (`maxRegs=12`) for `a16SecdedHealIR` |
| 17 | `a16FoldedParity_compiled_sound` | `[propext, Quot.sound]` | Compiled PTX & 16-lane AVX-512 match `((w>>1)^(w>>2)^(w>>3)) & 1` via `0x96` LUT |
| 18 | `popc32_parity_xor` | `[propext, Quot.sound]` | `(popc32 (x ^^^ y) &&& 1) = (popc32 x &&& 1) ^^^ (popc32 y &&& 1)` |
| 19 | `a16Syndrome_xor_linear` | `[propext, Quot.sound]` | `a16SyndromeSpec (x ^^^ y) = a16SyndromeSpec x ^^^ a16SyndromeSpec y` |
| 20 | `eval_a16SecdedHealIR_spec` | `[propext, Quot.sound]` | Exact closed-form evaluation of the 47-insn `a16SecdedHealIR` pipeline |
| 21 | `a16Syndrome_compiled_sound` | `[propext, Quot.sound]` | Compiled zero-spill PTX & AVX-512 `syndromePhys` match `razor_a16_secded_syndrome` |
| 22 | `a16_clean_codeword_exact` | `[propext, Quot.sound]` | `0` false alarms & exact codeword preservation on `encodeA16 msg` across all `lane : Fin 16` |
| 23 | `a16_sec_100pct_exact_recovery` | `[propext, Quot.sound]` | `100%` SEC exact recovery + `isSec=1, isDed=0` for all `msg`, `i : Fin 16`, `lane : Fin 16` |
| 24 | `a16_ded_100pct_flagged_zero_miscorrect` | `[propext, Quot.sound]` | `100%` DED flagging (`isDed=1, isSec=0`) + `0` miscorrections for all `i != j : Fin 16`, `lane : Fin 16` |

---

## Hardware & Silicon Verification Summary

### Offline `ptxas -arch=sm_86 -v` & `cuobjdump -sass`
Emitted PTX 7.5 module (`holoemit-dump ptx`, `208` lines, `4,463 B`):

| Emitted `sm_86` Kernel | `HoloIR` Insns | Cert `spillCount` | Cert `maxRegs` | `ptxas` Hardware Regs | Stack / Spill Stores / Spill Loads |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `holo_a16_folded_parity` | `6` | `0` | `8` | **`8`** | **`0 B` / `0 B` / `0 B`** |
| `holo_a16_syndrome` | `29` | `0` | `8` | **`8`** | **`0 B` / `0 B` / `0 B`** |
| `holo_a16_secded_heal` | `47` | `0` | `12` | **`10`** | **`0 B` / `0 B` / `0 B`** |

- **`sm_86` SASS Disassembly (`cuobjdump -sass`):** `21` whole-word `LOP3.LUT` + `9` uniform `ULOP3.LUT` (`30` substring matches), `6` whole-word `POPC` + `4` uniform `UPOPC` (`10` substring matches), **`LDL = 0`, `STL = 0`**.

### Live `AVX-512` (`F/BW/VL/VPOPCNTDQ`) 65,536-Word Parity
- Emitted C11 `<immintrin.h>` header (`holoemit-dump avx512`, `166` lines, `4,961 B`) compiles cleanly with `gcc -O3 -std=c11 -Wall -Wextra -Werror` (`0` warnings).
- Exhaustive execution across all `65,536` 16-bit inputs (`4,096` `zmm` vectors) matches the pure-Python reference specification bit-for-bit (**64-bit FNV-1a digest = `0xefff5bc400f37d25`**).

---

## Quickstart

### Prerequisites
- `Lean 4.36.0` (`leanprover/lean4:v4.36.0` via `elan` or official release archive)
- `Python >= 3.11` (pure standard library; zero third-party packages required)
- *(Optional, for `make test-silicon`)* Offline `CUDA` `ptxas`/`cuobjdump` (`sm_86`) and `GCC` on an `AVX-512` (`F/BW/VL/VPOPCNTDQ`) x86-64 CPU

### Build & Verify
```bash
# 1. Run 3-mode isolated reference verifier & negative-control test suite (< 3 s)
make verify
make test

# 2. Run cold Lean 4.36.0 build (0 warnings), leanchecker --fresh replay, and 24-theorem axiom audit
make lean

# 3. Emit standalone sm_86 PTX 7.5 or C11 AVX-512 header directly
cd lean && lake build holoemit-dump
./.lake/build/bin/holoemit-dump ptx > holoemit.ptx
./.lake/build/bin/holoemit-dump avx512 > holoemit_avx512.h

# 4. Run full end-to-end toolchain & live AVX-512 silicon suite (on sm_86 CUDA + AVX-512 host)
make test-silicon
```

---

## License

Licensed under the [Apache License, Version 2.0](LICENSE).
