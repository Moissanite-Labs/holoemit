#!/usr/bin/env python3
"""
Negative-Control & Refusal-Path Unit Test Suite for HoloEmit (`verify_holoemit.py`).

Pure Python 3 standard library. Zero bare asserts, zero floats, zero host-path dependencies.
"""
from __future__ import annotations

import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))
import verify_holoemit as vmod


class TestHoloEmitVerify(unittest.TestCase):
    def test_01_lut_opcodes_and_negative_controls(self) -> None:
        res = vmod.verify_lut_opcodes()
        self.assertEqual(res["checked_u32_triples"], 128)
        self.assertEqual(res["lut_opcodes_verified"], ["0x96", "0xE8", "0xCA"])
        for ba in (0, 1):
            for bb in (0, 1):
                for bc in (0, 1):
                    self.assertEqual(vmod.eval_lut_bool(0x96, ba, bb, bc), ba ^ bb ^ bc)
                    self.assertEqual(vmod.eval_lut_bool(0xE8, ba, bb, bc), (ba & bb) | (ba & bc) | (bb & bc))
                    self.assertEqual(vmod.eval_lut_bool(0xCA, ba, bb, bc), (ba & bb) | ((1 - ba) & bc))
        self.assertNotEqual(vmod.eval_lop3_u32(0x97, 0, 0, 0), 0)
        self.assertEqual(
            vmod.eval_lop3_u32(0x96, 0xF0F0CCAA, 0x55555555, 0x12345678),
            0xF0F0CCAA ^ 0x55555555 ^ 0x12345678,
        )
        self.assertEqual(vmod.folded_upper_parity_spec(0b1110), 1)
        self.assertEqual(vmod.folded_upper_parity_spec(0b1100), 0)
        self.assertEqual(vmod.folded_upper_parity_spec(0b0010), 1)
        self.assertEqual(vmod.popc32(0xFFFFFFFF), 32)
        self.assertEqual(vmod.popc32(0x80000001), 2)

        # Negative controls for every guard in verify_lut_opcodes
        for bad_imm in (0x96, 0xE8, 0xCA):
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lut_opcodes(
                    eval_lut_fn=lambda imm, a, b, c, bi=bad_imm: (
                        1 ^ vmod.eval_lut_bool(imm, a, b, c) if imm == bi else vmod.eval_lut_bool(imm, a, b, c)
                    )
                )
        with self.assertRaises(vmod.HoloEmitVerifyError):
            vmod.verify_lut_opcodes(folded_fn=lambda a: 1 ^ vmod.folded_upper_parity_spec(a))
        with self.assertRaises(vmod.HoloEmitVerifyError):
            vmod.verify_lut_opcodes(
                eval_lop3_fn=lambda imm, a, b, c: (
                    1 ^ vmod.eval_lop3_u32(imm, a, b, c)
                    if (imm == 0x96 and b == 0xFFFFFFFF)
                    else vmod.eval_lop3_u32(imm, a, b, c)
                )
            )
        for bad_imm in (0xE8, 0xCA):
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lut_opcodes(
                    eval_lop3_fn=lambda imm, a, b, c, bi=bad_imm: (
                        1 ^ vmod.eval_lop3_u32(imm, a, b, c) if imm == bi else vmod.eval_lop3_u32(imm, a, b, c)
                    )
                )

    def test_02_a16_basis_and_encoder_algebra(self) -> None:
        self.assertEqual(len(vmod.DATA_POSITIONS), 11)
        self.assertEqual(vmod.DATA_POSITIONS, (3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15))
        self.assertEqual(vmod.SYNDROME_MASKS, (0xFFFF, 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00))
        for k, d_pos in enumerate(vmod.DATA_POSITIONS):
            bw = vmod.a16_basis_word(d_pos)
            self.assertEqual(vmod.encode_a16(1 << k), bw)
            self.assertEqual(vmod.a16_syndrome_spec(bw), 0)
            self.assertEqual((bw >> d_pos) & 1, 1)
            self.assertEqual(vmod.popc32(bw) & 1, 0)
            self.assertGreaterEqual(vmod.popc32(bw), 4)
        for m1, m2 in ((0x155, 0x6AA), (0x7FF, 0x3C3), (0x001, 0x400)):
            self.assertEqual(vmod.encode_a16(m1 ^ m2), vmod.encode_a16(m1) ^ vmod.encode_a16(m2))
        for x, y in ((0xBEEF, 0x1234), (0xFFFF, 0x8001), (0x0002, 0x0100)):
            self.assertEqual(vmod.a16_syndrome_spec(x ^ y), vmod.a16_syndrome_spec(x) ^ vmod.a16_syndrome_spec(y))

    def test_03_secded_heal_exact_and_negative_controls(self) -> None:
        res = vmod.verify_a16_secded_exhaustive()
        self.assertEqual(res["codebook_size"], 2048)
        self.assertEqual(res["min_hamming_distance"], 4)
        self.assertEqual(res["sec_states_verified"], 32768)
        self.assertEqual(res["double_bit_masks_verified"], 120)
        self.assertEqual(res["ded_codeword_states_spot_verified"], 720)
        cw = vmod.encode_a16(0x5A5)
        self.assertEqual(vmod.secded_heal_spec(cw), cw)
        for bit_i in range(16):
            healed_pack = vmod.secded_heal_spec(cw ^ (1 << bit_i))
            self.assertEqual(healed_pack & 0xFFFF, cw)
            self.assertEqual((healed_pack >> 16) & 1, 1)
            self.assertEqual((healed_pack >> 17) & 1, 0)
        dbl = cw ^ (1 << 0) ^ (1 << 15)
        ded_pack = vmod.secded_heal_spec(dbl)
        self.assertEqual(ded_pack & 0xFFFF, dbl)
        self.assertEqual((ded_pack >> 16) & 1, 0)
        self.assertEqual((ded_pack >> 17) & 1, 1)

        # Negative controls for every guard in verify_a16_secded_exhaustive:
        for oob_cw in (-1, 0x10000):
            with self.assertRaisesRegex(vmod.HoloEmitVerifyError, r"^CW_RANGE_FAIL:"):
                vmod.verify_a16_secded_exhaustive(
                    encode_fn=lambda m, bad=oob_cw: bad if m == 0 else vmod.encode_a16(m),
                    syndrome_fn=lambda _: 0,
                    heal_fn=lambda w: w,
                )
        with self.assertRaisesRegex(vmod.HoloEmitVerifyError, r"^CLEAN_SYND_FAIL:"):
            vmod.verify_a16_secded_exhaustive(
                syndrome_fn=lambda w: 2 if w == 0 else vmod.a16_syndrome_spec(w)
            )
        with self.assertRaisesRegex(vmod.HoloEmitVerifyError, r"^CLEAN_HEAL_FAIL:"):
            vmod.verify_a16_secded_exhaustive(
                heal_fn=lambda w: 1 if w == 0 else vmod.secded_heal_spec(w)
            )
        with self.assertRaisesRegex(vmod.HoloEmitVerifyError, r"^CODEBOOK_INJECTIVITY_FAIL:"):
            vmod.verify_a16_secded_exhaustive(
                encode_fn=lambda m: vmod.encode_a16(1) if m == 2047 else vmod.encode_a16(m)
            )
        with self.assertRaisesRegex(vmod.HoloEmitVerifyError, r"^MIN_DIST_FAIL:"):
            vmod.verify_a16_secded_exhaustive(
                encode_fn=lambda m: 3 if m == 1 else vmod.encode_a16(m),
                syndrome_fn=lambda _: 0,
                heal_fn=lambda w: w,
            )
        with self.assertRaises(vmod.HoloEmitVerifyError):
            vmod.verify_a16_secded_exhaustive(
                heal_fn=lambda w: 0 if w == 1 else vmod.secded_heal_spec(w)
            )
        for bad_synd in (0, 1):
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_a16_secded_exhaustive(
                    syndrome_fn=lambda w, bs=bad_synd: bs if w == 3 else vmod.a16_syndrome_spec(w)
                )
        with self.assertRaises(vmod.HoloEmitVerifyError):
            vmod.verify_a16_secded_exhaustive(bit_width=15)
        with self.assertRaises(vmod.HoloEmitVerifyError):
            vmod.verify_a16_secded_exhaustive(
                heal_fn=lambda w: 0 if w == 3 else vmod.secded_heal_spec(w)
            )

    def test_04_trust_boundary_detector_positive_and_negative(self) -> None:
        clean_src = """
        -- line comment mentioning bv_decide and sorry
        /- nested /- block comment with bv_decide -/ ignored -/
        import HoloEmit.IR
        def escaped : String := "quote \\" bv_decide Classical.choice"
        theorem t (a : UInt32) : a = a := rfl
        """
        clean_axioms = [
            "",
            "'HoloEmit.t' does not depend on any axioms",
            "'HoloEmit.u' depends on axioms: [propext]",
            "'HoloEmit.v' depends on axioms: [propext, Quot.sound]",
        ]
        self.assertEqual(vmod.detect_lean4_bv_decide_escapes(clean_src, clean_axioms), [])

        self.assertIn(
            "LEAN4_BV_DECIDE_IMPORT",
            vmod.detect_lean4_bv_decide_escapes("import Std.Tactic.BVDecide\n", []),
        )
        self.assertIn(
            "LEAN4_BV_DECIDE_NATIVE",
            vmod.detect_lean4_bv_decide_escapes("theorem x : 1 = 1 := by bv_decide\n", []),
        )
        self.assertIn(
            "LEAN4_BV_DECIDE_NATIVE",
            vmod.detect_lean4_bv_decide_escapes("theorem x : 1 = 1 := by bv_normalize\n", []),
        )
        self.assertIn(
            "LEAN4_CLASSICAL_OR_UNSOUND_TACTIC",
            vmod.detect_lean4_bv_decide_escapes("theorem x (P : Prop) : P := by sorry\n", []),
        )
        self.assertIn(
            "LEAN4_CLASSICAL_OR_UNSOUND_TACTIC",
            vmod.detect_lean4_bv_decide_escapes("theorem x : 1 = 1 := by by_cases h : 1 = 1 <;> rfl\n", []),
        )
        self.assertIn(
            "LEAN4_PARTIAL_DECL",
            vmod.detect_lean4_bv_decide_escapes("partial def loop (x : Nat) : Nat := loop x\n", []),
        )
        ax_bv = ["'Foo.bar' depends on axioms: [propext, Quot.sound, Foo.bar._native.bv_decide.ax_1_15]"]
        findings_bv = vmod.detect_lean4_bv_decide_escapes("theorem bar : 1 = 1 := rfl\n", ax_bv)
        self.assertTrue(any(f.startswith("LEAN4_NATIVE_EVAL_AXIOM:") for f in findings_bv))

        ax_choice = ["'Foo.baz' depends on axioms: [propext, Classical.choice, Quot.sound]"]
        self.assertIn(
            "LEAN4_CLASSICAL_CHOICE_AXIOM",
            vmod.detect_lean4_bv_decide_escapes("theorem baz : 1 = 1 := rfl\n", ax_choice),
        )
        ax_custom = ["'Foo.custom' depends on axioms: [myCustomAxiom]"]
        self.assertIn(
            "LEAN4_NON_CONSTRUCTIVE_AXIOM:myCustomAxiom",
            vmod.detect_lean4_bv_decide_escapes("theorem custom : 1 = 1 := rfl\n", ax_custom),
        )
        self.assertEqual(
            vmod.detect_lean4_bv_decide_escapes("", ["unrecognized line"]),
            ["UNRECOGNIZED_AXIOM_OUTPUT:unrecognized line"],
        )
        with self.assertRaises(vmod.HoloEmitVerifyError):
            vmod.strip_lean_comments_and_strings("/- unterminated comment")
        with self.assertRaises(vmod.HoloEmitVerifyError):
            vmod.strip_lean_comments_and_strings('def s := "unterminated string')
        self.assertIn(
            "LEAN4_BV_DECIDE_NATIVE",
            vmod.detect_lean4_bv_decide_escapes("theorem sub_ok : 2 - 1 = 1 := by bv_decide\n", []),
        )
        for bad_rhs in ("propext", "[propext", "propext]"):
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.detect_lean4_bv_decide_escapes("", [f"'Foo.x' depends on axioms: {bad_rhs}"])

    def test_05_require_and_static_tree_negative_controls(self) -> None:
        with self.assertRaises(vmod.HoloEmitVerifyError):
            vmod.require(False, "TEST_ERR", "must fail")

        full = vmod.run_verification(REPO_ROOT)
        self.assertEqual(full["artifact"], "HoloEmit")
        self.assertEqual(full["lean_static"]["lean_files"], 8)
        self.assertEqual(full["lean_static"]["public_theorems_audited"], 24)
        self.assertEqual(len(full["payload_sha256"]), 64)

        with tempfile.TemporaryDirectory() as td:
            empty_dir = Path(td) / "missing_lean"
            empty_dir.mkdir()
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lean_sources_static(empty_dir)

            tmp_repo = Path(td) / "copy"
            shutil.copytree(REPO_ROOT / "lean", tmp_repo / "lean")

            # Bad toolchain
            (tmp_repo / "lean" / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n", encoding="utf-8")
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lean_sources_static(tmp_repo)
            (tmp_repo / "lean" / "lean-toolchain").write_text("leanprover/lean4:v4.36.0\n", encoding="utf-8")

            # Non-empty packages in lake-manifest.json
            orig_manifest = (tmp_repo / "lean" / "lake-manifest.json").read_text(encoding="utf-8")
            (tmp_repo / "lean" / "lake-manifest.json").write_text(
                json.dumps({"version": "1.1.0", "packages": [{"name": "batteries"}]}), encoding="utf-8"
            )
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lean_sources_static(tmp_repo)
            (tmp_repo / "lean" / "lake-manifest.json").write_text(orig_manifest, encoding="utf-8")

            # Extra .lean file count check
            extra_lean = tmp_repo / "lean" / "Extra.lean"
            extra_lean.write_text("theorem extra_t : 1 = 1 := rfl\n", encoding="utf-8")
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lean_sources_static(tmp_repo)
            extra_lean.unlink()

            # Static escape inside .lean source
            orig_holo = (tmp_repo / "lean" / "HoloEmit.lean").read_text(encoding="utf-8")
            (tmp_repo / "lean" / "HoloEmit.lean").write_text("theorem bad : 1 = 1 := by bv_decide\n", encoding="utf-8")
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lean_sources_static(tmp_repo)

            # Forbidden non-HoloEmit import
            (tmp_repo / "lean" / "HoloEmit.lean").write_text("import Init.Data.BitVec\n", encoding="utf-8")
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lean_sources_static(tmp_repo)
            (tmp_repo / "lean" / "HoloEmit.lean").write_text(orig_holo, encoding="utf-8")

            # Mismatched AxiomAudit.lean theorem list (same Proofs.lean count=24, broken AxiomAudit.lean)
            orig_ax = (tmp_repo / "lean" / "AxiomAudit.lean").read_text(encoding="utf-8")
            (tmp_repo / "lean" / "AxiomAudit.lean").write_text("#print axioms HoloEmit.lop3_0x96_exact\n", encoding="utf-8")
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lean_sources_static(tmp_repo)
            (tmp_repo / "lean" / "AxiomAudit.lean").write_text(orig_ax, encoding="utf-8")

            # Mismatched public theorem count (25 != 24) while keeping AxiomAudit.lean in 1-to-1 sync
            proofs_p = tmp_repo / "lean" / "HoloEmit" / "Proofs.lean"
            proofs_p.write_text(proofs_p.read_text(encoding="utf-8") + "\ntheorem extra_pub : 1 = 1 := rfl\n", encoding="utf-8")
            (tmp_repo / "lean" / "AxiomAudit.lean").write_text(
                orig_ax + "\n#print axioms HoloEmit.extra_pub\n", encoding="utf-8"
            )
            with self.assertRaises(vmod.HoloEmitVerifyError):
                vmod.verify_lean_sources_static(tmp_repo)


if __name__ == "__main__":
    unittest.main()
