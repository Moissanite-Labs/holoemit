#!/usr/bin/env python3
"""
Deterministic Pure-Python Reference Verifier & Lean 4.36.0 Trust-Boundary Gate
for HoloEmit (Pure-Init Zero-Spill HoloIR -> sm_86 PTX / 16-Lane AVX-512).

Zero floats, zero bare asserts, zero unseeded RNG, zero host-path dependencies.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any


class HoloEmitVerifyError(ValueError):
    """Fail-closed verification error for HoloEmit."""


DATA_POSITIONS: tuple[int, ...] = (3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15)
SYNDROME_MASKS: tuple[int, ...] = (0xFFFF, 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00)
PURE_CONSTRUCTIVE_AXIOMS: frozenset[str] = frozenset({"propext", "Quot.sound"})

_BV_DECIDE_TACTIC_RE = re.compile(r"\bbv_decide\b|\bbv_normalize\b")
_BV_DECIDE_IMPORT_RE = re.compile(r"(?:^|\n)[ \t]*import[ \t]+Std\.Tactic\.BVDecide\b")
_NATIVE_AXIOM_RE = re.compile(
    r"(?:\bLean\.(?:ofReduceBool|trustCompiler)\b|\._native\.(?:bv_decide|decide|ax_))"
)
_CLASSICAL_TACTIC_RE = re.compile(r"\b(?:by_cases|by_contra|Classical\.|grind|native_decide|sorry|admit)\b")
_PARTIAL_DECL_RE = re.compile(r"(?<!\.)\bpartial\s+(?:def|instance|abbrev)\b")
_PUB_THM_RE = re.compile(r"^[ \t]*theorem[ \t]+([A-Za-z0-9_']+)", flags=re.MULTILINE)
_PRINT_AXIOMS_RE = re.compile(r"^[ \t]*#print[ \t]+axioms[ \t]+HoloEmit\.([A-Za-z0-9_']+)", flags=re.MULTILINE)


def require(cond: bool, code: str, msg: str) -> None:
    if not cond:
        raise HoloEmitVerifyError(f"{code}: {msg}")


def popc32(x: int) -> int:
    return int(x & 0xFFFFFFFF).bit_count()


def eval_lut_bool(imm8: int, ba: int, bb: int, bc: int) -> int:
    idx = ((ba & 1) << 2) | ((bb & 1) << 1) | (bc & 1)
    return ((imm8 & 0xFF) >> idx) & 1


def eval_lop3_u32(imm8: int, a: int, b: int, c: int) -> int:
    u_a = a & 0xFFFFFFFF
    u_b = b & 0xFFFFFFFF
    u_c = c & 0xFFFFFFFF
    na = (~u_a) & 0xFFFFFFFF
    nb = (~u_b) & 0xFFFFFFFF
    nc = (~u_c) & 0xFFFFFFFF
    terms = (
        (na & nb & nc),
        (na & nb & u_c),
        (na & u_b & nc),
        (na & u_b & u_c),
        (u_a & nb & nc),
        (u_a & nb & u_c),
        (u_a & u_b & nc),
        (u_a & u_b & u_c),
    )
    acc = 0
    for bit_idx, mask_term in enumerate(terms):
        if ((imm8 >> bit_idx) & 1) == 1:
            acc |= mask_term
    return acc & 0xFFFFFFFF


def folded_upper_parity_spec(w: int) -> int:
    u = w & 0xFFFFFFFF
    return (((u >> 1) ^ (u >> 2) ^ (u >> 3)) & 1)


def a16_syndrome_spec(w16: int) -> int:
    u = w16 & 0xFFFFFFFF
    synd = 0
    for bit_pos, mask in enumerate(SYNDROME_MASKS):
        p = popc32(u & mask) & 1
        synd |= p << bit_pos
    return synd


def a16_basis_word(d_pos: int) -> int:
    d_bit = 1 << d_pos
    p1 = 2 if (d_pos & 1) != 0 else 0
    p2 = 4 if (d_pos & 2) != 0 else 0
    p3 = 16 if (d_pos & 4) != 0 else 0
    p4 = 256 if (d_pos & 8) != 0 else 0
    core = d_bit ^ p1 ^ p2 ^ p3 ^ p4
    p0 = popc32(core) & 1
    return core ^ p0


def encode_a16(msg: int) -> int:
    cw = 0
    for k, d_pos in enumerate(DATA_POSITIONS):
        if ((msg >> k) & 1) == 1:
            cw ^= a16_basis_word(d_pos)
    return cw


def secded_heal_spec(w16: int) -> int:
    synd = a16_syndrome_spec(w16)
    w_clean = w16 & 0xFFFF
    is_sec = synd & 1
    err_idx = (synd >> 1) & 0xF
    healed = (w_clean ^ (1 << err_idx)) if is_sec != 0 else w_clean
    is_ded = (0 if synd == 0 else 1) & (is_sec ^ 1)
    return healed | (is_sec << 16) | (is_ded << 17)


def strip_lean_comments_and_strings(src: str) -> str:
    out: list[str] = []
    i = 0
    n = len(src)
    depth = 0
    in_str = False
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_str:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            elif ch == '"':
                in_str = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif ch == '"':
            in_str = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    require(depth == 0 and not in_str, "LEAN_UNTERMINATED_LITERAL", "Unterminated Lean comment or string")
    return "".join(out)


def detect_lean4_bv_decide_escapes(lean_source: str, axiom_lines: list[str]) -> list[str]:
    """
    Pure-kernel trust-boundary detector: catches `Std.Tactic.BVDecide` imports,
    `bv_decide` / `bv_normalize` tactics, and `<decl>._native.bv_decide.ax_*`
    or any axiom outside `PURE_CONSTRUCTIVE_AXIOMS`.
    """
    cleaned = strip_lean_comments_and_strings(lean_source)
    findings: list[str] = []
    if _BV_DECIDE_IMPORT_RE.search(cleaned):
        findings.append("LEAN4_BV_DECIDE_IMPORT")
    if _BV_DECIDE_TACTIC_RE.search(cleaned):
        findings.append("LEAN4_BV_DECIDE_NATIVE")
    if _CLASSICAL_TACTIC_RE.search(cleaned):
        findings.append("LEAN4_CLASSICAL_OR_UNSOUND_TACTIC")
    if _PARTIAL_DECL_RE.search(cleaned):
        findings.append("LEAN4_PARTIAL_DECL")

    for raw_ln in axiom_lines:
        ln = raw_ln.strip()
        if not ln:
            continue
        if "does not depend on any axioms" in ln:
            continue
        if "depends on axioms:" in ln:
            rhs = ln.split("depends on axioms:", 1)[1].strip()
            require(rhs.startswith("[") and rhs.endswith("]"), "BAD_AXIOM_LINE", f"Malformed axiom list: {ln}")
            axioms = [a.strip() for a in rhs[1:-1].split(",") if a.strip()]
            for ax in axioms:
                if _NATIVE_AXIOM_RE.search(ax):
                    findings.append(f"LEAN4_NATIVE_EVAL_AXIOM:{ax}")
                elif ax == "Classical.choice":
                    findings.append("LEAN4_CLASSICAL_CHOICE_AXIOM")
                elif ax not in PURE_CONSTRUCTIVE_AXIOMS:
                    findings.append(f"LEAN4_NON_CONSTRUCTIVE_AXIOM:{ax}")
        else:
            findings.append(f"UNRECOGNIZED_AXIOM_OUTPUT:{ln[:60]}")
    return findings


def verify_lut_opcodes(
    eval_lut_fn: Any = eval_lut_bool,
    eval_lop3_fn: Any = eval_lop3_u32,
    folded_fn: Any = folded_upper_parity_spec,
) -> dict[str, Any]:
    test_words = (
        0x00000000,
        0xFFFFFFFF,
        0xAAAAAAAA,
        0x55555555,
        0xF0F0CCAA,
        0x12345678,
        0x9ABCDEF0,
        0x80000001,
    )
    for ba in (0, 1):
        for bb in (0, 1):
            for bc in (0, 1):
                require(
                    eval_lut_fn(0x96, ba, bb, bc) == (ba ^ bb ^ bc),
                    "LUT_0X96_BIT_FAIL",
                    f"0x96 mismatch at {(ba, bb, bc)}",
                )
                require(
                    eval_lut_fn(0xE8, ba, bb, bc) == ((ba & bb) | (ba & bc) | (bb & bc)),
                    "LUT_0XE8_BIT_FAIL",
                    f"0xE8 mismatch at {(ba, bb, bc)}",
                )
                require(
                    eval_lut_fn(0xCA, ba, bb, bc) == ((ba & bb) | ((1 - ba) & bc)),
                    "LUT_0XCA_BIT_FAIL",
                    f"0xCA mismatch at {(ba, bb, bc)}",
                )
    checked_triples = 0
    for a in test_words:
        require(
            (eval_lop3_fn(0x96, a >> 1, a >> 2, a >> 3) & 1) == folded_fn(a),
            "FOLDED_PARITY_FAIL",
            f"Folded parity mismatch on {a:#x}",
        )
        for b in test_words[:4]:
            for c in test_words[:4]:
                require(
                    eval_lop3_fn(0x96, a, b, c) == ((a ^ b ^ c) & 0xFFFFFFFF),
                    "LOP3_0X96_U32_FAIL",
                    "32-bit 0x96 XOR mismatch",
                )
                require(
                    eval_lop3_fn(0xE8, a, b, c) == (((a & b) | (a & c) | (b & c)) & 0xFFFFFFFF),
                    "LOP3_0XE8_U32_FAIL",
                    "32-bit 0xE8 majority mismatch",
                )
                require(
                    eval_lop3_fn(0xCA, a, b, c) == (((a & b) | ((~a & 0xFFFFFFFF) & c)) & 0xFFFFFFFF),
                    "LOP3_0XCA_U32_FAIL",
                    "32-bit 0xCA mux mismatch",
                )
                checked_triples += 1
    return {"checked_u32_triples": checked_triples, "lut_opcodes_verified": ["0x96", "0xE8", "0xCA"]}


def verify_a16_secded_exhaustive(
    encode_fn: Any = encode_a16,
    syndrome_fn: Any = a16_syndrome_spec,
    heal_fn: Any = secded_heal_spec,
    bit_width: int = 16,
) -> dict[str, Any]:
    codebook: list[int] = []
    min_nonzero_weight = 32
    for msg in range(2048):
        cw = encode_fn(msg)
        require(0 <= cw <= 0xFFFF, "CW_RANGE_FAIL", f"Codeword out of 16-bit range: {cw}")
        require(syndrome_fn(cw) == 0, "CLEAN_SYND_FAIL", f"Nonzero syndrome on msg={msg}")
        require(heal_fn(cw) == cw, "CLEAN_HEAL_FAIL", f"Clean heal altered msg={msg}")
        if msg != 0:
            w = popc32(cw)
            if w < min_nonzero_weight:
                min_nonzero_weight = w
        codebook.append(cw)

    require(len(set(codebook)) == 2048, "CODEBOOK_INJECTIVITY_FAIL", "Codebook size != 2048")
    require(min_nonzero_weight == 4, "MIN_DIST_FAIL", f"Expected d_min=4, got {min_nonzero_weight}")

    # Exhaustive 2,048 x 16 = 32,768 single-bit flips
    sec_states = 0
    for cw in codebook:
        for bit_i in range(bit_width):
            faulted = cw ^ (1 << bit_i)
            out = heal_fn(faulted)
            require(out == (cw | (1 << 16)), "SEC_RECOVERY_FAIL", f"SEC failed at cw={cw:#x}, bit={bit_i}")
            sec_states += 1

    # Exhaustive 120 double-bit error masks verified by linearity + sampled full-codebook sweep
    double_masks: list[int] = []
    for i in range(bit_width):
        for j in range(i + 1, bit_width):
            err = (1 << i) ^ (1 << j)
            synd = syndrome_fn(err)
            require(synd != 0 and (synd & 1) == 0, "DED_BASIS_FAIL", f"Bad double-bit syndrome at {(i, j)}")
            double_masks.append(err)
    require(len(double_masks) == 120, "DED_MASK_COUNT_FAIL", "Expected 120 double-bit masks")

    ded_states = 0
    for msg_idx in (0, 1, 42, 682, 1365, 2047):
        cw = codebook[msg_idx]
        for err in double_masks:
            faulted = cw ^ err
            out = heal_fn(faulted)
            require(out == (faulted | (1 << 17)), "DED_FLAG_FAIL", f"DED misbehaved at msg={msg_idx}")
            ded_states += 1

    return {
        "codebook_size": len(codebook),
        "min_hamming_distance": min_nonzero_weight,
        "sec_states_verified": sec_states,
        "double_bit_masks_verified": len(double_masks),
        "ded_codeword_states_spot_verified": ded_states,
    }


def verify_lean_sources_static(repo_dir: Path) -> dict[str, Any]:
    lean_dir = repo_dir / "lean"
    require(lean_dir.is_dir(), "MISSING_LEAN_DIR", "lean/ directory missing")
    toolchain = (lean_dir / "lean-toolchain").read_text(encoding="utf-8").strip()
    require(toolchain == "leanprover/lean4:v4.36.0", "BAD_TOOLCHAIN", f"Unexpected toolchain: {toolchain}")

    manifest = json.loads((lean_dir / "lake-manifest.json").read_text(encoding="utf-8"))
    require(manifest.get("packages") == [], "NON_EMPTY_PACKAGES", "External Lean packages forbidden")

    lean_files = sorted(lean_dir.rglob("*.lean"))
    require(len(lean_files) == 8, "LEAN_FILE_COUNT_FAIL", f"Expected 8 .lean files, found {len(lean_files)}")

    total_loc = 0
    for lf in lean_files:
        src = lf.read_text(encoding="utf-8")
        total_loc += len(src.splitlines())
        escapes = detect_lean4_bv_decide_escapes(src, [])
        require(not escapes, "STATIC_LEAN_ESCAPE", f"{lf.name}: {escapes}")
        cleaned = strip_lean_comments_and_strings(src)
        for m_imp in re.finditer(r"(?:^|\n)[ \t]*import[ \t]+([A-Za-z0-9_.]+)", cleaned):
            mod = m_imp.group(1)
            require(
                mod == "HoloEmit" or mod.startswith("HoloEmit."),
                "FORBIDDEN_IMPORT",
                f"{lf.name} imports non-HoloEmit module {mod}",
            )

    proofs_src = strip_lean_comments_and_strings(
        (lean_dir / "HoloEmit" / "Proofs.lean").read_text(encoding="utf-8")
    )
    pub_thms = _PUB_THM_RE.findall(proofs_src)
    audit_src = (lean_dir / "AxiomAudit.lean").read_text(encoding="utf-8")
    audited_thms = _PRINT_AXIOMS_RE.findall(audit_src)
    require(len(pub_thms) == 24, "PUB_THM_COUNT_FAIL", f"Expected 24 public theorems, got {len(pub_thms)}")
    require(pub_thms == audited_thms, "AXIOM_AUDIT_MISMATCH", "AxiomAudit.lean does not match Proofs.lean")

    return {
        "lean_toolchain": toolchain,
        "lean_files": len(lean_files),
        "lean_loc": total_loc,
        "public_theorems_audited": len(pub_thms),
    }


def run_verification(repo_dir: Path | None = None) -> dict[str, Any]:
    base = repo_dir if repo_dir is not None else Path(__file__).resolve().parent
    lut_res = verify_lut_opcodes()
    secded_res = verify_a16_secded_exhaustive()
    lean_res = verify_lean_sources_static(base)

    payload = {
        "artifact": "HoloEmit",
        "lut": lut_res,
        "a16_secded": secded_res,
        "lean_static": lean_res,
    }
    canon = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    payload["payload_sha256"] = hashlib.sha256(canon).hexdigest()
    return payload


def main() -> int:
    res = run_verification()
    print(json.dumps(res, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
