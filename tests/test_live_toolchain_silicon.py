#!/usr/bin/env python3
"""
Live Cold Lean 4.36.0 (`lake build` + `leanchecker --fresh` + `AxiomAudit.lean`) +
Offline `sm_86` `ptxas -v` / `cuobjdump -sass` + `AVX-512` 65,536-Word
End-to-End Silicon Suite for HoloEmit.

CPU-only (`CUDA_VISIBLE_DEVICES=""`), zero `.lake` or binary residue in the repository.
"""
from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))
import verify_holoemit as vmod


def _scrubbed_lean_env() -> dict[str, str]:
    home = os.path.expanduser("~")
    elan_bin = str(Path(home) / ".elan" / "bin")
    return {
        "PATH": f"{elan_bin}:/opt/cuda/bin:/usr/bin:/bin",
        "HOME": home,
        "CUDA_VISIBLE_DEVICES": "",
        "OPENBLAS_NUM_THREADS": "1",
        "OMP_NUM_THREADS": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
    }


class TestHoloEmitLiveToolchainSilicon(unittest.TestCase):
    def test_live_cold_lean436_ptxas_sass_and_avx512_silicon(self) -> None:
        env = _scrubbed_lean_env()
        with tempfile.TemporaryDirectory() as td:
            tmp_lean = Path(td) / "lean"
            shutil.copytree(REPO_ROOT / "lean", tmp_lean)

            # 1. Cold scrubbed lake build (0 warnings)
            r_build = subprocess.run(
                ["lake", "build"],
                cwd=tmp_lean,
                env=env,
                capture_output=True,
                text=True,
                timeout=90,
                check=False,
            )
            self.assertEqual(r_build.returncode, 0, msg=r_build.stdout + "\n" + r_build.stderr)
            self.assertNotIn("warning:", (r_build.stdout + r_build.stderr).lower())

            # 2. Fresh external kernel replay via leanchecker --fresh HoloEmit
            r_lc = subprocess.run(
                ["lake", "env", "leanchecker", "--fresh", "HoloEmit"],
                cwd=tmp_lean,
                env=env,
                capture_output=True,
                text=True,
                timeout=120,
                check=False,
            )
            self.assertEqual(r_lc.returncode, 0, msg=r_lc.stdout + "\n" + r_lc.stderr)

            # 3. AxiomAudit.lean: 24/24 theorems, 0 Classical.choice, 0 _native.bv_decide, 0 sorryAx
            r_ax = subprocess.run(
                ["lake", "env", "lean", "AxiomAudit.lean"],
                cwd=tmp_lean,
                env=env,
                capture_output=True,
                text=True,
                timeout=45,
                check=False,
            )
            self.assertEqual(r_ax.returncode, 0, msg=r_ax.stdout + "\n" + r_ax.stderr)
            ax_lines = [ln for ln in r_ax.stdout.splitlines() if ln.strip()]
            self.assertEqual(len(ax_lines), 24, msg=r_ax.stdout)
            self.assertEqual(sum(1 for ln in ax_lines if ln.endswith(": [propext]")), 4, msg=r_ax.stdout)
            self.assertEqual(sum(1 for ln in ax_lines if ln.endswith(": [propext, Quot.sound]")), 20, msg=r_ax.stdout)
            self.assertEqual(vmod.detect_lean4_bv_decide_escapes("", ax_lines), [], msg=r_ax.stdout)

            # 4. Dump sm_86 PTX & assemble offline via ptxas -arch=sm_86 -v (0 B stack, 0 B spill)
            dump_bin = tmp_lean / ".lake" / "build" / "bin" / "holoemit-dump"
            r_ptx = subprocess.run(
                [str(dump_bin), "ptx"],
                cwd=tmp_lean,
                env=env,
                capture_output=True,
                text=True,
                timeout=15,
                check=False,
            )
            self.assertEqual(r_ptx.returncode, 0, msg=r_ptx.stderr)
            self.assertIn("mov.u32 %r1, 0;", r_ptx.stdout)
            self.assertIn("mov.u32 %r30, 0;", r_ptx.stdout)
            self.assertNotIn("mov.u32 %r31, 0;", r_ptx.stdout)
            self.assertIn(".reg .b64 %rd<1>;", r_ptx.stdout)
            self.assertIn(".reg .pred %p<1>;", r_ptx.stdout)

            # Verify parameterless kernel emits mov.u32 %r0, 0; before st.global.u32
            zero_lean = tmp_lean / "ParamlessZeroCheck.lean"
            zero_lean.write_text(
                'import HoloEmit\n#eval IO.println (HoloEmit.renderPTXModule [("paramless_zero", { params := [], body := [], retReg := ⟨0, by decide⟩ })])\n',
                encoding="utf-8",
            )
            r_zero = subprocess.run(
                ["lake", "env", "lean", "ParamlessZeroCheck.lean"],
                cwd=tmp_lean,
                env=env,
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
            self.assertEqual(r_zero.returncode, 0, msg=r_zero.stdout + "\n" + r_zero.stderr)
            self.assertIn("mov.u32 %r0, 0;", r_zero.stdout)
            self.assertNotIn("mov.u32 %r31, 0;", r_zero.stdout)

            ptx_path = Path(td) / "holoemit.ptx"
            cubin_path = Path(td) / "holoemit.cubin"
            ptx_path.write_text(r_ptx.stdout, encoding="utf-8")
            ptxas_bin = Path("/opt/cuda/bin/ptxas")
            cuobjdump_bin = Path("/opt/cuda/bin/cuobjdump")
            self.assertTrue(ptxas_bin.is_file(), msg="Missing /opt/cuda/bin/ptxas")
            self.assertTrue(cuobjdump_bin.is_file(), msg="Missing /opt/cuda/bin/cuobjdump")

            r_ptxas = subprocess.run(
                [str(ptxas_bin), "-arch=sm_86", "-v", str(ptx_path), "-o", str(cubin_path)],
                env=env,
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
            self.assertEqual(r_ptxas.returncode, 0, msg=r_ptxas.stdout + "\n" + r_ptxas.stderr)
            ptxas_log = r_ptxas.stdout + "\n" + r_ptxas.stderr
            spill_matches = re.findall(r"(\d+)\s+bytes\s+spill\s+(?:stores|loads)", ptxas_log)
            self.assertEqual(len(spill_matches), 6, msg=ptxas_log)
            for sm in spill_matches:
                self.assertEqual(int(sm), 0, msg=ptxas_log)
            reg_pairs = re.findall(
                r"Compiling entry function '([^']+)'[\s\S]*?Used\s+(\d+)\s+registers",
                ptxas_log,
            )
            self.assertEqual(
                {fn: int(rc) for fn, rc in reg_pairs},
                {
                    "holo_a16_folded_parity": 8,
                    "holo_a16_syndrome": 8,
                    "holo_a16_secded_heal": 10,
                },
                msg=ptxas_log,
            )

            r_sass = subprocess.run(
                [str(cuobjdump_bin), "-sass", str(cubin_path)],
                env=env,
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
            self.assertEqual(r_sass.returncode, 0, msg=r_sass.stderr)
            self.assertEqual(len(re.findall(r"\bLOP3\.LUT\b", r_sass.stdout)), 21, msg=r_sass.stdout)
            self.assertEqual(len(re.findall(r"\bULOP3\.LUT\b", r_sass.stdout)), 9, msg=r_sass.stdout)
            self.assertEqual(r_sass.stdout.count("LOP3.LUT"), 30, msg=r_sass.stdout)
            self.assertEqual(len(re.findall(r"\bPOPC\b", r_sass.stdout)), 6, msg=r_sass.stdout)
            self.assertEqual(len(re.findall(r"\bUPOPC\b", r_sass.stdout)), 4, msg=r_sass.stdout)
            self.assertEqual(r_sass.stdout.count("POPC"), 10, msg=r_sass.stdout)
            self.assertEqual(len(re.findall(r"\bLDL\b", r_sass.stdout)), 0, msg=r_sass.stdout)
            self.assertEqual(len(re.findall(r"\bSTL\b", r_sass.stdout)), 0, msg=r_sass.stdout)

            # 5. Dump AVX-512 C11 header, compile with -Wall -Wextra -Werror, and execute all 65,536 words
            r_avx = subprocess.run(
                [str(dump_bin), "avx512"],
                cwd=tmp_lean,
                env=env,
                capture_output=True,
                text=True,
                timeout=15,
                check=False,
            )
            self.assertEqual(r_avx.returncode, 0, msg=r_avx.stderr)
            hdr_path = Path(td) / "holoemit_avx512.h"
            hdr_path.write_text(r_avx.stdout, encoding="utf-8")
            c_driver = Path(td) / "driver.c"
            bin_driver = Path(td) / "driver"
            c_driver.write_text(
                r"""
#include <stdint.h>
#include <stdio.h>
#include "holoemit_avx512.h"

__attribute__((target("avx512f,avx512bw,avx512vl,avx512vpopcntdq")))
int main(void) {
    uint32_t in_buf[16];
    uint32_t out_fp[16], out_sy[16], out_sh[16];
    uint64_t fnv = 14695981039346656037ULL;
    for (uint32_t base = 0; base < 65536u; base += 16u) {
        for (uint32_t i = 0; i < 16u; ++i) in_buf[i] = base + i;
        __m512i vin = _mm512_loadu_si512((const void*)in_buf);
        __m512i vfp = holo_a16_folded_parity_avx512(vin);
        __m512i vsy = holo_a16_syndrome_avx512(vin);
        __m512i vsh = holo_a16_secded_heal_avx512(vin);
        _mm512_storeu_si512((void*)out_fp, vfp);
        _mm512_storeu_si512((void*)out_sy, vsy);
        _mm512_storeu_si512((void*)out_sh, vsh);
        for (uint32_t i = 0; i < 16u; ++i) {
            uint64_t mix = ((uint64_t)out_fp[i] << 32) ^ ((uint64_t)out_sy[i] << 24) ^ (uint64_t)out_sh[i];
            fnv = (fnv ^ mix) * 1099511628211ULL;
        }
    }
    printf("%016llx\n", (unsigned long long)fnv);
    return 0;
}
""",
                encoding="utf-8",
            )
            r_gcc = subprocess.run(
                ["gcc", "-O3", "-std=c11", "-Wall", "-Wextra", "-Werror", str(c_driver), "-o", str(bin_driver)],
                cwd=td,
                env=env,
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
            self.assertEqual(r_gcc.returncode, 0, msg=r_gcc.stdout + "\n" + r_gcc.stderr)
            r_exec = subprocess.run(
                [str(bin_driver)],
                cwd=td,
                env=env,
                capture_output=True,
                text=True,
                timeout=15,
                check=False,
            )
            self.assertEqual(r_exec.returncode, 0, msg=r_exec.stderr)
            got_fnv = r_exec.stdout.strip()

            fnv_py = 14695981039346656037
            for w in range(65536):
                fp = vmod.folded_upper_parity_spec(w)
                sy = vmod.a16_syndrome_spec(w)
                sh = vmod.secded_heal_spec(w)
                mix = (fp << 32) ^ (sy << 24) ^ sh
                fnv_py = ((fnv_py ^ mix) * 1099511628211) & 0xFFFFFFFFFFFFFFFF
            self.assertEqual(got_fnv, f"{fnv_py:016x}")


if __name__ == "__main__":
    unittest.main()
