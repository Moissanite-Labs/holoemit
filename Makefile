SHELL := /bin/bash
PYTHON ?= python3

.PHONY: all lean verify test test-silicon clean

all: verify test lean

lean:
	@CUDA_VISIBLE_DEVICES="" OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -I -B -c '\
import os, pathlib, shutil, subprocess, sys, tempfile;\
home = os.path.expanduser("~");\
clean_path = f"{home}/.elan/bin:/usr/local/bin:/usr/bin:/bin:" + os.environ.get("PATH", "");\
env = {"PATH": clean_path, "HOME": home, "CUDA_VISIBLE_DEVICES": "", "OPENBLAS_NUM_THREADS": "1", "OMP_NUM_THREADS": "1"};\
td = tempfile.TemporaryDirectory();\
dst = pathlib.Path(td.name) / "lean";\
shutil.copytree("lean", dst);\
print("==> Building HoloEmit in isolated Lean 4.36.0 workspace...");\
r1 = subprocess.run(["lake", "build"], cwd=dst, env=env, capture_output=True, text=True);\
sys.stdout.write(r1.stdout + r1.stderr);\
(r1.returncode == 0 and "warning:" not in (r1.stdout + r1.stderr).lower()) or sys.exit(1);\
print("==> Replaying kernel environment via leanchecker --fresh HoloEmit...");\
subprocess.run(["lake", "env", "leanchecker", "--fresh", "HoloEmit"], cwd=dst, env=env, check=True);\
print("==> Auditing kernel axioms across all 24 public theorems...");\
subprocess.run(["lake", "env", "lean", "AxiomAudit.lean"], cwd=dst, env=env, check=True);\
td.cleanup()'

verify:
	@CUDA_VISIBLE_DEVICES="" PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -I -B -c '\
import subprocess, sys;\
outs = [subprocess.check_output([sys.executable, *flags, "verify_holoemit.py", "--json"], text=True) for flags in (["-I", "-B", "-W", "error"], ["-I", "-B"], ["-I", "-O", "-B"])];\
(outs[0] == outs[1] == outs[2]) or sys.exit(1);\
sys.stdout.write(outs[0])'

test:
	@set -euo pipefail; \
	CUDA_VISIBLE_DEVICES="" PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -I -B -W error tests/test_holoemit_r5.py; \
	CUDA_VISIBLE_DEVICES="" PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -I -B tests/test_holoemit_r5.py; \
	CUDA_VISIBLE_DEVICES="" PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -I -O -B tests/test_holoemit_r5.py

test-silicon:
	@CUDA_VISIBLE_DEVICES="" PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -I -B tests/test_live_toolchain_silicon.py

clean:
	rm -rf lean/.lake __pycache__ tests/__pycache__
