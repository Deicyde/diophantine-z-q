"""Restore missing local oleans in dependency order. Recompile Main even if a cache has it."""
from pathlib import Path
import re
import subprocess
import sys

local = Path(".lake/build/lib/lean")
seen = set()

def build(mod):
    if mod in seen:
        return
    seen.add(mod)
    if not mod.startswith("ZInQKernel."):
        return
    path = Path(*mod.split("."))
    src = path.with_suffix(".lean")
    olean = (local / path).with_suffix(".olean")
    for dep in re.findall(r"^(?:(?:public|meta) )?import ([\w.]+)", src.read_text(), re.M):
        build(dep)
    if not olean.is_file() or mod == "ZInQKernel.OneProof.Main":
        olean.parent.mkdir(parents=True, exist_ok=True)
        print(f"compile {mod}", flush=True)
        subprocess.run(["bash", "scratch/scholze-narrow/check.sh", "-o", olean, src], check=True)

for module in sys.argv[1:]:
    build(module)
