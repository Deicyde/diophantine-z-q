"""Assemble scratch/frontier/TYZChain.lean: tyz-cm's eleven Shimura modules (as merged into cm-bridge) and cm-bridge's Bridge.lean,
verbatim except that `import` lines are dropped and each body's top-level `noncomputable section` is closed,
followed by this task's composition (TYZChainTail.lean)."""
import subprocess, re
R = "/home/jackmccarthy/dzq-wt/frontier"
TCM = "ed50dc33"  # cm-bridge final, which merges tyz-cm 0ad48a7d
CMB = "ed50dc33"
parts = [(TCM, f"ZInQKernel/Contrib/TYZGenus/{m}.lean") for m in
         ["ShimuraRecip", "ShimuraZn", "ShimuraField", "ShimuraModFn", "ShimuraQExp", "ShimuraCusp", "ShimuraMain",
          "ShimuraEtaInv", "ShimuraTheta", "ShimuraThetaDup", "ShimuraFricke"]]
parts.append((CMB, "scratch/cm-bridge/Bridge.lean"))
out = ["import ZInQKernel.Contrib.TYZGenus.RingClassBridge",
       "import ZInQKernel.Contrib.GZTheta.NewCMProof",
       "import ZInQKernel.Contrib.GZTheta.New32",
       "import ZInQKernel.Contrib.GZTheta.Final",
       "import ZInQKernel.Contrib.GZDecomp.Decomp",
       "import ZInQKernel.Contrib.GZTheta.Eta",
       "import ZInQKernel.Contrib.GZTheta.JacobiGauss", ""]
for rev, path in parts:
    t = subprocess.run(["git", "-C", R, "show", f"{rev}:{path}"], capture_output=True, text=True, check=True).stdout
    lines = [l for l in t.split("\n") if not l.startswith("import ")]
    body = "\n".join(lines)
    out.append(f"-- ===== verbatim body of {path} @ {rev} (imports dropped) =====")
    out.append(body)
    if re.search(r"^noncomputable section\s*$", body, re.M):
        out.append("end  -- closes the file's top-level `noncomputable section`")
    out.append("")
out.append(open(f"{R}/scratch/frontier/TYZChainTail.lean").read())
open(f"{R}/scratch/frontier/TYZChain.lean", "w").write("\n".join(out))
print("written", sum(1 for _ in open(f"{R}/scratch/frontier/TYZChain.lean")), "lines")
