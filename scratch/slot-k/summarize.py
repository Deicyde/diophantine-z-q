"""Summarize the validation outputs out_*.txt of run_dl.py / run_families.py."""
import re, sys, glob
for f in sys.argv[1:]:
    rows = [l for l in open(f) if " m=" in l and ("OK" in l or "FAIL" in l)]
    ok = sum(l.rstrip().endswith("OK") for l in rows)
    aux = [int(re.search(r"#aux=(\d+)", l).group(1)) for l in rows]
    wb = [int(re.search(r"w\(beta\)=(\d+)", l).group(1)) for l in rows]
    wt = [int(re.search(r"w\(theta\)=(\d+)", l).group(1)) for l in rows]
    dig = [int(m.group(1)) for l in rows for m in [re.search(r"maxaux_digits=(\d+)", l)] if m]
    inputs = len({l.split(" m=")[0] for l in rows})
    print(f"{f}: inputs={inputs} runs={len(rows)} certified={ok} aux=[{min(aux)},{max(aux)}] "
          f"w(beta)=[{min(wb)},{max(wb)}] w(theta)=[{min(wt)},{max(wt)}] "
          f"digits<={max(dig) if dig else '-'} aux==w(beta)+w(theta): {all(a == b + t for a, b, t in zip(aux, wb, wt))}")
