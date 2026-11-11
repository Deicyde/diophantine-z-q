"""One line per curve (format of cr3-check/out_compare40.txt) from slots.json and curves.json."""
import json
S = {r["i"]: r for r in json.load(open("slots.json"))}
C = json.load(open("curves.json"))
print("d | primes (mod 8) | pair#/role beta theta | slot facts (d%8, sqf, beta|d, dim Sel2, beta in pi1) "
      "| rootno | anrank | ellrank r1..r2 s (effort) | #pts | Kummer images | beta in span")
bad = 0
for c in C:
    s = S[c["i"]]; f = s["facts1" if c["role"] == "d1" else "facts2"]
    facts_ok = f["mod8"] == 5 and f["sqf"] and f["beta_div"] and f["sel_dim"] == 3 and f["beta_in_pi1"]
    fail = c["rootno"] != -1 or c.get("anrank", 1) != 1 or c["r2"] == 0 or c["beta_in_span"] is False or not facts_ok
    bad += fail
    print(c["d"], "|", " ".join("%d(%d)" % (p, p % 8) for p in c["primes"]), "|",
          "#%d/%s %d %d" % (c["i"], c["role"], s["beta"], s["theta"]), "|",
          "%d %s %s %d %s" % (f["mod8"], f["sqf"], f["beta_div"], f["sel_dim"], f["beta_in_pi1"]), "|",
          c["rootno"], "|", c.get("anrank", "-"), "|", "[%d, %d] %d (%d)" % (c["r1"], c["r2"], c["s"], c["effort"]), "|",
          len(c["gens"]), "|", c["kummer"] or "-", "|", "-" if c["beta_in_span"] is None else c["beta_in_span"])
print("curves:", len(C), "failures:", bad)
