# theta-wp8 (2026-11-15)

**Verdict: `X0EtaRoute.ThetaWeierstrass8` is proved outright, and Theorem 1.1 compiles without `hX`.** Standard axioms
only, no new leaves: −1 GLUE.
- Proof: `ThetaWP8.thetaWeierstrass8`, in `ZInQKernel/Contrib/OneProof/ThetaWeierstrass8.lean`. The file is new,
  907 lines, and imports `ZInQKernel.Contrib.OneProof.X0ModuliUsed`.
- Inputs: Mathlib's `℘`, `jacobiTheta₂` and Liouville theorem, plus gz-theta's triple product.

**What compiles** (VERIFIED: `lake build`, and `#discharges` in `scratch/theta-wp8/discharges-output.txt`):
- `ThetaWP8.core`, `thetaWeierstrass8` and `xEtaWeierstrass` (`X0EtaRoute.XEtaWeierstrass`).
- `tyzThm35ReadingA_noHX (h11 h29 hCM h33)`.
- `frozenTarget_noHX`, which takes the binders of `ZInQ.OneProof.frozenTarget` minus `hX`.
- `#discharges` reports 7 discharges, the same as before this task. That is expected: `hX` is a plain argument of
  `frozenTarget`, not a bundle field, so `autofold.py` does not apply. The manual fold (one import, delete the `hX`
  binder, one term) is in report §2 and `scratch/theta-wp8/autofold.json`.

**Proof outline:**
- `h(u) = (℘(u) − ℘(c)) s(u)²/(s(u−c)s(u+c))` is a nonzero constant, with `s(z) = θ(z + (1+w)/2)` and
  `c = 1/2 + w/8`. Liouville applies after removing its singularities, using simple theta zeros from the triple
  product.
- So the `℘`-ratio is a quotient of six theta values.
- That quotient identity is `θ₂ θ(w/4) θ₃ θ₄(w/4) = 2θ(1/2+3w/8)²θ(1/2+w/8)²`. It follows from the triple product at
  base `e^{πiw/8}`, Euler's identity and `θ₄(w/4) = θ₃ − θ₂`.

**Second question: no.** gz-heegner uses `X0ModuliGaloisMero` at the newform level of `C_d`. That level is `32d²`
(`d ≡ 5 mod 8`, so at least 800; VERIFIED with PARI), for the coordinates of `C_d`'s parametrization. It is never
level 32, so the eta route does not cover it, and the hL3 fold keeps the Mero hypothesis. A Tian-style rerouting
through level 32 would need a different GZ leaf (SPECULATIVE, not attempted).

**What remains:** the integrator's manual fold of `Main.lean`, and the `kinds.tsv` / OPEN.md regeneration.
Report: `docs/research/theta-wp8.md`.
