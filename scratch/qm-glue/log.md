# qm-glue results log

Base debc37b4 (wip/w56). qm-split's olean chain (~/qms-olean, TailK) no longer exists on this host, so every
file here is self-contained (`import Mathlib`), with the needed definitions copied verbatim
(`HDec.PkgI1` from `ZInQKernel/OneProof/H/LPrefix.lean` l.227-363). Check: `lake env lean scratch/qm-glue/<file>.lean`.

## (a) `ThetaQuotientValue24` — `ThetaValue24.lean` (VERIFIED, compiled, axioms standard, ~10 s after import)
- Statement copied verbatim (qm-split `Haupt.lean` l.2287, namespace `HDec.LeafQCheck.HM.QMSplit`, with `HM.mu`).
- `fixedPoint_eq`: γ with matrix ι(μ), γ•τ = τ ⇒ τ = i(√6+√3) (= i√(9+6√2)).
- `omega_tau24`: Ω(i(√6+√3)) = Ω₂₄ = [[(−4+3√−6)/14, (−1−√−6)/7], [(−1−√−6)/7, (−4+3√−6)/7]] (exact).
- `gammaMu_fix`, `thetaQuotientValue24_iff : ThetaQuotientValue24 ↔ ThetaValueAtOmega24`
  (jDen Ω₂₄ ≠ 0 ∧ jNum Ω₂₄/jDen Ω₂₄ = −16/27: ten theta constants at one explicit matrix).
- LEAF `IgusaCMValue24` (Lin–Yang eqs. (2),(14) at j = −16/27, Baba–Granath CM value; LNY theta conventions;
  the manuscript's citation l.908-923; locators UNVERIFIED). `thetaQuotientValue24_of_igusa` and the converse
  `igusa_of_thetaQuotientValue24` (the leaf is equivalent to the glue: not stronger).
- Numerics (py/value24.py, pure-Python double precision, from the Lean definitions): j_θ(τ₂₄) =
  −0.5925925925925931 (−16/27 + 6e-16); Ω(τ₂₄) numerically equal to Ω₂₄; the ten |θ_m| come in five equal
  pairs (an extra involution of the polarized surface, as expected at an elliptic point of order 2). VERIFIED.
- Finding: an exact Lean computation of the value needs CM theory (the surface is isogenous to E×E with E
  CM by ℚ(√−6), class number 2); interval bounds give only |j_θ + 16/27| < ε, never the equality, without an
  arithmetic input (rationality with bounded denominator), which is not a published statement in that form.
