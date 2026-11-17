# lcal-one — fleet summary (2026-11-17)

**Result.** `ZInQ.Contrib.TYZDecomp.TYZLcalOne` (`lcalSq 1 = 1`, i.e. `L(y² = x³ − x, 1) = ¼∫₁^∞ dx/√(x³−x)`,
TYZ's `𝓛(1) = 1`) is **proved outright**, no new leaf, standard axioms:
`ZInQ.Contrib.LcalOne.tyzLcalOne_proof` in `ZInQKernel/Contrib/OneProof/TYZLcalOne.lean`. With tyz-genus's variant B,
`frozenTarget`'s two TYZ hypotheses `h11` and `hL29` are replaced by the one printed leaf `TYZThm21PairsC`
(**TYZ 2 → 1, open hypotheses 35 → 34**); variant C (pending a reading of Thm 2.1 at n = 1) is no longer needed.

**Proof.** (A) the tree's Hecke continuation writes `L(C₁,1)` as Mellin integrals of lattice theta kernels;
block decomposition mod 4 + grouping by the norm + gz-theta's `etaThetaIdentity` give `L(C₁,1) = 2π∫₀^∞ f(it)dt`,
`f = η(4τ)²η(8τ)²`. (B) on the imaginary axis x0-32's eta model `x, y` (`y² = x³+4x`) is real, `x' = −4π f y`
(gz-weil's `etaModelDifferential`), `x → 2` at the cusp 0 (theta S-law), `x → ∞` at i∞; the 2-isogeny substitution
`u = x/4 + 1/x` maps (0,∞) onto (1,∞) with `u'/√(u³−u) = 8πf`, and FTC gives `∫₀^∞ f(it)dt = Ω/(8π)`.

**Compiles.** The contribution (633 lines; `lake build` OK); `scratch/lcal-one/Discharges.lean` (`DISCHARGES [h11] by
LcalOne.tyzThm11Integral_of_thm21C_only still assumes [TYZThm21PairsC]`, and hL29 by tyz-genus's
`tyzLemma29PrintedNe3_of_thm21C`, same leaf); `FoldCheck.lean` (`frozenTarget_lcalOne`, the new frozenTarget body,
standard axioms); `fold-spec.json`, `kinds-rows.tsv` (row `h21C`). Report: `docs/research/lcal-one.md`.

**Remains.** Nothing on this target. Integrator: the manual fold of `Main.lean` (spec above). Optional: route
`TYZLcal.tyzLcalOne_of_leaves` consumers to `tyzLcalOne_proof`; drop `TunnellOddL1` / `TYZThm21PairsC1`.
