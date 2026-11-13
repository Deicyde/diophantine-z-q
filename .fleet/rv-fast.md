# rv-fast (fleet summary)

**Verdicts** (docs/research/rv-fast.md; check files in scratch/rv-fast/):
- **lg-kerwild: CONCERN.** The core results are sound: `TateBridgeK` from I3.M0, `KerWild` (a real constraint),
  and `DescentPts` for G7Data's model. But `exists_localGlue_of_tateModuleFree` (LocalGlue at every ℓ) assumes
  `G7Clauses β' ε' L` about data that `TateBridgeK` hides behind `∃`, so no consumer can discharge it.
  For the witness that proves `TateBridgeK` (`a' = 1`, `ε' = c = n/d`), the compiled lemma `rvf_c_sq_of_a_one`
  shows that `G7Clauses` forces `c² = 1`. That fails unless every descent factor `a_σ = (deg μ_σ)^{-1/4}` is 1.
  The two normalizations differ: unram-tate puts the real factor in ε', while G7Clauses and Glazer put it in a.
  So LocalGlue at general ℓ stays open. The ℓ = 5, 3 route (TateBridge35) still needs `[L:ℚ] ≤ D` and
  `ε = 1` on `G_L × G_L`. The committed KerWild.lean no longer rebuilds from the current local-glue source
  (integration conflict only).
- **ring-class: SOUND.** `hprimeNormal`, `iInH4` and `ringClassFieldD_tyz` match cm-points' types by `rfl`, and the
  fields are non-degenerate (`[H4 : H'] = 2`, `H4bar ≠ ⊥`). The condD conductor formula agrees with PARI on 30/30
  discriminants. Citation note: the leaf `CM.CMFieldOfDefinition ringClassFieldD` is true, but it follows from
  Shimura's reciprocity law, not from Gross 1984 §3 as printed.
- **unram-roots, afr-absfrob, curve-infra: SOUND.** All three are unconditional or use only kernel leaves (I2-NMP).
  Statements are byte-identical to their sources, and each gives the expected values on a concrete instance.

**What compiles** (one Lean process at a time):
- the ring-class build (10286 jobs);
- RingClassCheck, CurveInfraCheck, UnramRootsCheck, AbsFrobCheck, AfrCheck and KerWildCheck, all with 0 errors;
- every axiom print `[propext, Classical.choice, Quot.sound]`, including my two new lemmas.

**What remains:**
- TYZ source comparison for ring-class (`~/tyz-src` is absent);
- x0-32's `phiC` leaves;
- satisfiability of G7Data;
- the fix itself: TateBridgeK should export a transport and a non-trivial `a`, or the every-ℓ theorem should be restated.
