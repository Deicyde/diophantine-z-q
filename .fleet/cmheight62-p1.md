# cmheight62-p1

**Proved (no sorry, axioms [propext, Classical.choice, Quot.sound]):**
- Step 6, exact formula for every smooth model (no properness):
  `ZInQ.Contrib.CMHeight62.finrank_mul_modelHeight_eq_exact'` (ZInQKernel/Contrib/OneProof/CMHeight62/Final.lean):
  for `hdim : E.dim = 1`, `D : ShortData E`, `M : MetrizedModel E L 1`, periods `τ` with `0 < Im τ_σ` and
  `IsPeriodAt E (σ.comp (algebraMap K L)) (τ σ)`:
  `∃ hη : D.etaW M.model ≠ 0, [L:ℚ]·h(M) = Σ_σ summand62 (τ σ) + (1/12)(log|N_{L/ℚ}(algebraMap K L D.W.Δ)| − 12 log absNorm(coefficientFractionalIdeal M.model hdim (D.etaW M.model) hη))`.
- `ZInQ.Contrib.CMHeight62.cmHeight62_of_step7' : Step7 → HDec.CMBranch.CMHeight62`.
- Steps 1, 2, 4 are the theorem `archIdentity : ArchIdentity` (no hypotheses); step 0 `exists_metrizedModel`.

**Step-7 Prop** (Assembly.lean):
`Step7 := ∀ K L [..] (E : PkgI3.AbVar K) (hdim : E.dim = 1) (D : ShortData E) (𝒢 : GroupModel E L), IsProper 𝒢.G.hom → ∀ hη : D.etaW 𝒢 ≠ 0, |Algebra.norm ℚ (algebraMap K L D.W.Δ)| ≤ FractionalIdeal.absNorm (coefficientFractionalIdeal 𝒢 hdim (D.etaW 𝒢) hη) ^ 12`.

**Unproved sub-steps of 0-6:** none. **Open:** Step7 only (gap analysis: docs/research/cmheight62-p1.md §4:
Weierstrass scheme over a DVR with omega, minimal model with unit discriminant, AV7 for NeronGoodModelIso input,
DVR-to-𝓞_L omega comparison).

**No count change**: no frozen field retired; nothing folded; only new files under
ZInQKernel/Contrib/OneProof/CMHeight62/, docs/research/cmheight62-p1.md, scratch/cmheight62-p1/, .fleet/.

**Compiles:** `lake build ZInQKernel.Contrib.OneProof.CMHeight62.Final` succeeds; HodgeLineBinding.All and
HodgeLatticeIdeal.All both build.

**#discharges:** `cmHeight62_of_step7'` matches `OpenResearchLeaves79.cmHeight62`, still assumes `[Step7]`
(scratch/cmheight62-p1/discharges.out).

**Final SHA:** all work is at `74d5c8087c778404fcd09ad01c2eee5ae369749a`; this file is committed last, as its child.
