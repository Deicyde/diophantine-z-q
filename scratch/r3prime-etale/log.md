# r3prime-etale results log

## 2026-11-17 06:36 start
- Base: wip/r3prime-etale at 115cb119b (origin/wip/jp-an-retype already merged; step (1) done). VERIFIED (git log).
- sga1-etale, sga1-fix, gaga-serre are NOT ancestors of HEAD (VERIFIED, git merge-base); their CPt/AnFunAt world
  (analyticTopology, AffineChart, SerreHolAt) is on `X : Over (Spec ℂ)` and CPt X, not on the consumers'
  `𝒢.Pts τ` with `anTop`. No homeomorphism `𝒢.Pts τ ≃ₜ CPt(𝒢 ×_τ ℂ)` exists in the tree (survey fact iii).

## Plan (decided)
- Define on the consumers' carrier `𝒢.Pts τ` (anTop) Serre's structure sheaf directly: `AnHolAt h q` =
  near q, h = H(s_1,…,s_m) with s_j regular functions of 𝒢 at q and H holomorphic near (s_j(q))
  (GAGA §2 / SGA 1 XII 1.1 reduced structure sheaf; same generators as `anTop`). Not built from étale coordinates.
- `IsSerreChart φ`: φ is an isomorphism of ringed spaces onto an open of ℂ^g (stalkwise:
  AnHolAt h q ↔ h ∘ φ⁻¹ holomorphic near φ q).
- Target: `IsHolChart φ ↔ IsSerreChart φ` (with T35, as all consumers already use).
- Core glue identified: left translation by a complex point is holomorphic for Serre's sheaf (TranslationAnHol);
  IsHolChart's translated coordinates F(q⁻¹·) need it in both directions.

## 07:00 R3Etale.lean compiles (VERIFIED, `lake env lean`, axioms propext/choice/Quot.sound)
- `isHolChart_iff_isSerreChart (hT35) (hTH : TranslationAnHol) 𝒢 g hg τ φ : IsHolChart 𝒢 τ φ ↔ IsSerreChart 𝒢 τ φ`.
- Helpers: `anHolAt_pi`, `holo_of_anHolAt` (Serre-hol ⇒ hol along Φ), `anHolAt_of_holo` (converse, uses TH),
  `exists_localInverse`, `chartAt_anHolAt`.
- Remaining glue: `TranslationAnHol` (x ↦ s(p x) Serre-holomorphic). Next: prove it (tensor decomposition on
  an affine open of 𝒢 ×_{𝓞_L} 𝒢).
- Note: worktree lacked lean/.lake (z_in_q package); copied from ~/dzq-wt/carirr-refold (lean/ sources identical, diff -rq).

## 08:05 THGeneric.lean compiles (VERIFIED, axioms propext/choice/Quot.sound)
- `exists_tensor_formula`: for X, Y over Spec R₀, σ ∈ Γ(X ×_{R₀} Y, W), ℂ-points a, b₀ with (a,b₀) ∈ W(ℂ):
  ∃ V ∋ b₀, c_j ∈ Γ(Y,V), u_j, v_j ∈ ℂ, N with σ(a,b)·(Σ v_j c_j(b))^N = Σ u_j c_j(b) for b ∈ V(ℂ), Σ v_j c_j(b) ≠ 0
  (nonzero at b₀). Proof: affine V₁ ∋ a, V₂ ∋ b₀, V₁×V₂ = Spec(Γ(V₁)⊗Γ(V₂)) via Mathlib `pullbackSpecIso`,
  basic-open fraction (`exists_fraction`, Mathlib `isLocalization_basicOpen`), tensor decomposition.

## 08:25 R3' PROVED (VERIFIED: R3Etale.lean compiles; axioms propext, Classical.choice, Quot.sound)
- `translationAnHol : TranslationAnHol` (from `exists_tensor_formula` with X = Y = 𝒢, μ^*s).
- `isHolChart_iff_isSerreChart' (hT35) 𝒢 g hg τ φ : IsHolChart 𝒢 τ φ ↔ IsSerreChart 𝒢 τ φ` — only T35
  (the consumers' existing hypothesis) remains.

## 07:50 checks
- Contrib file `ZInQKernel/Contrib/OneProof/HolChartSerre.lean`: `lake env lean` clean (VERIFIED).
- `lake build +Main +Discharges +HolChartSerre`: Build completed successfully (16216 jobs) (VERIFIED).
- `#discharges` (scratch/r3prime-etale/discharges-output.txt): 19 pre-existing lines from imported contribs,
  none by ZInQ.R3Etale (no field discharged; R3' is a reading step, not a field). Axioms of the five main
  theorems: propext, Classical.choice, Quot.sound (VERIFIED).
- `isSerreMetricSq_iff`: IsAnMetricSq (base of IsAnStableHeight, IsAnStableHeightSS, IsStableHeightBarAn) equals
  the metric read in Serre's charts (VERIFIED, compiled).
- Report docs/research/r3prime-etale.md; autofold.json = empty spec + flag updates.
