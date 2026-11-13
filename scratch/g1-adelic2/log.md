# g1-adelic2 results log

- 03:12 Merged origin/wip/t30-adelic (already contained in fork main 883c4ddf).
  `ZInQKernel/Contrib/G1Adelic/Basic.lean` = `scratch/t30-adelic/Adelic.lean` (header changed only).
  `lake build ZInQKernel.Contrib.G1Adelic.Basic`: OK, 73 s; `#print axioms` of relIndex_eq_four,
  mem_sup_iff_forall, normalizer_component, gamma_count, gamma_order, gamma_count_Zint:
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- 03:50 scratch/g1-adelic2/FA1.lean compiles (VERIFIED, `lake env lean`, 19 s): `qmap` (ℍ[R,2,0,-3] functorial),
  `phi v` := Mathlib's `adicCompletion.padicEquiv v : ℚ_v ≃A[ℚ] ℚ_[primesEquiv v]` behind `irreducible_def`
  (opaque wrapper), `mem_integers_iff` (x ∈ ℤ_v ↔ ‖phi v x‖ ≤ 1, from `padicEquiv_bijOn`),
  `quatRP : ℍ[𝔸ᶠ[ℤ,ℚ],2,0,-3] ≃+* Πʳ_v [ℍ[ℚ_v,2,0,-3], ℍ[ℤ_v,2,0,-3]]`,
  `Rd : BA →+* Πʳ_v [...]` (`RestrictedProduct.mapAlongRingHom` along `primesEquiv`), `Rd_injective`,
  `Rd_surjective`, `Theta : BA ≃+* ℍ[𝔸ᶠ[ℤ,ℚ],2,0,-3]` with `Theta_re : (Theta y).re v = (phi v).symm (y (pe v)).re` (rfl).
  Route: index by `v : HeightOneSpectrum ℤ`, use `padicEquiv v` (no cast) and never `Padic.adicCompletionEquiv`
  / `PadicInt.adicCompletionIntegersEquiv`; the inverse is `RingEquiv.ofBijective`.
  Kernel pitfall found (VERIFIED): a tactic `let y₀ := Equiv.piCongrLeft P pe w` followed by a `change`
  that unfolds `Rd ⟨y₀, _⟩ v` is a kernel deterministic timeout (the kernel zeta-unfolds `y₀` and tries
  to reduce the cast along `pe.apply_symm_apply`); fix: hide the witness behind `∃` (`exists_reindex`)
  and rewrite with `RestrictedProduct.mk_apply` instead of `change`.
- 03:32 `ZInQKernel/Contrib/G1Adelic/FiniteAdele.lean` (= scratch FA1.lean) builds with
  `lake build ZInQKernel.Contrib.G1Adelic.FiniteAdele` (19 s). VERIFIED. Over Mathlib's objects
  (`AF = FiniteAdeleRing ℤ ℚ`, `HA = ℍ[AF, 2, 0, -3]`): `ZhatAF` (ℤ̂ = {a | ∀ v, a v ∈ ℤ_v}),
  `qcoord` (N5 coordinates), `OhatAF`/`OhatSubAF` (𝒪̂ = coordinates in ℤ̂), `NAF` (normalizer of 𝒪̂),
  `K0AF = OhatSubAF.toSubmonoid.units`, `ZAF = range (Units.map (algebraMap AF HA))`,
  `K3AF = {u ∈ K0AF | ∃ w ∈ 𝒪̂, u - 1 = 3w}`; `map_Nhat`, `map_K0`, `map_Zhat`, `map_K3` (each t30
  subgroup maps onto the Mathlib-side one under `ThetaU = Units.mapEquiv Theta`);
  `relIndex_eq_four_AF : (ZAF ⊔ K0AF).relIndex NAF = 4`,
  `relIndex_K3_AF : ((ZAF ⊓ K0AF) ⊔ K3AF).relIndex K0AF = 36`,
  `gamma_order_AF : (ZAF ⊔ K3AF).relIndex NAF = 144`.
  `#print axioms` of Theta, gamma_order_AF, relIndex_eq_four_AF, relIndex_K3_AF:
  [propext, Classical.choice, Quot.sound]. VERIFIED.
