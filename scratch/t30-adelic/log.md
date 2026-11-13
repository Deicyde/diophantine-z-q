# t30-adelic results log

## T30 (LeafSqrtCrit from LocalKroneckerWeber)
- 22:40 SqrtCrit.lean part 1 compiles (VERIFIED, `lake env lean`): roots-of-unity CRT (`act_crt`),
  `exists_emb` (resp p σ is restriction along an embedding ℚ̄ → ℚ̄_p), `cyc_resp_eq`,
  `cyc_resp_eq_one`, `cyc_resp_eq_u` (σ inverts μ_{p^k}, fixes μ_{N'} ⇒ cyc_N(resp σ) = u),
  `act_of_gal` (action through `galToProd` at level ℚ_p(μ_{p^k m})).
- 22:45 SqrtCrit.lean COMPLETE (VERIFIED, `lake env lean`, 8 s): 
  `T30.leafSqrtCrit_of_localKroneckerWeber (hLKW : ∀ p : Nat.Primes, PkgI6.LocalKroneckerWeber p) : GlueDescent.B2Q.LeafSqrtCrit`.
  `#print axioms`: [propext, Classical.choice, Quot.sound]. No sorry.
  Pieces: `sqrt_of_chi'` ("if", no LKW: inflation from L = ℚ_p(μ_{p^{k+1}(p^{2f}-1)})),
  `chi_of_sqrt'` ("only if": fixed field M of ker φ is finite abelian, LKW puts M in ℚ_p(μ_{p^a b}),
  lift τ₋₁ from ℚ_p(μ_{p^{k+a} N' b}); σ² ∈ ker φ), `exists_sqrt_iff` (ℂˣ divisible ⇒ Baer),
  `restrict_sq_eq_one` (two-torsion part of `sqrt_criterion_level`, copied).
  Kernel pitfall found: `rfl` for `((algebraMap (muField a) (muField b) y : _) : ℚ̄_p) = y` is a
  kernel deterministic timeout (kernel compares the carriers muField a vs muField b); fix: go through
  `IntermediateField.inclusion` + `coe_inclusion`.

## G1-adelic
- G1Count.lean (VERIFIED, compiles, standard axioms): `G1Count.index_count` / `index_count_of_central`:
  `[G : Z⊔K₃] = [G : Z⊔K₀] · [K₀ : (Z⊓K₀)⊔K₃]` for K₃ ≤ K₀, Z normal (or central), Z⊔K₃ normal; with
  the modular law `sup_inf_eq`.
- Adelic.lean (VERIFIED, compiles, `#print axioms` standard for `relIndex_eq_four`,
  `mem_sup_iff_forall`, `normalizer_component`):
  B̂ = `Πʳ p : Nat.Primes, [Bp p, OpSub p]` (restricted product of B_p w.r.t. N5's 𝒪_p),
  `Ohat`, `Nhat` (normalizer of 𝒪̂ in B̂^×), `K0` (= 𝒪̂^×), `Zhat` (central scalars, componentwise ℚ_p^×).
  `normalizer_component` (x ∈ N ⇒ x_p normalizes 𝒪_p), `mem_sup_iff_forall` (x ∈ Z K₀ ⇔ ∀ p, x_p ∈ ℚ_p^×𝒪_p^×),
  `mem_sup_iff` (for x ∈ N: ⇔ at p = 2, 3 only), `Phi`, `ker_Phi`, `Phi_surjective`, `quotEquiv`
  (N/(Z K₀) ≃* B_2^×/ℚ_2^×𝒪_2^× × B_3^×/ℚ_3^×𝒪_3^×), `relIndex_eq_four` ([N : Z K₀] = 4).
- Adelic.lean, K₃ and the count (VERIFIED, standard axioms): `K3` (u ∈ K₀, u_3 ≡ 1 mod 3𝒪_3),
  `K0_le_Nhat`, `Zhat_le_Nhat`, `conj_mem_K3` (N normalizes K₃), `sup_K3_normal`,
  `gamma_count : (Zhat ⊔ K3).relIndex Nhat = 4 * ((Zhat ⊓ K0) ⊔ K3).relIndex K0`.
- Adelic.lean, |Γ'| = 144 (VERIFIED, compiles, no sorry, `#print axioms gamma_order` standard):
  `R3` (𝒪/3𝒪 as a monoid on glue-repo's `mul3`), `card_units_R3` (= 72, from `card_units_mod3`),
  `red`, `redHom : K0 →* R3ˣ`, `redHom_eq_one_iff` (kernel = K₃), `redHom_surjective` (a lift with
  nrd a 3-adic unit is in 𝒪_3^×), `redHom_scalar` (ℤ̂^× ↦ ±1), `subgroupOf_eq_comap`,
  `relIndex_K3 : ((Zhat ⊓ K0) ⊔ K3).relIndex K0 = 36`, `gamma_order : (Zhat ⊔ K3).relIndex Nhat = 144`.
  Pitfall: `ZMod ((P3 : Nat.Primes) : ℕ)` vs `ZMod 3`; making P3 an `abbrev` breaks instance lookup
  (discrimination tree reduces the projection); fix: compose `PadicInt.toZMod` with
  `ZMod.ringEquivCongr (rfl : q3 = 3)` (`t3`). `R3` must stay a `def` (own Monoid), with `R3.mk` to keep
  rewrite targets well-typed.
- Adelic.lean: `Zint` (ℤ̂^× = ∏ ℤ_p^× scalars), `Zhat_inf_K0 : Zhat ⊓ K0 = Zint`, `gamma_count_Zint` (|Γ'| = [N:𝔸_f^×K₀]·[K₀:ℤ̂^×K₃], = 4, = 36). VERIFIED, standard axioms.
- 23:07 Attempt (abandoned, file removed): identify `Zhat` with the image of Mathlib's `𝔸ᶠ[ℤ, ℚ]ˣ` via
  `Padic.adicCompletionEquiv`. The component map `ev p a := (adicCompletionEquiv ℤ p).symm (a (primesEquiv.symm p))`,
  `ev_mul`, `ev_one` elaborate; but (i) any use of `PadicInt.adicCompletionIntegersEquiv ℤ p` (even `.toAlgEquiv`)
  fails with "synthesized type class instance is not definitionally equal" (instAlgebraSubtype… vs
  Ring.toIntAlgebra on `adicCompletionIntegers`), and (ii) unfolding `Padic.adicCompletionEquiv` to reach
  `padicEquiv_bijOn` gives a kernel deterministic timeout (even via `simp only`/`rw` with
  `ContinuousAlgEquiv.symm_trans_apply`, `cast_symm_apply`). Not pursued further.
