/-! # lt-local, part 1: a field isomorphism `ℂ ≃ ℚ̄_ℓ` extending two given embeddings of `ℚ̄`

`exists_equiv_extending ιC j`: for embeddings `ιC : ℚ̄ → ℂ` and `j : ℚ̄ → ℚ̄_ℓ` there is a ring
isomorphism `Φ : ℂ ≃+* ℚ̄_ℓ` with `Φ ∘ ιC = j` (both fields are algebraically closed over `ℚ̄`
with transcendence bases of cardinality `𝔠`; Mathlib's `IsAlgClosure.equivOfEquiv` applied to the
`ℚ̄`-algebra isomorphism of the two polynomial rings on the bases). It transports `G7Data`'s
`ℂ^×`-valued cochain `β = ιC ∘ β_ℚ̄` to `j ∘ β_ℚ̄`, as `G7Clauses` asks.

`padic_card_le` and `padicAlgCl_card` are copied verbatim from g8-tate's `part_tools.lean`
(namespace `G8Tate`, renamed here to `LTLocal` to avoid a clash at integration). -/

noncomputable section

namespace LTLocal

open Cardinal LadicCond

/-- (copied from g8-tate) `#ℚ_p ≤ 𝔠`. -/
theorem padic_card_le (p : ℕ) [Fact p.Prime] : #ℚ_[p] ≤ 𝔠 := by
  have hex : ∀ x : ℚ_[p], ∀ n : ℕ, ∃ r : ℚ, ‖x - r‖ < 1 / ((n : ℝ) + 1) :=
    fun x n => Padic.rat_dense p x (by positivity)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hpos)
    have h1 := hf x n
    have h2 := hf y n
    rw [hxy] at h1
    have h3 : ‖x - y‖ ≤ ‖x - (f y n : ℚ_[p])‖ + ‖y - (f y n : ℚ_[p])‖ := by
      calc ‖x - y‖ = ‖(x - (f y n : ℚ_[p])) - (y - (f y n : ℚ_[p]))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  calc #ℚ_[p] ≤ #(ℕ → ℚ) := mk_le_of_injective hinj
    _ = 𝔠 := by
      rw [← power_def, Cardinal.mkRat, mk_nat, aleph0_power_aleph0]

/-- (copied from g8-tate) `#ℚ̄_ℓ = 𝔠`. -/
theorem padicAlgCl_card (ℓ : ℕ) [Fact ℓ.Prime] : #(PadicAlgCl ℓ) = 𝔠 := by
  apply le_antisymm
  · calc #(PadicAlgCl ℓ) ≤ max #ℚ_[ℓ] ℵ₀ :=
          Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[ℓ] (PadicAlgCl ℓ)
      _ ≤ 𝔠 := max_le (padic_card_le ℓ) aleph0_le_continuum
  · calc 𝔠 ≤ #ℚ_[ℓ] := continuum_le_cardinal_of_nontriviallyNormedField _
      _ ≤ #(PadicAlgCl ℓ) := mk_le_of_injective (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

/-- `ℚ̄` is countable. -/
theorem qbar_card_le : #PkgI4.Qbar ≤ ℵ₀ := by
  calc #PkgI4.Qbar ≤ max #ℚ ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max ℚ PkgI4.Qbar
    _ = ℵ₀ := by rw [Cardinal.mkRat, max_self]

/-- **Two algebraically closed fields of cardinality `𝔠` containing `ℚ̄` are isomorphic over
`ℚ̄` (proved).** Stated for the `ℚ̄`-algebra structures given by `ι` and `j`. -/
theorem exists_equiv_extending_aux {K M : Type} [Field K] [Field M] [IsAlgClosed K]
    [IsAlgClosed M] (ι : PkgI4.Qbar →+* K) (j : PkgI4.Qbar →+* M) (hK : #K = 𝔠) (hM : #M = 𝔠) :
    ∃ Φ : K ≃+* M, ∀ x, Φ (ι x) = j x := by
  letI : Algebra PkgI4.Qbar K := ι.toAlgebra
  letI : Algebra PkgI4.Qbar M := j.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis PkgI4.Qbar K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis PkgI4.Qbar M
  have hc : ℵ₀ < 𝔠 := aleph0_lt_continuum
  have hs' : #K = #s :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs qbar_card_le
      (hK ▸ hc)
  have ht' : #M = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht qbar_card_le
      (hM ▸ hc)
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.mp (by rw [← hs', ← ht', hK, hM])
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e' : Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : s → K)) ≃ₐ[PkgI4.Qbar]
      Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : t → M)) :=
    (hs.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv PkgI4.Qbar e)).trans ht.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K M e'.toRingEquiv, fun x => ?_⟩
  have h1 : ι x = algebraMap (Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : s → K))) K
      (algebraMap PkgI4.Qbar _ x) := rfl
  rw [h1, IsAlgClosure.equivOfEquiv_algebraMap]
  show algebraMap _ M (e' (algebraMap PkgI4.Qbar _ x)) = j x
  rw [AlgEquiv.commutes]
  rfl

/-- **`ℂ ≃+* ℚ̄_ℓ` extending given embeddings of `ℚ̄` (proved).** -/
theorem exists_equiv_extending {ℓ : ℕ} [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ Φ : ℂ ≃+* PadicAlgCl ℓ, ∀ x, Φ (ιC x) = j x :=
  exists_equiv_extending_aux ιC.toRingHom j.toRingHom mk_complex (padicAlgCl_card ℓ)

end LTLocal

end
