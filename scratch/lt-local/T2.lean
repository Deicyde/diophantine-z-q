import Base
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.Classification

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

/-! # lt-local, part 2: `G7Clauses` and `dim A_{L'} = 2` for `TateBridge35`'s transported data

* `g7Clauses_of_transport`: local-data's `G7Clauses (j ∘ β_ℚ̄) ε' L` from `G7Data`, the bound
  `[L:ℚ] ≤ D` (local-data's finding F3: `G7Data` does not carry it), `ιC ∘ β_ℚ̄ = β` and
  `∂(j ∘ β_ℚ̄) = ε'` (both in `TateBridge35`'s output). The `ℂ^×`-valued clauses are carried to
  `ℚ̄_ℓ` by a field isomorphism `Φ : ℂ ≃ ℚ̄_ℓ` with `Φ ∘ ιC = j` (part 1), so that
  `j ∘ β_ℚ̄ = Φ ∘ β`; `ε' = 1` on `G_L × G_L` because `ε = 1` there (`DescentDatum`) and
  `j ∘ β_ℚ̄` has no zero. The proof of the clauses for `Φ ∘ β` follows g8-tate's
  `g7Clauses_of_g7Data` (copied, with `ε'` in place of `Φ ∘ ε`).
* `dim_bc_of_g7Data`: `dim A_{L'} = 2` from `G7Data`'s last clause `IsModelOver L' A_{L'} P`,
  `P.surface` and g0-dim's `pkgI3_dim_baseChange` (the proof of g0-split's `model_dim`). -/

noncomputable section

namespace LTLocal

open PkgI4 (GQ GQp decomp)
open LadicCond G0ModField
open ZInQ LeafQM.AV GlueDescent.B2
open CategoryTheory AlgebraicGeometry

/-- (copied from g8-tate) `T u` consists of primes. -/
theorem T_prime (u : ℚ) : ∀ q ∈ T u, q.Prime := by
  obtain ⟨hS, -, -⟩ := admissible_S_mul
  intro q hq
  rcases Finset.mem_union.mp hq with h | h
  · exact hS q h
  · exact Nat.prime_of_mem_primeFactors h

/-- **`G7Clauses` for the transported cochain `j ∘ β_ℚ̄` (proved).** -/
theorem g7Clauses_of_transport {ℓ : ℕ} [Fact ℓ.Prime] {u : ℚ}
    {P : QML3 Qbar} {L : IF} [FiniteDimensional ℚ L] {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (hC : ∀ g, ιC (βQ g) = (β g : ℂ)) {ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ}
    (hε' : ∀ g h, j (βQ g) * j (βQ h) = ε' g h * j (βQ (g * h))) :
    G15Ram.G7Clauses (fun g => j (βQ g)) ε' L := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_extending ιC j
  have hjβ : ∀ g, j (βQ g) = Φ (β g : ℂ) := fun g => by rw [← hC, hΦ]
  have hne : ∀ g, Φ (β g : ℂ) ≠ 0 := fun g => (map_ne_zero Φ).mpr (Units.ne_zero _)
  obtain ⟨-, hDD, -, -, ⟨Tm, hTmT, hN⟩, hβlc, hβsq, hβε, -⟩ := h
  have hfun : (fun g => j (βQ g)) = fun g => Φ (β g : ℂ) := funext hjβ
  refine ⟨inferInstance, hLD, hε', fun g => by simp only [hjβ]; exact hne g, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hβlc.comp (fun z : ℂˣ => Φ (z : ℂ))
  · have hT : ∀ q ∈ Tm, q.Prime := fun q hq => T_prime u q (hTmT hq)
    subst hN
    refine ⟨Tm, hT, inferInstance, χ, Units.map Φ.toRingHom.toMonoidHom, fun g => ?_⟩
    show j (βQ g) ^ 2 = Φ ((GlueDescent.B2Q.galChar χ g : ℂˣ) : ℂ)
    rw [hjβ, ← map_pow, ← Units.val_pow_eq_pow_val, hβsq g]
  · intro g h hg _
    obtain ⟨hε, hinf, h11, -⟩ := hDD
    have h1 := GlueDescent.B3Q.inflatedNormalized_of L ε hε hinf h11 g h
      (Or.inl (GlueDescent.B3Q.mem_GQL.mpr hg))
    have h2 := hβε g h
    rw [h1, one_mul] at h2
    have h3 := hε' g h
    rw [hjβ, hjβ, hjβ, ← map_mul, ← Units.val_mul, h2] at h3
    exact mul_right_cancel₀ (hne (g * h)) (h3.symm.trans (one_mul _).symm)

/-- **`dim A_{L'} = 2` on G7's data (proved)**: G7Data's clause `IsModelOver L' A_{L'} P`,
`P.surface` and g0-dim's `pkgI3_dim_baseChange` (as g0-split's `model_dim`). -/
theorem dim_bc_of_g7Data {u : ℚ} {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL') :
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := by
  obtain ⟨e⟩ := h.2.2.2.2.2.2.2.2.2.2.2
  rw [← G0Dim.pkgI3_dim_baseChange Qbar (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')),
    ← P.surface]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso ((Over.forget _).mapIso e)).isHomeomorph

end LTLocal

end

#print axioms LTLocal.g7Clauses_of_transport
#print axioms LTLocal.dim_bc_of_g7Data
