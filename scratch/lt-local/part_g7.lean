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
