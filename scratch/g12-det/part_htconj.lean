
/-! ## g12-det: `HTConj` reduced to `HTExtend` (independence of the coefficient field) -/

section G12DetHTSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- **Hodge–Tate multiplicities do not depend on the finite coefficient field (GLUE, about the
definition `PkgI4.LocalHasHTWeights`; STANDARD).** If a `ℚ̄_p`-valued `ρ` has a model `ρ_E` over a
finite `E ⊆ ℚ̄_p` with weights `S`, then for every finite `E' ⊇ E` the model over `E'` (the same
matrices) has weights `S`. Argument: `E' ⊗_E E^n ≅ (E^n)^{[E':E]}` as `ℚ_p[G]`-modules (`G` acts
trivially on `E'`), so `dim_{ℚ_p} H_i(ρ_{E'}) = [E':E] dim_{ℚ_p} H_i(ρ_E)` and `htMult`, which divides
by `[E':ℚ_p]`, is unchanged. (The docstring of `LocalHasHTWeights` asserts this, STANDARD.) -/
def HTExtend : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : PkgI4.GQp p →* GL (Fin n) (PadicAlgCl p))
    (S : Multiset ℤ) (E E' : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'], E ≤ E' →
    ∀ ρE : PkgI4.GQp p →* GL (Fin n) E,
      (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) →
      PkgI4.HasHTWeights p ρE S →
      ∃ ρE' : PkgI4.GQp p →* GL (Fin n) E',
        (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E' (PadicAlgCl p)) (ρE' σ) = ρ σ) ∧
        PkgI4.HasHTWeights p ρE' S

/-- Conjugating a model by `P ∈ GL_n(E)` does not change the Hodge–Tate spaces' dimensions. -/
lemma finrank_htSpace_conj {p : ℕ} [Fact p.Prime] {n : ℕ} {E : Type*} [Field E]
    [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (ρ ρ' : PkgI4.GQp p →* GL (Fin n) E) (P : GL (Fin n) E)
    (h : ∀ σ, ρ' σ = P⁻¹ * ρ σ * P) (i : ℤ) :
    Module.finrank ℚ_[p] (PkgI4.htSpace p ρ' i) = Module.finrank ℚ_[p] (PkgI4.htSpace p ρ i) := by
  let A : Matrix (Fin n) (Fin n) E := (P : Matrix (Fin n) (Fin n) E)
  let B : Matrix (Fin n) (Fin n) E := ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
  have hAB : A * B = 1 := by simp [A, B]
  have hBA : B * A = 1 := by simp [A, B]
  have hρ' : ∀ σ, ((ρ' σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      B * (ρ σ : Matrix (Fin n) (Fin n) E) * A := by
    intro σ; rw [h σ]; simp [A, B]
  let LA : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) := (Matrix.mulVecLin A).restrictScalars ℚ_[p]
  let LB : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) := (Matrix.mulVecLin B).restrictScalars ℚ_[p]
  let TA := LinearMap.lcomp ℚ_[p] ℂ_[p] LA
  let TB := LinearMap.lcomp ℚ_[p] ℂ_[p] LB
  have hTA : ∀ φ ∈ PkgI4.htSpace p ρ i, TA φ ∈ PkgI4.htSpace p ρ' i := by
    intro φ hφ σ v
    have := hφ σ (A.mulVec v)
    simp only [TA, LA, LinearMap.lcomp_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at this ⊢
    rw [hρ', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
    exact this
  have hTB : ∀ φ ∈ PkgI4.htSpace p ρ' i, TB φ ∈ PkgI4.htSpace p ρ i := by
    intro φ hφ σ v
    have := hφ σ (B.mulVec v)
    simp only [TB, LB, LinearMap.lcomp_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at this ⊢
    rw [hρ', Matrix.mulVec_mulVec, Matrix.mul_assoc _ A B, hAB, Matrix.mul_one] at this
    rw [Matrix.mulVec_mulVec]
    exact this
  let f : PkgI4.htSpace p ρ i →ₗ[ℚ_[p]] PkgI4.htSpace p ρ' i := TA.restrict hTA
  let g : PkgI4.htSpace p ρ' i →ₗ[ℚ_[p]] PkgI4.htSpace p ρ i := TB.restrict hTB
  have e : PkgI4.htSpace p ρ i ≃ₗ[ℚ_[p]] PkgI4.htSpace p ρ' i := LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext; intro φ; apply Subtype.ext; apply LinearMap.ext; intro v
      simp [f, g, TA, TB, LA, LB, Matrix.mulVec_mulVec, hAB, hBA])
    (by
      apply LinearMap.ext; intro φ; apply Subtype.ext; apply LinearMap.ext; intro v
      simp [f, g, TA, TB, LA, LB, Matrix.mulVec_mulVec, hAB, hBA])
  exact e.finrank_eq.symm

/-- **`HTConj` from `HTExtend`.** -/
theorem htConj_of (hX : HTExtend) : HTConj := by
  intro ℓ _ n r ρ' S hconj hr
  obtain ⟨P, hP⟩ := hconj
  obtain ⟨E, hEfd, ρE, hmap, hHT⟩ := hr
  let T : Set (PadicAlgCl ℓ) :=
    Set.range (fun ij : Fin n × Fin n => (P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) ij.1 ij.2) ∪
    Set.range (fun ij : Fin n × Fin n =>
      ((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) ij.1 ij.2)
  have hTfin : Finite T := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  have hadj : FiniteDimensional ℚ_[ℓ] (IntermediateField.adjoin ℚ_[ℓ] T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E' : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) := E ⊔ IntermediateField.adjoin ℚ_[ℓ] T
  have hE'fd : FiniteDimensional ℚ_[ℓ] E' := IntermediateField.finiteDimensional_sup _ _
  obtain ⟨ρE', hmap', hHT'⟩ := hX ℓ n (r.restrictLocal ℓ) S E E' le_sup_left ρE hmap hHT
  have hmemT : ∀ x ∈ T, x ∈ E' := fun x hx =>
    (le_sup_right : IntermediateField.adjoin ℚ_[ℓ] T ≤ E') (IntermediateField.subset_adjoin _ _ hx)
  let Pm : Matrix (Fin n) (Fin n) E' := Matrix.of fun i j =>
    ⟨(P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j, hmemT _ (Or.inl ⟨(i, j), rfl⟩)⟩
  let Qm : Matrix (Fin n) (Fin n) E' := Matrix.of fun i j =>
    ⟨((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j,
      hmemT _ (Or.inr ⟨(i, j), rfl⟩)⟩
  let φ := algebraMap E' (PadicAlgCl ℓ)
  have hinj : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) E' → _) := by
    intro M N hMN
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hMN i) j)
  have hPm : φ.mapMatrix Pm = (P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    ext i j; rfl
  have hQm : φ.mapMatrix Qm =
      ((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    ext i j; rfl
  have hPQ : Pm * Qm = 1 := hinj (by rw [map_mul, map_one, hPm, hQm]; simp)
  have hQP : Qm * Pm = 1 := hinj (by rw [map_mul, map_one, hPm, hQm]; simp)
  let P' : GL (Fin n) E' := ⟨Pm, Qm, hPQ, hQP⟩
  have hP' : Matrix.GeneralLinearGroup.map φ P' = P := by
    apply Units.ext
    exact hPm
  let ρ'E : PkgI4.GQp ℓ →* GL (Fin n) E' :=
    { toFun := fun σ => P'⁻¹ * ρE' σ * P'
      map_one' := by simp
      map_mul' := fun σ τ => by simp [mul_assoc] }
  refine ⟨E', hE'fd, ρ'E, ?_, ?_⟩
  · intro σ
    change Matrix.GeneralLinearGroup.map φ (P'⁻¹ * ρE' σ * P') = _
    rw [map_mul, map_mul, map_inv, hP', hmap' σ]
    change P⁻¹ * r.toHom (PkgI4.decomp ℓ σ) * P = ρ'.toHom (PkgI4.decomp ℓ σ)
    rw [hP]
    group
  · intro w
    unfold PkgI4.htMult
    rw [finrank_htSpace_conj ρE' ρ'E P' (fun σ => rfl) (-w)]
    exact hHT' w

end G0Galois

end

end G12DetHTSec

#print axioms G0Galois.finrank_htSpace_conj
#print axioms G0Galois.htConj_of
