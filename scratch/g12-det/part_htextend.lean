
/-! ## g12-det: `HTExtend` proved (Hodge–Tate multiplicities do not depend on the coefficient
field) -/

section G12DetHTExtSec

noncomputable section

namespace G0Galois

section Extend

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {E E' : Type} [Field E] [Field E'] [Algebra ℚ_[p] E]
  [Algebra ℚ_[p] E'] [Algebra E E'] [IsScalarTower ℚ_[p] E E'] [FiniteDimensional ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E'] {m : ℕ} (b : Module.Basis (Fin m) E E')

/-- `v ↦ (v_a • b_k)_a`. -/
def jk (k : Fin m) : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E') :=
  (LinearMap.pi fun a => (LinearMap.toSpanSingleton E E' (b k)).comp (LinearMap.proj a) :
    (Fin n → E) →ₗ[E] (Fin n → E')).restrictScalars ℚ_[p]

/-- `w ↦ (b.coord k (w_a))_a`. -/
def ck (k : Fin m) : (Fin n → E') →ₗ[ℚ_[p]] (Fin n → E) :=
  (LinearMap.pi fun a => (b.coord k).comp (LinearMap.proj a) :
    (Fin n → E') →ₗ[E] (Fin n → E)).restrictScalars ℚ_[p]

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma jk_apply (k : Fin m) (v : Fin n → E) (a : Fin n) : jk (p := p) b k v a = v a • b k := rfl

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_apply (k : Fin m) (w : Fin n → E') (a : Fin n) :
    ck (p := p) b k w a = b.repr (w a) k := rfl

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma jk_mulVec (k : Fin m) (M : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    jk (p := p) b k (M.mulVec v) = (M.map (algebraMap E E')).mulVec (jk (p := p) b k v) := by
  funext a
  simp only [jk_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  ring

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_mulVec (k : Fin m) (M : Matrix (Fin n) (Fin n) E) (w : Fin n → E') :
    ck (p := p) b k ((M.map (algebraMap E E')).mulVec w) = M.mulVec (ck (p := p) b k w) := by
  funext a
  simp only [ck_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_jk (k l : Fin m) (v : Fin n → E) :
    ck (p := p) b l (jk (p := p) b k v) = if k = l then v else 0 := by
  funext a
  rw [ck_apply, jk_apply, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma sum_jk_ck (w : Fin n → E') : ∑ k, jk (p := p) b k (ck (p := p) b k w) = w := by
  funext a
  simp only [Finset.sum_apply, jk_apply, ck_apply]
  exact b.sum_repr (w a)

/-- `htSpace` of the extended model is `htSpace` of the model, `m` times. -/
def htSpaceExtendEquiv (ρE : PkgI4.GQp p →* GL (Fin n) E) (i : ℤ) :
    PkgI4.htSpace p ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) i ≃ₗ[ℚ_[p]]
      (Fin m → PkgI4.htSpace p ρE i) where
  toFun φ k := ⟨φ.1.comp (jk (p := p) b k), by
    intro σ v
    have := φ.2 σ (jk (p := p) b k v)
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [jk_mulVec]
    exact this⟩
  invFun ψ := ⟨∑ k, (ψ k).1.comp (ck (p := p) b k), by
    intro σ w
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := (ψ k).2 σ (ck (p := p) b k w)
    have hm : ((((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) σ :
        GL (Fin n) E') : Matrix (Fin n) (Fin n) E') =
        ((ρE σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E E') := rfl
    rw [hm, ck_mulVec]
    exact h⟩
  left_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [← map_sum, sum_jk_ck]
  right_inv ψ := by
    funext k
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [Finset.sum_eq_single k]
    · rw [ck_jk, if_pos rfl]
    · intro l _ hl
      rw [ck_jk, if_neg (Ne.symm hl), map_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  map_add' φ ψ := by
    funext k; apply Subtype.ext; rfl
  map_smul' c φ := by
    funext k; apply Subtype.ext; rfl

include b in
lemma htMult_extend (ρE : PkgI4.GQp p →* GL (Fin n) E) (w : ℤ) :
    PkgI4.htMult p ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) w =
      PkgI4.htMult p ρE w := by
  have hm : 0 < m := by
    by_contra h
    have h0 : m = 0 := by omega
    subst h0
    have := b.index_nonempty
    exact (IsEmpty.false this.some)
  unfold PkgI4.htMult
  rw [(htSpaceExtendEquiv b ρE (-w)).finrank_eq,
    ← (Finsupp.linearEquivFunOnFinite ℚ_[p] (PkgI4.htSpace p ρE (-w)) (Fin m)).finrank_eq,
    Module.finrank_finsupp, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ_[p] E E',
    Module.finrank_eq_card_basis b, Fintype.card_fin, mul_comm (Module.finrank ℚ_[p] E) m]
  exact Nat.mul_div_mul_left _ _ hm

end Extend

/-- **`HTExtend`, proved.** -/
theorem htExtend : HTExtend := by
  intro p _ n ρ S E E' _ _ hle ρE hmap hHT
  letI : Algebra E E' := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[p] E E' := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite E E' := Module.Finite.of_restrictScalars_finite ℚ_[p] E E'
  haveI : Module.Free E E' := Module.Free.of_divisionRing E E'
  let b := Module.finBasis E E'
  refine ⟨(Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE, ?_, ?_⟩
  · intro σ
    rw [← hmap σ]
    apply Units.ext
    ext i j
    rfl
  · intro w
    rw [htMult_extend b ρE w]
    exact hHT w

end G0Galois

end

end G12DetHTExtSec

#print axioms G0Galois.htExtend
