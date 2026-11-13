import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Maximal
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Existence
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.InertiaDegree
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Padic

noncomputable section

namespace UnramRootsTask

open PkgI4 (GQp)
open LadicCond Polynomial TauCeti IntermediateField ValuativeRel

variable {p : ℕ} [Fact p.Prime]

/-- Frobenius data of a finite `F/ℚ_p` (TC-free): `q > 1` a power of `p` (the residue cardinality),
a Frobenius lift `φ ∈ G_F` raising the roots of every `X^{q^f} − X` to the `q`-th power, and every
`σ ∈ G_F` acting on the roots of `X^{q^f} − X` as a power `x ↦ x^{q^k}`. -/
def FrobData (F : Fld p) (q : ℕ) (φ : GQp p) : Prop :=
  1 < q ∧ (∃ e : ℕ, q = p ^ e) ∧ φ ∈ fixSet F ∧
  (∀ (f : ℕ) (x : Kbar p), 0 < f → x ^ q ^ f = x → φ x = x ^ q) ∧
  (∀ σ ∈ fixSet F, ∀ f : ℕ, 0 < f → ∃ k : ℕ, ∀ x : Kbar p, x ^ q ^ f = x → σ x = x ^ q ^ k)

/-- `σ ∈ G_F` as an `F`-automorphism of `ℚ̄_p`. -/
def toF (F : Fld p) (σ : GQp p) (hσ : σ ∈ fixSet F) : Kbar p ≃ₐ[F] Kbar p :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun c => hσ (c : Kbar p) c.2)

theorem toF_apply (F : Fld p) (σ : GQp p) (hσ : σ ∈ fixSet F) (x : Kbar p) :
    toF F σ hσ x = σ x := rfl

theorem mem_rootSet_of_pow (F : Fld p) {q f : ℕ} (hq : 1 < q) (hf : 0 < f) {x : Kbar p}
    (hx : x ^ q ^ f = x) : x ∈ (X ^ q ^ f - X : F[X]).rootSet (Kbar p) := by
  have hdeg : 1 < q ^ f := Nat.one_lt_pow hf.ne' hq
  have hne : (X ^ q ^ f - X : F[X]) ≠ 0 :=
    (monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hdeg)).ne_zero
  rw [mem_rootSet_of_ne hne]
  simp [hx]

/-- **Frobenius data from Tau Ceti (proved).** -/
theorem frobData_exists (F : Fld p) [FiniteDimensional ℚ_[p] F] : ∃ q φ, FrobData F q φ := by
  letI := finiteIntermediateFieldValuativeRel ℚ_[p] (Kbar p) F
  letI := finiteIntermediateFieldTopology ℚ_[p] (Kbar p) F
  haveI := finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (Kbar p) F
  haveI := finiteIntermediateField_valuativeExtension ℚ_[p] (Kbar p) F
  set q := Nat.card 𝓀[F] with hqdef
  have hq1 : 1 < q := Finite.one_lt_card
  have hpq : ∃ e : ℕ, q = p ^ e := by
    have h2 : q = Nat.card 𝓀[ℚ_[p]] ^ inertiaDegree ℚ_[p] F := TauCeti.natCard_residueField ℚ_[p] F
    rw [Padic.natCard_residueField p] at h2
    exact ⟨_, h2⟩
  haveI : Algebra.IsIntegral F (Kbar p) := Algebra.IsIntegral.tower_top ℚ_[p]
  haveI : IsAlgClosure F (Kbar p) := ⟨inferInstance, inferInstance⟩
  haveI : Normal F (Kbar p) := IsAlgClosure.normal F (Kbar p)
  set E := maximalUnramifiedExtension F (Kbar p)
  set Φ := maximalUnramifiedFrobenius F (Kbar p)
  set φF : Kbar p ≃ₐ[F] Kbar p := Φ.liftNormal (Kbar p)
  refine ⟨q, φF.restrictScalars ℚ_[p], hq1, hpq, ?_, ?_, ?_⟩
  · intro x hx
    exact φF.commutes ⟨x, hx⟩
  · intro f x hf hx
    have hxL := rootSet_subset_unramifiedExtension F (Kbar p) f (mem_rootSet_of_pow F hq1 hf hx)
    have hxE : x ∈ E := unramifiedExtension_le_maximalUnramifiedExtension F (Kbar p) f hxL
    change φF x = x ^ q
    have h := AlgEquiv.liftNormal_commutes Φ (Kbar p) ⟨x, hxE⟩
    have hx' : (⟨x, hxE⟩ : E) ^ q ^ f = ⟨x, hxE⟩ := Subtype.ext (by simp [hx])
    rw [maximalUnramifiedFrobenius_apply_of_pow_natCard_pow_eq_self hf.ne' hx'] at h
    simpa using h
  · intro σ hσ f hf
    set L := unramifiedExtension F (Kbar p) f
    letI := finiteIntermediateFieldValuativeRel F (Kbar p) L
    letI := finiteIntermediateFieldTopology F (Kbar p) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField F (Kbar p) L
    haveI := finiteIntermediateField_valuativeExtension F (Kbar p) L
    haveI : IsUnramified F L := isUnramified_unramifiedExtension hf.ne'
    set σL : L ≃ₐ[F] L := (toF F σ hσ).restrictNormal L
    have hmem : σL ∈ Subgroup.zpowers (frobeniusAlgEquiv (K := F) (L := L)) := by
      rw [zpowers_frobeniusAlgEquiv]; trivial
    rw [← mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, fun x hx => ?_⟩
    have hxL : x ∈ L := rootSet_subset_unramifiedExtension F (Kbar p) f (mem_rootSet_of_pow F hq1 hf hx)
    have h1 : σ x = (σL ⟨x, hxL⟩ : Kbar p) :=
      (AlgEquiv.restrictNormal_commutes (toF F σ hσ) L ⟨x, hxL⟩).symm
    rw [h1, ← hk]
    have key : ∀ j : ℕ, ∀ y : L, y ^ q ^ f = y →
        (frobeniusAlgEquiv (K := F) (L := L) ^ j) y = y ^ q ^ j := by
      intro j
      induction j with
      | zero => intro y _; simp
      | succ j ih =>
        intro y hy
        have hyq : (y ^ q) ^ q ^ f = y ^ q := by rw [← pow_mul, mul_comm, pow_mul, hy]
        rw [pow_succ', AlgEquiv.mul_apply, ih y hy, map_pow,
          frobeniusAlgEquiv_apply_of_pow_natCard_pow_eq_self hf.ne' hy, ← pow_mul]
        show y ^ (q * q ^ j) = _
        rw [← pow_succ']
    have hy : (⟨x, hxL⟩ : L) ^ q ^ f = ⟨x, hxL⟩ := Subtype.ext (by simp [hx])
    rw [key k _ hy]
    simp

end UnramRootsTask
