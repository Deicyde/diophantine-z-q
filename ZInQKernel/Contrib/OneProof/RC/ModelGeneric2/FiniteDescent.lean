import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Artinian.Module

/-! # Descent of values on a finite reduced algebra -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

variable {K L B : Type*} [Field K] [Field L] [CommRing B]
  [Algebra K L] [Algebra K B] [IsAlgClosed L] [Module.Finite K B] [IsReduced B]

private noncomputable def maximalEmbedding (m : MaximalSpectrum B) :
    B ⧸ m.asIdeal →ₐ[K] L := by
  letI := m.isMaximal
  letI : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact IsAlgClosed.lift

/-- The geometric points of a finite reduced algebra separate its elements. -/
theorem geometricPoints_separate (b c : B) (h : ∀ x : B →ₐ[K] L, x b = x c) : b = c := by
  letI : IsArtinianRing B := isArtinian_of_tower K (inferInstance : IsArtinian K B)
  apply (IsArtinianRing.equivPi B).injective
  funext m
  letI := m.isMaximal
  letI : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact (maximalEmbedding (K := K) (L := L) m).injective
    (h ((maximalEmbedding m).comp (Ideal.Quotient.mkₐ K m.asIdeal)))

private theorem conjugateEmbeddings {F : Type*} [Field F] [Algebra K F] [Normal K L]
    (f g : F →ₐ[K] L) :
    ∃ σ : L ≃ₐ[K] L, σ.toAlgHom.comp f = g := by
  let ef := f.equivFieldRange
  let eg := g.equivFieldRange
  let e := ef.symm.trans eg
  refine ⟨e.liftNormal L, AlgHom.ext fun t => ?_⟩
  have h := e.liftNormal_commutes L (ef t)
  rw [show e (ef t) = eg t by simp [e]] at h
  exact h

/-- A Galois-equivariant function on the geometric points of a finite reduced algebra
with values in an algebraically closed Galois extension comes from a unique algebra
element. Apply fixed-field descent in each factor of the Artinian product. -/
theorem finiteReduced_descent [IsGalois K L] (v : (B →ₐ[K] L) → L)
    (hv : ∀ (σ : L ≃ₐ[K] L) (x : B →ₐ[K] L), v (σ.toAlgHom.comp x) = σ (v x)) :
    ∃! b : B, ∀ x : B →ₐ[K] L, x b = v x := by
  classical
  letI : IsArtinianRing B := isArtinian_of_tower K (inferInstance : IsArtinian K B)
  let q (m : MaximalSpectrum B) := Ideal.Quotient.mkₐ K m.asIdeal
  let f (m : MaximalSpectrum B) := maximalEmbedding (K := K) (L := L) m
  have inRange (m : MaximalSpectrum B) : ∃ z, f m z = v ((f m).comp (q m)) := by
    letI := m.isMaximal
    letI : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    change v ((f m).comp (q m)) ∈ (f m).fieldRange
    rw [← InfiniteGalois.fixedField_fixingSubgroup (f m).fieldRange,
      IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
    have he : σ.toAlgHom.comp ((f m).comp (q m)) = (f m).comp (q m) :=
      AlgHom.ext fun b => h _ ⟨q m b, rfl⟩
    exact (hv σ ((f m).comp (q m))).symm.trans (congrArg v he)
  let z (m : MaximalSpectrum B) := (inRange m).choose
  let b := (IsArtinianRing.equivPi B).symm z
  have hb (m : MaximalSpectrum B) : q m b = z m :=
    congrFun ((IsArtinianRing.equivPi B).apply_symm_apply z) m
  have heval (x : B →ₐ[K] L) : x b = v x := by
    let m : MaximalSpectrum B :=
      ⟨RingHom.ker x, (IsArtinianRing.isPrime_iff_isMaximal _).mp (RingHom.ker_isPrime x)⟩
    letI := m.isMaximal
    letI : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    let g := Ideal.Quotient.liftₐ m.asIdeal x (fun _ h => h)
    have hg : g.comp (q m) = x := Ideal.Quotient.liftₐ_comp _ _ _
    obtain ⟨σ, hσ⟩ := conjugateEmbeddings (f m) g
    have hx : σ.toAlgHom.comp ((f m).comp (q m)) = x := by
      rw [← AlgHom.comp_assoc, hσ, hg]
    rw [← hx, hv]
    change σ (f m (q m b)) = σ (v ((f m).comp (q m)))
    rw [hb, (inRange m).choose_spec]
  exact ⟨b, heval, fun c hc => geometricPoints_separate c b fun x => (hc x).trans (heval x).symm⟩

#print axioms maximalEmbedding
#print axioms geometricPoints_separate
#print axioms conjugateEmbeddings
#print axioms finiteReduced_descent

end WeierstrassCurve.ModelLevels.ModelGeneric2
