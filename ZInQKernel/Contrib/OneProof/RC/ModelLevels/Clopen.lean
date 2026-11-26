import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Localization.BaseChange

/-! # Complements of closed subschemes in finite étale algebras -/

namespace WeierstrassCurve.ModelLevels

open scoped TensorProduct

variable {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
  [Algebra A S] [Algebra A T]

/-- A surjection between étale algebras over the same base has an idempotent
generator of its kernel. On geometric points the corresponding closed
subscheme is the zero locus of this idempotent. -/
theorem exists_idempotent_ker [Algebra.Etale A S] [Algebra.Etale A T]
    (f : S →ₐ[A] T) (hf : Function.Surjective f) :
    ∃ e : S, IsIdempotentElem e ∧ RingHom.ker f = Ideal.span {e} := by
  letI := f.toAlgebra
  haveI : IsScalarTower A S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  exact (Ideal.isIdempotentElem_iff_of_fg _
    (Algebra.FinitePresentation.ker_fG_of_surjective f hf)).mp
      ((Algebra.FormallyEtale.iff_of_surjective hf).mp (.of_restrictScalars (R := A)))

/-- The locus where an idempotent is one, equivalently the complement of its
vanishing locus. -/
abbrev ClopenFactor {S : Type*} [CommRing S] (e : S) :=
  Localization.Away e

/-- Localizing at an idempotent is a finite étale factor of any finite étale
algebra. The localization map is surjective. -/
theorem clopenFactor_finite_etale [Module.Finite A S] [Algebra.Etale A S]
    {e : S} (he : IsIdempotentElem e) :
    Module.Finite A (ClopenFactor e) ∧
      Algebra.Etale A (ClopenFactor e) ∧
      Function.Surjective (algebraMap S (ClopenFactor e)) := by
  let L := ClopenFactor e
  have hsurj : Function.Surjective (algebraMap S L) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he
  let f : S →ₐ[A] L := IsScalarTower.toAlgHom A S L
  exact ⟨Module.Finite.of_surjective f.toLinearMap hsurj, .comp A S L, hsurj⟩

/-- The clopen factor can be formed before or after any base extension. -/
noncomputable def clopenFactorBaseChange (B : Type*) [CommRing B] [Algebra A B] (e : S) :
    B ⊗[A] ClopenFactor e ≃ₐ[B] ClopenFactor ((1 : B) ⊗ₜ[A] e) :=
  IsLocalization.Away.tensorProductEquivTMulRight A B e (ClopenFactor e)

/-- The base-change comparison is the canonical map on numerators. -/
theorem clopenFactorBaseChange_tmul (B : Type*) [CommRing B] [Algebra A B]
    (e s : S) (b : B) :
    clopenFactorBaseChange (A := A) B e (b ⊗ₜ[A] algebraMap S (ClopenFactor e) s) =
      algebraMap _ _ (b ⊗ₜ[A] s) :=
  IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := A) (S := B) (A := S)
    (g := e) (B := ClopenFactor e) (x := b) (a := s)

/-- For a field-valued point, factoring through the closed subscheme cut out
by a surjection is exactly vanishing on its kernel idempotent. -/
theorem factorsThrough_iff_idempotent_vanishes
    {k : Type*} [Field k] [Algebra A k] (f : S →ₐ[A] T) (hf : Function.Surjective f)
    (x : S →ₐ[A] k) {e : S} (hker : RingHom.ker f = Ideal.span {e}) :
    (∃ y : T →ₐ[A] k, y.comp f = x) ↔ x e = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h : e ∈ RingHom.ker f := hker.symm ▸ Ideal.subset_span (Set.mem_singleton e)
    change y (f e) = 0
    rw [RingHom.mem_ker.mp h, map_zero]
  · intro he
    have hle : RingHom.ker f ≤ RingHom.ker x := by
      rw [hker, Ideal.span_le, Set.singleton_subset_iff]
      exact (RingHom.mem_ker (f := x.toRingHom)).2 he
    exact ⟨f.liftOfSurjective hf x hle, AlgHom.liftOfSurjective_comp f hf x hle⟩

#print axioms exists_idempotent_ker
#print axioms clopenFactor_finite_etale
#print axioms clopenFactorBaseChange_tmul
#print axioms factorsThrough_iff_idempotent_vanishes

end WeierstrassCurve.ModelLevels
