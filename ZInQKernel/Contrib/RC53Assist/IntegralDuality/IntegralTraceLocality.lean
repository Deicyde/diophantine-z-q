import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralCompactTrace

/-!
# Finite-place cyclotomic localization into compact top cohomology

Nekovář, Selmer complexes, 5.4.1 (printed pp. 125–126), with 5.3.1.2,
5.1.3 and 5.2.1, identifies top compact cyclotomic cohomology with the
sum of the finite-place local invariants. Each individual finite-place
inclusion consequently induces an isomorphism from local degree two to
compact degree three. Right-exact reciprocity suffices: no leading
injectivity of global degree two or scalar self-injectivity is needed.

The literature proposition below mentions only the number field, finite
support and actual integral cyclotomic coefficient. Its map is constructed
explicitly as the pure local inclusion, with the existing shifted cone
signs. It is not a Kummer, elliptic-curve or self-duality assumption.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open scoped Classical

section Component

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

/-- The inclusion of one actual cochain component into its product. -/
def componentRelationInclusion (A : ι → GCx R) (v : ι) : GHom (A v) (piCx A) where
  f i j h := by
    subst h
    exact LinearMap.single R (fun w => (A w).X i) v
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    funext w
    change (Pi.single v ((A v).d i i₁ h₁ x) : ∀ w, (A w).X i₁) w =
      (A w).d i i₁ h₂ ((Pi.single v x : ∀ w, (A w).X i) w)
    by_cases h : w = v
    · subst w
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne h, map_zero]

/-- Shifting a relation-indexed map preserves the negative differential on both sides. -/
def shiftDownRelationHom {A B : GCx R} (f : GHom A B) : GHom (shiftDown A) (shiftDown B) where
  f i j h := f.f (i - 1) (j - 1) (by omega)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    change f.f (i₁ - 1) (j₁ - 1) _ (-(A.d (i - 1) (i₁ - 1) (by omega) x)) =
      -(B.d (j - 1) (j₁ - 1) (by omega) (f.f (i - 1) (j - 1) _ x))
    rw [map_neg, f.comm (i - 1) (i₁ - 1) (j - 1) (j₁ - 1)
      (by omega) (by omega) (by omega) (by omega) x]

end Component

/-- The exact pure finite-place inclusion into the compact cyclotomic cone. -/
def integralLocalToCompactTarget (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (v : Places K S) :
    GHom (shiftDown (localCx ℤ_[2] (GKS K S) (fun w : Places K S => Gloc K w.1)
      (fun w => locMap K S w.1) (IntegralTate1 K S) v)) (integralCompactTarget K S) := by
  classical
  let A := fun w : Places K S => localCx ℤ_[2] (GKS K S)
    (fun w : Places K S => Gloc K w.1) (fun w => locMap K S w.1) (IntegralTate1 K S) w
  exact ghomComp (shiftDownRelationHom (componentRelationInclusion A v))
    (coneIncl (resS ℤ_[2] (GKS K S) (fun w : Places K S => Gloc K w.1)
      (fun w => locMap K S w.1) (IntegralTate1 K S)))

/-- The inclusion really sends a local degree-two cochain to the pure local degree-three component. -/
theorem integralLocalToCompactTarget_three (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (v : Places K S)
    (c : (localCx ℤ_[2] (GKS K S) (fun w : Places K S => Gloc K w.1)
      (fun w => locMap K S w.1) (IntegralTate1 K S) v).X 2) :
    (integralLocalToCompactTarget K S v).f 3 3 rfl c =
      ((0, Pi.single v c) : (integralCompactTarget K S).X 3) := rfl

/-- Nekovář 5.4.1's general coefficient top-cohomology result and its finite-place localization.
This is a literature parameter; no inhabitant or new axiom is supplied by this declaration. -/
def NekovarIntegralCompactLocality : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ [HasTwoPowerRoots K S],
      Nonempty ((integralCompactTarget K S).toCC.homology 3 ≃ₗ[ℤ_[2]] ℤ_[2]) ∧
        ∀ v : Places K S, QuasiIsoAt (GHom.toCC (integralLocalToCompactTarget K S v)) 3

/-- The stronger coefficient-localization statement supplies the already recorded top result. -/
theorem NekovarIntegralCompactLocality.to_topCohomology
    (h : NekovarIntegralCompactLocality) : NekovarIntegralCompactTopCohomology :=
  fun K _ _ hK S hS h2 _ => (h K hK S hS h2).1

end ZInQ.Contrib.RC53Assist.IntegralDuality
