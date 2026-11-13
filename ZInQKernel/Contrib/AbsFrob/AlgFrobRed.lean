import ZInQKernel.Contrib.AbsFrob.Basic

-- Adopted by task frob-contrib from scratch/afr-absfrob/AbsFrobDef.lean (task afr-absfrob), namespace `AlgFrobRedRed`, unchanged; `#print axioms` moved to scratch/frob-contrib/Check.lean.

/-! # The Prop `AlgFrobRedRed.AbsFrob` of task alg-frob-red, proved

`AbsFrob` is copied verbatim from `scratch/alg-frob-red/AlgFrobRed.lean` (via afr-absfrob); its proof
takes `Fr = AbsFrobDef.fr`. -/

noncomputable section

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry

/-- **`AbsFrob` (GLUE; the absolute Frobenius of an `𝔽_p`-scheme; standard, e.g. SGA 5 XIV,
Stacks Tag 0CC6 (locators UNVERIFIED); not in Mathlib 4.35).** For a scheme `X` over a field `k`
of characteristic `p` there is an endomorphism `Fr_X` (the identity on the space, `f ↦ f^p` on
sections) lying over `Fr_{Spec k} = Spec(z ↦ z^p)`, and natural for points: for every ring `R` of
characteristic `p` and `g : Spec R → X`, `Spec(r ↦ r^p) ≫ g = g ≫ Fr_X`. -/
def AbsFrob : Prop :=
  ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (X : Over (Spec (.of k))),
    ∃ Fr : X.left ⟶ X.left,
      Fr ≫ X.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (frobenius k p)) ∧
      ∀ (R : Type) [CommRing R] [CharP R p] (g : Spec (.of R) ⟶ X.left),
        Spec.map (CommRingCat.ofHom (frobenius R p)) ≫ g = g ≫ Fr

/-- `frobenius R p` is `AbsFrobDef.powHom`. -/
theorem frobenius_eq_powHom (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    frobenius R p = AbsFrobDef.powHom p R (CharP.cast_eq_zero R p) :=
  RingHom.ext fun _ => rfl

/-- **`AbsFrob` (proved):** `Fr_X = AbsFrobDef.fr`. -/
theorem absFrob : AbsFrob := by
  intro k _ p _ _ X
  have hk : ((p : ℕ) : CommRingCat.of k) = 0 := CharP.cast_eq_zero k p
  have hX := AbsFrobDef.natCast_of_hom p hk X.hom
  refine ⟨AbsFrobDef.fr p X.left hX, ?_, fun R _ _ g => ?_⟩
  · rw [frobenius_eq_powHom, ← AbsFrobDef.fr_Spec p (.of k) hk,
      AbsFrobDef.fr_naturality p X.hom]
  · have hR : ((p : ℕ) : CommRingCat.of R) = 0 := CharP.cast_eq_zero R p
    rw [frobenius_eq_powHom, ← AbsFrobDef.fr_Spec p (.of R) hR, AbsFrobDef.fr_naturality p g]

end AlgFrobRedRed
