import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Literal contracts for the valuation and section suppliers

These proposition values import only Mathlib, not the proof implementations.
The primary statements keep their original universe-zero scope and contain no
caller-provided Henselian, residue-closure, DVR, Noetherian or injectivity premise.
-/

open CategoryTheory AlgebraicGeometry CommRingCat
open MonoidalCategory CartesianMonoidalCategory

namespace DiophantineTate.Expected

def residueClosed : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (V : ValuationSubring Ω),
    IsAlgClosed (IsLocalRing.ResidueField V)

def henselian : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (V : ValuationSubring Ω),
    HenselianLocalRing V

def monicRootMem : Prop :=
  ∀ {Ω : Type} [Field Ω] (V : ValuationSubring Ω)
    (f : Polynomial V), f.Monic → ∀ x : Ω,
      (f.map V.subtype).IsRoot x → x ∈ V

def etaleSectionsInjective : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (T : Over (Spec (CommRingCat.of R))) [Etale T.hom],
    Function.Injective
      (fun Q : 𝟙_ (Over (Spec (of R))) ⟶ T =>
        toUnit
          (Over.mk
            (Spec.map
              (ofHom
                (algebraMap R (IsLocalRing.ResidueField R))))) ≫ Q)

end DiophantineTate.Expected
