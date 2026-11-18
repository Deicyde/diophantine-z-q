import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.Consistency
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.SelmerPairing

/-!
# The identification phrased against the Selmer-complex interfaces

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
L5509–5517: the remaining complex `D` is obtained from the Selmer complex over `S = 𝒪[G]` by the
simultaneous new-local cancellation (an invertible block is canceled, a homotopy equivalence).

This file states the "`D` is the remaining complex" part of the single identification against
lane PairedFunctional's Selmer-complex interface `SelData` (`G --res--> L <--ι-- U`, with Selmer
complex `selCx`), so that a construction of genuine cochain-level Selmer complexes can discharge it
by instantiation:

* `BlockComplex.toGCx`: the block complex as a `GCx` (free modules `S^{D^i}` in degrees `0, …, 3`,
  zero elsewhere, differentials the block matrices);
* `SelmerIdentification b dK hK cE tK` (GLUE; extends `Identification`): Selmer data `sel` over
  `𝒪[G]` and a quasi-isomorphism (Mathlib's `QuasiIso`) from `D` to the Selmer complex of `sel`
  (`GCx.toCC`);
* `clearingModel_of_selmer`: RC0's `ClearingModel` from it and E1 (PROVED);
* `selmerIdentification_trivial`: consistency, the trivial complex with Selmer data
  `G = D, U = L = 0` (PROVED).

Caveat: `sel` is unconstrained (the identity quasi-isomorphism with zero local complexes inhabits
`SelmerIdentification`), so it does not pin `D` to a genuine Selmer complex; superseded by the
`Identification2` route (`ClearingComplex/NewLocalModel`).

The remaining fields (augmentation, poles, central counts) stay as in `Identification`; they are
statements about `D` and its Smith data, which a Selmer construction supplies through the
quasi-isomorphism (central counts) and the new-local cancellation (poles; lane SelmerDuality's
`SupportChangeData` / `UnramifiedNewPlace` are the interfaces of the new local places;
`UnramifiedNewPlace` is not instantiable by genuine continuous cochains, and re-pointing to the
genuine Galois support data is pending).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks ScalarData genuinePole)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

namespace BlockComplex

variable {S : Type} [CommRing S] (D : BlockComplex S)

/-- The basis index of `D^n` (empty outside degrees `0, …, 3`). -/
def idx : ℤ → Type
  | 0 => Fin D.m0
  | 1 => Fin D.m0 ⊕ Unit ⊕ Fin D.m1
  | 2 => Fin D.m1 ⊕ Unit ⊕ Fin D.m2
  | 3 => Fin D.m2
  | _ => Empty

/-- The differential `D^i → D^{i+1}` as a linear map. -/
def ddL : (i : ℤ) → (D.idx i → S) →ₗ[S] (D.idx (i + 1) → S)
  | 0 => D.d0.mulVecLin
  | 1 => D.d1.mulVecLin
  | 2 => D.d2.mulVecLin
  | _ => 0

theorem ddL_ddL (i : ℤ) (x : D.idx i → S) : D.ddL (i + 1) (D.ddL i x) = 0 := by
  match i with
  | 0 =>
    have h : ∀ y : Fin D.m0 → S, Matrix.mulVec D.d1 (Matrix.mulVec D.d0 y) = 0 := fun y => by
      rw [Matrix.mulVec_mulVec, D.d1_d0, Matrix.zero_mulVec]
    exact h x
  | 1 =>
    have h : ∀ y : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → S, Matrix.mulVec D.d2 (Matrix.mulVec D.d1 y) = 0 := fun y => by
      rw [Matrix.mulVec_mulVec, D.d2_d1, Matrix.zero_mulVec]
    exact h x
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change D.ddL (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The block complex as a `GCx`** (lane PairedFunctional's cochain complexes). -/
def toGCx : GCx S where
  X n := ModuleCat.of S (D.idx n → S)
  d i j h := by subst h; exact D.ddL i
  d_d i j k hij hjk x := by
    subst hij hjk
    exact D.ddL_ddL i x

theorem toGCx_d (i : ℤ) (x : D.idx i → S) : D.toGCx.d i (i + 1) rfl x = D.ddL i x := rfl

end BlockComplex

/-! ### The identification against `SelData` -/

/-- **The single identification, phrased against `SelData`** (GLUE): the fields of
`Identification`, together with Selmer data `sel` over `𝒪[G]` and a quasi-isomorphism from the
remaining complex `D` to the Selmer complex of `sel` (the new-local cancellation is a homotopy
equivalence, tex 5509–5513).

Caveat: `sel` is unconstrained (the identity quasi-isomorphism with zero local complexes inhabits
it, `selmerIdentification_trivial`), so this adds nothing to `Identification`; superseded by the
`Identification2` route (`ClearingComplex/NewLocalModel`). -/
structure SelmerIdentification (b : ℕ) (dK hK cE tK : ℕ) extends Identification b dK hK cE tK where
  /-- the Selmer data over `𝒪[G]` (global cochains, local conditions, full local complexes) -/
  sel : SelData (MonoidAlgebra OO (SignGroup b))
  /-- the comparison of `D` with the Selmer complex -/
  φ : D.toGCx.toCC ⟶ (selCx sel).toCC
  /-- it is a quasi-isomorphism -/
  qis : QuasiIso φ

/-- **RC0's `ClearingModel` from the Selmer-phrased identification and E1** (PROVED). -/
theorem clearingModel_of_selmer {ℓ : ℕ} (Dd : RCData ℓ)
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (I : SelmerIdentification F.b dK hK cE tK) (sd : ScalarData I.B)
        (κ ε η : MonoidAlgebra OO (SignGroup F.b)),
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          ClearingCoordIdentity I.B sd κ ε η 0 e g I.D.RankOnePattern I.D.AcyclicPattern) :
    ClearingModel Dd := by
  obtain ⟨dK, hK, cE, tK, hF⟩ := h
  exact clearingModel_of_E1 Dd ⟨dK, hK, cE, tK, fun Co Ce F hFam => by
    obtain ⟨I, sd, κ, ε, η, hcoord⟩ := hF Co Ce F hFam
    exact ⟨I.toIdentification, sd, κ, ε, η, hcoord⟩⟩

/-! ### Consistency -/

section Consistency

variable {S : Type} [CommRing S]

/-- The zero complex. -/
def zeroGCx (S : Type) [CommRing S] : GCx S where
  X _ := ModuleCat.of S PUnit
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- The zero chain map. -/
def zeroGHom (A B : GCx S) : GHom A B where
  f _ _ _ := 0
  comm _ _ _ _ _ _ _ _ _ := by simp

/-- Selmer data with global complex `D` and zero local data. -/
def trivialSel (D : BlockComplex S) : SelData S where
  G := D.toGCx
  U := zeroGCx S
  L := zeroGCx S
  res := zeroGHom _ _
  ι := zeroGHom _ _

/-- `D^n ≅ C^n = D^n ⊕ 0 ⊕ 0`. -/
def trivialSelEquiv (D : BlockComplex S) (n : ℤ) :
    (D.idx n → S) ≃ₗ[S] selT (trivialSel D) n :=
  letI : Unique (PUnit.{1} × PUnit.{1}) :=
    { default := ⟨PUnit.unit, PUnit.unit⟩, uniq := fun _ => Subsingleton.elim _ _ }
  (LinearEquiv.prodUnique (R := S) (M := D.idx n → S) (M₂ := PUnit × PUnit)).symm

/-- The isomorphism of `D` with the Selmer complex of the trivial Selmer data. -/
def trivialSelIso (D : BlockComplex S) : D.toGCx.toCC ≅ (selCx (trivialSel D)).toCC := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => (trivialSelEquiv D n).toModuleIso) ?_
  intro i j hij
  change i + 1 = j at hij
  subst hij
  ext x
  change ((selCx (trivialSel D)).toCC.d i (i + 1)).hom (trivialSelEquiv D i x) =
    trivialSelEquiv D (i + 1) ((D.toGCx.toCC.d i (i + 1)).hom x)
  refine (GCx.toCC_d_hom _ i (i + 1) rfl _).trans ?_
  refine Eq.trans ?_ (congrArg (trivialSelEquiv D (i + 1)) (GCx.toCC_d_hom D.toGCx i (i + 1) rfl x)).symm
  exact Prod.ext rfl (Prod.ext rfl rfl)

/-- The identity comparison is a quasi-isomorphism (an isomorphism). -/
theorem trivialSel_qis (D : BlockComplex S) : QuasiIso (trivialSelIso D).hom :=
  quasiIso_of_isIso _

/-- **Consistency of the Selmer-phrased identification** (PROVED): the trivial remaining complex,
with Selmer data `G = D`, `U = L = 0` and the identity comparison, satisfies every field. -/
def selmerIdentification_trivial (b : ℕ) : SelmerIdentification b 0 0 0 0 where
  toIdentification := identification_trivial b
  sel := trivialSel (D₀ b)
  φ := (trivialSelIso (D₀ b)).hom
  qis := trivialSel_qis (D₀ b)

theorem selmerIdentification_nonempty (b : ℕ) : Nonempty (SelmerIdentification b 0 0 0 0) :=
  ⟨selmerIdentification_trivial b⟩

end Consistency

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
