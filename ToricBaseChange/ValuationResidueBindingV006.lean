import ToricBaseChange.G3AssemblyV001
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Residue fields of an extension of valuation rings and the common geometric point

For valuation subrings `O ⊆ K`, `O' ⊆ L` of a field extension `L/K` with `O' ∩ K = O`:

* `O → O'` is a local homomorphism (`isLocalHom_iota`), so it induces `κ(O) → κ(O')` (`resMap`);
* with `Ω = κ(O')^alg`, a `κ(O)`-embedding `jbar : κ(O)^alg → Ω` exists (`jbar`, the algebraic closure
  embeds into any algebraically closed extension);
* the square `Spec Ω → Spec O' → Spec O` = `Spec Ω → Spec κ(O)^alg → Spec κ(O) → Spec O` commutes
  (`geom_square`).

These are the inputs `(h, s, σ', jb, hsq)` of `toricRank_le_of_comparison` for the actual residue
fields: `h = Spec(O → O')`, `s = Spec(O → κ(O))`, `σ' = Spec(O' → κ(O')^alg)`, `jb = jbar`,
`hsq = geom_square`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Limits
open scoped CategoryTheory.Obj

namespace ToricBaseChange

section Residue

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem isLocalHom_iota (O : ValuationSubring K) (O' : ValuationSubring L)
    (hO : O'.comap (algebraMap K L) = O) : IsLocalHom (Comparison.iota O O' hO) := by
  constructor
  intro x hx
  obtain ⟨v, hv⟩ := hx
  have hval : ((Comparison.iota O O' hO x : O') : L) = algebraMap K L (x : K) := rfl
  have h1 : (algebraMap K L (x : K)) * ((↑(v⁻¹) : O') : L) = 1 := by
    rw [← hval, ← hv]
    exact congrArg Subtype.val (Units.mul_inv v)
  have hx0 : (x : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hinv : ((x : K))⁻¹ ∈ O := by
    have hmem : ((x : K))⁻¹ ∈ O'.comap (algebraMap K L) := by
      rw [ValuationSubring.mem_comap, map_inv₀]
      have : (algebraMap K L (x : K))⁻¹ = ((↑(v⁻¹) : O') : L) :=
        (eq_inv_of_mul_eq_one_right h1).symm
      rw [this]
      exact (↑(v⁻¹) : O').2
    rwa [hO] at hmem
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (by simp [hx0])⟩

/-- `κ(O) → κ(O')`. -/
def resMap (O : ValuationSubring K) (O' : ValuationSubring L) (hO : O'.comap (algebraMap K L) = O) :
    IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O' :=
  haveI := isLocalHom_iota O O' hO
  IsLocalRing.ResidueField.map (Comparison.iota O O' hO)

/-- `κ(O) → κ(O')^alg`, making `κ(O')^alg` a `κ(O)`-algebra. -/
@[reducible] def algResBar (O : ValuationSubring K) (O' : ValuationSubring L)
    (hO : O'.comap (algebraMap K L) = O) :
    Algebra (IsLocalRing.ResidueField O) (AlgebraicClosure (IsLocalRing.ResidueField O')) :=
  ((algebraMap (IsLocalRing.ResidueField O') (AlgebraicClosure (IsLocalRing.ResidueField O'))).comp
    (resMap O O' hO)).toAlgebra

/-- **A `κ(O)`-embedding `κ(O)^alg → κ(O')^alg`.** -/
def jbar (O : ValuationSubring K) (O' : ValuationSubring L) (hO : O'.comap (algebraMap K L) = O) :
    AlgebraicClosure (IsLocalRing.ResidueField O) →+* AlgebraicClosure (IsLocalRing.ResidueField O') :=
  letI := algResBar O O' hO
  (IsAlgClosed.lift : AlgebraicClosure (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O]
    AlgebraicClosure (IsLocalRing.ResidueField O')).toRingHom

theorem jbar_algebraMap (O : ValuationSubring K) (O' : ValuationSubring L)
    (hO : O'.comap (algebraMap K L) = O) (a : IsLocalRing.ResidueField O) :
    jbar O O' hO (algebraMap _ (AlgebraicClosure (IsLocalRing.ResidueField O)) a) =
      algebraMap (IsLocalRing.ResidueField O') (AlgebraicClosure (IsLocalRing.ResidueField O'))
        (resMap O O' hO a) := by
  letI := algResBar O O' hO
  exact (IsAlgClosed.lift : AlgebraicClosure (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O]
    AlgebraicClosure (IsLocalRing.ResidueField O')).commutes a

/-- **The geometric square**: `O → O' → κ(O')^alg` equals `O → κ(O) → κ(O)^alg → κ(O')^alg`. -/
theorem geom_square (O : ValuationSubring K) (O' : ValuationSubring L)
    (hO : O'.comap (algebraMap K L) = O) :
    Spec.map (CommRingCat.ofHom (algebraMap O' (AlgebraicClosure (IsLocalRing.ResidueField O')))) ≫
        Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO)) =
      sφ (φι (jbar O O' hO)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap O (IsLocalRing.ResidueField O))) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply, φι]
  rw [jbar_algebraMap, IsScalarTower.algebraMap_apply O' (IsLocalRing.ResidueField O')
    (AlgebraicClosure (IsLocalRing.ResidueField O'))]
  rfl

end Residue

/-! ## The assembled inequality over the actual residue fields -/

section Actual

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- The generic fibre target of the second model is the base change `A_L` (by definition). -/
example (A : PkgI3.AbVar K) :
    (A.baseChange L).X = (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.X := rfl

end Actual

end ToricBaseChange
