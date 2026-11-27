import ZInQKernel.Contrib.OneProof.HeightModelM.SemiAbelianModel
import ZInQKernel.Contrib.OneProof.HeightModelM2.Separated

/-! # Every group model is commutative: GR1's "modèle semi-abélien" is the tree's

GR1 (Gaudron–Rémond, Comment. Math. Helv. 89 (2014), §2.3, p. 351) takes "un modèle
semi-abélien" of `A`: a smooth separated commutative group scheme over `𝒪_K` with generic fibre
`A` and semi-abelian fibres. The tree's `GroupModel` (smooth, separated, quasi-compact, generic
fibre `≅ A_L` as group schemes) and `IsSemiAbelianModel` do not ask for commutativity. The
fidelity reading argued that it is automatic: `𝒜 ×_S 𝒜` is flat over the Dedekind `𝓞_L`, so its
generic fibre is schematically dense, the commutator is the unit there because `A_L` is
commutative (Mathlib's `isCommMonObj_of_isProper_of_geometricallyIntegral`), and `𝒜` is separated.
This file proves it.

* `groupModel_isCommMonObj`: every `GroupModel A L` is a commutative group object.
* `groupModel_commutator_eq_one`: the commutator morphism `𝒜 ×_S 𝒜 → 𝒜`,
  `(x, y) ↦ x y x⁻¹ y⁻¹`, is the constant unit morphism `1 = toUnit ≫ η`
  (`one_eq_toUnit_comp_unit`).
* `isSemiAbelianModel_iff_and_comm`: the predicate with commutativity added is the same
  predicate, so `IsSemiAbelianModel` admits exactly the commutative models GR1 admits.
* `exists_commSemiAbelianModel`: the bridge's `𝒩⁰` is a commutative semi-abelian model. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonObj
open MonoidalCategory CartesianMonoidalCategory CToPrinted
open DictModels.RaynaudOr ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightFix ZInQ.SemistabAssembly
open ZInQ.HeightModelM
open scoped NumberField

set_option linter.style.haveILetI false

namespace ZInQ.HeightModelM2

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- **Every group model is commutative.** A `GroupModel A L` is flat (smooth) and separated over
`𝓞_L`, and its generic fibre is `A_L`, commutative; so the group object is commutative. -/
theorem groupModel_isCommMonObj (𝒜 : GroupModel A L) : IsCommMonObj 𝒜.G := by
  letI : GrpObj (genericFibre L 𝒜.G) := Functor.grpObjObj
  haveI : IsMonHom 𝒜.gen.hom := 𝒜.gen_hom
  have hc : IsCommMonObj (genericFibre L 𝒜.G) := isCommMonObj_of_iso 𝒜.gen
  exact isCommMonObj_of_generic (IsFractionRing.injective (𝓞 L) L) 𝒜.G hc

/-- The unit of the group `𝒜 ×_S 𝒜 ⟶ 𝒜` is the constant morphism `toUnit ≫ η`. -/
theorem one_eq_toUnit_comp_unit (𝒜 : GroupModel A L) :
    (1 : 𝒜.G ⊗ 𝒜.G ⟶ 𝒜.G) = toUnit _ ≫ η[𝒜.G] := rfl

/-- **The commutator morphism is the constant unit morphism**: `x y x⁻¹ y⁻¹ = 1` for the two
projections `x, y : 𝒜 ×_S 𝒜 → 𝒜`. -/
theorem groupModel_commutator_eq_one (𝒜 : GroupModel A L) :
    fst 𝒜.G 𝒜.G * snd 𝒜.G 𝒜.G * (fst 𝒜.G 𝒜.G)⁻¹ * (snd 𝒜.G 𝒜.G)⁻¹ =
      (1 : 𝒜.G ⊗ 𝒜.G ⟶ 𝒜.G) := by
  haveI := groupModel_isCommMonObj 𝒜
  rw [_root_.mul_comm (fst 𝒜.G 𝒜.G), _root_.mul_inv_cancel_right, _root_.mul_inv_cancel]

/-- Points of a group model with values in any `T` commute. -/
theorem groupModel_mul_comm (𝒜 : GroupModel A L) {T : Over (Spec (CommRingCat.of (𝓞 L)))}
    (a b : T ⟶ 𝒜.G) : a * b = b * a := by
  haveI := groupModel_isCommMonObj 𝒜
  exact _root_.mul_comm a b

/-- **The predicate with commutativity added is the same predicate.** -/
theorem isSemiAbelianModel_iff_and_comm (𝒜 : GroupModel A L) :
    IsSemiAbelianModel 𝒜 ↔ IsSemiAbelianModel 𝒜 ∧ IsCommMonObj 𝒜.G :=
  ⟨fun h => ⟨h, groupModel_isCommMonObj 𝒜⟩, fun h => h.1⟩

/-- **`𝒩⁰` is a commutative semi-abelian model**: `exists_semiAbelianModel` with commutativity. -/
theorem exists_commSemiAbelianModel (𝒩 : GroupModel A L) (hO : IsOpen (idCompSet 𝒩.G))
    (hS : IsSemistablePrinted 𝒩) :
    ∃ (𝒢₀ : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒩.G), IsOpenImmersion i.left ∧ IsMonHom i ∧
      Set.range i.left = idCompSet 𝒩.G ∧ IsSemiAbelianModel 𝒢₀ ∧ IsCommMonObj 𝒢₀.G := by
  obtain ⟨𝒢₀, i, h1, h2, h3, h4⟩ := exists_semiAbelianModel 𝒩 hO hS
  exact ⟨𝒢₀, i, h1, h2, h3, h4, groupModel_isCommMonObj 𝒢₀⟩

end ZInQ.HeightModelM2
