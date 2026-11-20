import ZInQKernel.Contrib.OneProof.SZThm33.FiniteFixedTate
import ZInQKernel.Contrib.OneProof.SZThm33.GeomSpecialTate
import ZInQKernel.Contrib.OneProof.IdentityComponentLFT
import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect

/-!
# Tate towers of a finite-type group lie in its identity component
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology TopologicalSpace IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.SemiAbDescend

namespace SZRaynaud

/-- A group scheme homomorphism induces a homomorphism on points of
any test scheme. -/
def mapGroupPoint {S : Scheme.{0}} {P G H : Over S} [GrpObj G] [GrpObj H]
    (i : G ⟶ H) [IsMonHom i] : (P ⟶ G) →* (P ⟶ H) where
  toFun x := x ≫ i
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

variable {k : Type} [Field k] [IsAlgClosed k]

/-- The image of a connected open subgroup is the identity component. -/
theorem range_openConnectedSubgroup_eq_connectedComponent
    {G U : Over (Spec (.of k))} [GrpObj G] [GrpObj U] [LocallyOfFiniteType G.hom]
    [ConnectedSpace U.left] (i : U ⟶ G) [IsOpenImmersion i.left] [IsMonHom i] :
    Set.range i.left = connectedComponent ((1 : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G).left (closedPoint k)) := by
  have he : (1 : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G).left (closedPoint k) ∈ Set.range i.left := by
    refine ⟨(1 : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ U).left (closedPoint k), ?_⟩
    exact congrArg (fun a : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G => a.left (closedPoint k)) (map_one (mapGroupPoint i))
  exact le_antisymm
    ((isPreconnected_range i.left.continuous).subset_connectedComponent he)
    (IsClopen.connectedComponent_subset
      ⟨isClosed_range_openSubgroup i, i.left.isOpenEmbedding.isOpen_range⟩ he)

/-- The quotient of rational points by the connected open subgroup has
finitely many elements, since distinct cosets belong to distinct components. -/
theorem finite_componentQuotient
    {G U : Over (Spec (.of k))} [GrpObj G] [GrpObj U] [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] [ConnectedSpace U.left] (i : U ⟶ G) [IsOpenImmersion i.left] [IsMonHom i] :
    Finite (((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G) ⧸ (mapGroupPoint i (P := (𝟙_ (Over (Spec (CommRingCat.of k)))))).range) := by
  let H := (mapGroupPoint i (P := (𝟙_ (Over (Spec (CommRingCat.of k)))))).range
  let eval (x : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G) := x.left (closedPoint k)
  have htr (s x : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G) : (transl s).left (eval x) = eval (s * x) := by
    exact congrArg (fun a : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G => a.left (closedPoint k)) (point_comp_transl s x)
  have hrel (x y : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G) :
      QuotientGroup.leftRel H x y ↔ (eval y : _root_.ConnectedComponents G.left) = eval x := by
    rw [QuotientGroup.leftRel_apply, _root_.ConnectedComponents.coe_eq_coe']
    constructor
    · rintro ⟨z, hz⟩
      have hz' : eval (x⁻¹ * y) ∈ Set.range i.left := by
        rw [← hz]
        exact ⟨z.left (closedPoint k), rfl⟩
      rw [range_openConnectedSubgroup_eq_connectedComponent i] at hz'
      have h := (transl x).left.continuous.mapsTo_connectedComponent (eval 1) hz'
      rw [htr, htr, _root_.mul_one, _root_.mul_inv_cancel_left] at h
      exact h
    · intro hy
      have h := (transl x⁻¹).left.continuous.mapsTo_connectedComponent (eval x) hy
      rw [htr, htr, inv_mul_cancel, ← range_openConnectedSubgroup_eq_connectedComponent i] at h
      exact factor_point i _ (closedPoint k) h
  let f : ((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G) ⧸ H → _root_.ConnectedComponents G.left :=
    Quotient.lift (fun x => (eval x : _root_.ConnectedComponents G.left))
      (fun x y h => ((hrel x y).mp h).symm)
  have hf : Function.Injective f := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b =>
      intro h
      exact Quotient.sound ((hrel a b).mpr h.symm)
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : DiscreteTopology (_root_.ConnectedComponents G.left) := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro c
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [← _root_.ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
      connectedComponents_preimage_singleton]
    exact IdCompLFT.isOpen_cc_of_isLocallyNoetherian G.left x
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  exact Finite.of_injective f hf

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Every residue Tate tower belongs to the identity component. This
allows components of order divisible by ℓ in the finite component group. -/
theorem bijective_tate_map_connectedOpenSubgroup
    {G U : Over (Spec (.of k))} [GrpObj G] [GrpObj U] [IsCommMonObj G] [IsCommMonObj U]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [ConnectedSpace U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left] [IsMonHom i] :
    Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) (mapGroupPoint i (P := (𝟙_ (Over (Spec (CommRingCat.of k)))))).toAdditive) := by
  let f := mapGroupPoint i (P := (𝟙_ (Over (Spec (CommRingCat.of k)))))
  let H := f.range
  let q := QuotientGroup.mk' H
  have hf : Function.Injective f := by
    intro x y h
    apply Over.OverMorphism.ext
    exact (cancel_mono i.left).mp (congrArg Over.Hom.left h)
  have := finite_componentQuotient i
  constructor
  · intro t u h
    apply Subtype.ext
    funext n
    apply Additive.toMul.injective
    apply hf
    exact congrArg (fun t : PkgI3.Tate.T ℓ (Additive ((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G)) => Additive.toMul (t.1 n)) h
  · intro t
    have hq := tate_eq_zero_of_finite (PkgI3.Tate.map (ℓ := ℓ) q.toAdditive t)
    let x (n : ℕ) := Additive.toMul (t.1 n)
    have hx (n : ℕ) : x n ∈ H := by
      apply (QuotientGroup.eq_one_iff (N := H) (x n)).mp
      exact congrArg (fun t : PkgI3.Tate.T ℓ (Additive (((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G) ⧸ H)) =>
        Additive.toMul (t.1 n)) hq
    choose y hy using hx
    have hy₀ : y 0 = 1 := by
      apply hf
      rw [show f (y 0) = x 0 from hy 0, map_one]
      exact t.2.1
    have hyc (n : ℕ) : y (n + 1) ^ ℓ = y n := by
      apply hf
      rw [map_pow, show f (y (n + 1)) = x (n + 1) from hy (n + 1),
        show f (y n) = x n from hy n]
      exact t.2.2 n
    refine ⟨⟨fun n => Additive.ofMul (y n), hy₀, hyc⟩, Subtype.ext ?_⟩
    funext n
    exact congrArg Additive.ofMul (hy n)

#print axioms finite_componentQuotient
#print axioms bijective_tate_map_connectedOpenSubgroup

end SZRaynaud
