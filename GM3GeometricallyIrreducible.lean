/-
Lane5 producer for C3's exact GeomIrreducibleOverAlgClosed.{u} interface.
SOURCE ONLY / UNCOMPILED. Truth pre-check: true under the written LFT and
algebraically-closed-field hypotheses (EGA IV 4.5.8). No smoothness, properness,
reducedness, characteristic or dimension restriction is inserted.

Proof: every closed point is rational. A field-base-change projection is
open and surjective. Images of two nonempty opens meet at a closed point
of the Jacobson base. That rational point has a singleton geometric fibre,
so the two opens upstairs meet. This directly proves irreducibility for
EVERY field test, not just algebraic/finite extensions.

The rational-fibre calculation is reused in shape from Lane5's own frozen
FieldConnectedSection8ced; the GC theorem itself is not reproved or used as
an irreducibility shortcut. All maps are actual pullback maps.
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3Plan

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace H5OriginalDVR.Lane5.GM3Geometry

section RationalFibre
variable {k L : Type u} [Field k] [Field L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ f = 𝟙 _)

/-- Actual lift of a rational point along the given field test. -/
def liftPoint : Spec (CommRingCat.of L) ⟶ pullback f g :=
  pullback.lift (g ≫ e) (𝟙 _) (by simp only [Category.assoc, he, Category.comp_id,
    Category.id_comp])

/-- The rational-point fibre is literally isomorphic to Spec L. -/
theorem rationalFibre_subsingleton : Subsingleton (pullback e (pullback.fst f g)) := by
  let i1 : pullback e (pullback.fst f g) ≅ pullback (e ≫ f) g :=
    pullbackRightPullbackFstIso f g e
  let i2 : pullback (e ≫ f) g ≅ pullback (𝟙 _) g := pullback.congrHom he rfl
  let j := i1.hom ≫ i2.hom ≫ pullback.snd (𝟙 _) g
  letI : IsIso j := by dsimp only [j]; infer_instance
  exact (Scheme.Hom.homeomorph j).subsingleton

/-- All points above that same rational point equal its actual field lift. -/
theorem point_eq_of_projection (z : pullback f g)
    (hz : pullback.fst f g z = e (IsLocalRing.closedPoint k)) :
    z = liftPoint f g e he (IsLocalRing.closedPoint L) := by
  have hrange : Set.range (pullback.snd e (pullback.fst f g)) =
      pullback.fst f g ⁻¹' Set.range e := Scheme.Pullback.range_snd _ _
  have hz' : z ∈ Set.range (pullback.snd e (pullback.fst f g)) := by
    rw [hrange]
    exact ⟨_, hz.symm⟩
  have hw : liftPoint f g e he (IsLocalRing.closedPoint L) ∈
      Set.range (pullback.snd e (pullback.fst f g)) := by
    rw [hrange, Set.mem_preimage, ← Scheme.Hom.comp_apply, liftPoint,
      pullback.lift_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  obtain ⟨a, rfl⟩ := hz'
  obtain ⟨b, hb⟩ := hw
  letI := rationalFibre_subsingleton f g e he
  rw [← hb, Subsingleton.elim a b]
end RationalFibre

/-- Irreducibility after any field test over the algebraically closed base. -/
theorem irreducibleSpace_pullback_of_isAlgClosed
    {k L : Type u} [Field k] [IsAlgClosed k] [Field L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [IrreducibleSpace X]
    (g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) :
    IrreducibleSpace (pullback f g) := by
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  letI : UniversallyOpen g := inferInstance
  letI : Surjective g := ⟨Function.surjective_to_subsingleton _⟩
  let p : pullback f g ⟶ X := pullback.fst f g
  letI : Surjective p := inferInstance
  have hnonempty : Nonempty (pullback f g) := by
    obtain ⟨z, _⟩ := p.surjective (Classical.choice (inferInstance : Nonempty X))
    exact ⟨z⟩
  letI : Nonempty (pullback f g) := hnonempty
  letI : PreirreducibleSpace (pullback f g) :=
    PreirreducibleSpace.of_forall_nonempty_inter (by
      intro U V hU hV hUne hVne
      have hPU : IsOpen (p '' U) := p.isOpenMap U hU
      have hPV : IsOpen (p '' V) := p.isOpenMap V hV
      have hmeet : ((p '' U) ∩ (p '' V)).Nonempty :=
        nonempty_preirreducible_inter hPU hPV (hUne.image p) (hVne.image p)
      obtain ⟨x, hx, hxClosed⟩ := nonempty_inter_closedPoints
        (Z := (p '' U) ∩ (p '' V)) hmeet (hPU.inter hPV).isLocallyClosed
      obtain ⟨a, haU, ha⟩ := hx.1
      obtain ⟨b, hbV, hb⟩ := hx.2
      let e := pointOfClosedPoint f x hxClosed
      have he : e ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hxClosed
      have ha' : a = liftPoint f g e he (IsLocalRing.closedPoint L) := by
        apply point_eq_of_projection f g e he
        simpa only [p, e, pointOfClosedPoint_apply] using ha
      have hb' : b = liftPoint f g e he (IsLocalRing.closedPoint L) := by
        apply point_eq_of_projection f g e he
        simpa only [p, e, pointOfClosedPoint_apply] using hb
      have hab : a = b := ha'.trans hb'.symm
      exact ⟨a, haU, hab.symm ▸ hbV⟩)
  exact ⟨hnonempty⟩

/-- EXACT C3 consumer; no extra caller/Fact or field-test restriction. -/
theorem geomIrreducibleOverAlgClosed :
    ZInQ.Contrib.CloudR2NOS.Step1.GeomIrreducibleOverAlgClosed.{u} := by
  intro k _ _ X f _ _
  constructor
  intro L instL g Z a b h
  letI : IrreducibleSpace (pullback f g) := irreducibleSpace_pullback_of_isAlgClosed f g
  exact (Scheme.Hom.homeomorph h.isoPullback.hom).irreducibleSpace_iff.mpr inferInstance

end H5OriginalDVR.Lane5.GM3Geometry
