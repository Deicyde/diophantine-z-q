import PGBase
/-! # period-glue: `PiTwistC` from R2fp and two smaller named Props

Task period-glue, 2026-11-13. `PiTwistC Y Φ π` (period-map, `PGBase`, unchanged) is proved from
* `R1fpProps Y Φ` (only: `Y` proper and smooth over `ℚ`) and `R2fpProps Y Φ π` (the leaves R1, R2;
  both already hypotheses at the own triple),
* `TwistOrbitFinite Y Φ` (**GLUE**, moduli: the twist relation on `ℚ̄`- and `ℂ`-points is the
  orbit relation of a finite set of automorphisms of `Y`), and
* `FibreTransferC Y π` (**GLUE**, algebraic geometry: a fibre statement for `π` that holds on
  `ℚ̄`-points holds on `ℂ`-points),
by `piTwistC_of`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH

/-- **GLUE (moduli: the `Aut(𝒪)`-twist relation is a finite orbit relation).** There is a finite
set `G` of automorphisms of `Y` over `ℚ` such that, on `ℚ̄`-points and on `ℂ`-points, two points
have twist-equivalent QM pairs iff one is the image of the other under some `g ∈ G`.

Why true for the genuine `Y₃` (model argument): `G` = the automorphisms inducing `twist α`
(`α ∈ Aut 𝒪`) and `rightMul u` (`u ∈ 𝒪^×`) on points (`R1heckeProps`, a clause of R1), composed.
It is finite: `rightMul u` depends only on `u mod 3𝒪` (`Level3.rightMul_eq_self`), inner twists
are `rightMul`s up to isomorphism, and `Aut(𝒪)/Inn` is finite (mobius-glue `AutOInnerFinite`,
from the kernel's Skolem–Noether); an automorphism of the reduced `Y` is determined by its action
on field points. (⇐) is `Φ` of `y ≫ g`. (⇒) a QM isomorphism `Q.q.twist α ≅ Q'.q` transports
`Q'`'s level structure to one on `(A, ι∘α)`; over an algebraically closed field two level
structures on the same QM pair differ by right multiplication by a unit of `𝒪/3𝒪` (both are
`𝒪`-linear isomorphisms `𝒪/3𝒪 ≅ A[3]`, `|A[3]| = 81`), and `𝒪^× → (𝒪/3𝒪)^×` is onto (strong
approximation for `𝒪¹`, plus `1 + i` of reduced norm `−1`; a finite check on the 72 units of
`𝒪/3𝒪`); then `Φ` injective gives `y' = y ≫ g`. Size: medium. -/
def TwistOrbitFinite (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ G : Set (Y ≅ Y), G.Finite ∧
    (∀ (y y' : fieldPt Qbar ⟶ Y) (Q Q' : QML3 Qbar), Φ Qbar y = M3.mk Q → Φ Qbar y' = M3.mk Q' →
      ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
        ∃ g ∈ G, y' = y ≫ g.hom)) ∧
    (∀ (y y' : fieldPt ℂ ⟶ Y) (Q Q' : QML3 ℂ), Φ ℂ y = M3.mk Q → Φ ℂ y' = M3.mk Q' →
      ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
        ∃ g ∈ G, y' = y ≫ g.hom))

/-- **GLUE (algebraic geometry: transfer of a fibre statement from `ℚ̄`- to `ℂ`-points).** For a
proper smooth curve `Y` over `ℚ` (the hypotheses make the statement true for every `Y`; without
them it fails, e.g. for `Y = Spec ℂ`, which has no `ℚ̄`-points) and a finite set `G` of
automorphisms of `Y` over `ℚ`, if the fibres of `π` on `ℚ̄`-points are exactly
the `G`-orbits (in the sense below), the same holds on `ℂ`-points.

Why true (model argument), for `Y` of finite type and separated over `ℚ` (R1fp: proper):
`E = {(p, q) ∈ Y ×_ℚ Y : π(p) = π(q)}` (the equalizer of `π∘pr₁`, `π∘pr₂`, closed since `P¹` is
separated) and `Γ = ⋃_{g ∈ G} graph(g)` (finite union of closed graphs, `Y` separated) are closed
subsets of the finite-type `ℚ`-scheme `Y ×_ℚ Y`, hence Jacobson: each is the closure of its closed
points. Closed points are the images of `ℚ̄`-points (Nullstellensatz), and on those `E` and `Γ`
agree by hypothesis, so `E = Γ`. A `ℂ`-point `(y, y')` lies in `E` iff `π(y) = π(y')`, and in
`Γ` iff `y' = y ≫ g` for some `g ∈ G` (it factors through the reduced closed subscheme
`graph(g) ≅ Y`, `Y` smooth hence reduced). Mathlib has Jacobson schemes
(`AlgebraicGeometry.JacobsonSpace`) and equalizers/graphs of morphisms; the charts of `ToP1` must
be turned into a morphism to `P¹`. Size: medium. -/
def FibreTransferC (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ G : Set (Y ≅ Y), G.Finite →
    (∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)) →
    ∀ y y' : fieldPt ℂ ⟶ Y,
      (π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)

/-- **`PiTwistC` from R2fp, `TwistOrbitFinite` and `FibreTransferC` (proved).** -/
theorem piTwistC_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (hT : TwistOrbitFinite Y Φ)
    (hF : FibreTransferC Y π) :
    PiTwistC Y Φ π := by
  obtain ⟨G, hG, hQbar, hC⟩ := hT
  have hfibQ : ∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom) := by
    intro y y'
    have hP : Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) := (Quotient.out_eq _).symm
    have hQ : Φ Qbar y' = M3.mk (Quotient.out (Φ Qbar y')) := (Quotient.out_eq _).symm
    exact ((h2 y y' _ _ hP hQ).1).trans (hQbar y y' _ _ hP hQ)
  intro y y' Q Q' hQ hQ'
  exact (hF h1.1 h1.2.1 G hG hfibQ y y').trans (hC y y' Q Q' hQ hQ').symm

/-! ## `FibreTransferC` split into its two directions -/

/-- **GLUE (AG, textbook density): two maps to `P¹` agreeing on `ℚ̄`-points agree on `ℂ`-points.**
For `Y` proper and smooth over `ℚ` and `σ, ρ : Y → P¹` (by charts) with the same values at every
`ℚ̄`-point, the values agree at every `ℂ`-point.

Why true: the locus where two morphisms to the separated `P¹` agree, residue maps included, is a
closed subscheme (the equalizer). It contains every closed point, since closed points are images of
`ℚ̄`-points. `Y` is Jacobson (finite type over a field) and reduced (smooth), so the equalizer is
`Y`. Size: medium (the equalizer of two `ToP1` charts; Mathlib's `JacobsonSpace`). -/
def ToP1AgreeC (Y : Over (Spec (CommRingCat.of ℚ))) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ σ ρ : ToP1 Y.left,
    (∀ y : fieldPt Qbar ⟶ Y, σ.val (K := Qbar) y.left = ρ.val (K := Qbar) y.left) →
    ∀ y : fieldPt ℂ ⟶ Y, σ.val (K := ℂ) y.left = ρ.val (K := ℂ) y.left

/-- **GLUE (AG; the hard half of `FibreTransferC`).** If the fibres of `π` on `ℚ̄`-points are the
orbits of a finite set `G` of automorphisms, then two `ℂ`-points with the same `π`-value are in one
`G`-orbit.

Why true (model argument): the hypothesis forces `π` to be non-constant on every component (a
component has infinitely many `ℚ̄`-points, while `G`-orbits are finite). A `ℂ`-point over a closed
point of `Y` comes from a `ℚ̄`-point through one embedding `ℚ̄ → ℂ`, and so does every point in its
`π`-fibre (the value is algebraic, and `π` is non-constant on components). That case reduces to the
hypothesis. For points over generic points of components, the closed subsets `{π(p) = π(q)}` and
`⋃ graph(g)` of `Y ×_ℚ Y` agree on closed points, hence agree (Jacobson). Size: medium-large. -/
def FibreGenericC (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ G : Set (Y ≅ Y), G.Finite →
    (∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)) →
    ∀ y y' : fieldPt ℂ ⟶ Y,
      π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left → ∃ g ∈ G, y' = y ≫ g.hom

/-- **`FibreTransferC` from `ToP1AgreeC` and `FibreGenericC` (proved).** The direction (⇐) is
`ToP1AgreeC` applied to `π ∘ g` and `π`. -/
theorem fibreTransferC_of (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left)
    (hA : ToP1AgreeC Y) (hG : FibreGenericC Y π) : FibreTransferC Y π := by
  intro hP hS G hGf hQ y y'
  refine ⟨hG hP hS G hGf hQ y y', ?_⟩
  rintro ⟨g, hg, rfl⟩
  have e : ∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
      (π.comp g.hom.left).val (K := K) z.left = π.val (K := K) (z ≫ g.hom).left :=
    fun K _ _ z => ToP1.val_comp_right π g.hom.left (K := K) z.left
  have hagree := hA hP hS (π.comp g.hom.left) π (fun y0 => by
    rw [e]
    exact ((hQ y0 (y0 ≫ g.hom)).mpr ⟨g, hg, rfl⟩).symm) y
  rw [e] at hagree
  exact hagree.symm

/-! ### `ToP1AgreeC` (proved: density of closed points) -/

/-- A closed point of `Y` (locally of finite type over `ℚ`) is the point of a `ℚ̄`-point. -/
theorem exists_qbarPt (Y : Over (Spec (CommRingCat.of ℚ))) [LocallyOfFiniteType Y.hom]
    (x : Y.left) (hx : IsClosed ({x} : Set Y.left)) :
    ∃ emb : Y.left.residueField x ⟶ CommRingCat.of Qbar, ∃ y0 : fieldPt Qbar ⟶ Y,
      y0.left = (Scheme.SpecToEquivOfField Qbar Y.left).symm ⟨x, emb⟩ := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  haveI : LocallyOfFiniteType (Y.left.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective (Y.left.fromSpecResidueField x ≫ Y.hom)
  have hφ' : Spec.map φ = Y.left.fromSpecResidueField x ≫ Y.hom := hφ
  have hft : RingHom.FiniteType φ.hom := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ']; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra ℚ (Y.left.residueField x) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℚ (Y.left.residueField x) := hft
  haveI : Module.Finite ℚ (Y.left.residueField x) := finite_of_finite_type_of_isJacobsonRing ℚ _
  haveI : Algebra.IsAlgebraic ℚ (Y.left.residueField x) := Algebra.IsAlgebraic.of_finite ℚ _
  let emb : Y.left.residueField x →ₐ[ℚ] Qbar := IsAlgClosed.lift
  refine ⟨CommRingCat.ofHom emb.toRingHom,
    Over.homMk ((Scheme.SpecToEquivOfField Qbar Y.left).symm ⟨x, CommRingCat.ofHom emb.toRingHom⟩) ?_,
    rfl⟩
  show _ ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
  apply Spec.homEquiv.injective
  ext1
  exact Subsingleton.elim _ _

theorem eval_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V)
    (f : Γ(X, U)) :
    X.evaluation V x hx (X.presheaf.map (homOfLE h).op f) = X.evaluation U x (h hx) f := by
  rw [← Scheme.germ_residue, ← Scheme.germ_residue, CommRingCat.comp_apply,
    CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

/-- **`ToP1AgreeC` (proved).** -/
theorem toP1AgreeC_proof (Y : Over (Spec (CommRingCat.of ℚ))) : ToP1AgreeC Y := by
  intro hP hS σ ρ hQ y
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  -- closed points
  have hcl : ∀ x : Y.left, IsClosed ({x} : Set Y.left) → (x ∈ σ.U ↔ x ∈ ρ.U) ∧
      ∀ (h1 : x ∈ σ.U) (h2 : x ∈ ρ.U),
        Y.left.evaluation σ.U x h1 σ.f = Y.left.evaluation ρ.U x h2 ρ.f := by
    intro x hx
    obtain ⟨emb, y0, hy0⟩ := exists_qbarPt Y x hx
    have e := hQ y0
    unfold ToP1.val at e
    rw [hy0, Equiv.apply_symm_apply] at e
    refine ⟨⟨fun h1 => ?_, fun h2 => ?_⟩, fun h1 h2 => ?_⟩
    · by_contra h2
      rw [dif_pos h1, dif_neg h2] at e
      exact OnePoint.coe_ne_infty _ e
    · by_contra h1
      rw [dif_neg h1, dif_pos h2] at e
      exact OnePoint.coe_ne_infty _ e.symm
    · rw [dif_pos h1, dif_pos h2] at e
      exact emb.hom.injective (OnePoint.coe_injective e)
  -- the two chart domains coincide
  have hU : ∀ p : Y.left, p ∈ σ.U ↔ p ∈ ρ.U := by
    have side : ∀ (σ ρ : ToP1 Y.left),
        (∀ x : Y.left, IsClosed ({x} : Set Y.left) → (x ∈ σ.U → x ∈ ρ.U)) →
        ∀ p : Y.left, p ∈ σ.U → p ∈ ρ.U := by
      intro σ ρ hc p hp
      by_contra hq
      obtain ⟨x, ⟨hxσ, hxρ⟩, hxc⟩ := nonempty_inter_closedPoints (Z := (σ.U : Set Y.left) ∩ (ρ.U : Set Y.left)ᶜ)
        ⟨p, hp, hq⟩ (σ.U.isOpen.isLocallyClosed.inter ρ.U.isOpen.isClosed_compl.isLocallyClosed)
      exact hxρ (hc x hxc hxσ)
    intro p
    exact ⟨side σ ρ (fun x hx => (hcl x hx).1.mp) p, side ρ σ (fun x hx => (hcl x hx).1.mpr) p⟩
  -- the difference of the two chart functions vanishes in every residue field of `U ∩ V`
  set W := σ.U ⊓ ρ.U with hW
  let s : Γ(Y.left, W) := Y.left.presheaf.map (homOfLE inf_le_left).op σ.f -
    Y.left.presheaf.map (homOfLE inf_le_right).op ρ.f
  have hsx : ∀ (x : Y.left) (hx : x ∈ W), Y.left.evaluation W x hx s =
      Y.left.evaluation σ.U x hx.1 σ.f - Y.left.evaluation ρ.U x hx.2 ρ.f := by
    intro x hx
    simp only [s, map_sub, eval_res]
  have hs : Y.left.basicOpen s = ⊥ := by
    by_contra hne
    have hne' : ((Y.left.basicOpen s : Y.left.Opens) : Set Y.left).Nonempty := by
      by_contra h0
      apply hne
      ext1
      simpa [Set.not_nonempty_iff_eq_empty] using h0
    obtain ⟨x, hxb, hxc⟩ := nonempty_inter_closedPoints hne'
      (Y.left.basicOpen s).isOpen.isLocallyClosed
    have hxW : x ∈ W := Y.left.basicOpen_le s hxb
    have h0 := (Y.left.evaluation_ne_zero_iff_mem_basicOpen x hxW s).mpr hxb
    rw [hsx x hxW, (hcl x hxc).2 hxW.1 hxW.2, sub_self] at h0
    exact h0 rfl
  have hev : ∀ (p : Y.left) (h1 : p ∈ σ.U) (h2 : p ∈ ρ.U),
      Y.left.evaluation σ.U p h1 σ.f = Y.left.evaluation ρ.U p h2 ρ.f := by
    intro p h1 h2
    have := (Y.left.basicOpen_eq_bot_iff_forall_evaluation_eq_zero s).mp hs ⟨p, h1, h2⟩
    rw [hsx p ⟨h1, h2⟩] at this
    exact sub_eq_zero.mp this
  -- conclusion at the `ℂ`-point
  unfold ToP1.val
  by_cases h1 : (Scheme.SpecToEquivOfField ℂ Y.left y.left).1 ∈ σ.U
  · have h2 := (hU _).mp h1
    rw [dif_pos h1, dif_pos h2, hev _ h1 h2]
  · have h2 : (Scheme.SpecToEquivOfField ℂ Y.left y.left).1 ∉ ρ.U := fun h => h1 ((hU _).mpr h)
    rw [dif_neg h1, dif_neg h2]

/-- **`FibreTransferC` from its hard half `FibreGenericC` alone (proved).** -/
theorem fibreTransferC_of' (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left)
    (hG : FibreGenericC Y π) : FibreTransferC Y π :=
  fibreTransferC_of Y π (toP1AgreeC_proof Y) hG

/-! ### `FibreGenericC` (proved: Jacobson on `Y ×_ℚ Y`) -/

/-- Two maps to `P¹` agree at a point: same chart, same value. -/
def Agree {X : Scheme.{0}} (σ ρ : ToP1 X) (p : X) : Prop :=
  (p ∈ σ.U ↔ p ∈ ρ.U) ∧ ∀ (h1 : p ∈ σ.U) (h2 : p ∈ ρ.U),
    X.evaluation σ.U p h1 σ.f = X.evaluation ρ.U p h2 ρ.f

theorem agree_comm {X : Scheme.{0}} (σ ρ : ToP1 X) (p : X) : Agree σ ρ p ↔ Agree ρ σ p :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, fun a b => (h2 b a).symm⟩,
   fun ⟨h1, h2⟩ => ⟨h1.symm, fun a b => (h2 b a).symm⟩⟩

theorem val_eq_iff_agree {X : Scheme.{0}} (σ ρ : ToP1 X) {K : Type} [Field K]
    (a : Spec (CommRingCat.of K) ⟶ X) :
    σ.val a = ρ.val a ↔ Agree σ ρ (Scheme.SpecToEquivOfField K X a).1 := by
  unfold ToP1.val
  constructor
  · intro h
    refine ⟨⟨fun h1 => ?_, fun h2 => ?_⟩, fun h1 h2 => ?_⟩
    · by_contra h2
      rw [dif_pos h1, dif_neg h2] at h
      exact OnePoint.coe_ne_infty _ h
    · by_contra h1
      rw [dif_neg h1, dif_pos h2] at h
      exact OnePoint.coe_ne_infty _ h.symm
    · rw [dif_pos h1, dif_pos h2] at h
      exact (Scheme.SpecToEquivOfField K X a).2.hom.injective (OnePoint.coe_injective h)
  · rintro ⟨hU, hev⟩
    by_cases h1 : (Scheme.SpecToEquivOfField K X a).1 ∈ σ.U
    · rw [dif_pos h1, dif_pos (hU.mp h1), hev h1 (hU.mp h1)]
    · rw [dif_neg h1, dif_neg (fun h => h1 (hU.mpr h))]

theorem eval_mul_inv_P1 {X : Scheme.{0}} (ρ : ToP1 X) (q : X) (hq : q ∈ ρ.U ⊓ ρ.V) :
    X.evaluation ρ.U q hq.1 ρ.f * X.evaluation ρ.V q hq.2 ρ.g = 1 := by
  have h := congrArg (X.evaluation (ρ.U ⊓ ρ.V) q hq) ρ.inv
  rw [map_mul, map_one, eval_res, eval_res] at h
  exact h

/-- Near a point in one chart domain but not the other, the two maps disagree. -/
theorem disagree_nhds {X : Scheme.{0}} (σ ρ : ToP1 X) (p : X) (h1 : p ∈ σ.U) (h2 : p ∉ ρ.U) :
    ∀ᶠ q in nhds p, ¬ Agree σ ρ q := by
  have hpV : p ∈ ρ.V := by
    have : p ∈ ρ.U ⊔ ρ.V := by rw [ρ.cover]; trivial
    rcases this with h | h
    · exact absurd h h2
    · exact h
  set W := σ.U ⊓ ρ.V with hW
  let hfun : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op σ.f *
    X.presheaf.map (homOfLE inf_le_right).op ρ.g - 1
  have hhx : ∀ x (hx : x ∈ W), X.evaluation W x hx hfun =
      X.evaluation σ.U x hx.1 σ.f * X.evaluation ρ.V x hx.2 ρ.g - 1 := by
    intro x hx
    simp only [hfun, map_sub, map_mul, map_one, eval_res]
  have hg0 : X.evaluation ρ.V p hpV ρ.g = 0 := by
    rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, ρ.basicOpen_g]
    exact fun h => h2 h.1
  have hpb : p ∈ X.basicOpen hfun := by
    rw [← X.evaluation_ne_zero_iff_mem_basicOpen p (show p ∈ W from ⟨h1, hpV⟩), hhx, hg0, mul_zero,
      zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  filter_upwards [(X.basicOpen hfun).isOpen.mem_nhds hpb] with q hq hag
  have hqW : q ∈ W := X.basicOpen_le hfun hq
  have hqU : q ∈ ρ.U := hag.1.mp hqW.1
  have hev := hag.2 hqW.1 hqU
  have hinv := eval_mul_inv_P1 ρ q ⟨hqU, hqW.2⟩
  have := (X.evaluation_ne_zero_iff_mem_basicOpen q hqW hfun).mpr hq
  rw [hhx, hev, hinv, sub_self] at this
  exact this rfl

/-- The agreement locus of two maps to `P¹` is closed. -/
theorem isClosed_agree {X : Scheme.{0}} (σ ρ : ToP1 X) : IsClosed {p | Agree σ ρ p} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hp
  show ∀ᶠ q in nhds p, ¬ Agree σ ρ q
  by_cases h1 : p ∈ σ.U <;> by_cases h2 : p ∈ ρ.U
  · have hne : X.evaluation σ.U p h1 σ.f ≠ X.evaluation ρ.U p h2 ρ.f := fun h =>
      hp ⟨⟨fun _ => h2, fun _ => h1⟩, fun _ _ => h⟩
    set W := σ.U ⊓ ρ.U with hW
    let s : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op σ.f -
      X.presheaf.map (homOfLE inf_le_right).op ρ.f
    have hsx : ∀ x (hx : x ∈ W), X.evaluation W x hx s =
        X.evaluation σ.U x hx.1 σ.f - X.evaluation ρ.U x hx.2 ρ.f := by
      intro x hx
      simp only [s, map_sub, eval_res]
    have hpb : p ∈ X.basicOpen s := by
      rw [← X.evaluation_ne_zero_iff_mem_basicOpen p (show p ∈ W from ⟨h1, h2⟩), hsx]
      exact sub_ne_zero.mpr hne
    filter_upwards [(X.basicOpen s).isOpen.mem_nhds hpb] with q hq hag
    have hqW : q ∈ W := X.basicOpen_le s hq
    have := (X.evaluation_ne_zero_iff_mem_basicOpen q hqW s).mpr hq
    rw [hsx, hag.2 hqW.1 hqW.2, sub_self] at this
    exact this rfl
  · exact disagree_nhds σ ρ p h1 h2
  · filter_upwards [disagree_nhds ρ σ p h2 h1] with q hq hag
    exact hq ((agree_comm σ ρ q).mp hag)
  · exact absurd ⟨⟨fun h => absurd h h1, fun h => absurd h h2⟩, fun h => absurd h h1⟩ hp

/-- Residue maps of the two projections at a point of the diagonal. -/
theorem diag_rfm (Y : Over (Spec (CommRingCat.of ℚ))) (r : ↥(pullback Y.hom Y.hom))
    (hr : r ∈ Set.range (fun q : Y.left => pullback.diagonal Y.hom q)) :
    ∃ e1 : pullback.fst Y.hom Y.hom r = pullback.snd Y.hom Y.hom r,
      (pullback.fst Y.hom Y.hom).residueFieldMap r =
        (Y.left.residueFieldCongr e1).hom ≫ (pullback.snd Y.hom Y.hom).residueFieldMap r := by
  obtain ⟨q, rfl⟩ := hr
  set D := pullback.diagonal Y.hom with hD
  have hpt : ∀ (f : pullback Y.hom Y.hom ⟶ Y.left), D ≫ f = 𝟙 _ → f (D q) = q := by
    intro f hf
    have := congrArg (fun h : Y.left ⟶ Y.left => h q) hf
    simpa using this
  have e1 : pullback.fst Y.hom Y.hom (D q) = pullback.snd Y.hom Y.hom (D q) :=
    (hpt _ (pullback.diagonal_fst Y.hom)).trans (hpt _ (pullback.diagonal_snd Y.hom)).symm
  refine ⟨e1, ?_⟩
  haveI : Mono (D.residueFieldMap q) :=
    ConcreteCategory.mono_of_injective _ (D.residueFieldMap q).hom.injective
  rw [← cancel_mono (D.residueFieldMap q), Category.assoc]
  have c1 := Scheme.residueFieldMap_comp D (pullback.fst Y.hom Y.hom) q
  have c2 := Scheme.residueFieldMap_comp D (pullback.snd Y.hom Y.hom) q
  have d1 := Scheme.Hom.residueFieldMap_congr (pullback.diagonal_fst Y.hom) q
  have d2 := Scheme.Hom.residueFieldMap_congr (pullback.diagonal_snd Y.hom) q
  rw [Scheme.residueFieldMap_id] at d1 d2
  rw [← c1, ← c2, d1, d2]
  simp only [Scheme.residueFieldCongr, eqToIso.hom]
  erw [Category.comp_id, Category.comp_id, eqToHom_trans]
  rfl

/-- A field-valued point of `Y ×_ℚ Y` over the diagonal has equal projections. -/
theorem diag_eq (Y : Over (Spec (CommRingCat.of ℚ))) {K : Type} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ pullback Y.hom Y.hom)
    (hb : (Scheme.SpecToEquivOfField K _ b).1 ∈ Set.range (fun q : Y.left => pullback.diagonal Y.hom q)) :
    b ≫ pullback.fst Y.hom Y.hom = b ≫ pullback.snd Y.hom Y.hom := by
  apply (Scheme.SpecToEquivOfField K Y.left).injective
  rw [specToEquivOfField_comp_right, specToEquivOfField_comp_right,
    Scheme.SpecToEquivOfField_eq_iff]
  obtain ⟨e1, he1⟩ := diag_rfm Y _ hb
  refine ⟨e1, ?_⟩
  simp only
  rw [he1, Category.assoc]

/-- **`FibreGenericC` (proved).** Jacobson on `P = Y ×_ℚ Y`: the agreement locus `A` of `π∘pr₁`,
`π∘pr₂` is closed, `Γ = ⋃_{g ∈ G} (pr₁ ≫ g, pr₂)⁻¹(Δ)` is closed (`Y` separated), `A \ Γ` has no
closed point (closed points come from `ℚ̄`-points, where the hypothesis applies), so `A ⊆ Γ`; a
`ℂ`-point of `A` over `Γ` has `y ≫ g = y'` (`diag_eq`). -/
theorem fibreGenericC_proof (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) :
    FibreGenericC Y π := by
  intro hP hS G hGf hQ y y' hval
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : IsSeparated Y.hom := inferInstance
  let PO : Over (Spec (CommRingCat.of ℚ)) := Over.mk ((pullback.fst Y.hom Y.hom) ≫ Y.hom)
  haveI : LocallyOfFiniteType PO.hom := by
    show LocallyOfFiniteType ((pullback.fst Y.hom Y.hom) ≫ Y.hom); infer_instance
  haveI : JacobsonSpace ↥(pullback Y.hom Y.hom : Scheme.{0}) :=
    LocallyOfFiniteType.jacobsonSpace PO.hom
  set σ1 := π.comp (pullback.fst Y.hom Y.hom) with hσ1
  set σ2 := π.comp (pullback.snd Y.hom Y.hom) with hσ2
  set D := pullback.diagonal Y.hom with hD
  have hLw : ∀ g : Y ≅ Y, ((pullback.fst Y.hom Y.hom) ≫ g.hom.left) ≫ Y.hom = (pullback.snd Y.hom Y.hom) ≫ Y.hom := fun g => by
    rw [Category.assoc, Over.w g.hom, pullback.condition]
  let L : (Y ≅ Y) → (pullback Y.hom Y.hom ⟶ pullback Y.hom Y.hom) :=
    fun g => pullback.lift ((pullback.fst Y.hom Y.hom) ≫ g.hom.left) (pullback.snd Y.hom Y.hom) (hLw g)
  have hLf : ∀ g : Y ≅ Y, L g ≫ pullback.fst Y.hom Y.hom = pullback.fst Y.hom Y.hom ≫ g.hom.left :=
    fun g => pullback.lift_fst _ _ _
  have hLs : ∀ g : Y ≅ Y, L g ≫ pullback.snd Y.hom Y.hom = pullback.snd Y.hom Y.hom :=
    fun g => pullback.lift_snd _ _ _
  let Γ : Set ↥(pullback Y.hom Y.hom : Scheme.{0}) :=
    ⋃ g ∈ G, (fun x => L g x) ⁻¹' Set.range (fun q : Y.left => D q)
  have hΓ : IsClosed Γ := by
    apply hGf.isClosed_biUnion
    intro g _
    exact D.isClosedEmbedding.isClosed_range.preimage (L g).continuous
  have hmemΓ : ∀ (K : Type) [Field K] (b : Spec (CommRingCat.of K) ⟶ (pullback Y.hom Y.hom : Scheme.{0}))
      (g : Y ≅ Y) (c : Spec (CommRingCat.of K) ⟶ Y.left), b ≫ L g = c ≫ D →
      L g (Scheme.SpecToEquivOfField K _ b).1 ∈ Set.range (fun q : Y.left => D q) := by
    intro K _ b g c h
    have := congrArg (fun t => (Scheme.SpecToEquivOfField K _ t).1) h
    simp only [specToEquivOfField_comp_right] at this
    exact ⟨_, this.symm⟩
  -- the agreement locus lies in `Γ`
  have hAΓ : ∀ p, Agree σ1 σ2 p → p ∈ Γ := by
    intro p hp
    by_contra hpΓ
    obtain ⟨x, ⟨hxA, hxΓ⟩, hxc⟩ := nonempty_inter_closedPoints
      (Z := {p : ↥(pullback Y.hom Y.hom : Scheme.{0}) | Agree σ1 σ2 p} ∩ Γᶜ) ⟨p, hp, hpΓ⟩
      ((isClosed_agree σ1 σ2).isLocallyClosed.inter hΓ.isOpen_compl.isLocallyClosed)
    obtain ⟨emb, z, hz⟩ := exists_qbarPt PO x hxc
    let zl : Spec (CommRingCat.of Qbar) ⟶ (pullback Y.hom Y.hom : Scheme.{0}) := z.left
    have hzl : zl = (Scheme.SpecToEquivOfField Qbar (pullback Y.hom Y.hom : Scheme.{0})).symm
        ⟨x, emb⟩ := hz
    have hzw : z.left ≫ ((pullback.fst Y.hom Y.hom) ≫ Y.hom) = (fieldPt Qbar).hom := Over.w z
    let z1 : fieldPt Qbar ⟶ Y := Over.homMk (z.left ≫ (pullback.fst Y.hom Y.hom)) (by
      rw [Category.assoc]; exact hzw)
    let z2 : fieldPt Qbar ⟶ Y := Over.homMk (z.left ≫ (pullback.snd Y.hom Y.hom)) (by
      rw [Category.assoc, ← pullback.condition]; exact hzw)
    have hzval : π.val (K := Qbar) z1.left = π.val (K := Qbar) z2.left := by
      show π.val (zl ≫ (pullback.fst Y.hom Y.hom)) = π.val (zl ≫ (pullback.snd Y.hom Y.hom))
      rw [← ToP1.val_comp_right, ← ToP1.val_comp_right, ← hσ1, ← hσ2]
      apply (val_eq_iff_agree σ1 σ2 zl).mpr
      rw [hzl, Equiv.apply_symm_apply]
      exact hxA
    obtain ⟨g, hg, hgz⟩ := (hQ z1 z2).mp hzval
    apply hxΓ
    refine Set.mem_biUnion hg ?_
    let z2l : Spec (CommRingCat.of Qbar) ⟶ Y.left := z2.left
    have hfac : zl ≫ L g = z2l ≫ D := by
      apply pullback.hom_ext
      · rw [Category.assoc, hLf g, Category.assoc, pullback.diagonal_fst, Category.comp_id]
        have h3 := congrArg CommaMorphism.left hgz
        exact h3.symm
      · rw [Category.assoc, hLs g, Category.assoc, pullback.diagonal_snd, Category.comp_id]
        rfl
    have := hmemΓ Qbar zl g z2l hfac
    rw [hzl, Equiv.apply_symm_apply] at this
    exact this
  -- the `ℂ`-point
  have hyw : y.left ≫ Y.hom = y'.left ≫ Y.hom := by rw [Over.w y, Over.w y']
  let w : Spec (CommRingCat.of ℂ) ⟶ (pullback Y.hom Y.hom : Scheme.{0}) :=
    pullback.lift y.left y'.left hyw
  have hw1 : w ≫ pullback.fst Y.hom Y.hom = y.left := pullback.lift_fst _ _ _
  have hw2 : w ≫ pullback.snd Y.hom Y.hom = y'.left := pullback.lift_snd _ _ _
  have hwA : Agree σ1 σ2 (Scheme.SpecToEquivOfField ℂ _ w).1 := by
    apply (val_eq_iff_agree σ1 σ2 w).mp
    rw [hσ1, hσ2, ToP1.val_comp_right, ToP1.val_comp_right, hw1, hw2]
    exact hval
  obtain ⟨g, hg, hgΓ⟩ := Set.mem_iUnion₂.mp (hAΓ _ hwA)
  refine ⟨g, hg, ?_⟩
  have key := diag_eq Y (w ≫ L g) (by rw [specToEquivOfField_comp_right]; exact hgΓ)
  rw [Category.assoc, Category.assoc, hLf g, hLs g, ← Category.assoc, hw1, hw2] at key
  ext1
  exact key.symm

/-- **`FibreTransferC` (proved).** -/
theorem fibreTransferC_proof (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) :
    FibreTransferC Y π :=
  fibreTransferC_of' Y π (fibreGenericC_proof Y π)

/-! ## `TwistOrbitFinite` from R1hecke, `TorsionStructure` and two algebra facts -/

/-- **GLUE, proved in mobius-glue** (`scratch/mobius-glue/MobiusGlue.lean` §7, `AutOInnerFinite`;
from the kernel's Skolem–Noether and `N(𝒪)/ℚ^×𝒪^× = {1, i, j, ij}`; copied verbatim up to writing
`LeafQM.O` for `O`; it cannot be
imported here). Every automorphism of `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely
many. -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (LeafQM.O ≃+* LeafQM.O), T.Finite ∧ ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ t ∈ T,
    ∃ v : (LeafQM.O)ˣ, ∀ a : LeafQM.O,
      α a = (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O)

/-- **GLUE (finite computation; strong approximation for `𝒪¹`).** Every element of `𝒪` that is
invertible modulo `3𝒪` is congruent modulo `3𝒪` to a unit of `𝒪` (`𝒪^× → (𝒪/3𝒪)^×` is onto).

Why true: `B` is indefinite, so `𝒪¹` is dense in `∏_p 𝒪_p¹` (Eichler's strong approximation,
Vignéras, *Arithmétique des algèbres de quaternions*, III.4; UNVERIFIED locator), hence
`𝒪¹ → (𝒪/3𝒪)¹` is onto; together with `1 + i` (reduced norm `−1`) this covers
`(𝒪/3𝒪)^×` (72 elements). A finite check: the reductions of finitely many explicit units of `𝒪`
generate the 72 classes. Size: small-medium (a `decide`-style computation over `(ℤ/3)⁴`). -/
def UnitLiftMod3 : Prop :=
  ∀ u₀ v₀ : LeafQM.O, (∃ c : LeafQM.O, v₀ * u₀ - 1 = 3 * c) →
    ∃ u : (LeafQM.O)ˣ, ∃ c : LeafQM.O, (u : LeafQM.O) - u₀ = 3 * c

section TwistOrbit

variable {K : Type} [Field K]

/-- Transport of a level structure along an isomorphism of QM pairs (copied from mobius-glue). -/
def transportLevel' {A A' : PkgI3.AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (PkgI3.AbVar.ptMap (L := K) f.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ f.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ f.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ f.φ.hom) = _
    rw [Category.assoc, f.equivariant a, Category.assoc]
  ker a := by
    rw [← e.ker]
    constructor
    · intro h
      have h' : Additive.toMul (e.eta a) ≫ f.φ.hom = 1 := congrArg Additive.toMul h
      have : Additive.toMul (e.eta a) = 1 := by
        calc Additive.toMul (e.eta a) = Additive.toMul (e.eta a) ≫ f.φ.hom ≫ f.ψ.hom := by
              rw [f.left, Category.comp_id]
          _ = 1 := by rw [← Category.assoc, h', MonObj.one_comp]
      exact congrArg Additive.ofMul this
    · intro h
      change Additive.ofMul (Additive.toMul (e.eta a) ≫ f.φ.hom) = 0
      rw [h]
      change Additive.ofMul ((1 : _ ⟶ _) ≫ f.φ.hom) = 0
      rw [MonObj.one_comp]
      rfl

/-- A level-3 isomorphism gives a QM isomorphism. -/
def QML3.Iso.toQMIso {P Q : QML3 K} (f : P.Iso Q) : QMIso P.q Q.q where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant := f.equivariant

/-- Twists by `t` and by `v t v⁻¹` are isomorphic through `ι(v)` (copied from mobius-glue). -/
def conjUnitIso' {A : PkgI3.AbVar K} (q : QMStr A) (t α : LeafQM.O ≃+* LeafQM.O) (v : (LeafQM.O)ˣ)
    (hv : ∀ a, α a = (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O)) :
    QMIso (q.twist t) (q.twist α) where
  φ := q.iota v
  ψ := q.iota ↑v⁻¹
  left := by
    have : q.iota ↑v⁻¹ * q.iota ↑v = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    exact congrArg PkgI3.AbVar.Hom.hom this
  right := by
    have : q.iota ↑v * q.iota ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact congrArg PkgI3.AbVar.Hom.hom this
  equivariant a := by
    have : q.iota (v : LeafQM.O) * q.iota (t a) = q.iota (α a) * q.iota v := by
      rw [← map_mul, ← map_mul, hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    exact congrArg PkgI3.AbVar.Hom.hom this

/-- Finitely many representatives of the units of `𝒪` modulo `3𝒪`. -/
theorem unitReps : ∃ U : Set (LeafQM.O)ˣ, U.Finite ∧
    ∀ u : (LeafQM.O)ˣ, ∃ u' ∈ U, ∃ c : LeafQM.O, (u : LeafQM.O) - u' = 3 * c := by
  classical
  -- the class of `u` modulo `3𝒪`: its coordinates mod 3
  have hcoord : ∀ x : LeafQM.O, ∃ n : Fin 4 → ℤ, (x : LeafQM.B) = LeafQM.ofInt n := fun x => x.2
  choose n hn using hcoord
  let cls : (LeafQM.O)ˣ → (Fin 4 → ZMod 3) := fun u i => (n u i : ZMod 3)
  have hrep : ∀ c ∈ Set.range cls, ∃ u : (LeafQM.O)ˣ, cls u = c := fun c hc => hc
  choose! r hr using hrep
  refine ⟨r '' Set.range cls, (Set.toFinite (Set.range cls)).image r, fun u => ⟨r (cls u), ⟨_, ⟨u, rfl⟩, rfl⟩, ?_⟩⟩
  have hcl : cls (r (cls u)) = cls u := hr _ ⟨u, rfl⟩
  -- coordinates agree mod 3
  have hmod : ∀ i, (3 : ℤ) ∣ n u i - n (r (cls u)) i := by
    intro i
    have := congrFun hcl i
    simp only [cls] at this
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mp this
    exact_mod_cast h3
  choose k hk using hmod
  refine ⟨⟨LeafQM.ofInt k, ⟨k, rfl⟩⟩, Subtype.ext ?_⟩
  show ((u : LeafQM.O) : LeafQM.B) - ((r (cls u) : LeafQM.O) : LeafQM.B) = 3 * LeafQM.ofInt k
  rw [hn, hn, LeafQM.AV.ofInt_sub, LeafQM.AV.three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  linear_combination hk i

/-- The twist relation is the orbit relation of `{g_t ∘ h_u : t ∈ T, u ∈ U}`, over any field of
characteristic `0` (proved). -/
theorem twist_iff_orbit (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (hT : ObjBridge.TorsionStructure) (hU : UnitLiftMod3)
    (T : Set (LeafQM.O ≃+* LeafQM.O))
    (hTα : ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ t ∈ T, ∃ v : (LeafQM.O)ˣ, ∀ a : LeafQM.O,
      α a = (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O))
    (U : Set (LeafQM.O)ˣ) (hUu : ∀ u : (LeafQM.O)ˣ, ∃ u' ∈ U, ∃ c : LeafQM.O, (u : LeafQM.O) - u' = 3 * c)
    (g : (LeafQM.O ≃+* LeafQM.O) → (Y ≅ Y))
    (hg : ∀ α (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ (g α).hom) = M3.twist α (Φ K y))
    (h : (LeafQM.O)ˣ → (Y ≅ Y))
    (hh : ∀ u (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ (h u).hom) = M3.rightMul u (Φ K y))
    (K : Type) [Field K] [Algebra ℚ K] [CharZero K] (y y' : fieldPt K ⟶ Y) (Q Q' : QML3 K)
    (hQ : Φ K y = M3.mk Q) (hQ' : Φ K y' = M3.mk Q') :
    (∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
      ∃ G' ∈ (fun p : (LeafQM.O ≃+* LeafQM.O) × (LeafQM.O)ˣ => g p.1 ≪≫ h p.2) '' (T ×ˢ U),
        y' = y ≫ G'.hom := by
  constructor
  · rintro ⟨α, ⟨f⟩⟩
    obtain ⟨t, ht, v, hv⟩ := hTα α
    let f' : QMIso (Q.q.twist t) Q'.q := (conjUnitIso' Q.q t α v hv).trans f
    let P : QML3 K := Q.twist t
    let e' : Level3 P.q := transportLevel' f'.symm Q'.e
    obtain ⟨u₀, v₀, hinv, hu₀⟩ := Level3.torsor hT P e'
    obtain ⟨u, cu, hcu⟩ := hU u₀ v₀ hinv
    obtain ⟨u', hu'U, cu', hcu'⟩ := hUu u
    have hlev : ∀ a : LeafQM.O, e'.eta a = P.e.eta (a * u') := by
      intro a
      rw [hu₀ a, P.e.eq_iff]
      exact ⟨a * (cu' - cu), by
        calc a * u₀ - a * (u' : LeafQM.O)
            = a * (((u : LeafQM.O) - u') - ((u : LeafQM.O) - u₀)) := by noncomm_ring
          _ = a * (3 * cu' - 3 * cu) := by rw [hcu, hcu']
          _ = 3 * (a * (cu' - cu)) := by noncomm_ring⟩
    let iso : (P.rightMul u').Iso Q' :=
      { φ := f'.φ
        ψ := f'.ψ
        left := f'.left
        right := f'.right
        equivariant := f'.equivariant
        level := fun a => by
          change Additive.ofMul (Additive.toMul (P.e.eta (a * u')) ≫ f'.φ.hom) = Q'.e.eta a
          rw [← hlev a]
          change Additive.ofMul ((Additive.toMul (Q'.e.eta a) ≫ f'.ψ.hom) ≫ f'.φ.hom) = _
          rw [Category.assoc, f'.right, Category.comp_id]
          rfl }
    have hm : Φ K (y ≫ (g t ≪≫ h u').hom) = M3.mk Q' := by
      rw [Iso.trans_hom, ← Category.assoc, hh, hg, hQ, M3.twist_mk]
      exact Quotient.sound ⟨iso⟩
    exact ⟨g t ≪≫ h u', ⟨(t, u'), ⟨ht, hu'U⟩, rfl⟩, (Φ K).injective (hQ'.trans hm.symm)⟩
  · rintro ⟨G', ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩, hy'⟩
    have hm : M3.mk Q' = M3.mk ((Q.twist t).rightMul u) := by
      rw [← hQ', hy', Iso.trans_hom, ← Category.assoc, hh, hg, hQ, M3.twist_mk]
      rfl
    obtain ⟨iso⟩ := Quotient.exact hm
    exact ⟨t, ⟨QML3.Iso.toQMIso iso.symm⟩⟩

end TwistOrbit

/-- **`TwistOrbitFinite` from R1hecke, the textbook leaf `TorsionStructure` (T5), `AutOInnerFinite`
(proved in mobius-glue) and `UnitLiftMod3` (proved).** -/
theorem twistOrbitFinite_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (hH : R1heckeProps Y Φ) (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite)
    (hU : UnitLiftMod3) : TwistOrbitFinite Y Φ := by
  obtain ⟨hα, hu⟩ := hH
  choose g hg using hα
  choose h hh using hu
  obtain ⟨T, hTf, hTα⟩ := hA
  obtain ⟨U, hUf, hUu⟩ := unitReps
  exact ⟨_, (hTf.prod hUf).image (fun p => g p.1 ≪≫ h p.2),
    fun y y' Q Q' hQ hQ' => twist_iff_orbit Y Φ hT hU T hTα U hUu g hg h hh Qbar y y' Q Q' hQ hQ',
    fun y y' Q Q' hQ hQ' => twist_iff_orbit Y Φ hT hU T hTα U hUu g hg h hh ℂ y y' Q Q' hQ hQ'⟩

/-! ## `UnitLiftMod3` (proved by a finite computation) -/

/-- The reduced norm of `ofInt n` (`= nrd`, an integer). -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2

theorem nrdZ_mulCoord (n m : Fin 4 → ℤ) : nrdZ (LeafQM.mulCoord n m) = nrdZ n * nrdZ m := by
  simp [nrdZ, LeafQM.mulCoord]; ring

/-- Coordinates of the conjugate of `ofInt n`. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem mulCoord_conjC (n : Fin 4 → ℤ) : LeafQM.mulCoord (conjC n) n = ![nrdZ n, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [LeafQM.mulCoord, conjC, nrdZ] <;> ring

theorem mulCoord_conjC' (n : Fin 4 → ℤ) : LeafQM.mulCoord n (conjC n) = ![nrdZ n, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [LeafQM.mulCoord, conjC, nrdZ] <;> ring

/-- A unit of `𝒪` in each class of `(𝒪/3𝒪)^×` (`py/unit_table.py`; entry `c₀ + 3c₁ + 9c₂ + 27c₃`). -/
def unitTbl : Fin 81 → (Fin 4 → ℤ) :=
  ![![1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![-3, -2, 0, 0], ![1, 1, 0, 0], ![-1, 1, 0, 0], ![-3, -1, -3, -3], ![1, -1, 0, 0], ![-1, -1, 0, 0], ![0, 0, 1, 0], ![1, 0, 0, 0], ![-1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![-1, 1, 1, 0], ![0, -1, 1, 0], ![1, -1, 1, 0], ![-1, -1, 1, 0], ![0, 0, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, 0], ![-1, 1, -1, 0], ![0, -1, -1, 0], ![1, -1, -1, 0], ![-1, -1, -1, 0], ![-3, 0, 0, -2], ![1, 0, 0, 1], ![-1, 0, 0, 1], ![1, 0, 0, 0], ![-2, -2, 3, 1], ![-1, -2, 3, 1], ![-3, 2, 0, -2], ![1, -1, 0, 1], ![-1, -1, 0, 1], ![0, 0, 1, 1], ![1, 0, 1, 1], ![-1, 0, 1, 1], ![-3, -2, 1, 1], ![1, 0, 0, 0], ![-1, -2, -2, 1], ![0, -1, 1, 1], ![1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![1, 0, -1, 1], ![-1, 0, -1, 1], ![-3, -2, 2, 1], ![-2, -2, -1, 1], ![1, 0, 0, 0], ![0, -1, -1, 1], ![1, -1, -1, 1], ![-1, -1, -1, 1], ![-3, -3, -3, -1], ![1, 0, 0, -1], ![-1, 0, 0, -1], ![-3, -2, 0, 2], ![1, 1, 0, -1], ![-1, 1, 0, -1], ![1, 0, 0, 0], ![-2, -1, 3, -1], ![-1, -1, 3, -1], ![0, 0, 1, -1], ![1, 0, 1, -1], ![-1, 0, 1, -1], ![0, 1, 1, -1], ![1, 1, 1, -1], ![-1, 1, 1, -1], ![-3, -1, 1, -1], ![1, 0, 0, 0], ![-1, -1, -2, -1], ![0, 0, -1, -1], ![1, 0, -1, -1], ![-1, 0, -1, -1], ![0, 1, -1, -1], ![1, 1, -1, -1], ![-1, 1, -1, -1], ![-3, -1, 2, -1], ![-2, -1, -1, -1], ![1, 0, 0, 0]]

/-- The index of a class. -/
def encC (a b c d : ZMod 3) : Fin 81 :=
  ⟨a.val + 3 * b.val + 9 * c.val + 27 * d.val, by
    have ha : a.val < 3 := ZMod.val_lt a
    have hb : b.val < 3 := ZMod.val_lt b
    have hc : c.val < 3 := ZMod.val_lt c
    have hd : d.val < 3 := ZMod.val_lt d
    omega⟩

theorem unitTbl_spec : ∀ a b c d : ZMod 3, a ^ 2 + a * c + c ^ 2 - 2 * b ^ 2 - 2 * b * d - 2 * d ^ 2 ≠ 0 →
    (((unitTbl (encC a b c d) 0 : ℤ) : ZMod 3) = a ∧ ((unitTbl (encC a b c d) 1 : ℤ) : ZMod 3) = b ∧
      ((unitTbl (encC a b c d) 2 : ℤ) : ZMod 3) = c ∧ ((unitTbl (encC a b c d) 3 : ℤ) : ZMod 3) = d) ∧
    (nrdZ (unitTbl (encC a b c d)) = 1 ∨ nrdZ (unitTbl (encC a b c d)) = -1) := by
  set_option maxRecDepth 100000 in decide

/-- **`UnitLiftMod3` (proved).** -/
theorem unitLiftMod3_proof : UnitLiftMod3 := by
  rintro ⟨u₀, n, hn⟩ ⟨v₀, m, hm⟩ ⟨⟨c, k, hk⟩, hc⟩
  have hc' := congrArg Subtype.val hc
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one] at hc'
  have h33 : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3
  rw [h33, hm, hn, hk, LeafQM.ofInt_mul, ← LeafQM.ofInt_one, LeafQM.AV.ofInt_sub,
    LeafQM.AV.three_mul_ofInt] at hc'
  have hco := LeafQM.AV.ofInt_injective hc'
  -- `nrd(u₀) ≢ 0 mod 3`
  have hmn : ∀ i, LeafQM.mulCoord m n i = ![1, 0, 0, 0] i + 3 * k i := fun i => by
    have := congrFun hco i
    simp only [Pi.sub_apply] at this
    linear_combination this
  have hn1 : ((nrdZ (LeafQM.mulCoord m n) : ℤ) : ZMod 3) = 1 := by
    have e : LeafQM.mulCoord m n = fun i => ![1, 0, 0, 0] i + 3 * k i := funext hmn
    rw [e]
    simp only [nrdZ]
    push_cast
    have h3 : (3 : ZMod 3) = 0 := rfl
    rw [h3]
    norm_num
  have hnrd : (nrdZ n : ZMod 3) ≠ 0 := by
    intro h0
    rw [nrdZ_mulCoord, Int.cast_mul, h0, mul_zero] at hn1
    exact zero_ne_one hn1
  obtain ⟨⟨t0, t1, t2, t3⟩, hpm⟩ := unitTbl_spec (n 0 : ZMod 3) (n 1 : ZMod 3) (n 2 : ZMod 3)
    (n 3 : ZMod 3) (by
      have : ((nrdZ n : ℤ) : ZMod 3) = (n 0 : ZMod 3) ^ 2 + (n 0 : ZMod 3) * (n 2 : ZMod 3) +
          (n 2 : ZMod 3) ^ 2 - 2 * (n 1 : ZMod 3) ^ 2 - 2 * (n 1 : ZMod 3) * (n 3 : ZMod 3) -
          2 * (n 3 : ZMod 3) ^ 2 := by simp [nrdZ]
      rw [← this]; exact hnrd)
  set t := unitTbl (encC (n 0 : ZMod 3) (n 1 : ZMod 3) (n 2 : ZMod 3) (n 3 : ZMod 3)) with htdef
  set ε := nrdZ t with hε
  have hεε : ε * ε = 1 := by rcases hpm with h | h <;> rw [h] <;> norm_num
  -- the unit `ofInt t`, with inverse `ε · conj`
  let x : LeafQM.O := ⟨LeafQM.ofInt t, t, rfl⟩
  let y : LeafQM.O := ⟨LeafQM.ofInt (ε • conjC t), ε • conjC t, rfl⟩
  have hxy : x * y = 1 := by
    apply Subtype.ext
    show LeafQM.ofInt t * LeafQM.ofInt (ε • conjC t) = 1
    rw [LeafQM.ofInt_mul, ← LeafQM.ofInt_one]
    congr 1
    funext i
    have := congrFun (mulCoord_conjC' t) i
    fin_cases i <;> simp [LeafQM.mulCoord, conjC] at this ⊢ <;>
      first | linear_combination ε * this | linear_combination ε * this + hεε
  have hyx : y * x = 1 := by
    apply Subtype.ext
    show LeafQM.ofInt (ε • conjC t) * LeafQM.ofInt t = 1
    rw [LeafQM.ofInt_mul, ← LeafQM.ofInt_one]
    congr 1
    funext i
    have := congrFun (mulCoord_conjC t) i
    fin_cases i <;> simp [LeafQM.mulCoord, conjC] at this ⊢ <;>
      first | linear_combination ε * this | linear_combination ε * this + hεε
  refine ⟨⟨x, y, hxy, hyx⟩, ?_⟩
  -- the congruence
  have hdiv : ∀ i, ∃ q : ℤ, t i - n i = 3 * q := by
    intro i
    have hti : ((t i : ℤ) : ZMod 3) = (n i : ZMod 3) := by
      fin_cases i
      · exact t0
      · exact t1
      · exact t2
      · exact t3
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mp hti.symm
    exact ⟨q, by push_cast at hq; linear_combination hq⟩
  choose q hq using hdiv
  refine ⟨⟨LeafQM.ofInt q, q, rfl⟩, Subtype.ext ?_⟩
  show LeafQM.ofInt t - u₀ = ((3 : LeafQM.O) : LeafQM.B) * LeafQM.ofInt q
  rw [h33, hn, LeafQM.AV.ofInt_sub, LeafQM.AV.three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  exact hq i

/-- **`TwistOrbitFinite` from R1hecke, `TorsionStructure` and `AutOInnerFinite` (proved).** -/
theorem twistOrbitFinite_of' (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (hH : R1heckeProps Y Φ) (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) :
    TwistOrbitFinite Y Φ :=
  twistOrbitFinite_of Y Φ hH hT hA unitLiftMod3_proof

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.piTwistC_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.fibreTransferC_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.toP1AgreeC_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.fibreTransferC_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.unitLiftMod3_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.twistOrbitFinite_of
