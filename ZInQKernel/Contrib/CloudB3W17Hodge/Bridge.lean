/-
Original work of the Z-in-Q kernel (cloud batch 3, W17, task hodge-author). Not copied from
HodgeConjecture. It builds on the vendored port under `CloudB3W17Hodge/Port/`, whose provenance
and licence are recorded in `CloudB3W17Hodge/NOTICE` and `CloudB3W17Hodge/LICENSE`.

# The ported complex points are the kernel's complex points

The vendored port works with `AlgebraicGeometry.Point ℂ X`, the `ℂ`-points of a scheme
`X : Over (Spec ↧ℂ)` presented as `Over.mk (𝟙 (Spec ↧ℂ)) ⟶ X`, and evaluates a regular section
at such a point through the stalk map `Scheme.stalkClosedPointTo`.

The kernel presents the same `ℂ`-points as `PkgI3.AbVar.ptObj (K := ℂ) ℂ ⟶ X`, where
`ptObj = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)))`, and evaluates through
`Scheme.Hom.appLE U ⊤ ≫ (Scheme.ΓSpecIso ↧ℂ).hom`.

Both live in the same over-category: `↧ℂ` elaborates to a literal `CommRingCat.of ℂ`. They differ
only in the base object, and `algebraMap ℂ ℂ` is the identity, so `Spec.map_id` makes the two base
objects isomorphic by an isomorphism that is the identity on the underlying scheme. Consequently
the comparison `cptEquiv` does not move the underlying scheme morphism *definitionally*
(`cptEquiv_left` is `rfl`), and the two evaluation routes agree by Mathlib's
`AlgebraicGeometry.Scheme.germ_stalkClosedPointTo`.

`CPt`, `XPtIn`, `XevalAt`, `basicSets` and `classicalTopology` are the definitions of the host task
`unif-printed` (`docs/research/unif-printed.md`), repeated here because that task's module is not
on `main`. They are definitions only; this file discharges no leaf and duplicates no reduction.

## Main results

* `CloudB3W17Hodge.cptEquiv` : `CPt X ≃ AlgebraicGeometry.Point ℂ X`;
* `CloudB3W17Hodge.cptEquiv_left` : the comparison does not move the scheme morphism (`rfl`);
* `CloudB3W17Hodge.ptIn_iff` : `XPtIn X P U ↔ cptEquiv X P ∈ Point.overOpen U`;
* `CloudB3W17Hodge.evaluate_eq` : the ported evaluation, written through `appLE`;
* `CloudB3W17Hodge.xevalAt_eq_evaluate` : the kernel's `XevalAt` is the ported `Point.evaluate`;
* `CloudB3W17Hodge.classicalTopology_eq` : the kernel's classical topology is the ported analytic
  topology, transported along `cptEquiv`;
* `CloudB3W17Hodge.cptHomeomorph` : the comparison as a homeomorphism;
* `CloudB3W17Hodge.chartedSpace` : the ported `ChartedSpace (Fin d → ℂ)` carried over to `CPt X`.
-/
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import ZInQKernel.HDecomp.Analytic.Uniformization
import Mathlib.AlgebraicGeometry.Stalk

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace CloudB3W17Hodge

open PkgI3 (AbVar)

noncomputable section

/-! ## The kernel's carrier, topology and evaluation (host definitions, repeated) -/

/-- `ℂ`-points of a `ℂ`-scheme: `ℂ`-morphisms `Spec ℂ → X`. -/
abbrev CPt (X : Over (Spec ↧ℂ)) : Type := AbVar.ptObj (K := ℂ) ℂ ⟶ X

variable (X : Over (Spec ↧ℂ))

/-- The `ℂ`-point `P` lies in the Zariski open `U`. -/
def XPtIn (P : CPt X) (U : X.left.Opens) : Prop := ⊤ ≤ P.left ⁻¹ᵁ U

open Classical in
/-- The value at a `ℂ`-point of a regular function. -/
def XevalAt (U : X.left.Opens) (f : Γ(X.left, U)) (P : CPt X) : ℂ :=
  if h : XPtIn X P U then
    ((P.left.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso ↧ℂ).hom).hom f
  else 0

/-- The basic open sets `{P ∈ U(ℂ) : ‖f(P) - z‖ < ε}`. -/
def basicSets : Set (Set (CPt X)) :=
  {S | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (z : ℂ) (ε : ℝ),
    S = {P | XPtIn X P U ∧ ‖XevalAt X U f P - z‖ < ε}}

/-- The classical (analytic) topology on `X(ℂ)`: the coarsest topology in which every `U(ℂ)` is
open and every regular function on `U` is continuous on `U(ℂ)`. -/
def classicalTopology : TopologicalSpace (CPt X) := TopologicalSpace.generateFrom (basicSets X)

/-! ## The comparison with the ported carrier -/

/-- The kernel's base point object is isomorphic to the ported one, by an isomorphism which is the
identity on the underlying scheme: `algebraMap ℂ ℂ` is the identity, so `Spec.map_id` applies. -/
def ptIso : AbVar.ptObj (K := ℂ) ℂ ≅ Over.mk (𝟙 (Spec ↧ℂ)) :=
  Over.isoMk (Iso.refl _) (by simp [PkgI3.AbVar.ptObj])

/-- The kernel's `ℂ`-points are the ported `ℂ`-points. -/
def cptEquiv : CPt X ≃ AlgebraicGeometry.Point ℂ X where
  toFun P := ptIso.inv ≫ P
  invFun Q := ptIso.hom ≫ Q
  left_inv P := by simp
  right_inv Q := by simp

/-- The comparison does not move the underlying scheme morphism, definitionally. -/
@[simp]
lemma cptEquiv_left (P : CPt X) : (cptEquiv X P).left = P.left := rfl

/-- The underlying scheme point of the comparison is the image of the closed point. -/
@[simp]
lemma underlying_eq (P : CPt X) :
    (cptEquiv X P).underlying = P.left (IsLocalRing.closedPoint ℂ) := rfl

/-- Lying over a Zariski open agrees with the ported `Point.overOpen`. -/
lemma ptIn_iff (P : CPt X) (U : X.left.Opens) :
    XPtIn X P U ↔ (cptEquiv X P).underlying ∈ U :=
  ⟨fun h => h (TopologicalSpace.Opens.mem_top _),
    fun h => (AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem P.left h).ge⟩

/-- **The two evaluation routes agree.** The ported evaluation of a regular section at a `ℂ`-point,
defined through the stalk map `Scheme.stalkClosedPointTo`, is the sections-level evaluation
`appLE U ⊤ ≫ ΓSpecIso.hom`. Both are restrictions of `f.app U` along the same pair of opens, which
`Scheme.germ_stalkClosedPointTo` identifies; the two restriction maps agree because `Opens` is a
partial order. -/
lemma evaluate_eq (Q : AlgebraicGeometry.Point ℂ X) (U : X.left.Opens) (f : Γ(X.left, U))
    (hQ : Q.underlying ∈ U) :
    AlgebraicGeometry.Point.evaluate U f Q
      = ((Q.left.appLE U ⊤ (AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem
            Q.left hQ).ge) ≫ (Scheme.ΓSpecIso ↧ℂ).hom).hom f := by
  classical
  rw [AlgebraicGeometry.Point.evaluate, dif_pos hQ]
  have key := AlgebraicGeometry.Scheme.germ_stalkClosedPointTo (R := ↧ℂ) Q.left U hQ
  change (ConcreteCategory.hom (X.left.presheaf.germ U
      (Q.left (IsLocalRing.closedPoint _)) hQ ≫ Scheme.stalkClosedPointTo Q.left)) f = _
  rw [key]
  simp only [Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    Category.assoc]
  congr 2

/-- **The kernel's evaluation is the ported evaluation.** -/
lemma xevalAt_eq_evaluate (U : X.left.Opens) (f : Γ(X.left, U)) (P : CPt X) :
    XevalAt X U f P = AlgebraicGeometry.Point.evaluate U f (cptEquiv X P) := by
  classical
  by_cases h : XPtIn X P U
  · have h' : (cptEquiv X P).underlying ∈ U := (ptIn_iff X P U).mp h
    rw [evaluate_eq X (cptEquiv X P) U f h', XevalAt, dif_pos h]
    rfl
  · have h' : ¬ (cptEquiv X P).underlying ∈ U := fun hc => h ((ptIn_iff X P U).mpr hc)
    rw [XevalAt, dif_neg h, AlgebraicGeometry.Point.evaluate, dif_neg h']

/-- **The kernel's classical topology is the ported analytic topology.** `classicalTopology X` is
generated by the `ε`-balls `{P ∈ U(ℂ) : ‖f(P) - z‖ < ε}`; the ported `Point.analyticTopology` is
generated by `{z ∈ U(ℂ) : s(z) ∈ V}` for `V ⊆ ℂ` open. The two generate the same topology, because
the open balls are a basis of `ℂ`. -/
lemma classicalTopology_eq :
    classicalTopology X
      = TopologicalSpace.induced (cptEquiv X)
          (AlgebraicGeometry.Point.analyticTopology (R := ℂ) (X := X)) := by
  rw [show (AlgebraicGeometry.Point.analyticTopology (R := ℂ) (X := X))
        = TopologicalSpace.generateFrom
            (AlgebraicGeometry.Point.analyticSubbasis (R := ℂ) (X := X)) from
      AlgebraicGeometry.Point.analyticTopology_eq_generateFrom,
    induced_generateFrom_eq]
  apply le_antisymm
  · apply le_generateFrom
    rintro _ ⟨W, ⟨U, s, V, hV, rfl⟩, rfl⟩
    have hset : (cptEquiv X) ⁻¹'
        (AlgebraicGeometry.Point.overOpen U ∩ AlgebraicGeometry.Point.evaluate U s ⁻¹' V)
        = ⋃ (p : ℂ × ℝ) (_ : Metric.ball p.1 p.2 ⊆ V),
            {P : CPt X | XPtIn X P U ∧ ‖XevalAt X U s P - p.1‖ < p.2} := by
      ext P
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq,
        AlgebraicGeometry.Point.overOpen]
      constructor
      · rintro ⟨hU, hVv⟩
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV _ hVv
        refine ⟨(AlgebraicGeometry.Point.evaluate U s (cptEquiv X P), ε), hball, ?_, ?_⟩
        · exact (ptIn_iff X P U).mpr hU
        · rw [xevalAt_eq_evaluate]; simpa using hε
      · rintro ⟨p, hball, hPU, hlt⟩
        refine ⟨(ptIn_iff X P U).mp hPU, hball ?_⟩
        rw [← xevalAt_eq_evaluate]
        simpa [Metric.mem_ball, Complex.dist_eq] using hlt
    rw [hset]
    let _ : TopologicalSpace (CPt X) := classicalTopology X
    refine isOpen_iUnion fun p => isOpen_iUnion fun _ => ?_
    exact isOpen_generateFrom_of_mem ⟨U, s, p.1, p.2, rfl⟩
  · apply le_generateFrom
    rintro _ ⟨U, f, z, ε, rfl⟩
    have hset : {P : CPt X | XPtIn X P U ∧ ‖XevalAt X U f P - z‖ < ε}
        = (cptEquiv X) ⁻¹' (AlgebraicGeometry.Point.overOpen U
            ∩ AlgebraicGeometry.Point.evaluate U f ⁻¹' Metric.ball z ε) := by
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff,
        AlgebraicGeometry.Point.overOpen, Metric.mem_ball, Complex.dist_eq]
      rw [xevalAt_eq_evaluate]
      exact and_congr_left fun _ => ptIn_iff X P U
    rw [hset]
    exact isOpen_generateFrom_of_mem
      ⟨_, ⟨U, f, Metric.ball z ε, Metric.isOpen_ball, rfl⟩, rfl⟩

/-! ## Transport to the kernel's carrier -/

attribute [local instance] CloudB3W17Hodge.classicalTopology

/-- The comparison is a homeomorphism when `CPt X` carries the kernel's classical topology. -/
def cptHomeomorph : CPt X ≃ₜ AlgebraicGeometry.Point ℂ X :=
  (cptEquiv X).toHomeomorphOfIsInducing ⟨classicalTopology_eq X⟩

/-- **The charted-space structure, transported to the kernel's carrier.** For `X` smooth of
relative dimension `d` over `ℂ`, the set `X(ℂ)` with its classical topology is charted on
`Fin d → ℂ`. -/
def chartedSpace (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ChartedSpace (Fin d → ℂ) (CPt X) :=
  Homeomorph.chartedSpace (cptHomeomorph X).symm

end

end CloudB3W17Hodge
