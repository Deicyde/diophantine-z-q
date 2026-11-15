import ZInQKernel.OneProof.H.TailW
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.RelativeCoordinates

/-!
# p1-quot, helper A: mcr-glue parts 5-6 and mcr-quot parts 1-11 over the chain

`scratch/mcr-quot/MCRQuot.lean` from its line 4406 on (mcr-glue parts 5-6, mcr-quot parts 1-24; everything before
that line is `scratch/mcr-glue/MCRGlue.lean`, which the chain holds as `TailL`..`TailW` in `namespace HDec`), verbatim
inside `namespace HDec`, except that `ImagePlane.*`, `curveFacts`, `smoothStalkDimOne` and one `transportLevel` are
written with the prefix `_root_.LeafQM.AV.Pin.` (inside `namespace HDec` the unqualified names resolve to the chain's
aliases or are ambiguous). Split in two files at mcr-quot's part 12 (size). docs/research/p1-quot.md. -/


namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-glue, part 5: a sanity check of `IsGQuotient`, and a split of glue C
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue

/-- **Sanity check: `IsGQuotient` is satisfiable** — the identity is the quotient by the trivial
group (so the definition used by Leaves L2, L3 is not vacuous or contradictory in this case). -/
theorem isGQuotient_bot_id (X : Scheme.{0}) : IsGQuotient (⊥ : Subgroup (Aut X)) (𝟙 X) := by
  have hinv : ∀ g ∈ (⊥ : Subgroup (Aut X)), g.asIso.hom ≫ 𝟙 X = 𝟙 X := by
    intro g hg
    rw [Subgroup.mem_bot] at hg
    subst hg
    rfl
  refine ⟨hinv, inferInstance, fun W _ => ⟨fun a b h => h, ?_⟩⟩
  ext s
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, rfl⟩ g hg
    rw [Subgroup.mem_bot] at hg
    subst hg
    show (X.presheaf.map (𝟙 (Opposite.op W))) t = t
    rw [CategoryTheory.Functor.map_id]
    rfl
  · intro _
    exact ⟨s, rfl⟩

/-- **Glue (C1), from Leaves L5 and L6: the CM sections of the quotient are disjoint.** For the
quotient `q : 𝒴 → 𝒵` by `fibreAut` and two `ℚ̄`-points of `𝒴` with CM by two different ones of
`ℤ[i], ℤ[ζ₃], ℤ[√−6]`, the closures in `𝒵` of their images are disjoint. (Outline in
`CoordinateNormalization`: a common point of the closures lifts to a point `w` of `𝒴` in the
closures of `y` and `g y'`; the inertia group at `w` contains the stabilizers of `y` and `g y'`
(even orders 4, 6, 2) and is cyclic (L6), so its involution fixes `y` and `g y'`, whose closures
are then disjoint by L5.) -/
def CMSectionsDisjoint : Prop :=
  TameFixedPointsDisjoint → TameInertiaCyclic →
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
      IsGQuotient (fibreAut 𝒴 𝒜) q.left → IsFinite q.left →
    ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' →
      ((HasCM4 P.q ∧ HasCM3 P'.q) ∨ (HasCM4 P.q ∧ HasCM24 P'.q) ∨ (HasCM3 P.q ∧ HasCM24 P'.q)) →
      Disjoint (closure ({q.left (qbarPoint y)} : Set 𝒵.left)) (closure {q.left (qbarPoint y')})

/-- **Glue (C2): the coordinate from three disjoint sections** (geometry of `P¹_{ℤ_(p)}` and the
generic-fibre comparison; no new literature). Given the quotient `q : 𝒴 → 𝒵` by `fibreAut`, with
`𝒵` proper smooth, an isomorphism `ρ'₀ : 𝒵 ≅ P¹_{ℤ_(p)}`, and the CM sections pairwise disjoint (the
conclusion of C1), there is an isomorphism `ρ' : 𝒵 ≅ P¹_{ℤ_(p)}` with `CoordFibres` for `ρ' ∘ q`.
(Outline: `ρ'₀ = m ∘ π̄` on the generic fibre for a Möbius `m` (Glue B: both are isomorphisms
`𝒵_ℚ ≅ P¹_ℚ`); `m(0), m(∞), m(−16/27)` have pairwise distinct reductions, so `m ∈ PGL₂(ℤ_(p))`;
`ρ' := m⁻¹ ∘ ρ'₀`; `CoordFibres` from R2fp through `𝒴_ℚ ≅ Y`.) -/
def CoordinateFromSections : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
      IsGQuotient (fibreAut 𝒴 𝒜) q.left → IsFinite q.left →
      IsProper 𝒵.hom → SmoothOfRelativeDimension 1 𝒵.hom →
    (∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' →
      ((HasCM4 P.q ∧ HasCM3 P'.q) ∨ (HasCM4 P.q ∧ HasCM24 P'.q) ∨ (HasCM3 P.q ∧ HasCM24 P'.q)) →
      Disjoint (closure ({q.left (qbarPoint y)} : Set 𝒵.left)) (closure {q.left (qbarPoint y')})) →
    ∀ ρ'₀ : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ'₀ →
    ∃ ρ' : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ' ∧ CoordFibres 𝒴 𝒜 (ρ'.comp q.left)

/-- **`CoordinateNormalization` from C1 and C2** (compiled plumbing). -/
theorem coordinateNormalization_of (h1 : CMSectionsDisjoint) (h2 : CoordinateFromSections) :
    CoordinateNormalization := by
  intro hFix hCyc p _ hp 𝒴 𝒜 hM hCM Y Φ π h1' hh h2' 𝒵 q hq hqf hZp hZs ρ'₀ hρ'₀
  exact h2 p hp 𝒴 𝒜 hM hCM Y Φ π h1' hh h2' 𝒵 q hq hqf hZp hZs
    (h1 hFix hCyc p hp 𝒴 𝒜 hM hCM Y Φ π h1' hh h2' 𝒵 q hq hqf) ρ'₀ hρ'₀

/-- **`ModelCoordinateResidue` from the leaves L1-L6 and the glue A, B, C1, C2** (compiled). -/
theorem modelCoordinateResidue_of_leaves'' (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (gA : FibreAutTame) (gB : GenericQuotientP1)
    (gC1 : CMSectionsDisjoint) (gC2 : CoordinateFromSections) : ModelCoordinateResidue :=
  modelCoordinateResidue_of_leaves' hAF hQE hTS hP1 hFix hCyc gA gB
    (coordinateNormalization_of gC1 gC2)

end MCRGlue


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-glue, part 6: sanity check — `fibreAut` contains the Hecke automorphisms
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue

/-- An isomorphism of level-3 objects is an isomorphism of their QM pairs. -/
def qmIsoOfIso {K : Type} [Field K] {P Q : QML3 K} (f : P.Iso Q) : QMIso P.q Q.q where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant := f.equivariant

/-- The automorphism of `𝒴.left` underlying an automorphism of `𝒴` over `ℤ_(p)`. -/
def autOfOverIso {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    (g : 𝒴 ≅ 𝒴) : Aut 𝒴.left :=
  Aut.of ((Over.forget _).mapIso g)

/-- **Sanity check: `fibreAut` contains automorphisms inducing every Hecke operation** (`twist α`
and `rightMul u`, clauses 6-7 of `IsShimuraModel`), so the quotient by `fibreAut` is at least as
coarse as the quotient by `Γ'`. -/
theorem hecke_mem_fibreAut {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜) :
    (∀ α : LeafQM.O ≃+* LeafQM.O, ∃ g ∈ fibreAut 𝒴 𝒜,
      ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
        IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.asIso.hom) P' →
          M3.mk P' = M3.twist α (M3.mk P)) ∧
    (∀ u : (LeafQM.O)ˣ, ∃ g ∈ fibreAut 𝒴 𝒜,
      ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
        IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.asIso.hom) P' →
          M3.mk P' = M3.rightMul u (M3.mk P)) := by
  obtain ⟨-, -, -, -, -, htw, hru, -⟩ := hM
  constructor
  · intro α
    obtain ⟨g, hg⟩ := htw α
    refine ⟨autOfOverIso g, Subgroup.subset_closure ⟨Over.w g.hom, fun y P P' h1 h2 => ?_⟩, hg⟩
    have h : M3.mk P' = M3.mk (P.twist α) := by rw [← M3.twist_mk]; exact hg y P P' h1 h2
    obtain ⟨f⟩ := Quotient.exact (s := isoSetoid Qbar) h
    exact ⟨α, ⟨(qmIsoOfIso f).symm⟩⟩
  · intro u
    obtain ⟨g, hg⟩ := hru u
    refine ⟨autOfOverIso g, Subgroup.subset_closure ⟨Over.w g.hom, fun y P P' h1 h2 => ?_⟩, hg⟩
    have h : M3.mk P' = M3.mk (P.rightMul u) := hg y P P' h1 h2
    obtain ⟨f⟩ := Quotient.exact (s := isoSetoid Qbar) h
    let e : QMIso P.q P'.q := (qmIsoOfIso f).symm
    let e' : QMIso (P.q.twist (RingEquiv.refl LeafQM.O)) P'.q :=
      { φ := e.φ
        ψ := e.ψ
        left := e.left
        right := e.right
        equivariant := e.equivariant }
    exact ⟨RingEquiv.refl _, ⟨e'⟩⟩

end MCRGlue


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 1: `𝒪^× ↠ (𝒪/3𝒪)^×` and the transitivity of the Hecke automorphisms on twist
classes
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue

/-! ## Units of `𝒪` modulo 3 (a finite computation) -/

/-- The reduced norm of `ofInt n` (an integer form). -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [nrdZ, mulCoord]
  ring

/-- **The unit table** (computed by `py/units.py`): every class of `(ℤ/3)⁴` of nonzero norm mod 3
contains a unit `ofInt n` of `𝒪` (inverse `ofInt m`). -/
theorem unit_table : ∀ a b c d : ZMod 3,
    a ^ 2 + a * c + c ^ 2 - 2 * b ^ 2 - 2 * b * d - 2 * d ^ 2 ≠ 0 →
    ∃ n m : Fin 4 → ℤ, mulCoord n m = ![1, 0, 0, 0] ∧ mulCoord m n = ![1, 0, 0, 0] ∧
      ((n 0 : ℤ) : ZMod 3) = a ∧ ((n 1 : ℤ) : ZMod 3) = b ∧ ((n 2 : ℤ) : ZMod 3) = c ∧
      ((n 3 : ℤ) : ZMod 3) = d := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-3, 0, 0, -2], ![-3, 0, 0, 2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 0, 0, 2], ![-3, 0, 0, -2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, 0], ![1, 0, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, 1], ![-1, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, -1], ![-1, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, 0], ![-1, 0, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, 1], ![1, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, -1], ![1, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, -2, 0, 0], ![-3, 2, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-3, -2, 0, 2], ![-3, 2, 0, -2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, 1, 0], ![-1, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 1, 1, 1], ![-2, -1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, 1, -1], ![-1, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, -1, 0], ![1, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![3, 1, -1, 1], ![2, -1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, -1, -1], ![1, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 2, 0, 0], ![-3, -2, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 2, 0, -2], ![-3, -2, 0, 2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![0, -1, 1, 0], ![-1, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, 1, 1], ![-1, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, -1, 1, -1], ![-2, 1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, -1, 0], ![1, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, -1, 1], ![1, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![3, -1, -1, -1], ![2, 1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, 0], ![1, 0, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, 1], ![-1, 0, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, -1], ![-1, 0, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, 0, 1, 1], ![2, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 1, -1], ![2, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, 0], ![0, 0, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, 1], ![0, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, -1], ![0, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 0, 0], ![-1, 1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -3, 1], ![-2, -1, 3, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 0, -1], ![-1, 1, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 1, 0], ![2, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, 1, 1, -1], ![2, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -1, 0], ![0, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-2, 1, -1, 1], ![-3, -1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -1, -1], ![0, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 0, 0], ![-1, -1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 0, 1], ![-1, -1, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, -3, -1], ![-2, 1, 3, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 1, 0], ![2, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 1, 1], ![2, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, -1, -1, 0], ![0, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, -1, 1], ![0, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-2, -1, -1, -1], ![-3, 1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, 0], ![-1, 0, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, 1], ![1, 0, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, -1], ![1, 0, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, 0], ![0, 0, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, 1], ![0, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, -1], ![0, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-1, 0, -1, 1], ![-2, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, -1, -1], ![-2, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 0, 0], ![1, 1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 3, 1], ![2, -1, -3, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 0, -1], ![1, 1, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 1, 0], ![0, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, -2, 1], ![-3, -1, 2, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 1, -1], ![0, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, -1, 0], ![-2, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-1, 1, -1, -1], ![-2, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 0, 0], ![1, -1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 0, 1], ![1, -1, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 3, -1], ![2, 1, -3, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 1, 0], ![0, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 1, 1], ![0, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -2, -1], ![-3, 1, 2, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -1, 0], ![-2, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -1, 1], ![-2, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim

theorem nrdZ_mod3 (nc : Fin 4 → ℤ) :
    ((nrdZ (fun i => (![1, 0, 0, 0] : Fin 4 → ℤ) i + 3 * nc i) : ℤ) : ZMod 3) = 1 := by
  have h3 : (3 : ZMod 3) = 0 := rfl
  simp [nrdZ, h3]

/-- **`𝒪^× ↠ (𝒪/3𝒪)^×`**: an element of `𝒪` invertible modulo `3𝒪` is congruent modulo `3𝒪` to a
unit of `𝒪` (the unit table). -/
theorem exists_unit_congr (u₀ v₀ : O) (h : ∃ c : O, v₀ * u₀ - 1 = 3 * c) :
    ∃ u : Oˣ, ∃ c : O, (u : O) - u₀ = 3 * c := by
  obtain ⟨nu, hnu⟩ := u₀.2
  obtain ⟨nv, hnv⟩ := v₀.2
  obtain ⟨c, hc⟩ := h
  obtain ⟨nc, hnc⟩ := c.2
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  have hcB : (v₀ : B) * u₀ - 1 = 3 * c := by
    have := congrArg Subtype.val hc
    simpa [h33] using this
  have key : mulCoord nv nu = fun i => (![1, 0, 0, 0] : Fin 4 → ℤ) i + 3 * nc i := by
    have e : ofInt (mulCoord nv nu) - ofInt ![1, 0, 0, 0] = ofInt (fun i => 3 * nc i) := by
      rw [← ofInt_mul, ofInt_one, ← AV.three_mul_ofInt, ← hnu, ← hnv, ← hnc, hcB]
    rw [AV.ofInt_sub] at e
    have e2 := AV.ofInt_injective e
    funext i
    have := congrFun e2 i
    simp only [Pi.sub_apply] at this
    omega
  have hN : ((nrdZ nu : ℤ) : ZMod 3) ≠ 0 := by
    intro h0
    have e := nrdZ_mul nv nu
    rw [key] at e
    have e3 := congrArg (fun z : ℤ => (z : ZMod 3)) e
    simp only [nrdZ_mod3, Int.cast_mul, h0, mul_zero] at e3
    exact one_ne_zero e3
  have hN' : ((nu 0 : ℤ) : ZMod 3) ^ 2 + (nu 0 : ZMod 3) * (nu 2 : ZMod 3) +
      (nu 2 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) * (nu 3 : ZMod 3) -
      2 * (nu 3 : ZMod 3) ^ 2 ≠ 0 := by
    have : ((nrdZ nu : ℤ) : ZMod 3) = ((nu 0 : ℤ) : ZMod 3) ^ 2 + (nu 0 : ZMod 3) * (nu 2 : ZMod 3) +
      (nu 2 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) * (nu 3 : ZMod 3) -
      2 * (nu 3 : ZMod 3) ^ 2 := by simp [nrdZ]
    rwa [← this]
  obtain ⟨n, m, hnm, hmn, h0, h1, h2, h3⟩ := unit_table _ _ _ _ hN'
  have hdiv : ∀ i, (3 : ℤ) ∣ n i - nu i := by
    intro i
    have hi : ((nu i : ℤ) : ZMod 3) = ((n i : ℤ) : ZMod 3) := by
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · exact h2.symm
      · exact h3.symm
    exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).1 hi
  choose k hk using hdiv
  let u : Oˣ :=
    { val := ⟨ofInt n, ⟨n, rfl⟩⟩
      inv := ⟨ofInt m, ⟨m, rfl⟩⟩
      val_inv := by
        apply Subtype.ext
        change ofInt n * ofInt m = 1
        rw [ofInt_mul, hnm, ofInt_one]
      inv_val := by
        apply Subtype.ext
        change ofInt m * ofInt n = 1
        rw [ofInt_mul, hmn, ofInt_one] }
  refine ⟨u, ⟨ofInt k, ⟨k, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change ofInt n - (u₀ : B) = ((3 : O) : B) * ofInt k
  rw [hnu, h33, AV.ofInt_sub, AV.three_mul_ofInt]
  congr 1
  funext i
  simp [hk i]

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 2: twist classes are the `fibreAut`-orbits on `ℚ̄`-points
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

variable {K : Type} [Field K]

/-- Twist-equivalence of level-3 objects: their QM pairs are `Aut(𝒪)`-twists of each other (the
relation of `CoordFibres`). -/
def TwistEq (P P' : QML3 K) : Prop := ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) P'.q)

/-- A QM isomorphism `ι ∘ γ ≅ ι` when `γ` is the identity pointwise. -/
def twistIdIso {A : AbVar K} (q : QMStr A) (γ : O ≃+* O) (hγ : ∀ a, γ a = a) :
    QMIso (q.twist γ) q where
  φ := 1
  ψ := 1
  left := (QMIso.refl q).left
  right := (QMIso.refl q).right
  equivariant a := by
    change (q.iota (γ a)).hom ≫ _ = _ ≫ (q.iota a).hom
    rw [hγ a]
    exact (QMIso.refl q).equivariant a

/-- Twisting a QM isomorphism. -/
def twistIso {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q') (β : O ≃+* O) :
    QMIso (q.twist β) (q'.twist β) where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant a := f.equivariant (β a)

/-- `(ι ∘ α) ∘ β = ι ∘ (α ∘ β)`. -/
def twistTwistIso {A : AbVar K} (q : QMStr A) (α β : O ≃+* O) :
    QMIso (q.twist (β.trans α)) ((q.twist α).twist β) where
  φ := 1
  ψ := 1
  left := (QMIso.refl q).left
  right := (QMIso.refl q).right
  equivariant a := (QMIso.refl ((q.twist α).twist β)).equivariant a

theorem twistEq_of_qmIso {P P' : QML3 K} (f : QMIso P.q P'.q) : TwistEq P P' :=
  ⟨RingEquiv.refl O, ⟨(twistIdIso P.q _ fun _ => rfl).trans f⟩⟩

theorem twistEq_of_iso {P P' : QML3 K} (f : P.Iso P') : TwistEq P P' :=
  twistEq_of_qmIso (qmIsoOfIso f)

theorem TwistEq.trans' {P R S : QML3 K} (h1 : TwistEq P R) (h2 : TwistEq R S) : TwistEq P S := by
  obtain ⟨α, ⟨f⟩⟩ := h1
  obtain ⟨β, ⟨g⟩⟩ := h2
  exact ⟨β.trans α, ⟨((twistTwistIso P.q α β).trans (twistIso f β)).trans g⟩⟩

theorem TwistEq.symm' {P R : QML3 K} (h : TwistEq P R) : TwistEq R P := by
  obtain ⟨α, ⟨f⟩⟩ := h
  refine ⟨α.symm, ⟨(twistIso f.symm α.symm).trans ?_⟩⟩
  exact ((twistTwistIso P.q α α.symm).symm).trans
    (twistIdIso P.q _ fun a => RingEquiv.apply_symm_apply α a)

/-- **Orbits lie in twist classes**: if fibres at a `ℚ̄`-point are unique up to isomorphism, every
element of `fibreAut` moves a point within its twist class. -/
theorem twistEq_of_mem_fibreAut {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜)
    (huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P')
    {h : Aut 𝒴.left} (hh : h ∈ fibreAut 𝒴 𝒜) :
    ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ h.asIso.hom) P' → TwistEq P P' := by
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one =>
    intro y P P' hP hP'
    have hP'' : IsFibreOf 𝒜 y P' := by simpa using hP'
    obtain ⟨f⟩ := Quotient.exact (s := isoSetoid Qbar) (huniq y P P' hP hP'')
    exact twistEq_of_iso f
  | mul x z _ _ hx hz =>
    intro y P P' hP hP'
    obtain ⟨R, hR⟩ := hM.2.2.1 Qbar (y ≫ z.asIso.hom)
    have hP2 : IsFibreOf 𝒜 ((y ≫ z.asIso.hom) ≫ x.asIso.hom) P' := by
      simpa [Category.assoc] using hP'
    exact (hz y P R hP hR).trans' (hx _ R P' hR hP2)
  | inv x _ hx =>
    intro y P P' hP hP'
    have hP2 : IsFibreOf 𝒜 ((y ≫ x⁻¹.asIso.hom) ≫ x.asIso.hom) P := by
      simpa [Category.assoc] using hP
    exact (hx _ P' P hP' hP2).symm'

/-- **Twist classes lie in orbits** (from the Hecke clauses of `IsShimuraModel`, the level torsor
`Level3.torsor` (needs the kernel's textbook leaf `TorsionStructure`, T5) and
`𝒪^× ↠ (𝒪/3𝒪)^×` (`exists_unit_congr`, proved)). -/
theorem mem_orbit_of_twistEq (hT : ObjBridge.TorsionStructure) {p : ℕ} [Fact p.Prime]
    {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))} {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜)
    (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar)
    (hP : IsFibreOf 𝒜 y P) (hP' : IsFibreOf 𝒜 y' P') (hTE : TwistEq P P') :
    ∃ h ∈ fibreAut 𝒴 𝒜, y' = y ≫ h.asIso.hom := by
  obtain ⟨α, ⟨f⟩⟩ := hTE
  obtain ⟨htw, hru⟩ := hecke_mem_fibreAut hM
  obtain ⟨g1, hg1G, hg1⟩ := htw α
  obtain ⟨P1, hP1⟩ := hM.2.2.1 Qbar (y ≫ g1.asIso.hom)
  have e1 : M3.mk P1 = M3.mk (P.twist α) := by rw [← M3.twist_mk]; exact hg1 y P P1 hP hP1
  obtain ⟨i1⟩ := Quotient.exact (s := isoSetoid Qbar) e1
  let f1 : QMIso P1.q P'.q := (qmIsoOfIso i1).trans f
  let e' : Level3 P1.q := _root_.LeafQM.AV.Pin.transportLevel f1.symm P'.e
  have hiso : P'.Iso ⟨P1.A, P1.surface, P1.q, e'⟩ := QML3.isoTransport P' P1.surface f1.symm
  obtain ⟨u₀, v₀, hvu, hlin⟩ := Level3.torsor hT P1 e'
  obtain ⟨u, c, hc⟩ := exists_unit_congr u₀ v₀ hvu
  have heq : P1.rightMul u = ⟨P1.A, P1.surface, P1.q, e'⟩ := by
    simp only [QML3.rightMul, QML3.mk.injEq, heq_eq_eq, true_and]
    apply Level3.ext'
    refine DFunLike.ext _ _ fun a => ?_
    change P1.e.eta (a * u) = e'.eta a
    rw [hlin a, P1.e.eq_iff]
    refine ⟨a * c, ?_⟩
    calc a * (u : O) - a * u₀ = a * ((u : O) - u₀) := by noncomm_ring
      _ = a * (3 * c) := by rw [hc]
      _ = 3 * (a * c) := by noncomm_ring
  obtain ⟨g2, hg2G, hg2⟩ := hru u
  obtain ⟨P2, hP2⟩ := hM.2.2.1 Qbar ((y ≫ g1.asIso.hom) ≫ g2.asIso.hom)
  have e2 : M3.mk P2 = M3.mk P' := by
    rw [hg2 _ P1 P2 hP1 hP2]
    change M3.mk (P1.rightMul u) = M3.mk P'
    rw [heq]
    exact Quotient.sound ⟨hiso.symm⟩
  have hy := hM.2.2.2.1 _ y' P2 P' hP2 hP' e2
  refine ⟨g2 * g1, Subgroup.mul_mem _ hg2G hg1G, ?_⟩
  rw [← hy]
  simp [Category.assoc]

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 3: `ℚ̄`-points of a quotient by a finite group are the orbits

Commutative algebra (`exists_comp_smul_eq`: two ring maps `B → K` to a field that agree on
`A = B^G` differ by an element of `G`; from Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`
and `Ideal.Quotient.stabilizerHom_surjective`), then the scheme version for the SGA 1 quotient
`IsGQuotient`: the action of `G` on the sections over `q⁻¹ W`, `W ⊆ Z` affine, is a
`MulSemiringAction` with invariants `Γ(Z, W)`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits MCRGlue

/-- Values of two ring maps agreeing on invariants differ by an element of the group. -/
theorem exists_root_smul {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field K]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G] (χ χ' : B →+* K)
    (hχ : χ.comp (algebraMap A B) = χ'.comp (algebraMap A B)) (b : B) :
    ∃ k : G, χ' b = χ (k • b) := by
  obtain ⟨P, hP0⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G b
  have hP : P.map (algebraMap A B) = MulSemiringAction.charpoly G b := hP0
  have h1 : P.eval₂ (χ'.comp (algebraMap A B)) (χ' b) = 0 := by
    rw [← Polynomial.hom_eval₂, ← Polynomial.eval_map, hP, MulSemiringAction.eval_charpoly,
      map_zero]
  rw [← hχ, ← Polynomial.eval_map, ← Polynomial.map_map, hP, MulSemiringAction.charpoly_eq,
    Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
  obtain ⟨k, -, hk⟩ := h1
  refine ⟨k, ?_⟩
  simpa [sub_eq_zero] using hk

theorem exists_comp_smul_eq {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field K]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] (φ φ' : B →+* K)
    (h : φ.comp (algebraMap A B) = φ'.comp (algebraMap A B)) :
    ∃ g : G, ∀ b, φ' b = φ (g • b) := by
  classical
  cases nonempty_fintype G
  set Q := RingHom.ker φ with hQdef
  set Q' := RingHom.ker φ' with hQ'def
  have : Q.IsPrime := RingHom.ker_isPrime φ
  have : Q'.IsPrime := RingHom.ker_isPrime φ'
  have hunder : Q.under A = Q'.under A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, Q, Q', RingHom.mem_ker]
    rw [← RingHom.comp_apply, h, RingHom.comp_apply]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G Q Q' hunder
  let ψ : B →+* K := φ'.comp (MulSemiringAction.toRingHom G B g)
  have hψ : ∀ b, ψ b = φ' (g • b) := fun _ => rfl
  have hkerψ : ∀ b, ψ b = 0 ↔ φ b = 0 := by
    intro b
    rw [hψ]
    change g • b ∈ Q' ↔ b ∈ Q
    rw [hg, Ideal.smul_mem_pointwise_smul_iff]
  have hψA : ψ.comp (algebraMap A B) = φ.comp (algebraMap A B) := by
    ext a
    change φ' (g • algebraMap A B a) = φ (algebraMap A B a)
    rw [smul_algebraMap]
    exact (congrArg (fun f : A →+* K => f a) h).symm
  set P := Q.under A
  have : Q.LiesOver P := ⟨rfl⟩
  let φb : B ⧸ Q →+* K := Ideal.Quotient.lift Q φ (fun b hb => hb)
  let ψb : B ⧸ Q →+* K := Ideal.Quotient.lift Q ψ (fun b hb => (hkerψ b).2 hb)
  have hφb : Function.Injective φb :=
    RingHom.lift_injective_of_ker_le_ideal _ _ (fun b hb => hb)
  have hψb : Function.Injective ψb :=
    RingHom.lift_injective_of_ker_le_ideal _ _ (fun b hb => (hkerψ b).1 hb)
  have hrange1 : ∀ x : B ⧸ Q, ∃ y : B ⧸ Q, ψb x = φb y := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨k, hk⟩ := exists_root_smul G φ ψ hψA.symm b
    exact ⟨Ideal.Quotient.mk Q (k • b), hk⟩
  have hrange2 : ∀ y : B ⧸ Q, ∃ x : B ⧸ Q, φb y = ψb x := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨k, hk⟩ := exists_root_smul G ψ φ hψA b
    exact ⟨Ideal.Quotient.mk Q (k • b), hk⟩
  choose τf hτf using hrange1
  choose τi hτi using hrange2
  have hτ1 : ∀ x, τi (τf x) = x := fun x => hψb (by rw [← hτi, ← hτf])
  have hτ2 : ∀ y, τf (τi y) = y := fun y => hφb (by rw [← hτf, ← hτi])
  let τ : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) :=
    { toFun := τf
      invFun := τi
      left_inv := hτ1
      right_inv := hτ2
      map_mul' := fun x y => hφb (by rw [map_mul, ← hτf, ← hτf, ← hτf, map_mul])
      map_add' := fun x y => hφb (by rw [map_add, ← hτf, ← hτf, ← hτf, map_add])
      commutes' := by
        intro r
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        apply hφb
        rw [← hτf]
        change ψ (algebraMap A B a) = φ (algebraMap A B a)
        exact congrArg (fun f : A →+* K => f a) hψA }
  obtain ⟨s, hs⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q τ
  have key : ∀ b, φ' (g • b) = φ ((s : G) • b) := by
    intro b
    have e1 : τ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q ((s : G) • b) := by
      rw [← hs]
      rfl
    have e2 := hτf (Ideal.Quotient.mk Q b)
    change ψ b = φb (τ (Ideal.Quotient.mk Q b)) at e2
    rw [e1] at e2
    exact e2
  refine ⟨(s : G) * g⁻¹, fun b => ?_⟩
  have := key (g⁻¹ • b)
  rwa [smul_inv_smul, ← mul_smul] at this

section GQuot

variable {X Z : Scheme.{0}} {q : X ⟶ Z}

/-- The ring map on sections over `q⁻¹ W` induced by `f : X → X` with `f ≫ q = q`. -/
def secMap (f : X ⟶ X) (hf : f ≫ q = q) (W : Z.Opens) : Γ(X, q ⁻¹ᵁ W) →+* Γ(X, q ⁻¹ᵁ W) :=
  (f.appLE (q ⁻¹ᵁ W) (q ⁻¹ᵁ W) (preimage_le_of_comp_eq hf W)).hom

theorem appLE_congr' {X' Y' : Scheme.{0}} {f f' : X' ⟶ Y'} (h : f = f') (U : Y'.Opens)
    (V : X'.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h; rfl

theorem secMap_congr {f f' : X ⟶ X} (h : f = f') (hf : f ≫ q = q) (hf' : f' ≫ q = q)
    (W : Z.Opens) : secMap f hf W = secMap f' hf' W := by
  subst h; rfl

theorem secMap_id (h : 𝟙 X ≫ q = q) (W : Z.Opens) : secMap (𝟙 X) h W = RingHom.id _ := by
  ext b
  simp only [secMap, Scheme.Hom.appLE, Scheme.Hom.id_app]
  show (CommRingCat.Hom.hom (𝟙 _ ≫ X.presheaf.map (𝟙 (Opposite.op (q ⁻¹ᵁ W))))) b = b
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem secMap_comp (f f' : X ⟶ X) (hf : f ≫ q = q) (hf' : f' ≫ q = q) (h : (f ≫ f') ≫ q = q)
    (W : Z.Opens) : secMap (f ≫ f') h W = (secMap f hf W).comp (secMap f' hf' W) := by
  unfold secMap
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

/-- `f^*` fixes the pulled-back sections of `Z` when `f ≫ q = q`. -/
theorem secMap_app (f : X ⟶ X) (hf : f ≫ q = q) (W : Z.Opens) (a : Γ(Z, W)) :
    secMap f hf W (q.app W a) = q.app W a := by
  have key : q.app W ≫ f.appLE (q ⁻¹ᵁ W) (q ⁻¹ᵁ W) (preimage_le_of_comp_eq hf W) = q.app W := by
    conv_lhs => rw [Scheme.Hom.app_eq_appLE]
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr' hf W (q ⁻¹ᵁ W) _ le_rfl,
      ← Scheme.Hom.app_eq_appLE]
  exact congrArg (fun φ => φ.hom a) key

theorem inv_comp_eq {g : Aut X} (hg : g.asIso.hom ≫ q = q) : g.asIso.inv ≫ q = q := by
  conv_lhs => rw [← hg]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable {G : Subgroup (Aut X)}

/-- The action of `G` on `Γ(X, q⁻¹ W)`: `g • s = (g⁻¹)^* s`. -/
def secAction (hinv : ∀ g ∈ G, g.asIso.hom ≫ q = q) (W : Z.Opens) :
    MulSemiringAction G Γ(X, q ⁻¹ᵁ W) where
  smul g b := secMap (g : Aut X).asIso.inv (inv_comp_eq (hinv g g.2)) W b
  one_smul b := by
    change secMap _ _ W b = b
    rw [secMap_congr (f' := 𝟙 X) (by simp) _ (Category.id_comp q), secMap_id]
    rfl
  mul_smul x y b := by
    change secMap _ _ W b = secMap _ _ W (secMap _ _ W b)
    rw [secMap_congr (f' := (x : Aut X).asIso.inv ≫ (y : Aut X).asIso.inv) (by simp) _
      (by rw [Category.assoc, inv_comp_eq (hinv y y.2), inv_comp_eq (hinv x x.2)]),
      secMap_comp _ _ (inv_comp_eq (hinv x x.2)) (inv_comp_eq (hinv y y.2))]
    rfl
  smul_zero g := map_zero _
  smul_add g a b := map_add _ a b
  smul_one g := map_one _
  smul_mul g a b := map_mul _ a b

/-- A `K`-point is determined by its map on the sections of an affine open containing it. -/
theorem eq_of_appLE_eq {K : Type} [Field K] (y y' : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (e : ⊤ ≤ y ⁻¹ᵁ U) (e' : ⊤ ≤ y' ⁻¹ᵁ U)
    (h : y.appLE U ⊤ e = y'.appLE U ⊤ e') : y = y' := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec y hU (isAffineOpen_top _) e
  have h2 := IsAffineOpen.SpecMap_appLE_fromSpec y' hU (isAffineOpen_top _) e'
  rw [h, h2, IsAffineOpen.fromSpec_top] at h1
  exact ((cancel_epi _).1 h1).symm

/-- **The `K`-points of an SGA 1 quotient by a finite group are the orbits.** If `q : X → Z` is the
quotient by a finite group `G` (`IsGQuotient`) and two `K`-points of `X` have the same image in
`Z`, they differ by an element of `G`. -/
theorem exists_eq_comp_of_isGQuotient [Finite G] (hq : IsGQuotient G q) {K : Type} [Field K]
    (y y' : Spec (CommRingCat.of K) ⟶ X) (h : y ≫ q = y' ≫ q) :
    ∃ g ∈ G, y' = y ≫ g.asIso.hom := by
  obtain ⟨hinv, haff, hsec⟩ := hq
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hxW, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q (y default))) isOpen_univ
  set U := q ⁻¹ᵁ W with hUdef
  have hU : IsAffineOpen U := hW.preimage q
  have ey : ⊤ ≤ y ⁻¹ᵁ U := by
    intro a _
    rw [Subsingleton.elim a default]
    exact hxW
  have ey' : ⊤ ≤ y' ⁻¹ᵁ U := by
    intro a _
    rw [Subsingleton.elim a default]
    change q (y' default) ∈ W
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
    exact hxW
  letI : MulSemiringAction G Γ(X, U) := secAction hinv W
  letI : Algebra Γ(Z, W) Γ(X, U) := (q.app W).hom.toAlgebra
  haveI : SMulCommClass G Γ(Z, W) Γ(X, U) := by
    constructor
    intro g a b
    change secMap _ _ W (q.app W a * b) = q.app W a * secMap _ _ W b
    rw [map_mul, secMap_app]
  haveI : Algebra.IsInvariant Γ(Z, W) Γ(X, U) G := by
    constructor
    intro b hb
    have hmem : b ∈ Set.range (q.app W) := by
      rw [(hsec W hW).2]
      intro g hg
      have := hb ⟨g⁻¹, G.inv_mem hg⟩
      change secMap _ _ W b = b at this
      rw [secMap_congr (f' := g.asIso.hom) (by simp) _ (hinv g hg)] at this
      exact this
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha⟩
  let φ : Γ(X, U) →+* K :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (y.appLE U ⊤ ey).hom
  let φ' : Γ(X, U) →+* K :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (y'.appLE U ⊤ ey').hom
  have hagree : φ.comp (algebraMap Γ(Z, W) Γ(X, U)) = φ'.comp (algebraMap Γ(Z, W) Γ(X, U)) := by
    ext a
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom (y.appLE U ⊤ ey (q.app W a)) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (y'.appLE U ⊤ ey' (q.app W a))
    have k1 : q.app W ≫ y.appLE U ⊤ ey = (y ≫ q).appLE W ⊤ (ey.trans le_rfl) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have k2 : q.app W ≫ y'.appLE U ⊤ ey' = (y' ≫ q).appLE W ⊤ (ey'.trans le_rfl) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have k3 : q.app W ≫ y.appLE U ⊤ ey = q.app W ≫ y'.appLE U ⊤ ey' := by
      rw [k1, k2]; exact appLE_congr' h _ _ _ _
    exact congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of K)).hom (φ.hom a)) k3
  obtain ⟨g, hg⟩ := exists_comp_smul_eq G φ φ' hagree
  refine ⟨(g : Aut X)⁻¹, G.inv_mem g.2, ?_⟩
  have key := Scheme.Hom.appLE_comp_appLE y (g : Aut X).asIso.inv U U ⊤
    (preimage_le_of_comp_eq (inv_comp_eq (hinv g g.2)) W) ey
  have hy' : y' = y ≫ (g : Aut X).asIso.inv := by
    refine eq_of_appLE_eq y' (y ≫ (g : Aut X).asIso.inv) hU ey' ?_ ?_
    · intro a _
      change q ((g : Aut X).asIso.inv (y a)) ∈ W
      rw [← Scheme.Hom.comp_apply, inv_comp_eq (hinv g g.2)]
      exact ey (show a ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
    rw [← key]
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
    ext b
    exact hg b
  rw [hy']
  simp

end GQuot

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 4: glue C2 `CoordinateFromSections` from T5, glue A and the P¹ glue
`P1ThreePoints`
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-! ## Values at field points through charts -/

section Charts

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem top_le_preimage_of_ptOf_mem (y : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens}
    (hx : ptOf y ∈ O) : ⊤ ≤ y ⁻¹ᵁ O := by
  intro a _
  rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]
  exact hx

/-- The value of a section at a field point, through `appLE`. -/
theorem ev_eq_appLE (y : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf y ∈ O)
    (s : Γ(X, O)) :
    ev y hx s = (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (y.appLE O ⊤ (top_le_preimage_of_ptOf_mem y hx) s) := by
  have e1 := _root_.LeafQM.AV.Pin.ImagePlane.ev_comp (𝟙 _) y (O := O) hx s
  have e2 := ev_res (𝟙 (Spec (CommRingCat.of K)))
    (top_le_preimage_of_ptOf_mem y hx) (show ptOf (𝟙 (Spec (CommRingCat.of K))) ∈ ⊤ from trivial)
    (y.app O s)
  have e3 := ev_top (𝟙 (Spec (CommRingCat.of K)))
    (res (top_le_preimage_of_ptOf_mem y hx) (y.app O s))
  simp only [Category.id_comp] at e1
  rw [e1, ← e2, e3]
  rfl

/-- **Chart injectivity**: on an affine open `W` whose sections are generated by `h` over
`ℤ_(p)`, a field point in `W` is determined by the value of `h`. -/
theorem eq_of_ev_eq_chart {p : ℕ} [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
    {W : 𝒵.left.Opens} (hW : IsAffineOpen W) (h : Γ(𝒵.left, W))
    (hs : Function.Surjective (eval₂RingHom (baseToSections 𝒵 W) h))
    (z z' : Spec (CommRingCat.of K) ⟶ 𝒵.left) (hz : ptOf z ∈ W) (hz' : ptOf z' ∈ W)
    (he : ev z hz h = ev z' hz' h) : z = z' := by
  have hring : ev z hz = ev z' hz' := by
    ext s
    obtain ⟨P, rfl⟩ := hs s
    simp only [coe_eval₂RingHom]
    rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂, he,
      zloc_ringHom_ext ((ev z hz).comp (baseToSections 𝒵 W))
        ((ev z' hz').comp (baseToSections 𝒵 W))]
  refine eq_of_appLE_eq z z' hW (top_le_preimage_of_ptOf_mem z hz)
    (top_le_preimage_of_ptOf_mem z' hz') ?_
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
  ext s
  have := congrArg (fun φ : Γ(𝒵.left, W) →+* K => φ s) hring
  simp only [ev_eq_appLE] at this
  exact this

/-- **An isomorphism onto `P¹` is injective on field points.** -/
theorem val_injective_of_isP1Coordinate {p : ℕ} [Fact p.Prime]
    {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left} (hρ : IsP1Coordinate 𝒵 ρ)
    (z z' : Spec (CommRingCat.of K) ⟶ 𝒵.left) (h : ρ.val z = ρ.val z') : z = z' := by
  obtain ⟨hU, hV, hbU, hbV⟩ := hρ
  by_cases hz : ptOf z ∈ ρ.U <;> by_cases hz' : ptOf z' ∈ ρ.U
  · rw [val_of_mem ρ z hz, val_of_mem ρ z' hz'] at h
    exact eq_of_ev_eq_chart 𝒵 hU ρ.f hbU.2 z z' hz hz' (OnePoint.coe_injective h)
  · rw [val_of_mem ρ z hz, val_of_not_mem ρ z' hz'] at h
    exact (OnePoint.coe_ne_infty _ h).elim
  · rw [val_of_not_mem ρ z hz, val_of_mem ρ z' hz'] at h
    exact (OnePoint.coe_ne_infty _ h.symm).elim
  · have hv := mem_V_of_not_mem_U ρ hz
    have hv' := mem_V_of_not_mem_U ρ hz'
    refine eq_of_ev_eq_chart 𝒵 hV ρ.g hbV.2 z z' hv hv' ?_
    rw [ev_g_eq_zero ρ z hv hz, ev_g_eq_zero ρ z' hv' hz']

end Charts

/-- A point of `P¹(ℚ̄)` fixed by `Gal(ℚ̄/ℚ)` is rational. -/
theorem exists_rat_of_fixed (v : OnePoint Qbar)
    (hv : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, v.map σ = v) :
    ∃ r : OnePoint ℚ, v = r.map (algebraMap ℚ Qbar) := by
  induction v using OnePoint.rec with
  | infty => exact ⟨OnePoint.infty, rfl⟩
  | coe x =>
    have hx : x ∈ Set.range (algebraMap ℚ Qbar) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro σ
      exact OnePoint.coe_injective (hv σ)
    obtain ⟨r, rfl⟩ := hx
    exact ⟨OnePoint.some r, rfl⟩

/-! ## The P¹ glue -/

/-- **Glue (C2-P¹): normalizing a coordinate of `P¹_{ℤ_(p)}` by three disjoint rational
sections** (geometry of `P¹` over the DVR `ℤ_(p)`; no literature). Let `ρ₀ : 𝒵 ≅ P¹_{ℤ_(p)}` (by
charts, `IsP1Coordinate`) and let `z₀, zi, z₁` be `ℚ̄`-points of `𝒵` whose `ρ₀`-values are rational,
`a, b, c ∈ P¹(ℚ)`, and whose underlying points have pairwise disjoint closures. Then some
`ρ : 𝒵 ≅ P¹_{ℤ_(p)}` takes the values `0, ∞, −16/27` at them. (Proof outline: the closure of the
point `t = a` of the generic fibre is the section `t = a`, which meets the special fibre in
`a mod p ∈ P¹(𝔽_p)`; so `a, b, c` have pairwise distinct reductions, and so do `0, ∞, −16/27`
(`p > 3`). Hence the Möbius map `m` with `m(a) = 0`, `m(b) = ∞`, `m(c) = −16/27` lies in
`PGL₂(ℤ_(p))` (`PGL₂(ℤ_(p)) → PGL₂(𝔽_p)` is onto and `PGL₂` is sharply 3-transitive), and
`ρ = m ∘ ρ₀` is again an isomorphism onto `P¹_{ℤ_(p)}`: it is a composite of translations
`t ↦ t + e` (`e ∈ ℤ_(p)`), scalings `t ↦ u t` (`u ∈ ℤ_(p)^×`) and the inversion `t ↦ 1/t`.) -/
def P1ThreePoints : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
    (ρ₀ : ToP1 𝒵.left), IsP1Coordinate 𝒵 ρ₀ →
    ∀ (z₀ zi z₁ : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (a b c : OnePoint ℚ),
      ρ₀.val z₀ = a.map (algebraMap ℚ Qbar) → ρ₀.val zi = b.map (algebraMap ℚ Qbar) →
      ρ₀.val z₁ = c.map (algebraMap ℚ Qbar) →
      Disjoint (closure ({qbarPoint z₀} : Set 𝒵.left)) (closure {qbarPoint zi}) →
      Disjoint (closure ({qbarPoint z₀} : Set 𝒵.left)) (closure {qbarPoint z₁}) →
      Disjoint (closure ({qbarPoint zi} : Set 𝒵.left)) (closure {qbarPoint z₁}) →
      ∃ ρ : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ ∧ ρ.val z₀ = OnePoint.some 0 ∧
        ρ.val zi = OnePoint.infty ∧ ρ.val z₁ = OnePoint.some (-16 / 27)

/-! ## The reduction of C2 -/

theorem map_neg_16_27 (σ : Qbar ≃ₐ[ℚ] Qbar) : σ (-16 / 27 : Qbar) = -16 / 27 := by
  rw [map_div₀, map_neg, map_ofNat, map_ofNat]

/-- **Glue C2 `CoordinateFromSections` from the textbook leaf `TorsionStructure` (T5), glue A
`FibreAutTame` (used only for the finiteness of `fibreAut`) and the P¹ glue `P1ThreePoints`.**
The `ρ₀ ∘ q`-fibres on `ℚ̄`-points are the `q`-fibres (`val_injective_of_isP1Coordinate`), which are
the `fibreAut`-orbits (`exists_eq_comp_of_isGQuotient`), which are the twist classes
(`twistEq_of_mem_fibreAut`, `mem_orbit_of_twistEq`). The CM points have Galois-fixed, hence
rational, `ρ₀ ∘ q`-values (their `π`-values `0, ∞, −16/27` are rational, R2fp, through the
comparison `exists_genFib_to_Y`), and the disjointness hypothesis lets `P1ThreePoints` move them to
`0, ∞, −16/27`. -/
theorem coordinateFromSections_of (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
    (hN : P1ThreePoints) : CoordinateFromSections := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf hZp hZs hdisj ρ₀ hρ₀
  obtain ⟨hfin, -⟩ := hA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  have hinvq := hq.1
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  have horb : ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' → (y ≫ q.left = y' ≫ q.left ↔ TwistEq P P') := by
    intro y y' P P' hP hP'
    constructor
    · intro e
      obtain ⟨h, hhG, rfl⟩ := exists_eq_comp_of_isGQuotient hq y y' e
      exact twistEq_of_mem_fibreAut hM huniq hhG y P P' hP hP'
    · intro hte
      obtain ⟨h, hhG, rfl⟩ := mem_orbit_of_twistEq hT hM y y' P P' hP hP' hte
      rw [Category.assoc, hinvq h hhG]
  have hR2 : ∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P → IsFibreOf 𝒜 (s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P' →
      (π.val (K := Qbar) (s ≫ g).left = π.val (K := Qbar) (s' ≫ g).left ↔ TwistEq P P') ∧
      (HasCM4 P.q → π.val (K := Qbar) (s ≫ g).left = OnePoint.some 0) ∧
      (HasCM3 P.q → π.val (K := Qbar) (s ≫ g).left = OnePoint.infty) ∧
      (HasCM24 P.q → π.val (K := Qbar) (s ≫ g).left = OnePoint.some (-16 / 27)) :=
    fun s s' P P' hP hP' => h2 (s ≫ g) (s' ≫ g) P P' (hg Qbar s P hP) (hg Qbar s' P' hP')
  -- two points of the same CM type have the same image in `𝒵`
  have hsameCM : ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' →
      ((HasCM4 P.q ∧ HasCM4 P'.q) ∨ (HasCM3 P.q ∧ HasCM3 P'.q) ∨
        (HasCM24 P.q ∧ HasCM24 P'.q)) → y ≫ q.left = y' ≫ q.left := by
    intro y y' P P' hP hP' hcm
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    obtain ⟨s', hs'⟩ := genFib_pt 𝒴 y'
    have hP2 : IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P :=
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP
    have hP2' : IsFibreOf 𝒜 (s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P' := 
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs').mpr hP'
    obtain ⟨hrel, c4, c3, c2⟩ := hR2 s s' P P' hP2 hP2'
    obtain ⟨-, c4', c3', c2'⟩ := hR2 s' s P' P hP2' hP2
    refine (horb y y' P P' hP hP').2 (hrel.1 ?_)
    rcases hcm with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · rw [c4 a, c4' b]
    · rw [c3 a, c3' b]
    · rw [c2 a, c2' b]
  -- Galois-fixed values at CM points
  have hfix : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P : QML3 Qbar), IsFibreOf 𝒜 y P →
      (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, (ρ₀.val (y ≫ q.left)).map σ = ρ₀.val (y ≫ q.left) := by
    intro y P hP hcm σ
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    have hP2 : IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P :=
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP
    set s' : fieldPt Qbar ⟶ genFib 𝒴 := fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ s with hs'def
    have hs'l : s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
        Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y := by
      rw [← hs]
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ _ = _
      exact Category.assoc _ _ _
    obtain ⟨P', hP'⟩ := hM.2.2.1 Qbar (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y)
    have hP2' : IsFibreOf 𝒜 (s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P' := 
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs'l).mpr hP'
    obtain ⟨hrel, c4, c3, c2⟩ := hR2 s s' P P' hP2 hP2'
    have hl : (s' ≫ g).left = Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ (s ≫ g).left := by
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ g.left = _
      exact Category.assoc _ _ _
    have hπ : π.val (K := Qbar) (s' ≫ g).left =
        (π.val (K := Qbar) (s ≫ g).left).map (σ : Qbar →+* Qbar) :=
      (congrArg (fun t => π.val (K := Qbar) t) hl).trans (ToP1.val_comp π _ _)
    have hval : π.val (K := Qbar) (s ≫ g).left = π.val (K := Qbar) (s' ≫ g).left := by
      rw [hπ]
      rcases hcm with a | a | a
      · rw [c4 a]; simp
      · rw [c3 a]; rfl
      · rw [c2 a]
        show OnePoint.some (-16 / 27 : Qbar) = OnePoint.some (σ (-16 / 27 : Qbar))
        rw [map_neg_16_27]
    have hq' := (horb y _ P P' hP hP').2 (hrel.1 hval)
    have e := ToP1.val_comp ρ₀ (σ : Qbar →+* Qbar) (y ≫ q.left)
    rw [← Category.assoc, ← hq'] at e
    exact e.symm
  -- the three CM points
  obtain ⟨⟨P4, c4⟩, ⟨P3, c3⟩, ⟨P2, c2⟩⟩ := hCM
  obtain ⟨y4, hy4⟩ := hM.2.2.2.2.1 P4
  obtain ⟨y3, hy3⟩ := hM.2.2.2.2.1 P3
  obtain ⟨y2, hy2⟩ := hM.2.2.2.2.1 P2
  obtain ⟨a, ha⟩ := exists_rat_of_fixed _ (hfix y4 P4 hy4 (Or.inl c4))
  obtain ⟨b, hb⟩ := exists_rat_of_fixed _ (hfix y3 P3 hy3 (Or.inr (Or.inl c3)))
  obtain ⟨c, hc⟩ := exists_rat_of_fixed _ (hfix y2 P2 hy2 (Or.inr (Or.inr c2)))
  have d43 := hdisj y4 y3 P4 P3 hy4 hy3 (Or.inl ⟨c4, c3⟩)
  have d42 := hdisj y4 y2 P4 P2 hy4 hy2 (Or.inr (Or.inl ⟨c4, c2⟩))
  have d32 := hdisj y3 y2 P3 P2 hy3 hy2 (Or.inr (Or.inr ⟨c3, c2⟩))
  obtain ⟨ρ, hρ, v4, v3, v2⟩ := hN p (by omega) 𝒵 ρ₀ hρ₀ (y4 ≫ q.left) (y3 ≫ q.left)
    (y2 ≫ q.left) a b c ha hb hc d43 d42 d32
  refine ⟨ρ, hρ, ?_⟩
  intro y y' P Q hP hQ
  rw [ToP1.val_comp_right, ToP1.val_comp_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Iff.trans ?_ (horb y y' P Q hP hQ)
    exact ⟨fun e => val_injective_of_isP1Coordinate hρ _ _ e, fun e => by rw [e]⟩
  · intro h4
    rw [hsameCM y y4 P P4 hP hy4 (Or.inl ⟨h4, c4⟩), v4]
  · intro h3
    rw [hsameCM y y3 P P3 hP hy3 (Or.inr (Or.inl ⟨h3, c3⟩)), v3]
  · intro h24
    rw [hsameCM y y2 P P2 hP hy2 (Or.inr (Or.inr ⟨h24, c2⟩)), v2]

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 5: glue A `FibreAutTame` from T5, a fixed-point glue and a twist-class count
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **Glue (A-fix): nontrivial elements of `fibreAut` fix only finitely many `ℚ̄`-points**
(scheme theory of curves; no literature). For the smooth model `𝒴` at `p > 324` and a triple with
R1fp, R1hecke, R2fp, every `h ≠ 1` in `fibreAut 𝒴 𝒜` fixes only finitely many `ℚ̄`-points.
(Outline: `𝒴` is integral (model-glue's `ModelIntegral`: `𝒴_ℚ ≅ Y` by `CurveBijIso`, `Y`
irreducible, `𝒴` reduced and flat); the fixed locus of `h` is the closed equalizer of `h` and
`id` (`𝒴` separated); infinitely many fixed `ℚ̄`-points lie over infinitely many closed points of
the irreducible curve `𝒴_ℚ`, so the equalizer contains the generic point, hence is all of the
integral `𝒴`, and `h = id`.) -/
def FibreAutFixFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ h ∈ fibreAut 𝒴 𝒜, h ≠ 1 →
      {y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | y ≫ h.asIso.hom = y}.Finite

/-- **Glue (A-count): a twist class has at most `324 = 4 · 81` isomorphism classes** (algebra of
`𝒪` and level structures; no new literature beyond T5). (Outline: by Skolem–Noether every
`α ∈ Aut 𝒪` is, up to conjugation by `𝒪^×` (which does not change the pair's class,
`conjUnitIso`), one of the at most four automorphisms induced by `1, i, j, ij` (`NormO.T`, the
Atkin–Lehner group), so a twist class contains at most 4 pair classes; on one pair the level
structures are `η₀(· u₀)` with `u₀` determined mod `3𝒪` (`Level3.torsor`, given T5), at most
`#(𝒪/3𝒪) = 81` of them (in fact 72). Proved below: `twistClassCard`.) -/
def TwistClassCard : Prop :=
  ∀ P : QML3 Qbar, {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧ TwistEq P Q}.Finite ∧
    {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧ TwistEq P Q}.ncard ≤ 324

/-- The smooth model has infinitely many `ℚ̄`-points (`CurveSurj` for `π ∘ g` on `𝒴_ℚ`). -/
theorem infinite_qbarPoints {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left} (h1 : R1fpProps Y Φ) :
    (Set.univ : Set (Spec (CommRingCat.of Qbar) ⟶ 𝒴.left)).Infinite := by
  intro hfin
  obtain ⟨g, -, -⟩ := exists_genFib_to_Y hM h1
  have hfin' : (Set.univ : Set (fieldPt Qbar ⟶ genFib 𝒴)).Finite := by
    refine Set.Finite.of_finite_image (f := fun s => s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p))
      (hfin.subset (Set.subset_univ _)) ?_
    intro s _ s' _ h
    exact genFib_pt_inj 𝒴 s s' h
  obtain ⟨y0⟩ := hM.2.2.2.2.2.2.2
  obtain ⟨s0, -⟩ := genFib_pt 𝒴 y0
  have hsurj := _root_.LeafQM.AV.Pin.curveFacts.2 (genFib 𝒴) (genFib_isProper 𝒴 hM.1) (genFib_smooth 𝒴 hM.2.1) ⟨s0⟩
    (π.comp g.left) (fun _ => hfin'.subset (Set.subset_univ _))
  have : (Set.univ : Set (OnePoint Qbar)).Finite := by
    refine (hfin'.image (fun s => (π.comp g.left).val (K := Qbar) s.left)).subset ?_
    intro t _
    obtain ⟨s, hs⟩ := hsurj t
    exact ⟨s, trivial, hs⟩
  have hinf : (Set.univ : Set (OnePoint Qbar)).Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => OnePoint.some (n : Qbar)) ?_
      (fun _ => trivial)
    intro m n h
    exact_mod_cast OnePoint.coe_injective h
  exact hinf this

/-- **Glue A `FibreAutTame` from T5, (A-fix) and (A-count).** A finite subset `S` of `fibreAut`
injects into the twist class of a `ℚ̄`-point `y` avoiding the (finitely many) fixed points of the
`s⁻¹ t` (`s ≠ t ∈ S`), so `|S| ≤ 324`; hence `fibreAut` is finite of order `≤ 324 < p`. -/
theorem fibreAutTame_of (hT : ObjBridge.TorsionStructure) (hfix : FibreAutFixFinite)
    (hcnt : TwistClassCard) : FibreAutTame := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  choose fib hfib using fun y => hM.2.2.1 Qbar y
  have hbound : ∀ S : Finset (Aut 𝒴.left), (↑S : Set (Aut 𝒴.left)) ⊆ fibreAut 𝒴 𝒜 →
      S.card ≤ 324 := by
    intro S hS
    classical
    let F : Set (Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) :=
      ⋃ s ∈ S, ⋃ t ∈ S, {y | s ≠ t ∧ y ≫ (s⁻¹ * t).asIso.hom = y}
    have hF : F.Finite := by
      refine Set.Finite.biUnion S.finite_toSet fun s hs => Set.Finite.biUnion S.finite_toSet
        fun t ht => ?_
      by_cases hst : s = t
      · simp [hst]
      · have hmem : s⁻¹ * t ∈ fibreAut 𝒴 𝒜 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS hs)) (hS ht)
        have hne : s⁻¹ * t ≠ 1 := fun h => hst (inv_mul_eq_one.mp h)
        refine (hfix p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 _ hmem hne).subset ?_
        intro y hy
        exact hy.2
    obtain ⟨y, -, hyF⟩ := ((infinite_qbarPoints (π := π) hM h1).diff hF).nonempty
    have hcl := hcnt (fib y)
    have hmaps : ∀ s ∈ S, M3.mk (fib (y ≫ s.asIso.hom)) ∈
        {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧ TwistEq (fib y) Q} :=
      fun s hs => ⟨_, rfl, twistEq_of_mem_fibreAut hM huniq (hS hs) y _ _ (hfib y) (hfib _)⟩
    have hinj : Set.InjOn (fun s : Aut 𝒴.left => M3.mk (fib (y ≫ s.asIso.hom))) ↑S := by
      intro s hs t ht hst
      have e : y ≫ s.asIso.hom = y ≫ t.asIso.hom :=
        hM.2.2.2.1 _ _ _ _ (hfib _) (hfib _) hst
      by_contra hne
      apply hyF
      simp only [F, Set.mem_iUnion, Set.mem_setOf_eq]
      refine ⟨s, hs, t, ht, hne, ?_⟩
      simp only [Aut.mul_asIso, Aut.inv_asIso, Iso.trans_hom, Iso.symm_hom]
      rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    calc S.card = (↑S : Set (Aut 𝒴.left)).ncard := (Set.ncard_coe_finset S).symm
      _ ≤ _ := Set.ncard_le_ncard_of_injOn _ hmaps hinj hcl.1
      _ ≤ 324 := hcl.2
  have hfinG : (fibreAut 𝒴 𝒜 : Set (Aut 𝒴.left)).Finite := by
    by_contra hinf
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf 325
    have := hbound S hS
    omega
  haveI : Finite (fibreAut 𝒴 𝒜) := hfinG.to_subtype
  refine ⟨this, fun hdvd => ?_⟩
  have hpos : 0 < Nat.card (fibreAut 𝒴 𝒜) := Nat.card_pos
  have hle : Nat.card (fibreAut 𝒴 𝒜) ≤ 324 := by
    have e : Nat.card (fibreAut 𝒴 𝒜) = (fibreAut 𝒴 𝒜 : Set (Aut 𝒴.left)).ncard :=
      Nat.card_coe_set_eq _
    rw [e, Set.ncard_eq_toFinset_card _ hfinG]
    exact hbound _ (by simp)
  have := Nat.le_of_dvd hpos hdvd
  omega

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 6: glue C1 `CMSectionsDisjoint` from L5, L6, A and four smaller glue Props
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-! ## Automorphisms fixing every field point over a set -/

section FixOn

variable {X : Scheme.{0}}

/-- `h` fixes every field point of `X` whose point lies in `Z` (for `Z = {w}`: `h` fixes `w` and
acts trivially on `κ(w)`). -/
def FixesFieldPointsOn (h : Aut X) (Z : Set X) : Prop :=
  ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ X), ptOf t ∈ Z → t ≫ h.asIso.hom = t

/-- The automorphisms fixing every field point over `Z` form a subgroup. -/
def fixOn (Z : Set X) : Subgroup (Aut X) where
  carrier := {h | FixesFieldPointsOn h Z}
  one_mem' := fun K _ t _ => by simp
  mul_mem' := by
    intro a b ha hb K _ t ht
    simp only [Aut.mul_asIso, Iso.trans_hom]
    rw [← Category.assoc, hb K t ht, ha K t ht]
  inv_mem' := by
    intro a ha K _ t ht
    simp only [Aut.inv_asIso, Iso.symm_hom]
    conv_lhs => rw [← ha K t ht]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem FixesFieldPointsOn.mono {h : Aut X} {Z Z' : Set X} (hh : FixesFieldPointsOn h Z)
    (hZ : Z' ⊆ Z) : FixesFieldPointsOn h Z' := fun K _ t ht => hh K t (hZ ht)

/-- Fixing the field points at `w` gives the hypothesis of Leaf L6 at `w`. -/
theorem residue_trivial_of_fixesOn {h : Aut X} {w : X} (hh : FixesFieldPointsOn h {w}) :
    ∃ e : h.asIso.hom w = w,
      (X.residueFieldCongr e).inv ≫ h.asIso.hom.residueFieldMap w = 𝟙 _ := by
  let K : Type := X.residueField w
  let t : Spec (CommRingCat.of K) ⟶ X :=
    (Scheme.SpecToEquivOfField K X).symm ⟨w, CommRingCat.ofHom (RingHom.id K)⟩
  have ht : ptOf t = w := by
    simp only [ptOf, t, Equiv.apply_symm_apply]
  have hfix := hh K t (by rw [ht]; rfl)
  have key : ∀ a : (Σ x : X, X.residueField x ⟶ CommRingCat.of K),
      a = ⟨w, CommRingCat.ofHom (RingHom.id K)⟩ →
      (⟨h.asIso.hom a.1, h.asIso.hom.residueFieldMap a.1 ≫ a.2⟩ :
        Σ x : X, X.residueField x ⟶ CommRingCat.of K) = a →
      ∃ e : h.asIso.hom w = w,
        (X.residueFieldCongr e).inv ≫ h.asIso.hom.residueFieldMap w = 𝟙 _ := by
    rintro _ rfl e
    rw [Scheme.SpecToEquivOfField_eq_iff] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨e1, ?_⟩
    have e3 : h.asIso.hom.residueFieldMap w = (X.residueFieldCongr e1).hom := by
      have := e2
      dsimp only at this
      ext x
      exact congrArg (fun φ => φ.hom x) this
    rw [e3, Iso.inv_hom_id]
  have e := congrArg (Scheme.SpecToEquivOfField K X) hfix
  rw [specToEquivOfField_comp_right] at e
  exact key _ (Equiv.apply_symm_apply _ _) e

end FixOn

/-! ## The smaller glue Props -/

/-- **Glue (C1a): the points of `X` over a point of an SGA 1 quotient form one orbit**
(commutative algebra; SGA 1 Exp. V, Prop. 1.1 (ii) (locator UNVERIFIED); over an affine `W ⊆ Z`
it is the transitivity of `G` on the primes of `Γ(q⁻¹W)` over a prime of `Γ(q⁻¹W)^G`, Mathlib's
`Algebra.IsInvariant.exists_smul_of_under_eq`). -/
def GQuotientPointOrbits : Prop :=
  ∀ (X Z : Scheme.{0}) (G : Subgroup (Aut X)) (q : X ⟶ Z), Finite G → IsGQuotient G q →
    ∀ x x' : X, q x = q x' → ∃ g ∈ G, g.asIso.hom x' = x

/-- **Glue (C1b): the stabilizer of a CM point contains an involution** (algebra of QM surfaces
with CM; no new literature). For the smooth model and a `ℚ̄`-point `y` whose object has CM by
`ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]`, some `ι ≠ 1` in `fibreAut` with `ι² = 1` fixes `y`. (Outline: the CM
endomorphism `φ` (`φ² = −1`, resp. of order 6, resp. `φ² = −6` composed with the Atkin–Lehner
twist) is an isomorphism `(A, ι, η) ≅ (A, ι ∘ α, η ∘ (· u))` for a twist `α` and a unit `u`
(`Level3.torsor`, `exists_unit_congr`), so the Hecke automorphism of `(α, u)` (or a power of it)
fixes `y`; the stabilizers have the orbifold orders `4, 6, 2` modulo `±1`
(`RvNocm.ramification_eq_orbifold_order`), all even.) -/
def CMStabInvolution : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P : QML3 Qbar), IsFibreOf 𝒜 y P →
      (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
      ∃ ι ∈ fibreAut 𝒴 𝒜, ι ≠ 1 ∧ ι * ι = 1 ∧ y ≫ ι.asIso.hom = y

/-- **Glue (C1c): an automorphism fixing a `ℚ̄`-point fixes its closure pointwise, with trivial
residue action** (scheme theory; no literature). For `𝒴` proper and smooth over `ℤ_(p)` and an
automorphism `h` over `ℤ_(p)` with `y ≫ h = y`, `h` fixes every field point of `𝒴` lying in the
closure `Z` of the point of `y`. (Outline: `h` fixes `x` and acts trivially on `κ(x)` (it
commutes with the embedding `κ(x) → ℚ̄`); `Z` with its reduced structure is integral with
function field `κ(x)`, and `h|_Z, id_Z : Z → 𝒴` agree at the generic point, hence on a dense
open (`𝒴` locally of finite presentation over `ℤ_(p)`: EGA IV 8.13.1), hence everywhere (`Z`
reduced, `𝒴` separated); a field point over `Z` factors through `Z`.) -/
def StabFixesClosure : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    ∀ (h : Aut 𝒴.left), h.asIso.hom ≫ 𝒴.hom = 𝒴.hom →
    ∀ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, y ≫ h.asIso.hom = y →
      FixesFieldPointsOn h (closure {qbarPoint y})

/-- **Glue (C1d): two `ℚ̄`-points with the same underlying point are Galois conjugate**
(field theory; no literature): the two embeddings `κ(x) → ℚ̄` differ by an automorphism of `ℚ̄`
(extend one to `ℚ̄`, `IsAlgClosed.lift`; `ℚ̄` is algebraic over the image). -/
def QbarPointsConjugate : Prop :=
  ∀ (X : Scheme.{0}) (y y' : Spec (CommRingCat.of Qbar) ⟶ X), qbarPoint y = qbarPoint y' →
    ∃ σ : Qbar ≃ₐ[ℚ] Qbar, y' = Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y

/-! ## The reduction of C1 -/

/-- In a finite cyclic group there is at most one involution. -/
theorem eq_of_involutions_cyclic {H : Type*} [Group H] [Finite H] [IsCyclic H] {a b : H}
    (ha : a ≠ 1) (ha2 : a * a = 1) (hb : b ≠ 1) (hb2 : b * b = 1) : a = b := by
  classical
  cases nonempty_fintype H
  have hle := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  by_contra hab
  have hsub : ({1, a, b} : Finset H) ⊆ Finset.univ.filter (fun x : H => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · rw [pow_two, ha2]
    · rw [pow_two, hb2]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
    Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton] at hcard
  have : (Finset.univ.filter (fun x : H => x ^ 2 = 1)).card ≤ 2 := hle
  omega

theorem qbarPoint_comp {X X' : Scheme.{0}} (y : Spec (CommRingCat.of Qbar) ⟶ X) (h : X ⟶ X') :
    qbarPoint (y ≫ h) = h (qbarPoint y) := rfl

/-- **Glue C1 `CMSectionsDisjoint` from glue A, (A-fix), (C1a)-(C1d)** (L5 and L6 are the
hypotheses of the Prop). A common point `z` of the closures of `q(x)` and `q(x')` lifts to
`w ∈ closure{x}` and, after moving by some `h ∈ fibreAut` (C1a), to `w ∈ closure{h x'}`; the
inertia group `H` of `w` in `fibreAut` contains an involution fixing `y` and one fixing `y' ≫ h`
(C1b, C1c), is cyclic (L6), so the two involutions agree, and L5 makes the closures of `x` and
`h x'` disjoint (the two points differ: Galois conjugate points (C1d) have equal `π`-values, and
CM points of different types do not), a contradiction. -/
theorem cMSectionsDisjoint_of (hA : FibreAutTame) (hfix : FibreAutFixFinite)
    (hO : GQuotientPointOrbits) (hI : CMStabInvolution) (hS : StabFixesClosure)
    (hC : QbarPointsConjugate) : CMSectionsDisjoint := by
  intro hL5 hL6 p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf y y' P P' hP hP' htype
  obtain ⟨hfin, htame⟩ := hA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  rw [Set.disjoint_left]
  intro z hz hz'
  have hcl : ∀ u : 𝒴.left, closure {q.left u} ⊆ q.left '' closure {u} := by
    intro u
    refine closure_minimal ?_ (q.left.isClosedMap _ isClosed_closure)
    rintro _ rfl
    exact ⟨u, subset_closure rfl, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hcl _ hz
  obtain ⟨w', hw', hww'⟩ := hcl _ hz'
  obtain ⟨h, hhG, hhw⟩ := hO _ _ _ _ hfin hq w w' hww'.symm
  set y'' := y' ≫ h.asIso.hom with hy''
  have hw'' : w ∈ closure {qbarPoint y''} := by
    rw [hy'', qbarPoint_comp, ← hhw, ← Set.image_singleton]
    exact image_closure_subset_closure_image h.asIso.hom.continuous ⟨w', hw', rfl⟩
  obtain ⟨P'', hP''⟩ := hM.2.2.1 Qbar y''
  have hover := fibreAut_over 𝒴 𝒜
  -- the two involutions
  have htype1 : HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q := by
    rcases htype with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩
    · exact Or.inl a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
  have htype2 : HasCM4 P'.q ∨ HasCM3 P'.q ∨ HasCM24 P'.q := by
    rcases htype with ⟨-, a⟩ | ⟨-, a⟩ | ⟨-, a⟩
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr a)
    · exact Or.inr (Or.inr a)
  obtain ⟨ι, hιG, hι1, hι2, hιy⟩ := hI p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y P hP htype1
  obtain ⟨ι', hι'G, hι'1, hι'2, hι'y⟩ := hI p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y' P' hP' htype2
  set ι'' := h * ι' * h⁻¹ with hι''
  have hι''G : ι'' ∈ fibreAut 𝒴 𝒜 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhG hι'G) (Subgroup.inv_mem _ hhG)
  have hι''1 : ι'' ≠ 1 := by
    intro e
    apply hι'1
    have : ι' = h⁻¹ * ι'' * h := by rw [hι'']; group
    rw [this, e]; group
  have hι''2 : ι'' * ι'' = 1 := by
    have : ι'' * ι'' = h * (ι' * ι') * h⁻¹ := by rw [hι'']; group
    rw [this, hι'2]; group
  have hι''y : y'' ≫ ι''.asIso.hom = y'' := by
    simp only [hy'', hι'', Aut.mul_asIso, Aut.inv_asIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hι'y]
  -- the inertia group at `w`
  let H : Subgroup (Aut 𝒴.left) := fibreAut 𝒴 𝒜 ⊓ fixOn {w}
  have hιH : ι ∈ H := ⟨hιG, (hS p 𝒴 hM.1 hM.2.1 ι (hover ι hιG) y hιy).mono
    (Set.singleton_subset_iff.mpr hw)⟩
  have hι''H : ι'' ∈ H := ⟨hι''G, (hS p 𝒴 hM.1 hM.2.1 ι'' (hover ι'' hι''G) y'' hι''y).mono
    (Set.singleton_subset_iff.mpr hw'')⟩
  have hHle : H ≤ fibreAut 𝒴 𝒜 := inf_le_left
  haveI : Finite H := Finite.of_injective (fun x : H => (⟨x.1, hHle x.2⟩ : fibreAut 𝒴 𝒜))
    (fun a b e => Subtype.ext (by simpa using congrArg Subtype.val e))
  have hcyc : IsCyclic H := by
    refine hL6 p 𝒴 hM.1 hM.2.1 H inferInstance ?_ (fun x hx => hover x (hHle hx))
      (fun x hx hx1 => hfix p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 x (hHle hx) hx1) w
      (fun x hx => residue_trivial_of_fixesOn hx.2)
    intro hdvd
    exact htame (hdvd.trans (Subgroup.card_dvd_of_le hHle))
  have hιι : ι = ι'' := by
    have := eq_of_involutions_cyclic (H := H) (a := ⟨ι, hιH⟩) (b := ⟨ι'', hι''H⟩)
      (fun e => hι1 (congrArg Subtype.val e)) (Subtype.ext hι2)
      (fun e => hι''1 (congrArg Subtype.val e)) (Subtype.ext hι''2)
    exact congrArg Subtype.val this
  -- the two points differ
  have hne : qbarPoint y ≠ qbarPoint y'' := by
    intro e
    obtain ⟨σ, hσ⟩ := hC _ y y'' e
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    obtain ⟨s', hs'⟩ := genFib_pt 𝒴 y'
    obtain ⟨s'', hs''⟩ := genFib_pt 𝒴 y''
    have hP2 := (congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP
    have hP2' := (congrArg (fun t => IsFibreOf 𝒜 t _) hs').mpr hP'
    have hP2'' := (congrArg (fun t => IsFibreOf 𝒜 t _) hs'').mpr hP''
    -- the conjugate lift
    set sσ : fieldPt Qbar ⟶ genFib 𝒴 := fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ s with hsσ
    have hsσl : sσ.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) = y'' := by
      rw [hσ, ← hs]
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ _ = _
      exact Category.assoc _ _ _
    have hsσ'' : sσ = s'' := genFib_pt_inj 𝒴 _ _ (hsσl.trans hs''.symm)
    have hl : (sσ ≫ g).left = Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ (s ≫ g).left := by
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ g.left = _
      exact Category.assoc _ _ _
    have hπσ : π.val (K := Qbar) (s'' ≫ g).left =
        (π.val (K := Qbar) (s ≫ g).left).map (σ : Qbar →+* Qbar) := by
      rw [← hsσ'']
      exact (congrArg (fun t => π.val (K := Qbar) t) hl).trans (ToP1.val_comp π _ _)
    -- `y''` is in the orbit of `y'`, so it has the same `π`-value as `y'`
    have hte : TwistEq P' P'' := twistEq_of_mem_fibreAut hM huniq hhG y' P' P'' hP' hP''
    have hR' := h2 (s' ≫ g) (s'' ≫ g) P' P'' (hg Qbar s' P' hP2') (hg Qbar s'' P'' hP2'')
    have hR := h2 (s ≫ g) (s ≫ g) P P (hg Qbar s P hP2) (hg Qbar s P hP2)
    have hv : π.val (K := Qbar) (s' ≫ g).left = π.val (K := Qbar) (s'' ≫ g).left :=
      hR'.1.2 hte
    rw [hπσ] at hv
    have h16 : (0 : Qbar) ≠ -16 / 27 := by norm_num
    rcases htype with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · rw [hR.2.1 a, hR'.2.2.1 b] at hv
      norm_num at hv
    · rw [hR.2.1 a, hR'.2.2.2 b] at hv
      norm_num at hv
    · rw [hR.2.2.1 a, hR'.2.2.2 b] at hv
      norm_num at hv
  -- Leaf L5 for the involution `ι`
  have hfinι : {t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | t ≫ ι.asIso.hom = t}.Finite :=
    hfix p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 ι hιG hι1
  have hdisj := hL5 p 𝒴 hM.1 hM.2.1 ι 2 (hover ι hιG) (by norm_num)
    (fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega)
    (by rw [pow_two, hι2]) hfinι y y'' hιy (by rw [hιι]; exact hι''y) hne
  exact Set.disjoint_left.mp hdisj hw hw''

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 6b: glue B `GenericQuotientP1` from T5, a descent glue and a curve glue
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- The induced map of generic fibres `𝒴_ℚ → 𝒵_ℚ`. -/
def genFibMap {p : ℕ} [Fact p.Prime] {𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} (q : 𝒴 ⟶ 𝒵) :
    genFib 𝒴 ⟶ genFib 𝒵 :=
  Over.homMk (pullback.lift (pullback.fst 𝒴.hom (specRatToZloc p) ≫ q.left)
      (pullback.snd 𝒴.hom (specRatToZloc p))
      ((Category.assoc _ _ _).trans (by rw [Over.w q]; exact pullback.condition)))
    (pullback.lift_snd _ _ _)

theorem genFibMap_fst {p : ℕ} [Fact p.Prime] {𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))}
    (q : 𝒴 ⟶ 𝒵) : (genFibMap q).left ≫ pullback.fst 𝒵.hom (specRatToZloc p) =
      pullback.fst 𝒴.hom (specRatToZloc p) ≫ q.left :=
  pullback.lift_fst _ _ _

/-- **Glue (B-desc): an orbit-invariant coordinate on `𝒴_ℚ` descends to the quotient**
(scheme theory of quotients; SGA 1 Exp. V §1 (locators UNVERIFIED), no new literature). For the
SGA 1 quotient `q : 𝒴 → 𝒵` over `ℤ_(p)` of a proper smooth relative curve `𝒴` by a finite group
`G` of `ℤ_(p)`-automorphisms with `q` finite, a map `σ : 𝒴_ℚ → P¹` whose values on `ℚ̄`-points are constant on `G`-orbits factors
through `𝒵_ℚ`, and every `ℚ̄`-point of `𝒵_ℚ` comes from `𝒴_ℚ`. (Outline: `𝒵_ℚ = 𝒴_ℚ/G`, since
the formation of invariants commutes with the localization `ℤ_(p) → ℚ`; `σ` is `G`-invariant as a
morphism, its values on the dense set of `ℚ̄`-points of the reduced `𝒴_ℚ` being invariant; so the
opens `σ⁻¹(t ≠ ∞)`, `σ⁻¹(t ≠ 0)` are `G`-stable and saturated, their images in `𝒵_ℚ` are open
(`q` is closed and surjective), and `f, g` are invariant sections, i.e. sections on `𝒵_ℚ`;
`q` is integral and surjective, so `ℚ̄`-points lift.) -/
def QuotientDescendsQ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵)
    (G : Subgroup (Aut 𝒴.left)), IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    Finite G → (∀ g ∈ G, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) →
    IsGQuotient G q.left → IsFinite q.left →
    ∀ σ : ToP1 (genFib 𝒴).left,
      (∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (g : Aut 𝒴.left), g ∈ G →
        s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
          s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) ≫ g.asIso.hom →
        σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left) →
    ∃ σ' : ToP1 (genFib 𝒵).left,
      (∀ s : fieldPt Qbar ⟶ genFib 𝒴,
        σ'.val (K := Qbar) (s ≫ genFibMap q).left = σ.val (K := Qbar) s.left) ∧
      ∀ t : fieldPt Qbar ⟶ genFib 𝒵, ∃ s : fieldPt Qbar ⟶ genFib 𝒴, s ≫ genFibMap q = t

/-- **Glue (B-iso): a map to `P¹` of a proper smooth `ℚ`-curve that is bijective on `ℚ̄`-points is
an isomorphism onto `P¹_ℚ`** (curve theory; the `P¹` case of model-glue's `CurveBijIso`: finite
(quasi-finite and proper), generically étale in characteristic 0 of degree 1, onto the normal
`P¹`, hence an isomorphism (Hartshorne II.6.7, I.6.12; locators UNVERIFIED); the charts are then
the preimages of `𝔸¹` and `P¹ ∖ {0}`). -/
def ToP1BijIsCoordinateQ : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of ℚ))), IsProper Z.hom → SmoothOfRelativeDimension 1 Z.hom →
    ∀ σ : ToP1 Z.left, Function.Bijective (fun t : fieldPt Qbar ⟶ Z => σ.val (K := Qbar) t.left) →
      IsP1CoordinateQ Z σ

/-- **Glue B `GenericQuotientP1` from T5, glue A, Leaf L3 (`𝒵` proper smooth), (B-desc) and
(B-iso).** The map
`π ∘ g : 𝒴_ℚ → P¹` is constant on `fibreAut`-orbits (orbits lie in twist classes, R2fp), so it
descends to `σ̄ : 𝒵_ℚ → P¹` (B-desc); `σ̄` is injective on `ℚ̄`-points (equal values give
twist-equivalent fibres, hence one orbit (T5), hence one point of `𝒵`) and onto (`CurveSurj` for
`π ∘ g`, whose fibres are finite twist classes), so it is an isomorphism onto `P¹_ℚ` (B-iso). -/
theorem genericQuotientP1_of (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
    (hTS : TameQuotientSmooth) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ) :
    GenericQuotientP1 := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf
  obtain ⟨hfin, htame⟩ := hA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨hZp, hZs⟩ := hTS p 𝒴 𝒵 q hM.1 hM.2.1 _ hfin htame (fibreAut_over 𝒴 𝒜) hq hqf
  have hinvq := hq.1
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  choose fib hfib using fun y => hM.2.2.1 Qbar y
  set j := pullback.fst 𝒴.hom (specRatToZloc p)
  let σ : ToP1 (genFib 𝒴).left := π.comp g.left
  have hσ : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, σ.val (K := Qbar) s.left = π.val (K := Qbar) (s ≫ g).left :=
    fun s => ToP1.val_comp_right π g.left s.left
  -- `σ`-values and twist classes
  have hrel : ∀ s s' : fieldPt Qbar ⟶ genFib 𝒴,
      (σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left ↔
        TwistEq (fib (s.left ≫ j)) (fib (s'.left ≫ j))) := by
    intro s s'
    rw [hσ, hσ]
    exact (h2 (s ≫ g) (s' ≫ g) _ _ (hg Qbar s _ (hfib _)) (hg Qbar s' _ (hfib _))).1
  have hinvσ : ∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (h : Aut 𝒴.left), h ∈ fibreAut 𝒴 𝒜 →
      s'.left ≫ j = s.left ≫ j ≫ h.asIso.hom →
      σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left := by
    intro s s' h hh e
    refine (hrel s s').2 (twistEq_of_mem_fibreAut hM huniq hh (s.left ≫ j) _ _ (hfib _) ?_)
    exact (congrArg (fun t => IsFibreOf 𝒜 t (fib (s'.left ≫ j)))
      (e.trans (Category.assoc _ _ _).symm)).mp (hfib _)
  obtain ⟨σ', hσ', hlift⟩ := hD p 𝒴 𝒵 q (fibreAut 𝒴 𝒜) hM.1 hM.2.1 hfin (fibreAut_over 𝒴 𝒜) hq hqf σ hinvσ
  refine ⟨σ', hB (genFib 𝒵) (genFib_isProper 𝒵 hZp) (genFib_smooth 𝒵 hZs) σ' ⟨?_, ?_⟩⟩
  · intro t t' htt
    obtain ⟨s, rfl⟩ := hlift t
    obtain ⟨s', rfl⟩ := hlift t'
    simp only [hσ'] at htt
    obtain ⟨h, hhG, hh⟩ := mem_orbit_of_twistEq hT hM (s.left ≫ j) (s'.left ≫ j) _ _ (hfib _)
      (hfib _) ((hrel s s').1 htt)
    have k : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, (s ≫ genFibMap q).left ≫
        pullback.fst 𝒵.hom (specRatToZloc p) = (s.left ≫ j) ≫ q.left := fun s =>
      (Category.assoc _ _ _).trans ((congrArg (s.left ≫ ·) (genFibMap_fst q)).trans
        (Category.assoc _ _ _).symm)
    apply genFib_pt_inj 𝒵
    refine (k s).trans ((k s').trans ?_).symm
    exact (congrArg (· ≫ q.left) hh).trans ((Category.assoc _ _ _).trans
      (congrArg ((s.left ≫ j) ≫ ·) (hinvq h hhG)))
  · intro v
    obtain ⟨y0⟩ := hM.2.2.2.2.2.2.2
    obtain ⟨s0, -⟩ := genFib_pt 𝒴 y0
    have hfin' : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, {s' : fieldPt Qbar ⟶ genFib 𝒴 |
        σ.val (K := Qbar) s'.left = σ.val (K := Qbar) s.left}.Finite := by
      intro s
      have hT' := twistClassFinite hT (fib (s.left ≫ j))
      refine Set.Finite.of_finite_image (f := fun s' => M3.mk (fib (s'.left ≫ j)))
        (hT'.subset ?_) ?_
      · rintro _ ⟨s', hs', rfl⟩
        exact ⟨_, rfl, (hrel s s').1 hs'.symm⟩
      · intro a _ b _ hab
        exact genFib_pt_inj 𝒴 a b (hM.2.2.2.1 _ _ _ _ (hfib _) (hfib _) hab)
    obtain ⟨s, hs⟩ := _root_.LeafQM.AV.Pin.curveFacts.2 (genFib 𝒴) (genFib_isProper 𝒴 hM.1) (genFib_smooth 𝒴 hM.2.1)
      ⟨s0⟩ σ hfin' v
    exact ⟨s ≫ genFibMap q, (hσ' s).trans hs⟩

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 7: the composite
════════════════════════════════════════════════════════════════════════════════════════════ -/

namespace MCRQuot

open MCRGlue ModelGlue

/-- **`ModelCoordinateResidue` from the leaves L1-L6, the textbook leaf `TorsionStructure` (T5),
glue B, and the smaller glue of this task**: (A-fix) `FibreAutFixFinite`, (A-count)
`TwistClassCard`, (C1a) `GQuotientPointOrbits`, (C1b) `CMStabInvolution`, (C1c)
`StabFixesClosure`, (C1d) `QbarPointsConjugate`, (C2-P¹) `P1ThreePoints`. Glue A, C1 and C2 of
mcr-glue are no longer hypotheses. -/
theorem modelCoordinateResidue_of_mcrQuot (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (gB : GenericQuotientP1)
    (hfix : FibreAutFixFinite) (hcnt : TwistClassCard) (hO : GQuotientPointOrbits)
    (hI : CMStabInvolution) (hS : StabFixesClosure) (hC : QbarPointsConjugate)
    (hN : P1ThreePoints) : ModelCoordinateResidue :=
  have gA : FibreAutTame := fibreAutTame_of hT hfix hcnt
  modelCoordinateResidue_of_leaves'' hAF hQE hTS hP1 hFix hCyc gA gB
    (cMSectionsDisjoint_of gA hfix hO hI hS hC) (coordinateFromSections_of gA hT hN)

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 8: `P1ThreePoints` from the translation glue `P1Translate`

`PGL₂(ℤ_(p))` acting on isomorphisms `𝒵 ≅ P¹_{ℤ_(p)}` by charts: the inversion `t ↦ 1/t`
(`_root_.LeafQM.AV.Pin.ImagePlane.inv`, charts swapped) and the scalings `t ↦ u t` (`u ∈ ℤ_(p)^×`, same charts) are
constructed here; the translations `t ↦ t + e` are the glue `P1Translate`. Disjoint closures of
rational sections force distinct reductions (`isUnit_sub_of_disjoint`), and a normalization
argument moves three such sections to `0, ∞, −16/27`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

variable {p : ℕ} [Fact p.Prime]

/-- `ℤ_(p) → ℚ̄`. -/
def iq (p : ℕ) [Fact p.Prime] : Zloc p →+* Qbar := (algebraMap ℚ Qbar).comp (zlocToRat p)

theorem iq_injective : Function.Injective (iq p) :=
  (algebraMap ℚ Qbar).injective.comp (zlocToRat_injective p)

theorem ev_baseToSections (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) {W : 𝒵.left.Opens}
    (z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (hz : ptOf z ∈ W) (a : Zloc p) :
    ev z hz (baseToSections 𝒵 W a) = iq p a :=
  congrArg (fun φ : Zloc p →+* Qbar => φ a) (zloc_ringHom_ext ((ev z hz).comp _) (iq p))

theorem res_baseToSections (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) {W W' : 𝒵.left.Opens}
    (h : W' ≤ W) (a : Zloc p) : res h (baseToSections 𝒵 W a) = baseToSections 𝒵 W' a := by
  simp only [res, baseToSections, RingHom.coe_comp, Function.comp_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-! ## Inversion -/

theorem val_inv {K : Type} [Field K] {X : Scheme.{0}} (ρ : ToP1 X)
    (z : Spec (CommRingCat.of K) ⟶ X) : (_root_.LeafQM.AV.Pin.ImagePlane.inv ρ).val z = _root_.LeafQM.AV.Pin.ImagePlane.recip (ρ.val z) :=
  _root_.LeafQM.AV.Pin.ImagePlane.val_eq_recip (_root_.LeafQM.AV.Pin.ImagePlane.inv ρ) z

theorem isP1Coordinate_inv {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left}
    (h : IsP1Coordinate 𝒵 ρ) : IsP1Coordinate 𝒵 (_root_.LeafQM.AV.Pin.ImagePlane.inv ρ) :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-! ## Scaling by a unit -/

/-- The scaled coordinate `u · ρ`. -/
def scale (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (ρ : ToP1 𝒵.left) (u : (Zloc p)ˣ) :
    ToP1 𝒵.left where
  U := ρ.U
  V := ρ.V
  cover := ρ.cover
  f := baseToSections 𝒵 ρ.U (u : Zloc p) * ρ.f
  g := baseToSections 𝒵 ρ.V ((u⁻¹ : (Zloc p)ˣ) : Zloc p) * ρ.g
  inv := by
    change res _ (_ * ρ.f) * res _ (_ * ρ.g) = 1
    rw [map_mul, map_mul, res_baseToSections, res_baseToSections]
    have e : res (inf_le_left : ρ.U ⊓ ρ.V ≤ ρ.U) ρ.f * res (inf_le_right : ρ.U ⊓ ρ.V ≤ ρ.V) ρ.g
      = 1 := ρ.inv
    calc baseToSections 𝒵 (ρ.U ⊓ ρ.V) ↑u * res _ ρ.f *
          (baseToSections 𝒵 (ρ.U ⊓ ρ.V) ↑u⁻¹ * res _ ρ.g)
        = baseToSections 𝒵 (ρ.U ⊓ ρ.V) (↑u * ↑u⁻¹) *
            (res (inf_le_left : ρ.U ⊓ ρ.V ≤ ρ.U) ρ.f * res (inf_le_right : ρ.U ⊓ ρ.V ≤ ρ.V) ρ.g) := by
          rw [map_mul]; ring
      _ = 1 := by rw [e, Units.mul_inv, map_one, mul_one]
  basicOpen_f := by
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((u.isUnit).map _),
      inf_eq_right.mpr (Scheme.basicOpen_le _ _), ρ.basicOpen_f]
  basicOpen_g := by
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((u⁻¹.isUnit).map _),
      inf_eq_right.mpr (Scheme.basicOpen_le _ _), ρ.basicOpen_g]

theorem val_scale (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (ρ : ToP1 𝒵.left) (u : (Zloc p)ˣ)
    (z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) :
    (scale 𝒵 ρ u).val z = (ρ.val z).map (fun t => iq p u * t) := by
  by_cases hz : ptOf z ∈ ρ.U
  · rw [val_of_mem (scale 𝒵 ρ u) z hz, val_of_mem ρ z hz]
    change OnePoint.some (ev z hz (baseToSections 𝒵 ρ.U ↑u * ρ.f)) = _
    rw [map_mul, ev_baseToSections]
    rfl
  · rw [val_of_not_mem (scale 𝒵 ρ u) z hz, val_of_not_mem ρ z hz]
    rfl

/-- Bijectivity of `X ↦ c · h` when `X ↦ h` is bijective and `c` is a unit. -/
theorem bijective_eval₂_mul {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (h : S)
    (u : Rˣ) (hb : Function.Bijective (eval₂RingHom φ h)) :
    Function.Bijective (eval₂RingHom φ (φ u * h)) := by
  let m : R[X] →+* R[X] := eval₂RingHom C (C (u : R) * X)
  let m' : R[X] →+* R[X] := eval₂RingHom C (C ((u⁻¹ : Rˣ) : R) * X)
  have hcomp : eval₂RingHom φ (φ u * h) = (eval₂RingHom φ h).comp m := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m]
    · simp [m]
  have hmm' : m.comp m' = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m, m']
    · simp only [m, m', RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_mul,
        eval₂_C, eval₂_X, RingHom.id_apply]
      rw [← mul_assoc, ← C_mul, Units.inv_mul, C_1, one_mul]
  have hm'm : m'.comp m = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m, m']
    · simp only [m, m', RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_mul,
        eval₂_C, eval₂_X, RingHom.id_apply]
      rw [← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul]
  have hmb : Function.Bijective m :=
    ⟨Function.LeftInverse.injective (g := m') (fun x => congrArg (fun f => f x) hm'm),
      Function.RightInverse.surjective (g := m') (fun x => congrArg (fun f => f x) hmm')⟩
  rw [hcomp, RingHom.coe_comp]
  exact hb.comp hmb

theorem isP1Coordinate_scale {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left}
    (h : IsP1Coordinate 𝒵 ρ) (u : (Zloc p)ˣ) : IsP1Coordinate 𝒵 (scale 𝒵 ρ u) :=
  ⟨h.1, h.2.1, bijective_eval₂_mul _ _ u h.2.2.1, bijective_eval₂_mul _ _ u⁻¹ h.2.2.2⟩

/-! ## Translation (the glue) -/

/-- **Glue (C2-T): translations of `P¹_{ℤ_(p)}`** (chart algebra of `P¹` over `ℤ_(p)`; no
literature). For `ρ : 𝒵 ≅ P¹_{ℤ_(p)}` and `e ∈ ℤ_(p)`, the coordinate `ρ + e` is again an
isomorphism onto `P¹_{ℤ_(p)}`. (Outline: `U' = U`, `f' = f + e`;
`V' = D_V(1 + e g) ∪ D_U(f + e)`, `g'` glued from `g/(1 + e g)` and `1/(f + e)`; `V'` is covered by
the basic opens `D(g') = D_U(f + e)` and `D(1 − e g') = D_V(1 + e g)`, which are affine and generate
the unit ideal, so `V'` is affine; `ℤ_(p)[g'] = Γ(V')` because
`ℤ_(p)[Y, 1/Y] ∩ ℤ_(p)[Y, 1/(1 − eY)] = ℤ_(p)[Y]` (`Y` and `1 − eY` are coprime).) -/
def P1Translate : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (ρ : ToP1 𝒵.left),
    IsP1Coordinate 𝒵 ρ → ∀ e : Zloc p, ∃ ρ' : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ' ∧
      ∀ z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left, ρ'.val z = (ρ.val z).map (fun t => t + iq p e)

/-! ## Disjoint closures force distinct reductions -/

/-- The point of an affine open `W` with prime `ker ψ` lies in the closure of the point of a
`ℚ̄`-point `z` of `W` whose evaluation kernel is contained in `ker ψ`. -/
theorem fromSpec_ker_mem_closure {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W)
    {F : Type} [Field F] (ψ : Γ(X, W) →+* F) (z : Spec (CommRingCat.of Qbar) ⟶ X)
    (hz : ptOf z ∈ W) (hker : ∀ s, ev z hz s = 0 → ψ s = 0) :
    hW.fromSpec ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ ∈ closure {ptOf z} := by
  set w := hW.fromSpec ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ with hwdef
  have hwW : w ∈ W := by
    change w ∈ (W : Set X)
    rw [← hW.range_fromSpec]; exact ⟨_, rfl⟩
  rw [mem_closure_iff]
  intro o ho hwo
  obtain ⟨s, hsle, hws⟩ := hW.exists_basicOpen_le (V := ⟨o, ho⟩) ⟨w, hwo⟩ hwW
  have hs : ψ s ≠ 0 := by
    have h1 : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum Γ(X, W)) ∈
        hW.fromSpec ⁻¹ᵁ X.basicOpen s := hws
    rw [hW.fromSpec_preimage_basicOpen] at h1
    exact fun h0 => h1 (RingHom.mem_ker.mpr h0)
  have hzs : ptOf z ∈ X.basicOpen s := by
    by_contra hn
    exact hs (hker s ((ev_eq_zero_iff z hz s).2 hn))
  exact ⟨ptOf z, hsle hzs, rfl⟩

/-- **Disjoint closures force distinct reductions** (in a polynomial chart `W` of `𝒵`, values
`a, a' ∈ ℤ_(p)`): `a − a'` is a unit. Otherwise the point of `W` over `(p, h − a)` lies in both
closures. -/
theorem isUnit_sub_of_disjoint (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) {W : 𝒵.left.Opens}
    (hW : IsAffineOpen W) (h : Γ(𝒵.left, W))
    (hb : Function.Bijective (eval₂RingHom (baseToSections 𝒵 W) h))
    (z z' : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (hz : ptOf z ∈ W) (hz' : ptOf z' ∈ W)
    (a a' : Zloc p) (ha : ev z hz h = iq p a) (ha' : ev z' hz' h = iq p a')
    (hd : Disjoint (closure ({ptOf z} : Set 𝒵.left)) (closure {ptOf z'})) : IsUnit (a - a') := by
  by_contra hnu
  let e : (Zloc p)[X] ≃+* Γ(𝒵.left, W) := RingEquiv.ofBijective _ hb
  let ψ : Zloc p → (Γ(𝒵.left, W) →+* IsLocalRing.ResidueField (Zloc p)) := fun b =>
    (IsLocalRing.residue (Zloc p)).comp ((Polynomial.evalRingHom b).comp e.symm.toRingHom)
  have hres : IsLocalRing.residue (Zloc p) a = IsLocalRing.residue (Zloc p) a' := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hnu
  have hψ : ψ a = ψ a' := by
    ext s
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, coe_evalRingHom]
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, hres]
  have hev : ∀ (b : Zloc p) (zz : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (hzz : ptOf zz ∈ W),
      ev zz hzz h = iq p b → ∀ P : (Zloc p)[X], ev zz hzz (e P) = iq p (P.eval b) := by
    intro b zz hzz hbz P
    change ev zz hzz (eval₂RingHom (baseToSections 𝒵 W) h P) = _
    rw [coe_eval₂RingHom, Polynomial.hom_eval₂, hbz,
      zloc_ringHom_ext ((ev zz hzz).comp (baseToSections 𝒵 W)) ((iq p).comp (RingHom.id _)),
      ← Polynomial.hom_eval₂]
    rfl
  have hker : ∀ (b : Zloc p) (zz : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (hzz : ptOf zz ∈ W),
      ev zz hzz h = iq p b → ∀ s, ev zz hzz s = 0 → ψ b s = 0 := by
    intro b zz hzz hbz s hs
    obtain ⟨P, rfl⟩ := e.surjective s
    rw [hev b zz hzz hbz P, ← map_zero (iq p)] at hs
    have h0 : P.eval b = 0 := iq_injective hs
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, coe_evalRingHom, h0, map_zero]
  have h1 := fromSpec_ker_mem_closure hW (ψ a) z hz (hker a z hz ha)
  have h2 := fromSpec_ker_mem_closure hW (ψ a') z' hz' (hker a' z' hz' ha')
  have hpt : (⟨RingHom.ker (ψ a'), RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(𝒵.left, W)) =
      ⟨RingHom.ker (ψ a), RingHom.ker_isPrime _⟩ := PrimeSpectrum.ext (by rw [hψ])
  rw [hpt] at h2
  exact Set.disjoint_left.mp hd h1 h2

/-! ## Rational values and the normalization -/

theorem zlocToRat_algebraMap (n : ℤ) : zlocToRat p (algebraMap ℤ (Zloc p) n) = n := by
  unfold zlocToRat
  rw [IsLocalization.lift_eq]
  rfl

/-- A rational number or its inverse lies in `ℤ_(p)`; in the second case the inverse is a
non-unit. -/
theorem zloc_or_inv (r : ℚ) : (∃ e : Zloc p, zlocToRat p e = r) ∨
    (r ≠ 0 ∧ ∃ e : Zloc p, zlocToRat p e = r⁻¹ ∧ ¬ IsUnit e) := by
  have hp : (p : ℕ).Prime := Fact.out
  by_cases hd : (r.den : ℤ) ∈ (pIdeal p).primeCompl
  · left
    let u := (IsLocalization.map_units (Zloc p) (⟨r.den, hd⟩ : (pIdeal p).primeCompl)).unit
    refine ⟨algebraMap ℤ (Zloc p) r.num * ↑u⁻¹, ?_⟩
    rw [map_mul, zlocToRat_algebraMap, map_units_inv]
    change (r.num : ℚ) * (zlocToRat p (algebraMap ℤ (Zloc p) r.den))⁻¹ = r
    rw [zlocToRat_algebraMap, Int.cast_natCast, ← div_eq_mul_inv, Rat.num_div_den]
  · right
    have hd' : (p : ℤ) ∣ r.den := by
      have : (r.den : ℤ) ∈ pIdeal p := by
        simpa [Ideal.primeCompl] using hd
      exact Ideal.mem_span_singleton.mp this
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [Rat.den_zero, Nat.cast_one] at hd'
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd')
    have hnum : r.num ∈ (pIdeal p).primeCompl := by
      intro hmem
      have h1 : (p : ℤ) ∣ r.num := Ideal.mem_span_singleton.mp hmem
      have hcop := r.reduced
      have h2 : p ∣ r.num.natAbs := by
        exact Int.ofNat_dvd_left.mp h1
      have h3 : p ∣ r.den := by exact_mod_cast hd'
      have h4 : p ∣ 1 := by
        have := Nat.dvd_gcd h2 h3
        rwa [hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
    refine ⟨hr0, ?_⟩
    let u := (IsLocalization.map_units (Zloc p) (⟨r.num, hnum⟩ : (pIdeal p).primeCompl)).unit
    refine ⟨algebraMap ℤ (Zloc p) r.den * ↑u⁻¹, ?_, ?_⟩
    · rw [map_mul, zlocToRat_algebraMap, map_units_inv]
      change ((r.den : ℤ) : ℚ) * (zlocToRat p (algebraMap ℤ (Zloc p) r.num))⁻¹ = r⁻¹
      rw [zlocToRat_algebraMap, Int.cast_natCast, ← div_eq_mul_inv]
      conv_rhs => rw [← Rat.num_div_den r]
      rw [inv_div]
    · intro hu
      have : IsUnit (algebraMap ℤ (Zloc p) r.den) := by
        have := hu.mul u.isUnit
        rwa [mul_assoc, Units.inv_mul, mul_one] at this
      rw [IsLocalization.AtPrime.isUnit_to_map_iff (Zloc p) (pIdeal p)] at this
      exact hd this

theorem iq_apply (e : Zloc p) : iq p e = algebraMap ℚ Qbar (zlocToRat p e) := rfl

theorem rat_shift (r : OnePoint ℚ) (e : Zloc p) :
    (r.map (algebraMap ℚ Qbar)).map (fun t => t + iq p e) =
      (r.map (fun s => s + zlocToRat p e)).map (algebraMap ℚ Qbar) := by
  induction r using OnePoint.rec with
  | infty => rfl
  | coe s => simp [iq_apply]

theorem recip_map_alg (r : OnePoint ℚ) :
    _root_.LeafQM.AV.Pin.ImagePlane.recip (r.map (algebraMap ℚ Qbar)) = (_root_.LeafQM.AV.Pin.ImagePlane.recip r).map (algebraMap ℚ Qbar) := by
  induction r using OnePoint.rec with
  | infty => simp [_root_.LeafQM.AV.Pin.ImagePlane.recip_infty]
  | coe s =>
    rw [OnePoint.map_some, _root_.LeafQM.AV.Pin.ImagePlane.recip_coe, _root_.LeafQM.AV.Pin.ImagePlane.recip_coe]
    by_cases hs : s = 0
    · simp [hs]
    · simp [hs]

theorem chart_of_val {K : Type} [Field K] {X : Scheme.{0}} (ρ : ToP1 X)
    (z : Spec (CommRingCat.of K) ⟶ X) (t : K) (h : ρ.val z = OnePoint.some t) :
    ∃ hz : ptOf z ∈ ρ.U, ev z hz ρ.f = t := by
  by_cases hz : ptOf z ∈ ρ.U
  · rw [val_of_mem ρ z hz] at h
    exact ⟨hz, OnePoint.coe_injective h⟩
  · rw [val_of_not_mem ρ z hz] at h
    exact (OnePoint.infty_ne_coe t h).elim

theorem isUnit_of_vals {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left}
    (hρ : IsP1Coordinate 𝒵 ρ) (z z' : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (a a' : Zloc p)
    (h : ρ.val z = OnePoint.some (iq p a)) (h' : ρ.val z' = OnePoint.some (iq p a'))
    (hd : Disjoint (closure ({ptOf z} : Set 𝒵.left)) (closure {ptOf z'})) : IsUnit (a - a') := by
  obtain ⟨hz, hza⟩ := chart_of_val ρ z _ h
  obtain ⟨hz', hza'⟩ := chart_of_val ρ z' _ h'
  exact isUnit_sub_of_disjoint 𝒵 hρ.1 ρ.f hρ.2.2.1 z z' hz hz' a a' hza hza' hd

theorem ne_of_disjoint {X : Scheme.{0}} {z z' : Spec (CommRingCat.of Qbar) ⟶ X}
    (hd : Disjoint (closure ({ptOf z} : Set X)) (closure {ptOf z'})) : z ≠ z' := by
  rintro rfl
  exact Set.disjoint_left.mp hd (subset_closure rfl) (subset_closure rfl)

/-- A rational value whose section is disjoint from the section at `∞` is in `ℤ_(p)`. -/
theorem integral_of_disjoint_infty {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left}
    (hρ : IsP1Coordinate 𝒵 ρ) (z zi : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left)
    (hi : ρ.val zi = OnePoint.infty) (r : OnePoint ℚ) (hr : ρ.val z = r.map (algebraMap ℚ Qbar))
    (hd : Disjoint (closure ({ptOf z} : Set 𝒵.left)) (closure {ptOf zi})) :
    ∃ α : Zloc p, ρ.val z = OnePoint.some (iq p α) := by
  induction r using OnePoint.rec with
  | infty =>
    exact (ne_of_disjoint hd (val_injective_of_isP1Coordinate hρ z zi (hr.trans hi.symm))).elim
  | coe s =>
    rcases zloc_or_inv (p := p) s with ⟨e, he⟩ | ⟨hs0, e, he, hnu⟩
    · exact ⟨e, by rw [hr, OnePoint.map_some, iq_apply, he]⟩
    · exfalso
      apply hnu
      have h1 : (_root_.LeafQM.AV.Pin.ImagePlane.inv ρ).val z = OnePoint.some (iq p e) := by
        rw [val_inv, hr, OnePoint.map_some, _root_.LeafQM.AV.Pin.ImagePlane.recip_coe, if_neg (by simpa using hs0),
          iq_apply, he, map_inv₀]
      have h2 : (_root_.LeafQM.AV.Pin.ImagePlane.inv ρ).val zi = OnePoint.some (iq p 0) := by
        rw [val_inv, hi, _root_.LeafQM.AV.Pin.ImagePlane.recip_infty, map_zero]
      simpa using isUnit_of_vals (isP1Coordinate_inv hρ) z zi e 0 h1 h2 hd

/-- Step 1 of the normalization: move a rational section to `∞`, keeping rational values
rational. -/
theorem exists_infty (hTr : P1Translate) {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))}
    {ρ : ToP1 𝒵.left} (hρ : IsP1Coordinate 𝒵 ρ) (zi : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left)
    (b : OnePoint ℚ) (hb : ρ.val zi = b.map (algebraMap ℚ Qbar)) :
    ∃ ρ1 : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ1 ∧ ρ1.val zi = OnePoint.infty ∧
      ∀ (z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (r : OnePoint ℚ),
        ρ.val z = r.map (algebraMap ℚ Qbar) → ∃ r' : OnePoint ℚ,
          ρ1.val z = r'.map (algebraMap ℚ Qbar) := by
  induction b using OnePoint.rec with
  | infty => exact ⟨ρ, hρ, hb, fun z r h => ⟨r, h⟩⟩
  | coe s =>
    rcases zloc_or_inv (p := p) s with ⟨e, he⟩ | ⟨hs0, e, he, -⟩
    · obtain ⟨ρt, hρt, hvt⟩ := hTr p 𝒵 ρ hρ (-e)
      refine ⟨_root_.LeafQM.AV.Pin.ImagePlane.inv ρt, isP1Coordinate_inv hρt, ?_, ?_⟩
      · rw [val_inv, hvt, hb, OnePoint.map_some, OnePoint.map_some, map_neg, iq_apply, he,
          add_neg_cancel, _root_.LeafQM.AV.Pin.ImagePlane.recip_coe, if_pos rfl]
      · intro z r h
        exact ⟨_, by rw [val_inv, hvt, h, rat_shift, recip_map_alg]⟩
    · obtain ⟨ρt, hρt, hvt⟩ := hTr p 𝒵 (_root_.LeafQM.AV.Pin.ImagePlane.inv ρ) (isP1Coordinate_inv hρ) (-e)
      refine ⟨_root_.LeafQM.AV.Pin.ImagePlane.inv ρt, isP1Coordinate_inv hρt, ?_, ?_⟩
      · rw [val_inv, hvt, val_inv, hb, OnePoint.map_some, _root_.LeafQM.AV.Pin.ImagePlane.recip_coe,
          if_neg (by simpa using hs0), OnePoint.map_some, map_neg, iq_apply, he, map_inv₀,
          add_neg_cancel, _root_.LeafQM.AV.Pin.ImagePlane.recip_coe, if_pos rfl]
      · intro z r h
        exact ⟨_, by rw [val_inv, hvt, val_inv, h, recip_map_alg, rat_shift, recip_map_alg]⟩

/-- `−16/27` as a unit of `ℤ_(p)` (`p > 3`). -/
theorem exists_unit_neg_16_27 (hp3 : 3 < p) : ∃ μ : (Zloc p)ˣ, iq p μ = -16 / 27 := by
  have hp : (p : ℕ).Prime := Fact.out
  have h16 : (16 : ℤ) ∈ (pIdeal p).primeCompl := by
    intro hm
    have h1 : (p : ℤ) ∣ 16 := Ideal.mem_span_singleton.mp hm
    have h2 : p ∣ 2 ^ 4 := by exact_mod_cast h1
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
    omega
  have h27 : (27 : ℤ) ∈ (pIdeal p).primeCompl := by
    intro hm
    have h1 : (p : ℤ) ∣ 27 := Ideal.mem_span_singleton.mp hm
    have h2 : p ∣ 3 ^ 3 := by exact_mod_cast h1
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h2)
    omega
  let u16 := (IsLocalization.map_units (Zloc p) (⟨16, h16⟩ : (pIdeal p).primeCompl)).unit
  let u27 := (IsLocalization.map_units (Zloc p) (⟨27, h27⟩ : (pIdeal p).primeCompl)).unit
  refine ⟨-(u16 * u27⁻¹), ?_⟩
  rw [Units.val_neg, map_neg, Units.val_mul, map_mul, map_units_inv, neg_div]
  congr 1
  change iq p (algebraMap ℤ (Zloc p) 16) * (iq p (algebraMap ℤ (Zloc p) 27))⁻¹ = 16 / 27
  rw [iq_apply, iq_apply, zlocToRat_algebraMap, zlocToRat_algebraMap, div_eq_mul_inv]
  norm_num

/-- **`P1ThreePoints` from the translation glue `P1Translate`.** Move the section `z∞` to `∞`
(`exists_infty`); then `z₀` has a value in `ℤ_(p)` (its section is disjoint from `∞`), translate
it to `0`; then `z₁` has a unit value `γ` (disjoint from `0` and `∞`); scale by `(−16/27)/γ`. -/
theorem p1ThreePoints_of (hTr : P1Translate) : P1ThreePoints := by
  intro p _ hp3 𝒵 ρ₀ hρ₀ z₀ zi z₁ a b c ha hb hc d0i d01 di1
  obtain ⟨ρ1, hρ1, hi1, hrat1⟩ := exists_infty hTr hρ₀ zi b hb
  obtain ⟨a1, ha1⟩ := hrat1 z₀ a ha
  obtain ⟨c1, hc1⟩ := hrat1 z₁ c hc
  obtain ⟨α, hα⟩ := integral_of_disjoint_infty hρ1 z₀ zi hi1 a1 ha1 d0i
  obtain ⟨ρ2, hρ2, hv2⟩ := hTr p 𝒵 ρ1 hρ1 (-α)
  have h20 : ρ2.val z₀ = OnePoint.some (iq p 0) := by
    rw [hv2, hα, OnePoint.map_some, map_neg, add_neg_cancel, map_zero]
  have h2i : ρ2.val zi = OnePoint.infty := by rw [hv2, hi1]; rfl
  have h21 : ρ2.val z₁ = (c1.map (fun s => s + zlocToRat p (-α))).map (algebraMap ℚ Qbar) := by
    rw [hv2, hc1, rat_shift]
  obtain ⟨γ, hγ⟩ := integral_of_disjoint_infty hρ2 z₁ zi h2i _ h21 di1.symm
  have hγu : IsUnit γ := by
    simpa using isUnit_of_vals hρ2 z₁ z₀ γ 0 hγ h20 d01.symm
  obtain ⟨μ, hμ⟩ := exists_unit_neg_16_27 hp3
  let u : (Zloc p)ˣ := μ * hγu.unit⁻¹
  refine ⟨scale 𝒵 ρ2 u, isP1Coordinate_scale hρ2 u, ?_, ?_, ?_⟩
  · rw [val_scale, h20, OnePoint.map_some, map_zero, mul_zero]
  · rw [val_scale, h2i]; rfl
  · rw [val_scale, hγ, OnePoint.map_some, ← map_mul]
    congr 1
    rw [← hμ]
    congr 1
    show (↑(μ * hγu.unit⁻¹) : Zloc p) * γ = ↑μ
    rw [Units.val_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]

end MCRQuot

namespace MCRQuot

open MCRGlue ModelGlue

/-- **`ModelCoordinateResidue` with `P1ThreePoints` replaced by the translation glue
`P1Translate`** (the composite of `modelCoordinateResidue_of_mcrQuot` and `p1ThreePoints_of`). -/
theorem modelCoordinateResidue_of_mcrQuot' (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (gB : GenericQuotientP1)
    (hfix : FibreAutFixFinite) (hcnt : TwistClassCard) (hO : GQuotientPointOrbits)
    (hI : CMStabInvolution) (hS : StabFixesClosure) (hC : QbarPointsConjugate)
    (hTr : P1Translate) : ModelCoordinateResidue :=
  modelCoordinateResidue_of_mcrQuot hAF hQE hTS hP1 hFix hCyc hT gB hfix hcnt hO hI hS hC
    (p1ThreePoints_of hTr)

/-- **Glue C2 from T5, glue A and the translation glue.** -/
theorem coordinateFromSections_of' (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
    (hTr : P1Translate) : CoordinateFromSections :=
  coordinateFromSections_of hA hT (p1ThreePoints_of hTr)

/-- **Main composite: `ModelCoordinateResidue` with none of mcr-glue's glue Props A, B, C1, C2**:
from the leaves L1-L6 of mcr-glue, the kernel's textbook leaf `TorsionStructure` (T5), and the
smaller glue of this task: (A-fix) `FibreAutFixFinite`, (A-count) `TwistClassCard`,
(B-desc) `QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1a) `GQuotientPointOrbits`,
(C1b) `CMStabInvolution`, (C1c) `StabFixesClosure`, (C1d) `QbarPointsConjugate`,
(C2-T) `P1Translate`. -/
theorem modelCoordinateResidue_of_mcrQuot'' (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure)
    (hfix : FibreAutFixFinite) (hcnt : TwistClassCard) (hD : QuotientDescendsQ)
    (hB : ToP1BijIsCoordinateQ) (hO : GQuotientPointOrbits) (hI : CMStabInvolution)
    (hS : StabFixesClosure) (hC : QbarPointsConjugate) (hTr : P1Translate) :
    ModelCoordinateResidue :=
  modelCoordinateResidue_of_mcrQuot' hAF hQE hTS hP1 hFix hCyc hT
    (genericQuotientP1_of (fibreAutTame_of hT hfix hcnt) hT hTS hD hB) hfix hcnt hO hI hS hC hTr

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 10: proofs of some of the new glue Props
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open scoped Pointwise

/-! ## (C1a) `GQuotientPointOrbits`, proved -/

/-- **(C1a) proved: the points over a point of an SGA 1 quotient form one orbit.** On an affine
`W ⊆ Z` with `U = q⁻¹W`, the primes of `x, x'` lie over the same prime of `Γ(Z, W) = Γ(X, U)^G`
(`comap_primeIdealOf_appLE`), so they differ by `g ∈ G` (`exists_smul_of_under_eq`), and the
prime of `g x` is the `g`-translate of the prime of `x`. -/
theorem gQuotientPointOrbits : GQuotientPointOrbits := by
  intro X Z G q hfin hq x x' hxx
  have hq' := hq
  obtain ⟨hinv, haff, hsec⟩ := hq
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hxW, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q x)) isOpen_univ
  set U := q ⁻¹ᵁ W with hUdef
  have hU : IsAffineOpen U := hW.preimage q
  have hx : x ∈ U := hxW
  have hx' : x' ∈ U := by
    change q x' ∈ W
    rw [← hxx]; exact hxW
  letI : MulSemiringAction G Γ(X, U) := secAction hinv W
  letI : Algebra Γ(Z, W) Γ(X, U) := (q.app W).hom.toAlgebra
  haveI : SMulCommClass G Γ(Z, W) Γ(X, U) := by
    constructor
    intro g a b
    change secMap _ _ W (q.app W a * b) = q.app W a * secMap _ _ W b
    rw [map_mul, secMap_app]
  haveI : Algebra.IsInvariant Γ(Z, W) Γ(X, U) G := by
    constructor
    intro b hb
    have hmem : b ∈ Set.range (q.app W) := by
      rw [(hsec W hW).2]
      intro g hg
      have := hb ⟨g⁻¹, G.inv_mem hg⟩
      change secMap _ _ W b = b at this
      rw [secMap_congr (f' := g.asIso.hom) (by simp) _ (hinv g hg)] at this
      exact this
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha⟩
  have hcomap : ∀ (u : X) (hu : u ∈ U),
      (hU.primeIdealOf ⟨u, hu⟩).asIdeal.under Γ(Z, W) = (hW.primeIdealOf ⟨q u, hu⟩).asIdeal := by
    intro u hu
    have e := IsAffineOpen.comap_primeIdealOf_appLE (f := q) W hW U hU le_rfl hu
    rw [← e]
    change Ideal.comap (q.app W).hom _ = Ideal.comap (q.appLE W U le_rfl).hom _
    rw [Scheme.Hom.app_eq_appLE]
  have hunder : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.under Γ(Z, W) =
      (hU.primeIdealOf ⟨x', hx'⟩).asIdeal.under Γ(Z, W) := by
    rw [hcomap, hcomap]
    congr 3
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq Γ(Z, W) Γ(X, U) G _ _ hunder
  have hgx : (g : Aut X).asIso.hom x ∈ U := by
    change q ((g : Aut X).asIso.hom x) ∈ W
    rw [← Scheme.Hom.comp_apply, hinv g g.2]; exact hxW
  have e3 := IsAffineOpen.comap_primeIdealOf_appLE (f := (g : Aut X).asIso.hom) U hU U hU
    (preimage_le_of_comp_eq (hinv g g.2) W) hx
  have hpr : hU.primeIdealOf ⟨x', hx'⟩ = hU.primeIdealOf ⟨(g : Aut X).asIso.hom x, hgx⟩ := by
    apply PrimeSpectrum.ext
    rw [hg, ← e3]
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    change secMap _ _ W b ∈ _ ↔ _
    rw [secMap_congr (f' := (g : Aut X).asIso.hom) (by simp) _ (hinv g g.2)]
    rfl
  have e4 := congrArg hU.fromSpec hpr
  rw [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf] at e4
  have e5 : x' = (g : Aut X).asIso.hom x := e4
  refine ⟨(g : Aut X)⁻¹, G.inv_mem g.2, ?_⟩
  simp only [Aut.inv_asIso, Iso.symm_hom]
  rw [e5, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-! ## (C1d) `QbarPointsConjugate`, proved -/

/-- Two embeddings of a field into `ℚ̄` differ by an automorphism of `ℚ̄` (`AlgHom.liftNormal`). -/
theorem exists_algEquiv_comp_eq {K : Type} [Field K] (f1 f2 : K →+* Qbar) :
    ∃ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ k, f2 k = σ (f1 k) := by
  have : CharZero K := f1.charZero
  let _ : Algebra ℚ K := DivisionRing.toRatAlgebra
  let f1' : K →ₐ[ℚ] Qbar := f1.toRatAlgHom
  let f2' : K →ₐ[ℚ] Qbar := f2.toRatAlgHom
  let e1 := AlgEquiv.ofInjectiveField f1'
  let e2 := AlgEquiv.ofInjectiveField f2'
  let χ : f1'.fieldRange →ₐ[ℚ] f2'.fieldRange := e2.toAlgHom.comp e1.symm.toAlgHom
  refine ⟨AlgEquiv.ofBijective (χ.liftNormal Qbar)
    (Algebra.IsAlgebraic.algHom_bijective _), fun k => ?_⟩
  have h := AlgHom.liftNormal_commutes χ Qbar (e1 k)
  have h1 : algebraMap f1'.fieldRange Qbar (e1 k) = f1 k := rfl
  have h2 : χ (e1 k) = e2 k := by
    show e2 (e1.symm (e1 k)) = e2 k
    rw [AlgEquiv.symm_apply_apply]
  rw [h1, h2] at h
  exact h.symm

/-- **(C1d) proved: two `ℚ̄`-points with the same underlying point are Galois conjugate.** -/
theorem qbarPointsConjugate : QbarPointsConjugate := by
  intro X y y' h
  set S := Scheme.SpecToEquivOfField Qbar X with hS
  have e : (S y').1 = (S y).1 := h.symm
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp_eq
    ((X.residueFieldCongr e).hom ≫ (S y).2).hom (S y').2.hom
  refine ⟨σ, S.injective ?_⟩
  rw [specToEquivOfField_comp, Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨e, ?_⟩
  ext k
  exact hσ k

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 11: (A-count) `TwistClassCard`, proved from T5
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- The normalizer fact of the kernel (`NormO.normalizerFinite`) with its explicit set
`NormO.T = {1, i, j, ij}` (the same proof). -/
theorem normalizer_T (u : Bˣ) (hu : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) :
    ∃ t ∈ NormO.T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B) := by
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((NormO.sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : NormO.IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ :=
    NormO.descent _ (NormO.sc _ hm0 * u) n hu0 rfl ((NormO.isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((NormO.sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

theorem ncard_T_le : (NormO.T : Set Bˣ).ncard ≤ 4 := by
  simp only [NormO.T]
  refine (Set.ncard_insert_le _ _).trans ?_
  refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
  refine (Nat.succ_le_succ (Nat.succ_le_succ (Set.ncard_insert_le _ _))).trans ?_
  simp

/-- **`AutOInnerFinite` with a cardinality bound** (the kernel's
`AutOExt.autOInnerFinite_of_normalizer`, same proof, for `NormO.T`): every automorphism of `𝒪` is,
up to conjugation by a unit, one of at most 4. -/
theorem autOInnerCard : ∃ T' : Set (O ≃+* O), T'.Finite ∧ T'.ncard ≤ 4 ∧
    ∀ α : O ≃+* O, ∃ t ∈ T', ∃ v : Oˣ, ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O) := by
  classical
  let T := (NormO.T : Set Bˣ)
  have hT : T.Finite := NormO.T_finite
  let P : (O ≃+* O) → Bˣ → Prop := fun β t => ∀ a : O, ((β a : O) : B) * t = t * a
  let T' : Set (O ≃+* O) := {β | ∃ t ∈ T, P β t}
  let f : (O ≃+* O) → Bˣ := fun β => if h : ∃ t ∈ T, P β t then Classical.choose h else 1
  have hf : ∀ β ∈ T', f β ∈ T ∧ P β (f β) := by
    intro β hβ
    have hβ' : ∃ t ∈ T, P β t := hβ
    simp only [f, hβ', dite_true]
    exact Classical.choose_spec hβ'
  have hinj : Set.InjOn f T' := by
    intro β₁ h₁ β₂ h₂ heq
    apply RingEquiv.ext; intro a
    apply Subtype.ext
    have e1 := (hf β₁ h₁).2 a
    have e2 := (hf β₂ h₂).2 a
    rw [heq] at e1
    exact (Units.mul_left_inj (f β₂)).1 (e1.trans e2.symm)
  have hmaps : Set.MapsTo f T' T := fun β hβ => (hf β hβ).1
  have hT' : T'.Finite := Set.Finite.of_finite_image (hT.subset (hmaps.image_subset)) hinj
  refine ⟨T', hT', (Set.ncard_le_ncard_of_injOn f hmaps hinj hT).trans ncard_T_le, fun α => ?_⟩
  obtain ⟨u, hu⟩ := AutOExt.conj_of_skolem α
  have hback : ∀ b : B, AutOExt.extFun α.symm (AutOExt.extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (AutOExt.extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, AutOExt.extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show AutOExt.extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, AutOExt.extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := normalizer_T u hnorm
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← AutOExt.extFun_coe, hu, Units.inv_mul_cancel_right]
  let β : O ≃+* O := α.trans (AutOExt.conjUnit v)
  have hβ : ∀ a : O, β a = ((v⁻¹ : Oˣ) : O) * α a * v := fun a => rfl
  refine ⟨β, ⟨t, ht, fun a => ?_⟩, v, fun a => ?_⟩
  · have hvv : (((v⁻¹ : Oˣ) : O) : B) * ((v : O) : B) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul]; rfl
    have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    have h := hrel a
    rw [huq] at h
    rw [hβ, MulMemClass.coe_mul, MulMemClass.coe_mul]
    exact AutOExt.key_conj _ _ _ _ _ _ _ hvv hcc (Algebra.commutes q _) h
  · rw [hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

/-- **(A-count) proved from T5: a twist class has at most `4 · 81 = 324` isomorphism classes.** -/
theorem twistClassCard (hT : ObjBridge.TorsionStructure) : TwistClassCard := by
  classical
  intro P
  obtain ⟨T', hT'fin, hT'card, hT'⟩ := autOInnerCard
  haveI : Fintype T' := hT'fin.fintype
  set S := {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧ TwistEq P Q} with hSdef
  let S' : T' → (Fin 4 → ZMod 3) → Set (M3 Qbar) := fun t c =>
    {m | ∃ e : Level3 (P.q.twist (t : O ≃+* O)),
      (∀ a, e.eta a = (P.e.twist (t : O ≃+* O)).eta (a * liftO c)) ∧
      m = M3.mk ⟨P.A, P.surface, P.q.twist (t : O ≃+* O), e⟩}
  have hsub : ∀ t c, (S' t c).Subsingleton := by
    rintro t c _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have : e = e' := Level3.ext' (DFunLike.ext _ _ fun a => (he a).trans (he' a).symm)
    rw [this]
  let F : T' × (Fin 4 → ZMod 3) → M3 Qbar := fun tc =>
    if h : (S' tc.1 tc.2).Nonempty then h.some else M3.mk P
  have hcover : S ⊆ Set.range F := by
    rintro m ⟨Q, rfl, α, ⟨f⟩⟩
    obtain ⟨t, ht, v, hv⟩ := hT' α
    let f' : QMIso (P.q.twist t) Q.q := (conjUnitIso P.q t α v hv).trans f
    let e' : Level3 (P.q.twist t) := _root_.LeafQM.AV.Pin.transportLevel f'.symm Q.e
    have hiso : Q.Iso ⟨P.A, P.surface, P.q.twist t, e'⟩ := QML3.isoTransport Q P.surface f'.symm
    obtain ⟨u₀, v₀, -, hlin⟩ := Level3.torsor hT (P.twist t) e'
    obtain ⟨c, k, hk⟩ := exists_liftO_congr u₀
    have hmem : M3.mk Q ∈ S' ⟨t, ht⟩ c := by
      refine ⟨e', fun a => (hlin a).trans ?_, Quotient.sound ⟨hiso⟩⟩
      change (P.e.twist t).eta (a * u₀) = (P.e.twist t).eta (a * liftO c)
      rw [(P.e.twist t).eq_iff]
      refine ⟨a * k, ?_⟩
      calc a * u₀ - a * liftO c = a * (u₀ - liftO c) := by noncomm_ring
        _ = a * (3 * k) := by rw [hk]
        _ = 3 * (a * k) := by noncomm_ring
    refine ⟨(⟨t, ht⟩, c), ?_⟩
    have hne : (S' ⟨t, ht⟩ c).Nonempty := ⟨_, hmem⟩
    simp only [F, hne, dite_true]
    exact hsub ⟨t, ht⟩ c hne.some_mem hmem
  have hfinR : (Set.range F).Finite := Set.finite_range F
  refine ⟨hfinR.subset hcover, ?_⟩
  calc S.ncard ≤ (Set.range F).ncard := Set.ncard_le_ncard hcover hfinR
    _ ≤ Nat.card (T' × (Fin 4 → ZMod 3)) := by
      rw [← Set.image_univ, ← Set.ncard_univ]
      exact Set.ncard_image_le Set.finite_univ
    _ = T'.ncard * 81 := by
      rw [Nat.card_prod, Nat.card_coe_set_eq]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    _ ≤ 4 * 81 := Nat.mul_le_mul_right _ hT'card
    _ = 324 := by norm_num

/-- **Glue A from T5 and (A-fix) alone.** -/
theorem fibreAutTame_of' (hT : ObjBridge.TorsionStructure) (hfix : FibreAutFixFinite) :
    FibreAutTame :=
  fibreAutTame_of hT hfix (twistClassCard hT)

/-- **Glue C1 from glue A, (A-fix), (C1b), (C1c)** ((C1a), (C1d) proved). -/
theorem cMSectionsDisjoint_of' (hA : FibreAutTame) (hfix : FibreAutFixFinite)
    (hI : CMStabInvolution) (hS : StabFixesClosure) : CMSectionsDisjoint :=
  cMSectionsDisjoint_of hA hfix gQuotientPointOrbits hI hS qbarPointsConjugate

/-- **Main composite (final form): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaf T5 and six glue Props of this task**: (A-fix) `FibreAutFixFinite`, (B-desc)
`QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b) `CMStabInvolution`, (C1c)
`StabFixesClosure`, (C2-T) `P1Translate`. (A-count), (C1a), (C1d) are proved. -/
theorem modelCoordinateResidue_final (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure)
    (hfix : FibreAutFixFinite) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hI : CMStabInvolution) (hS : StabFixesClosure) (hTr : P1Translate) :
    ModelCoordinateResidue :=
  modelCoordinateResidue_of_mcrQuot'' hAF hQE hTS hP1 hFix hCyc hT hfix (twistClassCard hT) hD hB
    gQuotientPointOrbits hI hS qbarPointsConjugate hTr

end MCRQuot
