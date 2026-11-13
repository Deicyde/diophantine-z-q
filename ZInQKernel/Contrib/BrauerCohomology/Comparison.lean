import ZInQKernel.Contrib.BrauerCohomology.TopHomology
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

/-!
# Continuous `H²` with trivial coefficients as explicit cocycles modulo coboundaries

Mathlib's `continuousCohomology 2 X` is the homology, in `TopModuleCat`, of the complex of
*homogeneous* cochains: degree `n` is the `G`-invariant part of the iterated coinduction
`C(G, C(G, …, C(G, X)))` (`n + 1` factors), with `d₀ = const` and `dₙ₊₁ F = const F - dₙ ∘ F`.

For a topological group `G` and a topological representation `X` with **trivial** action, this file
identifies that homology with the classical description by *inhomogeneous* continuous cochains:

* a 2-cochain `ε : G → G → X` is a cocycle (`IsInhCocycle2`) if `(a, b) ↦ ε a b` is continuous on
  `G × G` and `ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0`;
* it is a coboundary (`IsInhCoboundary2`) if `ε a b = f b - f (a * b) + f a` for a continuous
  `f : G → X`.

These are, verbatim, the predicates `PkgI6.IsCocycle2` / `PkgI6.IsCoboundary2` of
`ZInQKernel/HDecomp/Conductor/I6Base.lean`, with `ZMod 2` replaced by the carrier of `X`.

The dictionary is `ε ↦ ((x₀, x₁, x₂) ↦ ε (x₀⁻¹ x₁) (x₁⁻¹ x₂))` with inverse
`F ↦ ((a, b) ↦ F 1 a (a b))`. Under it, Mathlib's homogeneous differential evaluated at
`(1, a, a b, a b c)` is the inhomogeneous cocycle expression above, and the image of a homogeneous
1-cochain `E` evaluated at `(1, a, a b)` is `f b - f (a b) + f a` with `f = E 1`, so no sign or
order convention is changed. Uncurrying requires `[LocallyCompactSpace G]` (true for profinite
groups such as absolute Galois groups).

## Main results

* `d12_apply`, `d23_apply`: Mathlib's differentials in homogeneous coordinates;
* `d23_toHC2_eq_zero_iff`: the homogeneous cocycle condition is the inhomogeneous one;
* `cls`: the class in `continuousCohomology 2 X` of an inhomogeneous cocycle;
* `cls_surjective`: every class is of this form (`G` locally compact);
* `cls_eq_zero_iff`: the class vanishes iff the cocycle is a coboundary;
* `cls_sub`: additivity;
* `isInhCocycle2_iff_isLocallyConstant`, `isInhCoboundary2_iff_isLocallyConstant`: for discrete
  coefficients, continuity of cochains is local constancy.

Naturality (`map_cls`, covering localization, inflation and coefficient maps) and the additive
equivalence `h2AddEquiv : Z²/B² ≃+ continuousCohomology 2 X` are in `Functoriality.lean`.
-/

open CategoryTheory ContRepresentation

namespace ZInQ.Contrib.BrauerCohomology

universe u v

section Predicates

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*} [AddCommGroup M]
  [TopologicalSpace M]

/-- Continuous inhomogeneous 2-cocycle with trivial action (spelling of `PkgI6.IsCocycle2`). -/
def IsInhCocycle2 (ε : G → G → M) : Prop :=
  Continuous (fun x : G × G => ε x.1 x.2) ∧ ∀ a b c, ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0

/-- Coboundary of a continuous 1-cochain (spelling of `PkgI6.IsCoboundary2`). -/
def IsInhCoboundary2 (ε : G → G → M) : Prop :=
  ∃ f : G → M, Continuous f ∧ ∀ a b, ε a b = f b - f (a * b) + f a

/-- For discrete coefficients, "continuous" is "locally constant": an inhomogeneous cocycle is a
locally constant function on `G × G` satisfying the cocycle identity. -/
theorem isInhCocycle2_iff_isLocallyConstant [DiscreteTopology M] (ε : G → G → M) :
    IsInhCocycle2 ε ↔ IsLocallyConstant (Function.uncurry ε) ∧
      ∀ a b c, ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0 := by
  rw [IsInhCocycle2, IsLocallyConstant.iff_continuous]
  rfl

/-- For discrete coefficients, coboundaries of continuous 1-cochains are coboundaries of locally
constant 1-cochains. -/
theorem isInhCoboundary2_iff_isLocallyConstant [DiscreteTopology M] (ε : G → G → M) :
    IsInhCoboundary2 ε ↔
      ∃ f : G → M, IsLocallyConstant f ∧ ∀ a b, ε a b = f b - f (a * b) + f a := by
  simp only [IsInhCoboundary2, IsLocallyConstant.iff_continuous]

theorem IsInhCocycle2.sub [IsTopologicalAddGroup M] {ε₁ ε₂ : G → G → M}
    (h₁ : IsInhCocycle2 ε₁) (h₂ : IsInhCocycle2 ε₂) :
    IsInhCocycle2 (ε₁ - ε₂) := by
  refine ⟨h₁.1.sub h₂.1, fun a b c => ?_⟩
  simp only [Pi.sub_apply]
  have e₁ := h₁.2 a b c
  have e₂ := h₂.2 a b c
  calc ε₁ b c - ε₂ b c - (ε₁ (a * b) c - ε₂ (a * b) c) + (ε₁ a (b * c) - ε₂ a (b * c)) -
        (ε₁ a b - ε₂ a b)
      = (ε₁ b c - ε₁ (a * b) c + ε₁ a (b * c) - ε₁ a b) -
        (ε₂ b c - ε₂ (a * b) c + ε₂ a (b * c) - ε₂ a b) := by abel
    _ = 0 := by rw [e₁, e₂, sub_zero]

theorem IsInhCocycle2.zero : IsInhCocycle2 (0 : G → G → M) :=
  ⟨continuous_const, fun _ _ _ => by simp⟩

theorem IsInhCoboundary2.isInhCocycle2 [ContinuousMul G] [IsTopologicalAddGroup M]
    {ε : G → G → M} (h : IsInhCoboundary2 ε) : IsInhCocycle2 ε := by
  obtain ⟨f, hf, e⟩ := h
  refine ⟨?_, fun a b c => ?_⟩
  · have : (fun x : G × G => ε x.1 x.2) = fun x => f x.2 - f (x.1 * x.2) + f x.1 :=
      funext fun x => e x.1 x.2
    rw [this]
    exact ((hf.comp continuous_snd).sub (hf.comp (continuous_fst.mul continuous_snd))).add
      (hf.comp continuous_fst)
  · rw [e, e, e, e, mul_assoc]
    abel

end Predicates

section Homogeneous

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep k G)

/-- `X` has trivial `G`-action. -/
abbrev IsTrivialAction : Prop := ∀ (g : G) (v : X), X.ρ g v = v

/-- Degree-1 homogeneous cochains (the term of `TopRep.homogeneousCochains X` in degree `1`). -/
abbrev HC1 := ↥(X.ρ.coind₁.coind₁).invariants

/-- Degree-2 homogeneous cochains (the term of `TopRep.homogeneousCochains X` in degree `2`). -/
abbrev HC2 := ↥(X.ρ.coind₁.coind₁.coind₁).invariants

/-- Homogeneous form `(x₀, x₁) ↦ f (x₀⁻¹ x₁)` of an inhomogeneous 1-cochain. -/
def homog1 (f : G → X) (hf : Continuous f) : C(G, C(G, X)) :=
  ContinuousMap.curry ⟨fun p : G × G => f (p.1⁻¹ * p.2),
    hf.comp (continuous_fst.inv.mul continuous_snd)⟩

@[simp]
theorem homog1_apply (f : G → X) (hf : Continuous f) (x₀ x₁ : G) :
    homog1 X f hf x₀ x₁ = f (x₀⁻¹ * x₁) := rfl

/-- Homogeneous form `(x₀, x₁, x₂) ↦ ε (x₀⁻¹ x₁) (x₁⁻¹ x₂)` of an inhomogeneous 2-cochain. -/
def homog2 (ε : G → G → X) (hε : Continuous (fun p : G × G => ε p.1 p.2)) :
    C(G, C(G, C(G, X))) :=
  ContinuousMap.curry (ContinuousMap.curry
    ⟨fun p : (G × G) × G => ε (p.1.1⁻¹ * p.1.2) (p.1.2⁻¹ * p.2),
      hε.comp (((continuous_fst.comp continuous_fst).inv.mul
        (continuous_snd.comp continuous_fst)).prodMk
        ((continuous_snd.comp continuous_fst).inv.mul continuous_snd))⟩)

@[simp]
theorem homog2_apply (ε : G → G → X) (hε : Continuous (fun p : G × G => ε p.1 p.2))
    (x₀ x₁ x₂ : G) : homog2 X ε hε x₀ x₁ x₂ = ε (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) := rfl

variable {X}

theorem homog1_mem (hX : IsTrivialAction X) (f : G → X) (hf : Continuous f) :
    homog1 X f hf ∈ (X.ρ.coind₁.coind₁).invariants := by
  intro g
  ext x₀ x₁
  simp only [coind₁_apply_apply, hX, homog1_apply, mul_inv_rev, inv_inv, mul_assoc,
    mul_inv_cancel_left]

theorem homog2_mem (hX : IsTrivialAction X) (ε : G → G → X)
    (hε : Continuous (fun p : G × G => ε p.1 p.2)) :
    homog2 X ε hε ∈ (X.ρ.coind₁.coind₁.coind₁).invariants := by
  intro g
  ext x₀ x₁ x₂
  simp only [coind₁_apply_apply, hX, homog2_apply, mul_inv_rev, inv_inv, mul_assoc,
    mul_inv_cancel_left]

/-- Invariance of a homogeneous 1-cochain, in coordinates. -/
theorem HC1.apply_eq (hX : IsTrivialAction X) (E : HC1 X) (x₀ x₁ : G) :
    E.1 x₀ x₁ = E.1 1 (x₀⁻¹ * x₁) := by
  have h := congrArg (fun F : C(G, C(G, X)) => F x₀ x₁) (E.2 x₀)
  simp only [coind₁_apply_apply, hX, inv_mul_cancel] at h
  exact h.symm

/-- Invariance of a homogeneous 2-cochain, in coordinates. -/
theorem HC2.apply_eq (hX : IsTrivialAction X) (F : HC2 X) (x₀ x₁ x₂ : G) :
    F.1 x₀ x₁ x₂ = F.1 1 (x₀⁻¹ * x₁) (x₀⁻¹ * x₂) := by
  have h := congrArg (fun F' : C(G, C(G, C(G, X))) => F' x₀ x₁ x₂) (F.2 x₀)
  simp only [coind₁_apply_apply, hX, inv_mul_cancel] at h
  exact h.symm

/-- Mathlib's differential from degree 1 to degree 2, in homogeneous coordinates. -/
theorem d12_apply (E : HC1 X) (x₀ x₁ x₂ : G) :
    ((((TopRep.homogeneousCochains X).d 1 2).hom (E : HC1 X)) : HC2 X).1 x₀ x₁ x₂ =
      E.1 x₁ x₂ - (E.1 x₀ x₂ - E.1 x₀ x₁) := by
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [TopRep.hom_d_succ, TopRep.d_zero, TopRep.hom_ofHom, ContIntertwiningMap.sub_apply,
    ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]

/-- Mathlib's differential from degree 2 to degree 3, in homogeneous coordinates. -/
theorem d23_apply (F : HC2 X) (x₀ x₁ x₂ x₃ : G) :
    ((((TopRep.homogeneousCochains X).d 2 3).hom (F : HC2 X)) :
        ↥(X.ρ.coind₁.coind₁.coind₁.coind₁).invariants).1 x₀ x₁ x₂ x₃ =
      F.1 x₁ x₂ x₃ - (F.1 x₀ x₂ x₃ - (F.1 x₀ x₁ x₃ - F.1 x₀ x₁ x₂)) := by
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [TopRep.hom_d_succ, TopRep.d_zero, TopRep.hom_ofHom, ContIntertwiningMap.sub_apply,
    ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]

end Homogeneous

section Coordinates

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : TopRep k G}

/-- Inhomogeneous coordinates `(a, b) ↦ F 1 a (a b)` of a homogeneous 2-cochain. -/
def inh2 (F : C(G, C(G, C(G, X)))) : G → G → X := fun a b => F 1 a (a * b)

theorem continuous_inh2 [LocallyCompactSpace G] (F : C(G, C(G, C(G, X)))) :
    Continuous (fun p : G × G => inh2 F p.1 p.2) :=
  (F 1).uncurry.continuous.comp (continuous_fst.prodMk (continuous_fst.mul continuous_snd))

theorem inh2_homog2 (ε : G → G → X) (hε : Continuous (fun p : G × G => ε p.1 p.2)) :
    inh2 (homog2 X ε hε) = ε := by
  funext a b
  simp [inh2, homog2_apply]

theorem homog2_inh2 [LocallyCompactSpace G] (hX : IsTrivialAction X) (F : HC2 X) :
    homog2 X (inh2 F.1) (continuous_inh2 F.1) = F.1 := by
  ext x₀ x₁ x₂
  rw [homog2_apply, HC2.apply_eq hX F x₀ x₁ x₂]
  simp only [inh2, mul_assoc, mul_inv_cancel_left]

/-- The homogeneous 1-cochain attached to a continuous inhomogeneous 1-cochain. -/
def toHC1 (hX : IsTrivialAction X) (f : G → X) (hf : Continuous f) : HC1 X :=
  ⟨homog1 X f hf, homog1_mem hX f hf⟩

/-- The homogeneous 2-cochain attached to a continuous inhomogeneous 2-cochain. -/
def toHC2 (hX : IsTrivialAction X) (ε : G → G → X)
    (hε : Continuous (fun p : G × G => ε p.1 p.2)) : HC2 X :=
  ⟨homog2 X ε hε, homog2_mem hX ε hε⟩

@[simp]
theorem toHC2_apply (hX : IsTrivialAction X) (ε : G → G → X)
    (hε : Continuous (fun p : G × G => ε p.1 p.2)) (x₀ x₁ x₂ : G) :
    (toHC2 hX ε hε).1 x₀ x₁ x₂ = ε (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) := rfl

@[simp]
theorem toHC1_apply (hX : IsTrivialAction X) (f : G → X) (hf : Continuous f) (x₀ x₁ : G) :
    (toHC1 hX f hf).1 x₀ x₁ = f (x₀⁻¹ * x₁) := rfl

/-- **The homogeneous cocycle condition is the inhomogeneous one.** -/
theorem d23_toHC2_eq_zero_iff (hX : IsTrivialAction X) (ε : G → G → X)
    (hε : Continuous (fun p : G × G => ε p.1 p.2)) :
    ((TopRep.homogeneousCochains X).d 2 3).hom (toHC2 hX ε hε : HC2 X) = 0 ↔
      ∀ a b c, ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0 := by
  constructor
  · intro h a b c
    have e := congrArg
      (fun z : ↥(X.ρ.coind₁.coind₁.coind₁.coind₁).invariants => z.1 1 a (a * b) (a * b * c)) h
    rw [d23_apply] at e
    simp only [toHC2_apply, inv_one, one_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left,
      ZeroMemClass.coe_zero, ContinuousMap.zero_apply] at e
    calc ε b c - ε (a * b) c + ε a (b * c) - ε a b
        = ε b c - (ε (a * b) c - (ε a (b * c) - ε a b)) := by abel
      _ = 0 := e
  · intro h
    apply Subtype.ext
    ext x₀ x₁ x₂ x₃
    rw [d23_apply]
    simp only [toHC2_apply]
    have e := h (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) (x₂⁻¹ * x₃)
    have h1 : x₀⁻¹ * x₁ * (x₁⁻¹ * x₂) = x₀⁻¹ * x₂ := by simp [mul_assoc]
    have h2 : x₁⁻¹ * x₂ * (x₂⁻¹ * x₃) = x₁⁻¹ * x₃ := by simp [mul_assoc]
    rw [h1, h2] at e
    change ε (x₁⁻¹ * x₂) (x₂⁻¹ * x₃) - (ε (x₀⁻¹ * x₂) (x₂⁻¹ * x₃) -
      (ε (x₀⁻¹ * x₁) (x₁⁻¹ * x₃) - ε (x₀⁻¹ * x₁) (x₁⁻¹ * x₂))) = 0
    rw [← e]
    abel

end Coordinates

section Classes

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : TopRep k G}

/-- The cycle attached to an inhomogeneous cocycle. -/
noncomputable def cyc2 (hX : IsTrivialAction X) (ε : G → G → X) (hε : IsInhCocycle2 ε) :
    (TopRep.homogeneousCochains X).cycles 2 :=
  TopHom.cyclesMkOfEq' (TopRep.homogeneousCochains X) (toHC2 hX ε hε.1 : HC2 X) 3 (by simp)
    ((d23_toHC2_eq_zero_iff hX ε hε.1).2 hε.2)

theorem iCycles_cyc2 (hX : IsTrivialAction X) (ε : G → G → X) (hε : IsInhCocycle2 ε) :
    (TopRep.homogeneousCochains X).iCycles 2 (cyc2 hX ε hε) = (toHC2 hX ε hε.1 : HC2 X) :=
  TopHom.iCycles_cyclesMkOfEq' _ _ _ _ _

/-- **The class in Mathlib's `continuousCohomology 2 X` of an inhomogeneous cocycle.** -/
noncomputable def cls (hX : IsTrivialAction X) (ε : G → G → X) (hε : IsInhCocycle2 ε) :
    continuousCohomology 2 X :=
  (TopRep.homogeneousCochains X).homologyπ 2 (cyc2 hX ε hε)

/-- **Every class of `continuousCohomology 2 X` is the class of an inhomogeneous cocycle.** -/
theorem cls_surjective [LocallyCompactSpace G] (hX : IsTrivialAction X)
    (x : continuousCohomology 2 X) : ∃ ε, ∃ hε : IsInhCocycle2 ε, cls hX ε hε = x := by
  obtain ⟨z, rfl⟩ := TopHom.homologyπ_surjective' (TopRep.homogeneousCochains X) (n := 2) x
  let F : HC2 X := (TopRep.homogeneousCochains X).iCycles 2 z
  have hF : ((TopRep.homogeneousCochains X).d 2 3).hom (F : HC2 X) = 0 :=
    TopHom.d_iCycles_apply _ 3 z
  have hF' : toHC2 hX (inh2 F.1) (continuous_inh2 F.1) = F := Subtype.ext (homog2_inh2 hX F)
  have hc : ∀ a b c, inh2 F.1 b c - inh2 F.1 (a * b) c + inh2 F.1 a (b * c) - inh2 F.1 a b = 0 :=
    (d23_toHC2_eq_zero_iff hX _ (continuous_inh2 F.1)).1 (by rw [hF']; exact hF)
  have hε : IsInhCocycle2 (inh2 F.1) := ⟨continuous_inh2 F.1, hc⟩
  refine ⟨inh2 F.1, hε, ?_⟩
  unfold cls
  congr 1
  apply TopHom.iCycles_injective'
  rw [iCycles_cyc2]
  exact hF'

/-- **A class vanishes iff the cocycle is a coboundary of a continuous 1-cochain.** -/
theorem cls_eq_zero_iff (hX : IsTrivialAction X) (ε : G → G → X) (hε : IsInhCocycle2 ε) :
    cls hX ε hε = 0 ↔ IsInhCoboundary2 ε := by
  unfold cls
  rw [TopHom.homologyπ_eq_zero_iff' _ (m := 1) (by simp)]
  constructor
  · rintro ⟨E, hE⟩
    have h1 : (((TopRep.homogeneousCochains X).d 1 2).hom E : HC2 X) = toHC2 hX ε hε.1 := by
      have e := congrArg ((TopRep.homogeneousCochains X).iCycles 2).hom hE
      rw [TopHom.iCycles_toCycles_apply] at e
      rw [e]
      exact iCycles_cyc2 hX ε hε
    let E' : HC1 X := E
    refine ⟨fun a => E'.1 1 a, (E'.1 1).continuous, fun a b => ?_⟩
    have e := congrArg (fun F : HC2 X => F.1 1 a (a * b)) h1
    rw [d12_apply, HC1.apply_eq hX E' a (a * b)] at e
    simp only [toHC2_apply, inv_one, one_mul, inv_mul_cancel_left] at e
    rw [← e]
    show E'.1 1 b - (E'.1 1 (a * b) - E'.1 1 a) = E'.1 1 b - E'.1 1 (a * b) + E'.1 1 a
    abel
  · rintro ⟨f, hf, hfε⟩
    refine ⟨(toHC1 hX f hf : HC1 X), ?_⟩
    apply TopHom.iCycles_injective'
    rw [TopHom.iCycles_toCycles_apply, iCycles_cyc2]
    apply Subtype.ext
    ext x₀ x₁ x₂
    rw [d12_apply]
    simp only [toHC1_apply, toHC2_apply, hfε]
    have h1 : x₀⁻¹ * x₁ * (x₁⁻¹ * x₂) = x₀⁻¹ * x₂ := by simp [mul_assoc]
    rw [h1]
    abel

theorem cyc2_sub (hX : IsTrivialAction X) {ε₁ ε₂ : G → G → X} (h₁ : IsInhCocycle2 ε₁)
    (h₂ : IsInhCocycle2 ε₂) :
    cyc2 hX (ε₁ - ε₂) (h₁.sub h₂) = cyc2 hX ε₁ h₁ - cyc2 hX ε₂ h₂ := by
  apply TopHom.iCycles_injective'
  rw [map_sub, iCycles_cyc2, iCycles_cyc2, iCycles_cyc2]
  apply Subtype.ext
  ext x₀ x₁ x₂
  rfl

theorem cls_sub (hX : IsTrivialAction X) {ε₁ ε₂ : G → G → X} (h₁ : IsInhCocycle2 ε₁)
    (h₂ : IsInhCocycle2 ε₂) :
    cls hX (ε₁ - ε₂) (h₁.sub h₂) = cls hX ε₁ h₁ - cls hX ε₂ h₂ := by
  unfold cls
  rw [cyc2_sub hX h₁ h₂, map_sub]

/-- The class does not depend on the proof of the cocycle condition, and is a function of `ε`. -/
theorem cls_congr (hX : IsTrivialAction X) {ε₁ ε₂ : G → G → X} (h : ε₁ = ε₂)
    (h₁ : IsInhCocycle2 ε₁) (h₂ : IsInhCocycle2 ε₂) : cls hX ε₁ h₁ = cls hX ε₂ h₂ := by
  subst h; rfl

end Classes

end ZInQ.Contrib.BrauerCohomology
