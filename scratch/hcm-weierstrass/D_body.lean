
/-! ## The complex structure on `E(ℂ)` for a short Weierstrass model -/

namespace HCMW

open WeierstrassCurve.Affine (Point)
open scoped PeriodPair

/-- The properties of a uniformization `ξ : ℂ → E(ℂ)` used to build the atlas. -/
structure UnifProps (W : WeierstrassCurve ℂ) (Λ : AddSubgroup ℂ) (ξ : ℂ → W.toAffine.Point) : Prop where
  analyticUnif : ZInQ.Contrib.HCMDict.IsAnalyticUnif W Λ ξ
  fib : ∀ z w, ξ z = ξ w ↔ z - w ∈ Λ
  small : ∃ ε > 0, ∀ l ∈ Λ, ‖l‖ < ε → l = 0
  continuous : Continuous ξ
  isOpenMap : IsOpenMap ξ
  t2 : T2Space W.toAffine.Point
  chart : ∀ P, ∃ D : ChartDatum ξ, D.c = coordFor P ∧ P ∈ ξ '' D.e.source

theorem unifProps_toPoint (L : PeriodPair) :
    UnifProps L.weierstrassCurve L.lattice.toAddSubgroup (L.toPoint L.discriminant_ne_zero) where
  analyticUnif := ZInQ.Contrib.HCMDict.toPoint_isAnalyticUnif L
  fib := toPoint_eq_iff L
  small := ZInQ.Contrib.HCMDict.exists_lattice_small L
  continuous := continuous_toPoint L
  isOpenMap := isOpenMap_toPoint L
  t2 := inferInstance
  chart := exists_chartDatum_toPoint L

section Short

variable (W : WeierstrassCurve ℂ) [W.IsElliptic] [W.IsShortNF]

theorem exists_lattice_eq_short : ∃ L : PeriodPair, L.weierstrassCurve = W :=
  ZInQ.Contrib.HCMDict.exists_lattice_eq W WeierstrassCurve.IsShortNF.a₁
    WeierstrassCurve.IsShortNF.a₂ WeierstrassCurve.IsShortNF.a₃

theorem exists_unifProps : ∃ (Λ : AddSubgroup ℂ) (ξ : ℂ → W.toAffine.Point), UnifProps W Λ ξ := by
  obtain ⟨L, rfl⟩ := exists_lattice_eq_short W
  exact ⟨_, _, unifProps_toPoint L⟩

/-- The lattice of the chosen uniformization. -/
def unifΛ : AddSubgroup ℂ := (exists_unifProps W).choose

/-- A chosen uniformization `ℂ → E(ℂ)` (used only to prove that the coordinate charts are compatible). -/
def unif : ℂ → W.toAffine.Point := (exists_unifProps W).choose_spec.choose

theorem unif_props : UnifProps W (unifΛ W) (unif W) := (exists_unifProps W).choose_spec.choose_spec

instance : T2Space W.toAffine.Point := (unif_props W).t2

/-- The chart data whose coordinate is one of `x`, `y`, `t = -x/y`. -/
def coordData : Set (ChartDatum (unif W)) := {D | D.c = xC ∨ D.c = yC ∨ D.c = tC}

/-- The chart datum chosen at `P`, with coordinate `coordFor P`. -/
def chartDatumAt (P : W.toAffine.Point) : ChartDatum (unif W) := ((unif_props W).chart P).choose

theorem chartDatumAt_c (P : W.toAffine.Point) : (chartDatumAt W P).c = coordFor P :=
  ((unif_props W).chart P).choose_spec.1

theorem chartDatumAt_mem (P : W.toAffine.Point) : P ∈ unif W '' (chartDatumAt W P).e.source :=
  ((unif_props W).chart P).choose_spec.2

theorem chartDatumAt_coordData (P : W.toAffine.Point) : chartDatumAt W P ∈ coordData W := by
  simp only [coordData, mem_setOf_eq, chartDatumAt_c]
  cases P with
  | zero => exact Or.inr (Or.inr rfl)
  | some x y h =>
    by_cases hy : y = 0
    · exact Or.inr (Or.inl (by simp [coordFor, hy]))
    · exact Or.inl (by simp [coordFor, hy])

/-- **The complex atlas of `E(ℂ)`**: the charts are the coordinates `x` (away from `y = 0` and `O`),
`y` (at the points with `y = 0`) and `t = -x/y` (at `O`), each restricted to an open set of `E(ℂ)` on
which it is a homeomorphism onto an open subset of `ℂ`. -/
instance chartedSpacePoint : ChartedSpace ℂ W.toAffine.Point :=
  chartedSpaceOf (unif_props W).continuous (unif_props W).isOpenMap (coordData W) (chartDatumAt W)
    (chartDatumAt_coordData W) (chartDatumAt_mem W)

/-- Every chart of the atlas is given by the coordinate `x`, `y` or `t = -x/y`. -/
theorem atlas_coord {e : OpenPartialHomeomorph W.toAffine.Point ℂ} (he : e ∈ atlas ℂ W.toAffine.Point) :
    ⇑e = xC ∨ ⇑e = yC ∨ ⇑e = tC := by
  obtain ⟨D, hD, rfl⟩ := he
  exact hD

/-- The chart at `P` is the coordinate `coordFor P`: `t = -x/y` at `O`, `y` where `y = 0`, else `x`. -/
theorem chartAt_coe (P : W.toAffine.Point) : ⇑(chartAt ℂ P) = coordFor P := chartDatumAt_c W P

/-- **`E(ℂ)` is a complex manifold** (one-dimensional, analytic transition maps). -/
instance isManifoldPoint : IsManifold 𝓘(ℂ) ω W.toAffine.Point :=
  isManifoldOf (unif_props W).continuous (unif_props W).isOpenMap (unif_props W).fib (coordData W)
    (chartDatumAt W) (chartDatumAt_coordData W) (chartDatumAt_mem W)

theorem unif_isLocalDiffeomorph : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (unif W) :=
  isLocalDiffeomorph_of (unif_props W).continuous (unif_props W).isOpenMap (unif_props W).fib
    (coordData W) (chartDatumAt W) (chartDatumAt_coordData W) (chartDatumAt_mem W)

end Short

/-- **Analytic isomorphism `ℂ/Λ → E(ℂ)`**, read on the lift `ξ : ℂ → E(ℂ)`: the fibres of `ξ` are the
cosets of `Λ` (so `ξ` induces a bijection `ℂ/Λ → E(ℂ)`), `ξ` is onto, and `ξ` is a local biholomorphism
`ℂ → E(ℂ)` for the complex structure `isManifoldPoint` (Mathlib's `IsLocalDiffeomorph` for the model
`𝓘(ℂ)` and `C^ω`). Since `ℂ → ℂ/Λ` is a local biholomorphism defining the complex structure of the
torus `ℂ/Λ`, this says exactly that the induced map `ℂ/Λ → E(ℂ)` is biholomorphic. No group law is
asked for. -/
def IsAnalyticIso (W : WeierstrassCurve ℂ) [W.IsElliptic] [W.IsShortNF] (Λ : Set ℂ)
    (ξ : ℂ → W.toAffine.Point) : Prop :=
  (∀ z w, ξ z = ξ w ↔ z - w ∈ Λ) ∧ Function.Surjective ξ ∧ IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω ξ

end HCMW
