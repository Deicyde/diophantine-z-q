import ZInQKernel.Contrib.OneProof.JDescent5
import ZInQKernel.Contrib.OneProof.JDescent4Genus
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.ModelOrigin
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.ProjectiveParameter
import ZInQKernel.Contrib.AbVarBC.Points

/-! # cmheight62-p1, step 2: the short model `W/K` and the differential `η_W = d(−x/y)`

For an elliptic curve `E/K` (`K` a number field), `abVar_shortSections_of_genusOne` (with the proved
`abVarFunctionFieldGenusOne`) gives regular functions `x, y` on `E ∖ {0}` with poles of order
`2, 3` at the identity place `P` and `y² = x³ + a x + b`, `Δ(0,0,0,a,b) ≠ 0`. We fix one such
datum (`shortData`), the short model `W = (0,0,0,a,b)` over `K` and its discriminant
`Δ_W ∈ K`.

The function `−x/y` has order `1` at `P`; since the image of `𝒪_{E,0}` in `K(E)` is the valuation
ring of `P` (`hp`), it is the image of a unique germ `t_E ∈ 𝔪_{E,0}` (`tE`). Its image in
`𝒪_{E_L,0}` (stalk map of the projection `E_L → E`) moved to `𝒪_{𝒢,ξ}` by `originStalkEquiv` is
`t`, and `η_W = 𝒢.wedge ![t] ∈ 𝒢.hodgeSpace 1` (`etaW`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open HDec.CMBranch.CMjBridges MonObj
open ZInQ.Contrib.RC53Assist.HodgeLineBinding (originStalkEquiv originStalkEquiv_symm_mem stalkMapAt
  stalkMapAt_mem)
open ZInQ.DefFaltings

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

/-- The short Weierstrass datum of `abVar_shortSections_of_genusOne`, bundled. -/
structure ShortData {K : Type} [Field K] (A : PkgI3.AbVar K) where
  /-- the identity place -/
  P : TauCeti.Place K (AbVarFunctionField A)
  /-- the image of the stalk at the identity is the valuation ring of `P` -/
  hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
    P.integers.toSubring
  /-- the abscissa -/
  x : Γ(A.X.left, abVarPunctured A)
  /-- the ordinate -/
  y : Γ(A.X.left, abVarPunctured A)
  /-- `a₄` -/
  a : K
  /-- `a₆` -/
  b : K
  hx : letI := abVarPunctured_nonempty A P hp
    P.ord (A.X.left.germToFunctionField (abVarPunctured A) x) = -2
  hy : letI := abVarPunctured_nonempty A P hp
    P.ord (A.X.left.germToFunctionField (abVarPunctured A) y) = -3
  hreg : letI := abVarPunctured_nonempty A P hp
    ∀ Q, Q ≠ P → 0 ≤ Q.ord (A.X.left.germToFunctionField (abVarPunctured A) x) ∧
      0 ≤ Q.ord (A.X.left.germToFunctionField (abVarPunctured A) y)
  heq : y ^ 2 = x ^ 3 + abVarSectionConst A _ a * x + abVarSectionConst A _ b
  hΔ : (⟨0, 0, 0, a, b⟩ : WeierstrassCurve K).Δ ≠ 0

theorem nonempty_shortData {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (hdim : A.dim = 1) : Nonempty (ShortData A) := by
  obtain ⟨P, hp, x, y, a, b, h⟩ :=
    abVar_shortSections_of_genusOne abVarFunctionFieldGenusOne A hdim
  exact ⟨⟨P, hp, x, y, a, b, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

/-- **The fixed short datum** of an elliptic curve `A/K`. -/
def shortData {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (hdim : A.dim = 1) :
    ShortData A :=
  (nonempty_shortData A hdim).some

namespace ShortData

variable {K : Type} [Field K] {A : PkgI3.AbVar K} (D : ShortData A)

/-- The short model `W = (0, 0, 0, a, b)` over `K`. -/
def W : WeierstrassCurve K := ⟨0, 0, 0, D.a, D.b⟩

/-- `Δ_W = −16 (4a³ + 27b²)`. -/
theorem W_Δ : D.W.Δ = -16 * (4 * D.a ^ 3 + 27 * D.b ^ 2) := by
  simp [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem W_Δ_ne_zero : D.W.Δ ≠ 0 := D.hΔ

include D in
theorem nonempty_punctured : Nonempty (abVarPunctured A) := abVarPunctured_nonempty A D.P D.hp

/-- `X = x` in the function field. -/
def X : AbVarFunctionField A :=
  letI := abVarPunctured_nonempty A D.P D.hp
  A.X.left.germToFunctionField (abVarPunctured A) D.x

/-- `Y = y` in the function field. -/
def Y : AbVarFunctionField A :=
  letI := abVarPunctured_nonempty A D.P D.hp
  A.X.left.germToFunctionField (abVarPunctured A) D.y

theorem ord_X : D.P.ord D.X = -2 := D.hx
theorem ord_Y : D.P.ord D.Y = -3 := D.hy

theorem X_ne_zero : D.X ≠ 0 := by
  intro h; have := D.ord_X; rw [h, TauCeti.Place.ord_zero] at this; omega

theorem Y_ne_zero : D.Y ≠ 0 := by
  intro h; have := D.ord_Y; rw [h, TauCeti.Place.ord_zero] at this; omega

/-- The local parameter `−x/y` at the identity, in the function field. -/
def fXY : AbVarFunctionField A := -D.X / D.Y

theorem fXY_ne_zero : D.fXY ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr D.X_ne_zero) D.Y_ne_zero

theorem ord_fXY : D.P.ord D.fXY = 1 := by
  rw [fXY, TauCeti.Place.ord_div D.P (neg_ne_zero.mpr D.X_ne_zero) D.Y_ne_zero,
    TauCeti.Place.ord_neg, D.ord_X, D.ord_Y]
  norm_num

theorem fXY_mem_range :
    D.fXY ∈ (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A))
      (AbVarFunctionField A)).range := by
  rw [D.hp]
  change D.fXY ∈ D.P.integers
  rw [TauCeti.Place.mem_integers_iff_ord_nonneg, D.ord_fXY]
  norm_num

/-- **The germ `t_E ∈ 𝒪_{E,0}` of `−x/y`.** -/
def tE : A.X.left.presheaf.stalk (abVarIdentity A) := D.fXY_mem_range.choose

theorem algebraMap_tE :
    algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A) D.tE =
      D.fXY :=
  D.fXY_mem_range.choose_spec

/-- The stalk at the identity, mapped onto the valuation ring of `P`. -/
def toIntegers : A.X.left.presheaf.stalk (abVarIdentity A) →+* D.P.integers :=
  (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).codRestrict
    D.P.integers.toSubring (fun s => by rw [← D.hp]; exact ⟨s, rfl⟩)

theorem tE_mem_maximalIdeal : D.tE ∈ maximalIdeal (A.X.left.presheaf.stalk (abVarIdentity A)) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := hu.map D.toIntegers
  have h1 : ((D.toIntegers D.tE : D.P.integers) : AbVarFunctionField A) = D.fXY :=
    D.algebraMap_tE
  have h0 := (TauCeti.Place.isUnit_iff_ord_eq_zero (P := D.P) (x := D.toIntegers D.tE)
    (by rw [h1]; exact D.fXY_ne_zero)).mp hu'
  rw [h1, D.ord_fXY] at h0
  exact one_ne_zero h0

end ShortData

section BaseChange

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L]

/-- The projection `E_L = E ×_K L → E`. -/
def bcProj : (A.baseChange L).X.left ⟶ A.X.left :=
  pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))

theorem unit_comp_bcProj : (η[(A.baseChange L).X]).left ≫ bcProj A L =
    (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))).left ≫
      pullback.fst _ _ ≫ (η[A.X]).left := by
  show (Functor.LaxMonoidal.ε (Over.pullback _) ≫ (Over.pullback _).map η[A.X]).left ≫ _ = _
  simp [bcProj]

/-- The projection maps the identity of `E_L` to the identity of `E`. -/
theorem bcProj_identity : bcProj A L (abVarIdentity (A.baseChange L)) = abVarIdentity A := by
  have h := congrArg (fun f => f (IsLocalRing.closedPoint L)) (unit_comp_bcProj A L)
  have h' : bcProj A L ((η[(A.baseChange L).X]).left (IsLocalRing.closedPoint L)) =
      (η[A.X]).left (((Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap K L))))).left ≫ pullback.fst _ _) (IsLocalRing.closedPoint L)) := h
  change bcProj A L ((η[(A.baseChange L).X]).left (IsLocalRing.closedPoint L)) = _
  rw [h']
  change (η[A.X]).left _ = (η[A.X]).left (IsLocalRing.closedPoint K)
  congr 1
  exact Subsingleton.elim _ _

end BaseChange

namespace ShortData

variable {K : Type} [Field K] {E : PkgI3.AbVar K} (D : ShortData E)
variable {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `t_E` moved to `𝒪_{E_L, 0}`. -/
def tL : (E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)) :=
  (stalkMapAt (bcProj E L) (bcProj_identity E L)).hom D.tE

omit [NumberField L] in
theorem tL_mem : tL (L := L) D ∈ maximalIdeal _ :=
  stalkMapAt_mem _ _ D.tE_mem_maximalIdeal

/-- **The germ `t ∈ 𝔪_ξ ⊂ 𝒪_{𝒢,ξ}` of `−x/y`.** -/
def tG (𝒢 : GroupModel E L) : maximalIdeal 𝒢.genStalk :=
  ⟨(originStalkEquiv 𝒢).symm (tL D), originStalkEquiv_symm_mem 𝒢 (tL_mem D)⟩

/-- **`η_W = 1 ⊗ d(−x/y) ∈ 𝒢.hodgeSpace 1`.** -/
def etaW (𝒢 : GroupModel E L) : 𝒢.hodgeSpace 1 := 𝒢.wedge ![tG D 𝒢]

end ShortData

end ZInQ.Contrib.CMHeight62
