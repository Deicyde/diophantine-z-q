import ZInQKernel.Contrib.RC53Assist.S2aNumberField.ProjectiveComparison

/-!
# The local parameters `-x/y` and `-1/y` at the point at infinity

On the projective model `Proj A` of a Weierstrass curve `E` over a field, the local ring at
`O = [0 : 1 : 0]` is the valuation ring of the place at infinity
(`stalkPointOEquivValuationSubring`). The functions `z = -x/y` and `w = -1/y` have valuations
`exp(-1)` and `exp(-3)`, so they are germs at `O` (`paramZ`, `paramW`) in the maximal ideal, and
`z` is not in the square of the maximal ideal (`paramZ_not_mem_sq`): every element of `𝔪_O` has
valuation at most `exp(-1)`, so every element of `𝔪_O²` has valuation at most `exp(-2)`.

The second part transports germs along a morphism of schemes `f` with a point equation
`f x = y` (`stalkMapAt`): the stalk map at `x`, read from the stalk at `y`. It is compatible with
function fields for dominant maps of integral schemes and preserves `𝔪` and the complement of
`𝔪²` for isomorphisms. Only the point equation is used, not any section.

Locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition, II.1, III.1 and IV.1.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open AlgebraicGeometry CategoryTheory IsLocalRing
open ZInQ.Contrib.RC53Assist.S2aNumberField
open WeierstrassCurve (Affine.infinityPlace)

section Valuation

/-- THEOREM (proved). In `ℤᵐ⁰`, an element below `1` is at most `exp(-1)`.
Locator: Mathlib, `WithZero.le_exp_of_log_le`. -/
theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) :
    a ≤ WithZero.exp (-1) := by
  rcases eq_or_ne a 0 with rfl | h0
  · exact zero_le
  · apply WithZero.le_exp_of_log_le
    rw [← WithZero.exp_log h0, WithZero.exp_lt_one_iff] at ha
    omega

end Valuation

variable {L : Type} [Field L] (E : WeierstrassCurve L)

/-- THEOREM (proved). `v_∞(-x/y) = exp(-1)`. Locator: `infinityPlace_genericX`,
`infinityPlace_genericY`. -/
theorem infinityPlace_paramZ :
    Affine.infinityPlace E.toAffine (-E.toAffine.genericX / E.toAffine.genericY) =
      WithZero.exp (-1) := by
  rw [map_div₀, Valuation.map_neg, infinityPlace_genericX, infinityPlace_genericY,
    ← WithZero.exp_sub]
  norm_num

/-- THEOREM (proved). `v_∞(-1/y) = exp(-3)`. Locator: `infinityPlace_genericY`. -/
theorem infinityPlace_paramW :
    Affine.infinityPlace E.toAffine (-1 / E.toAffine.genericY) = WithZero.exp (-3) := by
  rw [map_div₀, Valuation.map_neg, Valuation.map_one, infinityPlace_genericY, one_div,
    ← WithZero.exp_neg]

/-- DEFINITION. The germ at `O` of `z = -x/y`. Locator: `stalkPointOEquivValuationSubring`. -/
def paramZ : (Proj E.toProjective.grading).presheaf.stalk (pointO E) :=
  (stalkPointOEquivValuationSubring E).symm
    ⟨-E.toAffine.genericX / E.toAffine.genericY, (Valuation.mem_valuationSubring_iff _ _).mpr
      ((infinityPlace_paramZ E).le.trans (WithZero.exp_le_one_iff.mpr (by norm_num)))⟩

/-- DEFINITION. The germ at `O` of `w = -1/y`. Locator: `stalkPointOEquivValuationSubring`. -/
def paramW : (Proj E.toProjective.grading).presheaf.stalk (pointO E) :=
  (stalkPointOEquivValuationSubring E).symm
    ⟨-1 / E.toAffine.genericY, (Valuation.mem_valuationSubring_iff _ _).mpr
      ((infinityPlace_paramW E).le.trans (WithZero.exp_le_one_iff.mpr (by norm_num)))⟩

/-- THEOREM (proved). The germ `paramZ` is the function `-x/y`.
Locator: `coe_stalkPointOEquivValuationSubring`. -/
theorem stalkPointOToFunctionField_paramZ :
    stalkPointOToFunctionField E (paramZ E) = -E.toAffine.genericX / E.toAffine.genericY := by
  rw [← coe_stalkPointOEquivValuationSubring, paramZ, RingEquiv.apply_symm_apply]

/-- THEOREM (proved). The germ `paramW` is the function `-1/y`.
Locator: `coe_stalkPointOEquivValuationSubring`. -/
theorem stalkPointOToFunctionField_paramW :
    stalkPointOToFunctionField E (paramW E) = -1 / E.toAffine.genericY := by
  rw [← coe_stalkPointOEquivValuationSubring, paramW, RingEquiv.apply_symm_apply]

/-- THEOREM (proved). A germ at `O` whose function has valuation below `1` lies in the maximal
ideal. Locator: `infinityPlace_lt_one_iff_mem_maximalIdeal`,
`stalkPointOToFunctionField_injective`. -/
theorem mem_maximalIdeal_of_infinityPlace_lt_one
    (g : (Proj E.toProjective.grading).presheaf.stalk (pointO E))
    (hg : Affine.infinityPlace E.toAffine (stalkPointOToFunctionField E g) < 1) :
    g ∈ maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk (pointO E)) := by
  obtain ⟨g', hg', hgg'⟩ := (infinityPlace_lt_one_iff_mem_maximalIdeal E _).mp hg
  rwa [stalkPointOToFunctionField_injective E hgg'] at hg'

/-- THEOREM (proved). `z = -x/y` vanishes at `O`. Locator: `infinityPlace_paramZ`. -/
theorem paramZ_mem : paramZ E ∈ maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk
    (pointO E)) := by
  apply mem_maximalIdeal_of_infinityPlace_lt_one
  rw [stalkPointOToFunctionField_paramZ, infinityPlace_paramZ, WithZero.exp_lt_one_iff]
  norm_num

/-- THEOREM (proved). `w = -1/y` vanishes at `O`. Locator: `infinityPlace_paramW`. -/
theorem paramW_mem : paramW E ∈ maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk
    (pointO E)) := by
  apply mem_maximalIdeal_of_infinityPlace_lt_one
  rw [stalkPointOToFunctionField_paramW, infinityPlace_paramW, WithZero.exp_lt_one_iff]
  norm_num

/-- THEOREM (proved). Elements of `𝔪_O²` have valuation at most `exp(-2)`. Locator:
`infinityPlace_lt_one_of_mem_maximalIdeal_pointO`, `le_exp_neg_one_of_lt_one`;
Mathlib, `Submodule.mul_induction_on`. -/
theorem infinityPlace_le_of_mem_sq
    {g : (Proj E.toProjective.grading).presheaf.stalk (pointO E)}
    (hg : g ∈ maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk (pointO E)) ^ 2) :
    Affine.infinityPlace E.toAffine (stalkPointOToFunctionField E g) ≤ WithZero.exp (-2) := by
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [map_mul, map_mul]
    have h1 := le_exp_neg_one_of_lt_one (infinityPlace_lt_one_of_mem_maximalIdeal_pointO E a ha)
    have h2 := le_exp_neg_one_of_lt_one (infinityPlace_lt_one_of_mem_maximalIdeal_pointO E b hb)
    calc _ ≤ WithZero.exp (-1) * WithZero.exp (-1) := mul_le_mul' h1 h2
      _ = WithZero.exp (-2) := by rw [← WithZero.exp_add]; norm_num
  · rw [map_add]
    exact (Valuation.map_add _ _ _).trans (max_le ha hb)

/-- THEOREM (proved). `z = -x/y` is a local parameter at `O`: it is not in `𝔪_O²`.
Locator: `infinityPlace_paramZ`, `infinityPlace_le_of_mem_sq`. -/
theorem paramZ_not_mem_sq : paramZ E ∉
    maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk (pointO E)) ^ 2 := by
  intro h
  have h1 := infinityPlace_le_of_mem_sq E h
  rw [stalkPointOToFunctionField_paramZ, infinityPlace_paramZ, WithZero.exp_le_exp] at h1
  norm_num at h1

section StalkMapAt

/-- DEFINITION. The stalk map of `f : X ⟶ Y` at `x`, read from the stalk at a point `y` with
`f x = y`. Locator: Mathlib, `TopCat.Presheaf.stalkCongr`, `Scheme.Hom.stalkMap`. -/
def stalkMapAt {X Y : Scheme.{0}} (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  (Y.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ f.stalkMap x

/-- THEOREM (proved). For the trivial point equation, `stalkMapAt` is the stalk map.
Locator: Mathlib, `TopCat.Presheaf.stalkSpecializes_refl`. -/
theorem stalkMapAt_rfl {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    stalkMapAt f (rfl : f x = f x) = f.stalkMap x := by
  unfold stalkMapAt
  have : (Y.presheaf.stalkCongr (.of_eq (rfl : f x = f x).symm)).hom = 𝟙 _ :=
    Y.presheaf.stalkSpecializes_refl _
  rw [this, Category.id_comp]

/-- THEOREM (proved). `stalkMapAt` maps the maximal ideal into the maximal ideal.
Locator: the stalk map is a local homomorphism. -/
theorem stalkMapAt_mem {X Y : Scheme.{0}} (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y)
    {g : Y.presheaf.stalk y} (hg : g ∈ maximalIdeal (Y.presheaf.stalk y)) :
    (stalkMapAt f h).hom g ∈ maximalIdeal (X.presheaf.stalk x) := by
  subst h
  rw [stalkMapAt_rfl]
  exact (map_mem_nonunits_iff (f.stalkMap x).hom g).mpr hg

/-- THEOREM (proved). `stalkMapAt` is compatible with the pull-back of rational functions.
Locator: `IsogenyScheme.functionFieldMap_algebraMap_stalk`. -/
theorem algebraMap_stalkMapAt {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] {x : X} {y : Y} (h : f x = y) (g : Y.presheaf.stalk y) :
    algebraMap _ X.functionField ((stalkMapAt f h).hom g) =
      f.functionFieldMap.hom (algebraMap _ Y.functionField g) := by
  subst h
  rw [stalkMapAt_rfl]
  exact (ZInQ.Contrib.RC53Assist.IsogenyScheme.functionFieldMap_algebraMap_stalk f x g).symm

/-- THEOREM (proved). A ring isomorphism of local rings preserves the complement of `𝔪²`.
Locator: Mathlib, `map_ringEquiv_maximalIdeal`, `Ideal.map_pow`. -/
theorem ringEquiv_not_mem_sq {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (ψ : R ≃+* S) {g : R} (hg : g ∉ maximalIdeal R ^ 2) :
    ψ g ∉ maximalIdeal S ^ 2 := by
  intro h
  apply hg
  have hmap : (maximalIdeal S).map ψ.symm = maximalIdeal R := map_ringEquiv_maximalIdeal ψ.symm
  have h2 : ψ.symm (ψ g) ∈ ((maximalIdeal S) ^ 2).map ψ.symm := Ideal.mem_map_of_mem _ h
  rwa [Ideal.map_pow, hmap, RingEquiv.symm_apply_apply] at h2

/-- THEOREM (proved). For an isomorphism `f`, `stalkMapAt` preserves the complement of `𝔪²`.
Locator: `ringEquiv_not_mem_sq`; an isomorphism has bijective stalk maps. -/
theorem stalkMapAt_not_mem_sq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] {x : X} {y : Y}
    (h : f x = y) {g : Y.presheaf.stalk y} (hg : g ∉ maximalIdeal (Y.presheaf.stalk y) ^ 2) :
    (stalkMapAt f h).hom g ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  subst h
  rw [stalkMapAt_rfl]
  haveI : IsIso (f.stalkMap x) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 x
  exact ringEquiv_not_mem_sq (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv hg

end StalkMapAt

end ZInQ.Contrib.RC53Assist.HodgeLineBinding
