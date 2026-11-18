import Mathlib

/-!
# UnramifiedComplex: the two-term complex `U_w^ur = [W --(Φ−1)--> W]`

Manuscript `diophantine_zq.tex`, tex 3478–3481 ("the unramified complex `[Φ-1]` in degrees zero
and one") and tex 4551–4573 (the row "unramified" of the local-condition table), tex 4699–4701 (the
unramified condition has the degree-zero invariants of the full local complex and injects in degree
one).

For a module `W` over a ring `k` and an endomorphism `Φ` of `W` (the arithmetic Frobenius acting on
an unramified coefficient module), `frobCx Φ` is the cochain complex of `k`-modules, indexed by `ℤ`,
with `W` in degrees `0` and `1`, differential `Φ − 1`, and zero elsewhere: Mathlib's
`HomologicalComplex.double` of `ModuleCat.ofHom (Φ − 1)`. Its cohomology is computed:

* `h0Iso : H⁰ ≅ ker (Φ − 1)`;
* `h1Iso : H¹ ≅ W ⧸ (Φ − 1) W`;
* `isZero_homology`: `Hⁿ = 0` for `n ∉ {0, 1}`.

The comparison with continuous Galois cohomology of `Gal(K_w^ur/K_w) ≃ ℤ̂` is in
`UnramifiedComplex/ZHat.lean` and `UnramifiedComplex/H2.lean`.

Kinds: everything here is PROVED (definitions are genuine Mathlib objects).
-/


open CategoryTheory Limits
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

variable {k : Type} [Ring k] {W : Type} [AddCommGroup W] [Module k W] (Φ : W →ₗ[k] W)

/-- `0 → 1` is an arrow of the cochain shape. -/
theorem rel01 : (ComplexShape.up ℤ).Rel 0 1 := by simp

/-- **`U^ur = [W --(Φ−1)--> W]`**, concentrated in degrees `0` and `1` (tex 3478–3481). -/
def frobCx : CochainComplex (ModuleCat.{0} k) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom (Φ - 1)) rel01

/-- The differential `d⁰¹` is `Φ − 1` up to the structural isomorphisms. -/
theorem frobCx_d01 : (frobCx Φ).d 0 1 =
    (HomologicalComplex.doubleXIso₀ _ rel01).hom ≫ ModuleCat.ofHom (Φ - 1) ≫
      (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv :=
  HomologicalComplex.double_d _ _ _

/-- The differential into degree `0` vanishes. -/
theorem frobCx_d_prev : (frobCx Φ).d (-1) 0 = 0 :=
  HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide)

/-- The differential out of degree `1` vanishes. -/
theorem frobCx_d_next : (frobCx Φ).d 1 2 = 0 :=
  HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide)

/-- Index bookkeeping for the cochain shape. -/
theorem prev0 : (ComplexShape.up ℤ).prev 0 = -1 := by simp
/-- Index bookkeeping for the cochain shape. -/
theorem next0 : (ComplexShape.up ℤ).next 0 = 1 := by simp
/-- Index bookkeeping for the cochain shape. -/
theorem prev1 : (ComplexShape.up ℤ).prev 1 = 0 := by simp
/-- Index bookkeeping for the cochain shape. -/
theorem next1 : (ComplexShape.up ℤ).next 1 = 2 := by simp

/-- The kernel of the differential `d⁰¹` is the kernel of `Φ − 1`. -/
def kerIso : kernel ((frobCx Φ).d 0 1) ≅ kernel (ModuleCat.ofHom (Φ - 1)) :=
  kernelIsoOfEq (frobCx_d01 Φ) ≪≫
    kernelIsIsoComp (HomologicalComplex.doubleXIso₀ _ rel01).hom
      (ModuleCat.ofHom (Φ - 1) ≫ (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv) ≪≫
    kernelCompMono (ModuleCat.ofHom (Φ - 1))
      (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv

/-- The cokernel of the differential `d⁰¹` is the cokernel of `Φ − 1`. -/
def cokerIso : cokernel ((frobCx Φ).d 0 1) ≅ cokernel (ModuleCat.ofHom (Φ - 1)) :=
  cokernelIsoOfEq ((frobCx_d01 Φ).trans (Category.assoc _ _ _).symm) ≪≫
    cokernelCompIsIso ((HomologicalComplex.doubleXIso₀ _ rel01).hom ≫ ModuleCat.ofHom (Φ - 1))
      (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv ≪≫
    cokernelEpiComp (HomologicalComplex.doubleXIso₀ _ rel01).hom (ModuleCat.ofHom (Φ - 1))

/-- `H⁰` of `[W --(Φ−1)--> W]` is `ker (Φ − 1)`. -/
def h0Iso : (frobCx Φ).homology 0 ≅ ModuleCat.of k (LinearMap.ker (Φ - 1)) :=
  ((frobCx Φ).isoHomologyπ (-1) 0 prev0 (frobCx_d_prev Φ)).symm ≪≫
    (frobCx Φ).cyclesIsoSc' (-1) 0 1 prev0 next0 ≪≫ ShortComplex.cyclesIsoKernel _ ≪≫
    kerIso Φ ≪≫ ModuleCat.kernelIsoKer _

/-- `H¹` of `[W --(Φ−1)--> W]` is `W ⧸ (Φ − 1) W`. -/
def h1Iso : (frobCx Φ).homology 1 ≅ ModuleCat.of k (W ⧸ LinearMap.range (Φ - 1)) :=
  (frobCx Φ).isoHomologyι 1 2 next1 (frobCx_d_next Φ) ≪≫
    (frobCx Φ).opcyclesIsoSc' 0 1 2 prev1 next1 ≪≫ ShortComplex.opcyclesIsoCokernel _ ≪≫
    cokerIso Φ ≪≫ ModuleCat.cokernelIsoRangeQuotient _

/-- The complex vanishes outside degrees `0` and `1`. -/
theorem isZero_X (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) : IsZero ((frobCx Φ).X n) :=
  HomologicalComplex.isZero_double_X _ _ _ h0 h1

/-- **`Hⁿ(U^ur) = 0` for `n ∉ {0, 1}`.** PROVED. -/
theorem isZero_homology (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) : IsZero ((frobCx Φ).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_X Φ n h0 h1)

end ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
