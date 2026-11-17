import ZInQKernel.Contrib.OneProof.JavanpeykarDirect
import ZInQKernel.Contrib.OneProof.SemistablePrintedReadings

/-! # jp-an-retype: Javanpeykar 2014 Thm 1.1.1 + §2.3 over the analytic stable height

Task jp-an-retype (2026-11-17), report `docs/research/jp-an-retype.md`, scratch `scratch/jp-an-retype/`.
Base `wip/leaf-fold33b` bf691da22 with `wip/semistab-assembly` 418304785 merged.

**Target.** The research field `javanpeykarThm111 : JavanpeykarDirect.JavanpeykarThm111` (kinds row
consequence / GLUE). Its height predicate `JavanpeykarDirect.IsStableHeightBar` is built on height-fix's
`IsPrintedStableHeight`, whose archimedean metric is read in translated algebraic coordinates; that these are
holomorphic charts of `A_τ(ℂ)^an` is the step R3 (queue14 ruling (c)). r3-residual's `IsAnStableHeight` reads the
metric in every holomorphic chart (`IsHolChart`) and proves R3 except its chart part R3' (that the `IsHolChart`
atlas is the complex structure of `A(ℂ)^an`), the step behind `BostLowerBoundAn` and `GaudronRemondThm14An`.

**This file.**
* `isSemistableRes_of_printed`, `isAnStableHeightSS_iff`: the semistability clause as printed (semistab-assembly's
  `IsSemistablePrinted`, both readings) is *equivalent* to `IsSemistableRes` (converse of semistab-assembly's
  bridge: an open subgroup whose image is the connected component of the unit is connected);
* `IsStableHeightBarAn`: `IsStableHeightBar` with `IsPrintedStableHeight` replaced by `IsAnStableHeightSS`
  (metric on `A_τ(ℂ)^an`, semistability as printed); `isStableHeightBarAn_iff` (given T35);
* `JavanpeykarThm111An`: the leaf, `JavanpeykarThm111` verbatim over `IsStableHeightBarAn`, docstring giving the
  two cited statements (Thm 1.1.1, §2.3) and the manuscript line (diophantine_zq.tex L870);
* `javanpeykarThm111_of_an` (the field from the leaf and `mumfordTorsionAlgClosed`, T35 filled by
  `uniformizationLeafAll_proof`) and `javanpeykarThm111An_of_thm111` (converse, given T35): the new leaf is not
  stronger than the row it replaces.

No `sorry`, no `axiom`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonObj
open JavanpeykarDict JavanpeykarFix
open LeafModCurves (IsCurve)
open ZInQ.LeafPush2 (javanpeykarBound)
open ZInQ.HeightSplit ZInQ.HeightFix ZInQ.R3Residual ZInQ.SemistabAssembly
open ZInQ.DefFaltings ZInQ.HeightGlue ZInQ.HeightDict
open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace JavanpeykarAnRetype

/-! ## §1. Semistability as printed is equivalent to `IsSemistableRes` -/

section Semistab

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **The `k(𝔭)` reading gives `IsSemistableRes`** (converse of semistab-assembly's
`isSemistableResPrinted_of_res`): the open subgroup `U` with image the connected component of the unit is
connected (an open embedding is a homeomorphism onto its image, which is connected). -/
theorem isSemistableRes_of_resPrinted (𝒢 : GroupModel A L) (h : IsSemistableResPrinted 𝒢) :
    IsSemistableRes 𝒢 := by
  intro 𝔭 _
  obtain ⟨U, hU, inc, hoi, hmh, hcc, rest⟩ := h 𝔭
  refine ⟨U, hU, inc, hoi, hmh, ?_, rest⟩
  haveI := hoi
  have hc : _root_.IsConnected (inc.left '' Set.univ) := by
    rw [Set.image_univ, hcc]; exact isConnected_connectedComponent
  rw [connectedSpace_iff_univ]
  exact ⟨hc.nonempty.of_image,
    inc.left.isOpenEmbedding.isInducing.isPreconnected_image.mp hc.isPreconnected⟩

/-- **Semistability as printed (both readings) gives `IsSemistableRes`.** -/
theorem isSemistableRes_of_printed (𝒢 : GroupModel A L) (h : IsSemistablePrinted 𝒢) :
    IsSemistableRes 𝒢 :=
  isSemistableRes_of_resPrinted 𝒢 h.2

/-- **The two analytic stable heights coincide**: semistability as printed (`IsAnStableHeightSS`) or as
`IsSemistableRes` (`IsAnStableHeight`). No T35 needed. -/
theorem isAnStableHeightSS_iff {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) :
    IsAnStableHeightSS A x ↔ IsAnStableHeight A x := by
  constructor
  · rintro ⟨L, iF, iN, iA, 𝒩, g, hN, hS, rest⟩
    exact ⟨L, iF, iN, iA, 𝒩, g, hN, isSemistableRes_of_printed 𝒩 hS, rest⟩
  · exact isAnStableHeightSS_of

end Semistab

/-! ## §2. The stable Faltings height over `ℚ̄`, metric on `A_τ(ℂ)^an` -/

/-- **The stable Faltings height of an abelian variety over `ℚ̄`, metric on `A_τ(ℂ)^an`** (Faltings 1983 §1,
Deligne Sém. Bourbaki 616 §1: the stable height of `W/ℚ̄` is that of a model over a number field `L ⊆ ℚ̄`;
locators UNVERIFIED). `JavanpeykarDirect.IsStableHeightBar` verbatim with `IsPrintedStableHeight` replaced by
`IsAnStableHeightSS` (semistab-assembly: r3-residual's `IsAnStableHeight`, archimedean metric
`(i/2)^g ∫ η̃ ∧ η̄̃` read in every holomorphic chart of `A_τ(ℂ)^an`, with semistable reduction as printed:
the identity component of each special fibre is semi-abelian, over `k(𝔭)` and over `k(𝔭)‾`). -/
def IsStableHeightBarAn {Kbar : Type} [Field Kbar] (W : AbelianVariety Kbar) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra L Kbar) (V : AbelianVariety L),
    Nonempty ((AbelianVariety.baseChange L Kbar).obj V ≅ W) ∧ IsAnStableHeightSS (ofVendored V) x

/-- **The two heights over `ℚ̄` coincide** (given T35; `isAnStableHeight_iff`, `isAnStableHeightSS_iff`). -/
theorem isStableHeightBarAn_iff (hT35 : ZInQ.LeafPush2.UniformizationExists) {Kbar : Type} [Field Kbar]
    (W : AbelianVariety Kbar) (x : ℝ) :
    IsStableHeightBarAn W x ↔ JavanpeykarDirect.IsStableHeightBar W x := by
  constructor
  · rintro ⟨L, iF, iN, iA, V, hVW, hx⟩
    exact ⟨L, iF, iN, iA, V, hVW,
      (isAnStableHeight_iff hT35 _ x).mp ((isAnStableHeightSS_iff _ x).mp hx)⟩
  · rintro ⟨L, iF, iN, iA, V, hVW, hx⟩
    exact ⟨L, iF, iN, iA, V, hVW,
      (isAnStableHeightSS_iff _ x).mpr ((isAnStableHeight_iff hT35 _ x).mpr hx)⟩

/-! ## §3. The leaf -/

/-- **Leaf R18-Javanpeykar, Thm 1.1.1 with §2.3, over the analytic stable height** (A. Javanpeykar,
*Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014); locators recorded by
the locator audit, docs/research/locators.md row R18). The manuscript (diophantine_zq.tex L870, "Transfer from a
modular Jacobian") applies it as "Theorem 1.1.1 and Section 2.3" to `J = J₁(N)` (genus and degree of the standard
Belyi map of `X₁(N)` at most `N²`), giving `h_F(J) ≤ 13000000 N¹²`, and records that the normalization is the
original stable Faltings height of the Jacobian. The two cited statements:
* **Thm 1.1.1** (ANT p. 90; arXiv:1403.6404v1 p. 1): for a smooth projective connected curve `X` over `ℚ̄` of
  genus `g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`;
* **§2.3** (ANT p. 98; arXiv p. 9): the Faltings height `h_Fal(X)` of `X` is the stable Faltings height of its
  Jacobian, `h_Fal(X) = h_Fal(Jac X)`.
This Prop is their composite, `h_Fal(Jac X) ≤ 13·10⁶ · g · deg_B(X)⁵` (`h_Fal(X)` itself, the Arakelov-metrized
determinant of cohomology, is not defined in Lean; the composite is the form the manuscript uses). Nothing else
is assumed. Over the print's objects (`JavanpeykarDirect.JavanpeykarThm111` verbatim, with
`IsStableHeightBar` replaced by `IsStableHeightBarAn`):
* `ℚ̄`: `Kbar`, any algebraic closure of `ℚ`;
* `X`: a smooth proper geometrically connected curve over `ℚ̄` (`IsCurve`), integral, projective;
* `g = genusK X = dim_ℚ̄ H¹(X, 𝒪_X)`;
* `Jac(X)`: `W`, an abelian variety over `ℚ̄` representing the degree-zero Picard functor of `X` with the
  tensor-product group law;
* `h_Fal(Jac X)`: any `x` with `IsStableHeightBarAn W x` (stable height of a model over a number field, metric
  on `A_τ(ℂ)^an`, semistability as printed);
* `deg_B(X) = JavanpeykarDirect.belyiDegree X hB`, the least degree of a Belyi map, given that one exists
  (Belyi's theorem). -/
def JavanpeykarThm111An : Prop :=
  ∀ (Kbar : Type) [Field Kbar] [Algebra ℚ Kbar] [IsAlgClosure ℚ Kbar]
    (X : Over (Spec (CommRingCat.of Kbar))) [IsCurve X] [IsIntegral X.left],
    (∃ (n : Type) (_ : Finite n) (i : X.left ⟶ ℙ(n; Spec (CommRingCat.of Kbar))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of Kbar)) ↘ Spec (CommRingCat.of Kbar) = X.hom) →
    1 ≤ genusK X →
    ∀ (W : AbelianVariety Kbar)
      (repW : (picardFunctorDegree X.hom 0).obj.RepresentableBy W.group.X),
      PicardTensorCompatible X.hom W.group repW →
    ∀ (hB : ∃ d, JavanpeykarDirect.HasBelyiMapOfDegree X d),
    ∀ x : ℝ, IsStableHeightBarAn W x → x ≤ javanpeykarBound (genusK X) (JavanpeykarDirect.belyiDegree X hB)

/-! ## §4. The field from the leaf, and the converse -/

/-- **`javanpeykarThm111` from the leaf**, with T35 as `uniformizationLeafAll` and `mumfordTorsionAlgClosed`. -/
theorem javanpeykarThm111_of_an' (h : JavanpeykarThm111An)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : JavanpeykarDirect.JavanpeykarThm111 := by
  intro Kbar _ _ _ X _ _ hproj hg1 W repW htcW hB x hx
  exact h Kbar X hproj hg1 W repW htcW hB x
    ((isStableHeightBarAn_iff (AvSplit.Final.h38 hUL hMT) W x).mpr hx)

/-- **The field `javanpeykarThm111`** from the leaf and `mumfordTorsionAlgClosed` (`uniformizationLeafAll`
filled by its proof). -/
theorem javanpeykarThm111_of_an (h : JavanpeykarThm111An)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : JavanpeykarDirect.JavanpeykarThm111 :=
  javanpeykarThm111_of_an' h uniformizationLeafAll_proof hMT

/-- **The new leaf is never stronger** than `JavanpeykarThm111` (given T35). -/
theorem javanpeykarThm111An_of_thm111 (h : JavanpeykarDirect.JavanpeykarThm111)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) : JavanpeykarThm111An := by
  intro Kbar _ _ _ X _ _ hproj hg1 W repW htcW hB x hx
  exact h Kbar X hproj hg1 W repW htcW hB x ((isStableHeightBarAn_iff hT35 W x).mp hx)

end JavanpeykarAnRetype

end
