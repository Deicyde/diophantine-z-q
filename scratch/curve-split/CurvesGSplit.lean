import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.ZariskiConn.Basic
import ZInQKernel.Contrib.Dim.SmoothStalk

/-! # curve-split: rows H-81 `NormalCurveSmoothQ` and H-82 `GeomConnectedOfConstantFieldQ`

The two rows are imported from `ZInQKernel/Contrib/CurvesG/CurveSplit.lean` (not copied; statements
unchanged). Each is proved here from one published leaf, Mathlib and `ZInQKernel/`:

* H-82 `ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ` from `ZariskiConn.ZariskiConnectedness`
  (Zariski's connectedness theorem, EGA III₁ 4.3.1 with 4.3.4, already a kernel leaf in
  `ZInQKernel/Contrib/ZariskiConn/Basic.lean`). Glue: global functions are integral over `ℚ`
  (Mathlib, `isIntegral_appTop_of_universallyClosed`), embed in the function field, hence are
  rational because `ℚ` is algebraically closed in `F`; so `𝒪_{Spec ℚ} = f_*𝒪_X`
  (`ZariskiConn.app_bijective_of_appTop_bijective`). Normality is not used.
* H-81 `ZInQ.Contrib.CurvesG.NormalCurveSmoothQ` from `RegularSmoothPerfect` (Stacks 00TV: a
  finite type algebra over a perfect field is smooth at a prime with regular local ring).
  Glue: a stalk of an integral normal scheme of dimension `1` locally of finite type over `ℚ` is a
  noetherian integrally closed local domain of dimension `≤ 1`, i.e. a Dedekind domain, hence
  regular (Mathlib); the leaf gives smoothness at every point; the relative dimension is `1` by the
  dimension theory of smooth schemes (`ZInQ.Contrib.Dim`).

No `sorry`, no `axiom`. -/

noncomputable section

namespace CurveSplit

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

/-! ## H-82 -/

/-- **`ℚ = Γ(X, 𝒪_X)` when the function field has constant field `ℚ`** (proved). For `X` proper
and integral over `ℚ` with function field isomorphic to `F ⊇ ℚ(T)` in which `ℚ` is algebraically
closed, `Γ(Spec ℚ, ⊤) → Γ(X, ⊤)` is bijective. -/
theorem appTop_bijective_of_constantField (X : Over SpecQ) [IsProper X.hom] [IsIntegral X.left]
    (F : Type) [Field F] [Algebra Qj F] (hF : ConstantFieldIsQ F)
    (e : X.left.functionField ≃+* F) : Function.Bijective X.hom.appTop := by
  set ι := Scheme.ΓSpecIso (CommRingCat.of ℚ)
  set φ : ℚ →+* Γ(X.left, ⊤) := (ι.inv ≫ X.hom.appTop).hom with hφdef
  have hcomp : φ.comp ι.hom.hom = X.hom.appTop.hom := by
    rw [hφdef, ← CommRingCat.hom_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun a => ?_⟩
    have hint : X.hom.appTop.hom.IsIntegral := isIntegral_appTop_of_universallyClosed X.hom
    obtain ⟨p, hpm, hp⟩ := hint a
    set g : Γ(X.left, ⊤) →+* F := e.toRingHom.comp (X.left.germToFunctionField ⊤).hom with hg'
    have hg : g.comp φ = ratHom F := RingHom.ext_rat _ _
    have hy : ∃ f : Polynomial ℚ, f ≠ 0 ∧ f.eval₂ (ratHom F) (g a) = 0 := by
      refine ⟨p.map ι.hom.hom, (hpm.map _).ne_zero, ?_⟩
      rw [Polynomial.eval₂_map, ← hg, RingHom.comp_assoc, hcomp, ← Polynomial.hom_eval₂, hp,
        map_zero]
    obtain ⟨q, hq⟩ := hF _ hy
    refine ⟨q, ?_⟩
    have hginj : Function.Injective g :=
      e.injective.comp (Scheme.germToFunctionField_injective X.left ⊤)
    apply hginj
    rw [← RingHom.comp_apply, hg, hq]
  rw [show (⇑X.hom.appTop : _ → _) = ⇑(X.hom.appTop).hom from rfl, ← hcomp, RingHom.coe_comp]
  exact hφ.comp ι.commRingCatIsoToRingEquiv.bijective

/-- **H-82 `GeomConnectedOfConstantFieldQ` from Zariski's connectedness theorem** (proved). -/
theorem geomConnectedOfConstantFieldQ_of_zariski
    (hZ : ZariskiConn.ZariskiConnectedness.{0}) : GeomConnectedOfConstantFieldQ := by
  intro X hP hI _ F _ _ hF he
  obtain ⟨e⟩ := he
  have h2 := appTop_bijective_of_constantField X F hF e
  exact hZ X.hom hP inferInstance (ZariskiConn.app_bijective_of_appTop_bijective X.hom h2)

/-! ## H-81 -/

/-- **Leaf: regular points are smooth over a perfect field** (published).
Let `k` be a perfect field, `S` a finite type `k`-algebra and `q` a prime of `S`. If `S_q` is a
regular local ring, then `S` is smooth at `q` over `k`: there is `g ∉ q` with `S_g` smooth over
`k`. Source: Stacks Project, Tag 00TV (Algebra, Lemma 10.140.5 in the numbering of 2024;
UNVERIFIED, no network), "Let k be a perfect field. Let S be a finite type k-algebra. Let q be a
prime of S. Then S is smooth at q over k iff S_q is a regular local ring" (paraphrase); the
definition of "smooth at q" is Stacks Tag 00T6/00TB (some `g ∉ q` with `S_g` smooth). The `⇐`
direction, with `k`, `S` in `Type`. `IsRegularLocalRing` is Mathlib's (Stacks 00KU), `Algebra.Smooth`
Mathlib's (equivalent to Stacks' smoothness, Stacks 00T7 / 00TA). -/
def RegularSmoothPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (S : Type) [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime q) →
      ∃ g : S, g ∉ q ∧ Algebra.Smooth k (Localization.Away g)

/-- A noetherian integral normal scheme of dimension `≤ 1` has regular local rings (proved:
each stalk is a Dedekind domain). -/
theorem isRegularLocalRing_stalk_of_normal (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : IsNormalScheme X) (hd : topologicalKrullDim X ≤ 1) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  have hdim : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have h1 : (Order.coheight x : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    calc (Order.coheight x : WithBot ℕ∞) ≤ Order.krullDim X := Order.coheight_le_krullDim x
      _ = topologicalKrullDim X := hdim.symm
      _ ≤ 1 := hd
      _ = ((1 : ℕ) : WithBot ℕ∞) := rfl
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    krullDimLE_of_coheight_le (by exact_mod_cast h1)
  have : Ring.DimensionLEOne (X.presheaf.stalk x) :=
    ⟨fun hp hpp => hpp.isMaximal_of_ne_bot hp⟩
  have : IsIntegrallyClosed (X.presheaf.stalk x) := hN x
  have : IsDedekindDomain (X.presheaf.stalk x) := { }
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _

/-- `Γ(Spec ℚ, ⊤)` is a field. -/
theorem isField_gammaSpecQ : IsField Γ(SpecQ, ⊤) :=
  ZInQ.Contrib.Dim.isField_sections_spec ℚ ⊤ Set.univ_nonempty

/-- **Every point is in the smooth locus** (proved from the leaf). For `X` locally of finite type
over `ℚ` with regular local rings, every point of `X` is smooth over `ℚ`. -/
theorem mem_smoothLocus_of_regular (hL : RegularSmoothPerfect) (X : Over SpecQ)
    [LocallyOfFiniteType X.hom]
    (hreg : ∀ x : X.left, IsRegularLocalRing (X.left.presheaf.stalk x)) (x : X.left) :
    x ∈ X.hom.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen (⊤ : SpecQ.Opens) := isAffineOpen_top _
  have hVU : V ≤ X.hom ⁻¹ᵁ ⊤ := by simp
  have hFT := X.hom.finiteType_appLE hU hV hVU
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ hU V hV hVU hxV]
  let _ : Field Γ(SpecQ, ⊤) := isField_gammaSpecQ.toField
  let _ : Algebra Γ(SpecQ, ⊤) Γ(X.left, V) := (X.hom.appLE ⊤ V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(SpecQ, ⊤) Γ(X.left, V) := hFT
  have : CharZero Γ(SpecQ, ⊤) :=
    charZero_of_injective_ringHom (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom.injective
  have : PerfectField Γ(SpecQ, ⊤) := PerfectField.ofCharZero
  set q := hV.primeIdealOf ⟨x, hxV⟩ with hq
  let x' : V := ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk x'
  let _hA := TopCat.Presheaf.algebra_section_stalk X.left.presheaf x'
  have hregq : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
    IsRegularLocalRing.of_ringEquiv (R := X.left.presheaf.stalk x)
      (IsLocalization.algEquiv q.asIdeal.primeCompl (X.left.presheaf.stalk x')
        (Localization.AtPrime q.asIdeal)).toRingEquiv
  obtain ⟨g, hg, hsm⟩ := hL Γ(SpecQ, ⊤) Γ(X.left, V) q.asIdeal hregq
  have : Algebra.FinitePresentation Γ(SpecQ, ⊤) Γ(X.left, V) :=
    Algebra.FinitePresentation.of_finiteType.mp hFT
  have hsub := (Algebra.basicOpen_subset_smoothLocus_iff_smooth (f := g)).mpr hsm
  exact hsub ((PrimeSpectrum.mem_basicOpen g q).mpr hg)

/-- **Smooth of relative dimension `1`** (proved): a smooth irreducible `ℚ`-scheme of dimension
`1` is smooth of relative dimension `1`. -/
theorem smoothOfRelativeDimension_one (X : Over SpecQ) [Smooth X.hom] [IrreducibleSpace X.left]
    (hd : topologicalKrullDim X.left = 1) : SmoothOfRelativeDimension 1 X.hom := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth X.hom x
  let _ := (X.hom.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(SpecQ, U) Γ(X.left, V) := h
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h'.out
  have hP := P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨y, hyV, hyc⟩ := nonempty_inter_closedPoints (Z := (V : Set X.left))
    ⟨x, hxV⟩ V.isOpen.isLocallyClosed
  have h1 := (ZInQ.Contrib.Dim.ringKrullDim_stalk_of_chart X.hom hV e P.dimension hP y hyV hyc).1
  have h2 := (ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth X.hom y hyc).1
  have hn : P.dimension = 1 := by
    rw [hd, h1] at h2
    exact_mod_cast h2.symm
  exact ⟨U, hU, V, hV, hxV, e, hn ▸ hP⟩

/-- **H-81 `NormalCurveSmoothQ` from Stacks 00TV** (proved). -/
theorem normalCurveSmoothQ_of_regularSmooth (hL : RegularSmoothPerfect) : NormalCurveSmoothQ := by
  intro X hLFT hI hN hd
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hreg := isRegularLocalRing_stalk_of_normal X.left hN hd.le
  have hsl : X.hom.smoothLocus = ⊤ := by
    rw [← top_le_iff]
    rintro x -
    exact mem_smoothLocus_of_regular hL X hreg x
  have : Smooth X.hom := Scheme.Hom.smoothLocus_eq_top_iff.mp hsl
  exact smoothOfRelativeDimension_one X hd

end CurveSplit

#print axioms CurveSplit.geomConnectedOfConstantFieldQ_of_zariski
#print axioms CurveSplit.normalCurveSmoothQ_of_regularSmooth
