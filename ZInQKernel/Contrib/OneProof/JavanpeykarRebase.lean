import ZInQKernel.Contrib.OneProof.JavanpeykarFix
import ZInQKernel.Contrib.OneProof.PrintedStableHeight
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll

/-! # javanpeykar-rebase: `JavanpeykarBound` over height-fix's printed stable height

Task javanpeykar-rebase (2026-11-16), report `docs/research/javanpeykar-rebase.md`, scratch
`scratch/javanpeykar-rebase/`.

**Target.** The bundle field `javanpeykarBound : ZInQ.HeightSplit.JavanpeykarBound`
(`ZInQKernel/OneProof/H/TailY.lean`). javanpeykar-fix proved it from `JavanpeykarFix.JavanpeykarPrintedMap`
(over height-dict's `IsPrintedStableHeight`, whose metric definition had the soundness defect and the
unproved step R3) and `JavanpeykarFix.ConstantFieldExtensionUnramifiedFull` (Stichtenoth for any algebraic
`K'/K`).

**Result.** `javanpeykarBound_of_printed_rebase : JavanpeykarPrintedMap → ConstantFieldExtensionUnramifiedFinite →
UniformizationLeafAll → MumfordTorsionAlgClosed → ZInQ.HeightFix.SemiAbelianDescendsPerfect → JavanpeykarBound`:
* `JavanpeykarPrintedMap` is javanpeykar-fix's leaf verbatim over height-fix's
  `ZInQ.HeightFix.IsPrintedStableHeight` (§2); `javanpeykarPrintedMap_of_fix` shows it is never stronger than
  javanpeykar-fix's leaf (given T35 and Stacks 04KV);
* `ConstantFieldExtensionUnramifiedFinite` is Stichtenoth's Thm 3.6.3(a) for **finite** `K'/K` (§1); the
  algebraic case used by the consumer (`K' = K̄`) is proved from it (`full_of_finite`: an element of
  `F ⊗_K K̄` comes from `F ⊗_K K'` with `K'/K` finite, and the place restricts to the compositum `F K'`);
  `finite_of_full` gives the converse, so the two leaves are equivalent;
* `javanpeykarBound_of_printed_rebase_final` fills `UniformizationLeafAll` with `uniformizationLeafAll_proof`;
* `SemiAbelianDescendsPerfect` is height-fix's glue (descent of semi-abelian identity components from `k̄` to a
  perfect field), the only unproved step between the print and the kernel; it is shared with height-fix's
  `bostLowerBound_of_printed` and `gaudronRemondThm14_of_printed`.

No `sorry`, no `axiom`. -/

noncomputable section

set_option linter.style.haveILetI false

open scoped TensorProduct

namespace JavanpeykarRebase

/-- **Leaf: a finite constant field extension of an algebraic function field is unramified** (H. Stichtenoth,
*Algebraic Function Fields and Codes*, 2nd ed., Springer GTM 254 (2009), §3.6, Thm 3.6.3(a); theorem number
from memory, UNVERIFIED). For an algebraic function field `F/K` (characteristic `0`, `F/K(t)` finite for a
transcendental `t`) with full constant field `K` (Stichtenoth's standing hypothesis in §3.6) and a **finite**
extension `L/K` with `F ⊗_K L ≅ FL` (the constant field extension `F' = FL`), every place `P'` of `FL/L`
(a valuation subring `w ⊇ L`) is unramified over `P = P' ∩ F`: a generator `π` of the maximal ideal of `P`
generates that of `P'` (`e(P'|P) = 1`). javanpeykar-fix's `ConstantFieldExtensionUnramifiedFull` with
`[Algebra.IsAlgebraic K L]` replaced by `[FiniteDimensional K L]`. -/
def ConstantFieldExtensionUnramifiedFinite : Prop :=
  ∀ (K F L FL : Type) [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL] [CharZero K] [FiniteDimensional K L]
    (ι : F →ₐ[K] FL),
    (∃ t : F, Transcendental K t ∧ FiniteDimensional (IntermediateField.adjoin K {t}) F) →
    (∀ a : F, IsAlgebraic K a → a ∈ Set.range (algebraMap K F)) →
    Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)) →
    ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ∀ π : F,
      π ∈ (w.comap (ι : F →+* FL)).nonunits →
      (∀ x ∈ (w.comap (ι : F →+* FL)).nonunits, ∃ y ∈ w.comap (ι : F →+* FL), x = π * y) →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = ι π * y

theorem mem_nonunits_comap {E E' : Type} [Field E] [Field E'] (A : ValuationSubring E')
    (f : E →+* E') (x : E) : x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  simp only [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero]

section Tensor

variable {K F L : Type} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]

theorem range_lTensor_mono {L1 L2 : IntermediateField K L} (h : L1 ≤ L2) :
    LinearMap.range (L1.val.toLinearMap.lTensor F) ≤
      LinearMap.range (L2.val.toLinearMap.lTensor F) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨(IntermediateField.inclusion h).toLinearMap.lTensor F x, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  rfl

/-- Every element of `F ⊗_K L` (`L/K` algebraic) comes from `F ⊗_K L'` for a finite subextension
`L'`. -/
theorem exists_fd_of_tensor [Algebra.IsAlgebraic K L] (z : F ⊗[K] L) :
    ∃ L' : IntermediateField K L, FiniteDimensional K L' ∧
      z ∈ LinearMap.range (L'.val.toLinearMap.lTensor F) := by
  induction z using TensorProduct.inductionOn with
  | tmul f l =>
    refine ⟨IntermediateField.adjoin K {l},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral l), ?_⟩
    exact ⟨f ⊗ₜ ⟨l, IntermediateField.mem_adjoin_simple_self K l⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨L1, h1, hx⟩ := hx
    obtain ⟨L2, h2, hy⟩ := hy
    exact ⟨L1 ⊔ L2, inferInstance, Submodule.add_mem _ (range_lTensor_mono le_sup_left hx)
      (range_lTensor_mono le_sup_right hy)⟩

end Tensor

/-- **The finite case follows from the algebraic one** (so `ConstantFieldExtensionUnramifiedFinite` is never
stronger than javanpeykar-fix's `ConstantFieldExtensionUnramifiedFull`). -/
theorem finite_of_full (h : JavanpeykarFix.ConstantFieldExtensionUnramifiedFull) :
    ConstantFieldExtensionUnramifiedFinite := by
  intro K F L FL _ _ _ _ _ _ _ _ _ _ _ ι
  exact h K F L FL ι

/-- **The algebraic case of the leaf from the finite case (glue, proved).** For `L/K` algebraic, an element
`x` of `FL ≅ F ⊗_K L` comes from `F ⊗_K L'` for a finite subextension `L'` (`exists_fd_of_tensor`); the
compositum `E = ι(F) ⊔ L'` inside `FL` satisfies `F ⊗_K L' ≅ E` (injective by flatness, surjective by
`IntermediateField.sup_toSubalgebra_of_right`); the finite case at `E` with the place `w ∩ E` gives
`x = ι π · y` with `y ∈ w ∩ E`. -/
theorem full_of_finite (h : ConstantFieldExtensionUnramifiedFinite) :
    JavanpeykarFix.ConstantFieldExtensionUnramifiedFull := by
  intro K F L FL _ _ _ _ _ _ _ _ _ _ _ ι ht hfull hbij w hw π hπ hgen x hx
  obtain ⟨z, rfl⟩ := hbij.2 x
  obtain ⟨L', hL', z', rfl⟩ := exists_fd_of_tensor (F := F) z
  let j' : L' →ₐ[K] FL := (IsScalarTower.toAlgHom K L FL).comp L'.val
  have hfac : ∀ u : F ⊗[K] L',
      Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)
        (L'.val.toLinearMap.lTensor F u) = Algebra.TensorProduct.productMap ι j' u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul a b => simp [j']
    | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
  have hinj : Function.Injective (Algebra.TensorProduct.productMap ι j') := by
    intro u v huv
    rw [← hfac, ← hfac] at huv
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := F) L'.val.toLinearMap
      Subtype.val_injective (hbij.1 huv)
  haveI : FiniteDimensional K j'.fieldRange :=
    (AlgHom.equivFieldRange j').toLinearEquiv.finiteDimensional
  let E : IntermediateField K FL := ι.fieldRange ⊔ j'.fieldRange
  have hE : E.toSubalgebra = (Algebra.TensorProduct.productMap ι j').range := by
    rw [Algebra.TensorProduct.productMap_range, IntermediateField.sup_toSubalgebra_of_right,
      AlgHom.fieldRange_toSubalgebra, AlgHom.fieldRange_toSubalgebra]
  let ι' : F →ₐ[K] E := ι.codRestrict E.toSubalgebra fun a =>
    (le_sup_left : ι.fieldRange ≤ E) ⟨a, rfl⟩
  let j'' : L' →ₐ[K] E := j'.codRestrict E.toSubalgebra fun a =>
    (le_sup_right : j'.fieldRange ≤ E) ⟨a, rfl⟩
  letI : Algebra L' E := j''.toRingHom.toAlgebra
  haveI : IsScalarTower K L' E := IsScalarTower.of_algebraMap_eq fun a => (j''.commutes a).symm
  have hval : ∀ u : F ⊗[K] L',
      (E.val (Algebra.TensorProduct.productMap ι' (IsScalarTower.toAlgHom K L' E) u) : FL) =
        Algebra.TensorProduct.productMap ι j' u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul a b => simp; rfl
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  have hbij' : Function.Bijective
      (Algebra.TensorProduct.productMap ι' (IsScalarTower.toAlgHom K L' E)) := by
    refine ⟨fun u v huv => hinj ?_, fun e => ?_⟩
    · rw [← hval, ← hval, huv]
    · have he : (e : FL) ∈ E.toSubalgebra := e.2
      rw [hE] at he
      obtain ⟨u, hu⟩ := he
      exact ⟨u, Subtype.ext ((hval u).trans hu)⟩
  let w' : ValuationSubring E := w.comap (E.val : E →+* FL)
  have hcomp : w'.comap (ι' : F →+* E) = w.comap (ι : F →+* FL) := by
    ext a
    simp only [w', ValuationSubring.mem_comap]
    rfl
  have hw' : ∀ c : L', algebraMap L' E c ∈ w' := fun c => ValuationSubring.mem_comap.mpr (hw c)
  have key := h K F L' E ι' ht hfull hbij' w' hw' π (hcomp ▸ hπ) (hcomp ▸ hgen)
  set x' : E := Algebra.TensorProduct.productMap ι' (IsScalarTower.toAlgHom K L' E) z'
  have hxx : (E.val x' : FL) = Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)
      (L'.val.toLinearMap.lTensor F z') := (hval z').trans (hfac z').symm
  have hx' : x' ∈ w'.nonunits := by
    have h1 : (E.val x' : FL) ∈ w.nonunits := by rw [hxx]; exact hx
    exact (mem_nonunits_comap _ _ _).mpr h1
  obtain ⟨y', hy', hxy⟩ := key x' hx'
  refine ⟨E.val y', hy', ?_⟩
  rw [← hxx, hxy, map_mul]
  rfl

/-! ## §2. The restated Javanpeykar leaf and the reduction -/

section Printed

open CategoryTheory AlgebraicGeometry Limits
open JavanpeykarDict JavanpeykarFix
open LeafModCurves (IsCurve IsBelyiFunction)
open ZInQ.LeafPush2 (ffAlgebra javanpeykarBound)

/-- **Leaf R18-Javanpeykar, printed form, over height-fix's printed stable height** (A. Javanpeykar,
*Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014),
Thm 1.1.1, p. 90; height identification p. 98 (arXiv:1403.6404v1 §2.3); locators recorded by the
locator audit, docs/research/locators.md row R18; no statement check recorded). Printed: for a smooth
projective connected curve `X/ℚ̄` of genus `g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`, where
`h_Fal(X)` is the stable Faltings height of `Jac(X)` and `deg_B(X)` the least degree of a finite
morphism `X → ℙ¹_ℚ̄` unramified over `ℙ¹ ∖ {0, 1, ∞}`.

This is `JavanpeykarFix.JavanpeykarPrintedMap` (javanpeykar-fix) verbatim, with height-dict's
`ZInQ.HeightDict.IsPrintedStableHeight` replaced by height-fix's `ZInQ.HeightFix.IsPrintedStableHeight`
(sound archimedean metric: the measure `(i/2)^g η ∧ η̄`, defined chart by chart, must exist; Néron
model over a field of semistable reduction read over the residue fields `k(𝔭)`, SGA 7 IX Déf. 3.4).
Stated for `X = X₀ ×_K ℚ̄` (`X₀` a smooth proper geometrically connected curve over a number field
`K`, `ℚ̄ = AlgebraicClosure K`):
* `X` smooth, connected, projective (a closed immersion into `ℙ(n; Spec ℚ̄)`, hypothesis);
* `Jac(X)`: `W`, an abelian variety over `ℚ̄` representing the degree-zero Picard functor of `X` with
  the tensor-product group law;
* `h_Fal(Jac X)`: the printed stable height of a model `V` of `W` over `K` (`V_ℚ̄ ≅ W`);
* `g = genusBar X₀ = dim H¹(X, 𝒪_X)`;
* a Belyi map `β : X → ℙ¹_ℚ̄ = Proj ℚ̄[X₀, X₁]` of degree `d` (`IsBelyiMap`), so `deg_B(X) ≤ d`; the
  bound is increasing in `deg_B`. -/
def JavanpeykarPrintedMap : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    [IsIntegral (baseChangeCurve X (AlgebraicClosure K)).left],
    (∃ (n : Type) (_ : Finite n)
      (i : (baseChangeCurve X (AlgebraicClosure K)).left ⟶
        ℙ(n; Spec (CommRingCat.of (AlgebraicClosure K)))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of (AlgebraicClosure K))) ↘
        Spec (CommRingCat.of (AlgebraicClosure K)) = (baseChangeCurve X (AlgebraicClosure K)).hom) →
    ∀ (W : AbelianVariety (AlgebraicClosure K))
      (repW : (picardFunctorDegree (baseChangeCurve X (AlgebraicClosure K)).hom 0).obj.RepresentableBy
        W.group.X),
      PicardTensorCompatible (baseChangeCurve X (AlgebraicClosure K)).hom W.group repW →
    ∀ V : AbelianVariety K, Nonempty ((AbelianVariety.baseChange K (AlgebraicClosure K)).obj V ≅ W) →
    1 ≤ genusBar X →
    ∀ (β : (baseChangeCurve X (AlgebraicClosure K)).left ⟶ P1 (AlgebraicClosure K)) (d : ℕ),
      IsBelyiMap (baseChangeCurve X (AlgebraicClosure K)) β d → 0 < d →
    ∀ x : ℝ, ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) x → x ≤ javanpeykarBound (genusBar X) d

/-- **The new leaf is never stronger than javanpeykar-fix's** (given T35 and Stacks 04KV): a height-fix
printed height is a kernel height (`ZInQ.HeightFix.isStableFaltingsHeight_of_printed`), hence a
height-dict printed height (`ZInQ.HeightDict.isPrintedStableHeight_of`). -/
theorem javanpeykarPrintedMap_of_fix (h : JavanpeykarFix.JavanpeykarPrintedMap)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) (hGC : AVGlue.GeomConnOfRationalPoint) :
    JavanpeykarPrintedMap := by
  intro K _ _ X _ _ hproj W repW htcW V hVW hg1 β d hβ hd0 x hx
  exact h K X hproj W repW htcW V hVW hg1 β d hβ hd0 x
    (ZInQ.HeightDict.isPrintedStableHeight_of
      (ZInQ.HeightGlue.analyticUniformizationUnique_of_t35 hT35)
      (ZInQ.HeightGlue.uniformizationDim_of_t35 hT35)
      (ZInQ.HeightFix.isStableFaltingsHeight_of_printed hT35 hGC hx))

/-- **`JavanpeykarBound` from the restated leaves.** Steps: (1) the kernel Jacobian is `Pic⁰`
(javanpeykar-dict); (a) kernel height ⇒ height-fix printed height (`isPrintedStableHeight_of`, T35
from `uniformizationLeafAll`, `mumfordTorsionAlgClosed`, and the glue `SemiAbelianDescendsPerfect`);
(2) `g` is the genus of `X_K̄`; (3) Stichtenoth (finite form, `full_of_finite`) with the full constant
field proved; (b) Belyi function to Belyi map (`belyiMapOfFunction_proof`); (c) projectivity;
(d) `V_K̄ = Jac(X_K̄)`. -/
theorem javanpeykarBound_of_printed_rebase (hJ : JavanpeykarPrintedMap)
    (hS : ConstantFieldExtensionUnramifiedFinite)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) (hD : ZInQ.HeightFix.SemiAbelianDescendsPerfect) :
    ZInQ.HeightSplit.JavanpeykarBound := by
  intro K _ _ X _ _ P₀ J aj hJac g hg hg1 t ht d hd hd0 x hx
  have hX : IsCurve X := inferInstance
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  letI : X.left.Over (Spec (CommRingCat.of K)) := ⟨X.hom⟩
  have : SmoothOfRelativeDimension 1 (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ Spec (CommRingCat.of K)) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  -- (1) the kernel Jacobian is `Pic⁰`; (a) the height-fix printed height
  obtain ⟨V, rep, htc, -⟩ := exists_abelianVariety_picardDegreeZero (baseField := K) X.left
  obtain ⟨e, he⟩ := abVarIso_picZero_of_isJacobian hX hJac V rep htc
  have hx' : ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) x :=
    ZInQ.HeightFix.isPrintedStableHeight_of (AvSplit.Final.h38 hUL hMT) hD
      (isStableFaltingsHeight_of_iso e hx)
  -- (2) `g` is the genus of `X_K̄`
  have hgen : g = genusBar X := by
    have h2 := dim_eq_genusK hX hJac
    rw [hg] at h2
    rw [genusBar_eq hX]
    exact_mod_cast h2
  subst hgen
  -- (3) Stichtenoth, finite form: a Belyi function of `X_K̄` over `K̄`
  obtain ⟨hint, t', ht', hd'⟩ := belyiBaseChange_of_full (full_of_finite hS) K X t ht d hd hd0
  -- (b) the Belyi map
  have : IsProper (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (IsProper ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  have : SmoothOfRelativeDimension 1 (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1
      ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  obtain ⟨β, hβ⟩ := belyiMapOfFunction_proof (AlgebraicClosure K)
    (baseChangeCurve X (AlgebraicClosure K)) t' ht' d hd' hd0
  -- (c) `X_K̄` is projective
  have hproj := exists_closedImmersion_projectiveSpace (baseChangeCurve X (AlgebraicClosure K))
  -- (d) `V_K̄ = Jac(X_K̄)`
  obtain ⟨W, repW, htcW, hVW⟩ := exists_jacBar X hX V rep htc (AlgebraicClosure K)
  exact hJ K X hproj W repW htcW V hVW hg1 β d hβ hd0 x hx'

/-- **`JavanpeykarBound` with `uniformizationLeafAll` filled by its proof** (`uniformizationLeafAll_proof`,
folded at TailZ44): the remaining hypotheses are the two new leaves, the textbook field
`mumfordTorsionAlgClosed` and height-fix's glue `SemiAbelianDescendsPerfect`. -/
theorem javanpeykarBound_of_printed_rebase_final (hJ : JavanpeykarPrintedMap)
    (hS : ConstantFieldExtensionUnramifiedFinite) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hD : ZInQ.HeightFix.SemiAbelianDescendsPerfect) : ZInQ.HeightSplit.JavanpeykarBound :=
  javanpeykarBound_of_printed_rebase hJ hS uniformizationLeafAll_proof hMT hD

end Printed

end JavanpeykarRebase
