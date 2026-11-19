import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ResidualAfterT

/-!
# Genuine instantiations, part 22: RC6's transfer after inverting `t`, with comparisons of complexes

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4593–4647.

Review of `residualRankCounts_afterT` (part 21) found two defects, repaired here additively:

* **C3 (erased differentials).** Its inputs `hred` (equal graded ranks), `hbc` (degreewise linear
  equivalences) and `e` never compare differentials: zeroing every differential of `P`, `P'` and
  taking `L = P'` satisfies them and gives `genericRank = rankTot`. Here the reduction and the base
  change are **isomorphisms of complexes** with the base-changed differentials:
  - `baseChangeCx f P`: the complex `S ⊗_R P` with differentials `id ⊗ d` (`LinearMap.baseChange`),
    for a ring map `f : R → S`;
  - `ered : baseChangeCx constantCoeff P ≅ (selCx Dsel).toCC` (the reduction of `P` modulo `t` is
    the residual model, with `Dsel`'s actual differentials);
  - `ebc : P' ≅ baseChangeCx (𝔽₂[[t]] → 𝔽₂((t))) P`.
  `differentials_zero_of_erased` (compiled probe): if `P` has zero differentials, any complex
  isomorphic to its base change has zero differentials — so the erased-differential model is
  excluded as soon as `Dsel` has a nonzero differential.
* **C4 (degree coverage).** The counts summed over `s ⊆ [0, 2]` while the models live in
  `[0, 3]` (degree `3` of the Selmer cone carries the local `H²` terms). Here every degree of the
  bounded models is counted: `s = [0, 3]`, with `P`, `P'`, `L` strictly supported in `[0, 3]`, so
  `rankTot` and `genericRank` are whole-model ranks. The global part of `Dsel` contributes up to
  degree `2` only: `GlobalDegreeThreeVanishes Dsel` (named GLUE: `cd₂ G_{K,S} ≤ 2` for totally
  complex `K`, Neukirch–Schmidt–Wingberg (8.3.17), so `H³(G_{K,S}, W) = 0` and the minimal global
  model has no degree-`3` term) is an explicit input.

Remaining input of the transfer (as in part 21): the generic minimal model `L` over `𝔽₂((t))` is
tied to the arithmetic only through `e : HomotopyEquiv L P'` (the text's tex 4626–4631; there are
no `𝔽₂((t))`-coefficient Galois cochains in this tree).

* `transfer_after_inverting_t'`, `residualRankCounts_afterT'`;
* `globalDegreeThreeVanishes_of_milne`, `residualRankCounts_afterT''`: the named GLUE discharged by
  the Milne print from an identification `eG3` of the degree-`3` global term with Mathlib's
  continuous `H³` (the degree-`3` genuine-to-Mathlib comparison is missing, so `eG3` cannot yet be
  stated against the genuine `genH K S₀ 3` or derived from a minimal model);
* Non-vacuity: `transfer_after_inverting_t'_nonvacuous`, `reduction_nonvacuous` (zero complexes;
  model level only — like the peer's witness, they do not tie the models to the arithmetic
  cochains). Non-vacuity of the whole constructor is not shown (as for
  `residualRankCounts_genuine`).

**Classification.** PROVED (from the inputs listed).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open NumberField IsDedekindDomain CategoryTheory ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer ZInQ.Contrib.CloudB3RC53.Mattuck TensorProduct

section BaseChange

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

/-- **The base change of a complex** `S ⊗_R P` along `f : R → S`, with differentials `id ⊗ d`. -/
def baseChangeCx (P : CochainComplex (ModuleCat.{0} R) ℤ) : CochainComplex (ModuleCat.{0} S) ℤ :=
  letI := f.toAlgebra
  { X := fun i => ModuleCat.of S (S ⊗[R] P.X i)
    d := fun i j => ModuleCat.ofHom ((P.d i j).hom.baseChange S)
    shape := fun i j h => by
      rw [P.shape i j h]
      ext x
      simp
    d_comp_d' := fun i j k _ _ => by
      rw [← ModuleCat.ofHom_comp, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp,
        P.d_comp_d, ModuleCat.hom_zero, LinearMap.baseChange_zero]
      rfl }

theorem baseChangeCx_d (P : CochainComplex (ModuleCat.{0} R) ℤ) (i j : ℤ) :
    letI := f.toAlgebra
    (baseChangeCx f P).d i j = ModuleCat.ofHom ((P.d i j).hom.baseChange S) :=
  rfl

/-- The base change of a free module has the same rank. PROVED. -/
theorem finrank_baseChangeCx [StrongRankCondition R] [StrongRankCondition S] (P : CochainComplex (ModuleCat.{0} R) ℤ)
    [∀ i, Module.Free R (P.X i)] [∀ i, Module.Finite R (P.X i)] (i : ℤ) :
    Module.finrank S ((baseChangeCx f P).X i) = Module.finrank R (P.X i) := by
  let := f.toAlgebra
  exact Module.finrank_baseChange

/-- **Compiled probe against the erased-differential impostor (C3)**: if every differential of
`P` is zero, every complex isomorphic to its base change has zero differentials. PROVED. -/
theorem differentials_zero_of_erased (P : CochainComplex (ModuleCat.{0} R) ℤ)
    (hP : ∀ i j, P.d i j = 0) (C : CochainComplex (ModuleCat.{0} S) ℤ)
    (e : baseChangeCx f P ≅ C) (i j : ℤ) : C.d i j = 0 := by
  have h0 : (baseChangeCx f P).d i j = 0 := by
    let := f.toAlgebra
    rw [baseChangeCx_d, hP, ModuleCat.hom_zero, LinearMap.baseChange_zero]
    rfl
  have h2 : C.d i j = e.inv.f i ≫ e.hom.f i ≫ C.d i j := by
    rw [← Category.assoc, ← HomologicalComplex.comp_f, e.inv_hom_id, HomologicalComplex.id_f,
      Category.id_comp]
  rw [h2, e.hom.comm, h0, Limits.zero_comp, Limits.comp_zero]

end BaseChange

/-- **The transfer after a base change to a field, with a comparison of complexes** (tex
4598–4631, model level): a minimal model `L` over the field `R'` homotopy equivalent to a complex
`P'` isomorphic, as a complex, to the base change of a bounded free model `P` over `R`, has total
rank at most that of `P`. PROVED. -/
theorem transfer_after_inverting_t' {R R' : Type} [CommRing R] [StrongRankCondition R] [Field R']
    (φ : R →+* R') (P : CochainComplex (ModuleCat.{0} R) ℤ) [∀ i, Module.Free R (P.X i)]
    [∀ i, Module.Finite R (P.X i)] (P' L : CochainComplex (ModuleCat.{0} R') ℤ) (a b : ℤ)
    [P'.IsStrictlyGE a] [P'.IsStrictlyLE b] [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Finite R' (P'.X i)] [∀ i, Module.Finite R' (L.X i)]
    (ebc : P' ≅ baseChangeCx φ P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal R' • (⊤ : Submodule R' (L.X j)))
    (e : HomotopyEquiv L P') (s : Finset ℤ) (genericRank rankTot : ℕ)
    (hgen : genericRank = ∑ n ∈ s, Module.finrank R' (L.X n))
    (htot : rankTot = ∑ n ∈ s, Module.finrank R (P.X n)) : genericRank ≤ rankTot := by
  have h := transferOfModels_final L P' a b hLmin e s genericRank
    (∑ n ∈ s, Module.finrank R' (P'.X n)) hgen rfl
  have heq : ∑ n ∈ s, Module.finrank R' (P'.X n) = ∑ n ∈ s, Module.finrank R (P.X n) :=
    Finset.sum_congr rfl fun n _ =>
      (HomologicalComplex.Hom.isoApp ebc n).toLinearEquiv.finrank_eq.trans
        (finrank_baseChangeCx φ P n)
  rw [htot, ← heq]
  exact h

section NonVacuity2

instance baseChangeCx_punit_subsingleton {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (i : ℤ) : Subsingleton ((baseChangeCx φ (punitCx R)).X i) := by
  let := φ.toAlgebra
  change Subsingleton (S ⊗[R] PUnit)
  infer_instance

/-- The zero complex is isomorphic to the base change of the zero complex. -/
def punitCxIsoBaseChange {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) :
    punitCx S ≅ baseChangeCx φ (punitCx R) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (LinearEquiv.ofSubsingleton ((punitCx S).X i)
      ((baseChangeCx φ (punitCx R)).X i)).toModuleIso)
    (fun i j _ => by
      ext x
      exact Subsingleton.elim _ _)

/-- **Non-vacuity of the inputs of `transfer_after_inverting_t'`** at `𝔽₂[[t]] → 𝔽₂((t))`, with the
zero complexes (the base-change comparison is an isomorphism of complexes; model level only — as
the peer's witness, this does not tie the models to the arithmetic cochains). PROVED. -/
theorem transfer_after_inverting_t'_nonvacuous : 0 ≤ 0 :=
  transfer_after_inverting_t' (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)))
    (punitCx (PowerSeries (ZMod 2))) (punitCx (LaurentSeries (ZMod 2)))
    (punitCx (LaurentSeries (ZMod 2))) 0 0 (punitCxIsoBaseChange _)
    (fun i j x => by rw [Subsingleton.elim x 0, map_zero]; exact Submodule.zero_mem _)
    (HomotopyEquiv.refl _) {0} 0 0
    (by rw [Finset.sum_singleton, Module.finrank_zero_of_subsingleton])
    (by rw [Finset.sum_singleton, Module.finrank_zero_of_subsingleton])

/-- **Non-vacuity of the reduction comparison**: the reduction modulo `t` of the zero complex is
isomorphic, as a complex, to the zero complex over `𝔽₂`. PROVED. -/
theorem reduction_nonvacuous :
    Nonempty (baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2)
      (punitCx (PowerSeries (ZMod 2))) ≅ punitCx (ZMod 2)) :=
  ⟨(punitCxIsoBaseChange _).symm⟩

end NonVacuity2

/-- **Named GLUE (C4): the global part of the residual model has no degree-`3` term.** For a
totally complex number field `K`, `cd₂ G_{K,S} ≤ 2` (Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, (8.3.17)), so `H³(G_{K,S}, W) = 0` and a minimal model of `RΓ(G_{K,S}, W)` has no
degree-`3` term. -/
def GlobalDegreeThreeVanishes (Dsel : SelData (ZMod 2)) : Prop :=
  Module.finrank (ZMod 2) (Dsel.G.X 3) = 0

/-- **`GlobalDegreeThreeVanishes` from the Milne print** (tex 4529, `H^{>2} = 0`): if the degree-`3`
term of the global part of the residual model is identified with Mathlib's continuous
`H³(G_{K,S₀}, W)` (`eG3`, the same kind of term-level identification as `eG` in degrees `0..2`),
then Milne ADT I.4.10 (`H³ = 0` for totally complex `K`) gives rank `0`. PROVED.

The identification targets Mathlib's `continuousCohomology 3 (Wrep K S₀)`, not the genuine `genH K
S₀ 3`: the comparison of the genuine continuous cochains with Mathlib's continuous cohomology
(`genHEquiv`) exists only in degrees `≤ 2`. That degree-`3` genuine-to-Mathlib comparison is the
missing piece for stating `eG3` against `genH` (or for deriving it from a minimal model
quasi-isomorphic to the genuine global complex). -/
theorem globalDegreeThreeVanishes_of_milne {K : Type} [Field K] [NumberField K]
    (h410 : MilneADT_I_4_10_totallyComplex) (hK : IsTotallyComplex K) {N r : ℕ}
    {D : Finset ℕ} (hN : N ≠ 0) (hr : r.Prime) (hD : ∀ p ∈ D, p.Prime)
    (Dsel : SelData (ZMod 2))
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2]
      continuousCohomology 3 (Wrep K (primesAboveSet K (chargedPrimes N r D)))) :
    GlobalDegreeThreeVanishes Dsel := by
  have hS : (primesAboveSet K (chargedPrimes N r D)).Finite :=
    primesAboveSet_finite K _ (ne_zero_of_mem_chargedPrimes hN hr hD)
  have hS2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal →
      v ∈ primesAboveSet K (chargedPrimes N r D) :=
    two_mem_primesAboveSet K (two_mem_chargedPrimes hN)
  have hsub : Subsingleton (continuousCohomology 3
      (Wrep K (primesAboveSet K (chargedPrimes N r D)))) :=
    h410 K hK _ hS hS2 _ inferInstance inferInstance
      (continuous_trivialRepS_action _ (ZMod 2 × ZMod 2)) 3 (by norm_num)
  unfold GlobalDegreeThreeVanishes
  rw [eG3.finrank_eq]
  exact Module.finrank_zero_of_subsingleton

variable (K : Type) [Field K] [NumberField K]
  (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

open Classical in
/-- **RC6's `ResidualRankCounts` with the transfer after inverting `t`, repaired** (tex
4453–4648; replaces `residualRankCounts_afterT`): all degrees `[0, 3]` of the bounded models are
counted, with the global degree-`3` vanishing `hG3` (named GLUE); the reduction modulo `t` of the
smaller-support free model `P` over `𝔽₂[[t]]` is isomorphic **as a complex** to the residual model
(`ered`), and `P'` is isomorphic **as a complex** to the base change of `P` to `𝔽₂((t))` (`ebc`);
the generic minimal model `L` over `𝔽₂((t))` with `e : L ≃ P'` (the text's tex 4626–4631, an
input). PROVED. -/
def residualRankCounts_afterT' (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hG3 : GlobalDegreeThreeVanishes Dsel)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    (e : HomotopyEquiv L P') :
    ResidualRankCounts :=
  haveI : ∀ i, Module.Finite (ZMod 2) ((selCx Dsel).toCC.X i) := fun i => by
    change Module.Finite (ZMod 2) (Dsel.G.X i × Dsel.U.X i × Dsel.L.X (i - 1))
    infer_instance
  residualRankCounts_mattuck K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Dsel (Finset.Icc 0 3)
    (∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) ((selCx Dsel).X n)) rfl
    (by
      have h := hG_of_genuineModel K _ Dsel (Finset.Icc 0 2) le_rfl eG
      have hsplit : Finset.Icc (0 : ℤ) 3 = insert 3 (Finset.Icc 0 2) := by decide
      rw [hsplit, Finset.sum_insert (by decide), hG3, zero_add]
      exact h)
    (hL_of_genuineModel2 K Sloc hr hD cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew)) Dsel
      (Finset.Icc 0 3) (archTotal K w) hUm hLm)
    (∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (L.X n))
    (transfer_after_inverting_t' _ P P' L 0 3 ebc hLmin e (Finset.Icc 0 3) _ _ rfl
      (Finset.sum_congr rfl fun n _ =>
        (HomologicalComplex.Hom.isoApp ered n).toLinearEquiv.finrank_eq.symm.trans
          (finrank_baseChangeCx _ P n)))

open Classical in
/-- **`residualRankCounts_afterT'` with the degree-`3` vanishing from the Milne print**: the named
GLUE `GlobalDegreeThreeVanishes Dsel` is replaced by the identification `eG3` of the degree-`3`
global term with Mathlib's continuous `H³(G_{K,S₀}, W)` (the same kind as `eG`), and discharged by
`globalDegreeThreeVanishes_of_milne` (Milne ADT I.4.10, already an argument). The degree-`3`
genuine-to-Mathlib comparison is the missing piece for stating `eG3` against `genH K S₀ 3`.
PROVED. -/
def residualRankCounts_afterT'' (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2]
      continuousCohomology 3 (Wrep K (primesAboveSet K (chargedPrimes N r D))))
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    (e : HomotopyEquiv L P') :
    ResidualRankCounts :=
  residualRankCounts_afterT' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG (globalDegreeThreeVanishes_of_milne h410 hK hN hr hD Dsel eG3) hUm hLm
    P ered P' L ebc hLmin e

end ZInQ.Contrib.CloudB3RC53.GenuineInst
