import ZInQKernel.Contrib.CloudB3RC53.Mattuck.ResidualGenuine

/-!
# Genuine instantiations, part 21: RC6's transfer after inverting `t`

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4598–4647.

**The finding.** In the text the support transfer happens over `𝔽₂[[t]]` and then `𝔽₂((t))`, not
over `𝔽₂`. At an active place the reduction of (4.4) has `A = D = ((1+t)^e − 1) I₂` with
`((1+t)^e − 1)/t ∈ 𝔽₂[[t]]^×`, so "the full, unramified and singular comparison blocks all become
contractible **after inverting `t`**" (tex 4618–4626). The text then says: "For each fixed finite
active support retain the comparison maps and homotopies, take the inner limit, and only then
invert `t`. Every active comparison cone is then contractible, so the original complex has the
same generic residual cohomology as the bounded smaller-support model" (tex 4626–4631). The
estimate (5.1) "applies before inverting `t` to the smaller-support model" (tex 4598), whose
reduction modulo `t` is the residual model with `W = E[2]`.

`residualRankCounts_genuine` (`Mattuck/ResidualGenuine.lean`) and `residualRankCounts_actual`
(`GenuineInst/CoefResidualCounts.lean`) instead take the change of condition with coefficients
`ZMod 2` and its acyclic quotient `hW : W.toCC.Acyclic` over `ZMod 2`, where `t = 0`: the
comparison blocks are `0`, and at an active place `h¹` of the unramified condition (`2`) differs
from `h¹` of the full local complex (`4`), so that quotient is not acyclic (the peer's
`active_full_change_not_acyclic`). Those constructors therefore only apply when no
unramified-to-full change happens at an active place. There is no bridge from the old `hW` to the
text's statement: the old one is about `𝔽₂`-coefficients, the text's about `𝔽₂((t))`.

**The additive variant.** The genuine Selmer complexes of this project have discrete finite
coefficients; continuous cochains with coefficients in `𝔽₂((t))`, the inner limit and the
inversion of `t` are not formalized. So the text's step is taken at the level of the models:

* `transfer_after_inverting_t`: for a ring map `R → R'` with `R'` a field, a bounded free model
  `P` over `R`, its degreewise base change `P'` over `R'` (`hbc`), and a minimal model `L` over `R'`
  homotopy equivalent to `P'`: `rank L ≤ rank P`;
* `residualRankCounts_afterT`: `residualRankCounts_mattuck` (with the genuine `hG`, `hL` of
  `residualRankCounts_genuine`) whose `transfer` comes from `transfer_after_inverting_t` at
  `R = 𝔽₂[[t]]`, `R' = 𝔽₂((t))`: the smaller-support free model `P` over `𝔽₂[[t]]` whose reduction
  modulo `t` is the residual model `Dsel` (`hred`, in ranks), its base change `P'` to `𝔽₂((t))`, and the
  generic minimal model `L` over `𝔽₂((t))` with `e : L ≃ P'` — the text's "same generic residual
  cohomology after inverting `t`" (tex 4626–4631), an input here (the inner limit and the
  contractibility of the active comparison cones over `𝔽₂((t))` are not formalized; in particular
  the PRINT `NekovarProp788ii` is not used by this variant). No `hW` over `ZMod 2`.
* Non-vacuity: `transfer_after_inverting_t_nonvacuous` (zero complexes over `𝔽₂[[t]]`,
  `𝔽₂((t))`; the hypotheses of the transfer are jointly satisfiable). Non-vacuity of the whole
  constructor is not shown (as for `residualRankCounts_genuine`).

**Classification.** PROVED (from the inputs listed).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open NumberField IsDedekindDomain CategoryTheory ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer ZInQ.Contrib.CloudB3RC53.Mattuck TensorProduct

/-- **The transfer after a base change to a field** (tex 4598–4631, model level): a minimal model
`L` over the field `R'` homotopy equivalent to the base change `P'` of a bounded free model `P` over
`R` has total rank at most that of `P`. PROVED. -/
theorem transfer_after_inverting_t {R R' : Type} [CommRing R] [StrongRankCondition R] [Field R']
    [Algebra R R'] (P : CochainComplex (ModuleCat.{0} R) ℤ) [∀ i, Module.Free R (P.X i)]
    [∀ i, Module.Finite R (P.X i)] (P' L : CochainComplex (ModuleCat.{0} R') ℤ) (a b : ℤ)
    [P'.IsStrictlyGE a] [P'.IsStrictlyLE b] [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Finite R' (P'.X i)] [∀ i, Module.Finite R' (L.X i)]
    (hbc : ∀ n, Nonempty (P'.X n ≃ₗ[R'] R' ⊗[R] P.X n))
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal R' • (⊤ : Submodule R' (L.X j)))
    (e : HomotopyEquiv L P') (s : Finset ℤ) (genericRank rankTot : ℕ)
    (hgen : genericRank = ∑ n ∈ s, Module.finrank R' (L.X n))
    (htot : rankTot = ∑ n ∈ s, Module.finrank R (P.X n)) : genericRank ≤ rankTot := by
  have h := transferOfModels_final L P' a b hLmin e s genericRank
    (∑ n ∈ s, Module.finrank R' (P'.X n)) hgen rfl
  have heq : ∑ n ∈ s, Module.finrank R' (P'.X n) = ∑ n ∈ s, Module.finrank R (P.X n) :=
    Finset.sum_congr rfl fun n _ => by
      rw [(hbc n).some.finrank_eq, Module.finrank_baseChange]
  rw [htot, ← heq]
  exact h

section NonVacuity

/-- The complex with every term `0` (`PUnit`) over a ring `R`. -/
def punitCx (R : Type) [CommRing R] : CochainComplex (ModuleCat.{0} R) ℤ where
  X _ := ModuleCat.of R PUnit
  d _ _ := 0

instance punitCx_subsingleton (R : Type) [CommRing R] (i : ℤ) : Subsingleton ((punitCx R).X i) :=
  inferInstanceAs (Subsingleton PUnit)

instance punitCx_free (R : Type) [CommRing R] (i : ℤ) : Module.Free R ((punitCx R).X i) :=
  inferInstanceAs (Module.Free R PUnit)

instance punitCx_finite (R : Type) [CommRing R] (i : ℤ) : Module.Finite R ((punitCx R).X i) :=
  inferInstanceAs (Module.Finite R PUnit)

instance punitCx_ge (R : Type) [CommRing R] : (punitCx R).IsStrictlyGE 0 :=
  (CochainComplex.isStrictlyGE_iff _ 0).2 fun _ _ => ModuleCat.isZero_of_subsingleton _

instance punitCx_le (R : Type) [CommRing R] : (punitCx R).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun _ _ => ModuleCat.isZero_of_subsingleton _

/-- **Non-vacuity of the hypotheses of `transfer_after_inverting_t`** at `𝔽₂[[t]] → 𝔽₂((t))`:
the zero complexes (total ranks `0 ≤ 0`). PROVED. -/
theorem transfer_after_inverting_t_nonvacuous :
    0 ≤ 0 :=
  transfer_after_inverting_t (punitCx (PowerSeries (ZMod 2)))
    (punitCx (LaurentSeries (ZMod 2))) (punitCx (LaurentSeries (ZMod 2))) 0 0
    (fun n => ⟨LinearEquiv.ofSubsingleton _ _⟩)
    (fun i j x => by rw [Subsingleton.elim x 0, map_zero]; exact Submodule.zero_mem _)
    (HomotopyEquiv.refl _) {0} 0 0
    (by rw [Finset.sum_singleton, Module.finrank_zero_of_subsingleton])
    (by rw [Finset.sum_singleton, Module.finrank_zero_of_subsingleton])

end NonVacuity

variable (K : Type) [Field K] [NumberField K]
  (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

open Classical in
/-- **Superseded** by `residualRankCounts_afterT'` (`ResidualAfterT2.lean`): this form accepts
erased-differential models (C3: `hred`, `hbc`, `e` never compare differentials) and omits degree
`3` (C4: the counts sum over `s ⊆ [0, 2]` while the models live in `[0, 3]`).

**RC6's `ResidualRankCounts` with the transfer after inverting `t`** (tex 4453–4648): as
`residualRankCounts_genuine` (the counts `kummer`, `hcond`, `hG`, `hL` from the genuine producers),
with `transfer` from `transfer_after_inverting_t` at `𝔽₂[[t]] → 𝔽₂((t))`: the smaller-support free
model `P` over `𝔽₂[[t]]` whose reduction modulo `t` has the ranks of the residual model `Dsel`
(`hred`; only its ranks are used), its base change `P'` to `𝔽₂((t))` (`hbc`), and the generic
minimal model `L` over
`𝔽₂((t))` homotopy equivalent to `P'` (`e`; the text's tex 4626–4631, an input). No acyclicity
hypothesis over `ZMod 2`. PROVED. -/
def residualRankCounts_afterT (h410 : MilneADT_I_4_10_totallyComplex)
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
    -- the residual model and its identifications
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (s : Finset ℤ) (hs : s ⊆ Finset.Icc 0 2)
    (eG : ∀ n ∈ s, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hUm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.U.X n) ≤ ∑ p ∈ chargedPrimes N r D,
      condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)]
    (hred : ∀ n ∈ s, Module.finrank (PowerSeries (ZMod 2)) (P.X n) =
      Module.finrank (ZMod 2) ((selCx Dsel).X n))
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ) (a b : ℤ)
    [P'.IsStrictlyGE a] [P'.IsStrictlyLE b] [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (hbc : ∀ n, Nonempty (P'.X n ≃ₗ[LaurentSeries (ZMod 2)]
      LaurentSeries (ZMod 2) ⊗[PowerSeries (ZMod 2)] P.X n))
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    (e : HomotopyEquiv L P') :
    ResidualRankCounts :=
  haveI : ∀ i, Module.Finite (ZMod 2) ((selCx Dsel).toCC.X i) := fun i => by
    change Module.Finite (ZMod 2) (Dsel.G.X i × Dsel.U.X i × Dsel.L.X (i - 1))
    infer_instance
  residualRankCounts_mattuck K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Dsel s (∑ n ∈ s, Module.finrank (ZMod 2) ((selCx Dsel).X n)) rfl
    (hG_of_genuineModel K _ Dsel s hs eG)
    (hL_of_genuineModel2 K Sloc hr hD cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew)) Dsel s
      (archTotal K w) hUm hLm)
    (∑ n ∈ s, Module.finrank (LaurentSeries (ZMod 2)) (L.X n))
    (transfer_after_inverting_t P P' L a b hbc hLmin e s _ _ rfl
      (Finset.sum_congr rfl fun n hn => (hred n hn).symm))

end ZInQ.Contrib.CloudB3RC53.GenuineInst
