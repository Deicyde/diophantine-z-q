import ZInQKernel.Contrib.OneProof.RC.Limits.ResidualBound
import ZInQKernel.Contrib.OneProof.RC.Limits.ResidualAlgebra
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SupportChange
import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.DegreewiseInvertible

/-!
# RC53 ResidualTransfer: the field `transfer` of RC6's residual rank counts

Lemma `ex:limits-residual-bound`, tex L4598–4647 ("It remains to transfer this estimate to the
original support"). RC6 records the transfer as the field

```
transfer : genericRank ≤ rankTot
```

of `ZInQ.Manuscript.RC.Limits.ResidualRankCounts` (`RC/Limits/ResidualBound.lean`, L617–624), with
`rankTot` the total rank of the finite free model of the smaller-support Selmer cone `C_{S₀}` and
`genericRank` the rank of the reduced generic residual model of the original support.

The text's argument (tex L4606–4647): the support comparison of [Nekovář, Proposition 7.8.8(ii)]
identifies `C_{S₀}` with the complex having unramified conditions at the active primes; every
active comparison cone is contractible after inverting `t`; a finite free model over the local ring
`𝔽₂((t))[G]` has a minimal model obtained by cancelling unit entries, whose ranks are the
dimensions of the cohomology after augmentation. Hence the generic rank is at most the rank of the
smaller-support model.

Nodes:
* `MinimalRankLe` (PROVED from RC6's `MinimalModelsExist`, itself PROVED as
  `minimalModelsExist_proof` in `MinimalModelsExist.lean`): over a local ring, a minimal
  bounded finite free complex homotopy equivalent to a bounded finite free complex `K₀` has, degree
  by degree, rank at most that of `K₀` (the minimal model `L₀` of `K₀` has ranks at most those of
  `K₀`, and two homotopy-equivalent minimal complexes are degreewise isomorphic,
  `MinimalHomotopyEquivDegreewise`).
* `TransferOfModels` (PROVED, exact type of the field): with `genericRank = ∑_{n∈s} rank Lⁿ` and
  `rankTot = ∑_{n∈s} rank K₀ⁿ`, `genericRank ≤ rankTot`.
* `transferBaseChange` (PROVED): the same with `rankTot` the rank *before* inverting `t`, i.e. of a
  finite free model over a ring `B` whose scalar extension to `S` is `K₀` (ranks are preserved).
* `SupportComparisonHomotopyEquiv` (PROVED from the GLUE input `SupportChangeInput`): the support
  comparison of bounded finite free Selmer models is an integral homotopy equivalence.
* `TransferOfSupportChange` (PROVED from the inputs named in its type): the field `transfer` for
  `rankTot` the total rank of the smaller-support Selmer model `selCx T.D` (the `rankTot` of
  `cone_of_selmerModel`) and `genericRank` the rank of a minimal model of the original-support
  complex, from `SupportChangeInput` and the contractibility of the active comparison cone after
  inverting `t` (an explicit hypothesis, tex L4625–4631: "Every active comparison cone is then
  contractible"; its algebra is RC6's `ResidualAlgebra`).

Caveat: `SupportChangeInput` takes `SupportChangeUnramified` (through `UnramifiedNewPlace`), which
requires degreewise isomorphisms of the full local complex at `q` with the 3-term tame model
`M → M ⊕ M → M`; genuine continuous cochains `C^•(G_{K_q}, M)` are only quasi-isomorphic to it (they
are nonzero in every degree `≥ 0`), so `supportComparisonHomotopyEquiv` and `transferOfSupportChange`
have consistent hypotheses (zero witnesses) that are not instantiable by genuine continuous
cochains; re-pointing to the genuine Galois support data is pending.
-/

namespace ZInQ.Contrib.CloudB3RC53.ResidualTransfer

open CategoryTheory CategoryTheory.Limits ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.MinimalComplexes
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

section Core

variable {S : Type u} [CommRing S] [IsLocalRing S]

/-- A free finite module of `finrank` zero is trivial. -/
theorem subsingleton_of_finrank_eq_zero {M : Type u} [AddCommGroup M] [Module S M]
    [Module.Free S M] [Module.Finite S M] (h : Module.finrank S M = 0) : Subsingleton M := by
  have hc : Fintype.card (Module.Free.ChooseBasisIndex S M) = 0 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]; exact h
  have : IsEmpty (Module.Free.ChooseBasisIndex S M) := Fintype.card_eq_zero_iff.mp hc
  exact (Module.Free.chooseBasis S M).repr.toEquiv.subsingleton

/-- **A minimal model has ranks at most those of any homotopy-equivalent finite free model**
(tex L4633–4647). Given RC6's `MinimalModelsExist S` (PROVED: `minimalModelsExist_proof`) over a
local ring `S`, let `K₀` be a
bounded (`IsStrictlyGE a`, `IsStrictlyLE b`) complex of finite free modules and `L` a minimal
(`d(L) ⊆ 𝔪 L`) bounded complex of finite free modules with a homotopy equivalence `L ≃ K₀`. Then
`rank Lⁱ ≤ rank K₀ⁱ` for every `i`. Classification: PROVED (from `MinimalModelsExist`). -/
def MinimalRankLe : Prop :=
  ∀ (S : Type u) [CommRing S] [IsLocalRing S], MinimalModelsExist S →
    ∀ (L K₀ : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    [L.IsStrictlyGE a] [L.IsStrictlyLE b] [K₀.IsStrictlyGE a] [K₀.IsStrictlyLE b]
    [∀ i, Module.Free S (L.X i)] [∀ i, Module.Finite S (L.X i)]
    [∀ i, Module.Free S (K₀.X i)] [∀ i, Module.Finite S (K₀.X i)],
    (∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S (L.X j))) →
    HomotopyEquiv L K₀ → ∀ i, Module.finrank S (L.X i) ≤ Module.finrank S (K₀.X i)

theorem minimalRankLe_proof : MinimalRankLe.{u} := by
  intro S _ _ hMM L K₀ a b _ _ _ _ _ _ _ _ hLmin e i
  have hbdd : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → Subsingleton (K₀.X i) := by
    refine ⟨a, b, fun i hi => ?_⟩
    rcases hi with hi | hi
    · exact ModuleCat.subsingleton_of_isZero (K₀.isZero_of_isStrictlyGE a i hi)
    · exact ModuleCat.subsingleton_of_isZero (K₀.isZero_of_isStrictlyLE b i hi)
  obtain ⟨L₀, ⟨e₀⟩, hfree, hmin, hle, -⟩ :=
    hMM K₀ (fun i => ⟨inferInstance, inferInstance⟩) hbdd
  have : ∀ i, Module.Free S (L₀.X i) := fun i => (hfree i).1
  have : ∀ i, Module.Finite S (L₀.X i) := fun i => (hfree i).2
  -- `L₀` is bounded: its ranks vanish where those of `K₀` do
  have hzero : ∀ i, Subsingleton (K₀.X i) → IsZero (L₀.X i) := by
    intro i hi
    have h0 : Module.finrank S (K₀.X i) = 0 := Module.finrank_zero_of_subsingleton
    have : Module.finrank S (L₀.X i) = 0 := Nat.eq_zero_of_le_zero (h0 ▸ hle i)
    have := subsingleton_of_finrank_eq_zero this
    exact ModuleCat.isZero_of_subsingleton _
  have : L₀.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hzero i (ModuleCat.subsingleton_of_isZero (K₀.isZero_of_isStrictlyGE a i hi))
  have : L₀.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hzero i (ModuleCat.subsingleton_of_isZero (K₀.isZero_of_isStrictlyLE b i hi))
  have hbij := minimalHomotopyEquivDegreewise_proof S L L₀ a b hLmin hmin (e.trans e₀) i
  rw [(LinearEquiv.ofBijective _ hbij).finrank_eq]
  exact hle i

end Core

/-- **RC6's field `transfer`, from models** (tex L4598–4647; exact type `genericRank ≤ rankTot`).
Given `MinimalModelsExist S`, a bounded finite free model `K₀` of the smaller-support complex (after
inverting `t`) and a minimal bounded finite free model `L` of the original-support complex with a
homotopy equivalence `L ≃ K₀`, and `genericRank`, `rankTot` the total ranks over a finite degree
set `s`, the field `transfer` holds. Classification: PROVED (from `MinimalModelsExist`). -/
theorem transferOfModels {S : Type u} [CommRing S] [IsLocalRing S] (hMM : MinimalModelsExist S)
    (L K₀ : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    [L.IsStrictlyGE a] [L.IsStrictlyLE b] [K₀.IsStrictlyGE a] [K₀.IsStrictlyLE b]
    [∀ i, Module.Free S (L.X i)] [∀ i, Module.Finite S (L.X i)]
    [∀ i, Module.Free S (K₀.X i)] [∀ i, Module.Finite S (K₀.X i)]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S (L.X j)))
    (e : HomotopyEquiv L K₀) (s : Finset ℤ) (genericRank rankTot : ℕ)
    (hgen : genericRank = ∑ n ∈ s, Module.finrank S (L.X n))
    (htot : rankTot = ∑ n ∈ s, Module.finrank S (K₀.X n)) :
    genericRank ≤ rankTot := by
  rw [hgen, htot]
  exact Finset.sum_le_sum fun n _ => minimalRankLe_proof S hMM L K₀ a b hLmin e n

/-- **The rank before inverting `t`** (tex L4598–4600: "The estimate applies before inverting `t` to
the smaller-support model"). If `K₀` is the scalar extension along `f : B →+* S` of a complex `K₀ᴮ`
of finite free `B`-modules (`B` with the strong rank condition, e.g. `𝔽₂[[t]] → 𝔽₂((t))`), then
`rank_S K₀ⁿ = rank_B K₀ᴮⁿ`. PROVED. -/
theorem finrank_extendScalars {B S : Type u} [CommRing B] [CommRing S] [StrongRankCondition B]
    [Nontrivial S] (f : B →+* S) (M : ModuleCat.{u} B) [Module.Free B M] [Module.Finite B M] :
    Module.finrank S ((ModuleCat.extendScalars.{u, u, u} f).obj M) = Module.finrank B M := by
  let := f.toAlgebra
  change Module.finrank S (TensorProduct B S M) = _
  exact Module.finrank_baseChange

/-- The scalar extension of a cochain complex along `f : B →+* S`. -/
noncomputable abbrev extCx {B S : Type u} [CommRing B] [CommRing S] (f : B →+* S)
    (K : CochainComplex (ModuleCat.{u} B) ℤ) : CochainComplex (ModuleCat.{u} S) ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex _).obj K

/-- **RC6's field `transfer` with `rankTot` the rank before inverting `t`** (tex L4598–4647). As
`transferOfModels`, with `K₀` the scalar extension along `f : B →+* S` of a finite free model `K₀ᴮ`
over `B` and `rankTot = ∑_{n∈s} rank_B K₀ᴮⁿ`. Classification: PROVED (from `MinimalModelsExist`). -/
theorem transferBaseChange {B S : Type u} [CommRing B] [CommRing S] [IsLocalRing S]
    [StrongRankCondition B] (f : B →+* S) (hMM : MinimalModelsExist S)
    (L : CochainComplex (ModuleCat.{u} S) ℤ) (K₀B : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ)
    [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Free S (L.X i)] [∀ i, Module.Finite S (L.X i)]
    [∀ i, Module.Free B (K₀B.X i)] [∀ i, Module.Finite B (K₀B.X i)]
    [(extCx f K₀B).IsStrictlyGE a]
    [(extCx f K₀B).IsStrictlyLE b]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S (L.X j)))
    (e : HomotopyEquiv L (extCx f K₀B))
    (s : Finset ℤ) (genericRank rankTot : ℕ)
    (hgen : genericRank = ∑ n ∈ s, Module.finrank S (L.X n))
    (htot : rankTot = ∑ n ∈ s, Module.finrank B (K₀B.X n)) :
    genericRank ≤ rankTot := by
  let := f.toAlgebra
  have : ∀ i, Module.Free S
      ((extCx f K₀B).X i) :=
    fun i => by
      change Module.Free S (TensorProduct B S (K₀B.X i))
      infer_instance
  have : ∀ i, Module.Finite S
      ((extCx f K₀B).X i) :=
    fun i => by
      change Module.Finite S (TensorProduct B S (K₀B.X i))
      infer_instance
  refine transferOfModels hMM L _ a b hLmin e s genericRank rankTot hgen ?_
  rw [htot]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact (finrank_extendScalars f (K₀B.X n)).symm

/-- **The support comparison is an integral homotopy equivalence** (tex L4612–4618, with the
support change of [Nekovář, Proposition 7.8.8(ii)] as the GLUE input `SupportChangeInput` of
`SelmerDuality/SupportChange.lean`). If the old and new Selmer models `selCx T.D`, `selCx T.Dp`
are bounded complexes of free modules, the support comparison is the forward map of a homotopy
equivalence (a quasi-isomorphism of bounded free complexes has an integral homotopy inverse,
`QuasiIsoFreeHomotopyInverse`). Caveat: the hypothesis `SupportChangeUnramified` (through
`UnramifiedNewPlace`) is not instantiable by genuine continuous cochains; re-pointing to the genuine
Galois support data is pending.
Classification: PROVED (from the GLUE input). -/
theorem supportComparisonHomotopyEquiv {S : Type u} [CommRing S] (T : SupportChangeData S)
    (H : SupportChangeUnramified T) (hSC : SupportChangeInput T H) (a b : ℤ)
    [(selCx T.D).toCC.IsStrictlyGE a] [(selCx T.D).toCC.IsStrictlyLE b]
    [(selCx T.Dp).toCC.IsStrictlyGE a] [(selCx T.Dp).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx T.D).toCC.X n)] [∀ n, Module.Free S ((selCx T.Dp).toCC.X n)] :
    ∃ e : HomotopyEquiv (selCx T.D).toCC (selCx T.Dp).toCC, e.hom = GHom.toCC (supportMap T) := by
  have : QuasiIso (GHom.toCC (supportMap T)) := hSC
  exact quasiIsoFreeHomotopyInverse_proof S _ _ a b (GHom.toCC (supportMap T))

/-- **RC6's field `transfer` from the support change** (tex L4598–4647). Over a local ring `S`
(the inner limit after inverting `t`), let:
* `T` be the support change from the smaller support `S₀` (Selmer data `T.D`) to the complex with
  unramified conditions at the active primes (`T.Dp`), with the GLUE input `SupportChangeInput`
  (Nekovář 7.8.8(ii), tex L4612–4618) and bounded free Selmer models;
* `C` the original-support complex, with the active comparison `jact : C ⟶ (selCx T.Dp).toCC`
  whose mapping cone is contractible after inverting `t` (hypothesis `hact`, tex L4619–4631: "Every
  active comparison cone is then contractible"; the local algebra — `C = 0`, `A = D` with
  `((1+t)^{±e} − 1)/t` units — is RC6's `ResidualAlgebra`);
* `L` a minimal bounded finite free model of `C` (`eL : L ≃ C`), `genericRank` its total rank, and
  `rankTot` the total rank of the smaller-support Selmer model `selCx T.D` (the quantity of
  `cone_of_selmerModel`).
Then, given RC6's `MinimalModelsExist S` (PROVED: `minimalModelsExist_proof`; discharged in
`transferOfSupportChange_final`), `genericRank ≤ rankTot`. Caveat: the hypothesis
`SupportChangeUnramified` (through `UnramifiedNewPlace`) is not instantiable by genuine continuous
cochains; re-pointing to the genuine Galois support data is pending.
Classification: PROVED (from the inputs in its type). -/
theorem transferOfSupportChange {S : Type u} [CommRing S] [IsLocalRing S]
    (hMM : MinimalModelsExist S) (T : SupportChangeData S) (H : SupportChangeUnramified T)
    (hSC : SupportChangeInput T H) (a b : ℤ)
    [(selCx T.D).toCC.IsStrictlyGE a] [(selCx T.D).toCC.IsStrictlyLE b]
    [(selCx T.Dp).toCC.IsStrictlyGE a] [(selCx T.Dp).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx T.D).toCC.X n)] [∀ n, Module.Free S ((selCx T.Dp).toCC.X n)]
    [∀ n, Module.Finite S ((selCx T.D).toCC.X n)]
    (C : CochainComplex (ModuleCat.{u} S) ℤ) (jact : C ⟶ (selCx T.Dp).toCC)
    (hact : Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone jact)) 0))
    (L : CochainComplex (ModuleCat.{u} S) ℤ) [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Free S (L.X i)] [∀ i, Module.Finite S (L.X i)]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S (L.X j)))
    (eL : HomotopyEquiv L C) (s : Finset ℤ) (genericRank rankTot : ℕ)
    (hgen : genericRank = ∑ n ∈ s, Module.finrank S (L.X n))
    (htot : rankTot = ∑ n ∈ s, Module.finrank S ((selCx T.D).X n)) :
    genericRank ≤ rankTot := by
  obtain ⟨e₁, -⟩ := supportComparisonHomotopyEquiv T H hSC a b
  obtain ⟨hc⟩ := hact
  obtain ⟨e₂, -⟩ := homotopyEquiv_of_cone_contractible jact hc
  exact transferOfModels hMM L (selCx T.D).toCC a b hLmin ((eL.trans e₂).trans e₁.symm) s
    genericRank rankTot hgen htot

end ZInQ.Contrib.CloudB3RC53.ResidualTransfer
