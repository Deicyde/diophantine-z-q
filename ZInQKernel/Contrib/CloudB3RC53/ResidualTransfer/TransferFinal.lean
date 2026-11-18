import ZInQKernel.Contrib.CloudB3RC53.ResidualTransfer.Transfer
import ZInQKernel.Contrib.CloudB3RC53.ResidualTransfer.MinimalModelsExist
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.SelmerCone

/-!
# RC53 ResidualTransfer: the field `transfer` with the minimal models and the active cone discharged

Lemma `ex:limits-residual-bound`, tex L4598–4647. `Transfer.lean` proves RC6's field
`transfer : genericRank ≤ rankTot` from three inputs: RC6's `MinimalModelsExist S`, the support
comparison `SupportChangeInput` (GLUE, Nekovář 7.8.8(ii)), and the contractibility `hact` of the
active comparison cone after inverting `t`. Here:

* `transferOfModels_final`, `transferOfSupportChange_final` (PROVED): the same statements with
  `MinimalModelsExist S` discharged by `minimalModelsExist_proof`.
* `quasiIso_f_of_shortExact_acyclic` (PROVED): in a short exact sequence of cochain complexes of
  modules `0 → X₁ → X₂ → X₃ → 0` with `X₃` acyclic, `X₁ → X₂` is a quasi-isomorphism (long exact
  homology sequence).
* `acyclic_of_contractible`, `twoTerm_acyclic`, `bijective_unit_smul`, `activeSingular_unit`
  (PROVED): the singular quotient at an active place, a two-term complex `[M --D--> M]` with
  `D = ((1+t)^e − 1)·φ`, `e` odd, `φ` bijective, is acyclic over `𝔽₂((t))` (tex L4619–4624:
  "`((1+t)^e − 1)/t` [is a unit] ... after inverting `t`"; RC6 `isUnit_laurentSeries_...`).
* `hact_of_singularQuotient` (PROVED, tex L4624–4631): for the change of local conditions
  `0 → U' → U → W → 0` of `SelmerDuality` (`changeMap`, `RelaxedQuotientNode`) with `W` acyclic and
  bounded finite free Selmer models, the cone of `C(U') → C(U)` is contractible — exactly the input
  `hact` of `transferOfSupportChange`.
* `transfer_final` (PROVED from the inputs in its type): the field `transfer` for a minimal model of
  the original-support complex `C(U_full)` (full conditions at the active primes), whose only
  remaining inputs are `SupportChangeInput` (GLUE) and the stateable local data (the short exact
  sequence `U^ur → U^full → W` of local conditions, `W` acyclic, freeness and bounds). An earlier
  version had the direction reversed (see its docstring); `transfer_final_nonvacuous` (in `TransferFinalNonVacuity.lean`) checks that
  the corrected hypotheses are jointly satisfiable.

Universe: the cone lemmas of `SelmerCone.lean` are stated for `ModuleCat.{0}`, so the last two
nodes take `S : Type` (the text's `𝔽₂((t))[G]` and `𝔽₂((t))` are such).
-/

namespace ZInQ.Contrib.CloudB3RC53.ResidualTransfer

open CategoryTheory CategoryTheory.Limits ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.MinimalComplexes ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

/-- **The field `transfer` from models, `MinimalModelsExist` discharged** (tex L4633–4647).
Classification: PROVED. -/
theorem transferOfModels_final {S : Type u} [CommRing S] [IsLocalRing S]
    (L K₀ : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    [L.IsStrictlyGE a] [L.IsStrictlyLE b] [K₀.IsStrictlyGE a] [K₀.IsStrictlyLE b]
    [∀ i, Module.Free S (L.X i)] [∀ i, Module.Finite S (L.X i)]
    [∀ i, Module.Free S (K₀.X i)] [∀ i, Module.Finite S (K₀.X i)]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S (L.X j)))
    (e : HomotopyEquiv L K₀) (s : Finset ℤ) (genericRank rankTot : ℕ)
    (hgen : genericRank = ∑ n ∈ s, Module.finrank S (L.X n))
    (htot : rankTot = ∑ n ∈ s, Module.finrank S (K₀.X n)) :
    genericRank ≤ rankTot :=
  transferOfModels (minimalModelsExist_proof S) L K₀ a b hLmin e s genericRank rankTot hgen htot

/-- **The field `transfer` from the support change, `MinimalModelsExist` discharged** (tex
L4598–4647). Remaining inputs: `SupportChangeInput` (GLUE) and `hact`. Classification: PROVED. -/
theorem transferOfSupportChange_final {S : Type u} [CommRing S] [IsLocalRing S]
    (T : SupportChangeData S) (H : SupportChangeUnramified T)
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
    genericRank ≤ rankTot :=
  transferOfSupportChange (minimalModelsExist_proof S) T H hSC a b C jact hact L hLmin eL s
    genericRank rankTot hgen htot

/-! ### The active comparison cone -/

section Acyclic

variable {R : Type u} [CommRing R]

/-- **A short exact sequence with acyclic quotient**: `X₁ → X₂` is a quasi-isomorphism (from the
long exact homology sequence). PROVED. -/
theorem quasiIso_f_of_shortExact_acyclic
    {E : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)} (hE : E.ShortExact)
    (h3 : E.X₃.Acyclic) : QuasiIso E.f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz : ∀ j, IsZero (E.X₃.homology j) := fun j =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h3 j)
  have hmono : Mono (HomologicalComplex.homologyMap E.f i) :=
    (hE.homology_exact₁ (i - 1) i (by simp)).mono_g ((hz (i - 1)).eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap E.f i) :=
    (hE.homology_exact₂ i).epi_f ((hz i).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- A contractible complex is acyclic. PROVED. -/
theorem acyclic_of_contractible (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : Nonempty (Homotopy (𝟙 K) 0)) : K.Acyclic := by
  obtain ⟨h⟩ := h
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have := h.homologyMap_eq i
  rw [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at this
  exact this

/-- **A two-term complex with bijective differential is acyclic** (the singular quotient at an
active place after inverting `t`, tex L4619–4624). If `W` vanishes outside degrees `n, n + 1` and
`d : Wⁿ → Wⁿ⁺¹` is bijective, then `W` is acyclic. PROVED. -/
theorem twoTerm_acyclic (W : GCx R) (n : ℤ)
    (hz : ∀ i, i ≠ n → i ≠ n + 1 → Subsingleton (W.X i))
    (hd : Function.Bijective (W.d n (n + 1) rfl)) : W.toCC.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff' W.toCC (i - 1) i (i + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro (x : W.X i) hx
  have hx' : W.d i (i + 1) rfl x = 0 := by
    rw [← GCx.toCC_d_hom W i (i + 1) rfl]; exact hx
  show ∃ y : W.X (i - 1), (W.toCC.d (i - 1) i).hom y = x
  by_cases hi : i = n
  · subst hi
    have hx0 : x = 0 := hd.1 (by rw [hx', map_zero])
    exact ⟨0, by rw [hx0]; exact LinearMap.map_zero _⟩
  · by_cases hi' : i = n + 1
    · subst hi'
      have e : n + 1 - 1 = n := by ring
      have key : ∀ (m : ℤ) (hm : m = n) (z : W.X (n + 1)), ∃ y : W.X m,
          (W.toCC.d m (n + 1)).hom y = z := by
        intro m hm z
        subst hm
        obtain ⟨y, hy⟩ := hd.2 z
        exact ⟨y, by rw [GCx.toCC_d_hom W m (m + 1) rfl]; exact hy⟩
      exact key (n + 1 - 1) e x
    · exact ⟨0, @Subsingleton.elim (W.X i) (hz i hi hi') _ _⟩

/-- A unit multiple of a bijective linear map is bijective. PROVED. -/
theorem bijective_unit_smul {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {c : R} (hc : IsUnit c) {φ : M →ₗ[R] N} (hφ : Function.Bijective φ) :
    Function.Bijective (c • φ) := by
  obtain ⟨u, rfl⟩ := hc
  refine ⟨fun x y h => hφ.1 ?_, fun y => ?_⟩
  · have h' : (↑u⁻¹ : R) • ((u : R) • φ x) = (↑u⁻¹ : R) • ((u : R) • φ y) := by
      simpa using congrArg (fun z => (↑u⁻¹ : R) • z) h
    simpa [smul_smul] using h'
  · obtain ⟨x, hx⟩ := hφ.2 y
    exact ⟨(↑u⁻¹ : R) • x, by simp [map_smul, hx, smul_smul]⟩

end Acyclic

/-- **The active singular differential is invertible after inverting `t`** (tex L4619–4624): at an
oriented active place `D = ((1+t)^e − 1)·φ` with `e` odd; over `𝔽₂((t))` the scalar is a unit
(RC6 `isUnit_laurentSeries_one_add_X_pow_sub_one`), so `D` is bijective whenever `φ` is.
PROVED. -/
theorem activeSingular_bijective {e : ℕ} (he : Odd e) {M N : Type*} [AddCommGroup M]
    [Module (LaurentSeries (ZMod 2)) M] [AddCommGroup N] [Module (LaurentSeries (ZMod 2)) N]
    {φ : M →ₗ[LaurentSeries (ZMod 2)] N} (hφ : Function.Bijective φ) :
    Function.Bijective
      (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))
        (((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ e - 1) • φ) :=
  bijective_unit_smul (isUnit_laurentSeries_one_add_X_pow_sub_one he) hφ

/-- **The active comparison cone is contractible** (tex L4624–4631: "Every active comparison cone is
then contractible"). Let `D` be Selmer data over a commutative ring `S`, and `0 → U' --f--> U --g-->
W → 0` a degreewise short exact sequence of local conditions (`RelaxedQuotientNode`) whose quotient
`W` (the singular quotient) is acyclic. If the Selmer models `C(U')` and `C(U)` are bounded and
free, the mapping cone of the comparison `C(U') → C(U)` is contractible: this is the input `hact`
of `transferOfSupportChange`, with `jact = GHom.toCC (changeMap D f)`. Classification: PROVED. -/
theorem hact_of_singularQuotient {S : Type} [CommRing S] (D : SelData S) (U' W : GCx S)
    (f : GHom U' D.U) (g : GHom D.U W)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : D.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) (a b : ℤ)
    [(selCx (restrictData D f)).toCC.IsStrictlyGE a] [(selCx (restrictData D f)).toCC.IsStrictlyLE b]
    [(selCx D).toCC.IsStrictlyGE a] [(selCx D).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx (restrictData D f)).toCC.X n)]
    [∀ n, Module.Free S ((selCx D).toCC.X n)] :
    Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone (GHom.toCC (changeMap D f)))) 0) := by
  have hSE := relaxedQuotientNode_proof S D U' W f g hfg hinj hsurj hex
  have : QuasiIso (GHom.toCC (changeMap D f)) :=
    quasiIso_f_of_shortExact_acyclic (E := changeSES D f g hfg) hSE hW
  exact cone_contractible_of_homotopyEquiv _ (homotopyEquiv_of_quasiIso_free a b _)

/-- **The field `transfer`, final form** (tex L4598–4647; direction as in tex L4612–4631). Over a
local ring `S` (`𝔽₂((t))[G]` or `𝔽₂((t))`):
* the smaller-support model `C_{S₀} = selCx T.D` is related by the support comparison
  (`SupportChangeInput`, GLUE: Nekovář 7.8.8(ii)) to `selCx T.Dp`, the complex with the
  **unramified** condition `U' = T.Dp.U` at the active primes (tex L4612–4618);
* replacing the unramified condition by the **full** one gives the **original-support** complex:
  Selmer data `Dfull` with full condition `Dfull.U`, the inclusion `f : U' → Dfull.U` with
  `T.Dp = restrictData Dfull f`, and the singular quotient `0 → U' → Dfull.U → W → 0` acyclic after
  inverting `t` (tex L4619–4631; e.g. `twoTerm_acyclic` with `activeSingular_bijective`);
* `genericRank` is typed against a minimal model `L ≃ C(U_full) = selCx Dfull` of the
  original-support complex.
Then `genericRank ≤ rankTot` with `rankTot` the total rank of `C_{S₀}`: the ranks of `L` are
transported to `C(U')` by the active comparison (`hact_of_singularQuotient`), then to `C_{S₀}` by
the inverse support comparison. Remaining inputs: only `SupportChangeInput` and the stateable local
data in the type.

*Correction note.* An earlier version of this theorem had the modelling direction reversed: it took
the minimal model `L` of `C(U')` (the unramified side) as the original-support complex. This version
follows tex L4612–4631. Classification: PROVED (from the inputs in its type). -/
theorem transfer_final {S : Type} [CommRing S] [IsLocalRing S]
    (T : SupportChangeData S) (H : SupportChangeUnramified T)
    (hSC : SupportChangeInput T H) (a b : ℤ)
    [(selCx T.D).toCC.IsStrictlyGE a] [(selCx T.D).toCC.IsStrictlyLE b]
    [(selCx T.Dp).toCC.IsStrictlyGE a] [(selCx T.Dp).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx T.D).toCC.X n)] [∀ n, Module.Free S ((selCx T.Dp).toCC.X n)]
    [∀ n, Module.Finite S ((selCx T.D).toCC.X n)]
    (Dfull : SelData S) (W : GCx S) (f : GHom T.Dp.U Dfull.U) (g : GHom Dfull.U W)
    (hDp : T.Dp = restrictData Dfull f)
    (hfg : ∀ i (u : T.Dp.U.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic)
    [(selCx (restrictData Dfull f)).toCC.IsStrictlyGE a]
    [(selCx (restrictData Dfull f)).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx (restrictData Dfull f)).toCC.X n)]
    [(selCx Dfull).toCC.IsStrictlyGE a] [(selCx Dfull).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx Dfull).toCC.X n)]
    (L : CochainComplex (ModuleCat.{0} S) ℤ) [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Free S (L.X i)] [∀ i, Module.Finite S (L.X i)]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S (L.X j)))
    (eL : HomotopyEquiv L (selCx Dfull).toCC) (s : Finset ℤ)
    (genericRank rankTot : ℕ)
    (hgen : genericRank = ∑ n ∈ s, Module.finrank S (L.X n))
    (htot : rankTot = ∑ n ∈ s, Module.finrank S ((selCx T.D).X n)) :
    genericRank ≤ rankTot := by
  -- `C_{S₀} ≃ C(U')`: the support comparison (GLUE input)
  obtain ⟨e₁, -⟩ := supportComparisonHomotopyEquiv T H hSC a b
  -- `C(U') ≃ C(U_full)`: the active comparison cone is contractible
  obtain ⟨hc⟩ := hact_of_singularQuotient Dfull T.Dp.U W f g hfg hinj hsurj hex hW a b
  obtain ⟨e₂, -⟩ := homotopyEquiv_of_cone_contractible _ hc
  -- `selCx T.Dp = selCx (restrictData Dfull f)`
  let e₃ : HomotopyEquiv (selCx T.Dp).toCC (selCx (restrictData Dfull f)).toCC :=
    HomotopyEquiv.ofIso (eqToIso (congrArg (fun D => (selCx D).toCC) hDp))
  exact transferOfModels_final L (selCx T.D).toCC a b hLmin
    (((eL.trans e₂.symm).trans e₃.symm).trans e₁.symm) s genericRank rankTot hgen htot

end ZInQ.Contrib.CloudB3RC53.ResidualTransfer
