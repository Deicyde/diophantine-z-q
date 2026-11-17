import ZInQKernel.Contrib.OneProof.NeronFLT.Henselian
import ZInQKernel.Contrib.OneProof.StrictHenselizationPair

/-! # neron-flt: `NeronExt.NeronDVRLocal` from Néron existence over henselian DVRs and descent from `R^sh`

`NeronExt.NeronDVRLocal` (neron-ext's leaf: BLR §1.4 Thm. 3 over the DVRs `(𝓞_L)_v`) is reduced to
* **proved** (vendored FLT development, `NeronFLT.exists_neron_of_henselian`): an abelian variety over the fraction
  field of a *henselian* DVR has a Néron model (BLR §1.4 Thm. 3 over a henselian DVR; any residue field);
* **proved** (gt-shpair, `GapSHPair.isSHSep_inertia`): every DVR `O ⊆ L` has an unramified strictly henselian
  extension `O₁ ⊆ K₁` with `K₁/L` separable (`IsSHSep`), the valuation ring of the inertia field in `L̄`;
* the new **leaf `NeronDescentSH`**: descent of the existence of a Néron model from the strict henselization.

The leaf is the "if" half of BLR's statement that a smooth group scheme `X_K` of finite type has a Néron model over
`R` if and only if `X_K ⊗ K^sh` has one over `R^sh` (BLR, *Néron models*, §6.5 / §7.2; number UNVERIFIED, recalled,
no network), specialised to abelian varieties.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField

namespace NeronFLT

/-- **LEAF `NeronDescentSH`** (Bosch–Lütkebohmert–Raynaud, *Néron models*, Springer 1990: descent of Néron models
along `R → R^sh`; §6.5 and §7.2 Thm. 1, numbers and wording recalled, UNVERIFIED, no network). *Printed* (as
recalled): for a discrete valuation ring `R` with fraction field `K`, strict henselization `R^sh` and `K^sh` its
fraction field, a smooth `K`-group scheme of finite type `X_K` admits a Néron model over `R` if and only if
`X_K ⊗_K K^sh` admits a Néron model over `R^sh`.

*Lean form* (the "if" direction, for an abelian variety `A = X_K`): `R` any DVR with fraction field `K`; `O₁ ⊆ K₁`
any extension of the valuation ring `O = R ⊆ K` (Mathlib's `(ValuationRing.valuation R K).valuationSubring`, whose
elements are exactly the image of `R`) with `IsSHSep O O₁` (strictly henselian DVR, `K₁/K` separable algebraic,
ramification index 1, separable residue extension), which characterizes `O₁` as `R^sh` up to isomorphism over `R`
(gt-shpair's report §2, via EGA IV₄ 18.8.8; the same pinning as the chain's leaf
`GapSHPair.NeronBaseChangeStrictHenselization`). A Néron model is `CToPrinted.IsNeronModelOver` (BLR §1.2 Def. 1)
with an isomorphism of its generic fibre with the abelian variety. -/
def NeronDescentSH : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (K₁ : Type) [Field K₁] [Algebra K K₁] (O₁ : ValuationSubring K₁)
    (hO : O₁.comap (algebraMap K K₁) = (ValuationRing.valuation R K).valuationSubring),
    GapSHPair.IsSHSep (ValuationRing.valuation R K).valuationSubring O₁ hO →
    ∀ A : PkgI3.AbVar K,
      (∃ N₁ : Over (Spec (CommRingCat.of O₁)), CToPrinted.IsNeronModelOver O₁ K₁ N₁ ∧
        Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O₁ K₁)))).obj N₁ ≅
          (A.baseChange K₁).X)) →
      ∃ N : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R K N ∧
        Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj N ≅ A.X)

section ValSub

variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem mem_valSub_iff (x : K) :
    x ∈ (ValuationRing.valuation R K).valuationSubring ↔ ∃ a : R, algebraMap R K a = x :=
  ValuationRing.mem_integer_iff R K x

/-- `R` is isomorphic to its valuation subring of `K`. -/
def valSubEquiv : R ≃+* (ValuationRing.valuation R K).valuationSubring :=
  RingEquiv.ofBijective
    { toFun := fun a => ⟨algebraMap R K a, (mem_valSub_iff R K _).2 ⟨a, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
    ⟨fun a b h => IsFractionRing.injective R K (congrArg Subtype.val h),
     fun x => by
       obtain ⟨a, ha⟩ := (mem_valSub_iff R K x.1).1 x.2
       exact ⟨a, Subtype.ext ha⟩⟩

theorem isDVR_valSub : IsDiscreteValuationRing (ValuationRing.valuation R K).valuationSubring :=
  RingEquivClass.isDiscreteValuationRing (valSubEquiv R K)

/-- **Néron models over any DVR, from the descent leaf.** -/
theorem exists_neron_of_descentSH (h : NeronDescentSH) (A : PkgI3.AbVar K) :
    ∃ N : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R K N ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj N ≅ A.X) := by
  haveI := isDVR_valSub R K
  obtain ⟨w, hw⟩ := GapSHPair.exists_comap_eq (Ω := AlgebraicClosure K)
    (ValuationRing.valuation R K).valuationSubring
  have hS := GapSHPair.isSHSep_inertia w hw
  haveI : IsDiscreteValuationRing (GapSHPair.wE (K := K) w) := hS.1.1
  haveI : HenselianLocalRing (GapSHPair.wE (K := K) w) := hS.1.2.1
  exact h R K _ _ _ hS A (exists_neron_of_henselian _ _ _)

end ValSub

/-- **`NeronExt.NeronDVRLocal` from the descent leaf** (and the vendored FLT existence over henselian DVRs). -/
theorem neronDVRLocal_of_descentSH (h : NeronDescentSH) : NeronExt.NeronDVRLocal := by
  intro K _ A L _ _ _ v _ Rv _ _ _ _ _
  have hv0 : v ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField L)
  haveI : IsDomain Rv :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := v.primeCompl) _
      (Ideal.primeCompl_le_nonZeroDivisors v)
  haveI : IsDiscreteValuationRing Rv :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hv0 Rv
  haveI : IsFractionRing Rv L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.primeCompl Rv L
  exact exists_neron_of_descentSH Rv L h (A.baseChange L)

/-- **The textbook field `neronSchemeExtensionExists`** from the chain's EGA IV 8.10.5 (xii) leaf and the descent
leaf (neron-ext's `NeronExt.extension_of_dvrLocal` with `neronDVRLocal_of_descentSH`). -/
theorem extension_of_descentSH (hpr : ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii) (h : NeronDescentSH) :
    ZInQ.Contrib.NeronC.NeronSchemeExtensionExists :=
  NeronExt.extension_of_dvrLocal hpr (neronDVRLocal_of_descentSH h)

end NeronFLT

end
