import ShRG

/-! # sh-printed2, Part B: the field `blr_1_2_4` from BLR 1.2 Prop. 4 over strict henselizations

`CToPrinted.BLR_1_2_4` (field `blr_1_2_4` of `HDec.HSyn.OpenResearchLeaves12`) states BLR §1.2 Prop. 4
with the localizations `𝒪_{S,s} = R_𝔭`. If the print uses the strict henselizations `𝒪^{sh}_{S,s}`, the
published form is `BLR_1_2_4_SH` below, with the strict henselization of the discrete valuation ring
`R_𝔭` expressed as sh-route's `ShRoute.IsSHUnram` (in characteristic 0 this characterizes `R_𝔭 → R_𝔭^{sh}`
up to isomorphism, docs/research/sh-route.md §3). This part proves `BLR_1_2_4_0` (the field statement
word for word with `[CharZero K]` added) from `BLR_1_2_4_SH` alone: the localization form is the
strict-henselization form applied twice, once over `R` and once over the Dedekind domain `R_𝔭`, whose
only closed point has the same strict henselization. No other leaf and no commutative algebra beyond
localization of localizations is used. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReductSplit ReductGlue CToPrinted

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SHPrinted2

/-- **LEAF `BLR_1_2_4_SH`** (Bosch–Lütkebohmert–Raynaud, *Néron models*, Ergebnisse 21 (1990), §1.2
Prop. 4, in its strict-henselization reading; number and wording recalled, UNVERIFIED, no network).
*Printed* (as recalled, the reading flagged by reduct-glue §5 and c-to-printed): `R` a Dedekind domain with
field of fractions `K`, `X` a smooth, separated `R`-scheme of finite type; then `X` is a Néron model of
its generic fibre if and only if, for every closed point `s` of `Spec R`, `X ⊗_R 𝒪^{sh}_{S,s}` is a Néron
model of its generic fibre over the strict henselization `𝒪^{sh}_{S,s}`.

*Lean form*: `K` of characteristic 0; `𝒪_{S,s} = R_𝔭` is a valuation subring `O` of `K` with
`IsLocalization.AtPrime O 𝔭` (as in the field statement); `𝒪^{sh}_{S,s}` is any `O₁ ⊆ K₁` with
`ShRoute.IsSHUnram O O₁ hO` (a strictly henselian DVR over `O`, `K₁/K` algebraic, ramification index 1,
separable residue extension), which in characteristic 0 is `O → O^{sh}` up to isomorphism over `O`
(sh-route §3, SPECULATIVE argument with STANDARD inputs; for a field `R` there is no such `O₁` and both
sides hold). `X ⊗_R O₁` is the pullback along `R → O → O₁`. -/
def BLR_1_2_4_SH : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [QuasiCompact X.hom],
    IsNeronModelOver R K X ↔
      ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (O : ValuationSubring K) [Algebra R O]
        [IsLocalization.AtPrime O 𝔭] [IsScalarTower R O K] (K₁ : Type) [Field K₁] [Algebra K K₁]
        (O₁ : ValuationSubring K₁) (hO : O₁.comap (algebraMap K K₁) = O), ShRoute.IsSHUnram O O₁ hO →
        IsNeronModelOver O₁ K₁ ((Over.pullback (Spec.map (CommRingCat.ofHom
          ((comapHom hO).comp (algebraMap R O))))).obj X)

/-- **`BLR_1_2_4` for fields of characteristic 0**: `CToPrinted.BLR_1_2_4` word for word with
`[CharZero K]` added (its one use, `neronLocalizesDVR`, is at a number field). -/
def BLR_1_2_4_0 : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [QuasiCompact X.hom],
    IsNeronModelOver R K X ↔
      ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
        [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
        IsNeronModelOver R𝔭 K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)

/-- `BLR_1_2_4_0` is a specialization of the field's statement. -/
theorem blr_1_2_4_0_of_field (h : BLR_1_2_4) : BLR_1_2_4_0 :=
  fun R K _ _ _ _ _ _ X _ _ _ => h R K X

section Transport

/-- The Néron property of BLR §1.2 Def. 1 is invariant under isomorphism of `R`-schemes. -/
theorem isNeronModelOver_of_iso {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {X X' : Over (Spec (CommRingCat.of R))} (e : X ≅ X') (h : IsNeronModelOver R K X) :
    IsNeronModelOver R K X' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hw : X'.hom = e.inv.left ≫ X.hom := (Over.w e.inv).symm
  refine ⟨?_, ?_, ?_, ?_, fun Y _ => ?_⟩
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have hb := h5 Y
  have : (fun f : Y ⟶ X' => F.map f) =
      (fun g => g ≫ F.map e.hom) ∘ (fun f : Y ⟶ X => F.map f) ∘ (fun f : Y ⟶ X' => f ≫ e.inv) := by
    funext f
    simp only [Function.comp_apply, ← Functor.map_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  show Function.Bijective (fun f : Y ⟶ X' => F.map f)
  rw [this]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp hb ?_)
  · exact ⟨fun a b hab => (cancel_mono (F.map e.hom)).mp hab,
      fun c => ⟨c ≫ F.map e.inv, by simp [← Functor.map_comp]⟩⟩
  · exact ⟨fun a b hab => (cancel_mono e.inv).mp hab, fun c => ⟨c ≫ e.hom, by simp⟩⟩

/-- Pullback along a composite of ring maps is the composite of the pullbacks. -/
theorem pb_comp_iso {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (ψ : R →+* S)
    (φ : S →+* T) (χ : R →+* T) (h : φ.comp ψ = χ) (X : Over (Spec (CommRingCat.of R))) :
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom χ))).obj X ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj X)) := by
  subst h
  have hs : Spec.map (CommRingCat.ofHom (φ.comp ψ)) =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← Spec.map_comp]; rfl
  rw [hs]
  exact ⟨(Over.pullbackComp _ _).app X⟩

instance smooth_pb {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S)
    (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] :
    Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj X).hom := by
  change Smooth (pullback.snd X.hom _); infer_instance

instance isSeparated_pb {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S)
    (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom] :
    IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj X).hom := by
  change IsSeparated (pullback.snd X.hom _); infer_instance

instance quasiCompact_pb {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S)
    (X : Over (Spec (CommRingCat.of R))) [QuasiCompact X.hom] :
    QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj X).hom := by
  change QuasiCompact (pullback.snd X.hom _); infer_instance

end Transport

/-- **The field's statement (characteristic 0) from the strict-henselization form.** -/
theorem blr_1_2_4_0_of_SH (h : BLR_1_2_4_SH) : BLR_1_2_4_0 := by
  intro R K _ _ _ _ _ _ X _ _ _
  constructor
  · -- `X` Néron over `R` ⟹ `X_{R𝔭}` Néron over `R𝔭`: the SH form over the Dedekind domain `R𝔭`
    intro hX 𝔭 _ R𝔭 _ _ _ _ _
    haveI : IsDomain R𝔭 := IsLocalization.isDomain_of_le_nonZeroDivisors R𝔭
      (M := 𝔭.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
    haveI : IsDedekindDomain R𝔭 :=
      IsLocalization.isDedekindDomain R (Ideal.primeCompl_le_nonZeroDivisors 𝔭) R𝔭
    haveI : IsFractionRing R𝔭 K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (R := R) (M := 𝔭.primeCompl)
        (S := R𝔭) (T := K)
    refine (h R𝔭 K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)).mpr ?_
    intro 𝔮 _ O _ _ _ K₁ _ _ O₁ hO hU
    letI : Algebra R O := ((algebraMap R𝔭 O).comp (algebraMap R R𝔭)).toAlgebra
    haveI : IsScalarTower R R𝔭 O := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower R O K := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R R𝔭 K, IsScalarTower.algebraMap_apply R𝔭 O K]; rfl)
    haveI : IsLocalRing R𝔭 := IsLocalization.AtPrime.isLocalRing R𝔭 𝔭
    have h𝔮 : 𝔮.comap (algebraMap R R𝔭) = 𝔭 := by
      have : 𝔮 = IsLocalRing.maximalIdeal R𝔭 := IsLocalRing.eq_maximalIdeal ‹_›
      rw [this]
      exact IsLocalization.AtPrime.under_maximalIdeal R𝔭 𝔭
    haveI : IsLocalization.AtPrime O 𝔭 := by
      have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization 𝔭.primeCompl
        (S := R𝔭) 𝔮 (T := O)
      subst h𝔮
      exact this
    have h1 := (h R K X).mp hX 𝔭 O K₁ O₁ hO hU
    obtain ⟨e⟩ := pb_comp_iso (algebraMap R R𝔭) ((comapHom hO).comp (algebraMap R𝔭 O))
      ((comapHom hO).comp (algebraMap R O)) rfl X
    exact isNeronModelOver_of_iso e h1
  · -- localizations Néron ⟹ strict henselizations Néron (the SH form over `O = R𝔭`) ⟹ `X` Néron
    intro hX
    refine (h R K X).mpr ?_
    intro 𝔭 _ O _ _ _ K₁ _ _ O₁ hO hU
    have h1 := hX 𝔭 O
    haveI : IsLocalization.AtPrime O (IsLocalRing.maximalIdeal O) :=
      IsLocalization.of_le_isUnit (fun y hy => by
        by_contra hu
        exact hy ((IsLocalRing.mem_maximalIdeal y).mpr hu))
    haveI : IsDedekindDomain O :=
      IsLocalization.isDedekindDomain R (Ideal.primeCompl_le_nonZeroDivisors 𝔭) O
    have h2 := (h O K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R O)))).obj X)).mp h1
      (IsLocalRing.maximalIdeal O) O K₁ O₁ hO hU
    obtain ⟨e⟩ := pb_comp_iso (algebraMap R O) ((comapHom hO).comp (algebraMap O O))
      ((comapHom hO).comp (algebraMap R O)) rfl X
    exact isNeronModelOver_of_iso e.symm h2

/-- **The field `neronLocalizesDVR` from `BLR_1_2_4_0`** (the proof of
`CToPrinted.neronLocalizesDVR_of_printed`, verbatim apart from the hypothesis: the use is at a number
field `L`, which has characteristic 0). -/
theorem neronLocalizesDVR_of_printed0 (hB : BLR_1_2_4_0) : ReductGlue.NeronLocalizesDVR := by
  intro K _ A L _ _ _ 𝒩 h𝒩 O _
  haveI := ReductGlue.center_isMaximal O
  letI := algOL O
  haveI := isScalarTower_OL O
  haveI := isLocalization_center O
  have h1 := isNeronModelOver_of 𝒩 h𝒩
  have h2 := ((hB (NumberField.RingOfIntegers L) L 𝒩.G).mp h1) (ReductGlue.center O) O
  obtain ⟨_, _, _, _, h3⟩ := h2
  have h4 : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ (ReductGlue.toO 𝒩 O).G => (Over.pullback (ReductSplit.jO O)).map f :=
    h3
  intro Y _
  have hb := h4 Y
  refine ⟨fun a b hab => hb.1 ?_, fun g => ?_⟩
  · simp only at hab ⊢
    exact (cancel_mono (ReductGlue.toO 𝒩 O).gen.hom).mp hab
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ (ReductGlue.toO 𝒩 O).gen.inv)
    refine ⟨f, ?_⟩
    simp only at hf ⊢
    rw [hf]
    simp

/-- **The field `neronLocalizesDVR` from the strict-henselization form of BLR 1.2/4.** -/
theorem neronLocalizesDVR_of_SH (h : BLR_1_2_4_SH) : ReductGlue.NeronLocalizesDVR :=
  neronLocalizesDVR_of_printed0 (blr_1_2_4_0_of_SH h)

end SHPrinted2

#print axioms SHPrinted2.blr_1_2_4_0_of_SH
#print axioms SHPrinted2.neronLocalizesDVR_of_SH
