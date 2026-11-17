import ZInQKernel.Contrib.OneProof.NeronExtSpread
import ZInQKernel.Contrib.SpreadOut.NumberField

/-! # neron-ext: a Néron model near a closed point from a Néron model over its local ring -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open NumberField

namespace NeronExt

open GapBLR ZInQ.Contrib.SpreadOut

section Gen

theorem isPullback_id_mono {C : Type*} [Category C] {W D Z : C} (g : W ⟶ D) (m : D ⟶ Z) [Mono m] :
    IsPullback (𝟙 W) g (g ≫ m) m := by
  refine IsPullback.of_isLimit' ⟨by simp⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst) (fun s => ?_)
    (fun s => ?_) (fun s l h1 h2 => ?_))
  · simp
  · rw [← cancel_mono m]; simpa using s.condition
  · simpa using h1

/-- For a monomorphism `m`, pulling `W → D → Z` back along `m` gives `W`. -/
noncomputable def pbMapIso {Z D : Scheme.{0}} (m : D ⟶ Z) [Mono m] (W : Over D) :
    (Over.pullback m).obj (Over.mk (W.hom ≫ m)) ≅ W :=
  Over.isoMk ((isPullback_id_mono W.hom m).isoPullback.symm) (by
    show (isPullback_id_mono W.hom m).isoPullback.inv ≫ W.hom = pullback.snd (W.hom ≫ m) m
    exact (isPullback_id_mono W.hom m).isoPullback_inv_snd)

theorem isNeronModelOver_of_iso {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {X X' : Over (Spec (CommRingCat.of R))} (i : X ≅ X')
    (h : CToPrinted.IsNeronModelOver R K X') : CToPrinted.IsNeronModelOver R K X := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hX : X.hom = i.hom.left ≫ X'.hom := (Over.w i.hom).symm
  haveI : IsIso i.hom.left := ⟨i.inv.left, by rw [← Over.comp_left, i.hom_inv_id]; rfl,
    by rw [← Over.comp_left, i.inv_hom_id]; rfl⟩
  refine ⟨by rw [hX]; infer_instance, by rw [hX]; infer_instance, by rw [hX]; infer_instance,
    by rw [hX]; infer_instance, fun Y _ => ?_⟩
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have hb := h5 Y
  have e : (fun f : Y ⟶ X => F.map f) =
      (fun g => g ≫ (F.mapIso i).inv) ∘ (fun g : Y ⟶ X' => F.map g) ∘ (fun f => f ≫ i.hom) := by
    funext f
    simp only [Function.comp_apply, Functor.mapIso_inv, CategoryTheory.Functor.map_comp,
      Category.assoc, ← CategoryTheory.Functor.map_comp F i.hom i.inv, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [e]
  have b1 : Function.Bijective (fun f : Y ⟶ X => f ≫ i.hom) :=
    ⟨fun a b hab => by simpa using congrArg (· ≫ i.inv) hab, fun g => ⟨g ≫ i.inv, by simp⟩⟩
  have b2 : Function.Bijective (fun g : F.obj Y ⟶ F.obj X' => g ≫ (F.mapIso i).inv) :=
    ⟨fun a b hab => by simpa using congrArg (· ≫ (F.mapIso i).hom) hab,
      fun g => ⟨g ≫ (F.mapIso i).hom, by simp⟩⟩
  exact b2.comp (hb.comp b1)

variable {L : Type} [Field L] [NumberField L]

theorem locNeron_of_iso {𝔭 : Ideal (𝓞 L)} [𝔭.IsPrime] {X X' : Over (S L)} (i : X ≅ X')
    (h : LocNeron L 𝔭 X') : LocNeron L 𝔭 X := by
  unfold LocNeron at *
  letI := locAlg L 𝔭
  exact isNeronModelOver_of_iso ((Over.pullback _).mapIso i) h

/-- `Spec (𝓞_L)_w → Spec 𝓞_L` lands in every open containing `w`. -/
theorem preimage_loc_eq_top (w : Ideal (𝓞 L)) [w.IsPrime] {U : (S L).Opens} (hw : w ∈ maxIn U) :
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime w)))) ⁻¹ᵁ U = ⊤ := by
  obtain ⟨x, hxU, hx⟩ := hw
  refine top_unique (fun q _ => ?_)
  let y : PrimeSpectrum (𝓞 L) := PrimeSpectrum.comap (algebraMap (𝓞 L) (Localization.AtPrime w)) q
  have hy : (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime w)))) q = y := by
    rw [Spec.map_base]; rfl
  have hle : y ≤ x := by
    show Ideal.comap _ q.asIdeal ≤ x.asIdeal
    rw [hx]
    calc Ideal.comap _ q.asIdeal ≤ Ideal.comap (algebraMap (𝓞 L) (Localization.AtPrime w))
          (IsLocalRing.maximalIdeal _) :=
          Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)
      _ = w := Localization.AtPrime.under_maximalIdeal
  show (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime w)))) q ∈ U
  rw [hy]
  exact ((PrimeSpectrum.le_iff_specializes y x).mp hle).mem_open U.isOpen hxU

theorem isIso_pb_resι {T : Scheme.{0}} (j : T ⟶ S L) (X : Over (S L)) {U : (S L).Opens}
    (hU : j ⁻¹ᵁ U = ⊤) : IsIso ((Over.pullback j).map (resι X U)) :=
  isIso_pb_map j (resι X U) U hU (fun x hx => by
    show x ∈ Set.range (X.hom ⁻¹ᵁ U).ι
    rw [Scheme.Opens.range_ι]; exact hx)

theorem locNeron_res_iff {w : Ideal (𝓞 L)} [w.IsPrime] {U : (S L).Opens} (hw : w ∈ maxIn U)
    (X : Over (S L)) : LocNeron L w (res X U) ↔ LocNeron L w X := by
  haveI := isIso_pb_resι (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime w))))
    X (preimage_loc_eq_top w hw)
  let i := asIso ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (Localization.AtPrime w))))).map (resι X U))
  unfold LocNeron
  letI := locAlg L w
  exact ⟨fun h => isNeronModelOver_of_iso i.symm h, fun h => isNeronModelOver_of_iso i h⟩

end Gen

section Near

variable {L : Type} [Field L] [NumberField L]

theorem mem_ej_opensRange {𝔭 : Ideal (𝓞 L)} [𝔭.IsPrime] (a : (GapBLR.Idx 𝔭)ᵒᵖ) {x : S L} :
    x ∈ (ej a).opensRange ↔ a.unop.s ∉ (PrimeSpectrum.asIdeal (R := 𝓞 L) x) := by
  have hrange := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (𝓞 L)) a.unop.s
  exact (Eq.to_iff (congrArg (x ∈ ·) hrange)).trans (PrimeSpectrum.mem_basicOpen _ _)

/-- The point of `Spec 𝓞_L` of a prime ideal. -/
def pt (v : Ideal (𝓞 L)) [hv : v.IsPrime] : S L := (⟨v, hv⟩ : PrimeSpectrum (𝓞 L))

/-- The Néron property of `N` over `(𝓞_L)_v` (algebra `locAlg`), with `N_L ≅ B`. -/
def LocalModel (B : Over (Spec (CommRingCat.of L))) (v : Ideal (𝓞 L)) [v.IsPrime]
    (N : Over (Spec (CommRingCat.of (Localization.AtPrime v)))) : Prop :=
  letI := locAlg L v
  CToPrinted.IsNeronModelOver (Localization.AtPrime v) L N ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.AtPrime v) L)))).obj N ≅ B)

/-- **Spreading the local Néron model at `v`.** -/
theorem spreadAt (B : Over (Spec (CommRingCat.of L))) (v : Ideal (𝓞 L)) [v.IsPrime]
    (N : Over (Spec (CommRingCat.of (Localization.AtPrime v)))) (hN : LocalModel B v N) :
    ∃ (Dv : (S L).Opens) (X : Over (S L)) (_ : Smooth X.hom) (_ : IsSeparated X.hom)
      (_ : QuasiCompact X.hom) (_ : (gf L).obj X ≅ B), pt v ∈ Dv ∧ Supp L Dv X ∧ LocNeron L v X := by
  letI := locAlg L v
  haveI := locAlg_tower L v
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨eN⟩⟩ := hN
  haveI := h1; haveI := h2; haveI := h4
  obtain ⟨a, W, hWs, hWsep, hWqc, ⟨eW⟩⟩ := exists_spread_sep (𝔭 := v) (Localization.AtPrime v) N
  haveI := hWs; haveI := hWsep; haveI := hWqc
  let X : Over (S L) := Over.mk (W.hom ≫ ej a)
  haveI : Smooth X.hom := show Smooth (W.hom ≫ ej a) from inferInstance
  haveI : IsSeparated X.hom := show IsSeparated (W.hom ≫ ej a) from inferInstance
  haveI : QuasiCompact X.hom := show QuasiCompact (W.hom ≫ ej a) from inferInstance
  let jv := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime v)))
  have hjv : (specCone v (Localization.AtPrime v)).π.app a ≫ ej a = jv := π_ej _ a
  let pbX : (Over.pullback jv).obj X ≅ N :=
    pbCongr hjv.symm X ≪≫ (Over.pullbackComp _ (ej a)).app X ≪≫
      (Over.pullback _).mapIso (pbMapIso (ej a) W) ≪≫ eW
  let kL := Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime v) L))
  have hk : kL ≫ jv = jL L := by
    simp only [kL, jv, jL, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  let eX : (gf L).obj X ≅ B :=
    pbCongr hk.symm X ≪≫ (Over.pullbackComp kL jv).app X ≪≫ (Over.pullback kL).mapIso pbX ≪≫ eN
  refine ⟨(ej a).opensRange, X, inferInstance, inferInstance, inferInstance, eX, ?_, ?_, ?_⟩
  · exact (mem_ej_opensRange a).2 a.unop.hs
  · show (W.hom ≫ ej a) ⁻¹ᵁ (ej a).opensRange = ⊤
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]
  · show CToPrinted.IsNeronModelOver (Localization.AtPrime v) L ((Over.pullback jv).obj X)
    exact isNeronModelOver_of_iso pbX ⟨h1, h2, h3, h4, h5⟩

/-- **Prime avoidance.** For `k ≠ 0` and a maximal `v`, some `g ∉ v` lies in every other maximal ideal
containing `k`. -/
theorem exists_avoid (v : Ideal (𝓞 L)) [hv : v.IsMaximal] (k : 𝓞 L) (hk : k ≠ 0) :
    ∃ g : 𝓞 L, g ∉ v ∧ ∀ w : Ideal (𝓞 L), w.IsMaximal → w ≠ v → k ∈ w → g ∈ w := by
  classical
  have hI : Ideal.span {k} ≠ (0 : Ideal (𝓞 L)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hk
  let T := (Ideal.finite_factors hI).toFinset.filter (fun w => w.asIdeal ≠ v)
  have hx : ∀ w ∈ T, ∃ x ∈ w.asIdeal, x ∉ v := by
    intro w hw
    have hwv : w.asIdeal ≠ v := (Finset.mem_filter.1 hw).2
    by_contra hcon
    push Not at hcon
    have hle : w.asIdeal ≤ v := hcon
    haveI : w.asIdeal.IsMaximal := w.isMaximal
    exact hwv (Ideal.IsMaximal.eq_of_le this hv.ne_top hle)
  choose x hxw hxv using hx
  refine ⟨∏ w ∈ T.attach, x w.1 w.2, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨w, -, hw⟩
    exact hxv w.1 w.2 hw
  · intro w hwmax hwv hkw
    have hw0 : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hwmax (RingOfIntegers.not_isField L)
    let w' : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := ⟨w, hwmax.isPrime, hw0⟩
    have hw'T : w' ∈ T := by
      refine Finset.mem_filter.2 ⟨?_, hwv⟩
      rw [Set.Finite.mem_toFinset]
      show w ∣ Ideal.span {k}
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hkw
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun u : T => x u.1 u.2) (Finset.mem_attach T ⟨w', hw'T⟩)
    rw [hc]
    exact Ideal.mul_mem_right c _ (hxw w' hw'T)

/-- Inclusion `res X U → res X U'` for `U ≤ U'`. -/
noncomputable def incl (X : Over (S L)) {U U' : (S L).Opens} (h : U ≤ U') : res X U ⟶ res X U' :=
  liftRes (supp_mono h (supp_res X U)) (resι X U)

@[simp] theorem incl_ι (X : Over (S L)) {U U' : (S L).Opens} (h : U ≤ U') :
    incl X h ≫ resι X U' = resι X U := liftRes_ι _ _

theorem mono_left_resι (X : Over (S L)) (U : (S L).Opens) {Y : Over (S L)} {f g : Y ⟶ res X U}
    (h : f ≫ resι X U = g ≫ resι X U) : f = g := by
  apply Over.OverMorphism.ext
  have h' := congrArg (fun t => t.left) h
  simp only [Over.comp_left] at h'
  exact (cancel_mono (resι X U).left).mp h'

/-- **Comparison near the generic point.** Two smooth separated quasi-compact models with the same
generic fibre agree over some `D(s₁) ∩ D(s₂)`: the Néron property at a maximal ideal there passes from
one to the other. -/
theorem isoNear (B : Over (Spec (CommRingCat.of L))) (X 𝒜 : Over (S L)) [Smooth X.hom]
    [IsSeparated X.hom] [QuasiCompact X.hom] [Smooth 𝒜.hom] [IsSeparated 𝒜.hom]
    [QuasiCompact 𝒜.hom] (eX : (gf L).obj X ≅ B) (eA : (gf L).obj 𝒜 ≅ B) :
    ∃ s₁ s₂ : GIdx L, ∀ (w : Ideal (𝓞 L)) [w.IsPrime], w ∈ maxIn (Dg s₁ ⊓ Dg s₂) →
      LocNeron L w 𝒜 → LocNeron L w X := by
  obtain ⟨s₁, α, hα⟩ := spread_generic X 𝒜 (eX.hom ≫ eA.inv)
  obtain ⟨s₂, β, hβ⟩ := spread_generic 𝒜 X (eA.hom ≫ eX.inv)
  refine ⟨s₁, s₂, fun w _ hw h𝒜 => ?_⟩
  let D := Dg s₁ ⊓ Dg s₂
  have hD : (jL L) ⁻¹ᵁ D = ⊤ := by
    obtain ⟨x, hxD, -⟩ := hw
    exact jL_preimage_eq_top L ⟨x, hxD⟩
  haveI := isIso_gf_resι X hD
  haveI := isIso_gf_resι 𝒜 hD
  let α' : res X D ⟶ res 𝒜 D := liftRes (supp_res X D) (incl X inf_le_left ≫ α)
  let β' : res 𝒜 D ⟶ res X D := liftRes (supp_res 𝒜 D) (incl 𝒜 inf_le_right ≫ β)
  have gα : (gf L).map α' ≫ (gf L).map (resι 𝒜 D) = (gf L).map (resι X D) ≫ eX.hom ≫ eA.inv := by
    rw [← CategoryTheory.Functor.map_comp, liftRes_ι, CategoryTheory.Functor.map_comp, hα,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp, incl_ι]
  have gβ : (gf L).map β' ≫ (gf L).map (resι X D) = (gf L).map (resι 𝒜 D) ≫ eA.hom ≫ eX.inv := by
    rw [← CategoryTheory.Functor.map_comp, liftRes_ι, CategoryTheory.Functor.map_comp, hβ,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp, incl_ι]
  have h1 : α' ≫ β' = 𝟙 _ := by
    apply mono_left_resι X D
    apply ZInQ.Contrib.NeronC.neron_extension_injective L X eX (res X D)
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Category.id_comp]
    show (gf L).map α' ≫ (gf L).map β' ≫ (gf L).map (resι X D) ≫ eX.hom =
      (gf L).map (resι X D) ≫ eX.hom
    rw [← Category.assoc ((gf L).map β'), gβ, Category.assoc, Category.assoc,
      ← Category.assoc ((gf L).map α'), gα]
    simp
  have h2 : β' ≫ α' = 𝟙 _ := by
    apply mono_left_resι 𝒜 D
    apply ZInQ.Contrib.NeronC.neron_extension_injective L 𝒜 eA (res 𝒜 D)
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Category.id_comp]
    show (gf L).map β' ≫ (gf L).map α' ≫ (gf L).map (resι 𝒜 D) ≫ eA.hom =
      (gf L).map (resι 𝒜 D) ≫ eA.hom
    rw [← Category.assoc ((gf L).map α'), gα, Category.assoc, Category.assoc,
      ← Category.assoc ((gf L).map β'), gβ]
    simp
  let i : res X D ≅ res 𝒜 D := ⟨α', β', h1, h2⟩
  rw [← locNeron_res_iff hw X]
  rw [← locNeron_res_iff hw 𝒜] at h𝒜
  exact locNeron_of_iso i h𝒜

/-- The basic open `D(g)`. -/
def Db (g : 𝓞 L) : (S L).Opens := PrimeSpectrum.basicOpen (R := 𝓞 L) g

theorem mem_Db {g : 𝓞 L} {x : S L} : x ∈ Db g ↔ g ∉ (PrimeSpectrum.asIdeal (R := 𝓞 L) x) :=
  PrimeSpectrum.mem_basicOpen _ _

theorem ne_zero_of_idx (s : GIdx L) : s.unop.s ≠ 0 := fun h => s.unop.hs (h ▸ Ideal.zero_mem _)

/-- **Glue N1-g2 (proved).** Given a local Néron model at a maximal ideal `v` and a smooth separated
quasi-compact model `𝒜` which is a Néron model at every maximal ideal not containing `f ≠ 0`, `B` has a
Néron model over an open neighbourhood of `v`. -/
theorem near (B : Over (Spec (CommRingCat.of L))) (v : Ideal (𝓞 L)) [hv : v.IsMaximal]
    (N : Over (Spec (CommRingCat.of (Localization.AtPrime v)))) (hN : LocalModel B v N)
    (𝒜 : Over (S L)) [Smooth 𝒜.hom] [IsSeparated 𝒜.hom] [QuasiCompact 𝒜.hom]
    (eA : (gf L).obj 𝒜 ≅ B) (f : 𝓞 L) (hf : f ≠ 0)
    (h𝒜 : ∀ (w : Ideal (𝓞 L)) [w.IsMaximal], f ∉ w → LocNeron L w 𝒜) :
    ∃ U : (S L).Opens, pt v ∈ U ∧ Nonempty (NeronOn L B U) := by
  obtain ⟨Dv, X, hXs, hXsep, hXqc, eX, hvD, hXD, hXv⟩ := spreadAt B v N hN
  haveI := hXs; haveI := hXsep; haveI := hXqc
  obtain ⟨s₁, s₂, hcmp⟩ := isoNear B X 𝒜 eX eA
  let k := s₁.unop.s * s₂.unop.s * f
  have hk : k ≠ 0 := mul_ne_zero (mul_ne_zero (ne_zero_of_idx s₁) (ne_zero_of_idx s₂)) hf
  obtain ⟨g, hgv, hg⟩ := exists_avoid v k hk
  let U := Dv ⊓ Db g
  have hvU : pt v ∈ U := ⟨hvD, mem_Db.2 hgv⟩
  have hU : (jL L) ⁻¹ᵁ U = ⊤ := jL_preimage_eq_top L ⟨_, hvU⟩
  haveI := isIso_gf_resι X hU
  refine ⟨U, hvU, ⟨neronOn_of_local B U (res X U) (supp_res X U)
    (asIso ((gf L).map (resι X U)) ≪≫ eX) (fun w _ hw => ?_) (hT_of_mem (pt v) hv hvU)⟩⟩
  rw [locNeron_res_iff hw X]
  by_cases hwv : w = v
  · subst hwv; exact hXv
  · obtain ⟨x, hxU, hxw⟩ := hw
    have hgw : g ∉ w := by
      have := mem_Db.1 hxU.2
      rwa [hxw] at this
    have hkw : k ∉ w := fun h => hgw (hg w ‹_› hwv h)
    have h1 : s₁.unop.s ∉ w := fun h => hkw (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h))
    have h2 : s₂.unop.s ∉ w := fun h => hkw (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h))
    have h3 : f ∉ w := fun h => hkw (Ideal.mul_mem_left _ _ h)
    refine hcmp w ⟨x, ⟨mem_Dg.2 ?_, mem_Dg.2 ?_⟩, hxw⟩ (h𝒜 w h3)
    · rwa [hxw]
    · rwa [hxw]

end Near

/-! ## The good part: an abelian scheme over `𝓞_L[1/f]` -/

section Good

variable {L : Type} [Field L] [NumberField L]

theorem isUnit_f_L {f : 𝓞 L} (hf : f ≠ 0) : IsUnit (algebraMap (𝓞 L) L f) :=
  isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)).2 hf)

/-- **Glue N1-g1 + N1-ab.** An abelian variety over `L` has a smooth separated quasi-compact model
over `𝓞_L` (supported on some `D(f)`) which is a Néron model at every maximal ideal not containing
`f`: spread out to a smooth proper group scheme over `𝓞_L[1/f]` (`abVarSpreadsOut_of_ega`: EGA IV
8.8.2 (ii) and 17.7.8 (ii) proved, 8.10.5 (xii) the chain's leaf), and use BLR 1.2/8 over the DVRs
`(𝓞_L)_w` (`isNeronModelOver_of_grpObj`). -/
theorem goodModel (hpr : EGAIV_8_10_5_xii) (B : PkgI3.AbVar L) :
    ∃ (𝒜 : Over (S L)) (_ : Smooth 𝒜.hom) (_ : IsSeparated 𝒜.hom) (_ : QuasiCompact 𝒜.hom)
      (_ : (gf L).obj 𝒜 ≅ B.X) (f : 𝓞 L), f ≠ 0 ∧
        ∀ (w : Ideal (𝓞 L)) [w.IsMaximal], f ∉ w → LocNeron L w 𝒜 := by
  obtain ⟨f, hf, hR⟩ := NF.abVarSpreadsOut_of_ega EGAIV_8_8_2_ii_proof hpr EGAIV_17_7_8_ii_proof L B
  let R := Localization.Away f
  letI : Algebra R L := (IsLocalization.Away.lift f (isUnit_f_L hf)).toAlgebra
  haveI : IsScalarTower (𝓞 L) R L :=
    IsScalarTower.of_algebraMap_eq (fun z => (IsLocalization.Away.lift_eq f (isUnit_f_L hf) z).symm)
  obtain ⟨G, hG, hGs, hGp, gen, -⟩ := hR R
  haveI := hGs; haveI := hGp
  let ιf := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) R))
  haveI : IsOpenImmersion ιf := IsOpenImmersion.of_isLocalization f
  let 𝒜 : Over (S L) := Over.mk (G.hom ≫ ιf)
  haveI : Smooth 𝒜.hom := show Smooth (G.hom ≫ ιf) from inferInstance
  haveI : IsSeparated 𝒜.hom := show IsSeparated (G.hom ≫ ιf) from inferInstance
  haveI : QuasiCompact 𝒜.hom := show QuasiCompact (G.hom ≫ ιf) from inferInstance
  let jRL := Spec.map (CommRingCat.ofHom (algebraMap R L))
  have hk : jRL ≫ ιf = jL L := by
    simp only [jRL, ιf, jL, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  let eA : (gf L).obj 𝒜 ≅ B.X :=
    pbCongr hk.symm 𝒜 ≪≫ (Over.pullbackComp jRL ιf).app 𝒜 ≪≫ (Over.pullback jRL).mapIso (pbMapIso ιf G) ≪≫ gen
  refine ⟨𝒜, inferInstance, inferInstance, inferInstance, eA, f, hf, fun w hw hfw => ?_⟩
  have hw0 : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (RingOfIntegers.not_isField L)
  letI := locAlg L w
  haveI := locAlg_tower L w
  haveI : IsDiscreteValuationRing (Localization.AtPrime w) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hw0 _
  haveI : IsFractionRing (Localization.AtPrime w) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization w.primeCompl _ L
  have hfu : IsUnit (algebraMap (𝓞 L) (Localization.AtPrime w) f) :=
    IsLocalization.map_units (Localization.AtPrime w) (⟨f, hfw⟩ : w.primeCompl)
  let φ : R →+* Localization.AtPrime w := IsLocalization.Away.lift f hfu
  let jw' := Spec.map (CommRingCat.ofHom φ)
  let jw := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime w)))
  have hjw : jw' ≫ ιf = jw := by
    simp only [jw', ιf, jw, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact IsLocalization.Away.lift_comp f hfu
  let iso : (Over.pullback jw).obj 𝒜 ≅ (Over.pullback jw').obj G :=
    pbCongr hjw.symm 𝒜 ≪≫ (Over.pullbackComp jw' ιf).app 𝒜 ≪≫ (Over.pullback jw').mapIso (pbMapIso ιf G)
  letI : GrpObj ((Over.pullback jw').obj G) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback jw').obj G).hom := show IsProper (pullback.snd _ _) from inferInstance
  haveI : Smooth ((Over.pullback jw').obj G).hom := show Smooth (pullback.snd _ _) from inferInstance
  exact isNeronModelOver_of_iso iso (isNeronModelOver_of_grpObj (Localization.AtPrime w) L _)

end Good

/-! ## The main theorem -/

/-- **`NeronDVRLocal` (LEAF; published).** For an abelian variety `A/K` and a number field `L ⊇ K`,
at every maximal ideal `v` of `𝓞_L` the abelian variety `A_L` has a Néron model over the discrete
valuation ring `(𝓞_L)_v` (any presentation `R_v` with its map to `L`) in the sense of BLR §1.2 Def. 1:
a smooth, separated, quasi-compact `R_v`-scheme `N` with the Néron mapping property for all smooth
`R_v`-schemes (`CToPrinted.IsNeronModelOver`) and `N_L ≅ A_L`. Source: Bosch–Lütkebohmert–Raynaud,
*Néron models* (1990), §1.4 Thm. 3 over the Dedekind scheme `Spec R_v` (a discrete valuation ring),
with §1.2 Def. 1 (locators UNVERIFIED, no network). It follows from `NeronSchemeExtensionExists`
(`dvrLocal_of_extension`), so it is not stronger. -/
def NeronDVRLocal : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (v : Ideal (𝓞 L)) [v.IsMaximal] (Rv : Type) [CommRing Rv] [Algebra (𝓞 L) Rv]
    [IsLocalization.AtPrime Rv v] [Algebra Rv L] [IsScalarTower (𝓞 L) Rv L],
    ∃ N : Over (Spec (CommRingCat.of Rv)), CToPrinted.IsNeronModelOver Rv L N ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Rv L)))).obj N ≅
        (A.baseChange L).X)

/-- **`neronSchemeExtensionExists` from the local leaf** (and the chain's EGA IV 8.10.5 (xii) leaf). -/
theorem extension_of_dvrLocal (hpr : EGAIV_8_10_5_xii) (hloc : NeronDVRLocal) :
    ZInQ.Contrib.NeronC.NeronSchemeExtensionExists := by
  intro K _ A L _ _ _
  let B := (A.baseChange L).X
  obtain ⟨𝒜, h1, h2, h3, eA, f, hf, h𝒜⟩ := goodModel hpr (A.baseChange L)
  haveI := h1; haveI := h2; haveI := h3
  have hcov : ∀ x : S L, ∃ U : (S L).Opens, x ∈ U ∧ Nonempty (NeronOn L B U) := by
    intro x
    obtain ⟨v, hv, hxv⟩ := Ideal.exists_le_maximal (PrimeSpectrum.asIdeal (R := 𝓞 L) x)
      (PrimeSpectrum.isPrime (R := 𝓞 L) x).ne_top
    letI := locAlg L v
    haveI := locAlg_tower L v
    obtain ⟨N, hN1, hN2⟩ := hloc K A L v (Localization.AtPrime v)
    obtain ⟨U, hvU, hn⟩ := near B v N ⟨hN1, hN2⟩ 𝒜 eA f hf h𝒜
    refine ⟨U, ?_, hn⟩
    have hle : (show PrimeSpectrum (𝓞 L) from x) ≤ (show PrimeSpectrum (𝓞 L) from pt v) := hxv
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hle).mem_open U.isOpen hvU
  let n := glued B hcov
  exact ⟨n.X, n.smooth, n.sep, n.qc, n.e, fun Y _ => n.ext Y (Scheme.Hom.preimage_top _)⟩

/-- **The local leaf is not stronger than the field**: `NeronSchemeExtensionExists` gives `NeronDVRLocal`
(localize the Néron model over `𝓞_L`: gt-blr's `GapBLR.isNeronModelOver_localization`). -/
theorem dvrLocal_of_extension (h : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) : NeronDVRLocal := by
  intro K _ A L _ _ _ v _ Rv _ _ _ _ _
  obtain ⟨N, hS, hSep, hQC, e, hN⟩ := ZInQ.Contrib.NeronC.neronSchemeModelExists_of_extension h K A L
  haveI := hS; haveI := hSep; haveI := hQC
  have hX : CToPrinted.IsNeronModelOver (𝓞 L) L N := by
    refine ⟨hS, hSep, inferInstance, hQC, fun Y _ => ?_⟩
    have hb := hN Y
    have heq : (fun f : Y ⟶ N => (Over.pullback (jL L)).map f) =
        (fun g => g ≫ e.inv) ∘ (fun f : Y ⟶ N => (Over.pullback (jL L)).map f ≫ e.hom) := by
      funext f; simp
    rw [heq]
    have b2 : Function.Bijective (fun g : (Over.pullback (jL L)).obj Y ⟶ _ => g ≫ e.inv) :=
      ⟨fun a b hab => by simpa using congrArg (· ≫ e.hom) hab, fun g => ⟨g ≫ e.hom, by simp⟩⟩
    exact b2.comp hb
  have hloc := GapBLR.isNeronModelOver_localization (𝔭 := v) Rv hX
  refine ⟨_, hloc, ⟨?_⟩⟩
  have hk : Spec.map (CommRingCat.ofHom (algebraMap Rv L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) Rv)) = jL L := by
    simp only [jL, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  exact ((Over.pullbackComp _ _).app N).symm ≪≫ pbCongr hk N ≪≫ e

end NeronExt

#print axioms NeronExt.extension_of_dvrLocal
#print axioms NeronExt.dvrLocal_of_extension
