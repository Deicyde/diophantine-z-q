import ZInQKernel.Contrib.OneProof.NeronDedekind.Glue
import ZInQKernel.Contrib.OneProof.NeronDedekind.Spread
import ZInQKernel.Contrib.OneProof.NeronSchemeExtensionExists

/-! Néron models on neighborhoods of closed points of an affine Dedekind scheme.

This generalizes the local spreading and comparison in
`ZInQKernel.Contrib.OneProof.NeronSchemeExtensionExists` from rings of integers
to arbitrary Dedekind domains.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace NeronExtDedekind

open GapBLR
open NeronExt (LocNeron locAlg locAlg_tower ext_of_localT pbCongr exists_spread_sep)

variable {D L : Type} [CommRing D] [IsDedekindDomain D] [Field L]
  [Algebra D L] [IsFractionRing D L]

/-- The prime ideals represented by points of an open. -/
def maxIn (U : (S D).Opens) : Set (Ideal D) := {𝔭 | ∃ x : S D, x ∈ U ∧ x.asIdeal = 𝔭}

/-- **The Néron property over `U` is local** (BLR 1.2/4 over the open `U`, from GapBLR's `local_pt`). -/
noncomputable def neronOn_of_local (B : Over (Spec (CommRingCat.of L))) (U : (S D).Opens)
    (X : Over (S D)) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom] (hX : Supp D U X)
    (e : (gf D L).obj X ≅ B)
    (hloc : ∀ (𝔭 : Ideal D) [𝔭.IsMaximal], 𝔭 ∈ maxIn U → LocNeron L 𝔭 X)
    (hT : ∀ x : S D, x ∈ U → ∃ 𝔭 : Ideal D, 𝔭.IsMaximal ∧ 𝔭 ∈ maxIn U ∧ x.asIdeal ≤ 𝔭) :
    NeronOn D L B U where
  X := X
  supp := hX
  smooth := inferInstance
  sep := inferInstance
  qc := inferInstance
  e := e
  ext := fun Y _ hY φ => by
    obtain ⟨f, hf⟩ := ext_of_localT (K := L) (maxIn U) hloc Y
      (fun y => hT _ (mem_of_supp D hY y)) (φ ≫ e.inv)
    refine ⟨f, ?_⟩
    have hf' : (gf D L).map f = φ ≫ e.inv := hf
    show (gf D L).map f ≫ e.hom = φ
    rw [hf', Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every point of an open containing a maximal ideal lies under a maximal ideal of that open. -/
theorem hT_of_mem {U : (S D).Opens} (v : S D) (hv : v.asIdeal.IsMaximal) (hvU : v ∈ U) :
    ∀ x : S D, x ∈ U → ∃ 𝔭 : Ideal D, 𝔭.IsMaximal ∧ 𝔭 ∈ maxIn U ∧ x.asIdeal ≤ 𝔭 := by
  intro x hx
  by_cases h0 : x.asIdeal = ⊥
  · exact ⟨v.asIdeal, hv, ⟨v, hvU, rfl⟩, h0 ▸ bot_le⟩
  · exact ⟨x.asIdeal, Ideal.IsPrime.isMaximal x.isPrime h0, ⟨x, hx, rfl⟩, le_rfl⟩

theorem locNeron_of_iso {𝔭 : Ideal D} [𝔭.IsPrime] {X X' : Over (S D)} (i : X ≅ X')
    (h : LocNeron L 𝔭 X') : LocNeron L 𝔭 X := by
  unfold LocNeron at *
  letI := locAlg L 𝔭
  exact NeronExt.isNeronModelOver_of_iso ((Over.pullback _).mapIso i) h

/-- Localization at a prime `w` lands in every open containing `w`. -/
theorem preimage_loc_eq_top (w : Ideal D) [w.IsPrime] {U : (S D).Opens} (hw : w ∈ maxIn U) :
    (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime w)))) ⁻¹ᵁ U = ⊤ := by
  obtain ⟨x, hxU, hx⟩ := hw
  refine top_unique (fun q _ => ?_)
  let y : PrimeSpectrum D := PrimeSpectrum.comap (algebraMap D (Localization.AtPrime w)) q
  have hy : (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime w)))) q = y := by
    rw [Spec.map_base]; rfl
  have hle : y ≤ x := by
    show Ideal.comap _ q.asIdeal ≤ x.asIdeal
    rw [hx]
    calc Ideal.comap _ q.asIdeal ≤ Ideal.comap (algebraMap D (Localization.AtPrime w))
          (IsLocalRing.maximalIdeal _) :=
          Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)
      _ = w := Localization.AtPrime.under_maximalIdeal
  show (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime w)))) q ∈ U
  rw [hy]
  exact ((PrimeSpectrum.le_iff_specializes y x).mp hle).mem_open U.isOpen hxU

theorem isIso_pb_resι {T : Scheme.{0}} (j : T ⟶ S D) (X : Over (S D)) {U : (S D).Opens}
    (hU : j ⁻¹ᵁ U = ⊤) : IsIso ((Over.pullback j).map (resι X U)) :=
  NeronExt.isIso_pb_map j (resι X U) U hU (fun x hx => by
    show x ∈ Set.range (X.hom ⁻¹ᵁ U).ι
    rw [Scheme.Opens.range_ι]; exact hx)

theorem locNeron_res_iff {w : Ideal D} [w.IsPrime] {U : (S D).Opens} (hw : w ∈ maxIn U)
    (X : Over (S D)) : LocNeron L w (res X U) ↔ LocNeron L w X := by
  haveI := isIso_pb_resι (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime w))))
    X (preimage_loc_eq_top w hw)
  let i := asIso ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap D (Localization.AtPrime w))))).map (resι X U))
  unfold LocNeron
  letI := locAlg L w
  exact ⟨fun h => NeronExt.isNeronModelOver_of_iso i.symm h, fun h => NeronExt.isNeronModelOver_of_iso i h⟩

theorem mem_ej_opensRange {𝔭 : Ideal D} [𝔭.IsPrime] (a : (GapBLR.Idx 𝔭)ᵒᵖ) {x : S D} :
    x ∈ (ej a).opensRange ↔ a.unop.s ∉ (PrimeSpectrum.asIdeal (R := D) x) := by
  have hrange := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of D) a.unop.s
  exact (Eq.to_iff (congrArg (x ∈ ·) hrange)).trans (PrimeSpectrum.mem_basicOpen _ _)

/-- The point of `Spec D` corresponding to a prime ideal. -/
def pt (v : Ideal D) [hv : v.IsPrime] : S D := (⟨v, hv⟩ : PrimeSpectrum D)

/-- The Néron property of `N` over `D_v`, with generic fibre isomorphic to `B`. -/
def LocalModel (B : Over (Spec (CommRingCat.of L))) (v : Ideal D) [v.IsPrime]
    (N : Over (Spec (CommRingCat.of (Localization.AtPrime v)))) : Prop :=
  letI := locAlg L v
  CToPrinted.IsNeronModelOver (Localization.AtPrime v) L N ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.AtPrime v) L)))).obj N ≅ B)

/-- **Spreading the local Néron model at `v`.** -/
theorem spreadAt (B : Over (Spec (CommRingCat.of L))) (v : Ideal D) [v.IsPrime]
    (N : Over (Spec (CommRingCat.of (Localization.AtPrime v)))) (hN : LocalModel B v N) :
    ∃ (Dv : (S D).Opens) (X : Over (S D)) (_ : Smooth X.hom) (_ : IsSeparated X.hom)
      (_ : QuasiCompact X.hom) (_ : (gf D L).obj X ≅ B), pt v ∈ Dv ∧ LocNeron L v X := by
  letI := locAlg L v
  haveI := locAlg_tower L v
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨eN⟩⟩ := hN
  haveI := h1; haveI := h2; haveI := h4
  obtain ⟨a, W, hWs, hWsep, hWqc, ⟨eW⟩⟩ := exists_spread_sep (𝔭 := v) (Localization.AtPrime v) N
  haveI := hWs; haveI := hWsep; haveI := hWqc
  let X : Over (S D) := Over.mk (W.hom ≫ ej a)
  haveI : Smooth X.hom := show Smooth (W.hom ≫ ej a) from inferInstance
  haveI : IsSeparated X.hom := show IsSeparated (W.hom ≫ ej a) from inferInstance
  haveI : QuasiCompact X.hom := show QuasiCompact (W.hom ≫ ej a) from inferInstance
  let jv := Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime v)))
  have hjv : (specCone v (Localization.AtPrime v)).π.app a ≫ ej a = jv := π_ej _ a
  let pbX : (Over.pullback jv).obj X ≅ N :=
    pbCongr hjv.symm X ≪≫ (Over.pullbackComp _ (ej a)).app X ≪≫
      (Over.pullback _).mapIso (NeronExt.pbMapIso (ej a) W) ≪≫ eW
  let kL := Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime v) L))
  have hk : kL ≫ jv = jL D L := by
    simp only [kL, jv, jL, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  let eX : (gf D L).obj X ≅ B :=
    pbCongr hk.symm X ≪≫ (Over.pullbackComp kL jv).app X ≪≫ (Over.pullback kL).mapIso pbX ≪≫ eN
  refine ⟨(ej a).opensRange, X, inferInstance, inferInstance, inferInstance, eX, ?_, ?_⟩
  · exact (mem_ej_opensRange a).2 a.unop.hs
  · show CToPrinted.IsNeronModelOver (Localization.AtPrime v) L ((Over.pullback jv).obj X)
    exact NeronExt.isNeronModelOver_of_iso pbX ⟨h1, h2, h3, h4, h5⟩

/-- **Prime avoidance.** For `k ≠ 0` and a maximal `v`, some `g ∉ v` lies in every other maximal ideal
containing `k`. -/
theorem exists_avoid (hnf : ¬ IsField D) (v : Ideal D) [hv : v.IsMaximal] (k : D) (hk : k ≠ 0) :
    ∃ g : D, g ∉ v ∧ ∀ w : Ideal D, w.IsMaximal → w ≠ v → k ∈ w → g ∈ w := by
  classical
  have hI : Ideal.span {k} ≠ (0 : Ideal D) := by
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
    have hw0 : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hwmax hnf
    let w' : IsDedekindDomain.HeightOneSpectrum D := ⟨w, hwmax.isPrime, hw0⟩
    have hw'T : w' ∈ T := by
      refine Finset.mem_filter.2 ⟨?_, hwv⟩
      rw [Set.Finite.mem_toFinset]
      show w ∣ Ideal.span {k}
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hkw
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun u : T => x u.1 u.2) (Finset.mem_attach T ⟨w', hw'T⟩)
    rw [hc]
    exact Ideal.mul_mem_right c _ (hxw w' hw'T)

/-- Inclusion `res X U → res X U'` for `U ≤ U'`. -/
noncomputable def incl (X : Over (S D)) {U U' : (S D).Opens} (h : U ≤ U') : res X U ⟶ res X U' :=
  liftRes (supp_mono h (supp_res X U)) (resι X U)

@[simp] theorem incl_ι (X : Over (S D)) {U U' : (S D).Opens} (h : U ≤ U') :
    incl X h ≫ resι X U' = resι X U := liftRes_ι _ _

theorem mono_left_resι (X : Over (S D)) (U : (S D).Opens) {Y : Over (S D)} {f g : Y ⟶ res X U}
    (h : f ≫ resι X U = g ≫ resι X U) : f = g := by
  apply Over.OverMorphism.ext
  have h' := congrArg (fun t => t.left) h
  simp only [Over.comp_left] at h'
  exact (cancel_mono (resι X U).left).mp h'

/-- **Comparison near the generic point.** Two smooth separated quasi-compact models with the same
generic fibre agree over some `D(s₁) ∩ D(s₂)`: the Néron property at a maximal ideal there passes from
one to the other. -/
theorem isoNear (B : Over (Spec (CommRingCat.of L))) (X 𝒜 : Over (S D)) [Smooth X.hom]
    [IsSeparated X.hom] [QuasiCompact X.hom] [Smooth 𝒜.hom] [IsSeparated 𝒜.hom]
    [QuasiCompact 𝒜.hom] (eX : (gf D L).obj X ≅ B) (eA : (gf D L).obj 𝒜 ≅ B) :
    ∃ s₁ s₂ : GIdx D, ∀ (w : Ideal D) [w.IsPrime], w ∈ maxIn (Dg s₁ ⊓ Dg s₂) →
      LocNeron L w 𝒜 → LocNeron L w X := by
  obtain ⟨s₁, α, hα⟩ := spread_generic (L := L) X 𝒜 (eX.hom ≫ eA.inv)
  obtain ⟨s₂, β, hβ⟩ := spread_generic (L := L) 𝒜 X (eA.hom ≫ eX.inv)
  refine ⟨s₁, s₂, fun w _ hw h𝒜 => ?_⟩
  let U := Dg s₁ ⊓ Dg s₂
  let α' : res X U ⟶ res 𝒜 U := liftRes (supp_res X U) (incl X inf_le_left ≫ α)
  let β' : res 𝒜 U ⟶ res X U := liftRes (supp_res 𝒜 U) (incl 𝒜 inf_le_right ≫ β)
  have gα : (gf D L).map α' ≫ (gf D L).map (resι 𝒜 U) = (gf D L).map (resι X U) ≫ eX.hom ≫ eA.inv := by
    rw [← CategoryTheory.Functor.map_comp, liftRes_ι, CategoryTheory.Functor.map_comp, hα,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp, incl_ι]
  have gβ : (gf D L).map β' ≫ (gf D L).map (resι X U) = (gf D L).map (resι 𝒜 U) ≫ eA.hom ≫ eX.inv := by
    rw [← CategoryTheory.Functor.map_comp, liftRes_ι, CategoryTheory.Functor.map_comp, hβ,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp, incl_ι]
  have h1 : α' ≫ β' = 𝟙 _ := by
    apply mono_left_resι X U
    apply neron_extension_injective X eX (res X U)
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Category.id_comp]
    show (gf D L).map α' ≫ (gf D L).map β' ≫ (gf D L).map (resι X U) ≫ eX.hom =
      (gf D L).map (resι X U) ≫ eX.hom
    rw [← Category.assoc ((gf D L).map β'), gβ, Category.assoc, Category.assoc,
      ← Category.assoc ((gf D L).map α'), gα]
    simp
  have h2 : β' ≫ α' = 𝟙 _ := by
    apply mono_left_resι 𝒜 U
    apply neron_extension_injective 𝒜 eA (res 𝒜 U)
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Category.id_comp]
    show (gf D L).map β' ≫ (gf D L).map α' ≫ (gf D L).map (resι 𝒜 U) ≫ eA.hom =
      (gf D L).map (resι 𝒜 U) ≫ eA.hom
    rw [← Category.assoc ((gf D L).map α'), gα, Category.assoc, Category.assoc,
      ← Category.assoc ((gf D L).map β'), gβ]
    simp
  let i : res X U ≅ res 𝒜 U := ⟨α', β', h1, h2⟩
  rw [← locNeron_res_iff hw X]
  rw [← locNeron_res_iff hw 𝒜] at h𝒜
  exact locNeron_of_iso i h𝒜

/-- The basic open `D(g)`. -/
def Db (g : D) : (S D).Opens := PrimeSpectrum.basicOpen (R := D) g

theorem mem_Db {g : D} {x : S D} : x ∈ Db g ↔ g ∉ (PrimeSpectrum.asIdeal (R := D) x) :=
  PrimeSpectrum.mem_basicOpen _ _

/-- Given a local Néron model at a maximal ideal `v` and a smooth separated
quasi-compact model `𝒜` which is a Néron model at every maximal ideal not containing `f ≠ 0`, `B` has a
Néron model over an open neighbourhood of `v`. -/
theorem near (hnf : ¬ IsField D) (B : Over (Spec (CommRingCat.of L))) (v : Ideal D) [hv : v.IsMaximal]
    (N : Over (Spec (CommRingCat.of (Localization.AtPrime v)))) (hN : LocalModel B v N)
    (𝒜 : Over (S D)) [Smooth 𝒜.hom] [IsSeparated 𝒜.hom] [QuasiCompact 𝒜.hom]
    (eA : (gf D L).obj 𝒜 ≅ B) (f : D) (hf : f ≠ 0)
    (h𝒜 : ∀ (w : Ideal D) [w.IsMaximal], f ∉ w → LocNeron L w 𝒜) :
    ∃ U : (S D).Opens, pt v ∈ U ∧ Nonempty (NeronOn D L B U) := by
  obtain ⟨Dv, X, hXs, hXsep, hXqc, eX, hvD, hXv⟩ := spreadAt B v N hN
  haveI := hXs; haveI := hXsep; haveI := hXqc
  obtain ⟨s₁, s₂, hcmp⟩ := isoNear B X 𝒜 eX eA
  let k := s₁.unop.s * s₂.unop.s * f
  have hk : k ≠ 0 := mul_ne_zero (mul_ne_zero (ne_zero_of_idx s₁) (ne_zero_of_idx s₂)) hf
  obtain ⟨g, hgv, hg⟩ := exists_avoid hnf v k hk
  let U := Dv ⊓ Db g
  have hvU : pt v ∈ U := ⟨hvD, mem_Db.2 hgv⟩
  have hU : (jL D L) ⁻¹ᵁ U = ⊤ := jL_preimage_eq_top D L ⟨_, hvU⟩
  haveI := isIso_gf_resι (L := L) X hU
  refine ⟨U, hvU, ⟨neronOn_of_local B U (res X U) (supp_res X U)
    (asIso ((gf D L).map (resι X U)) ≪≫ eX) (fun w _ hw => ?_) (hT_of_mem (pt v) hv hvU)⟩⟩
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

end NeronExtDedekind
