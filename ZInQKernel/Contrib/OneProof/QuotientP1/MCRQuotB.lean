import ZInQKernel.Contrib.OneProof.QuotientP1.MCRQuotA

/-!
# p1-quot, helper B: mcr-glue parts 5-6 and mcr-quot parts 12-24 over the chain

`scratch/mcr-quot/MCRQuot.lean` from its line 4406 on (mcr-glue parts 5-6, mcr-quot parts 1-24; everything before
that line is `scratch/mcr-glue/MCRGlue.lean`, which the chain holds as `TailL`..`TailW` in `namespace HDec`), verbatim
inside `namespace HDec`, except that `ImagePlane.*`, `curveFacts`, `smoothStalkDimOne` and one `transportLevel` are
written with the prefix `_root_.LeafQM.AV.Pin.` (inside `namespace HDec` the unqualified names resolve to the chain's
aliases or are ambiguous). Split in two files at mcr-quot's part 12 (size). docs/research/p1-quot.md. -/


namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 12: translations of a coordinate (towards `P1Translate`)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV MCRGlue LeafQM.AV.Pin
open TopologicalSpace Opposite

section Translate

variable {X : Scheme.{0}}

theorem res_inv_mul {O O' : X.Opens} (h : O' ≤ O) (u : (Γ(X, O))ˣ) :
    res h (↑u⁻¹ : Γ(X, O)) * res h (u : Γ(X, O)) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

theorem res_res' {O O' O'' : X.Opens} (h : O' ≤ O) (h' : O'' ≤ O') (h'' : O'' ≤ O)
    (s : Γ(X, O)) : res h' (res h s) = res h'' s := res_res h h' s

theorem eq_of_mul_eq_one {R : Type*} [CommRing R] {a b c : R} (ha : a * c = 1) (hb : b * c = 1) :
    a = b := by
  calc a = a * (c * b) := by rw [mul_comm c b, hb, mul_one]
    _ = (a * c) * b := by ring
    _ = b := by rw [ha, one_mul]

/-- Outside the basic open of `s`, `1 + a s` is a unit. -/
theorem mem_basicOpen_one_add {O : X.Opens} (a s : Γ(X, O)) {x : X} (hx : x ∈ O)
    (hs : x ∉ X.basicOpen s) : x ∈ X.basicOpen (1 + a * s) := by
  rw [Scheme.mem_basicOpen _ _ x hx] at hs ⊢
  rw [map_add, map_one, map_mul]
  apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
  rw [show (1 : X.presheaf.stalk x) - (1 + _ * _) = -(X.presheaf.germ O x hx a *
    X.presheaf.germ O x hx s) by ring, ← IsLocalRing.mem_maximalIdeal]
  refine neg_mem (Ideal.mul_mem_left _ _ ?_)
  rw [IsLocalRing.mem_maximalIdeal]
  exact hs

variable (ρ : ToP1 X) (E : Γ(X, ⊤))

/-- `f + E` on `U`. -/
def tF : Γ(X, ρ.U) := ρ.f + res le_top E
/-- `1 + E g` on `V`. -/
def tG : Γ(X, ρ.V) := 1 + res le_top E * ρ.g
/-- `D_U(f + E)`. -/
def tDU : X.Opens := X.basicOpen (tF ρ E)
/-- `D_V(1 + E g)`. -/
def tDV : X.Opens := X.basicOpen (tG ρ E)

theorem tDU_le : tDU ρ E ≤ ρ.U := Scheme.basicOpen_le _ _
theorem tDV_le : tDV ρ E ≤ ρ.V := Scheme.basicOpen_le _ _

/-- The unit `f + E` on `D_U(f + E)`. -/
def uF : (Γ(X, tDU ρ E))ˣ := (X.toRingedSpace.isUnit_res_basicOpen (tF ρ E)).unit
/-- The unit `1 + E g` on `D_V(1 + E g)`. -/
def uG : (Γ(X, tDV ρ E))ˣ := (X.toRingedSpace.isUnit_res_basicOpen (tG ρ E)).unit

theorem uF_val : (uF ρ E : Γ(X, tDU ρ E)) = res (tDU_le ρ E) (tF ρ E) := rfl
theorem uG_val : (uG ρ E : Γ(X, tDV ρ E)) = res (tDV_le ρ E) (tG ρ E) := rfl

/-- `g / (1 + E g)` on `D_V(1 + E g)`. -/
def tS1 : Γ(X, tDV ρ E) := res (tDV_le ρ E) ρ.g * ↑(uG ρ E)⁻¹
/-- `1 / (f + E)` on `D_U(f + E)`. -/
def tS2 : Γ(X, tDU ρ E) := ↑(uF ρ E)⁻¹

/-- On `U ⊓ V`, `g · (f + E) = 1 + E g`. -/
theorem g_mul_tF {W : X.Opens} (hW : W ≤ ρ.U ⊓ ρ.V) :
    res (hW.trans inf_le_right) ρ.g * res (hW.trans inf_le_left) (tF ρ E) =
      res (hW.trans inf_le_right) (tG ρ E) := by
  have hinv := congrArg (res (hW : W ≤ ρ.U ⊓ ρ.V)) ρ.inv
  rw [map_mul, map_one, res_res, res_res] at hinv
  simp only [tF, tG, map_add, map_mul, map_one, res_res]
  rw [mul_add, mul_comm (res _ ρ.g) (res _ ρ.f), hinv, mul_comm]

theorem tS_compat :
    res (inf_le_left : tDV ρ E ⊓ tDU ρ E ≤ tDV ρ E) (tS1 ρ E) =
      res (inf_le_right : tDV ρ E ⊓ tDU ρ E ≤ tDU ρ E) (tS2 ρ E) := by
  have hW : tDV ρ E ⊓ tDU ρ E ≤ ρ.U ⊓ ρ.V :=
    le_inf (inf_le_right.trans (tDU_le ρ E)) (inf_le_left.trans (tDV_le ρ E))
  let c := res (hW.trans inf_le_left) (tF ρ E)
  refine eq_of_mul_eq_one (c := c) ?_ ?_
  · have h1 := g_mul_tF ρ E hW
    simp only [tS1, map_mul, c, res_res]
    rw [mul_assoc, mul_comm (res _ (↑(uG ρ E)⁻¹ : Γ(X, tDV ρ E))), ← mul_assoc, h1]
    have := res_inv_mul (inf_le_left : tDV ρ E ⊓ tDU ρ E ≤ tDV ρ E) (uG ρ E)
    rw [uG_val, res_res] at this
    rw [mul_comm]; exact this
  · have := res_inv_mul (inf_le_right : tDV ρ E ⊓ tDU ρ E ≤ tDU ρ E) (uF ρ E)
    rw [uF_val, res_res] at this
    exact this

/-- `g' = 1/(t + E)` on `V' = D_V(1 + E g) ∪ D_U(f + E)`, glued. -/
def tg : Γ(X, tDV ρ E ⊔ tDU ρ E) :=
  (X.sheaf.objSupIsoProdEqLocus (tDV ρ E) (tDU ρ E)).inv ⟨(tS1 ρ E, tS2 ρ E), tS_compat ρ E⟩

theorem tg_res_DV : res (le_sup_left : tDV ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E) = tS1 ρ E :=
  TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf _ _ _

theorem tg_res_DU : res (le_sup_right : tDU ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E) = tS2 ρ E :=
  TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf _ _ _

omit ρ E in
theorem basicOpen_res_of_le {O O' : X.Opens} (h : O' ≤ O) (s : Γ(X, O)) :
    X.basicOpen (res h s) = O' ⊓ X.basicOpen s := Scheme.basicOpen_res X s (homOfLE h).op

theorem U_inf_tDV_le : ρ.U ⊓ tDV ρ E ≤ tDU ρ E := by
  intro x hx
  have hW : ρ.U ⊓ tDV ρ E ≤ ρ.U ⊓ ρ.V := inf_le_inf_left _ (tDV_le ρ E)
  have h1 := g_mul_tF ρ E hW
  have h2 : x ∈ X.basicOpen (res (hW.trans inf_le_right) (tG ρ E)) := by
    rw [basicOpen_res_of_le]; exact ⟨hx, hx.2⟩
  rw [← h1, Scheme.basicOpen_mul] at h2
  have h3 := h2.2
  rw [basicOpen_res_of_le] at h3
  exact h3.2

theorem tF_basicOpen : X.basicOpen (tF ρ E) = ρ.U ⊓ (tDV ρ E ⊔ tDU ρ E) := by
  apply le_antisymm
  · exact le_inf (tDU_le ρ E) le_sup_right
  · rintro x ⟨hU, hx⟩
    rcases hx with h | h
    · exact U_inf_tDV_le ρ E ⟨hU, h⟩
    · exact h

/-- **The translated coordinate `ρ + E`.** -/
def translate : ToP1 X where
  U := ρ.U
  V := tDV ρ E ⊔ tDU ρ E
  cover := by
    apply eq_top_iff.mpr
    intro x _
    by_cases hU : x ∈ ρ.U
    · exact Or.inl hU
    · have hV : x ∈ ρ.V := mem_V_of_not_mem_U ρ hU
      have hg : x ∉ X.basicOpen ρ.g := by rw [ρ.basicOpen_g]; exact fun h => hU h.1
      exact Or.inr (Or.inl (mem_basicOpen_one_add (res le_top E) ρ.g hV hg))
  f := tF ρ E
  g := tg ρ E
  inv := by
    refine X.sheaf.eq_of_locally_eq₂ (homOfLE (le_inf inf_le_left (inf_le_right.trans le_sup_left) :
        ρ.U ⊓ tDV ρ E ≤ ρ.U ⊓ (tDV ρ E ⊔ tDU ρ E)))
      (homOfLE (le_inf (tDU_le ρ E) le_sup_right : tDU ρ E ≤ ρ.U ⊓ (tDV ρ E ⊔ tDU ρ E)))
      ?_ _ _ ?_ ?_
    · rintro x ⟨hU, hx⟩
      rcases hx with h | h
      · exact Or.inl ⟨hU, h⟩
      · exact Or.inr h
    · change res _ (res _ (tF ρ E) * res _ (tg ρ E)) = res _ 1
      rw [map_mul, map_one, res_res, res_res]
      rw [show res (_ : ρ.U ⊓ tDV ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E) =
          res (inf_le_right : ρ.U ⊓ tDV ρ E ≤ tDV ρ E) (res le_sup_left (tg ρ E)) from
          (res_res _ _ _).symm, tg_res_DV]
      simp only [tS1, map_mul, res_res]
      have h1 := g_mul_tF ρ E (W := ρ.U ⊓ tDV ρ E) (inf_le_inf_left _ (tDV_le ρ E))
      rw [← mul_assoc, mul_comm (res _ (tF ρ E)), h1]
      have := res_inv_mul (inf_le_right : ρ.U ⊓ tDV ρ E ≤ tDV ρ E) (uG ρ E)
      rw [uG_val, res_res] at this
      rw [mul_comm]; exact this
    · change res _ (res _ (tF ρ E) * res _ (tg ρ E)) = res _ 1
      rw [map_mul, map_one, res_res, res_res, tg_res_DU, tS2,
        show res (_ : tDU ρ E ≤ ρ.U) (tF ρ E) = (uF ρ E : Γ(X, tDU ρ E)) from rfl,
        Units.mul_inv]
  basicOpen_f := tF_basicOpen ρ E
  basicOpen_g := by
    rw [← tF_basicOpen]
    apply le_antisymm
    · intro x hx
      have hxV : x ∈ tDV ρ E ⊔ tDU ρ E := Scheme.basicOpen_le _ _ hx
      rcases hxV with h | h
      · have h2 : x ∈ X.basicOpen (res (le_sup_left : tDV ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E)) := by
          rw [basicOpen_res_of_le]; exact ⟨h, hx⟩
        rw [tg_res_DV, tS1, Scheme.basicOpen_mul, basicOpen_res_of_le] at h2
        have h3 : x ∈ X.basicOpen ρ.g := h2.1.2
        rw [ρ.basicOpen_g] at h3
        exact U_inf_tDV_le ρ E ⟨h3.1, h⟩
      · exact h
    · intro x hx
      have h2 : X.basicOpen (res (le_sup_right : tDU ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E)) =
          tDU ρ E := by
        rw [tg_res_DU, tS2]; exact Scheme.basicOpen_of_isUnit _ (Units.isUnit _)
      have h3 : x ∈ X.basicOpen (res (le_sup_right : tDU ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E)) := by
        rw [h2]; exact hx
      rw [basicOpen_res_of_le] at h3
      exact h3.2

end Translate

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 13: (C1c) `StabFixesClosure` proved (the fixed locus as a closed subscheme)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- The residue field map of a closed immersion is an isomorphism (the stalk map is surjective). -/
theorem isIso_residueFieldMap_of_closedImm {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  have hs : Function.Surjective (f.residueFieldMap x) := by
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
    refine ⟨Y.residue (f x) c, ?_⟩
    rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap]
    rfl
  have hb : Function.Bijective (f.residueFieldMap x) := ⟨(f.residueFieldMap x).hom.injective, hs⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2 hb

/-- A field point whose point lies in the range of a closed immersion factors through it. -/
theorem exists_factor_of_mem_range_closedImm {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ Y) (ht : ptOf t ∈ Set.range f) :
    ∃ t' : Spec (CommRingCat.of K) ⟶ X, t' ≫ f = t := by
  obtain ⟨e, he⟩ := ht
  have := isIso_residueFieldMap_of_closedImm f e
  set xf := Scheme.SpecToEquivOfField K Y t with hxf
  have ht' : t = Spec.map xf.2 ≫ Y.fromSpecResidueField xf.1 :=
    ((Scheme.SpecToEquivOfField K Y).symm_apply_apply t).symm
  have h1 : Y.fromSpecResidueField (f e) =
      Spec.map (inv (f.residueFieldMap e)) ≫ X.fromSpecResidueField e ≫ f := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  refine ⟨Spec.map xf.2 ≫ Spec.map (Y.residueFieldCongr he).hom ≫
    Spec.map (inv (f.residueFieldMap e)) ≫ X.fromSpecResidueField e, ?_⟩
  refine Eq.trans ?_ ht'.symm
  simp only [Category.assoc]
  rw [← h1, Scheme.residueFieldCongr_fromSpecResidueField]

/-- **The fixed locus is closed and contains the closure of a fixed point.** For an automorphism
`h` over `S` of a separated `S`-scheme `X` and a field point `y` with `y ≫ h = y`, every field point
whose point lies in the closure of the point of `y` is fixed by `h`. Proof: the equalizer of `h`
and `id` in `Over S` is a closed subscheme (`isClosedImmersion_equalizer_ι_left`, Stacks 01KM);
`y` factors through it, so its closed range contains the closure; a field point with point in the
range of a closed immersion factors through it (residue fields agree). -/
theorem fixes_closure_of_separated {S : Scheme.{0}} (X : Over S) [IsSeparated X.hom]
    (h : X.left ≅ X.left) (hh : h.hom ≫ X.hom = X.hom) {K₀ : Type} [Field K₀]
    (y : Spec (CommRingCat.of K₀) ⟶ X.left) (hy : y ≫ h.hom = y) {K : Type} [Field K]
    (t : Spec (CommRingCat.of K) ⟶ X.left) (ht : ptOf t ∈ closure {ptOf y}) : t ≫ h.hom = t := by
  let f : X ⟶ X := Over.homMk h.hom hh
  let g : X ⟶ X := 𝟙 X
  let ι := (equalizer.ι f g).left
  have hι : ι ≫ h.hom = ι := by
    have := congrArg CommaMorphism.left (equalizer.condition f g)
    simpa [f, g, ι] using this
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hyr : ptOf y ∈ Set.range ι := by
    let y' : Over.mk (y ≫ X.hom) ⟶ X := Over.homMk y rfl
    have hc : y' ≫ f = y' ≫ g := by
      ext1; simpa [f, g, y'] using hy
    refine ⟨(equalizer.lift y' hc).left (IsLocalRing.closedPoint K₀), ?_⟩
    show ((equalizer.lift y' hc).left ≫ (equalizer.ι f g).left) _ = _
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have htr : ptOf t ∈ Set.range ι :=
    (closure_minimal (Set.singleton_subset_iff.2 hyr) hcl) ht
  obtain ⟨t', rfl⟩ := exists_factor_of_mem_range_closedImm ι t htr
  rw [Category.assoc, hι]

/-- **(C1c) `StabFixesClosure` proved.** Only the separatedness of `𝒴 → Spec ℤ_(p)` (from
properness) is used; smoothness is not needed, and the fixed field points over the closure need no
spreading out (EGA IV 8.13.1 is not used). -/
theorem stabFixesClosure : StabFixesClosure := by
  intro p _ 𝒴 hP _ h hh y hy K _ t ht
  exact fixes_closure_of_separated 𝒴 h.asIso hh y hy t ht

/-- **Glue C1 from glue A, (A-fix), (C1b)** ((C1a), (C1c), (C1d) proved). -/
theorem cMSectionsDisjoint_of'' (hA : FibreAutTame) (hfix : FibreAutFixFinite)
    (hI : CMStabInvolution) : CMSectionsDisjoint :=
  cMSectionsDisjoint_of' hA hfix hI stabFixesClosure

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 14: (C2-T) `P1Translate` proved (translations of `P¹_{ℤ_(p)}` by charts)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

variable {p : ℕ} [Fact p.Prime]

/-- Bijectivity of `X ↦ h + c` when `X ↦ h` is bijective. -/
theorem bijective_eval₂_add {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (h : S)
    (c : R) (hb : Function.Bijective (eval₂RingHom φ h)) :
    Function.Bijective (eval₂RingHom φ (h + φ c)) := by
  let m : R[X] →+* R[X] := eval₂RingHom C (X + C c)
  let m' : R[X] →+* R[X] := eval₂RingHom C (X - C c)
  have hcomp : eval₂RingHom φ (h + φ c) = (eval₂RingHom φ h).comp m := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m]
    · simp [m]
  have hmm' : m.comp m' = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m, m']
    · simp [m, m']
  have hm'm : m'.comp m = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m, m']
    · simp [m, m']
  have hmb : Function.Bijective m :=
    ⟨Function.LeftInverse.injective (g := m') (fun x => congrArg (fun f => f x) hm'm),
      Function.RightInverse.surjective (g := m') (fun x => congrArg (fun f => f x) hmm')⟩
  rw [hcomp, RingHom.coe_comp]
  exact hb.comp hmb

section P1T

variable (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (ρ : ToP1 𝒵.left) (e : Zloc p)

/-- The constant `e` as a global section. -/
abbrev cE : Γ(𝒵.left, ⊤) := baseToSections 𝒵 ⊤ e

theorem res_cE {W : 𝒵.left.Opens} (h : W ≤ ⊤) : res h (cE 𝒵 e) = baseToSections 𝒵 W e :=
  res_baseToSections 𝒵 h e

theorem tF_eq : tF ρ (cE 𝒵 e) = ρ.f + baseToSections 𝒵 ρ.U e := by
  rw [tF, res_cE]

/-- The section `h' = 1 − e g'` on `V'`. -/
def tH : Γ(𝒵.left, tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e)) :=
  1 - baseToSections 𝒵 _ e * tg ρ (cE 𝒵 e)

theorem basicOpen_tg : 𝒵.left.basicOpen (tg ρ (cE 𝒵 e)) = tDU ρ (cE 𝒵 e) :=
  (translate ρ (cE 𝒵 e)).basicOpen_g.trans (tF_basicOpen ρ (cE 𝒵 e)).symm

theorem res_tH_DV : res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e) * (uG ρ (cE 𝒵 e) : _) = 1 := by
  have hu := Units.inv_mul (uG ρ (cE 𝒵 e))
  have huval : (uG ρ (cE 𝒵 e) : Γ(𝒵.left, tDV ρ (cE 𝒵 e))) =
      1 + baseToSections 𝒵 _ e * res (tDV_le ρ (cE 𝒵 e)) ρ.g := by
    rw [uG_val, tG, map_add, map_one, map_mul, res_res, res_cE]
  rw [tH, map_sub, map_one, map_mul, res_baseToSections, tg_res_DV, tS1]
  linear_combination huval - baseToSections 𝒵 (tDV ρ (cE 𝒵 e)) e *
    res (tDV_le ρ (cE 𝒵 e)) ρ.g * hu

theorem res_tH_DU : res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e) =
    res (tDU_le ρ (cE 𝒵 e)) ρ.f * (tS2 ρ (cE 𝒵 e)) := by
  have hu := Units.mul_inv (uF ρ (cE 𝒵 e))
  have huval : (uF ρ (cE 𝒵 e) : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) =
      res (tDU_le ρ (cE 𝒵 e)) ρ.f + baseToSections 𝒵 _ e := by
    rw [uF_val, tF_eq, map_add, res_baseToSections]
  rw [tH, map_sub, map_one, map_mul, res_baseToSections, tg_res_DU, tS2]
  linear_combination (-1 : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) * hu +
    (↑(uF ρ (cE 𝒵 e))⁻¹ : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) * huval

theorem basicOpen_tH : 𝒵.left.basicOpen (tH 𝒵 ρ e) = tDV ρ (cE 𝒵 e) := by
  apply le_antisymm
  · intro x hx
    have hxV : x ∈ tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e) := Scheme.basicOpen_le _ _ hx
    rcases hxV with h | h
    · exact h
    · have h2 : x ∈ 𝒵.left.basicOpen (res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e)) := by
        rw [basicOpen_res_of_le]; exact ⟨h, hx⟩
      rw [res_tH_DU, Scheme.basicOpen_mul, basicOpen_res_of_le, ρ.basicOpen_f] at h2
      have hUV : x ∈ ρ.U ⊓ ρ.V := h2.1.2
      have h1 := g_mul_tF ρ (cE 𝒵 e) (W := ρ.U ⊓ ρ.V) le_rfl
      have h3 : x ∈ 𝒵.left.basicOpen (res (le_rfl.trans inf_le_right : ρ.U ⊓ ρ.V ≤ ρ.V) ρ.g *
          res (le_rfl.trans inf_le_left : ρ.U ⊓ ρ.V ≤ ρ.U) (tF ρ (cE 𝒵 e))) := by
        rw [Scheme.basicOpen_mul, basicOpen_res_of_le, basicOpen_res_of_le, ρ.basicOpen_g]
        exact ⟨⟨hUV, hUV⟩, ⟨hUV, h⟩⟩
      rw [h1, basicOpen_res_of_le] at h3
      exact h3.2
  · intro x hx
    have h2 : 𝒵.left.basicOpen (res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e)) =
        tDV ρ (cE 𝒵 e) :=
      Scheme.basicOpen_of_isUnit _ (isUnit_iff_exists_inv.mpr ⟨_, res_tH_DV 𝒵 ρ e⟩)
    have h3 : x ∈ 𝒵.left.basicOpen (res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e)) := by
      rw [h2]; exact hx
    rw [basicOpen_res_of_le] at h3
    exact h3.2

theorem isAffineOpen_V' (hρ : IsP1Coordinate 𝒵 ρ) :
    IsAffineOpen (tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e)) := by
  refine isAffineOpen_of_isAffineOpen_basicOpen _ {tg ρ (cE 𝒵 e), tH 𝒵 ρ e} ?_ ?_
  · rw [Ideal.eq_top_iff_one]
    have : (1 : Γ(𝒵.left, tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e))) =
        baseToSections 𝒵 _ e * tg ρ (cE 𝒵 e) + tH 𝒵 ρ e := by rw [tH]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.subset_span (by simp))
  · rintro i (rfl | rfl)
    · rw [basicOpen_tg]; exact hρ.1.basicOpen _
    · rw [basicOpen_tH]; exact hρ.2.1.basicOpen _

/-- `res` of `ψ(P) = P(g')` to `D_U(f + e)` is `P(1/(f + e))`. -/
theorem res_eval_DU (P : (Zloc p)[X]) :
    res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (eval₂ (baseToSections 𝒵 _) (tg ρ (cE 𝒵 e)) P) =
      eval₂ (baseToSections 𝒵 _) (↑(uF ρ (cE 𝒵 e))⁻¹ : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) P := by
  rw [hom_eval₂, tg_res_DU, tS2,
    show (res _).comp (baseToSections 𝒵 _) = baseToSections 𝒵 (tDU ρ (cE 𝒵 e)) from
      RingHom.ext (res_baseToSections 𝒵 _)]

/-- `res` of `ψ(P) = P(g')` to `D_V(1 + e g)` is `P(g/(1 + e g))`. -/
theorem res_eval_DV (P : (Zloc p)[X]) :
    res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (eval₂ (baseToSections 𝒵 _) (tg ρ (cE 𝒵 e)) P) =
      eval₂ (baseToSections 𝒵 _) (tS1 ρ (cE 𝒵 e)) P := by
  rw [hom_eval₂, tg_res_DV,
    show (res _).comp (baseToSections 𝒵 _) = baseToSections 𝒵 (tDV ρ (cE 𝒵 e)) from
      RingHom.ext (res_baseToSections 𝒵 _)]

/-- Sections on `D_U(f + e)` are polynomials in `1/(f + e)` up to a power of `1/(f + e)`. -/
theorem exists_poly_DU (hρ : IsP1Coordinate 𝒵 ρ) (z : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) :
    ∃ (N : ℕ) (P : (Zloc p)[X]),
      z * (↑(uF ρ (cE 𝒵 e))⁻¹ : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) ^ N =
        eval₂ (baseToSections 𝒵 _) (↑(uF ρ (cE 𝒵 e))⁻¹ : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) P := by
  letI : Algebra Γ(𝒵.left, ρ.U) Γ(𝒵.left, tDU ρ (cE 𝒵 e)) := (res (tDU_le ρ (cE 𝒵 e))).toAlgebra
  haveI := hρ.1.isLocalization_of_eq_basicOpen (tF ρ (cE 𝒵 e)) (homOfLE (tDU_le ρ (cE 𝒵 e))) rfl
  obtain ⟨⟨a0, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (tF ρ (cE 𝒵 e))) z
  obtain ⟨Q, rfl⟩ := hρ.2.2.1.2 a0
  change z * res (tDU_le ρ (cE 𝒵 e)) (tF ρ (cE 𝒵 e) ^ n) =
    res (tDU_le ρ (cE 𝒵 e)) (eval₂ (baseToSections 𝒵 ρ.U) ρ.f Q) at hz
  set x : Γ(𝒵.left, tDU ρ (cE 𝒵 e)) := ↑(uF ρ (cE 𝒵 e)) with hxdef
  set xi : Γ(𝒵.left, tDU ρ (cE 𝒵 e)) := ↑(uF ρ (cE 𝒵 e))⁻¹ with hxidef
  have hx : x * xi = 1 := Units.mul_inv _
  letI : Invertible x := Units.invertible _
  have hfx : res (tDU_le ρ (cE 𝒵 e)) ρ.f = x - baseToSections 𝒵 _ e := by
    rw [hxdef, uF_val, tF_eq, map_add, res_baseToSections]; ring
  have hQ : res (tDU_le ρ (cE 𝒵 e)) (eval₂ (baseToSections 𝒵 ρ.U) ρ.f Q) =
      eval₂ (baseToSections 𝒵 _) x (Q.comp (X - C e)) := by
    rw [hom_eval₂, show (res _).comp (baseToSections 𝒵 ρ.U) = baseToSections 𝒵 (tDU ρ (cE 𝒵 e))
      from RingHom.ext (res_baseToSections 𝒵 _), hfx, eval₂_comp]
    simp
  set Q' := Q.comp (X - C e)
  set N := Q'.natDegree
  have hR := eval₂_reflect_mul_pow (baseToSections 𝒵 (tDU ρ (cE 𝒵 e))) x N Q' le_rfl
  have hinv : (⅟x : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) = xi := rfl
  rw [hinv] at hR
  have hxn : res (tDU_le ρ (cE 𝒵 e)) (tF ρ (cE 𝒵 e) ^ n) = x ^ n := by
    rw [map_pow, hxdef, uF_val]
  rw [hxn, hQ, ← hR] at hz
  refine ⟨N, reflect N Q' * X ^ n, ?_⟩
  rw [eval₂_mul, eval₂_X_pow]
  set R := eval₂ (baseToSections 𝒵 (tDU ρ (cE 𝒵 e))) xi (reflect N Q')
  calc z * xi ^ N = z * xi ^ N * (x * xi) ^ n := by rw [hx, one_pow, mul_one]
    _ = (z * x ^ n) * xi ^ N * xi ^ n := by ring
    _ = R * x ^ N * xi ^ N * xi ^ n := by rw [hz]
    _ = R * xi ^ n * (x * xi) ^ N := by ring
    _ = R * xi ^ n := by rw [hx, one_pow, mul_one]

/-- Sections on `D_V(1 + e g)` are polynomials in `g' = g/(1 + e g)` up to a power of
`h' = 1/(1 + e g)`. -/
theorem exists_poly_DV (hρ : IsP1Coordinate 𝒵 ρ) (z : Γ(𝒵.left, tDV ρ (cE 𝒵 e))) :
    ∃ (N : ℕ) (P : (Zloc p)[X]),
      z * res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e) ^ N =
        eval₂ (baseToSections 𝒵 _) (tS1 ρ (cE 𝒵 e)) P := by
  letI : Algebra Γ(𝒵.left, ρ.V) Γ(𝒵.left, tDV ρ (cE 𝒵 e)) := (res (tDV_le ρ (cE 𝒵 e))).toAlgebra
  haveI := hρ.2.1.isLocalization_of_eq_basicOpen (tG ρ (cE 𝒵 e)) (homOfLE (tDV_le ρ (cE 𝒵 e))) rfl
  obtain ⟨⟨b0, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (tG ρ (cE 𝒵 e))) z
  obtain ⟨Q, rfl⟩ := hρ.2.2.2.2 b0
  change z * res (tDV_le ρ (cE 𝒵 e)) (tG ρ (cE 𝒵 e) ^ n) =
    res (tDV_le ρ (cE 𝒵 e)) (eval₂ (baseToSections 𝒵 ρ.V) ρ.g Q) at hz
  set φ := baseToSections 𝒵 (tDV ρ (cE 𝒵 e))
  set y : Γ(𝒵.left, tDV ρ (cE 𝒵 e)) := ↑(uG ρ (cE 𝒵 e)) with hydef
  set v := res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e) with hvdef
  set w := tS1 ρ (cE 𝒵 e) with hwdef
  set a := res (tDV_le ρ (cE 𝒵 e)) ρ.g with hadef
  have hvy : v * y = 1 := res_tH_DV 𝒵 ρ e
  have hv : v = 1 - φ e * w := by
    rw [hvdef, tH, map_sub, map_one, map_mul, res_baseToSections, tg_res_DV]
  have haw : a = w * y := by
    rw [hwdef, tS1, mul_assoc, Units.inv_mul, mul_one]
  have hyn : res (tDV_le ρ (cE 𝒵 e)) (tG ρ (cE 𝒵 e) ^ n) = y ^ n := by
    rw [map_pow, hydef, uG_val]
  have hQ : res (tDV_le ρ (cE 𝒵 e)) (eval₂ (baseToSections 𝒵 ρ.V) ρ.g Q) = eval₂ φ a Q := by
    rw [hom_eval₂, show (res _).comp (baseToSections 𝒵 ρ.V) = φ
      from RingHom.ext (res_baseToSections 𝒵 _)]
  rw [hyn, hQ] at hz
  set D := Q.natDegree + 1
  have hsum : eval₂ φ a Q = ∑ i ∈ Finset.range D, φ (Q.coeff i) * a ^ i :=
    eval₂_eq_sum_range' φ (Nat.lt_succ_self _) a
  refine ⟨D, ∑ i ∈ Finset.range D, C (Q.coeff i) * X ^ i * (1 - C e * X) ^ (n + D - i), ?_⟩
  rw [eval₂_finsetSum]
  have hterm : ∀ i ∈ Finset.range D,
      eval₂ φ w (C (Q.coeff i) * X ^ i * (1 - C e * X) ^ (n + D - i)) =
        φ (Q.coeff i) * a ^ i * v ^ (n + D) := by
    intro i hi
    have hiD : i ≤ n + D := (Finset.mem_range.1 hi).le.trans (Nat.le_add_left _ _)
    rw [eval₂_mul, eval₂_mul, eval₂_C, eval₂_X_pow, eval₂_pow, eval₂_sub, eval₂_one, eval₂_mul,
      eval₂_C, eval₂_X, ← hv, haw]
    conv_rhs => rw [← Nat.sub_add_cancel hiD, pow_add]
    calc φ (Q.coeff i) * w ^ i * v ^ (n + D - i)
        = φ (Q.coeff i) * w ^ i * v ^ (n + D - i) * (v * y) ^ i := by rw [hvy, one_pow, mul_one]
      _ = φ (Q.coeff i) * (w * y) ^ i * (v ^ (n + D - i) * v ^ i) := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← hsum, ← hz]
  calc z * v ^ D = z * v ^ D * (v * y) ^ n := by rw [hvy, one_pow, mul_one]
    _ = z * y ^ n * v ^ (n + D) := by ring

/-- Clearing a power of `s` after restriction to `D(s)` (`O` affine). -/
theorem exists_pow_mul_eq_of_res {X : Scheme.{0}} {O W : X.Opens} (hO : IsAffineOpen O)
    (hWO : W ≤ O) (s : Γ(X, O)) (hW : X.basicOpen s = W) (c d : Γ(X, O)) (N : ℕ)
    (h : res hWO c * (res hWO s) ^ N = res hWO d) : ∃ m : ℕ, s ^ m * (c * s ^ N) = s ^ m * d := by
  letI : Algebra Γ(X, O) Γ(X, W) := (res hWO).toAlgebra
  haveI := hO.isLocalization_of_eq_basicOpen s (homOfLE hWO) hW.symm
  have h0 : algebraMap Γ(X, O) Γ(X, W) (c * s ^ N - d) = 0 := by
    change res hWO (c * s ^ N - d) = 0
    rw [map_sub, map_mul, map_pow, h, sub_self]
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) Γ(X, W) _).1 h0
  refine ⟨m, ?_⟩
  rw [← sub_eq_zero, ← mul_sub]
  exact hm

theorem surjective_g' (hρ : IsP1Coordinate 𝒵 ρ) :
    Function.Surjective (eval₂RingHom (baseToSections 𝒵 (tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e)))
      (tg ρ (cE 𝒵 e))) := by
  intro c
  set ψ := eval₂RingHom (baseToSections 𝒵 (tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e))) (tg ρ (cE 𝒵 e))
  have hV' := isAffineOpen_V' 𝒵 ρ e hρ
  have hψX : ψ X = tg ρ (cE 𝒵 e) := by simp [ψ]
  have hψH : ψ (1 - C e * X) = tH 𝒵 ρ e := by simp [ψ, tH]
  obtain ⟨N1, P1, h1⟩ := exists_poly_DU 𝒵 ρ e hρ (res le_sup_right c)
  have h1' : res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) c *
      (res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (tg ρ (cE 𝒵 e))) ^ N1 =
      res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (ψ P1) := by
    rw [tg_res_DU, tS2, h1]
    exact (res_eval_DU 𝒵 ρ e P1).symm
  obtain ⟨m1, hm1⟩ := exists_pow_mul_eq_of_res hV' le_sup_right (tg ρ (cE 𝒵 e))
    (basicOpen_tg 𝒵 ρ e) c (ψ P1) N1 h1'
  obtain ⟨N2, P2, h2⟩ := exists_poly_DV 𝒵 ρ e hρ (res le_sup_left c)
  have h2' : res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) c *
      (res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e)) ^ N2 =
      res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (ψ P2) := by
    rw [h2]
    exact (res_eval_DV 𝒵 ρ e P2).symm
  obtain ⟨m2, hm2⟩ := exists_pow_mul_eq_of_res hV' le_sup_left (tH 𝒵 ρ e)
    (basicOpen_tH 𝒵 ρ e) c (ψ P2) N2 h2'
  have hcop : IsCoprime ((X : (Zloc p)[X]) ^ (m1 + N1)) ((1 - C e * X) ^ (m2 + N2)) :=
    (show IsCoprime (X : (Zloc p)[X]) (1 - C e * X) from ⟨C e, 1, by ring⟩).pow
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u * (X ^ m1 * P1) + v * ((1 - C e * X) ^ m2 * P2), ?_⟩
  have e1 : ψ (X ^ m1 * P1) = c * tg ρ (cE 𝒵 e) ^ (m1 + N1) := by
    rw [map_mul, map_pow, hψX, ← hm1]; ring
  have e2 : ψ ((1 - C e * X) ^ m2 * P2) = c * tH 𝒵 ρ e ^ (m2 + N2) := by
    rw [map_mul, map_pow, hψH, ← hm2]; ring
  have e3 := congrArg ψ huv
  rw [map_add, map_mul, map_mul, map_pow, map_pow, hψX, hψH, map_one] at e3
  rw [map_add, map_mul ψ u, map_mul ψ v, e1, e2]
  linear_combination c * e3

theorem injective_g' (hρ : IsP1Coordinate 𝒵 ρ) :
    Function.Injective (eval₂RingHom (baseToSections 𝒵 (tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e)))
      (tg ρ (cE 𝒵 e))) := by
  have hbU := hρ.2.2.1
  let eU := RingEquiv.ofBijective _ hbU
  haveI : IsDomain Γ(𝒵.left, ρ.U) :=
    Function.Injective.isDomain eU.symm.toRingHom eU.symm.injective
  letI : Algebra Γ(𝒵.left, ρ.U) Γ(𝒵.left, tDU ρ (cE 𝒵 e)) := (res (tDU_le ρ (cE 𝒵 e))).toAlgebra
  haveI := hρ.1.isLocalization_of_eq_basicOpen (tF ρ (cE 𝒵 e)) (homOfLE (tDU_le ρ (cE 𝒵 e))) rfl
  have htF0 : tF ρ (cE 𝒵 e) ≠ 0 := by
    intro h0
    have : eval₂RingHom (baseToSections 𝒵 ρ.U) ρ.f (X + C e) = 0 := by
      rw [← h0, tF_eq]; simp
    exact X_add_C_ne_zero e (hbU.1 (this.trans (map_zero _).symm))
  have hresinj : Function.Injective (res (tDU_le ρ (cE 𝒵 e))) :=
    IsLocalization.injective (M := Submonoid.powers (tF ρ (cE 𝒵 e))) Γ(𝒵.left, tDU ρ (cE 𝒵 e))
      (powers_le_nonZeroDivisors_of_noZeroDivisors htF0)
  rw [injective_iff_map_eq_zero]
  intro P hP
  have h1 := congrArg (res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _)) hP
  rw [map_zero, coe_eval₂RingHom, res_eval_DU] at h1
  letI : Invertible (uF ρ (cE 𝒵 e) : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) := Units.invertible _
  set N := P.natDegree
  have h2 : eval₂ (baseToSections 𝒵 (tDU ρ (cE 𝒵 e)))
      (⅟(uF ρ (cE 𝒵 e) : Γ(𝒵.left, tDU ρ (cE 𝒵 e)))) (reflect N (reflect N P)) = 0 := by
    rw [reflect_reflect]; exact h1
  rw [eval₂_reflect_eq_zero_iff _ _ N _ (natDegree_reflect_le.trans (max_self _).le), uF_val]
    at h2
  have h3 : res (tDU_le ρ (cE 𝒵 e))
      (eval₂ (baseToSections 𝒵 ρ.U) (tF ρ (cE 𝒵 e)) (reflect N P)) = 0 := by
    rw [hom_eval₂, show (res _).comp (baseToSections 𝒵 ρ.U) = baseToSections 𝒵 _ from
      RingHom.ext (res_baseToSections 𝒵 _)]
    exact h2
  have h4 := hresinj (h3.trans (map_zero _).symm)
  rw [tF_eq] at h4
  have h5 := (bijective_eval₂_add _ _ e hbU).1
    ((show eval₂RingHom (baseToSections 𝒵 ρ.U) (ρ.f + baseToSections 𝒵 ρ.U e) (reflect N P) = 0
      from h4).trans (map_zero _).symm)
  exact reflect_eq_zero_iff.mp h5

/-- **The translated coordinate is again an isomorphism onto `P¹_{ℤ_(p)}` by charts.** -/
theorem isP1Coordinate_translate (hρ : IsP1Coordinate 𝒵 ρ) :
    IsP1Coordinate 𝒵 (translate ρ (cE 𝒵 e)) := by
  refine ⟨hρ.1, isAffineOpen_V' 𝒵 ρ e hρ, ?_, injective_g' 𝒵 ρ e hρ, surjective_g' 𝒵 ρ e hρ⟩
  show Function.Bijective (eval₂RingHom (baseToSections 𝒵 ρ.U) (tF ρ (cE 𝒵 e)))
  rw [tF_eq]
  exact bijective_eval₂_add _ _ e hρ.2.2.1

theorem val_translate (z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) :
    (translate ρ (cE 𝒵 e)).val z = (ρ.val z).map (fun t => t + iq p e) := by
  by_cases hz : ptOf z ∈ ρ.U
  · rw [val_of_mem (translate ρ (cE 𝒵 e)) z hz, val_of_mem ρ z hz]
    change OnePoint.some (ev z hz (tF ρ (cE 𝒵 e))) = _
    rw [tF_eq, map_add, ev_baseToSections]
    rfl
  · rw [val_of_not_mem (translate ρ (cE 𝒵 e)) z hz, val_of_not_mem ρ z hz]
    rfl

end P1T

/-- **(C2-T) `P1Translate` proved**: translations `t ↦ t + e` (`e ∈ ℤ_(p)`) of `P¹_{ℤ_(p)}` act
on isomorphisms by charts. -/
theorem p1Translate : P1Translate := by
  intro p _ 𝒵 ρ hρ e
  exact ⟨translate ρ (cE 𝒵 e), isP1Coordinate_translate 𝒵 ρ e hρ, val_translate 𝒵 ρ e⟩

/-- **Glue C2 from glue A (finiteness of `fibreAut`) and T5 alone.** -/
theorem coordinateFromSections_of'' (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure) :
    CoordinateFromSections :=
  coordinateFromSections_of' hA hT p1Translate

/-- **Main composite (final form, after (C1c) and (C2-T)): `ModelCoordinateResidue` from the
leaves L1-L6, the textbook leaf T5 and four glue Props of this task**: (A-fix)
`FibreAutFixFinite`, (B-desc) `QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b)
`CMStabInvolution`. -/
theorem modelCoordinateResidue_final2 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure)
    (hfix : FibreAutFixFinite) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hI : CMStabInvolution) : ModelCoordinateResidue :=
  modelCoordinateResidue_final hAF hQE hTS hP1 hFix hCyc hT hfix hD hB hI stabFixesClosure
    p1Translate

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 15: (A-fix) `FibreAutFixFinite` reduced (the fixed locus of `h` is closed)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **Input (A-fix-irr): the moduli curve `Y` is irreducible over `ℚ`.** For a triple with R1fp,
R1hecke, R2fp, the scheme `Y` is irreducible. True for `Y₃`: its two geometric components
(`π₀ = ℤ̂^×/nrd(K₃) ≅ (ℤ/3)^×`) are conjugate over `ℚ(√−3)` (Shimura reciprocity on `π₀`;
locator UNVERIFIED, SPECULATIVE reading as in `NormalizationModel`'s docstring). In this
development it also follows from a normalization chart: `ModelGlue.irreducible_of_chart` proves
`IrreducibleSpace Y.left` from T5 (`TwistClassFinite`) and any `E` with `NormalizationModel Y π E`.
The targets A and C1 have no such `E` among their hypotheses, so the irreducibility enters here as
a separate input (it is not implied by R1fp, R1hecke, R2fp as clause lists without arithmetic). -/
def ModelYIrreducible : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π → IrreducibleSpace Y.left

/-- **Glue (A-fix-dim): a closed subset of an integral relative curve over `ℤ_(p)` that misses the
generic point carries only finitely many `ℚ̄`-points** (dimension theory of curves; no
literature). For `𝒴` integral, proper and smooth of relative dimension 1 over `ℤ_(p)` and `Z ⊆ 𝒴` closed
with `η ∉ Z`, only finitely many `ℚ̄`-points of `𝒴` have their point in `Z`. (Outline: `ℚ̄`-points
lie on the generic fibre `𝒴_ℚ`, an integral curve over `ℚ`; by `_root_.LeafQM.AV.Pin.smoothStalkDimOne` every point of
`Z ∩ 𝒴_ℚ` is closed (a non-closed point `x ≠ η` would give a chain `η ⤳ x ⤳ z` of length 2 below a
closed point `z`), so the closed set `Z ∩ 𝒴_ℚ` of the Noetherian space `𝒴_ℚ` is finite; each closed
point has a residue field finite over `ℚ` (Zariski's lemma), hence finitely many embeddings into
`ℚ̄`.) Properness (only quasi-compactness is used) cannot be dropped: the affine line with
infinitely many doubled points is integral and smooth, and its doubled points form an infinite
closed set missing the generic point. -/
def CurveClosedQbarFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom → ∀ (_ : IsIntegral 𝒴.left) (Z : Set 𝒴.left),
    IsClosed Z → genericPoint 𝒴.left ∉ Z →
    {y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | qbarPoint y ∈ Z}.Finite

/-- **The model is integral, from `CurveBijIso` and the irreducibility of `Y`** (the argument of
`ModelGlue.modelIntegral_of`, with `ModelYIrreducible` in place of the chart). -/
theorem isIntegral_model (hC : CurveBijIso) (hYI : ModelYIrreducible) {p : ℕ} [Fact p.Prime]
    {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))} {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h1 : R1fpProps Y Φ) (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π) : IsIntegral 𝒴.left := by
  obtain ⟨g, -, hbij⟩ := exists_genFib_to_Y hM h1
  haveI : IsIso g := hC (genFib 𝒴) Y (genFib_isProper 𝒴 hM.1) (genFib_smooth 𝒴 hM.2.1)
    h1.1 h1.2.1 g hbij
  haveI : IsIso g.left := (Over.forget _).map_isIso g
  haveI : IrreducibleSpace Y.left := hYI Y Φ π h1 hh h2
  haveI : IrreducibleSpace (genFib 𝒴).left := by
    rw [irreducibleSpace_def]
    show IsIrreducible (Set.univ : Set (genFib 𝒴).left)
    have hsurj : Function.Surjective (inv g.left) := fun s =>
      ⟨g.left s, by rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl⟩
    rw [← Set.range_eq_univ.2 hsurj, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (inv g.left).continuous.continuousOn
  haveI : SmoothOfRelativeDimension 1 𝒴.hom := hM.2.1
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  haveI : IsReduced 𝒴.left := isReduced_of_smooth_zloc 𝒴
  haveI : IrreducibleSpace 𝒴.left := irreducibleSpace_of_genFib 𝒴
  exact isIntegral_of_irreducibleSpace_of_isReduced 𝒴.left

/-- **An automorphism over `S` of an integral separated `S`-scheme whose fixed locus contains the
generic point is the identity** (the fixed locus is a closed subscheme; a surjective closed
immersion into a reduced scheme is an isomorphism). -/
theorem eq_one_of_genericPoint_fixed {S : Scheme.{0}} (X : Over S) [IsSeparated X.hom]
    [IsIntegral X.left] (h : Aut X.left) (hh : h.asIso.hom ≫ X.hom = X.hom)
    (hη : genericPoint X.left ∈ Set.range (equalizer.ι (Over.homMk h.asIso.hom hh : X ⟶ X)
      (𝟙 X)).left) : h = 1 := by
  let f : X ⟶ X := Over.homMk h.asIso.hom hh
  let ι := (equalizer.ι f (𝟙 X)).left
  have hι : ι ≫ h.asIso.hom = ι := by
    have := congrArg CommaMorphism.left (equalizer.condition f (𝟙 X))
    simpa [f, ι] using this
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hsurj : Function.Surjective ι := by
    intro x
    have hcl' : closure ({genericPoint X.left} : Set X.left) = Set.univ := (genericPoint_spec _).def
    have hx : x ∈ closure ({genericPoint X.left} : Set X.left) := by rw [hcl']; trivial
    exact closure_minimal (Set.singleton_subset_iff.2 hη) hcl hx
  haveI : Surjective ι := ⟨hsurj⟩
  haveI := isIso_of_isClosedImmersion_of_surjective ι
  have h1 : h.asIso.hom = 𝟙 _ := by rw [← cancel_epi ι, hι, Category.comp_id]
  exact Aut.ext (Iso.ext h1)

/-- **(A-fix) reduced: `FibreAutFixFinite` from `CurveBijIso` (model-glue's textbook leaf),
`ModelYIrreducible` and `CurveClosedQbarFinite`.** If `h ≠ 1` fixed infinitely many `ℚ̄`-points,
the closed fixed locus of `h` would contain the generic point of the integral `𝒴`
(`CurveClosedQbarFinite`), so `h = 1` (`eq_one_of_genericPoint_fixed`). -/
theorem fibreAutFixFinite_of (hC : CurveBijIso) (hYI : ModelYIrreducible)
    (hF : CurveClosedQbarFinite) : FibreAutFixFinite := by
  intro p _ hp 𝒴 𝒜 hM Y Φ π h1 hh h2 h hmem hne
  haveI : IsIntegral 𝒴.left := isIntegral_model hC hYI hM h1 hh h2
  haveI := hM.1
  have hh' := fibreAut_over 𝒴 𝒜 h hmem
  by_contra hinf
  apply hne
  refine eq_one_of_genericPoint_fixed 𝒴 h hh' ?_
  let f : 𝒴 ⟶ 𝒴 := Over.homMk h.asIso.hom hh'
  let ι := (equalizer.ι f (𝟙 𝒴)).left
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hfix : ∀ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, y ≫ h.asIso.hom = y →
      qbarPoint y ∈ Set.range ι := by
    intro y hy
    let y' : Over.mk (y ≫ 𝒴.hom) ⟶ 𝒴 := Over.homMk y rfl
    have hc : y' ≫ f = y' ≫ 𝟙 𝒴 := by
      ext1; simpa [f, y'] using hy
    refine ⟨(equalizer.lift y' hc).left (IsLocalRing.closedPoint Qbar), ?_⟩
    show ((equalizer.lift y' hc).left ≫ (equalizer.ι f (𝟙 𝒴)).left) _ = _
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  by_contra hη
  exact hinf ((hF p 𝒴 hM.1 hM.2.1 inferInstance _ hcl hη).subset (fun y hy => hfix y hy))

/-- **Glue A from T5, `CurveBijIso`, `ModelYIrreducible`, `CurveClosedQbarFinite`.** -/
theorem fibreAutTame_of'' (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hYI : ModelYIrreducible) (hF : CurveClosedQbarFinite) : FibreAutTame :=
  fibreAutTame_of' hT (fibreAutFixFinite_of hC hYI hF)

/-- **Main composite (after part 15): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the input `ModelYIrreducible`, and the glue (A-fix-dim)
`CurveClosedQbarFinite`, (B-desc) `QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b)
`CMStabInvolution`.** -/
theorem modelCoordinateResidue_final3 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hYI : ModelYIrreducible) (hF : CurveClosedQbarFinite) (hD : QuotientDescendsQ)
    (hB : ToP1BijIsCoordinateQ) (hI : CMStabInvolution) : ModelCoordinateResidue :=
  modelCoordinateResidue_final2 hAF hQE hTS hP1 hFix hCyc hT (fibreAutFixFinite_of hC hYI hF) hD hB
    hI

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 16: (A-fix-dim) `CurveClosedQbarFinite` proved (dimension theory of curves)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **A closed point of a `ℚ`-scheme locally of finite type has a residue field finite over `ℚ`**
(Zariski's lemma, Mathlib's `finite_of_finite_type_of_isJacobsonRing`, through the closed immersion
`Spec κ(x) → X`). The `ℚ`-algebra structure is the one from the structure map. -/
theorem finite_residueField_of_isClosed (X : Over (Spec (CommRingCat.of ℚ)))
    [LocallyOfFiniteType X.hom] (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    ∃ ψ : ℚ →+* X.left.residueField x,
      @Module.Finite ℚ (X.left.residueField x) _ _ ψ.toAlgebra.toModule := by
  haveI := isClosed_singleton_iff_isClosedImmersion.mp hx
  have hft : LocallyOfFiniteType (X.left.fromSpecResidueField x ≫ X.hom) := inferInstance
  set ψ := Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom) with hψ
  rw [← Spec.map_preimage (X.left.fromSpecResidueField x ≫ X.hom), ← hψ,
    HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  letI : Algebra ℚ (X.left.residueField x) := ψ.hom.toAlgebra
  haveI : Algebra.FiniteType ℚ (X.left.residueField x) := hft
  exact ⟨ψ.hom, finite_of_finite_type_of_isJacobsonRing ℚ (X.left.residueField x)⟩

/-- **Finitely many `ℚ̄`-points over a closed point** of a `ℚ`-scheme locally of finite type. -/
theorem finite_qbarPts_over_closed (X : Over (Spec (CommRingCat.of ℚ)))
    [LocallyOfFiniteType X.hom] (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    {y : Spec (CommRingCat.of Qbar) ⟶ X.left | ptOf y = x}.Finite := by
  obtain ⟨ψ, hfin⟩ := finite_residueField_of_isClosed X x hx
  letI : Algebra ℚ (X.left.residueField x) := ψ.toAlgebra
  haveI : Module.Finite ℚ (X.left.residueField x) := hfin
  haveI : Finite (X.left.residueField x →ₐ[ℚ] Qbar) := inferInstance
  haveI : Finite (X.left.residueField x →+* Qbar) :=
    Finite.of_equiv _ (RingHom.equivRatAlgHom (R := X.left.residueField x) (S := Qbar)).symm
  haveI : Finite (X.left.residueField x ⟶ CommRingCat.of Qbar) :=
    Finite.of_injective (fun φ : X.left.residueField x ⟶ CommRingCat.of Qbar => φ.hom)
      (fun _ _ h => CommRingCat.hom_ext h)
  refine (Set.finite_range (fun φ : X.left.residueField x ⟶ CommRingCat.of Qbar =>
    (Scheme.SpecToEquivOfField Qbar X.left).symm ⟨x, φ⟩)).subset ?_
  intro y hy
  obtain ⟨⟨x', φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Qbar X.left).symm.surjective y
  have hx' : x' = x := by
    have := hy
    simp only [Set.mem_setOf_eq, ptOf, Equiv.apply_symm_apply] at this
    exact this
  subst hx'
  exact ⟨φ, rfl⟩

/-- In a quasi-sober Noetherian space, a closed set all of whose points are closed is finite. -/
theorem finite_of_isClosed_of_closedPoints {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] [QuasiSober α] {s : Set α} (hs : IsClosed s)
    (hpts : ∀ x ∈ s, IsClosed ({x} : Set α)) : s.Finite := by
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine Set.Finite.sUnion hSf (fun t ht => ?_)
  have hg := (hSirr t ht).isGenericPoint_genericPoint_closure
  rw [(hScl t ht).closure_eq] at hg
  have hcl := hpts _ (Set.mem_sUnion.2 ⟨t, ht, hg.mem⟩)
  refine (Set.finite_singleton (hSirr t ht).genericPoint).subset ?_
  intro x hxt
  rw [← hcl.closure_eq, hg.def]
  exact hxt

/-- **(A-fix-dim) `CurveClosedQbarFinite` proved.** Every point of `Z` over the generic fibre is
closed there (`_root_.LeafQM.AV.Pin.smoothStalkDimOne`: a non-closed point would give a chain of length 2 below a
closed point), so `Z ∩ 𝒴_ℚ` is finite (Noetherian, quasi-sober), and each closed point carries
finitely many `ℚ̄`-points (`finite_qbarPts_over_closed`). -/
theorem curveClosedQbarFinite : CurveClosedQbarFinite := by
  intro p _ 𝒴 hP hS hI Z hZ hη
  haveI := hP
  haveI := hS
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  haveI := isOpenImmersion_specRatToZloc p
  set G := genFib 𝒴 with hG
  set j : G.left ⟶ 𝒴.left := pullback.fst 𝒴.hom (specRatToZloc p) with hj
  haveI : IsOpenImmersion j :=
    MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ (isOpenImmersion_specRatToZloc p)
  haveI : IsProper G.hom := genFib_isProper 𝒴 hP
  haveI hGs : SmoothOfRelativeDimension 1 G.hom := genFib_smooth 𝒴 hS
  haveI : Smooth G.hom := SmoothOfRelativeDimension.smooth 1 G.hom
  haveI : LocallyOfFiniteType G.hom := inferInstance
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  set Z' : Set G.left := j ⁻¹' Z with hZ'
  have hZ'cl : IsClosed Z' := hZ.preimage j.continuous
  obtain ⟨w, hw⟩ : ∃ w : G.left, j w = genericPoint 𝒴.left := genericPoint_mem_range 𝒴
  -- every point of `Z'` is closed in `G`
  have hpts : ∀ x ∈ Z', IsClosed ({x} : Set G.left) := by
    intro x hx
    obtain ⟨z, hzc, hzc'⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty x |>.mono
      subset_closure) isClosed_closure.isLocallyClosed
    have hz1 : IsClosed ({z} : Set G.left) := mem_closedPoints_iff.mp hzc'
    have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hzc
    have hwx : w ⤳ x := by
      rw [← j.isOpenEmbedding.isInducing.specializes_iff, hw]
      exact (genericPoint_spec 𝒴.left).specializes trivial
    have hwx' : w ≠ x := by
      intro h
      apply hη
      rw [← hw, h]
      exact hx
    by_contra hxc
    have hzx : z ≠ x := by
      intro h; subst h; exact hxc hz1
    have hd := _root_.LeafQM.AV.Pin.smoothStalkDimOne ℚ G.left G.hom hGs z hz1
    rw [ringKrullDim_stalk_eq_coheight] at hd
    have h1 : z < x := lt_of_le_not_ge hxz (fun h => hzx (Specializes.antisymm h hxz).eq)
    have h2 : x < w := lt_of_le_not_ge hwx (fun h => hwx' (Specializes.antisymm h hwx).eq.symm)
    have c1 := Order.coheight_add_one_le h1
    have c2 := Order.coheight_add_one_le h2
    have hd' : Order.coheight z = 1 := by exact_mod_cast hd
    have : (2 : ℕ∞) ≤ Order.coheight z := by
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ Order.coheight w + 1 + 1 := add_le_add (add_le_add zero_le le_rfl) le_rfl
        _ ≤ Order.coheight x + 1 := add_le_add c2 le_rfl
        _ ≤ Order.coheight z := c1
    rw [hd'] at this
    exact absurd this (by decide)
  have hfin : Z'.Finite := finite_of_isClosed_of_closedPoints hZ'cl hpts
  have hfin2 : {y' : Spec (CommRingCat.of Qbar) ⟶ G.left | ptOf y' ∈ Z'}.Finite := by
    refine (hfin.biUnion (fun x hx => finite_qbarPts_over_closed G x (hpts x hx))).subset ?_
    intro y' hy'
    exact Set.mem_biUnion hy' rfl
  refine (hfin2.image (fun y' => y' ≫ j)).subset ?_
  intro y hy
  obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
  let s' : Spec (CommRingCat.of Qbar) ⟶ G.left := s.left
  have hs' : s' ≫ j = y := hs
  refine ⟨s', ?_, hs'⟩
  show j (ptOf s') ∈ Z
  have hpt : qbarPoint (s' ≫ j) = j (ptOf s') := by
    unfold qbarPoint
    rw [specToEquivOfField_comp_right]
  rw [← hpt, hs']
  exact hy

/-- **(A-fix) from `CurveBijIso` and `ModelYIrreducible` alone.** -/
theorem fibreAutFixFinite_of' (hC : CurveBijIso) (hYI : ModelYIrreducible) : FibreAutFixFinite :=
  fibreAutFixFinite_of hC hYI curveClosedQbarFinite

/-- **Main composite (after part 16): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the input `ModelYIrreducible`, and the glue (B-desc)
`QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b) `CMStabInvolution`.** -/
theorem modelCoordinateResidue_final4 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hYI : ModelYIrreducible) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hI : CMStabInvolution) : ModelCoordinateResidue :=
  modelCoordinateResidue_final3 hAF hQE hTS hP1 hFix hCyc hT hC hYI curveClosedQbarFinite hD hB hI

/-- **`ModelYIrreducible` from the decomposition's glue `CoverModelOfHeckeN` and T5** (the
normalization chart of `CoverModelN` and model-glue's `irreducible_of_chart`). -/
theorem modelYIrreducible_of_coverModelN (hT : ObjBridge.TorsionStructure)
    (hCov : CoverModelOfHeckeN) : ModelYIrreducible := by
  intro Y Φ π h1 hh h2
  obtain ⟨E, i1, i2, i3, i4, i5, i6, hN, -, -⟩ := hCov Y Φ π h1 hh h2
  exact irreducible_of_chart (twistClassFinite hT) h1 h2 E hN

/-- **Main composite (after part 16, chart form): `ModelCoordinateResidue` from the leaves L1-L6,
the textbook leaves T5 and `CurveBijIso`, the decomposition's glue `CoverModelOfHeckeN`, and the
glue (B-desc) `QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b) `CMStabInvolution`.** -/
theorem modelCoordinateResidue_final5 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hCov : CoverModelOfHeckeN) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hI : CMStabInvolution) : ModelCoordinateResidue :=
  modelCoordinateResidue_final4 hAF hQE hTS hP1 hFix hCyc hT hC
    (modelYIrreducible_of_coverModelN hT hCov) hD hB hI

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 17: (C1b) `CMStabInvolution` reduced to a statement on QM objects over `ℚ̄`
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **Glue (C1b-obj): a CM object is fixed by a Hecke operation of order exactly 2 on classes**
(QM with CM; the elliptic points of `Y₃ → P¹` have stabilizers of even order `4, 6, 2` in the
group of Hecke operations on classes, `CoverBranchData`/`nY3`, Baba–Granath §3.1 (locator
UNVERIFIED)). For a level-3 object `P` over `ℚ̄` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]`, some
operation `T = twist α ∘ rightMul u` on `M3 ℚ̄` fixes the class of `P`, is an involution, and is not
the identity. (Outline: for `ℤ[i]` take `α = id` and `u ≡ φ` on `A[3]` (`Level3.torsor`,
`exists_unit_congr`); then `u² ≡ −1`, and `−1` acts trivially on classes. For `ℤ[ζ₃]` and
`ℤ[√−6]` the involution is an Atkin–Lehner-type twist induced by an element of the normalizer of
`ι(𝒪)` in `End A` (for `ℤ[√−6]`: `ι(ij)⁻¹ φ`), which needs the structure of `End A` at CM points.) -/
def CMStabObj : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    ∃ (α : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ),
      M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
      (∀ m : M3 Qbar, M3.twist α (M3.rightMul u (M3.twist α (M3.rightMul u m))) = m) ∧
      ∃ m : M3 Qbar, M3.twist α (M3.rightMul u m) ≠ m

/-- **An automorphism over `ℤ_(p)` of the smooth model fixing every `ℚ̄`-point is the identity**
(given `CurveBijIso` and `ModelYIrreducible`; through `FibreAutFixFinite` and the infinitely many
`ℚ̄`-points). -/
theorem eq_one_of_fixes_all (hC : CurveBijIso) (hYI : ModelYIrreducible) {p : ℕ} [Fact p.Prime]
    (hp : 324 < p) {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))} {𝒜 : QMFamily 𝒴.left}
    (hM : IsShimuraModel p 𝒴 𝒜) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h1 : R1fpProps Y Φ) (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π)
    (g : Aut 𝒴.left) (hg : g ∈ fibreAut 𝒴 𝒜)
    (hfix : ∀ z : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, z ≫ g.asIso.hom = z) : g = 1 := by
  by_contra hne
  have hfin := fibreAutFixFinite_of' hC hYI p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 g hg hne
  apply infinite_qbarPoints (π := π) hM h1
  refine hfin.subset ?_
  intro z _
  exact hfix z

/-- **(C1b) reduced: `CMStabInvolution` from `CurveBijIso`, `ModelYIrreducible` and the
object-level glue `CMStabObj`.** The Hecke automorphisms `g_α`, `g_u` of `IsShimuraModel` lie in
`fibreAut` (`hecke_mem_fibreAut`); `ι = g_α ∘ g_u` acts on classes as `T`. It fixes `y` (moduli
injectivity), `ι²` fixes every `ℚ̄`-point (`T² = id`), hence `ι² = 1` (`eq_one_of_fixes_all`), and
`ι ≠ 1` because `T` moves the class of some object, which is the fibre at some `ℚ̄`-point. -/
theorem cMStabInvolution_of (hC : CurveBijIso) (hYI : ModelYIrreducible) (hO : CMStabObj) :
    CMStabInvolution := by
  intro p _ hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y P hP hCM
  obtain ⟨α, u, hfixP, hinv, m0, hm0⟩ := hO P hCM
  obtain ⟨htw, hru⟩ := hecke_mem_fibreAut hM
  obtain ⟨ga, hgaG, hga⟩ := htw α
  obtain ⟨gu, hguG, hgu⟩ := hru u
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  set ι : Aut 𝒴.left := ga * gu with hιdef
  have hιG : ι ∈ fibreAut 𝒴 𝒜 := Subgroup.mul_mem _ hgaG hguG
  have hιhom : ι.asIso.hom = gu.asIso.hom ≫ ga.asIso.hom := rfl
  have hact : ∀ (z : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (Q Q' : QML3 Qbar), IsFibreOf 𝒜 z Q →
      IsFibreOf 𝒜 (z ≫ ι.asIso.hom) Q' →
        M3.mk Q' = M3.twist α (M3.rightMul u (M3.mk Q)) := by
    intro z Q Q' hQ hQ'
    obtain ⟨Q1, hQ1⟩ := hM.2.2.1 Qbar (z ≫ gu.asIso.hom)
    have e1 := hgu z Q Q1 hQ hQ1
    rw [hιhom, ← Category.assoc] at hQ'
    have e2 := hga _ Q1 Q' hQ1 hQ'
    rw [e2, e1]
  have hfix2 : ∀ z : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, z ≫ (ι * ι).asIso.hom = z := by
    intro z
    obtain ⟨Q, hQ⟩ := hM.2.2.1 Qbar z
    obtain ⟨Q1, hQ1⟩ := hM.2.2.1 Qbar (z ≫ ι.asIso.hom)
    obtain ⟨Q2, hQ2⟩ := hM.2.2.1 Qbar ((z ≫ ι.asIso.hom) ≫ ι.asIso.hom)
    have e1 := hact z Q Q1 hQ hQ1
    have e2 := hact _ Q1 Q2 hQ1 hQ2
    have e3 : M3.mk Q2 = M3.mk Q := by rw [e2, e1, hinv]
    have := hM.2.2.2.1 _ z Q2 Q hQ2 hQ e3
    show z ≫ (ι.asIso.hom ≫ ι.asIso.hom) = z
    rw [← Category.assoc]
    exact this
  refine ⟨ι, hιG, ?_, ?_, ?_⟩
  · intro hι1
    obtain ⟨Q, rfl⟩ : ∃ Q : QML3 Qbar, M3.mk Q = m0 := Quotient.exists_rep m0
    obtain ⟨z, hz⟩ := hM.2.2.2.2.1 Q
    obtain ⟨Q1, hQ1⟩ := hM.2.2.1 Qbar (z ≫ ι.asIso.hom)
    have e1 := hact z Q Q1 hz hQ1
    have hz1 : z ≫ ι.asIso.hom = z := by rw [hι1]; simp
    rw [hz1] at hQ1
    apply hm0
    have e2 := huniq z Q1 Q hQ1 hz
    rw [← e1]
    exact e2
  · exact eq_one_of_fixes_all hC hYI hp hM h1 hh h2 _ (Subgroup.mul_mem _ hιG hιG) hfix2
  · obtain ⟨P1, hP1⟩ := hM.2.2.1 Qbar (y ≫ ι.asIso.hom)
    have e := hact y P P1 hP hP1
    rw [hfixP] at e
    exact hM.2.2.2.1 _ y P1 P hP1 hP e

/-- **Main composite (after part 17): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the decomposition's glue `CoverModelOfHeckeN`, and the glue (B-desc)
`QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b-obj) `CMStabObj`.** -/
theorem modelCoordinateResidue_final6 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hCov : CoverModelOfHeckeN) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hO : CMStabObj) : ModelCoordinateResidue :=
  modelCoordinateResidue_final5 hAF hQE hTS hP1 hFix hCyc hT hC hCov hD hB
    (cMStabInvolution_of hC (modelYIrreducible_of_coverModelN hT hCov) hO)

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 18: (B-desc) split; the lifting of `ℚ̄`-points through the quotient, proved
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **An SGA 1 quotient by a finite group is surjective** (lying over for the integral extension
`Γ(W) = Γ(q⁻¹W)^G ⊆ Γ(q⁻¹W)`: Mathlib's `Algebra.IsInvariant.isIntegral` and
`Ideal.exists_ideal_over_prime_of_isIntegral`). -/
theorem isGQuotient_surjective {X Z : Scheme.{0}} (G : Subgroup (Aut X)) (q : X ⟶ Z)
    (hfin : Finite G) (hq : IsGQuotient G q) : Function.Surjective q := by
  intro z
  obtain ⟨hinv, haff, hsec⟩ := hq
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hzW, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  set U := q ⁻¹ᵁ W with hUdef
  have hU : IsAffineOpen U := hW.preimage q
  letI : MulSemiringAction G Γ(X, U) := secAction hinv W
  letI : Algebra Γ(Z, W) Γ(X, U) := (q.app W).hom.toAlgebra
  haveI : SMulCommClass G Γ(Z, W) Γ(X, U) := by
    constructor
    intro g a b
    change secMap _ _ W (q.app W a * b) = q.app W a * secMap _ _ W b
    rw [map_mul, secMap_app]
  haveI : Algebra.IsInvariant Γ(Z, W) Γ(X, U) G := by
    constructor
    intro b hb
    have hmem : b ∈ Set.range (q.app W) := by
      rw [(hsec W hW).2]
      intro g hg
      have := hb ⟨g⁻¹, G.inv_mem hg⟩
      change secMap _ _ W b = b at this
      rw [secMap_congr (f' := g.asIso.hom) (by simp) _ (hinv g hg)] at this
      exact this
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha⟩
  haveI : Algebra.IsIntegral Γ(Z, W) Γ(X, U) := Algebra.IsInvariant.isIntegral Γ(Z, W) Γ(X, U) G
  set P := (hW.primeIdealOf ⟨z, hzW⟩).asIdeal with hPdef
  haveI : P.IsPrime := (hW.primeIdealOf ⟨z, hzW⟩).isPrime
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal Γ(X, U))
    (by
      intro a ha
      have h0 : q.app W a = 0 := Ideal.mem_bot.mp (Ideal.mem_comap.mp ha)
      rw [(hsec W hW).1 (h0.trans (map_zero _).symm)]
      exact P.zero_mem)
  obtain ⟨y, hy⟩ : ∃ y : Spec Γ(X, U), y.asIdeal = Q := ⟨⟨Q, hQ⟩, rfl⟩
  refine ⟨hU.fromSpec y, ?_⟩
  have h1 : Spec.map (q.appLE W U le_rfl) y = hW.primeIdealOf ⟨z, hzW⟩ := by
    apply PrimeSpectrum.ext
    change Ideal.comap (q.appLE W U le_rfl).hom y.asIdeal = P
    rw [← Scheme.Hom.app_eq_appLE, hy]
    exact hQP
  rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.SpecMap_appLE_fromSpec q hW hU le_rfl,
    Scheme.Hom.comp_apply, h1, IsAffineOpen.fromSpec_primeIdealOf]

/-- **`ℚ̄`-points lift through a finite SGA 1 quotient by a finite group**: the fibre
`X ×_Z Spec ℚ̄` is finite over `Spec ℚ̄` and nonempty (surjectivity), so it has a closed point,
which is a `ℚ̄`-point (Mathlib's `pointOfClosedPoint`). -/
theorem exists_lift_qbar {X Z : Scheme.{0}} (G : Subgroup (Aut X)) (q : X ⟶ Z) (hfin : Finite G)
    (hq : IsGQuotient G q) [IsFinite q] (t₀ : Spec (CommRingCat.of Qbar) ⟶ Z) :
    ∃ y₀ : Spec (CommRingCat.of Qbar) ⟶ X, y₀ ≫ q = t₀ := by
  have hsurj := isGQuotient_surjective G q hfin hq
  let f : pullback q t₀ ⟶ Spec (CommRingCat.of Qbar) := pullback.snd q t₀
  haveI : IsFinite f := inferInstance
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace (pullback q t₀ : Scheme.{0}) := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx⟩ := hsurj (t₀ (IsLocalRing.closedPoint Qbar))
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := t₀) x
    (IsLocalRing.closedPoint Qbar) hx
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (⟨w, Set.mem_univ _⟩ :
    (Set.univ : Set (pullback q t₀ : Scheme.{0})).Nonempty) isOpen_univ.isLocallyClosed
  have hcl : IsClosed ({c} : Set (pullback q t₀ : Scheme.{0})) := mem_closedPoints_iff.mp hc
  refine ⟨pointOfClosedPoint f c hcl ≫ pullback.fst q t₀, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (pointOfClosedPoint f c hcl ≫ f) ≫ t₀ = t₀
  rw [pointOfClosedPoint_comp, Category.id_comp]

/-- **Glue (B-desc-map): an orbit-invariant coordinate on `𝒴_ℚ` descends to the quotient** (the
descent half of `QuotientDescendsQ`; SGA 1 Exp. V §1, locators UNVERIFIED). Same hypotheses as
`QuotientDescendsQ`; conclusion: some `σ' : 𝒵_ℚ → P¹` with `σ' ∘ q = σ` on `ℚ̄`-points. (Outline:
`𝒵_ℚ = 𝒴_ℚ/G` since invariants commute with the localization `ℤ_(p) → ℚ`; `σ` is `G`-invariant as
a morphism, its values on the dense set of `ℚ̄`-points of the reduced `𝒴_ℚ` being invariant; the
`G`-stable saturated opens `σ⁻¹(t ≠ ∞)`, `σ⁻¹(t ≠ 0)` have open images (`q` closed and surjective),
and `f, g` are invariant sections, i.e. sections on `𝒵_ℚ`.) -/
def QuotientDescendsMapQ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵)
    (G : Subgroup (Aut 𝒴.left)), IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    Finite G → (∀ g ∈ G, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) →
    IsGQuotient G q.left → IsFinite q.left →
    ∀ σ : ToP1 (genFib 𝒴).left,
      (∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (g : Aut 𝒴.left), g ∈ G →
        s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
          s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) ≫ g.asIso.hom →
        σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left) →
    ∃ σ' : ToP1 (genFib 𝒵).left,
      ∀ s : fieldPt Qbar ⟶ genFib 𝒴,
        σ'.val (K := Qbar) (s ≫ genFibMap q).left = σ.val (K := Qbar) s.left

/-- **(B-desc) from its descent half**: the lifting half is proved (`exists_lift_qbar`). -/
theorem quotientDescendsQ_of (hDm : QuotientDescendsMapQ) : QuotientDescendsQ := by
  intro p _ 𝒴 𝒵 q G hP hS hfin hover hq hqf σ hσ
  obtain ⟨σ', hσ'⟩ := hDm p 𝒴 𝒵 q G hP hS hfin hover hq hqf σ hσ
  refine ⟨σ', hσ', fun t => ?_⟩
  haveI := hqf
  obtain ⟨y₀, hy₀⟩ := exists_lift_qbar G q.left hfin hq
    (t.left ≫ pullback.fst 𝒵.hom (specRatToZloc p))
  obtain ⟨s, hs⟩ := genFib_pt 𝒴 y₀
  refine ⟨s, genFib_pt_inj 𝒵 _ _ ?_⟩
  refine ((Category.assoc _ _ _).trans ((congrArg (s.left ≫ ·) (genFibMap_fst q)).trans
    (Category.assoc _ _ _).symm)).trans ?_
  rw [hs]
  exact hy₀

/-- **Main composite (after part 18): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the decomposition's glue `CoverModelOfHeckeN`, and the glue
(B-desc-map) `QuotientDescendsMapQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b-obj) `CMStabObj`.** -/
theorem modelCoordinateResidue_final7 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hCov : CoverModelOfHeckeN) (hDm : QuotientDescendsMapQ) (hB : ToP1BijIsCoordinateQ)
    (hO : CMStabObj) : ModelCoordinateResidue :=
  modelCoordinateResidue_final6 hAF hQE hTS hP1 hFix hCyc hT hC hCov (quotientDescendsQ_of hDm) hB
    hO

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 19: descent of invariant sections through an SGA 1 quotient (any open)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

section Descent

variable {X Z : Scheme.{0}} {G : Subgroup (Aut X)} {q : X ⟶ Z}

/-- Restriction commutes with pulling back sections along `q`. -/
theorem app_map_eq {W W' : Z.Opens} (h : W ≤ W') (t : Γ(Z, W')) :
    q.app W (Z.presheaf.map (homOfLE h).op t) =
      X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ W' from fun _ hx => h hx)).op (q.app W' t) := by
  have n := ConcreteCategory.congr_hom (q.naturality (homOfLE h).op) t
  simp only [ConcreteCategory.comp_apply] at n
  exact n

/-- `secMap` commutes with restriction. -/
theorem secMap_map (f : X ⟶ X) (hf : f ≫ q = q) {W W' : Z.Opens} (h : W ≤ W')
    (s : Γ(X, q ⁻¹ᵁ W')) :
    secMap f hf W (X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ W' from fun _ hx => h hx)).op s) =
      X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ W' from fun _ hx => h hx)).op (secMap f hf W' s) := by
  simp only [secMap]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- **Pulling back sections along an SGA 1 quotient is injective over every open.** -/
theorem app_injective_of_isGQuotient (hq : IsGQuotient G q) (W' : Z.Opens) :
    Function.Injective (q.app W') := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  apply TopCat.Presheaf.section_ext Z.sheaf W'
  intro z hz
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWW'⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hz W'.isOpen
  have hle : W ≤ W' := hWW'
  have n := app_map_eq (q := q) hle t
  rw [ht, map_zero] at n
  have h0 : Z.presheaf.map (homOfLE hle).op t = 0 :=
    (hq.2.2 W hW).1 (n.trans (map_zero _).symm)
  have e := Z.presheaf.germ_res_apply (homOfLE hle) z hzW t
  rw [h0, map_zero] at e
  change Z.presheaf.germ W' z hz t = Z.presheaf.germ W' z hz 0
  rw [← e, map_zero]

/-- **Invariant sections over any open descend through an SGA 1 quotient** (glue over an affine
cover from the affine case, which is the definition of `IsGQuotient`). -/
theorem exists_descend_section (hq : IsGQuotient G q) (W' : Z.Opens) (s : Γ(X, q ⁻¹ᵁ W'))
    (hs : ∀ (g : Aut X) (hg : g ∈ G), secMap g.asIso.hom (hq.1 g hg) W' s = s) :
    ∃ t : Γ(Z, W'), q.app W' t = s := by
  have key : ∀ z : W', ∃ W : Z.Opens, IsAffineOpen W ∧ z.1 ∈ W ∧ W ≤ W' := by
    intro z
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWW'⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open z.2 W'.isOpen
    exact ⟨W, hW, hzW, hWW'⟩
  choose Wf hWf hzWf hWfle using key
  have hloc : ∀ z : W', ∃ tz : Γ(Z, Wf z), q.app (Wf z) tz =
      X.presheaf.map (homOfLE (show q ⁻¹ᵁ Wf z ≤ q ⁻¹ᵁ W' from fun _ hx => hWfle z hx)).op s := by
    intro z
    have hr := (hq.2.2 (Wf z) (hWf z)).2
    have hmem : X.presheaf.map (homOfLE (show q ⁻¹ᵁ Wf z ≤ q ⁻¹ᵁ W' from
        fun _ hx => hWfle z hx)).op s ∈ Set.range (q.app (Wf z)) := by
      rw [hr]
      intro g hg
      have := secMap_map (q := q) g.asIso.hom (hq.1 g hg) (hWfle z) s
      change secMap g.asIso.hom (hq.1 g hg) (Wf z) _ = _
      rw [secMap_congr rfl _ (hq.1 g hg), this, hs g hg]
    obtain ⟨tz, htz⟩ := hmem
    exact ⟨tz, htz⟩
  choose tz htz using hloc
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 Wf tz := by
    intro i j
    apply app_injective_of_isGQuotient hq (Wf i ⊓ Wf j)
    change q.app _ (Z.presheaf.map (homOfLE inf_le_left).op (tz i)) =
      q.app _ (Z.presheaf.map (homOfLE inf_le_right).op (tz j))
    rw [app_map_eq, app_map_eq, htz i, htz j, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨t0, ht, -⟩ := Z.sheaf.existsUnique_gluing' Wf W' (fun i => homOfLE (hWfle i))
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzWf ⟨z, hz⟩⟩) tz hcompat
  let t : Γ(Z, W') := t0
  have ht' : ∀ z : W', Z.presheaf.map (homOfLE (hWfle z)).op t = tz z := ht
  refine ⟨t, ?_⟩
  apply TopCat.Presheaf.section_ext X.sheaf (q ⁻¹ᵁ W')
  intro x hx
  let z : W' := ⟨q x, hx⟩
  have hxz : x ∈ q ⁻¹ᵁ Wf z := hzWf z
  have hle' : q ⁻¹ᵁ Wf z ≤ q ⁻¹ᵁ W' := fun _ hy => hWfle z hy
  change X.presheaf.germ _ x hx (q.app W' t) = X.presheaf.germ _ x hx s
  rw [← X.presheaf.germ_res_apply (homOfLE hle') x hxz (q.app W' t),
    ← X.presheaf.germ_res_apply (homOfLE hle') x hxz s]
  have e1 : X.presheaf.map (homOfLE hle').op (q.app W' t) =
      q.app (Wf z) (Z.presheaf.map (homOfLE (hWfle z)).op t) := (app_map_eq (hWfle z) t).symm
  rw [e1, ht' z, htz z]

end Descent

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 20: descent of a `G`-invariant map to `P¹` (on an open) through an SGA 1 quotient
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

/-- A map to `P¹` by charts defined on the open `O` (the charts `U, V` cover `O`). -/
structure ToP1In (X : Scheme.{0}) (O : X.Opens) where
  U : X.Opens
  V : X.Opens
  cover : U ⊔ V = O
  f : Γ(X, U)
  g : Γ(X, V)
  inv : X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op f *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op g = 1
  basicOpen_f : X.basicOpen f = U ⊓ V
  basicOpen_g : X.basicOpen g = U ⊓ V

section DescentP1

variable {X Z : Scheme.{0}} {G : Subgroup (Aut X)} {q : X ⟶ Z}

/-- The image of a `G`-stable open under a closed quotient map, as an open. -/
def imgOpen (q : X ⟶ Z) [UniversallyClosed q] (U : X.Opens) : Z.Opens :=
  ⟨(q '' (U : Set X)ᶜ)ᶜ, (q.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩

theorem preimage_imgOpen [UniversallyClosed q] (hq : IsGQuotient G q) (hfin : Finite G)
    (U : X.Opens) (hU : ∀ g ∈ G, ∀ x, g.asIso.hom x ∈ U ↔ x ∈ U) : q ⁻¹ᵁ imgOpen q U = U := by
  ext x
  change q x ∈ (q '' (U : Set X)ᶜ)ᶜ ↔ x ∈ U
  constructor
  · intro h
    by_contra hx
    exact h ⟨x, hx, rfl⟩
  · rintro hx ⟨x', hx', hqx⟩
    obtain ⟨g, hg, hgx⟩ := gQuotientPointOrbits X Z G q hfin hq x' x hqx
    apply hx'
    rw [← hgx]
    exact (hU g hg x).2 hx

theorem eq_of_preimage_eq (hs : Function.Surjective q) {A B : Z.Opens}
    (h : q ⁻¹ᵁ A = q ⁻¹ᵁ B) : A = B := by
  ext z
  obtain ⟨x, rfl⟩ := hs z
  change x ∈ q ⁻¹ᵁ A ↔ x ∈ q ⁻¹ᵁ B
  rw [h]

/-- Invariance of a pulled-back section, transported along an equality of opens. -/
theorem secMap_eqToHom (hq : IsGQuotient G q) {g : Aut X} (hg : g ∈ G) {W : Z.Opens}
    {U : X.Opens} (e : q ⁻¹ᵁ W = U) (hU : U ≤ g.asIso.hom ⁻¹ᵁ U) (s : Γ(X, U))
    (hs : g.asIso.hom.appLE U U hU s = s) :
    secMap g.asIso.hom (hq.1 g hg) W (X.presheaf.map (eqToHom e).op s) =
      X.presheaf.map (eqToHom e).op s := by
  simp only [secMap]
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
  conv_rhs => rw [← hs]
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

/-- **Descent of a `G`-invariant map to `P¹` through an SGA 1 quotient** (on the preimage of an
open `O`). The charts are the images of the `G`-stable charts (open, `q` closed and surjective);
the functions are the invariant sections, which descend (`exists_descend_section`); the identities
descend by injectivity of `q.app` (`app_injective_of_isGQuotient`). -/
theorem exists_descend_toP1In [IsFinite q] (hq : IsGQuotient G q) (hfin : Finite G) (O : Z.Opens)
    (σ : ToP1In X (q ⁻¹ᵁ O))
    (hU : ∀ g ∈ G, ∀ x, g.asIso.hom x ∈ σ.U ↔ x ∈ σ.U)
    (hV : ∀ g ∈ G, ∀ x, g.asIso.hom x ∈ σ.V ↔ x ∈ σ.V)
    (hf : ∀ (g : Aut X) (hg : g ∈ G),
      g.asIso.hom.appLE σ.U σ.U (fun x hx => (hU g hg x).2 hx) σ.f = σ.f)
    (hg' : ∀ (g : Aut X) (hg : g ∈ G),
      g.asIso.hom.appLE σ.V σ.V (fun x hx => (hV g hg x).2 hx) σ.g = σ.g) :
    ∃ σ' : ToP1In Z O, ∃ eU : q ⁻¹ᵁ σ'.U = σ.U,
      q.app σ'.U σ'.f = X.presheaf.map (eqToHom eU).op σ.f := by
  have hsurj := isGQuotient_surjective G q hfin hq
  set U' := imgOpen q σ.U with hU'
  set V' := imgOpen q σ.V with hV'
  have eU : q ⁻¹ᵁ U' = σ.U := preimage_imgOpen hq hfin σ.U hU
  have eV : q ⁻¹ᵁ V' = σ.V := preimage_imgOpen hq hfin σ.V hV
  obtain ⟨f', hf'⟩ := exists_descend_section hq U' (X.presheaf.map (eqToHom eU).op σ.f)
    (fun g hg => secMap_eqToHom hq hg eU _ σ.f (hf g hg))
  obtain ⟨g', hg''⟩ := exists_descend_section hq V' (X.presheaf.map (eqToHom eV).op σ.g)
    (fun g hg => secMap_eqToHom hq hg eV _ σ.g (hg' g hg))
  have eUV : q ⁻¹ᵁ (U' ⊓ V') = σ.U ⊓ σ.V := by
    rw [Scheme.Hom.preimage_inf, eU, eV]
  -- pulling back restrictions
  have hresf : q.app (U' ⊓ V') (Z.presheaf.map (homOfLE (inf_le_left : U' ⊓ V' ≤ U')).op f') =
      X.presheaf.map (eqToHom eUV).op
        (X.presheaf.map (homOfLE (inf_le_left : σ.U ⊓ σ.V ≤ σ.U)).op σ.f) := by
    rw [app_map_eq, hf', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hresg : q.app (U' ⊓ V') (Z.presheaf.map (homOfLE (inf_le_right : U' ⊓ V' ≤ V')).op g') =
      X.presheaf.map (eqToHom eUV).op
        (X.presheaf.map (homOfLE (inf_le_right : σ.U ⊓ σ.V ≤ σ.V)).op σ.g) := by
    rw [app_map_eq, hg'', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hbf : Z.basicOpen f' = U' ⊓ V' := by
    apply eq_of_preimage_eq hsurj
    rw [Scheme.preimage_basicOpen, hf', Scheme.basicOpen_res, σ.basicOpen_f, eUV]
    exact inf_eq_right.mpr (by rw [eU]; exact inf_le_left)
  have hbg : Z.basicOpen g' = U' ⊓ V' := by
    apply eq_of_preimage_eq hsurj
    rw [Scheme.preimage_basicOpen, hg'', Scheme.basicOpen_res, σ.basicOpen_g, eUV]
    exact inf_eq_right.mpr (by rw [eV]; exact inf_le_right)
  refine ⟨⟨U', V', ?_, f', g', ?_, hbf, hbg⟩, eU, hf'⟩
  · apply eq_of_preimage_eq hsurj
    rw [Scheme.Hom.preimage_sup, eU, eV, σ.cover]
  · apply app_injective_of_isGQuotient hq (U' ⊓ V')
    rw [map_mul, map_one, hresf, hresg, ← map_mul, σ.inv, map_one]

end DescentP1

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 21: transport of maps to `P¹` along open immersions
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

section Transport

variable {X Y : Scheme.{0}}

/-- Sections over an open inside the range of an open immersion are detected after pulling back. -/
theorem app_injective_of_le_range (j : Y ⟶ X) [IsOpenImmersion j] (A : X.Opens)
    (hA : A ≤ j.opensRange) : Function.Injective (j.app A) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply TopCat.Presheaf.section_ext X.sheaf A
  intro x hx
  obtain ⟨y, rfl⟩ := hA hx
  have e := j.germ_stalkMap_apply A y hx s
  rw [hs, map_zero] at e
  have hinj : Function.Injective (j.stalkMap y) :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap y)).1
  change X.presheaf.germ A (j y) hx s = X.presheaf.germ A (j y) hx 0
  rw [map_zero]
  exact hinj (e.trans (map_zero _).symm)

theorem eq_of_preimage_eq_of_le_range (j : Y ⟶ X) [IsOpenImmersion j] {A B : X.Opens} (hA : A ≤ j.opensRange)
    (hB : B ≤ j.opensRange) (h : j ⁻¹ᵁ A = j ⁻¹ᵁ B) : A = B := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := hA hx
    have : y ∈ j ⁻¹ᵁ B := h ▸ hx
    exact this
  · intro hx
    obtain ⟨y, rfl⟩ := hB hx
    have : y ∈ j ⁻¹ᵁ A := h.symm ▸ hx
    exact this

/-- The section `(j.appIso U).inv s` pulls back to `s`. -/
theorem app_appIso_inv_apply (j : Y ⟶ X) [IsOpenImmersion j] (U : Y.Opens) (s : Γ(Y, U)) :
    j.app (j ''ᵁ U) ((j.appIso U).inv s) =
      Y.presheaf.map (eqToHom (j.preimage_image_eq U)).op s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appIso_inv_app]

/-- **Pushing a map to `P¹` forward along an open immersion**, as a map on its range. -/
def pushToP1In (j : Y ⟶ X) [IsOpenImmersion j] (σ : ToP1 Y) : ToP1In X j.opensRange where
  U := j ''ᵁ σ.U
  V := j ''ᵁ σ.V
  cover := by
    rw [← j.image_top_eq_opensRange, ← σ.cover]
    ext x
    simp only [Opens.coe_sup, Set.mem_union, Scheme.Hom.coe_image, SetLike.mem_coe, Set.image_union]
  f := (j.appIso σ.U).inv σ.f
  g := (j.appIso σ.V).inv σ.g
  inv := by
    have hle : j ''ᵁ σ.U ⊓ j ''ᵁ σ.V ≤ j.opensRange :=
      inf_le_left.trans (j.image_le_opensRange _)
    apply app_injective_of_le_range j _ hle
    have hpre : j ⁻¹ᵁ (j ''ᵁ σ.U ⊓ j ''ᵁ σ.V) = σ.U ⊓ σ.V := by
      rw [Scheme.Hom.preimage_inf, j.preimage_image_eq, j.preimage_image_eq]
    rw [map_mul, map_one, app_map_eq, app_map_eq, app_appIso_inv_apply, app_appIso_inv_apply,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    have := congrArg (Y.presheaf.map (eqToHom hpre).op) σ.inv
    rw [map_mul, map_one, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp] at this
    exact this
  basicOpen_f := by
    rw [← Scheme.image_basicOpen, σ.basicOpen_f]
    ext x
    simp only [Opens.coe_inf, Scheme.Hom.coe_image, Set.mem_inter_iff, Set.mem_image,
      SetLike.mem_coe]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨y, h1, rfl⟩, ⟨y, h2, rfl⟩⟩
    · rintro ⟨⟨y, h1, rfl⟩, ⟨y', h2, hy⟩⟩
      obtain rfl := j.isOpenEmbedding.injective hy
      exact ⟨y', ⟨h1, h2⟩, rfl⟩
  basicOpen_g := by
    rw [← Scheme.image_basicOpen, σ.basicOpen_g]
    ext x
    simp only [Opens.coe_inf, Scheme.Hom.coe_image, Set.mem_inter_iff, Set.mem_image,
      SetLike.mem_coe]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨y, h1, rfl⟩, ⟨y, h2, rfl⟩⟩
    · rintro ⟨⟨y, h1, rfl⟩, ⟨y', h2, hy⟩⟩
      obtain rfl := j.isOpenEmbedding.injective hy
      exact ⟨y', ⟨h1, h2⟩, rfl⟩

/-- Values of the pushed-forward function. -/
theorem ev_pushToP1In (j : Y ⟶ X) [IsOpenImmersion j] (σ : ToP1 Y) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ Y) (hy : ptOf y ∈ σ.U)
    (hy' : ptOf (y ≫ j) ∈ (pushToP1In j σ).U) :
    ev (y ≫ j) hy' (pushToP1In j σ).f = ev y hy σ.f := by
  rw [_root_.LeafQM.AV.Pin.ImagePlane.ev_comp]
  change ev y _ (j.app (j ''ᵁ σ.U) ((j.appIso σ.U).inv σ.f)) = _
  rw [app_appIso_inv_apply]
  have e : Y.presheaf.map (eqToHom (j.preimage_image_eq σ.U)).op =
      Y.presheaf.map (homOfLE (j.preimage_image_eq σ.U).le).op :=
    congrArg (fun i : (j ⁻¹ᵁ j ''ᵁ σ.U) ⟶ σ.U => Y.presheaf.map i.op) (Subsingleton.elim _ _)
  rw [e]
  exact ev_res y _ _ σ.f

/-- **Pulling a map to `P¹` on `O` back along `h` with `h⁻¹O = ⊤`.** -/
def pullToP1 {O : X.Opens} (σ : ToP1In X O) (h : Y ⟶ X) (hO : h ⁻¹ᵁ O = ⊤) : ToP1 Y where
  U := h ⁻¹ᵁ σ.U
  V := h ⁻¹ᵁ σ.V
  cover := by rw [← Scheme.Hom.preimage_sup, σ.cover, hO]
  f := h.app σ.U σ.f
  g := h.app σ.V σ.g
  inv := by
    have n1 := ConcreteCategory.congr_hom
      (h.naturality (homOfLE (inf_le_left : σ.U ⊓ σ.V ≤ σ.U)).op) σ.f
    have n2 := ConcreteCategory.congr_hom
      (h.naturality (homOfLE (inf_le_right : σ.U ⊓ σ.V ≤ σ.V)).op) σ.g
    simp only [ConcreteCategory.comp_apply] at n1 n2
    have e := congrArg (h.app (σ.U ⊓ σ.V)) σ.inv
    rw [map_mul, map_one, n1, n2] at e
    exact e
  basicOpen_f := by rw [← Scheme.preimage_basicOpen, σ.basicOpen_f]; rfl
  basicOpen_g := by rw [← Scheme.preimage_basicOpen, σ.basicOpen_g]; rfl

theorem val_pullToP1_of_mem {O : X.Opens} (σ : ToP1In X O) (h : Y ⟶ X) (hO : h ⁻¹ᵁ O = ⊤)
    {K : Type} [Field K] (y : Spec (CommRingCat.of K) ⟶ Y) (hy : ptOf (y ≫ h) ∈ σ.U) :
    (pullToP1 σ h hO).val y = OnePoint.some (ev (y ≫ h) hy σ.f) := by
  rw [val_of_mem (pullToP1 σ h hO) y hy]
  rw [_root_.LeafQM.AV.Pin.ImagePlane.ev_comp]
  rfl

theorem val_pullToP1_of_not_mem {O : X.Opens} (σ : ToP1In X O) (h : Y ⟶ X) (hO : h ⁻¹ᵁ O = ⊤)
    {K : Type} [Field K] (y : Spec (CommRingCat.of K) ⟶ Y) (hy : ptOf (y ≫ h) ∉ σ.U) :
    (pullToP1 σ h hO).val y = OnePoint.infty :=
  val_of_not_mem (pullToP1 σ h hO) y hy

end Transport

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 22: (B-desc-map) `QuotientDescendsMapQ` proved
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

/-- The inclusion of the generic fibre `𝒴_ℚ → 𝒴`. -/
abbrev genJ {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) :
    (genFib 𝒴).left ⟶ 𝒴.left :=
  pullback.fst 𝒴.hom (specRatToZloc p)

instance isOpenImmersion_genJ {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) :
    IsOpenImmersion (genJ 𝒴) :=
  MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ (isOpenImmersion_specRatToZloc p)

theorem ev_congr {K : Type} [Field K] {X : Scheme.{0}} {y y' : Spec (CommRingCat.of K) ⟶ X}
    (h : y = y') {O : X.Opens} (hx : ptOf y ∈ O) (hx' : ptOf y' ∈ O) (s : Γ(X, O)) :
    ev y hx s = ev y' hx' s := by
  subst h; rfl

theorem ev_appLE {K : Type} [Field K] {X Y : Scheme.{0}} (h : Y ⟶ X)
    (y : Spec (CommRingCat.of K) ⟶ Y) {O : X.Opens} {O' : Y.Opens} (e : O' ≤ h ⁻¹ᵁ O)
    (hy : ptOf y ∈ O') (hy' : ptOf (y ≫ h) ∈ O) (s : Γ(X, O)) :
    ev y hy (h.appLE O O' e s) = ev (y ≫ h) hy' s := by
  rw [_root_.LeafQM.AV.Pin.ImagePlane.ev_comp y h hy' s]
  change ev y hy (Y.presheaf.map (homOfLE e).op (h.app O s)) = _
  exact ev_res y e hy (h.app O s)

section Invariance

variable {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
  (hS : SmoothOfRelativeDimension 1 𝒴.hom) {G : Subgroup (Aut 𝒴.left)}
  (hover : ∀ g ∈ G, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) (σ : ToP1 (genFib 𝒴).left)
  (hσ : ∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (g : Aut 𝒴.left), g ∈ G →
    s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
      s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) ≫ g.asIso.hom →
    σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left)

include hS in
/-- Closed points of the generic fibre give `ℚ̄`-points; the generic fibre is Jacobson. -/
theorem genFib_jacobson : JacobsonSpace (genFib 𝒴).left := by
  haveI : SmoothOfRelativeDimension 1 (genFib 𝒴).hom := genFib_smooth 𝒴 hS
  haveI : Smooth (genFib 𝒴).hom := SmoothOfRelativeDimension.smooth 1 _
  exact LocallyOfFiniteType.jacobsonSpace (genFib 𝒴).hom

include hS hσ in
/-- **The pushed-forward chart `U` is `G`-stable** (closed points carry `ℚ̄`-points). -/
theorem pushU_stable (g : Aut 𝒴.left) (hg : g ∈ G) (x : 𝒴.left)
    (hx : x ∈ (pushToP1In (genJ 𝒴) σ).U) : g.asIso.hom x ∈ (pushToP1In (genJ 𝒴) σ).U := by
  haveI := genFib_jacobson hS
  haveI : SmoothOfRelativeDimension 1 (genFib 𝒴).hom := genFib_smooth 𝒴 hS
  haveI : Smooth (genFib 𝒴).hom := SmoothOfRelativeDimension.smooth 1 _
  by_contra hgx
  set j := genJ 𝒴 with hj
  set σX := pushToP1In j σ with hσX
  let S : Set (genFib 𝒴).left :=
    j ⁻¹' (σX.U : Set 𝒴.left) ∩ (j ≫ g.asIso.hom) ⁻¹' (σX.U : Set 𝒴.left)ᶜ
  have hSlc : IsLocallyClosed S :=
    ((σX.U.isOpen.preimage j.continuous).isLocallyClosed).inter
      ((σX.U.isOpen.isClosed_compl.preimage (j ≫ g.asIso.hom).continuous).isLocallyClosed)
  obtain ⟨y, hy⟩ : x ∈ Set.range j := j.image_le_opensRange _ hx
  have hne : S.Nonempty := ⟨y, by rw [← hy] at hx hgx; exact ⟨hx, hgx⟩⟩
  obtain ⟨c, hcS, hcc⟩ := nonempty_inter_closedPoints hne hSlc
  obtain ⟨emb, s, hs⟩ := exists_qbarPt (genFib 𝒴) c (mem_closedPoints_iff.mp hcc)
  have hpts : ptOf s.left = c := by
    change (Scheme.SpecToEquivOfField Qbar _ s.left).1 = c
    rw [hs, Equiv.apply_symm_apply]
  obtain ⟨s', hs'⟩ := genFib_pt 𝒴 (s.left ≫ j ≫ g.asIso.hom)
  have hv := hσ s s' g hg hs'
  have hcU : c ∈ σ.U := by
    have h1 := hcS.1
    change j c ∈ j ''ᵁ σ.U at h1
    obtain ⟨c', hc', he⟩ := h1
    rwa [← j.isOpenEmbedding.injective he]
  have hs'U : ptOf s'.left ∉ σ.U := by
    intro h
    apply hcS.2
    have e1 : j (ptOf s'.left) = (j ≫ g.asIso.hom) c := by
      rw [← hpts]
      change qbarPoint (s'.left ≫ j) = qbarPoint ((s.left ≫ j) ≫ g.asIso.hom)
      exact congrArg _ (hs'.trans (Category.assoc _ _ _).symm)
    change (j ≫ g.asIso.hom) c ∈ (j ''ᵁ σ.U : Set 𝒴.left)
    rw [← e1]
    exact ⟨_, h, rfl⟩
  rw [val_of_mem σ s.left (hpts ▸ hcU), val_of_not_mem σ s'.left hs'U] at hv
  exact OnePoint.coe_ne_infty _ hv

include hS hover hσ in
theorem pushU_stable_iff (g : Aut 𝒴.left) (hg : g ∈ G) (x : 𝒴.left) :
    g.asIso.hom x ∈ (pushToP1In (genJ 𝒴) σ).U ↔ x ∈ (pushToP1In (genJ 𝒴) σ).U := by
  constructor
  · intro h
    have := pushU_stable hS σ hσ g⁻¹ (G.inv_mem hg) _ h
    have e : (g⁻¹).asIso.hom (g.asIso.hom x) = x := by
      simp only [Aut.inv_asIso, Iso.symm_hom]
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rwa [e] at this
  · exact pushU_stable hS σ hσ g hg x

include hS hover hσ in
/-- **The pushed-forward function `f` is `G`-invariant** (`𝒴` reduced; a nonzero difference
would be nonzero at a closed point of the generic fibre, i.e. at a `ℚ̄`-point). -/
theorem pushF_invariant (g : Aut 𝒴.left) (hg : g ∈ G) :
    g.asIso.hom.appLE (pushToP1In (genJ 𝒴) σ).U (pushToP1In (genJ 𝒴) σ).U
      (fun x hx => (pushU_stable_iff hS hover σ hσ g hg x).2 hx) (pushToP1In (genJ 𝒴) σ).f =
      (pushToP1In (genJ 𝒴) σ).f := by
  haveI := genFib_jacobson hS
  haveI : SmoothOfRelativeDimension 1 (genFib 𝒴).hom := genFib_smooth 𝒴 hS
  haveI : Smooth (genFib 𝒴).hom := SmoothOfRelativeDimension.smooth 1 _
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  haveI : IsReduced 𝒴.left := isReduced_of_smooth_zloc 𝒴
  set j := genJ 𝒴 with hj
  set σX := pushToP1In j σ with hσX
  set d := g.asIso.hom.appLE σX.U σX.U
      (fun x hx => (pushU_stable_iff hS hover σ hσ g hg x).2 hx) σX.f - σX.f with hd
  rw [← sub_eq_zero, ← hd, ← basicOpen_eq_bot_iff]
  by_contra hne
  obtain ⟨x, hx⟩ : ((𝒴.left.basicOpen d : 𝒴.left.Opens) : Set 𝒴.left).Nonempty := by
    by_contra h0
    apply hne
    ext1
    simpa [Set.not_nonempty_iff_eq_empty] using h0
  have hxU : x ∈ σX.U := 𝒴.left.basicOpen_le d hx
  obtain ⟨y, hy⟩ : x ∈ Set.range j := j.image_le_opensRange _ hxU
  let B : Set (genFib 𝒴).left := j ⁻¹' (𝒴.left.basicOpen d : Set 𝒴.left)
  have hBo : IsOpen B := (𝒴.left.basicOpen d).isOpen.preimage j.continuous
  have hyB : y ∈ B := by
    change j y ∈ (𝒴.left.basicOpen d : Set 𝒴.left)
    rw [hy]; exact hx
  obtain ⟨c, hcB, hcc⟩ := nonempty_inter_closedPoints ⟨y, hyB⟩ hBo.isLocallyClosed
  obtain ⟨emb, s, hs⟩ := exists_qbarPt (genFib 𝒴) c (mem_closedPoints_iff.mp hcc)
  let t : Spec (CommRingCat.of Qbar) ⟶ (genFib 𝒴).left := s.left
  have hpts : ptOf t = c := by
    change (Scheme.SpecToEquivOfField Qbar _ s.left).1 = c
    rw [hs, Equiv.apply_symm_apply]
  have hcX : j c ∈ σX.U := 𝒴.left.basicOpen_le d hcB
  have hcU : c ∈ σ.U := by
    obtain ⟨c', hc', he⟩ := hcX
    rwa [← j.isOpenEmbedding.injective he]
  obtain ⟨s', hs'⟩ := genFib_pt 𝒴 (t ≫ j ≫ g.asIso.hom)
  let t' : Spec (CommRingCat.of Qbar) ⟶ (genFib 𝒴).left := s'.left
  have hs't : t' ≫ j = t ≫ j ≫ g.asIso.hom := hs'
  have hv : σ.val t = σ.val t' := hσ s s' g hg hs'
  have hgc : g.asIso.hom (j c) ∈ σX.U := (pushU_stable_iff hS hover σ hσ g hg _).2 hcX
  have hs'X : ptOf (t' ≫ j) ∈ σX.U := by
    have e2 : qbarPoint (t' ≫ j) = g.asIso.hom (j (ptOf t)) := congrArg qbarPoint hs't
    change qbarPoint (t' ≫ j) ∈ _
    rw [e2, hpts]; exact hgc
  have hs'U : ptOf t' ∈ σ.U := by
    obtain ⟨c', hc', he⟩ := hs'X
    have : c' = ptOf t' := j.isOpenEmbedding.injective (he.trans rfl)
    rwa [← this]
  have hsX : ptOf (t ≫ j) ∈ σX.U := by
    change j (ptOf t) ∈ _; rw [hpts]; exact hcX
  rw [val_of_mem σ t (hpts ▸ hcU), val_of_mem σ t' hs'U] at hv
  have hv' := OnePoint.coe_injective hv
  have hdx : ptOf (t ≫ j) ∈ 𝒴.left.basicOpen d := by
    change j (ptOf t) ∈ _; rw [hpts]; exact hcB
  apply (ev_eq_zero_iff (t ≫ j) hsX d).1 _ hdx
  rw [hd, map_sub, sub_eq_zero]
  have hgX : ptOf ((t ≫ j) ≫ g.asIso.hom) ∈ σX.U := by
    rw [Category.assoc, ← hs't]; exact hs'X
  rw [ev_appLE (O := σX.U) (O' := σX.U) g.asIso.hom (t ≫ j)
    (fun x hx => (pushU_stable_iff hS hover σ hσ g hg x).2 hx) hsX hgX]
  rw [ev_congr (show (t ≫ j) ≫ g.asIso.hom = t' ≫ j by rw [Category.assoc, hs't]) hgX hs'X]
  rw [ev_pushToP1In j σ t' hs'U hs'X, ev_pushToP1In j σ t (hpts ▸ hcU) hsX]
  exact hv'.symm

end Invariance

end MCRQuot

/-! ## The descent, assembled -/

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

/-- **(B-desc-map) `QuotientDescendsMapQ` proved.** Push `σ` forward to the open `𝒴_ℚ ⊆ 𝒴`
(`pushToP1In`), check `G`-invariance of its charts and functions at `ℚ̄`-points (`pushU_stable_iff`,
`pushF_invariant`, also for the swapped charts `_root_.LeafQM.AV.Pin.ImagePlane.inv σ`), descend through the quotient
(`exists_descend_toP1In`, on the open `𝒵_ℚ ⊆ 𝒵`, whose preimage is `𝒴_ℚ`), and pull back to
`𝒵_ℚ` (`pullToP1`). -/
theorem quotientDescendsMapQ : QuotientDescendsMapQ := by
  intro p _ 𝒴 𝒵 q G hP hS hfin hover hq hqf σ hσ
  haveI := hqf
  set j := genJ 𝒴 with hj
  set jZ := genJ 𝒵 with hjZ
  set O : 𝒵.left.Opens := jZ.opensRange with hOdef
  have hO : q.left ⁻¹ᵁ O = j.opensRange := by
    ext x
    change q.left x ∈ Set.range jZ ↔ x ∈ Set.range j
    have h1 := Set.ext_iff.mp (Scheme.Pullback.range_fst 𝒵.hom (specRatToZloc p)) (q.left x)
    have h2 := Set.ext_iff.mp (Scheme.Pullback.range_fst 𝒴.hom (specRatToZloc p)) x
    refine h1.trans (Iff.trans ?_ h2.symm)
    change 𝒵.hom (q.left x) ∈ Set.range (specRatToZloc p) ↔
      𝒴.hom x ∈ Set.range (specRatToZloc p)
    rw [← Scheme.Hom.comp_apply, Over.w q]
  let σX0 := pushToP1In j σ
  let σX : ToP1In 𝒴.left (q.left ⁻¹ᵁ O) :=
    { U := σX0.U, V := σX0.V, cover := σX0.cover.trans hO.symm, f := σX0.f, g := σX0.g,
      inv := σX0.inv, basicOpen_f := σX0.basicOpen_f, basicOpen_g := σX0.basicOpen_g }
  have hσinv : ∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (g : Aut 𝒴.left), g ∈ G →
      s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
        s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) ≫ g.asIso.hom →
      (_root_.LeafQM.AV.Pin.ImagePlane.inv σ).val (K := Qbar) s.left = (_root_.LeafQM.AV.Pin.ImagePlane.inv σ).val (K := Qbar) s'.left := by
    intro s s' g hg h
    exact (val_inv σ _).trans ((congrArg _ (hσ s s' g hg h)).trans (val_inv σ _).symm)
  obtain ⟨σ', eU, hf'⟩ := exists_descend_toP1In hq hfin O σX
    (pushU_stable_iff hS hover σ hσ) (pushU_stable_iff hS hover (_root_.LeafQM.AV.Pin.ImagePlane.inv σ) hσinv)
    (pushF_invariant hS hover σ hσ) (pushF_invariant hS hover (_root_.LeafQM.AV.Pin.ImagePlane.inv σ) hσinv)
  have hOZ : jZ ⁻¹ᵁ O = ⊤ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩
  refine ⟨pullToP1 σ' jZ hOZ, fun s => ?_⟩
  let t : Spec (CommRingCat.of Qbar) ⟶ (genFib 𝒵).left := (s ≫ genFibMap q).left
  let u : Spec (CommRingCat.of Qbar) ⟶ (genFib 𝒴).left := s.left
  have htj : t ≫ jZ = (u ≫ j) ≫ q.left :=
    (Category.assoc _ _ _).trans ((congrArg (s.left ≫ ·) (genFibMap_fst q)).trans
      (Category.assoc _ _ _).symm)
  change (pullToP1 σ' jZ hOZ).val t = σ.val u
  by_cases hu : ptOf u ∈ σ.U
  · have huX : ptOf (u ≫ j) ∈ σX.U := ⟨_, hu, rfl⟩
    have hqU : ptOf ((u ≫ j) ≫ q.left) ∈ σ'.U := by
      have : ptOf (u ≫ j) ∈ q.left ⁻¹ᵁ σ'.U := by rw [eU]; exact huX
      exact this
    have htU : ptOf (t ≫ jZ) ∈ σ'.U := by
      change qbarPoint (t ≫ jZ) ∈ σ'.U
      rw [htj]; exact hqU
    rw [val_pullToP1_of_mem σ' jZ hOZ t htU, val_of_mem σ u hu]
    congr 1
    rw [ev_congr htj htU hqU, _root_.LeafQM.AV.Pin.ImagePlane.ev_comp (u ≫ j) q.left hqU σ'.f, hf']
    have e : 𝒴.left.presheaf.map (eqToHom eU).op =
        𝒴.left.presheaf.map (homOfLE eU.le).op :=
      congrArg (fun i : (q.left ⁻¹ᵁ σ'.U) ⟶ σX.U => 𝒴.left.presheaf.map i.op)
        (Subsingleton.elim _ _)
    rw [e, ev_res]
    exact ev_pushToP1In j σ u hu huX
  · have htU : ptOf (t ≫ jZ) ∉ σ'.U := by
      intro h
      apply hu
      change qbarPoint (t ≫ jZ) ∈ σ'.U at h
      rw [htj] at h
      have h' : ptOf (u ≫ j) ∈ q.left ⁻¹ᵁ σ'.U := h
      rw [eU] at h'
      obtain ⟨c', hc', he⟩ := h'
      have : c' = ptOf u := j.isOpenEmbedding.injective (he.trans rfl)
      rwa [← this]
    rw [val_pullToP1_of_not_mem σ' jZ hOZ t htU, val_of_not_mem σ u hu]

/-- **(B-desc) `QuotientDescendsQ` proved** (descent half `quotientDescendsMapQ`, lifting half
`exists_lift_qbar`). -/
theorem quotientDescendsQ : QuotientDescendsQ := quotientDescendsQ_of quotientDescendsMapQ

/-- **Glue B from glue A, T5, L3 and (B-iso) alone.** -/
theorem genericQuotientP1_of' (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
    (hTS : TameQuotientSmooth) (hB : ToP1BijIsCoordinateQ) : GenericQuotientP1 :=
  genericQuotientP1_of hA hT hTS quotientDescendsQ hB

/-- **Main composite (after part 22): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the decomposition's glue `CoverModelOfHeckeN`, and the glue
(B-iso) `ToP1BijIsCoordinateQ`, (C1b-obj) `CMStabObj`.** -/
theorem modelCoordinateResidue_final8 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hCov : CoverModelOfHeckeN) (hB : ToP1BijIsCoordinateQ) (hO : CMStabObj) :
    ModelCoordinateResidue :=
  modelCoordinateResidue_final7 hAF hQE hTS hP1 hFix hCyc hT hC hCov quotientDescendsMapQ hB hO

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 23: (B-iso) reduced to `CurveBijIso` and the existence of `P¹_ℚ`
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

/-- **Glue (B-P¹): the projective line over `ℚ` exists and represents maps to `P¹` by charts**
(foundations; Mathlib 4.35 has `Proj` with `IsProper (Proj.toSpecZero 𝒜)` but no `P¹` with its
smoothness and functor of points; Hartshorne II.7.1 / EGA II 4.2.4 (locators UNVERIFIED)). There
are a proper scheme `P` over `ℚ`, smooth of relative dimension 1, and charts `τ : P ≅ P¹` (by
`IsP1CoordinateQ`: the two charts are `Spec ℚ[t]`, `Spec ℚ[s]`), such that every `σ : ToP1 Z`
of a `ℚ`-scheme `Z` is `τ ∘ m` for a morphism `m : Z → P` over `ℚ` (`m⁻¹U_τ = U_σ`,
`m⁻¹V_τ = V_σ`, `m^*τ.f = σ.f`, `m^*τ.g = σ.g`). (`P = Proj ℚ[X₀, X₁]`; `m` is glued from
`U_σ → D₊(X₀)`, `t ↦ f`, and `V_σ → D₊(X₁)`, `s ↦ g`, which agree on `U_σ ∩ V_σ` because
`f g = 1`; `m⁻¹ D₊(X₀) = U_σ` because `g` vanishes exactly on `V_σ ∖ U_σ`.) -/
def P1SchemeQ : Prop :=
  ∃ (P : Over (Spec (CommRingCat.of ℚ))) (τ : ToP1 P.left),
    IsProper P.hom ∧ SmoothOfRelativeDimension 1 P.hom ∧ IsP1CoordinateQ P τ ∧
    ∀ (Z : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 Z.left),
      ∃ (m : Z ⟶ P) (eU : m.left ⁻¹ᵁ τ.U = σ.U) (eV : m.left ⁻¹ᵁ τ.V = σ.V),
        m.left.app τ.U τ.f = Z.left.presheaf.map (eqToHom eU).op σ.f ∧
        m.left.app τ.V τ.g = Z.left.presheaf.map (eqToHom eV).op σ.g

section ChartsQ

variable {K : Type} [Field K]

/-- **Chart injectivity over `ℚ`** (as `eq_of_ev_eq_chart`, with `ℚ` in place of `ℤ_(p)`). -/
theorem eq_of_ev_eq_chartQ (Z : Over (Spec (CommRingCat.of ℚ))) {W : Z.left.Opens}
    (hW : IsAffineOpen W) (h : Γ(Z.left, W))
    (hs : Function.Surjective (eval₂RingHom (baseToSectionsOver _ Z W) h))
    (z z' : Spec (CommRingCat.of K) ⟶ Z.left) (hz : ptOf z ∈ W) (hz' : ptOf z' ∈ W)
    (he : ev z hz h = ev z' hz' h) : z = z' := by
  have hring : ev z hz = ev z' hz' := by
    ext s
    obtain ⟨P, rfl⟩ := hs s
    simp only [coe_eval₂RingHom]
    rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂, he,
      Subsingleton.elim ((ev z hz).comp (baseToSectionsOver _ Z W))
        ((ev z' hz').comp (baseToSectionsOver _ Z W))]
  refine eq_of_appLE_eq z z' hW (top_le_preimage_of_ptOf_mem z hz)
    (top_le_preimage_of_ptOf_mem z' hz') ?_
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
  ext s
  have := congrArg (fun φ : Γ(Z.left, W) →+* K => φ s) hring
  simp only [ev_eq_appLE] at this
  exact this

/-- **An isomorphism onto `P¹_ℚ` by charts is injective on field points.** -/
theorem val_injective_of_isP1CoordinateQ {Z : Over (Spec (CommRingCat.of ℚ))} {ρ : ToP1 Z.left}
    (hρ : IsP1CoordinateQ Z ρ) (z z' : Spec (CommRingCat.of K) ⟶ Z.left)
    (h : ρ.val z = ρ.val z') : z = z' := by
  obtain ⟨hU, hV, hbU, hbV⟩ := hρ
  by_cases hz : ptOf z ∈ ρ.U <;> by_cases hz' : ptOf z' ∈ ρ.U
  · rw [val_of_mem ρ z hz, val_of_mem ρ z' hz'] at h
    exact eq_of_ev_eq_chartQ Z hU ρ.f hbU.2 z z' hz hz' (OnePoint.coe_injective h)
  · rw [val_of_mem ρ z hz, val_of_not_mem ρ z' hz'] at h
    exact (OnePoint.coe_ne_infty _ h).elim
  · rw [val_of_not_mem ρ z hz, val_of_mem ρ z' hz'] at h
    exact (OnePoint.coe_ne_infty _ h.symm).elim
  · have hv := mem_V_of_not_mem_U ρ hz
    have hv' := mem_V_of_not_mem_U ρ hz'
    refine eq_of_ev_eq_chartQ Z hV ρ.g hbV.2 z z' hv hv' ?_
    rw [ev_g_eq_zero ρ z hv hz, ev_g_eq_zero ρ z' hv' hz']

end ChartsQ

/-- Transport of the polynomial-chart property along an isomorphism `m`. -/
theorem bijective_eval₂_transport {Z P : Over (Spec (CommRingCat.of ℚ))} (m : Z ⟶ P)
    [IsIso m.left] {A : P.left.Opens} {B : Z.left.Opens} (e : m.left ⁻¹ᵁ A = B)
    (a : Γ(P.left, A)) (b : Γ(Z.left, B))
    (hab : m.left.app A a = Z.left.presheaf.map (eqToHom e).op b)
    (ha : Function.Bijective (eval₂RingHom (baseToSectionsOver _ P A) a)) :
    Function.Bijective (eval₂RingHom (baseToSectionsOver _ Z B) b) := by
  let ψ : Γ(P.left, A) →+* Γ(Z.left, B) :=
    (Z.left.presheaf.map (eqToHom e.symm).op).hom.comp (m.left.app A).hom
  have hψb : Function.Bijective ψ := by
    refine (ConcreteCategory.bijective_of_isIso (Z.left.presheaf.map (eqToHom e.symm).op)).comp
      ?_
    exact ConcreteCategory.bijective_of_isIso (m.left.app A)
  have hψa : ψ a = b := by
    change Z.left.presheaf.map (eqToHom e.symm).op (m.left.app A a) = b
    rw [hab, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    simp
  have hcomp : eval₂RingHom (baseToSectionsOver _ Z B) b =
      ψ.comp (eval₂RingHom (baseToSectionsOver _ P A) a) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [coe_eval₂RingHom, eval₂_C, RingHom.coe_comp, Function.comp_apply]
      have hsub := Subsingleton.elim (baseToSectionsOver _ Z B)
        (ψ.comp (baseToSectionsOver _ P A))
      exact congrArg (fun φ => φ r) hsub
    · simp only [coe_eval₂RingHom, eval₂_X, RingHom.coe_comp, Function.comp_apply]
      exact hψa.symm
  rw [hcomp, RingHom.coe_comp]
  exact hψb.comp ha

/-- **(B-iso) reduced: `ToP1BijIsCoordinateQ` from the textbook leaf `CurveBijIso` and the
foundational glue `P1SchemeQ`.** Write `σ = τ ∘ m` (`P1SchemeQ`); `m` is bijective on `ℚ̄`-points
(`σ` is, and `τ` is injective on them), so it is an isomorphism (`CurveBijIso`), and the charts of
`τ` transport to `σ`. -/
theorem toP1BijIsCoordinateQ_of (hC : CurveBijIso) (hP : P1SchemeQ) : ToP1BijIsCoordinateQ := by
  intro Z hZp hZs σ hbij
  obtain ⟨P, τ, hPp, hPs, hτ, huniv⟩ := hP
  obtain ⟨m, eU, eV, hfU, hgV⟩ := huniv Z σ
  have hval : ∀ t : Spec (CommRingCat.of Qbar) ⟶ Z.left, τ.val (t ≫ m.left) = σ.val t := by
    intro t
    rw [← ToP1.val_comp_right τ m.left t]
    by_cases ht : ptOf t ∈ σ.U
    · have ht' : ptOf t ∈ (τ.comp m.left).U := by
        change ptOf t ∈ m.left ⁻¹ᵁ τ.U
        rw [eU]; exact ht
      rw [val_of_mem _ t ht', val_of_mem σ t ht]
      congr 1
      change ev t ht' (m.left.app τ.U τ.f) = _
      rw [hfU]
      have e : Z.left.presheaf.map (eqToHom eU).op =
          Z.left.presheaf.map (homOfLE eU.le).op :=
        congrArg (fun i : (m.left ⁻¹ᵁ τ.U) ⟶ σ.U => Z.left.presheaf.map i.op)
          (Subsingleton.elim _ _)
      rw [e]
      exact ev_res t _ _ σ.f
    · have ht' : ptOf t ∉ (τ.comp m.left).U := by
        change ptOf t ∉ m.left ⁻¹ᵁ τ.U
        rw [eU]; exact ht
      rw [val_of_not_mem _ t ht', val_of_not_mem σ t ht]
  have hmb : Function.Bijective (fun s : fieldPt Qbar ⟶ Z => s ≫ m) := by
    constructor
    · intro s s' h
      apply hbij.1
      exact (hval s.left).symm.trans
        ((congrArg (fun w : fieldPt Qbar ⟶ P => τ.val (K := Qbar) w.left) h).trans (hval s'.left))
    · intro w
      obtain ⟨s, hs⟩ := hbij.2 (τ.val (K := Qbar) w.left)
      refine ⟨s, ?_⟩
      apply Over.OverMorphism.ext
      apply val_injective_of_isP1CoordinateQ hτ
      exact (hval s.left).trans hs
  haveI : IsIso m := hC Z P hZp hZs hPp hPs m hmb
  haveI : IsIso m.left := (Over.forget _).map_isIso m
  refine ⟨?_, ?_, bijective_eval₂_transport m eU τ.f σ.f hfU hτ.2.2.1,
    bijective_eval₂_transport m eV τ.g σ.g hgV hτ.2.2.2⟩
  · rw [← eU]; exact hτ.1.preimage m.left
  · rw [← eV]; exact hτ.2.1.preimage m.left

/-- **Glue B from glue A, T5, L3, `CurveBijIso` and `P1SchemeQ`.** -/
theorem genericQuotientP1_of'' (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
    (hTS : TameQuotientSmooth) (hC : CurveBijIso) (hP : P1SchemeQ) : GenericQuotientP1 :=
  genericQuotientP1_of' hA hT hTS (toP1BijIsCoordinateQ_of hC hP)

/-- **Main composite (after part 23): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the decomposition's glue `CoverModelOfHeckeN`, the foundational glue
`P1SchemeQ` (the projective line over `ℚ`) and the QM glue (C1b-obj) `CMStabObj`.** -/
theorem modelCoordinateResidue_final9 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hCov : CoverModelOfHeckeN) (hP : P1SchemeQ) (hO : CMStabObj) : ModelCoordinateResidue :=
  modelCoordinateResidue_final8 hAF hQE hTS hP1 hFix hCyc hT hC hCov (toP1BijIsCoordinateQ_of hC hP)
    hO

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 24: the downstream composite (`HeckeVertWitness`)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **`HeckeVertWitness` (model-glue's target) from the leaves and the two new glue Props of this
task**: `ShimuraGoodReduction`, `R1R2fp`, T5, `CurveBijIso`, mcr-glue's leaves L1-L6, the
decomposition's glue `CoverModelOfHeckeN`, and `P1SchemeQ`, `CMStabObj`
(`ModelGlue.heckeVertWitness_of_curveBijIso` with `modelCoordinateResidue_final9`). -/
theorem heckeVertWitness_of_mcrQuot (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso) (hAF : ProperCurveAF)
    (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1)
    (hFix : TameFixedPointsDisjoint) (hCyc : TameInertiaCyclic) (hCov : CoverModelOfHeckeN)
    (hP : P1SchemeQ) (hO : CMStabObj) : HeckeVertWitness :=
  heckeVertWitness_of_curveBijIso hL hRR hT
    (modelCoordinateResidue_final9 hAF hQE hTS hP1 hFix hCyc hT hC hCov hP hO) hC

end MCRQuot
