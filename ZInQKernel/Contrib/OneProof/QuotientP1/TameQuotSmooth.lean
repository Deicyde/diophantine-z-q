import ZInQKernel.Contrib.OneProof.QuotientP1.TameInvariants
import ZInQKernel.Contrib.OneProof.QuotientP1.QuotProper
import ZInQKernel.OneProof.H.TailR

/-!
# p1-quot3, helper: `TameQuotientSmoothRelDim` is proved (from the chain's field `RegularSmoothPerfect`)

Generated from `scratch/p1-quot3/Scheme.lean`. Report: docs/research/p1-quot3.md.

For `q : 𝒴 → 𝒵` an SGA 1 quotient (`IsGQuotient`) by a finite group `G` of order prime to `p`, with `q` finite and
`𝒴` proper and smooth of relative dimension `1` over `ℤ_(p)`:
* `G` acts on `Γ(𝒴, q⁻¹V)` by `Γ(S, U)`-algebra maps (`sect`, `action`), and `Γ(𝒵, V) → Γ(𝒴, q⁻¹V)` is injective with
  image the invariants (`invariant_setup`);
* `smooth_appLE`: `Γ(S, ⊤) → Γ(𝒵, V)` is smooth for every affine `V` (the algebra of
  `QuotientP1Proof.TameQuot.smooth_of_invariants`: Reynolds operator, flatness as a retract, smooth fibres by
  normality of invariants and Stacks 00TV, EGA IV 17.5.1);
* `relDim_eq_one`: every standard smooth chart of `𝒵` has relative dimension `1` (fibres of `𝒵` and of `𝒴` have the
  same dimension);
* `HDec.MCRGlue.tameQuotientSmoothRelDim_of_regularSmoothPerfect : CurveSplit.RegularSmoothPerfect →
  TameQuotientSmoothRelDim`.

No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace HDec.MCRGlue.TameQuotScheme

open QuotientP1Proof.TameQuot VertWitness

theorem appLE_comp_eq {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (U V W e₁ e₂ e₃) : g.appLE U V e₁ ≫ f.appLE V W e₂ = h.appLE U W e₃ := by
  subst hfg; rw [Scheme.Hom.appLE_comp_appLE]

theorem appLE_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (U V W e₁ e₂ e₃) (x) : (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (h.appLE U W e₃).hom x := by
  rw [← appLE_comp_eq f g h hfg U V W e₁ e₂ e₃]; rfl

section Action

variable {X Z : Scheme.{0}} (q : X ⟶ Z) (W : Z.Opens)

/-- The action of an automorphism `g` with `g ≫ q = q` on `Γ(X, q⁻¹W)`. -/
def sect (g : Aut X) (h : g.asIso.hom ≫ q = q) : Γ(X, q ⁻¹ᵁ W) →+* Γ(X, q ⁻¹ᵁ W) :=
  (g.asIso.hom.appLE (q ⁻¹ᵁ W) (q ⁻¹ᵁ W) (preimage_le_of_comp_eq h W)).hom

theorem sect_congr (g g' : Aut X) (hgg : g = g') (h h') (b) : sect q W g h b = sect q W g' h' b := by
  subst hgg; rfl

theorem sect_one (g : Aut X) (h) (hg : g = 1) (b) : sect q W g h b = b := by
  subst hg
  change ((𝟙 X : X ⟶ X).appLE (q ⁻¹ᵁ W) ((𝟙 X : X ⟶ X) ⁻¹ᵁ (q ⁻¹ᵁ W)) le_rfl).hom b = b
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
  rfl

theorem sect_mul (x y z : Aut X) (hx hy hz) (hxyz : z = x * y) (b) :
    sect q W z hz b = sect q W y hy (sect q W x hx b) := by
  subst hxyz
  exact (appLE_comp_apply y.asIso.hom x.asIso.hom (x * y).asIso.hom rfl _ _ _ _ _ _ b).symm

/-- The action of `G` on `Γ(X, q⁻¹W)` (`g` acts by `g⁻¹` pulled back, so that it is a left action). -/
def action (G : Subgroup (Aut X)) (hG : ∀ g ∈ G, g.asIso.hom ≫ q = q) :
    MulSemiringAction G Γ(X, q ⁻¹ᵁ W) where
  smul g b := sect q W ((g⁻¹ : G) : Aut X) (hG _ (g⁻¹ : G).2) b
  one_smul b := sect_one q W _ _ (by simp) b
  mul_smul g h b := sect_mul q W _ _ _ _ _ _ (by simp) b
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

theorem action_smul (G : Subgroup (Aut X)) (hG : ∀ g ∈ G, g.asIso.hom ≫ q = q) (g : G) (b) :
    (action q W G hG).smul g b = sect q W ((g⁻¹ : G) : Aut X) (hG _ (g⁻¹ : G).2) b := rfl

end Action

section Setup

variable {X Z S : Scheme.{0}} (q : X ⟶ Z) (fX : X ⟶ S) (fZ : Z ⟶ S) (hw : q ≫ fZ = fX)
  (G : Subgroup (Aut X)) (hGq : ∀ g ∈ G, g.asIso.hom ≫ q = q) (hGX : ∀ g ∈ G, g.asIso.hom ≫ fX = fX)

include hw in
theorem preimage_le (U : S.Opens) (V : Z.Opens) (e : V ≤ fZ ⁻¹ᵁ U) : q ⁻¹ᵁ V ≤ fX ⁻¹ᵁ U := by
  subst hw
  intro x hx
  exact e hx

include hw hGX in
/-- **The algebra at an affine open `V ⊆ Z` over `U ⊆ S`** (continuation-passing form): `Γ(Z, V) → Γ(X, q⁻¹V)`
over `Γ(S, U)` is injective, `G`-equivariant for the action of `G` (by `Γ(S, U)`-algebra maps), with image the
invariants. -/
theorem invariant_setup (hq : IsGQuotient G q) (U : S.Opens) (V : Z.Opens) (hV : IsAffineOpen V)
    (e : V ≤ fZ ⁻¹ᵁ U) (P : Prop)
    (H : letI : Algebra Γ(S, U) Γ(Z, V) := (fZ.appLE U V e).hom.toAlgebra
      letI : Algebra Γ(S, U) Γ(X, q ⁻¹ᵁ V) := (fX.appLE U (q ⁻¹ᵁ V) (preimage_le q fX fZ hw U V e)).hom.toAlgebra
      ∀ (ι : Γ(Z, V) →ₐ[Γ(S, U)] Γ(X, q ⁻¹ᵁ V)) [MulSemiringAction G Γ(X, q ⁻¹ᵁ V)]
        [SMulCommClass G Γ(S, U) Γ(X, q ⁻¹ᵁ V)], Function.Injective ι →
        (∀ (g : G) (a : Γ(Z, V)), g • ι a = ι a) →
        (∀ b : Γ(X, q ⁻¹ᵁ V), (∀ g : G, g • b = b) → ∃ a, ι a = b) → P) : P := by
  obtain ⟨hGq', -, hW⟩ := hq
  letI : Algebra Γ(S, U) Γ(Z, V) := (fZ.appLE U V e).hom.toAlgebra
  letI : Algebra Γ(S, U) Γ(X, q ⁻¹ᵁ V) :=
    (fX.appLE U (q ⁻¹ᵁ V) (preimage_le q fX fZ hw U V e)).hom.toAlgebra
  letI act : MulSemiringAction G Γ(X, q ⁻¹ᵁ V) := action q V G hGq'
  let ι : Γ(Z, V) →ₐ[Γ(S, U)] Γ(X, q ⁻¹ᵁ V) :=
    { (q.app V).hom with
      commutes' := fun r => by
        change (q.app V).hom ((fZ.appLE U V e).hom r) = (fX.appLE U (q ⁻¹ᵁ V) _).hom r
        rw [Scheme.Hom.app_eq_appLE]
        exact appLE_comp_apply q fZ fX hw _ _ _ _ _ _ r }
  have hsmul : ∀ (g : G) (b : Γ(X, q ⁻¹ᵁ V)),
      g • b = sect q V ((g⁻¹ : G) : Aut X) (hGq' _ (g⁻¹ : G).2) b := fun _ _ => rfl
  have hcomm : SMulCommClass G Γ(S, U) Γ(X, q ⁻¹ᵁ V) := ⟨fun g r b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hsmul g (algebraMap _ _ r)]
    congr 1
    exact appLE_comp_apply _ fX fX (hGX _ (g⁻¹ : G).2) _ _ _ _ _ _ r⟩
  refine H ι (by exact (hW V hV).1) (fun g a => ?_) (fun b hb => ?_)
  · rw [hsmul]
    change (sect q V _ _) ((q.app V).hom a) = (q.app V).hom a
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_comp_apply _ q q (hGq' _ (g⁻¹ : G).2) _ _ _ _ _ _ a
  · have hmem : b ∈ Set.range (q.app V) := by
      rw [(hW V hV).2]
      intro g hg
      have := hb (⟨g, hg⟩ : G)⁻¹
      rw [hsmul] at this
      have h2 : sect q V g (hGq' g hg) b = b := by
        rw [sect_congr q V g (((⟨g, hg⟩ : G)⁻¹⁻¹ : G) : Aut X) (by rw [inv_inv]) _ (hGq' _ (((⟨g, hg⟩ : G)⁻¹⁻¹ : G)).2)]
        exact this
      exact h2
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha⟩

include hw hGX in
/-- **Smoothness on an affine chart** (the algebra `smooth_of_invariants` at `V ⊆ Z` over `U ⊆ S`). -/
theorem smooth_appLE (hRS : RegularSmoothPerfect) (hq : IsGQuotient G q) [Fintype G]
    (U : S.Opens) (hU : IsAffineOpen U) (V : Z.Opens) (hV : IsAffineOpen V) (e : V ≤ fZ ⁻¹ᵁ U)
    (hcard : IsUnit ((Fintype.card G : ℕ) : Γ(S, U))) [IsNoetherianRing Γ(S, U)]
    (hperf : ∀ (I : Ideal Γ(S, U)) [I.IsPrime], PerfectField I.ResidueField)
    [SmoothOfRelativeDimension 1 fX] [LocallyOfFiniteType fZ] :
    (fZ.appLE U V e).hom.Smooth := by
  letI : Algebra Γ(S, U) Γ(Z, V) := (fZ.appLE U V e).hom.toAlgebra
  letI : Algebra Γ(S, U) Γ(X, q ⁻¹ᵁ V) :=
    (fX.appLE U (q ⁻¹ᵁ V) (preimage_le q fX fZ hw U V e)).hom.toAlgebra
  refine invariant_setup q fX fZ hw G hGX hq U V hV e _ ?_
  intro ι _ _ hι hfix hinv
  have : IsAffineHom q := hq.2.1
  have hW : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hsm : (fX.appLE U (q ⁻¹ᵁ V) (preimage_le q fX fZ hw U V e)).hom.Smooth :=
    HasRingHomProperty.appLE (P := @Smooth) fX (SmoothOfRelativeDimension.smooth 1 fX) ⟨U, hU⟩
      ⟨q ⁻¹ᵁ V, hW⟩ _
  have hft : (fZ.appLE U V e).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) fZ inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e
  have hsrd : SmoothOfRelativeDimension 1
      (Spec.map (fX.appLE U (q ⁻¹ᵁ V) (preimage_le q fX fZ hw U V e))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
      (HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension 1) fX inferInstance ⟨U, hU⟩
        ⟨q ⁻¹ᵁ V, hW⟩ _)
  have : Algebra.Smooth Γ(S, U) Γ(X, q ⁻¹ᵁ V) := hsm
  have : Algebra.FiniteType Γ(S, U) Γ(Z, V) := hft
  exact smooth_of_invariants Γ(S, U) Γ(Z, V) Γ(X, q ⁻¹ᵁ V) ι hι G hfix hinv hcard hRS hperf
    (fun I _ => ringKrullDim_tensor_le_one Γ(S, U) Γ(X, q ⁻¹ᵁ V) I.ResidueField)

include hw hGX in
/-- **The relative dimension of a standard smooth chart of `Z` is `1`.** -/
theorem relDim_eq_one (hq : IsGQuotient G q) [Fintype G]
    (U : S.Opens) (hU : IsAffineOpen U) (V : Z.Opens) (hV : IsAffineOpen V) (e : V ≤ fZ ⁻¹ᵁ U)
    (hcard : IsUnit ((Fintype.card G : ℕ) : Γ(S, U))) [SmoothOfRelativeDimension 1 fX]
    (z : Z) (hz : z ∈ V) (n : ℕ) (hn : (fZ.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n) :
    n = 1 := by
  letI : Algebra Γ(S, U) Γ(Z, V) := (fZ.appLE U V e).hom.toAlgebra
  letI : Algebra Γ(S, U) Γ(X, q ⁻¹ᵁ V) :=
    (fX.appLE U (q ⁻¹ᵁ V) (preimage_le q fX fZ hw U V e)).hom.toAlgebra
  refine invariant_setup q fX fZ hw G hGX hq U V hV e _ ?_
  intro ι _ _ hι hfix hinv
  have : IsAffineHom q := hq.2.1
  have hW : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hsrd : SmoothOfRelativeDimension 1
      (Spec.map (fX.appLE U (q ⁻¹ᵁ V) (preimage_le q fX fZ hw U V e))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
      (HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension 1) fX inferInstance ⟨U, hU⟩
        ⟨q ⁻¹ᵁ V, hW⟩ _)
  have hn' : Algebra.IsStandardSmoothOfRelativeDimension n Γ(S, U) Γ(Z, V) := hn
  -- the prime of `z` and the fibre through it
  let 𝔮 : PrimeSpectrum Γ(Z, V) := hV.primeIdealOf ⟨z, hz⟩
  let 𝔭 : PrimeSpectrum Γ(S, U) := PrimeSpectrum.comap (algebraMap Γ(S, U) Γ(Z, V)) 𝔮
  let k := 𝔭.asIdeal.ResidueField
  have hne : Nonempty (PrimeSpectrum (𝔭.asIdeal.Fiber Γ(Z, V))) :=
    ⟨PrimeSpectrum.preimageEquivFiber Γ(S, U) Γ(Z, V) 𝔭 ⟨𝔮, rfl⟩⟩
  have : Nontrivial (k ⊗[Γ(S, U)] Γ(Z, V)) := PrimeSpectrum.nonempty_iff_nontrivial.mp hne
  obtain ⟨hφinj, -, -⟩ := fibre_invariants Γ(S, U) Γ(Z, V) Γ(X, q ⁻¹ᵁ V) ι hι G hfix hinv hcard k
  have : Nontrivial (k ⊗[Γ(S, U)] Γ(X, q ⁻¹ᵁ V)) := by
    refine ⟨⟨0, 1, fun h => zero_ne_one (α := k ⊗[Γ(S, U)] Γ(Z, V)) (hφinj ?_)⟩⟩
    rw [map_zero, map_one, h]
  have h1 := ringKrullDim_of_isStandardSmoothOfRelativeDimension n k (k ⊗[Γ(S, U)] Γ(Z, V))
  have h2 := ringKrullDim_fibre_eq Γ(S, U) Γ(Z, V) Γ(X, q ⁻¹ᵁ V) ι hι G hfix hinv hcard k
  have h3 := ringKrullDim_tensor_eq_one Γ(S, U) Γ(X, q ⁻¹ᵁ V) k
  rw [h2, h3] at h1
  exact_mod_cast h1.symm

end Setup

/-! ## The main theorem -/

theorem isUnit_card_Zloc (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : ¬ p ∣ n) : IsUnit ((n : ℕ) : Zloc p) := by
  have hmem : (n : ℤ) ∈ (pIdeal p).primeCompl := by
    intro h
    apply hn
    have := Ideal.mem_span_singleton.mp h
    exact_mod_cast this
  have := IsLocalization.map_units (Zloc p) (⟨(n : ℤ), hmem⟩ : (pIdeal p).primeCompl)
  simpa using this

/-- **`TameQuotientSmoothRelDim` from the chain's field `RegularSmoothPerfect`** (Stacks 00TV; no new leaf). -/
theorem tameQuotientSmoothRelDim_of_regularSmoothPerfect (hRS : RegularSmoothPerfect) :
    TameQuotientSmoothRelDim := by
  intro p _ 𝒴 𝒵 q hP hS G hGf hpG hover hq hqf
  haveI := hqf; haveI := hP; haveI := hS
  letI : Fintype G := Fintype.ofFinite G
  have hw : q.left ≫ 𝒵.hom = 𝒴.hom := Over.w q
  haveI : IsNoetherianRing (Zloc p) :=
    IsLocalization.isNoetherianRing (pIdeal p).primeCompl (Zloc p) inferInstance
  have : IsAffineHom q.left := hq.2.1
  haveI : LocallyOfFiniteType 𝒵.hom :=
    QuotProper.locallyOfFiniteType_of_isGQuotient G q.left 𝒴.hom 𝒵.hom hw hq
  have hunit : ∀ U : (Spec (CommRingCat.of (Zloc p))).Opens, IsUnit ((Fintype.card G : ℕ) : Γ(Spec (CommRingCat.of (Zloc p)), U)) := by
    intro U
    have h0 : IsUnit ((Fintype.card G : ℕ) : Zloc p) := by
      apply isUnit_card_Zloc p
      rwa [← Nat.card_eq_fintype_card]
    have := h0.map ((Scheme.ΓSpecIso (CommRingCat.of (Zloc p))).inv ≫
      (Spec (CommRingCat.of (Zloc p))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
    rwa [map_natCast] at this
  -- smoothness, on the affine opens of `𝒵` over `⊤`
  have hsm : Smooth 𝒵.hom := by
    have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of (Zloc p))).Opens) := isAffineOpen_top _
    have : IsNoetherianRing Γ(Spec (CommRingCat.of (Zloc p)), ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, hU⟩
    have hperf : ∀ (I : Ideal Γ(Spec (CommRingCat.of (Zloc p)), ⊤)) [I.IsPrime], PerfectField I.ResidueField := fun I _ =>
      perfectField_residueField (M := (pIdeal p).primeCompl) (R₀ := Zloc p)
        (Scheme.ΓSpecIso (CommRingCat.of (Zloc p))).inv.hom
        (Scheme.ΓSpecIso (CommRingCat.of (Zloc p))).commRingCatIsoToRingEquiv.symm.surjective I
    refine HasRingHomProperty.of_iSup_eq_top (P := @Smooth) (fun V : 𝒵.left.affineOpens => V)
      (iSup_affineOpens_eq_top 𝒵.left) (fun V => ?_)
    exact smooth_appLE q.left 𝒴.hom 𝒵.hom hw G hover hRS hq ⊤ hU V.1 V.2 le_top (hunit ⊤) hperf
  -- relative dimension `1`, on standard smooth charts
  constructor
  intro z
  obtain ⟨U, hU, V, hV, hzV, e, hst⟩ := Smooth.exists_isStandardSmooth 𝒵.hom z
  letI := (𝒵.hom.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of (Zloc p)), U) Γ(𝒵.left, V) := hst
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h'.out
  have hP := P.isStandardSmoothOfRelativeDimension rfl
  have hn : P.dimension = 1 :=
    relDim_eq_one q.left 𝒴.hom 𝒵.hom hw G hover hq U hU V hV e (hunit U) z hzV P.dimension hP
  exact ⟨U, hU, V, hV, hzV, e, hn ▸ hP⟩

end HDec.MCRGlue.TameQuotScheme

namespace HDec.MCRGlue

/-- **The smoothness half of mcr-glue's L3, proved** from the chain's textbook field `regularSmoothPerfect`
(Stacks 00TV). -/
theorem tameQuotientSmoothRelDim_of_regularSmoothPerfect (hRS : _root_.CurveSplit.RegularSmoothPerfect) :
    TameQuotientSmoothRelDim :=
  TameQuotScheme.tameQuotientSmoothRelDim_of_regularSmoothPerfect hRS

/-- **mcr-glue's L3 (`TameQuotientSmooth`), proved** from `regularSmoothPerfect` (properness: p1-quot2's
`QuotProper`). -/
theorem tameQuotientSmooth_of_regularSmoothPerfect (hRS : _root_.CurveSplit.RegularSmoothPerfect) :
    TameQuotientSmooth :=
  tameQuotientSmooth_of_relDim (tameQuotientSmoothRelDim_of_regularSmoothPerfect hRS)

end HDec.MCRGlue
