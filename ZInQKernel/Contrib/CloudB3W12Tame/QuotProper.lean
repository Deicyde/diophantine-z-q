/-
Copied from task p1-quot3 (branch `wip/p1-quot3`, commit b533b204d640ee45ac924ee030497d427ec9926e), file
`ZInQKernel/Contrib/OneProof/QuotientP1/QuotProper.lean`, by the owner's task p1-quot3 (report docs/research/p1-quot3.md §2 on that branch; p1-quot2.md).
Changes for Cloud Worker 12 (task H-91): module path moved under `ZInQKernel.Contrib.CloudB3W12Tame`, every
declaration namespace renamed (`HDec.MCRGlue.QuotProper` → `HDec.CloudB3W12Tame.QuotProper`, the `HDec.MCRGlue` section → `HDec.CloudB3W12Tame` with `open HDec.MCRGlue`) so nothing clashes if p1-quot3 is folded later; no proof changed.
-/

import ZInQKernel.OneProof.H.TailW

/-!
# p1-quot2, helper: the quotient by a finite group is proper; mcr-glue's L3 reduced to its smoothness half

`HDec.CloudB3W12Tame.QuotProper`: for `q : X → Z` with `IsGQuotient G q` (mcr-glue's SGA 1 quotient) and `q` finite,
* `surjective_of_isGQuotient` (lying over on affine opens),
* `locallyOfFiniteType_of_isGQuotient` (Artin–Tate, Mathlib `fg_of_fg_of_fg`, over a locally noetherian base),
* `isSeparated_of_isGQuotient` (the diagonal of `Z` is the image of that of `X` under the universally closed
  `X ×_S X → Z ×_S Z`),
* `isProper_of_isGQuotient`.
`HDec.CloudB3W12Tame.TameQuotientSmoothRelDim` (glue: the smoothness half of L3) and
`HDec.CloudB3W12Tame.tameQuotientSmooth_of_relDim : TameQuotientSmoothRelDim → TameQuotientSmooth`.
docs/research/p1-quot2.md. -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace HDec.CloudB3W12Tame.QuotProper

open HDec.MCRGlue

/-- Artin–Tate for ring maps: `A → B → C` with `A` noetherian, `C` of finite type over `A`, and `B → C` finite
and injective: `B` is of finite type over `A`. -/
theorem finiteType_of_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
    (φ : A →+* B) (ψ : B →+* C) (hc : (ψ.comp φ).FiniteType) (hf : ψ.Finite)
    (hi : Function.Injective ψ) : φ.FiniteType := by
  algebraize [φ, ψ, ψ.comp φ]
  exact ⟨fg_of_fg_of_fg A B C hc.out hf.1 hi⟩

variable {X Z : Scheme.{0}} (G : Subgroup (Aut X)) (q : X ⟶ Z)

/-- **A quotient map with `q` integral is surjective** (lying over on each affine open). -/
theorem surjective_of_isGQuotient (hq : IsGQuotient G q) [IsIntegralHom q] : Surjective q := by
  obtain ⟨hinv, hA, hW⟩ := hq
  refine ⟨fun z => ?_⟩
  obtain ⟨_, ⟨W, hWa : IsAffineOpen W, rfl⟩, hzW, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hV : IsAffineOpen (q ⁻¹ᵁ W) := hWa.preimage q
  obtain ⟨P, hP⟩ : z ∈ Set.range hWa.fromSpec := by rw [hWa.range_fromSpec]; exact hzW
  have hinj := (hW W hWa).1
  have hint := q.isIntegral_app W hWa
  algebraize [(q.app W).hom]
  have hinj' : (⊥ : Ideal Γ(X, q ⁻¹ᵁ W)).under Γ(Z, W) ≤ P.asIdeal :=
    Ideal.comap_bot_le_of_injective _ hinj
  haveI : P.asIdeal.IsPrime := P.isPrime
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal ⊥ hinj'
  let x : Spec Γ(X, q ⁻¹ᵁ W) := ⟨Q, hQp⟩
  refine ⟨hV.fromSpec x, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec q hWa hV le_rfl
  have h2 := congrArg (fun φ : Spec Γ(X, q ⁻¹ᵁ W) ⟶ Z => φ x) h
  simp only [Scheme.Hom.comp_apply] at h2
  rw [← h2, ← hP]
  congr 1
  apply PrimeSpectrum.ext
  rw [Scheme.Hom.appLE_eq_app]
  exact hQ


/-- **The quotient is locally of finite type** over a locally noetherian base (Artin–Tate on affine opens). -/
theorem locallyOfFiniteType_of_isGQuotient {S : Scheme.{0}} [IsLocallyNoetherian S] (f : X ⟶ S) (g : Z ⟶ S)
    (hw : q ≫ g = f) [LocallyOfFiniteType f] (hq : IsGQuotient G q) [IsFinite q] :
    LocallyOfFiniteType g := by
  obtain ⟨hinv, hA, hW⟩ := hq
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)]
  intro U V e
  haveI := IsLocallyNoetherian.component_noetherian U
  have hV : IsAffineOpen (q ⁻¹ᵁ (V : Z.Opens)) := V.2.preimage q
  have hcomp := Scheme.Hom.appLE_comp_appLE q g U V (q ⁻¹ᵁ (V : Z.Opens)) e le_rfl
  have hft := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (q ≫ g) (hw ▸ inferInstance) U
    ⟨q ⁻¹ᵁ (V : Z.Opens), hV⟩ (le_rfl.trans ((TopologicalSpace.Opens.map q.base).map (homOfLE e)).le)
  rw [← hcomp, CommRingCat.hom_comp] at hft
  refine finiteType_of_comp _ _ hft ?_ ?_
  · rw [Scheme.Hom.appLE_eq_app]; exact q.finite_app V V.2
  · rw [Scheme.Hom.appLE_eq_app]; exact (hW V V.2).1

/-- **The quotient is separated** if `X` is: the diagonal of `Z` is the image of the diagonal of `X` under the
universally closed `X ×_S X → Z ×_S Z`. -/
theorem isSeparated_of_isGQuotient {S : Scheme.{0}} (f : X ⟶ S) (g : Z ⟶ S) (hw : q ≫ g = f)
    [IsSeparated f] [UniversallyClosed q] [Surjective q] : IsSeparated g := by
  let m := pullback.map f f g g q q (𝟙 S) ((Category.comp_id _).trans hw.symm)
    ((Category.comp_id _).trans hw.symm)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) inferInstance inferInstance hw.symm hw.symm
  have hnat : pullback.diagonal f ≫ m = q ≫ pullback.diagonal g := by
    apply pullback.hom_ext <;> simp [m]
  have hrange : Set.range (pullback.diagonal g) = m '' Set.range (pullback.diagonal f) := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ := q.surjective z
      refine ⟨pullback.diagonal f y, ⟨y, rfl⟩, ?_⟩
      rw [← Scheme.Hom.comp_apply, hnat, Scheme.Hom.comp_apply]
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨q y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hnat, Scheme.Hom.comp_apply]
  have hcl : IsClosed (Set.range (pullback.diagonal g)) := by
    rw [hrange]
    exact m.isClosedMap _ (pullback.diagonal f).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hcl⟩

/-- **The quotient of a proper scheme by a finite group (with `q` finite) is proper** over a locally
noetherian base. -/
theorem isProper_of_isGQuotient {S : Scheme.{0}} [IsLocallyNoetherian S] (f : X ⟶ S) (g : Z ⟶ S)
    (hw : q ≫ g = f) [IsProper f] (hq : IsGQuotient G q) [IsFinite q] : IsProper g := by
  haveI : Surjective q := surjective_of_isGQuotient G q hq
  haveI : UniversallyClosed (q ≫ g) := hw ▸ inferInstance
  haveI : UniversallyClosed g := UniversallyClosed.of_comp_surjective q g
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_isGQuotient G q f g hw hq
  haveI : IsSeparated g := isSeparated_of_isGQuotient q f g hw
  exact {}

end HDec.CloudB3W12Tame.QuotProper

namespace HDec.CloudB3W12Tame

open HDec.MCRGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue

/-- **Glue (L3-smooth): the tame quotient is smooth of relative dimension 1** (the smoothness half of mcr-glue's
composite L3 `TameQuotientSmooth`, whose properness half is proved in `QuotProper.isProper_of_isGQuotient`). Same
hypotheses as L3. Sources (composite; locators UNVERIFIED): tame quotients commute with base change (Reynolds
operator; SGA 1 Exp. V Prop. 1.9, Mumford, *Abelian Varieties* §7 Thm 3), so the fibres of `𝒵` are the quotients
`𝒴_s/G`, normal curves over the perfect fields `𝔽_p`, `ℚ`, hence smooth (Stacks 00TV); `𝒵` is flat over
`ℤ_(p)` (torsion-free), so smooth (EGA IV 17.5.1). -/
def TameQuotientSmoothRelDim : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    ∀ G : Subgroup (Aut 𝒴.left), Finite G → ¬ p ∣ Nat.card G →
    (∀ g ∈ G, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) → IsGQuotient G q.left → IsFinite q.left →
    SmoothOfRelativeDimension 1 𝒵.hom

/-- **mcr-glue's L3 from its smoothness half** (properness of the quotient proved). -/
theorem tameQuotientSmooth_of_relDim (h : TameQuotientSmoothRelDim) : TameQuotientSmooth := by
  intro p _ 𝒴 𝒵 q h1 h2 G hG hp hover hq hf
  haveI := hf
  haveI := h1
  exact ⟨QuotProper.isProper_of_isGQuotient G q.left 𝒴.hom 𝒵.hom (Over.w q) hq,
    h p 𝒴 𝒵 q h1 h2 G hG hp hover hq hf⟩

end HDec.CloudB3W12Tame

