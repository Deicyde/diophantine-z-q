import ZInQKernel.Contrib.OneProof.GaRigidity
import ZInQKernel.Contrib.OneProof.SGA7IX33Cor
import ZInQKernel.Contrib.OneProof.UnipotentForward

/-!
# ga-rigidity: the two SGA 7 IX rows with semistability read as in SGA 7 IX Déf. 3.4 ("no `𝔾_a`")

The fields `sga7_IX_Cor3_3` (`SGA33Steps.SGA7_IX_Cor3_3`) and `sga7_IX_3_5_ForwardGeom`
(`UnipotentForward.SGA7_IX_3_5_ForwardGeom`) read "semistable reduction" as `GroupModelO.IsSemistable`: the identity
component of the geometric special fibre is an extension of an abelian variety by a split torus
(`ZInQ.HeightSplit.HasSemiAbelianIdentityComponent`). Per the queue11 reviewer verdict, SGA 7 I Exp. IX Déf. 3.4 (via
Déf. 2.1.5) states the condition as "the identity component of the geometric special fibre contains no subgroup
isomorphic to `𝔾_a`" (locators UNVERIFIED here, no network), and the extension form reaches it only through rigidity.

`GaRigidity` (`ZInQKernel/Contrib/OneProof/GaRigidity.lean`) proves that rigidity:
`GaRigidity.noGaSubgroup_of_semiAbelian`. This file

* defines the printed condition `NoGaInIdComp G` (no homomorphism `𝔾_a → G` that is a closed immersion with image in
  the identity component `G⁰ = CToPrinted.idCompSet G`), `IsSemistableDef34 𝒩` and `HasSemistableReductionDef34 A O`;
* proves `IsSemistable → IsSemistableDef34` (`isSemistableDef34_of_isSemistable`, from rigidity);
* states the two rows with Déf. 3.4's hypothesis, `SGA7_IX_Cor3_3_Def34` and `SGA7_IX_3_5_ForwardGeom_Def34`
  (character for character the old statements with only the semistability hypothesis replaced), and proves each
  field, statement unchanged, from its new form (`sga7_IX_Cor3_3_of_def34`, `sga7_IX_3_5_ForwardGeom_of_def34`).

No `sorry`, no `axiom`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsInertia)
open CToPrinted ReductSplit ReductGlue ZInQ.HeightSplit UnipotentForward SGA33Steps GaRigidity

namespace GaRigidity.SGA7

/-! ## The printed condition and the dictionary -/

/-- **SGA 7 I Exp. IX Déf. 3.4 / 2.1.5's condition** on a group scheme `G` over an algebraically closed field
(applied to the geometric special fibre of a Néron model): the identity component `G⁰` contains no subgroup scheme
isomorphic to `𝔾_a`, i.e. no homomorphism `𝔾_a → G` of group schemes (`GaRigidity.IsGaHom`) is a closed immersion with
image in `G⁰ = idCompSet G` (the connected component of the unit). Locators per the queue11 reviewer verdict,
UNVERIFIED here. -/
def NoGaInIdComp {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] : Prop :=
  ∀ g : algPt k (Polynomial k) ⟶ G, IsGaHom G g → IsClosedImmersion g.left →
    Set.range g.left ⊆ idCompSet G → False

theorem noGaInIdComp_of_noGaSubgroup {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    (h : NoGaSubgroup G) : NoGaInIdComp G :=
  fun g hg hc _ => h g hg hc

section Defs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}

/-- **Semistable special fibre, Déf. 3.4's form**: the identity component of the geometric special fibre `𝒩 ×_O κ̄`
contains no `𝔾_a`. -/
def IsSemistableDef34 (𝒩 : GroupModelO A O) : Prop :=
  NoGaInIdComp (geomSpecialFibre 𝒩)

/-- `A` has semistable reduction at `O` in Déf. 3.4's form: a Néron model whose geometric special fibre has no `𝔾_a`
in its identity component. -/
def HasSemistableReductionDef34 (A : PkgI3.AbVar K) (O : ValuationSubring K) : Prop :=
  ∃ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel ∧ IsSemistableDef34 𝒩

/-- **The dictionary (rigidity)**: the kernel's semistability (extension of an abelian variety by a split torus) gives
Déf. 3.4's (no `𝔾_a`). -/
theorem isSemistableDef34_of_isSemistable (𝒩 : GroupModelO A O) (h : 𝒩.IsSemistable) : IsSemistableDef34 𝒩 :=
  noGaInIdComp_of_noGaSubgroup _ (noGaSubgroup_of_semiAbelian _ h)

theorem hasSemistableReductionDef34_of_has (h : HasSemistableReduction A O) : HasSemistableReductionDef34 A O := by
  obtain ⟨𝒩, h1, h2⟩ := h
  exact ⟨𝒩, h1, isSemistableDef34_of_isSemistable 𝒩 h2⟩

end Defs

/-! ## SGA 7 IX Cor. 3.3 with Déf. 3.4's hypothesis -/

/-- **LEAF `SGA7_IX_Cor3_3_Def34`** (Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exp. IX, LNM 288 (1972),
Cor. 3.3, p. 348; semistable reduction Déf. 3.4, p. 349, whose condition is read through Déf. 2.1.5 as "the identity
component of the geometric special fibre contains no `𝔾_a`" per the queue11 reviewer verdict; locators from the
sga33-steps brief, UNVERIFIED here). `SGA33Steps.SGA7_IX_Cor3_3` word for word, with the hypothesis
`𝒩.IsSemistable` replaced by Déf. 3.4's `IsSemistableDef34 𝒩`. -/
def SGA7_IX_Cor3_3_Def34 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] (O' : ValuationSubring K') [IsDiscreteValuationRing O']
    (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → IsSemistableDef34 𝒩 →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    ∀ u : bcO hO 𝒩.G ⟶ 𝒩'.G,
      (Over.pullback (jO O')).map u ≫ 𝒩'.gen.hom = (ReductGlue.bcDVR hO 𝒩).gen.hom →
    ∀ U : (bcO hO 𝒩.G).left.Opens,
      (U : Set (bcO hO 𝒩.G).left) =
        pullback.fst 𝒩.G.hom (Spec.map (CommRingCat.ofHom (comapHom hO))) ⁻¹' idCompSet 𝒩.G →
    ∀ W : 𝒩'.G.left.Opens, (W : Set 𝒩'.G.left) = idCompSet 𝒩'.G →
      ∃ e : (U : Scheme) ≅ (W : Scheme), e.hom ≫ W.ι = U.ι ≫ u.left

/-- **The field `sga7_IX_Cor3_3`, statement unchanged**, from Déf. 3.4's form and rigidity. -/
theorem sga7_IX_Cor3_3_of_def34 (h : SGA7_IX_Cor3_3_Def34) : SGA33Steps.SGA7_IX_Cor3_3 := by
  intro K _ O _ K' _ _ O' _ hO A 𝒩 h𝒩 hs 𝒩' h𝒩' u hu U hU W hW
  exact h K O K' O' hO A 𝒩 h𝒩 (isSemistableDef34_of_isSemistable 𝒩 hs) 𝒩' h𝒩' u hu U hU W hW

/-! ## SGA 7 IX Prop. 3.5 (forward) with Déf. 3.4's hypothesis -/

/-- **LEAF `SGA7_IX_3_5_ForwardGeom_Def34`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5, p. 350, (i) ⇒ (iv) at
`σ = τ`; semistable reduction as in Déf. 3.4 read through Déf. 2.1.5, "no `𝔾_a` in the identity component of the
geometric special fibre", per the queue11 reviewer verdict; locators UNVERIFIED here).
`UnipotentForward.SGA7_IX_3_5_ForwardGeom` word for word, with the hypothesis `HasSemistableReduction A O` replaced
by Déf. 3.4's `HasSemistableReductionDef34 A O`. -/
def SGA7_IX_3_5_ForwardGeom_Def34 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReductionDef34 A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0

/-- **The field `sga7_IX_3_5_ForwardGeom`, statement unchanged**, from Déf. 3.4's form and rigidity. -/
theorem sga7_IX_3_5_ForwardGeom_of_def34 (h : SGA7_IX_3_5_ForwardGeom_Def34) :
    UnipotentForward.SGA7_IX_3_5_ForwardGeom := by
  intro K _ O _ hO Ω _ _ _ w hw A ℓ _ hℓ hA σ hσ
  exact h K O hO Ω w hw A ℓ hℓ (hasSemistableReductionDef34_of_has hA) σ hσ

end GaRigidity.SGA7
