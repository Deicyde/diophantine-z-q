import ZInQKernel.Contrib.OneProof.QuotientP1Coordinate
import ZInQKernel.OneProof.H.TailZ30

/-!
# p1-quot: `QuotientP1Coordinate` from the chain's own fields for T5, `HeckeIrreducible` and `QMAutCard`

* `HeckeIrreducible` from the added field `deligneComponentsY3PrintedAb` alone, **without Mumford's rigidity**
  (`QuotientP1Proof.DeligneAb.heckeIrreducible_of_ab`): the Deligne witness `Y₀` is connected (the chain's orbit
  computation, with the clause list cut to the `ℚ̄`-point it uses), and `R1univProps` of any triple `Y` applied to
  the abelian scheme of `Y₀` gives a surjection `Y₀ → Y`. (The chain itself converts the leaf to the `R1fpProps`
  form with `mumfordRigidityCore`, `TailZ23`.)
* T5 from the textbook field `mumfordTorsionAlgClosed` (`AvSplit.torsionStructure_of_mumford`, as in `TailZ23`);
* `QMAutCard` from `QMCentralizerCM` (`QMSplit.Aut.qmAutCard_of`, TailU), itself from `QMCentralizerCMC` (proved by the
  contribution `QMLattice` from the textbook fields `uniformizationLeafAll`, `gagaMorphism`,
  `mumfordTorsionAlgClosed`, as in `TailZ30`) and T11(b) (`AVB2.t11b_of_exists` of the proved `t11bExists_lf8`).
-/

noncomputable section

namespace QuotientP1Proof.DeligneAb

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open ShimuraSplit

/-- `ShimuraSplit.y3Connected_of_deligne`, with the clause list replaced by the one clause it uses (a `ℚ̄`-point);
the body is verbatim. -/
theorem connected_of_pi0 (Y : Over (Spec (CommRingCat.of ℚ))) (y₀ : fieldPt Qbar ⟶ Y)
    (c : _root_.ConnectedComponents (baseQbar Y) ≃ (ZMod 3)ˣ)
    (hc : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (z : _root_.ConnectedComponents (baseQbar Y)),
        c (galActπ₀ Y σ z) = chi3 σ * c z) : ConnectedSpace Y.left := by
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨y₀.left (IsLocalRing.closedPoint _)⟩, fun U hU => ?_⟩
  let p : baseQbar Y ⟶ Y.left := pullback.fst _ _
  have hpsurj : Function.Surjective p := p.surjective
  let V : Set (baseQbar Y) := p ⁻¹' U
  have hV : IsClopen V := hU.preimage p.continuous
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hne0, hne1⟩ := hne
  obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.2 hne0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra hall
    exact hne1 (Set.eq_univ_of_forall fun a => by by_contra ha; exact hall ⟨a, ha⟩)
  obtain ⟨z, hz⟩ := hpsurj u
  obtain ⟨z', hz'⟩ := hpsurj u'
  have hzV : z ∈ V := by show p z ∈ U; rw [hz]; exact hu
  have hz'V : z' ∉ V := by show p z' ∉ U; rw [hz']; exact hu'
  -- labels of components inside `V`
  let T : Set (ZMod 3)ˣ := {t | ∃ w ∈ V, c (ConnectedComponents.mk w) = t}
  have hT : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ t ∈ T, chi3 σ * t ∈ T := by
    rintro σ t ⟨w, hw, rfl⟩
    refine ⟨galAct Y σ w, ?_, ?_⟩
    · show p (galAct Y σ w) ∈ U
      change (pullback.fst Y.hom sQbar) (galAct Y σ w) ∈ U
      rw [← Scheme.Hom.comp_apply, galAct_fst]; exact hw
    · rw [← hc σ]; rfl
  obtain ⟨σ, hσ⟩ := exists_chi3_neg
  have hzT : c (ConnectedComponents.mk z) ∈ T := ⟨z, hzV, rfl⟩
  rcases units_zmod3 (c (ConnectedComponents.mk z)) (c (ConnectedComponents.mk z')) with e | e
  · -- same component as `z`
    have hmk : ConnectedComponents.mk z' = ConnectedComponents.mk z := c.injective e
    rw [ConnectedComponents.coe_eq_coe'] at hmk
    exact hz'V (hV.connectedComponent_subset hzV hmk)
  · obtain ⟨w, hw, hwe⟩ := hT σ _ hzT
    rw [hσ, ← e] at hwe
    have hmk : ConnectedComponents.mk z' = ConnectedComponents.mk w := c.injective hwe.symm
    rw [ConnectedComponents.coe_eq_coe'] at hmk
    exact hz'V (hV.connectedComponent_subset hw hmk)

/-- `ShimuraGlue.deligneComponentsY3_of_printed`, for one `Y` (the body is verbatim). -/
theorem pi0_of_printed (Y : Over (Spec (CommRingCat.of ℚ))) (h : ShimuraGlue.DelignePi0 Y ShimuraGlue.K3) :
    ∃ c : _root_.ConnectedComponents (baseQbar Y) ≃ (ZMod 3)ˣ,
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (z : _root_.ConnectedComponents (baseQbar Y)),
        c (galActπ₀ Y σ z) = chi3 σ * c z := by
  obtain ⟨c, ε, hc⟩ := h
  refine ⟨c.trans ShimuraGlue.pi0K3Equiv.toEquiv, fun σ z => ?_⟩
  have := hc σ (ShimuraGlue.cycU σ.toRingEquiv) (fun v => ShimuraGlue.cycU_apply _ v) z
  simp only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, this, map_mul,
    map_zpow, ShimuraGlue.pi0K3Equiv_mk]
  rw [ShimuraGlue.chi_cycU ShimuraSplit.card_mu3, ShimuraGlue.zmod3_zpow]
  rfl

/-- `LeafQM.AV.phi_part` with only the clauses it uses (proper, smooth, a classifying family). -/
theorem phi_part' {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : R1univProps Y Φ) (hp' : IsProper Y'.hom) (hs' : SmoothOfRelativeDimension 1 Y'.hom)
    (hf' : R1famProps Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨𝒜', h𝒜'⟩ := hf'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜' s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm

/-- **`HeckeIrreducible` from the abelian-scheme Deligne leaf, without Mumford's rigidity.** The Deligne
witness `Y₀` (abelian-scheme clause list) is connected (the orbit computation); `R1univProps` of a triple `Y`
applied to the abelian scheme of `Y₀` (a `QMFamily`) gives `g : Y₀ → Y` with `Φ₀ = Φ ∘ g`, onto because `Φ₀` is
onto and `Φ` injective (as in `exists_surjective_of_R1fp`); so `Y` is connected, hence irreducible. -/
theorem heckeIrreducible_of_ab (hD : ShimuraGlue.DeligneComponentsY3PrintedAb) :
    HDec.PropTSGlue.HeckeIrreducible := by
  intro Y Φ π h1 _ _
  obtain ⟨Y₀, Φ₀, h0, hπ⟩ := hD
  obtain ⟨hp0, hs0, ⟨y₀⟩, -, hfam0, -⟩ := h0
  obtain ⟨c, hc⟩ := pi0_of_printed Y₀ hπ
  haveI : ConnectedSpace Y₀.left := connected_of_pi0 Y₀ y₀ c hc
  obtain ⟨g, hg⟩ := phi_part' h1.2.2.2.2.2 hp0 hs0
    (LeafQM.AV.R1UnivRigid.r1famProps_of_r1famAbProps hfam0)
  have hsurj : Function.Surjective g.left := by
    intro x
    let φ : CommRingCat.of ℚ ⟶ Y.left.residueField x :=
      Spec.preimage (Y.left.fromSpecResidueField x ≫ Y.hom)
    letI : Algebra ℚ (Y.left.residueField x) := φ.hom.toAlgebra
    let y : fieldPt (Y.left.residueField x) ⟶ Y :=
      Over.homMk (Y.left.fromSpecResidueField x) (by
        change _ = Spec.map φ
        exact (Spec.map_preimage _).symm)
    obtain ⟨y', hy'⟩ := (Φ₀ (Y.left.residueField x)).surjective (Φ _ y)
    have hyy : y' ≫ g = y := (Φ _).injective ((hg _ y').symm.trans hy')
    let s : (fieldPt (Y.left.residueField x)).left := IsLocalRing.closedPoint _
    refine ⟨y'.left s, ?_⟩
    have h1 : (y' ≫ g).left s = y.left s := by rw [hyy]
    rw [Over.comp_left, Scheme.Hom.comp_apply] at h1
    rw [h1]
    exact Y.left.fromSpecResidueField_apply x _
  haveI : ConnectedSpace Y.left := hsurj.connectedSpace g.left.continuous
  obtain ⟨hP, hS, -⟩ := h1
  exact HDec.TSHecke.irreducibleSpace_of_connected Y.hom hP hS

end QuotientP1Proof.DeligneAb

end

namespace HDec.MCRQuot

open MCRGlue

theorem quotientP1Coordinate_of_fields (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1)
    (hE : EdixhovenFixedSmooth2) (hMT : _root_.AvSplit.MumfordTorsionAlgClosed)
    (hD : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb)
    (hU : _root_.BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : _root_.ZInQ.HomLattice.GAGAMorphism) (h24 : CMStab24) :
    MCRGlue.QuotientP1Coordinate :=
  quotientP1Coordinate_of_printed hAF hQE hTS hP1 hE
    (_root_.AvSplit.torsionStructure_of_mumford hMT)
    (_root_.QuotientP1Proof.DeligneAb.heckeIrreducible_of_ab hD)
    (QMSplit.Aut.qmAutCard_of (QMSplit.Aut.qmCentralizerCM_of
      (QMLattice.qmCentralizerCMC_of hU hG hMT) (AVB2.t11b_of_exists HSyn.t11bExists_lf8)))
    h24

end HDec.MCRQuot
