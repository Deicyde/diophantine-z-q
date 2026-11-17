import ZInQKernel.OneProof.H.TailD
import ZInQKernel.Contrib.OneProof.CarayolLevel

/-!
# r17-bypass: the consumer of `r17` needs only `CarayolLevel.CarayolLevelLe`

Check with `lake env lean scratch/r17-bypass/Bypass.lean`.

`G0ModNewform.g15` (TailA) is the only theorem of the route that applies `r17 : CarayolR17'`
(through `NewformLeaves.r17`). Here: `g15_of_levelLe`, the same conclusion `G15Out N u` from the
weakest form `CarayolLevelLe` (`v_p(N) ≤ a(ρ|G_{ℚ_p})` for `p ∣ N`, `p ≠ ℓ`), and the chain above it
(`g13_g16`, `g13_g16_ram`, `modularConstituent_tail`, `modularConstituent_tail_G`,
`G0AssembleMod.afterG7_of3`) re-proved with `CarayolLevelLe` in place of `CarayolR17'`. The last
step of a bypass fold, the G0 term of `TailK.lean:333`, is the integrator's (same term with
`afterG7_of3_levelLe`).
-/

noncomputable section

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

namespace G0ModNewform

open _root_.PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep GaloisChar)
open PkgI3 PkgI3.AbVar C9Rhof
open LeafModCurves hiding Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform
open CategoryTheory AlgebraicGeometry

/-- `factorization_eq_condAt` with `≤`, from `CarayolLevelLe` (for `p ∣ N`). -/
theorem factorization_le_condAt (hLe : CarayolLevel.CarayolLevelLe)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) {ℓ : ℕ} [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ) (r : GaloisRep ℓ 2)
    (ρ : GaloisRep ℓ 2) (hss : ρ.IsSemisimple) (hρ : ρ.AttachedTo ιC ιL f)
    (e : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ))
    (he : ∀ g v, e (toRep r g v) = toRep ρ g (e v)) (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (hpN : p ∣ N) (Lp : LadicCond.Fld p) (hL : LadicCond.IsAdapted Lp (r.restrictLocal p)) :
    (N.factorization p : ℚ) ≤ LadicCond.condAt Lp (r.restrictLocal p) := by
  have hint := restrictLocal_intertwine (p := p) r ρ e he
  have h1 := hLe ℓ ιC ιL N χ f ρ p hN hf hss hρ hpℓ hpN
  rw [LadicCond.condExp_eq_condAt (hSw p) (isAdapted_of_intertwine _ _ e hint Lp hL)] at h1
  rwa [condAt_eq_of_intertwine _ _ e hint Lp] at h1

/-- **G15 from the weakest form of R17** (GLUE, proved; as `g15`, with `CarayolLevelLe` for
`CarayolR17'`). -/
theorem g15_of_levelLe (hLe : CarayolLevel.CarayolLevelLe)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (h13 : G13Spec D N χ f) (h14 : G14Spec D N f)
    (u : ℚ) (hloc : G15LocalBounds D u) : G15Out N u := by
  obtain ⟨hN, hf, -⟩ := h13
  obtain ⟨⟨ρ5, hss5, hρ5, e5, he5⟩, ⟨ρ3, hss3, hρ3, e3, he3⟩⟩ := h14
  have key : ∀ p : ℕ, ∀ hp : p.Prime, p ∣ N → ∃ (Lp : @LadicCond.Fld p ⟨hp⟩) (c : ℚ),
      (N.factorization p : ℚ) ≤ c ∧ ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → c ≤ (ZInQ.heightE0 : ℚ)) ∧
      ((ZInQ.heightD : ℝ) < p → c ≤ 2) ∧
      (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → c = 0) := by
    intro p hp hpN
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases h5 : p = 5
    · obtain ⟨Lp, had, h1, h2, h3⟩ := (hloc p hp).2 h5
      exact ⟨Lp, _, factorization_le_condAt hLe hSw D.ιC D.ι3 N hN χ f hf D.r3 ρ3 hss3 hρ3 e3
        he3 p (by omega) hpN Lp had, h1, h2, h3⟩
    · obtain ⟨Lp, had, h1, h2, h3⟩ := (hloc p hp).1 h5
      exact ⟨Lp, _, factorization_le_condAt hLe hSw D.ιC D.ι5 N hN χ f hf D.r5 ρ5 hss5 hρ5 e5
        he5 p h5 hpN Lp had, h1, h2, h3⟩
  refine ⟨fun p hp hpR => ?_, fun p hp hpR => ?_, fun p hp hpN => ?_⟩
  · by_cases hpN : p ∣ N
    · obtain ⟨Lp, c, hc, h1, -, -⟩ := key p hp hpN
      have h : (N.factorization p : ℚ) ≤ (ZInQ.heightE0 : ℚ) := hc.trans (h1 hpR)
      exact_mod_cast h
    · rw [Nat.factorization_eq_zero_of_not_dvd hpN]
      exact Nat.zero_le _
  · by_cases hpN : p ∣ N
    · obtain ⟨Lp, c, hc, -, h2, -⟩ := key p hp hpN
      have h : (N.factorization p : ℚ) ≤ 2 := hc.trans (h2 hpR)
      exact_mod_cast h
    · rw [Nat.factorization_eq_zero_of_not_dvd hpN]
      exact Nat.zero_le _
  · by_contra hcon
    push_neg at hcon
    obtain ⟨Lp, c, hc, -, -, h3⟩ := key p hp hpN
    have h0 := h3 hcon.1 hcon.2
    rw [h0] at hc
    have hfac : N.factorization p ≤ 0 := by exact_mod_cast hc
    have hpos : 0 < N.factorization p := hp.factorization_pos_of_dvd hN.ne' hpN
    omega

/-- `NewformLeaves` without `r17` (the other nine fields, unchanged). -/
structure NewformLeavesNoR17 : Prop where
  t24 : PkgI4.EigenformTwist
  t25 : PkgI4.NewformOfEigenform
  r14 : PkgI4.EigenformRepExists
  r16 : R16_EichlerShimuraJ1'
  r9a : FaltingsSemisimple
  r9b : FaltingsTate
  m0 : TateModuleFree
  t18 : FrobeniusDense
  t19 : GlueC10.BrauerNesbittChar0

theorem NewformLeavesNoR17.of (lv : NewformLeaves) : NewformLeavesNoR17 :=
  ⟨lv.t24, lv.t25, lv.r14, lv.r16, lv.r9a, lv.r9b, lv.m0, lv.t18, lv.t19⟩

/-- `g13_g16` with `CarayolLevelLe` for `NewformLeaves.r17`. -/
theorem g13_g16_levelLe (lv : NewformLeavesNoR17) (hLe : CarayolLevel.CarayolLevelLe)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (D : ModData L A)
    (h12 : G12Spec D) (hc : G14TraceCompat D) (hloc : G15LocalBounds D u) : G16Out A u := by
  obtain ⟨N, χ, f, h13⟩ := g13 lv.t24 lv.t25 lv.r16 lv.r9a lv.r9b lv.m0 lv.t19 lv.t18 D h12
  have h14 := g14 lv.r14 lv.t19 lv.t18 D N χ f h13 hc
  have h15 := g15_of_levelLe hLe hSw D N χ f h13 h14 u hloc
  exact ⟨N, h13.1, g16 N h13.1 u h15, h13.2.2.2.2.2⟩

/-- `modularConstituent_tail_G` with `CarayolLevelLe` for `NewformLeaves.r17`. -/
theorem modularConstituent_tail_G_levelLe (lv : NewformLeavesNoR17)
    (hLe : CarayolLevel.CarayolLevelLe) (hJac : JacobianExists ℚ) (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, hram⟩ := h
  exact g16Out_with_J1 hJac hX u (g13_g16_levelLe lv hLe hSw u D h12 hc
    (g15LocalBounds_of_ram hL8 hAd D u (g15Ram_of_G D u hram)))

end G0ModNewform

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- `newformLeaves_of3` without R17. -/
theorem newformLeavesNoR17_of3 (r : ResearchLeaves3) (t : TextbookLeaves) :
    G0ModNewform.NewformLeavesNoR17 :=
  ⟨C9Rhof.eigenformTwist_of_hsyn t.t24, t.t25, C9Rhof.eigenformRepExists_of_hsyn r.r14, r.r16,
    r.r9a, r.r9b, t.t26, C9Rhof.frobeniusDense_of_hsyn t.frobeniusDense,
    TSkolemKW.C10.brauerNesbittChar0'⟩

/-- **`afterG7_of3` with the weakest form of R17** (`CarayolLevelLe` for `CarayolR17'`; the
body of `afterG7_of3`, TailD.lean:156, with `modularConstituent_tail_G_levelLe`). -/
theorem afterG7_of3_levelLe (r : ResearchLeaves3) (t : TextbookLeaves) (m : G0Galois.GaloisPieces)
    (h9 : G0Galois.G9GlueNoT23)
    (hDF : G0ModNewform.DirichletOfFinite) (hLe : CarayolLevel.CarayolLevelLe)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6) (hLink : LinkedTateData) : AfterG7 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h6, h3₅, h3₃⟩ := hG36 Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  obtain ⟨Tm₅, c₅, ε₅, a₅, β₅, u₅, Tm₃, c₃, ε₃, a₃, β₃, u₃, h7₅, h7₃, hlink⟩ :=
    hLink Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  have h2 : G0Galois.G2Out L' (T u) :=
    galoisG2Out_of_g7Data resQRange u P L A ε N χ β L' hLL' hdata
  obtain ⟨r₅, h8₅, -, -, h11₅, h12⟩ :=
    G0Galois.g8_g12_of_leaves3 r t m h9 _ (T u) h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, h8₃, -, -, h11₃⟩ :=
    G0Galois.g8_g11 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t11a
      t.t11b (G0Galois.g8Matrix_of_burnside m.burnside) h9 m.odd _ (T u) h2 h6 3 h3₃
      Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨i, ιC, ι5, hspec⟩ := G0ModNewform.g12Spec_of_galois hDF _ _ _ r₅ r₃ h8₅ h8₃ h12
  obtain ⟨ι3, h14, h15⟩ := hlink r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ :=
    G0ModNewform.modularConstituent_tail_G_levelLe (newformLeavesNoR17_of3 r t) hLe t.t33
      t.x1ModelExists hSw hL8 hAd _ u ⟨_, hspec ι3, h14, g15RamG_of_wild _ u h15 h11₅ h11₃⟩
  exact ⟨M, J, hM, hJ, hMle, (commonConstituent_copy' _ _).1 hCC⟩

/-- The original `afterG7_of3` is the special case (sanity check of the bypass). -/
example (r : ResearchLeaves3) (t : TextbookLeaves) (m : G0Galois.GaloisPieces)
    (h9 : G0Galois.G9GlueNoT23)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : _root_.LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6) (hLink : LinkedTateData) : AfterG7 :=
  afterG7_of3_levelLe r t m h9 hDF (CarayolLevel.carayolLevelLe_of_R17' hCar) hSw hL8 hAd hG36 hLink

end HSyn.G0AssembleMod

end HDec

#print axioms HDec.HSyn.G0AssembleMod.afterG7_of3_levelLe
#print axioms CarayolLevel.carayolR17'_of_newformRepConductor
