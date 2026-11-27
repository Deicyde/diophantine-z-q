import ZInQKernel.Contrib.OneProof.ColmezTiltIso.Theta
import ZInQKernel.Contrib.G9.KerTheta

/-!
# Colmez's `R` over `O_{C_p}`: limits in `ℂ_p`, `θ⁺`, and the Galois action

Specialization of `Ring.lean` and `Theta.lean` to `O = 𝓞_ℂ_[p]`, Colmez's `O_{C_p}` (p. 632:
"C_p le complété p-adique de Q̄_p, O_{C_p} son anneau d'entiers").

* `tendsto_of_isPAdicLim`: a `p`-adic limit in `𝓞_ℂ_[p]` is a limit in `ℂ_p`. So the printed
  addition holds with `lim` read in `ℂ_p` (`tendsto_add_seq`), and the printed series for `θ`
  converges in `ℂ_p` to the tree's `θ` (`tendsto_printedThetaSum`).
* `thetaPlusCp_ofPlus_wittEquiv`: on the image of `W(R)` in `B_dR^+`, the tree's residue map
  `thetaPlusCp` is Colmez's `θ`; `thetaPlusCp_teichmuller`: `θ⁺([x]) = x^{(0)}`.
* `galAct σ`: the componentwise action of `σ ∈ G_{ℚ_p}` on `R` (`galAct_seq`), a ring map that
  corresponds to the tree's action `DR.preTiltMap p (oAct p σ)` on `PreTilt` (`colmezEquiv_galAct`),
  to `WittVector.map` of it on `W` (`wittEquiv_map_galAct`), and to the tree's actions
  `DR.bdrPlusMap p (oAct p σ)` on `B_dR^+` (`bdrPlusMap_ofLoc_wittEquiv`) and `bdrAct p σ` on
  `B_dR` (`bdrAct_wittEquiv`).
-/

namespace ZInQ.Contrib.ColmezTiltIso

set_option linter.unusedSectionVars false

open Ideal WittVector ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4

section Functorial

variable {R S : Type*} [CommRing R] [CommRing S] {p : ℕ} [Fact p.Prime]

/-- The componentwise map `(x^{(n)})_n ↦ (f(x^{(n)}))_n`. -/
def ColmezR.map (f : R →+* S) (x : ColmezR R p) : ColmezR S p :=
  ⟨fun n => f (x.seq n), fun n => by rw [← map_pow, x.pow_seq_succ]⟩

variable [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : R)}) R]
  [IsAdicComplete (span {(p : S)}) S]

/-- The componentwise map corresponds to the tree's functoriality `DR.preTiltMap` of the tilt. -/
theorem colmezEquiv_map (f : R →+* S) (x : ColmezR R p) :
    colmezEquiv (x.map f) = DR.preTiltMap p f (colmezEquiv x) :=
  Perfection.ext fun _ => rfl

/-- The componentwise map, as a ring map. -/
noncomputable def ColmezR.mapHom (f : R →+* S) : ColmezR R p →+* ColmezR S p :=
  (colmezEquiv (O := S) (p := p)).symm.toRingHom.comp
    ((DR.preTiltMap p f).comp (colmezEquiv (O := R) (p := p)).toRingHom)

theorem ColmezR.mapHom_apply (f : R →+* S) (x : ColmezR R p) : ColmezR.mapHom f x = x.map f := by
  apply (colmezEquiv (O := S) (p := p)).injective
  change colmezEquiv (colmezEquiv.symm _) = _
  rw [RingEquiv.apply_symm_apply, colmezEquiv_map]
  rfl

theorem ColmezR.mapHom_seq (f : R →+* S) (x : ColmezR R p) (n : ℕ) :
    (ColmezR.mapHom f x).seq n = f (x.seq n) := by
  rw [ColmezR.mapHom_apply]
  rfl

theorem colmezEquiv_mapHom (f : R →+* S) (x : ColmezR R p) :
    colmezEquiv (ColmezR.mapHom f x) = DR.preTiltMap p f (colmezEquiv x) := by
  rw [ColmezR.mapHom_apply, colmezEquiv_map]

theorem wittEquiv_map_mapHom (f : R →+* S) (w : WittVector p (ColmezR R p)) :
    wittEquiv (WittVector.map (ColmezR.mapHom f) w) =
      WittVector.map (DR.preTiltMap p f) (wittEquiv w) := by
  refine WittVector.ext fun n => ?_
  rw [coeff_wittEquiv, map_coeff, map_coeff, coeff_wittEquiv, colmezEquiv_mapHom]

end Functorial

variable (p : ℕ) [Fact p.Prime]

/-- A `p`-adic limit in `𝓞_ℂ_[p]` is a limit in `ℂ_p`. -/
theorem tendsto_of_isPAdicLim {a : ℕ → 𝓞_ℂ_[p]} {L : 𝓞_ℂ_[p]} (h : IsPAdicLim p a L) :
    Filter.Tendsto (fun m => (a m : ℂ_[p])) Filter.atTop (nhds (L : ℂ_[p])) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (Cp.norm_p_lt_one p)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (h k)
  refine ⟨M, fun m hm => ?_⟩
  have h1 := (Cp.mem_span_pow_iff p _ k).mp (hM m hm)
  rw [dist_eq_norm]
  push_cast at h1
  exact lt_of_le_of_lt h1 hk

/-- **The printed addition, with `lim` in `ℂ_p`** (Colmez, p. 632):
`(x+y)^{(n)} = lim_{m→∞} (x^{(n+m)}+y^{(n+m)})^{p^m}`. -/
theorem tendsto_add_seq (x y : ColmezR 𝓞_ℂ_[p] p) (n : ℕ) :
    Filter.Tendsto (fun m => ((x.seq (n + m) : ℂ_[p]) + (y.seq (n + m) : ℂ_[p])) ^ p ^ m)
      Filter.atTop (nhds ((x + y).seq n : ℂ_[p])) := by
  have h := tendsto_of_isPAdicLim p (ColmezR.add_seq_isPAdicLim x y n)
  push_cast at h
  exact h

/-- **The printed series for `θ` converges in `ℂ_p` to the tree's `θ`** (Colmez, p. 632):
`Σ_{n<N} p^n x_n^{(n)} → fontaineTheta (W(colmezEquiv) w)`. -/
theorem tendsto_printedThetaSum (w : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (p : ℂ_[p]) ^ n * ((w.coeff n).seq n : ℂ_[p]))
      Filter.atTop (nhds (fontaineTheta 𝓞_ℂ_[p] p (wittEquiv w) : ℂ_[p])) := by
  have h := tendsto_of_isPAdicLim p (isPAdicLim_colmezTheta w)
  simp only [printedThetaSum, colmezTheta_apply] at h
  push_cast at h
  exact h

/-- `θ[1/p]` on `W(O♭)`: `θ[1/p](w) = θ(w)`. -/
theorem fontaineThetaInvertP_algebraMap (w : WittVector p (PreTilt 𝓞_ℂ_[p] p)) :
    fontaineThetaInvertP 𝓞_ℂ_[p] p (algebraMap _ (Localization.Away (p : WittVector p
      (PreTilt 𝓞_ℂ_[p] p))) w) =
        algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])) (fontaineTheta 𝓞_ℂ_[p] p w) := by
  simp only [fontaineThetaInvertP, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq, RingHom.comp_apply]

/-- **The tree's `θ⁺ : B_dR^+ → ℂ_p` is Colmez's `θ`** on the image of `W(R)`. -/
theorem thetaPlusCp_ofPlus_wittEquiv (w : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :
    BdrKer.Cp.thetaPlusCp p (BdrKer.ofPlus 𝓞_ℂ_[p] p (algebraMap _ (Localization.Away
      (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) (wittEquiv w))) =
        (colmezTheta 𝓞_ℂ_[p] p w : ℂ_[p]) := by
  change BdrKer.Cp.awayEquivCp p (BdrKer.Cp.thetaPlus p _) = _
  rw [BdrKer.Cp.thetaPlus_ofPlus, fontaineThetaInvertP_algebraMap, AlgEquiv.commutes]
  rfl

/-- `θ⁺` applied to the image of `w ∈ W(R)` is the limit in `ℂ_p` of the printed series. -/
theorem tendsto_printedThetaSum_thetaPlusCp (w : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (p : ℂ_[p]) ^ n * ((w.coeff n).seq n : ℂ_[p]))
      Filter.atTop (nhds (BdrKer.Cp.thetaPlusCp p (BdrKer.ofPlus 𝓞_ℂ_[p] p (algebraMap _
        (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) (wittEquiv w))))) := by
  rw [thetaPlusCp_ofPlus_wittEquiv]
  exact tendsto_printedThetaSum p w

/-- **`θ⁺([x]) = x^{(0)}`** for the Teichmüller lift of `x ∈ R`. -/
theorem thetaPlusCp_teichmuller (x : ColmezR 𝓞_ℂ_[p] p) :
    BdrKer.Cp.thetaPlusCp p (BdrKer.ofPlus 𝓞_ℂ_[p] p (algebraMap _ (Localization.Away
      (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) (wittEquiv (teichmuller p x)))) =
        (x.seq 0 : ℂ_[p]) := by
  rw [thetaPlusCp_ofPlus_wittEquiv, colmezTheta_teichmuller]

/-! ### The Galois action -/

/-- The componentwise action of `σ ∈ G_{ℚ_p}` on `R`: `(σ x)^{(n)} = σ(x^{(n)})`. -/
noncomputable def galAct (σ : GQp p) : ColmezR 𝓞_ℂ_[p] p →+* ColmezR 𝓞_ℂ_[p] p :=
  ColmezR.mapHom (oAct p σ)

/-- **The action is componentwise**, through the tree's action `cpAct` of `G_{ℚ_p}` on `ℂ_p`. -/
theorem galAct_seq (σ : GQp p) (x : ColmezR 𝓞_ℂ_[p] p) (n : ℕ) :
    ((galAct p σ x).seq n : ℂ_[p]) = cpAct p σ (x.seq n) := by
  rw [galAct, ColmezR.mapHom_seq]
  rfl

/-- **Galois compatibility on `R`**: the componentwise action corresponds to the tree's action
`DR.preTiltMap p (oAct p σ)` on `PreTilt`. -/
theorem colmezEquiv_galAct (σ : GQp p) (x : ColmezR 𝓞_ℂ_[p] p) :
    colmezEquiv (galAct p σ x) = DR.preTiltMap p (oAct p σ) (colmezEquiv x) :=
  colmezEquiv_mapHom _ x

theorem wittEquiv_map_galAct (σ : GQp p) (w : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :
    wittEquiv (WittVector.map (galAct p σ) w) =
      WittVector.map (DR.preTiltMap p (oAct p σ)) (wittEquiv w) :=
  wittEquiv_map_mapHom _ w

/-- **Galois compatibility on `B_dR^+`**: the tree's action `DR.bdrPlusMap p (oAct p σ)` on the
image of `w ∈ W(R)` is the image of the componentwise action on `W(R)`. -/
theorem bdrPlusMap_ofLoc_wittEquiv (σ : GQp p) (w : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :
    DR.bdrPlusMap p (oAct p σ) (ofLoc p (algebraMap _ _ (wittEquiv w))) =
      ofLoc p (algebraMap _ _ (wittEquiv (WittVector.map (galAct p σ) w))) := by
  rw [bdrPlusMap_ofLoc, locMap_algebraMap, wittEquiv_map_galAct]

/-- **Galois compatibility on `B_dR`**: the same for the tree's action `bdrAct p σ`. -/
theorem bdrAct_wittEquiv (σ : GQp p) (w : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :
    bdrAct p σ (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (ofLoc p (algebraMap _ _
      (wittEquiv w)))) = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (ofLoc p (algebraMap _ _
        (wittEquiv (WittVector.map (galAct p σ) w)))) := by
  rw [bdrAct, DR.bdrMap, IsLocalization.map_eq, bdrPlusMap_ofLoc_wittEquiv]

end ZInQ.Contrib.ColmezTiltIso
