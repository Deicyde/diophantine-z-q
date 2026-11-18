import ZInQKernel.Contrib.OneProof.LogPTranscendence
import ZInQKernel.Contrib.OneProof.BdRInvariants

/-!
# Transcendence of `log [p̃]`: the core is `log [p̃] ∉ Frac(B_max)` (task logp-transc)

Report: `docs/research/logp-transc.md`. With Fontaine's `B_dR^{G_{ℚ_p}} = ℚ_p`, proved in the tree in dimension form
(`BdRInv.bdRInvariantsPrinted_proof`), turned here into the element form (`bdr_invariant_eq_algebraMap`), the core
`LogCore` of `LogPTranscendence.lean` is the sharp statement `NotInFrac`: no `a ≠ 0`, `b` in `B` with `a · u = b`.
So `BergerBst.LogPTildeTranscendental` follows from `log [p̃] ∉ Frac(B_max)` (`logPTildeTranscendental_of_notInFrac`),
and is equivalent to it (`logPTildeTranscendental_iff_notInFrac`).
-/

noncomputable section

namespace HDec
namespace PkgI4
namespace LogPTransc

open Module BergerBst

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`B_dR^{G_{ℚ_p}} = ℚ_p`, element form**, from the tree's dimension form `dim_{ℚ_p} B_dR^{G_{ℚ_p}} = 1`. -/
theorem bdr_invariant_eq_algebraMap (y : BdR p) (hy : ∀ σ : GQp p, bdrAct p σ y = y) :
    ∃ c : ℚ_[p], y = algebraMap ℚ_[p] (BdR p) c := by
  have hdim : finrank ℚ_[p] (DeRhamPrint.bdrFix p ℚ_[p]) = 1 := by
    have := BdRInv.bdRInvariantsPrinted_proof p ℚ_[p]
    rw [this, finrank_self]
  have h1 : (1 : BdR p) ∈ DeRhamPrint.bdrFix p ℚ_[p] := fun σ => map_one _
  have hyF : y ∈ DeRhamPrint.bdrFix p ℚ_[p] := fun σ => hy _
  have hne : (⟨1, h1⟩ : DeRhamPrint.bdrFix p ℚ_[p]) ≠ 0 := by
    intro h0
    have h0' : (1 : BdR p) = 0 := congrArg Subtype.val h0
    obtain ⟨a, b, hab⟩ := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).exists_pair_ne
    have hz : ∀ c : BdR p, c = 0 := fun c => by rw [← mul_one c, h0', mul_zero]
    exact hab ((hz a).trans (hz b).symm)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨y, hyF⟩
  refine ⟨c, ?_⟩
  have h2 : c • (1 : BdR p) = y := congrArg Subtype.val hc
  rw [← h2, Algebra.algebraMap_eq_smul_one]

/-- **The core is `u ∉ Frac(B)`** (for any `B`, any `u`). -/
theorem logCore_iff_notInFrac (B : Subalgebra ℚ_[p] (BdR p)) (u : BdR p) :
    LogCore p B u ↔ NotInFrac p B u := by
  constructor
  · intro h a b ha he
    exact h a b ha 0 (fun σ => map_zero _) (by rw [sub_zero]; exact he)
  · exact logCore_of_notInFrac p B u (bdr_invariant_eq_algebraMap p)

/-- **`BergerBst.LogPTildeTranscendental` follows from `log [p̃] ∉ Frac(B_max)`.** -/
theorem logPTildeTranscendental_of_notInFrac
    (h : ∀ (p : ℕ) [Fact p.Prime], NotInFrac p (Bmax p) (toBdR p (logPTilde p))) :
    LogPTildeTranscendental :=
  logPTildeTranscendental_of_core fun p _ => (logCore_iff_notInFrac p _ _).mpr (h p)

/-- **`BergerBst.LogPTildeTranscendental` is equivalent to `log [p̃] ∉ Frac(B_max)`** (for every `p`). -/
theorem logPTildeTranscendental_iff_notInFrac :
    LogPTildeTranscendental ↔
      ∀ (p : ℕ) [Fact p.Prime], NotInFrac p (Bmax p) (toBdR p (logPTilde p)) := by
  refine ⟨fun ht p _ => ?_, logPTildeTranscendental_of_notInFrac⟩
  refine (logCore_iff_notInFrac p _ _).mp (logCore_of_transcendental p _ _ (fun y hy => ?_) (ht p))
  obtain ⟨c, rfl⟩ := bdr_invariant_eq_algebraMap p y hy
  exact Subalgebra.algebraMap_mem _ c

/-- **Over `B_cris`**: transcendence from `log [p̃] ∉ Frac(B_cris)`. -/
theorem transcendental_bcris_of_notInFrac {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : BmaxOne.IsGenEps p ε₀)
    (hc : NotInFrac p (FontaineSt.BcrisOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (FontaineSt.theta_xi' p))
      (toBdR p (logPTilde p))) :
    Transcendental (FontaineSt.BcrisOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (FontaineSt.theta_xi' p))
      (toBdR p (logPTilde p)) :=
  transcendental_bcris_of_core p h ((logCore_iff_notInFrac p _ _).mpr hc)

end LogPTransc
end PkgI4
end HDec

end
