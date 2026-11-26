import ZInQKernel.Contrib.OneProof.C8Manuscript.AttachedTwist
import ZInQKernel.Contrib.OneProof.C8Manuscript.CyclotomicFactor
import ZInQKernel.Contrib.OneProof.ConradB3Verbatim

/-! # C8 from the cited Appendix B before matching the modular weights

Conrad's author preprint of December 11, 2011, p. 32 (Def. B.1 and the
following Tate equivalence), p. 33 (Prop. B.3; proof pp. 33–34) applies to a
continuous rank-one character with finite coefficients. We use only the case
`L = ℚ₅`. The germ with arithmetic reciprocity is `u ↦ u^(-a)`, where `a` is
Conrad's weight; in the manuscript's convention `w = -a`.

The project’s existing coefficient and Artin bridges convert the cited
formulation to the arithmetic unit equations. The finite character is
constructed before the weight match, with the actual cyclotomic character.
This uses the Hodge–Tate consequence needed by Conrad; the separate statement
of de Rham admissibility of the Hom line is not asserted here.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.PkgI4 (GaloisRep GaloisChar)

/-- The finite residual character is a ray-class character over `ℚ`: its
values on the whole Galois group factor through `(ℤ/m)ˣ` via the actual
mod-`m` cyclotomic character. -/
def HasRayClassFactor (η : GaloisChar 5) : Prop :=
  ∃ (m : ℕ+) (δ : DirichletCharacter (PadicAlgCl 5) m),
    ∀ σ : PkgI4.GQ, (η.toHom σ : PadicAlgCl 5) = δ ((TSkolemKW.KW.cycChar m σ : (ZMod m)ˣ) : ZMod m)

/-- The proved rational Kronecker–Weber theorem supplies the ray-class factor. -/
theorem hasRayClassFactor_of_finite (η : GaloisChar 5) (hfin : (Set.range η.toHom).Finite) :
    HasRayClassFactor η :=
  TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic HSyn.t17_proved η.toHom
    (TSkolemKW.KW.isOpen_ker_of_continuous η.toHom η.continuous_toHom hfin)

set_option maxHeartbeats 1500000 in
/-- The factorization of the actual Pan twist, along with the weight-shift
equation. In particular the factorization does not require `k = 2` or `w = 0`.
The finite image assertion is obtained before the final weight comparison. -/
theorem factorBeforeWeightComparison_of_conrad
    (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT) (hDS : HSyn.DeligneSerreConseq)
    (hFD : HSyn.FrobeniusDense) (hBN : HSyn.BrauerNesbitt) (hC : ConradAppB)
    (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ) (hN : 0 < N) (hk : 1 ≤ k) (hg : PkgI4.IsNormalizedEigenform g χ)
    (hirr : r.IsIrreducible) (hw : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1})
    (hatt : r.AttachedUpToTwist ψ ιC ιL g S) :
    ∃ (w : ℤ) (η : GaloisChar 5), (Set.range η.toHom).Finite ∧ HasRayClassFactor η ∧
      ψ.toHom = η.toHom * cycQ 5 ^ (-w) ∧
      ({0, -1} : Multiset ℤ) = ({0, 1 - k} : Multiset ℤ).map (· + w) := by
  obtain ⟨ρ, hρ, hline, hram, E, hE, hEg, ψE, w, hlift, hwt, hshift⟩ :=
    attachedTwistHTBeforeComparison hR hHT hDS hFD hBN r N k χ g ψ ιC ιL S hN hk hg hirr hw hatt
  have hcont : Continuous (fun σ => (((ψE σ : Eˣ) : E) : PadicAlgCl 5)) := by
    have h₀ : Continuous (fun σ : PkgI4.GQp 5 => (ψ.toHom (PkgI4.decomp 5 σ) : PadicAlgCl 5)) :=
      Units.continuous_val.comp (ψ.continuous_toHom.comp
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[5])).continuous)
    exact (funext hlift : _) ▸ h₀
  obtain ⟨a, ha⟩ := hC.1 5 E ψE hcont ⟨w, hwt⟩
  have haw : a = w := locAlgExponentEqWeight_of_conradAppB hC 5 E ψE w a hcont hwt ha
  subst a
  obtain ⟨η, hfin, heq⟩ := exists_finite_cyclotomic_factor 5
    inertiaAtPDecomp_proof minkowskiInertiaQ_proof ψ E ψE w hlift ha
  exact ⟨w, η, hfin, hasRayClassFactor_of_finite η hfin, heq, hshift⟩

/-- The final comparison is applied after obtaining the finite factor. The
input citation is the available `ℚ_p` specialization of Conrad's printed
statements, not the weight-zero specialization of a different theorem. -/
theorem weightTwo_and_finiteTwist_of_conradPrint
    (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT) (hDS : HSyn.DeligneSerreConseq)
    (hFD : HSyn.FrobeniusDense) (hBN : HSyn.BrauerNesbitt) (hConrad : Bridges.ConradAppBPrint)
    (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ) (hN : 0 < N) (hk : 1 ≤ k) (hg : PkgI4.IsNormalizedEigenform g χ)
    (hirr : r.IsIrreducible) (hw : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1})
    (hatt : r.AttachedUpToTwist ψ ιC ιL g S) :
    k = 2 ∧ (Set.range ψ.toHom).Finite := by
  obtain ⟨w, η, hfin, hRay, heq, hshift⟩ := factorBeforeWeightComparison_of_conrad hR hHT hDS hFD hBN
    (Bridges.conradAppB_of_print hConrad) r N k χ g ψ ιC ιL S hN hk hg hirr hw hatt
  have hweights : ({w, w + 1 - k} : Multiset ℤ) = {0, -1} := by
    rw [hshift]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    congr 1
    · ring
    · congr 1; ring
  obtain ⟨hwzero, hk₂⟩ := PkgI4.weight_match w k hk hweights
  refine ⟨hk₂, ?_⟩
  have heq' : ψ.toHom = η.toHom := by
    apply MonoidHom.ext
    intro σ
    have h := congrArg (fun f : PkgI4.GQ →* (PadicAlgCl 5)ˣ => f σ) heq
    simpa only [hwzero, neg_zero, MonoidHom.mul_apply, MonoidHom.zpow_apply, zpow_zero, mul_one] using h
  rw [heq']
  exact hfin

end HDec.G0Galois.C8Conrad.Manuscript
