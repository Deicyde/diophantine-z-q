import ZInQKernel.Contrib.OneProof.C8DeRham.KatoWitness
import ZInQKernel.Contrib.OneProof.C8DeRham.FiniteImageDeRham
import ZInQKernel.Contrib.OneProof.C8Manuscript.AttachedTwist

/-! # The modular input before the C8 weight comparison

In weight one use Deligne–Serre and proved finite-image descent. In higher
weight apply Kato to a newform of the original eigensystem. Only good-prime
attachment is needed for the comparison; the original Pan eigenform is not
changed in the final conclusion.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.PkgI4 (GaloisRep GaloisChar)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- An attached comparison representation and both local properties, for the
same good-prime eigensystem. It is not assumed semisimple. If the Pan level is
not already new, the exceptional set is enlarged only by its prime divisors. -/
theorem exists_modular_comparison_of_kato
    (hKato : C8Kato.NewformGeometricComparison) (hR : HSyn.EigenformRepExists) (hDS : HSyn.DeligneSerreConseq)
    (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : PkgI4.GaloisChar 5)
    (ε : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ) (hN : 0 < N) (hk : 1 ≤ k) (hg : PkgI4.IsNormalizedEigenform g ε)
    (hatt : r.AttachedUpToTwist χ ιC ιL g S) :
    ∃ (M : ℕ) (f : PkgI4.CF M k) (S' : Finset ℕ) (ρ : GaloisRep 5 2),
      0 < M ∧ ρ.AttachedTo ιC ιL f ∧ r.AttachedUpToTwist χ ιC ιL f S' ∧
      PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ) 5 {0, 1 - k} ∧
      PkgI4.LocalIsDeRham 5 2 (ρ.restrictLocal 5) := by
  by_cases h1 : k = 1
  · subst k
    obtain ⟨ρH, hss, hρatt⟩ := hR 5 ιC ιL N 1 ε g hN le_rfl hg
    let ρ : GaloisRep 5 2 := ⟨ρH.toHom, ρH.continuous_toHom⟩
    have hfin : (Set.range ρH.toHom).Finite := hDS 5 ιC ιL ρH N ε g hN hg hss hρatt
    have hzero := HSyn.HodgeLF7.finiteImageHT
      (_root_.ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate
        _root_.ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
        _root_.ZInQ.Contrib.CloudB3W11.axSenTate_proof) 5 2 ρ hfin
    refine ⟨N, g, S, ρ, hN, hρatt, hatt, ?_, ?_⟩
    · simpa [Multiset.replicate_succ] using hzero
    · exact localIsDeRham_restrictLocal_of_finite_image 5 (HSyn.HodgeLF7.toG9Rep ρ) hfin
  · have hk₂ : 2 ≤ k := by omega
    obtain ⟨M, ε', f, hM, _, hf, hcoef⟩ := _root_.T25.newformOfEigenform_leaf N k ε g hN hg
    have hfg := _root_.NewformDict.g9_isNewform_iff_pkgI4.mpr hf
    obtain ⟨hMz, ff, he, _⟩ := (_root_.NewformDict.g9_isNewform_iff hM).mp hfg
    letI : NeZero M := hMz
    obtain ⟨ρ', hρ', hh, hd⟩ := C8Kato.arithmetic_witness_of_kato hKato 5 ιC ιL M k ff hk₂
    let ρ := HSyn.HodgeLF7.ofG9Rep ρ'
    have hρ : ρ.AttachedTo ιC ιL f := he ▸ hρ'
    refine ⟨M, f, S ∪ N.primeFactors, ρ, hM, hρ, ?_, hh, hd⟩
    intro q hq hqS
    have hs : q ∉ S := fun h => hqS (Finset.mem_union_left _ h)
    have hqN : ¬ q ∣ N := fun h => hqS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hq, h, hN.ne'⟩))
    obtain ⟨hu, a, ha, ht⟩ := hatt q hq hs
    exact ⟨hu, a, ha.trans (hcoef q hq hqN).symm, ht⟩

end HDec.G0Galois.C8Conrad.Manuscript
