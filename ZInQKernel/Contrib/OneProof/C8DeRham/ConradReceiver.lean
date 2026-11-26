import ZInQKernel.Contrib.OneProof.C8DeRham.ManuscriptComparison

/-! # C8 with the original printed Conrad citation

The Serre route uses a checked implementation of the same Conrad interface.
This entry point instead takes the independently checked specialization of
Conrad's own printed statement, as in the manuscript. -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.PkgI4 (GaloisRep GaloisChar)

set_option maxHeartbeats 1600000 in
/-- Use the cited local theorem after identifying the actual de Rham Hom line.
Chebotarev density is supplied by the repository's proof, not assumed. -/
theorem g12Out_from_kato_conrad
    (hExt : DeRhamExtends) (hRows : DeRhamHasRows) (hConj : ConjOfTraceIrredFive)
    (hKato : C8Kato.NewformGeometricComparison) (hR : HSyn.EigenformRepExists) (hDS : HSyn.DeligneSerreConseq)
    (hPB : PkgI4.PanBerger) (hConrad : Bridges.ConradAppBPrint)
    (r : GaloisRep 5 2) (T : Finset ℕ) (hirr : r.IsIrreducible) (h9 : G9Out r)
    (h10 : G10Out r) (h11 : G11Out T r) : G12Out r := by
  obtain ⟨N, k, ε, g, hN, hk, hg, ψ, ιC, ιL, S, hatt⟩ :=
    hPB 5 (le_refl 5) r hirr (finitelyRamified_of_g11 h11) h9.1 h10 ⟨0, -1, by norm_num, h9.2⟩
  obtain ⟨w, η, hfin, _, heq, hshift, _⟩ := factor_before_matching_from_kato hExt hRows hConj
    hKato hR hDS HSyn.frobeniusDense_proved (Bridges.conradAppB_of_print hConrad)
    r N k ε g ψ ιC ιL S hN hk hg hirr h9 hatt
  have hs : ({w, w + 1 - k} : Multiset ℤ) = {0, -1} := by
    rw [hshift]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    congr 1
    · ring
    · congr 1; ring
  obtain ⟨hw, rfl⟩ := PkgI4.weight_match w k hk hs
  have heq' : ψ.toHom = η.toHom := by
    apply MonoidHom.ext
    intro σ
    have h := congrArg (fun f : PkgI4.GQ →* (PadicAlgCl 5)ˣ => f σ) heq
    simpa only [hw, neg_zero, MonoidHom.mul_apply, MonoidHom.zpow_apply, zpow_zero, mul_one] using h
  exact ⟨N, ε, g, ψ, ιC, ιL, S, hN, hg, heq'.symm ▸ hfin, hatt⟩

end HDec.G0Galois.C8Conrad.Manuscript
