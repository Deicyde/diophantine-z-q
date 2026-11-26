import ZInQKernel.Contrib.OneProof.C8DeRham.TwistDeRhamAssembly
import ZInQKernel.Contrib.OneProof.C8Manuscript.ConradInOrder
import ZInQKernel.Contrib.OneProof.ConradSerre.ConcreteLocal

/-! # C8: the actual Hom line, the cited local theorem, and the final match

First obtain the actual de Rham character. Read its local algebraic exponent
using the existing Conrad interface, remove the cyclotomic part and form the
finite ray-class character. Compare weights last. Internal lemmas needed by
the Hom calculation are kept separate from the literature boundary.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.PkgI4 (GaloisRep GaloisChar)

set_option maxHeartbeats 1600000 in
/-- A finite ray-class factor of the original global twist before comparing
weights; the original local twisting line is de Rham. -/
theorem factor_before_matching_from_kato
    (hExt : DeRhamExtends) (hRows : DeRhamHasRows) (hConj : ConjOfTraceIrredFive)
    (hKato : C8Kato.NewformGeometricComparison) (hR : HSyn.EigenformRepExists) (hDS : HSyn.DeligneSerreConseq)
    (hFD : HSyn.FrobeniusDense) (hConrad : ConradAppB)
    (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (ε : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ) (hN : 0 < N) (hk : 1 ≤ k) (hg : PkgI4.IsNormalizedEigenform g ε)
    (hirr : r.IsIrreducible) (h9 : G9Out r) (hatt : r.AttachedUpToTwist ψ ιC ιL g S) :
    ∃ (w : ℤ) (η : GaloisChar 5), (Set.range η.toHom).Finite ∧ HasRayClassFactor η ∧
      ψ.toHom = η.toHom * cycQ 5 ^ (-w) ∧
      ({0, -1} : Multiset ℤ) = ({0, 1 - k} : Multiset ℤ).map (· + w) ∧
      ∃ (E : IntermediateField ℚ_[5] (PadicAlgCl 5)) (_ : FiniteDimensional ℚ_[5] E)
        (χ : PkgI4.GQp 5 →* Eˣ),
        (∀ σ, (((χ σ : Eˣ) : E) : PadicAlgCl 5) = (ψ.toHom (PkgI4.decomp 5 σ) : PadicAlgCl 5)) ∧
        _root_.ZInQ.Contrib.G9.PkgI4.IsDeRham 5 (charRep χ) := by
  obtain ⟨_, E, hE, _, χ, w, hval, hdR, hHT, hshift⟩ :=
    local_twist_deRham_and_weight hExt hRows hConj hKato hR hDS hFD r N k ε g ψ ιC ιL S hN hk hg hirr h9 hatt
  have hcont : Continuous (fun σ => (((χ σ : Eˣ) : E) : PadicAlgCl 5)) := by
    have h₀ : Continuous (fun σ : PkgI4.GQp 5 => (ψ.toHom (PkgI4.decomp 5 σ) : PadicAlgCl 5)) :=
      Units.continuous_val.comp (ψ.continuous_toHom.comp
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[5])).continuous)
    exact (funext hval : _) ▸ h₀
  obtain ⟨a, ha⟩ := hConrad.1 5 E χ hcont ⟨w, hHT⟩
  have haw := locAlgExponentEqWeight_of_conradAppB hConrad 5 E χ w a hcont hHT ha
  subst a
  obtain ⟨η, hfin, heq⟩ := exists_finite_cyclotomic_factor 5
    inertiaAtPDecomp_proof minkowskiInertiaQ_proof ψ E χ w hval ha
  exact ⟨w, η, hfin, hasRayClassFactor_of_finite η hfin, heq, hshift, E, hE, χ, hval, hdR⟩

set_option maxHeartbeats 1600000 in
/-- The Pan/Berger receiver in manuscript order, with the named local-algebraic
input supplied by the landed Serre adapter. -/
theorem g12Out_from_kato_serre
    (hExt : DeRhamExtends) (hRows : DeRhamHasRows) (hConj : ConjOfTraceIrredFive)
    (hKato : C8Kato.NewformGeometricComparison) (hR : HSyn.EigenformRepExists) (hDS : HSyn.DeligneSerreConseq)
    (hFD : HSyn.FrobeniusDense) (hPB : PkgI4.PanBerger)
    (hSerre : SerreAppB.LocalArtin.serreA6OnIntegerUnits)
    (r : GaloisRep 5 2) (T : Finset ℕ) (hirr : r.IsIrreducible) (h9 : G9Out r)
    (h10 : G10Out r) (h11 : G11Out T r) : G12Out r := by
  obtain ⟨N, k, ε, g, hN, hk, hg, ψ, ιC, ιL, S, hatt⟩ :=
    hPB 5 (le_refl 5) r hirr (finitelyRamified_of_g11 h11) h9.1 h10 ⟨0, -1, by norm_num, h9.2⟩
  obtain ⟨w, η, hfin, _, heq, hshift, _⟩ := factor_before_matching_from_kato hExt hRows hConj
    hKato hR hDS hFD (SerreAppB.conradAppB_of_serreIntegerUnits hSerre)
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
