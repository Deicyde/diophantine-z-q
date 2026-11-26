import ZInQKernel.Contrib.OneProof.C8DeRham.CommonHomModel
import ZInQKernel.Contrib.OneProof.C8Manuscript.CharDeRham
import ZInQKernel.Contrib.OneProof.C8DeRham.ModularComparison
import ZInQKernel.Contrib.OneProof.C8DeRham.GoodPrimeTrace

/-! # The de Rham Hom calculation before the weight comparison

The coefficient extension, period rows and trace-to-conjugacy interfaces
here describe internal proof obligations, not literary assumptions.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.PkgI4 (GaloisRep GaloisChar)
open C8HomModel

/-- Internal interface: de Rhamness is unchanged by extension of the
coefficient field. -/
def DeRhamExtends : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E F : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] F]
    (h : E ≤ F) {n : ℕ} (r : PkgI4.GQp p →* GL (Fin n) E),
    _root_.ZInQ.Contrib.G9.PkgI4.IsDeRham p r →
      _root_.ZInQ.Contrib.G9.PkgI4.IsDeRham p (extendModel h r)

/-- Internal interface: the actual de Rham rank supplies period rows on the
coefficient-fixing subgroup. -/
def DeRhamHasRows : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E] {n : ℕ}
    (r : PkgI4.GQp p →* GL (Fin n) E),
    _root_.ZInQ.Contrib.G9.PkgI4.IsDeRham p r → HasBdRRows p E r

/-- Internal interface: trace comparison with the irreducible Pan
representation. Kato's attached witness need not be assumed semisimple. -/
def ConjOfTraceIrredFive : Prop :=
  ∀ (r ρ : GaloisRep 5 2), r.IsIrreducible →
    (∀ σ, (r.mat σ).trace = (ρ.mat σ).trace) → IsConj r ρ

set_option maxHeartbeats 2800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The actual local twisting character is de Rham, with its integral HT
weight, before any comparison specializes the modular weight. The proof uses
the original invertible Hom intertwiner at the same coefficient model. -/
theorem local_twist_deRham_and_weight
    (hExt : DeRhamExtends) (hRows : DeRhamHasRows) (hConj : ConjOfTraceIrredFive)
    (hKato : C8Kato.NewformGeometricComparison) (hR : HSyn.EigenformRepExists) (hDS : HSyn.DeligneSerreConseq)
    (hFD : HSyn.FrobeniusDense)
    (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (ε : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ) (hN : 0 < N) (hk : 1 ≤ k) (hg : PkgI4.IsNormalizedEigenform g ε)
    (hirr : r.IsIrreducible) (h9 : G9Out r) (hatt : r.AttachedUpToTwist ψ ιC ιL g S) :
    (∃ S₀ : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S₀ → CharUnramifiedAt ψ q) ∧
    ∃ (E : IntermediateField ℚ_[5] (PadicAlgCl 5)) (_ : FiniteDimensional ℚ_[5] E)
      (_ : IsGalois ℚ_[5] E) (χ : PkgI4.GQp 5 →* Eˣ) (w : ℤ),
      (∀ σ, (((χ σ : Eˣ) : E) : PadicAlgCl 5) = (ψ.toHom (PkgI4.decomp 5 σ) : PadicAlgCl 5)) ∧
      _root_.ZInQ.Contrib.G9.PkgI4.IsDeRham 5 (charRep χ) ∧
      PkgI4.HasHTWeights 5 (charRep χ) {w} ∧
      ({0, -1} : Multiset ℤ) = ({0, 1 - k} : Multiset ℤ).map (· + w) := by
  obtain ⟨M, f, S', ρ, hM, hρ, hr', hmod, hmodDR⟩ :=
    exists_modular_comparison_of_kato hKato hR hDS r N k ψ ε g ιC ιL S hN hk hg hatt
  obtain ⟨ρ', htw⟩ := twistExists 5 2 ρ ψ
  have hc := hConj r ρ' hirr (trace_eq_of_attached_twist hFD r ρ ρ' ψ ιC ιL M f S' hM hρ hr' htw)
  obtain ⟨T, hT⟩ := equivariant_hom_line_of_conj r ρ ρ' ψ htw hc
  have hw' := htConj_of htExtend 5 2 r ρ' _ hc h9.2
  obtain ⟨C, hC, hCG, ψC, w, hψ, hHT, hshift⟩ :=
    actualTwistHT_and_shift 5 (n := 2) (by decide) (HSyn.HodgeLF7.toG9Rep ρ)
      (HSyn.HodgeLF7.toG9Rep ρ') (HSyn.HodgeLF7.toG9Char ψ) _ _ htw (by simp) (by simp) hmod hw'
  obtain ⟨R, hRfd, rR, hrR, hdR⟩ := h9.1
  obtain ⟨D, hDfd, ρD, hρD, hdD⟩ := hmodDR
  have hTloc (σ : PkgI4.GQp 5) :
      (Matrix.GeneralLinearGroup.map (algebraMap R (PadicAlgCl 5)) (rR σ) :
        Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) * (T : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) =
      (((ψC σ : Cˣ) : C) : PadicAlgCl 5) •
        ((T : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) *
          (↑(Matrix.GeneralLinearGroup.map (algebraMap D (PadicAlgCl 5)) (ρD σ)) :
            Matrix (Fin 2) (Fin 2) (PadicAlgCl 5))) := by
    rw [hrR, hρD, hψ]
    exact hT (PkgI4.decomp 5 σ)
  obtain ⟨E, hE, hEG, hRE, hDE, hCE, TE, _, hTE⟩ := exists_common_hom_model R D C rR ρD ψC T hTloc
  let χ := extendCharacter hCE ψC
  have hval (σ : PkgI4.GQp 5) : (((χ σ : Eˣ) : E) : PadicAlgCl 5) =
      (ψ.toHom (PkgI4.decomp 5 σ) : PadicAlgCl 5) := hψ σ
  have hrDR := hExt 5 R E hRE rR hdR
  have hρDR := hExt 5 D E hDE ρD hdD
  obtain ⟨c, hc₀, hperiod⟩ := exists_bdr_period_of_hom_line 5 E (n := 2) (by decide)
    (extendModel hRE rR) (extendModel hDE ρD) χ TE hTE
    (hRows 5 E _ hrDR) (hRows 5 E _ hρDR)
  have hDR := isDeRham_char_of_period_with_embedding 5 E χ (coeffToBdR 5 E)
    (bdrAct_coeffToBdR_restrict 5 E) c hc₀ hperiod
  have hHTE : PkgI4.HasHTWeights 5 (charRep χ) {w} := by
    let ρΩ := (Matrix.GeneralLinearGroup.map (algebraMap C (PadicAlgCl 5))).comp (charRep ψC)
    have hLift (σ : PkgI4.GQp 5) :
        Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl 5)) (charRep χ σ) = ρΩ σ := by
      apply Units.ext
      ext i j
      change ((Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl 5)) (charRep χ σ) :
        GL (Fin 1) (PadicAlgCl 5)) : Matrix (Fin 1) (Fin 1) (PadicAlgCl 5)) i j =
        ((Matrix.GeneralLinearGroup.map (algebraMap C (PadicAlgCl 5)) (charRep ψC σ) :
          GL (Fin 1) (PadicAlgCl 5)) : Matrix (Fin 1) (Fin 1) (PadicAlgCl 5)) i j
      rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
      have he : i = j := Subsingleton.elim i j
      subst j
      simp [charRep, Matrix.algebraMap_matrix_apply, χ, extendCharacter]
    intro v
    have he := _root_.ZInQ.Contrib.HodgeSplit.htMult_eq_of_lifts 5 ρΩ (charRep χ) (charRep ψC)
      hLift (fun _ => rfl) v
    exact he.trans (hHT v)
  exact ⟨attachedTwist_finitelyRamified r ρ M f ψ ιC ιL S' hM hρ hr' T hT,
    E, hE, hEG, χ, w, hval, hDR, hHTE, hshift⟩

end HDec.G0Galois.C8Conrad.Manuscript
