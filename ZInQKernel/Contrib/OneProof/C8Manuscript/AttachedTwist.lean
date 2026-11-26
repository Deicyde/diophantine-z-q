import ZInQKernel.Contrib.OneProof.C8Manuscript.TwistPeriod

/-! # Identify the actual twist before any weight comparison

The conjugating matrix from Chebotarev and Brauer–Nesbitt is the intertwiner
spanning the line in `Hom(ρ_g,r)`. We retain it and the actual local weight of
its scalar action. No comparison forcing `k = 2` occurs in this file.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.PkgI4 (GaloisRep GaloisChar)

/-- The matrix equation for the actual Hom line. A nonzero intertwiner
`P : ψ ⊗ ρ → r` satisfies `r(σ) P = ψ(σ) P ρ(σ)`. It thus spans a line
with character `ψ` for the conjugation action on the Hom space. -/
theorem equivariant_hom_line_of_conj {p n : ℕ} [Fact p.Prime]
    (r ρ ρ' : GaloisRep p n) (ψ : GaloisChar p)
    (htw : IsTwist ρ' ψ ρ) (hc : IsConj r ρ') :
    ∃ T : GL (Fin n) (PadicAlgCl p), ∀ σ,
      r.mat σ * (T : Matrix (Fin n) (Fin n) (PadicAlgCl p)) =
        (ψ.toHom σ : PadicAlgCl p) • ((T : Matrix (Fin n) (Fin n) (PadicAlgCl p)) * ρ.mat σ) := by
  obtain ⟨T, hT⟩ := hc
  refine ⟨T, fun σ => ?_⟩
  have he := congrArg (fun a : GL (Fin n) (PadicAlgCl p) =>
    ((a * T : GL (Fin n) (PadicAlgCl p)) : Matrix (Fin n) (Fin n) (PadicAlgCl p))) (hT σ)
  simp only [mul_assoc, inv_mul_cancel, mul_one, Units.val_mul] at he
  change r.mat σ * (T : Matrix (Fin n) (Fin n) (PadicAlgCl p)) = _ at he
  -- `he` is the matrix identity after multiplying on the right by `T`.
  change r.mat σ * (T : Matrix (Fin n) (Fin n) (PadicAlgCl p)) =
    (T : Matrix (Fin n) (Fin n) (PadicAlgCl p)) * ρ'.mat σ at he
  rw [he, htw σ, Matrix.mul_smul]

set_option maxHeartbeats 1000000 in
/-- The two attachment clauses give finite ramification of the same twist
spanning the Hom line. The exceptional set is `S ∪ {q | q ∣ 5N}`. -/
theorem attachedTwist_finitelyRamified
    (r ρ : GaloisRep 5 2) (N : ℕ) {k : ℤ} (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ) (hN : 0 < N) (hρ : ρ.AttachedTo ιC ιL g) (hr : r.AttachedUpToTwist ψ ιC ιL g S)
    (T : GL (Fin 2) (PadicAlgCl 5)) (hT : ∀ σ,
      r.mat σ * (T : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) =
        (ψ.toHom σ : PadicAlgCl 5) • ((T : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) * ρ.mat σ)) :
    ∃ S₀ : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S₀ → CharUnramifiedAt ψ q := by
  refine ⟨S ∪ (N * 5).primeFactors, fun q hq hqS v hv τ hτ => ?_⟩
  have hqS₁ : q ∉ S := fun h => hqS (Finset.mem_union_left _ h)
  have hqp : ¬ q ∣ N * 5 := fun h => hqS (Finset.mem_union_right _
    (Nat.mem_primeFactors.mpr ⟨hq, h, Nat.mul_ne_zero hN.ne' (by decide)⟩))
  have hrτ := (hr q hq hqS₁).1 v hv τ hτ
  have hρτ := (hρ q hq hqp).1 v hv τ hτ
  have he := hT (τ : PkgI4.GQ)
  change r.toHom (τ : PkgI4.GQ) = 1 at hrτ
  change ρ.toHom (τ : PkgI4.GQ) = 1 at hρτ
  simp only [PkgI4.GaloisRep.mat, hrτ, hρτ, Units.val_one, one_mul, mul_one] at he
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, (T : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) 0 j ≠ 0 := by
    by_contra! h
    exact Matrix.GeneralLinearGroup.det_ne_zero T (Matrix.det_eq_zero_of_row_eq_zero 0 h)
  have he₀ := congrFun (congrFun he 0) j
  simp only [Matrix.smul_apply, smul_eq_mul] at he₀
  apply Units.ext
  exact mul_right_cancel₀ hj (he₀.symm.trans (one_mul _).symm)

set_option maxHeartbeats 1800000 in
/-- At the actual Pan receiver and for every allowed eigenform weight, provide
the Hom line and Hodge–Tate witness. For weight one use Deligne–Serre finite
image; no weight is ruled out until the later comparison. -/
theorem attachedTwistHTBeforeComparison
    (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT) (hDS : HSyn.DeligneSerreConseq)
    (hFD : HSyn.FrobeniusDense) (hBN : HSyn.BrauerNesbitt)
    (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ) (hN : 0 < N) (hk : 1 ≤ k) (hg : PkgI4.IsNormalizedEigenform g χ)
    (hirr : r.IsIrreducible) (hw : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1})
    (hatt : r.AttachedUpToTwist ψ ιC ιL g S) :
    ∃ ρ : GaloisRep 5 2, ρ.AttachedTo ιC ιL g ∧
      (∃ T : GL (Fin 2) (PadicAlgCl 5), ∀ σ,
        r.mat σ * (T : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) =
          (ψ.toHom σ : PadicAlgCl 5) • ((T : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) * ρ.mat σ)) ∧
      (∃ S₀ : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S₀ → CharUnramifiedAt ψ q) ∧
      ∃ (E : IntermediateField ℚ_[5] (PadicAlgCl 5)) (_ : FiniteDimensional ℚ_[5] E)
        (_ : IsGalois ℚ_[5] E) (ψE : PkgI4.GQp 5 →* Eˣ) (w : ℤ),
        (∀ σ, (((ψE σ : Eˣ) : E) : PadicAlgCl 5) = (ψ.toHom (PkgI4.decomp 5 σ) : PadicAlgCl 5)) ∧
        PkgI4.HasHTWeights 5 (charRep ψE) {w} ∧
        ({0, -1} : Multiset ℤ) = ({0, 1 - k} : Multiset ℤ).map (· + w) := by
  obtain ⟨ρH, hss, hρatt⟩ := hR 5 ιC ιL N k χ g hN hk hg
  let ρ : GaloisRep 5 2 := ⟨ρH.toHom, ρH.continuous_toHom⟩
  have hss' : ρ.IsSemisimple := hss
  have hatt' : ρ.AttachedTo ιC ιL g := hρatt
  obtain ⟨ρ', htw⟩ := twistExists 5 2 ρ ψ
  have hc : IsConj r ρ' := twistConj_of hFD hBN 5 r ρ ρ' ψ ιC ιL N k g S hN hirr hss' hatt' hatt htw
  have hw' : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ') 5 {0, -1} := htConj_of htExtend 5 2 r ρ' _ hc hw
  have hmod : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ) 5 {0, 1 - k} := by
    rcases eq_or_lt_of_le hk with h1 | h2
    · subst k
      have hfin : (Set.range ρH.toHom).Finite := hDS 5 ιC ιL ρH N χ g hN hg hss hρatt
      have hzero := HSyn.HodgeLF7.finiteImageHT
        (_root_.ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate
          _root_.ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
          _root_.ZInQ.Contrib.CloudB3W11.axSenTate_proof) 5 2 ρ hfin
      simpa [Multiset.replicate_succ] using hzero
    · exact hHT 5 ιC ιL N k χ g ρ hN (by omega) hg hss' hatt'
  obtain ⟨T, hT⟩ := equivariant_hom_line_of_conj r ρ ρ' ψ htw hc
  refine ⟨ρ, hatt', ⟨T, hT⟩, attachedTwist_finitelyRamified r ρ N g ψ ιC ιL S hN hatt' hatt T hT, ?_⟩
  exact actualTwistHT_and_shift 5 (n := 2) (by decide) (HSyn.HodgeLF7.toG9Rep ρ)
    (HSyn.HodgeLF7.toG9Rep ρ') (HSyn.HodgeLF7.toG9Char ψ) _ _ htw (by simp) (by simp) hmod hw'

end HDec.G0Galois.C8Conrad.Manuscript
