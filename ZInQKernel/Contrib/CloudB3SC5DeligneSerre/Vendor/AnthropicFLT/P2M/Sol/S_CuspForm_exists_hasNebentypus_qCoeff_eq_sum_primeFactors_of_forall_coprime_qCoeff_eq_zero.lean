/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero (git blob 6dce71ce370e0e0f0c98b3026cc77f1faa917cd1, sha256 82fc288d6a42c863bb814add99af5b4398f453e0d50cd9685e77b30898e8d4cb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

noncomputable section

namespace AtkinLehnerNebentypus

variable {L : ℕ} {k : ℤ}



theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_add (f g : CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  simp only [qCoeff, CuspForm.coe_add]
  rw [ModularForm.qExpansion_add one_pos (one_mem_strictPeriods L) f g, map_add]

theorem qCoeff_smul (c : ℂ) (f : CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  simp only [qCoeff, CuspForm.IsGLPos.coe_smul]
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods L) c f, map_smul, smul_eq_mul]

def qCoeffLin (n : ℕ) : CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] ℂ where
  toFun f := qCoeff (⇑f) n
  map_add' f g := qCoeff_add f g n
  map_smul' c f := qCoeff_smul c f n

theorem qCoeffLin_apply (n : ℕ) (f : CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) : qCoeffLin n f = qCoeff (⇑f) n := rfl

theorem qCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    qCoeff (⇑(∑ i ∈ s, f i)) n = ∑ i ∈ s, qCoeff (⇑(f i)) n := by
  rw [← qCoeffLin_apply, map_sum]; rfl

theorem qCoeff_zero' (n : ℕ) : qCoeff (⇑(0 : CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)) n = 0 := by
  rw [← qCoeffLin_apply, map_zero]

theorem hasNebentypus_zero (ε : DirichletCharacter ℂ L) :
    CuspForm.HasNebentypus ε (0 : CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) := by
  intro γ _ τ
  simp

theorem hasNebentypus_add {ε : DirichletCharacter ℂ L} {f g : CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f + g) := by
  intro γ hγ τ
  simp only [CuspForm.add_apply]
  rw [hf γ hγ τ, hg γ hγ τ]
  ring

theorem hasNebentypus_smul {ε : DirichletCharacter ℂ L} {f : CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k}
    (hf : CuspForm.HasNebentypus ε f) (c : ℂ) : CuspForm.HasNebentypus ε (c • f) := by
  intro γ hγ τ
  simp only [CuspForm.IsGLPos.smul_apply, smul_eq_mul]
  rw [hf γ hγ τ]
  ring

theorem hasNebentypus_sum {ε : DirichletCharacter ℂ L} {ι : Type*} (s : Finset ι)
    (f : ι → CuspForm ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (hf : ∀ i ∈ s, CuspForm.HasNebentypus ε (f i)) :
    CuspForm.HasNebentypus ε (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasNebentypus_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasNebentypus_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem main (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (ε : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (hε : CuspForm.HasNebentypus ε f)
    (hf : ∀ n : ℕ, Nat.Coprime n K → qCoeff (⇑f) n = 0) :
    ∃ g : (p : ℕ) → CuspForm ((Gamma1 (N / p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ (p : ℕ) (hp : p ∈ N.primeFactors), g p = 0 ∨
        ∃ εp : DirichletCharacter ℂ (N / p),
          DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) εp = ε ∧
          CuspForm.HasNebentypus εp (g p)) ∧
      ∀ n : ℕ, qCoeff (⇑f) n =
        ∑ p ∈ N.primeFactors, if p ∣ n then qCoeff (⇑(g p)) (n / p) else 0 := by
  classical

  obtain ⟨h, hh⟩ :=
    CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero N k K hK f hf

  set pf := N.primeFactors with hpf
  have hdvd : ∀ P : pf, (P : ℕ) ∣ N := fun P => Nat.dvd_of_mem_primeFactors P.2
  have hdiv : ∀ P : pf, N / (P : ℕ) ∣ N := fun P => Nat.div_dvd_of_dvd (hdvd P)
  have hne : ∀ P : pf, NeZero (N / (P : ℕ)) := fun P =>
    ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) (hdvd P)) (Nat.prime_of_mem_primeFactors P.2).pos).ne'⟩
  have hmul : ∀ P : pf, N / (P : ℕ) * (P : ℕ) ∣ N := fun P => by rw [Nat.div_mul_cancel (hdvd P)]

  have hSS : ∀ P : pf, ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm ((Gamma1 (N / (P : ℕ)) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k))
      (εb : Fin n → DirichletCharacter ℂ (N / (P : ℕ))), ∀ i, CuspForm.HasNebentypus (εb i) (b i) := by
    intro P
    haveI := hne P
    obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen (N / (P : ℕ)) k
    choose εb hεb _ using hb
    exact ⟨n, b, εb, hεb⟩
  choose n b εb hεb using hSS

  have hDEG : ∀ (P : pf) (i : Fin (n P)), ∃ G : CuspForm ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ m : ℕ, qCoeff (⇑G) m = if (P : ℕ) ∣ m then qCoeff (⇑(b P i)) (m / P) else 0) ∧
      CuspForm.HasNebentypus (DirichletCharacter.changeLevel (hdiv P) (εb P i)) G := by
    intro P i
    obtain ⟨G, -, hGq, hGε⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) (hmul P) (b P i)
    exact ⟨G, hGq, hGε _ (hεb P i)⟩
  choose G hGq hGε using hDEG

  let ι := Σ P : pf, Fin (n P)
  let c : ι → ℂ := fun x => (b x.1).repr (h x.1) x.2
  let χ : ι → DirichletCharacter ℂ N := fun x => DirichletCharacter.changeLevel (hdiv x.1) (εb x.1 x.2)

  have hsum : ∑ x : ι, c x • G x.1 x.2 = f := by
    refine ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods N) fun m => ?_
    rw [qCoeff_sum, hh m, Fintype.sum_sigma, ← Finset.sum_coe_sort pf]
    refine Finset.sum_congr rfl fun P _ => ?_
    simp only [qCoeff_smul, hGq, c]
    split_ifs with hPm
    ·
      have := congrArg (fun F : CuspForm ((Gamma1 (N / (P : ℕ)) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k => qCoeff (⇑F) (m / P))
        ((b P).sum_repr (h P))
      simp only [qCoeff_sum, qCoeff_smul] at this
      exact this
    · simp

  have hfilt := CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq Finset.univ χ (fun x : ι => c x • G x.1 x.2)
    (fun x _ => hasNebentypus_smul (hGε x.1 x.2) _) hε hsum

  let g : (p : ℕ) → CuspForm ((Gamma1 (N / p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k := fun p =>
    if hp : p ∈ pf then
      ∑ i ∈ Finset.univ.filter (fun i => χ ⟨⟨p, hp⟩, i⟩ = ε), c ⟨⟨p, hp⟩, i⟩ • b ⟨p, hp⟩ i
    else 0
  have hg : ∀ P : pf, g P = ∑ i ∈ Finset.univ.filter (fun i => χ ⟨P, i⟩ = ε), c ⟨P, i⟩ • b P i := by
    intro P
    simp only [g, dif_pos P.2]
  refine ⟨g, fun p hp => ?_, fun m => ?_⟩
  ·
    set P : pf := ⟨p, hp⟩
    by_cases hex : ∃ εp : DirichletCharacter ℂ (N / p), DirichletCharacter.changeLevel (hdiv P) εp = ε
    · obtain ⟨εp, hεp⟩ := hex
      refine Or.inr ⟨εp, hεp, ?_⟩
      rw [show g p = g P from rfl, hg P]
      refine hasNebentypus_sum _ _ fun i hi => hasNebentypus_smul ?_ _
      obtain ⟨-, hi⟩ := Finset.mem_filter.mp hi

      have hinj := DirichletCharacter.changeLevel_injective (R := ℂ) (hdiv P) (hi.trans hεp.symm)
      rw [← hinj]
      exact hεb P i
    · refine Or.inl ?_
      rw [show g p = g P from rfl, hg P]
      refine Finset.sum_eq_zero fun i hi => ?_
      obtain ⟨-, hi⟩ := Finset.mem_filter.mp hi
      exact absurd ⟨εb P i, hi⟩ hex
  ·
    rw [← hfilt, qCoeff_sum, Finset.sum_filter, Fintype.sum_sigma, ← Finset.sum_coe_sort pf]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [hg P, qCoeff_sum, Finset.sum_filter]
    split_ifs with hPm
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hχ
      · rw [qCoeff_smul, qCoeff_smul, hGq, if_pos hPm]
      · rfl
    · refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with hχ
      · rw [qCoeff_smul, hGq, if_neg hPm, mul_zero]
      · rfl

end AtkinLehnerNebentypus

end

open scoped MatrixGroups in
theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (ε : DirichletCharacter ℂ N)
    (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) (hε : CuspForm.HasNebentypus ε f)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0) :
    ∃ g : (p : ℕ) → CuspForm (CongruenceSubgroup.Gamma1 (N / p)) k,
      (∀ (p : ℕ) (hp : p ∈ N.primeFactors), g p = 0 ∨
        ∃ εp : DirichletCharacter ℂ (N / p),
          DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) εp = ε ∧
          CuspForm.HasNebentypus εp (g p)) ∧
      ∀ n : ℕ, ModularFormClass.qCoeff f n =
        ∑ p ∈ N.primeFactors, if p ∣ n then ModularFormClass.qCoeff (g p) (n / p) else 0 :=
  AtkinLehnerNebentypus.main N k K hK ε f hε hf
