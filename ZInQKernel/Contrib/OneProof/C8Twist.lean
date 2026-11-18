import ZInQKernel.Contrib.OneProof.C8CFT

/-! # c8-conrad3: `TwistCharHTWt0` proved (on-the-spot step of C8)

`TwistCharHTWt0` (C8CFT; the Hodge–Tate half of c8-conrad's `TwistCharHT0`; diophantine_zq.tex L758-760, "the
twisting character is a de Rham subrepresentation of the Hom representation", on-the-spot) is
`TwistHT.twistCharHTWt0_proof`, with no new cited input:

1. R14 (`HSyn.EigenformRepExists`, a hypothesis of the Prop) gives a semisimple `ρ_g` attached to `g`, R13
   (`PkgI4.EigenformHT`, a hypothesis) its weights `{0, −1}`; Chebotarev (the kernel's T18, `ZInQ.Contrib.frobeniusDense`)
   gives `tr r = ψ · tr ρ_g` on `G_ℚ` (`trace_eq_of_attached`), hence `det r = ψ² det ρ_g`
   (`2 det M = (tr M)² − tr M²`, `det_eq_of_trace_eq`). No semisimplicity of `r` is used.
2. `ψ|_{G_{ℚ_5}}` takes values in a finite Galois `E` (`exists_galois_values`: an open `G_M` on which `tr ρ_g ≠ 0`
   and coset representatives; no Baire argument).
3. Over `G_E`, in hodge-split's Tate–Sen coordinates (`Ysp`, `htMult_eq_finrank_Ysp`, with Tate's two theorems,
   proved in the tree), nonzero `y₀ ∈ Y_0`, `y₁ ∈ Y_1` are `ℂ_p`-independent, and `d = det(y₀, y₁)` satisfies
   `d · det ρ(σ) = χ(σ) σ(d)` (`exists_det_vector`); for `r` and `ρ_g` this gives `y = d_r / d_g ≠ 0` with
   `σ(y) = ψ(σ)² y`.
4. A square root `c` of `y` in `ℂ_p` (Mathlib: `ℂ_p` is algebraically closed) has `σ(c) = ±ψ(σ) c`; the orbit map
   `σ ↦ σ(c)` is continuous (`continuous_cpAct_orbit`), so `σ(c) = ψ(σ) c` on `G_{E'}` for a finite Galois `E' ⊇ E`
   (`exists_sqrt_twist`), and `ψ` is Hodge–Tate of weight `0` over `E'` (`hasHTWeights_zero_of_twist`). -/

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace HDec.G0Galois.C8Conrad

namespace TwistHT

open _root_.PkgI4 (GaloisRep GaloisChar)

/-! ## §1. The global part: `tr r = ψ · tr ρ_g` and `det r = ψ² · det ρ_g` on `G_ℚ` -/

/-- `2 det M = (tr M)² − tr(M²)` for `2 × 2` matrices. -/
theorem two_mul_det_fin_two {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    2 * M.det = M.trace ^ 2 - (M * M).trace := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem continuous_trace_mat {ℓ : ℕ} [Fact ℓ.Prime] (ρ : GaloisRep ℓ 2) :
    Continuous fun σ => (ρ.mat σ).trace := by
  have h : Continuous fun σ => (ρ.toHom σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) :=
    Units.continuous_val.comp ρ.continuous_toHom
  exact h.matrix_trace

theorem continuous_char {ℓ : ℕ} [Fact ℓ.Prime] (ψ : GaloisChar ℓ) :
    Continuous fun σ => ((ψ.toHom σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) :=
  Units.continuous_val.comp ψ.continuous_toHom

/-- **Chebotarev (the kernel's T18) gives the trace identity on all of `G_ℚ`.** -/
theorem trace_eq_of_attached (r ρ : GaloisRep 5 2) (N : ℕ) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ)
    (hatt : r.AttachedUpToTwist ψ ιC ιL g S) (hρ : ρ.AttachedTo ιC ιL g) (hN : 0 < N) (σ : PkgI4.GQ) :
    (r.mat σ).trace = (ψ.toHom σ : PadicAlgCl 5) * (ρ.mat σ).trace := by
  have key := C9Rhof.eq_of_eq_on_arithFrob ZInQ.Contrib.frobeniusDense (S ∪ (N * 5).primeFactors)
    (fun σ => (r.mat σ).trace) (fun σ => (ψ.toHom σ : PadicAlgCl 5) * (ρ.mat σ).trace)
    (continuous_trace_mat r) ((continuous_char ψ).mul (continuous_trace_mat ρ)) (by
      intro p hp hpS v τ hv hτ
      have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
      have hpN : ¬ p ∣ N * 5 := fun h => hpS (Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hp, h, by positivity⟩))
      obtain ⟨-, α, hα, htr⟩ := hatt p hp hpS1
      obtain ⟨-, β, hβ, htrρ⟩ := hρ p hp hpN
      have hαβ : α = β := ιC.toRingHom.injective (by
        change ιC α = ιC β
        rw [hα, hβ])
      show (r.mat τ).trace = (ψ.toHom τ : PadicAlgCl 5) * (ρ.mat τ).trace
      rw [htr v τ hv hτ, htrρ v τ hv hτ, hαβ])
  exact congrFun key σ

/-- **The determinant identity** `det r = ψ² det ρ_g` on `G_ℚ` (from the trace identity at `σ` and `σ²`). -/
theorem det_eq_of_trace_eq (r ρ : GaloisRep 5 2) (ψ : GaloisChar 5)
    (htr : ∀ σ, (r.mat σ).trace = (ψ.toHom σ : PadicAlgCl 5) * (ρ.mat σ).trace) (σ : PkgI4.GQ) :
    (r.mat σ).det = (ψ.toHom σ : PadicAlgCl 5) ^ 2 * (ρ.mat σ).det := by
  have hmul : ∀ (ρ' : GaloisRep 5 2), ρ'.mat (σ * σ) = ρ'.mat σ * ρ'.mat σ := by
    intro ρ'
    simp only [PkgI4.GaloisRep.mat, map_mul, Units.val_mul]
  have h1 := two_mul_det_fin_two (r.mat σ)
  have h2 := two_mul_det_fin_two (ρ.mat σ)
  rw [← hmul, htr, htr (σ * σ), hmul, map_mul, Units.val_mul] at h1
  have h3 : (2 : PadicAlgCl 5) * (r.mat σ).det = 2 * ((ψ.toHom σ : PadicAlgCl 5) ^ 2 * (ρ.mat σ).det) := by
    rw [h1, mul_left_comm, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

/-! ## §2. Local lemmas over `ℂ_p` (pkg-I4's G9 copy, as hodge-split's `Ysp` machinery) -/

section Local

open ZInQ.Contrib.HodgeSplit

variable (p : ℕ) [Fact p.Prime]

/-- `σ ↦ σ(x)` is continuous on `G_{ℚ_p}` for every `x ∈ ℂ_p` (approximate `x` by `a ∈ ℚ̄_p`; the stabilizer of `a`
is open and `G_{ℚ_p}` acts by isometries). -/
theorem continuous_cpAct_orbit (x : ℂ_[p]) :
    Continuous fun σ : ZInQ.Contrib.G9.PkgI4.GQp p => ZInQ.Contrib.G9.PkgI4.cpAct p σ x := by
  rw [continuous_iff_continuousAt]
  intro σ₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, ha⟩ : ∃ a : PadicAlgCl p, dist x (a : ℂ_[p]) < ε / 2 :=
    (Metric.denseRange_iff.mp UniformSpace.Completion.denseRange_coe) x (ε / 2) (by positivity)
  have hV : IsOpen {σ : ZInQ.Contrib.G9.PkgI4.GQp p | σ a = σ₀ a} := by
    have hS : IsOpen ((MulAction.stabilizer (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) a :
        Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) :=
      stabilizer_isOpen_of_isIntegral (K := ℚ_[p]) (L := PadicAlgCl p) a
    have hset : {σ : ZInQ.Contrib.G9.PkgI4.GQp p | σ a = σ₀ a} =
        (fun σ => σ₀⁻¹ * σ) ⁻¹' (MulAction.stabilizer (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) a) := by
      ext σ
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        show (σ₀⁻¹ * σ) a = a
        rw [AlgEquiv.mul_apply, h]
        show (σ₀⁻¹ * σ₀) a = a
        rw [inv_mul_cancel]; rfl
      · intro h
        have h2 : (σ₀⁻¹ * σ) a = a := h
        rw [AlgEquiv.mul_apply] at h2
        have h3 := congrArg σ₀ h2
        rw [← h3]
        show σ a = (σ₀ * σ₀⁻¹) (σ a)
        rw [mul_inv_cancel]; rfl
    rw [hset]
    exact hS.preimage (continuous_const.mul continuous_id)
  filter_upwards [hV.mem_nhds rfl] with σ hσ
  have hσa : σ a = σ₀ a := hσ
  have e : ZInQ.Contrib.G9.PkgI4.cpAct p σ x - ZInQ.Contrib.G9.PkgI4.cpAct p σ₀ x =
      ZInQ.Contrib.G9.PkgI4.cpAct p σ (x - a) + ZInQ.Contrib.G9.PkgI4.cpAct p σ₀ ((a : ℂ_[p]) - x) := by
    rw [map_sub, map_sub, ZInQ.Contrib.G9.PkgI4.cpAct_coe, ZInQ.Contrib.G9.PkgI4.cpAct_coe, hσa]
    ring
  rw [dist_eq_norm, e]
  calc ‖ZInQ.Contrib.G9.PkgI4.cpAct p σ (x - a) + ZInQ.Contrib.G9.PkgI4.cpAct p σ₀ ((a : ℂ_[p]) - x)‖
      ≤ ‖ZInQ.Contrib.G9.PkgI4.cpAct p σ (x - a)‖ + ‖ZInQ.Contrib.G9.PkgI4.cpAct p σ₀ ((a : ℂ_[p]) - x)‖ :=
        norm_add_le _ _
    _ = ‖x - a‖ + ‖(a : ℂ_[p]) - x‖ := by
        rw [ZInQ.Contrib.G9.PkgI4.norm_cpAct, ZInQ.Contrib.G9.PkgI4.norm_cpAct]
    _ < ε / 2 + ε / 2 := by
        rw [← dist_eq_norm, ← dist_eq_norm, dist_comm (a : ℂ_[p])]
        exact add_lt_add ha ha
    _ = ε := by ring

/-- `dim_K Y_i(ρ) ≤ n` (from Tate–Sen independence, as in `Ysp_finiteDimensional`). -/
theorem finrank_Ysp_le (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : ZInQ.Contrib.G9.PkgI4.GQp p →* GL (Fin n) E)
    (i : ℤ) : Module.finrank K (Ysp p ρ i K) ≤ n := by
  classical
  haveI := Ysp_finiteDimensional p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    ZInQ.Contrib.CloudB3W11.axSenTate_proof K ρ i
  haveI : Module.Free K (Ysp p ρ i K) := Module.Free.of_divisionRing K _
  let b := Module.finBasis K (Ysp p ρ i K)
  have hli : LinearIndependent ℂ_[p] (fun k => ((b k : Ysp p ρ i K) : Fin n → ℂ_[p])) := by
    refine Ysp_linearIndependent p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
      ZInQ.Contrib.CloudB3W11.axSenTate_proof K ρ (fun _ => i) _ (fun k => (b k).2) ?_
    intro j₀ a _ hsum
    have h1 : ∑ k, a k • (b k) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul]
      exact hsum
    exact Fintype.linearIndependent_iff.mp b.linearIndependent a h1
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_fin, Module.finrank_fin_fun] at this

/-- Two nonzero vectors of `Y`-spaces of different weights are `ℂ_p`-independent (Tate–Sen). -/
theorem linIndep_two (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : ZInQ.Contrib.G9.PkgI4.GQp p →* GL (Fin n) E)
    (i₀ i₁ : ℤ) (hi : i₀ ≠ i₁) (y₀ y₁ : Fin n → ℂ_[p]) (h₀ : y₀ ∈ Ysp p ρ i₀ K)
    (h₁ : y₁ ∈ Ysp p ρ i₁ K) (hy₀ : y₀ ≠ 0) (hy₁ : y₁ ≠ 0) : LinearIndependent ℂ_[p] ![y₀, y₁] := by
  refine Ysp_linearIndependent p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    ZInQ.Contrib.CloudB3W11.axSenTate_proof K ρ ![i₀, i₁] ![y₀, y₁]
    (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩) ?_
  intro j₀ a ha hs
  rw [Fin.sum_univ_two] at hs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs
  have ha0 : ∀ k : Fin 2, a k • ![y₀, y₁] k = 0 → a k = 0 := by
    intro k hk
    by_contra hne
    have hy : ![y₀, y₁] k = 0 := by
      rw [← one_smul K (![y₀, y₁] k), ← inv_mul_cancel₀ hne, mul_smul, hk, smul_zero]
    fin_cases k
    · exact hy₀ hy
    · exact hy₁ hy
  by_cases e : i₀ = j₀
  · have h1 : a 1 = 0 := ha 1 (by simp only [Matrix.cons_val_one]; rw [← e]; exact hi.symm)
    have h0 : a 0 = 0 := ha0 0 (by rw [h1, zero_smul, add_zero] at hs; exact hs)
    exact Fin.forall_fin_two.mpr ⟨h0, h1⟩
  · have h0 : a 0 = 0 := ha 0 (by simpa using e)
    have h1 : a 1 = 0 := ha0 1 (by rw [h0, zero_smul, zero_add] at hs; exact hs)
    exact Fin.forall_fin_two.mpr ⟨h0, h1⟩

/-- **The square root step** (on-the-spot): if `σ(y) = ψ(σ)² y` on `G_E` with `y ≠ 0`, a square root `c` of `y` in the
algebraically closed `ℂ_p` satisfies `σ(c) = ±ψ(σ) c` on `G_E`; the sign is continuous (`continuous_cpAct_orbit`),
so `σ(c) = ψ(σ) c` on an open subgroup, which contains `G_{E'}` for a finite Galois `E' ⊇ E`. -/
theorem exists_sqrt_twist (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ψL : ZInQ.Contrib.G9.PkgI4.GQp p →* (PadicAlgCl p)ˣ) (hψc : Continuous fun σ => (ψL σ : PadicAlgCl p))
    (y : ℂ_[p]) (hy0 : y ≠ 0)
    (hy : ∀ σ ∈ E.fixingSubgroup,
      ZInQ.Contrib.G9.PkgI4.cpAct p σ y = ((ψL σ : PadicAlgCl p) : ℂ_[p]) ^ 2 * y) :
    ∃ E' : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] E' ∧ IsGalois ℚ_[p] E' ∧
      E ≤ E' ∧ ∃ c : ℂ_[p], c ≠ 0 ∧ ∀ σ ∈ E'.fixingSubgroup,
        ZInQ.Contrib.G9.PkgI4.cpAct p σ c = ((ψL σ : PadicAlgCl p) : ℂ_[p]) * c := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq y two_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hc
    exact hy0 hc.symm
  let ψC : ZInQ.Contrib.G9.PkgI4.GQp p → ℂ_[p] := fun σ => ((ψL σ : PadicAlgCl p) : ℂ_[p])
  have hψCc : Continuous ψC := (UniformSpace.Completion.continuous_coe _).comp hψc
  have hpm : ∀ σ ∈ E.fixingSubgroup, ZInQ.Contrib.G9.PkgI4.cpAct p σ c = ψC σ * c ∨
      ZInQ.Contrib.G9.PkgI4.cpAct p σ c = -(ψC σ * c) := by
    intro σ hσ
    have h2 : (ZInQ.Contrib.G9.PkgI4.cpAct p σ c) ^ 2 = (ψC σ * c) ^ 2 := by
      rw [← map_pow, hc, hy σ hσ, mul_pow, hc]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
  let Um : Set (ZInQ.Contrib.G9.PkgI4.GQp p) := {σ | ZInQ.Contrib.G9.PkgI4.cpAct p σ c = -(ψC σ * c)}
  have hUm : IsClosed Um := isClosed_eq (continuous_cpAct_orbit p c) (hψCc.mul continuous_const).neg
  have hG : IsOpen (E.fixingSubgroup : Set (ZInQ.Contrib.G9.PkgI4.GQp p)) :=
    IntermediateField.fixingSubgroup_isOpen E
  have hopen : IsOpen ((E.fixingSubgroup : Set (ZInQ.Contrib.G9.PkgI4.GQp p)) ∩ Umᶜ) :=
    hG.inter hUm.isOpen_compl
  have h1 : (1 : ZInQ.Contrib.G9.PkgI4.GQp p) ∈ (E.fixingSubgroup : Set (ZInQ.Contrib.G9.PkgI4.GQp p)) ∩ Umᶜ := by
    refine ⟨E.fixingSubgroup.one_mem, fun h => ?_⟩
    have h' : ZInQ.Contrib.G9.PkgI4.cpAct p 1 c = -(ψC 1 * c) := h
    have hψ1 : ψC 1 = 1 := by simp [ψC]
    have hone : ZInQ.Contrib.G9.PkgI4.cpAct p 1 c = c := ZInQ.Contrib.G9.cpAct_one p c
    rw [hone, hψ1, one_mul] at h'
    have h2 : (2 : ℂ_[p]) * c = 0 := by linear_combination h'
    exact hc0 ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
  obtain ⟨L, hLfd, hLn, hLsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[p] (PadicAlgCl p) _).mp (hopen.mem_nhds h1)
  haveI := hLfd
  let EL : IntermediateField ℚ_[p] (PadicAlgCl p) := E ⊔ L
  let E' : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.normalClosure ℚ_[p] EL (PadicAlgCl p)
  have hle : EL ≤ E' := IntermediateField.le_normalClosure EL
  refine ⟨E', normalClosure.is_finiteDimensional ℚ_[p] EL (PadicAlgCl p),
    IsGalois.normalClosure ℚ_[p] EL (PadicAlgCl p), le_sup_left.trans hle, c, hc0, ?_⟩
  intro σ hσ
  have hσL : σ ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_le (le_sup_right.trans hle) hσ
  obtain ⟨hσE, hσm⟩ := hLsub hσL
  rcases hpm σ hσE with h | h
  · exact h
  · exact absurd h hσm

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The conclusion**: a character with values in a finite Galois `E'` and a nonzero `c ∈ ℂ_p` with `σ(c) = ψ(σ) c` on
`G_{E'}` is Hodge–Tate of weight `0` (`htMult_eq_finrank_Ysp`, Tate–Sen independence). -/
theorem hasHTWeights_zero_of_twist (E' : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E']
    [IsGalois ℚ_[p] E'] (ψL : ZInQ.Contrib.G9.PkgI4.GQp p →* (PadicAlgCl p)ˣ)
    (hψE : ∀ σ, (ψL σ : PadicAlgCl p) ∈ E') (c : ℂ_[p]) (hc0 : c ≠ 0)
    (hc : ∀ σ ∈ E'.fixingSubgroup,
      ZInQ.Contrib.G9.PkgI4.cpAct p σ c = ((ψL σ : PadicAlgCl p) : ℂ_[p]) * c) :
    ∃ ψE : PkgI4.GQp p →* E'ˣ, (∀ σ, (((ψE σ : E'ˣ) : E') : PadicAlgCl p) = ψL σ) ∧
      PkgI4.HasHTWeights p (charRep ψE) {0} := by
  let ψE : PkgI4.GQp p →* E'ˣ :=
    { toFun := fun σ => Units.mk0 ⟨ψL σ, hψE σ⟩ (fun h => (ψL σ).ne_zero (congrArg Subtype.val h))
      map_one' := Units.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Units.ext (Subtype.ext (by simp)) }
  refine ⟨ψE, fun σ => rfl, fun w => ?_⟩
  have hbr : PkgI4.htMult p (charRep ψE) w = ZInQ.Contrib.G9.PkgI4.htMult p (charRep ψE) w := rfl
  rw [hbr, htMult_eq_finrank_Ysp p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    ZInQ.Contrib.CloudB3W11.axSenTate_proof E' (charRep ψE) w]
  let cv : Fin 1 → ℂ_[p] := fun _ => c
  have hcv0 : cv ≠ 0 := fun h => hc0 (congrFun h 0)
  have hcv : cv ∈ Ysp p (charRep ψE) 0 E' := by
    intro σ hσ
    ext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have hval : algebraMap E' ℂ_[p] ((ψE σ : E'ˣ) : E') = ((ψL σ : PadicAlgCl p) : ℂ_[p]) := rfl
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.transpose_apply, matC, Matrix.map_apply,
      Pi.smul_apply, vAct, cycPow_zero, one_smul]
    have hm : ((charRep ψE σ : GL (Fin 1) E') : Matrix (Fin 1) (Fin 1) E') 0 0 = ((ψE σ : E'ˣ) : E') := by
      simp [charRep, Matrix.algebraMap_matrix_apply]
    rw [hm, hval]
    exact (hc σ hσ).symm
  haveI : ∀ i : ℤ, FiniteDimensional E' (Ysp p (charRep ψE) i E') := fun i =>
    Ysp_finiteDimensional p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
      ZInQ.Contrib.CloudB3W11.axSenTate_proof E' (charRep ψE) i
  have hle : ∀ i : ℤ, Module.finrank E' (Ysp p (charRep ψE) i E') ≤ 1 := fun i =>
    finrank_Ysp_le p E' (charRep ψE) i
  by_cases hw : w = 0
  · subst hw
    rw [neg_zero, Multiset.count_singleton_self]
    have hne0 : Ysp p (charRep ψE) 0 E' ≠ ⊥ := by
      intro h
      have : cv ∈ (⊥ : Submodule E' (Fin 1 → ℂ_[p])) := h ▸ hcv
      exact hcv0 ((Submodule.mem_bot E').mp this)
    have hpos : 0 < Module.finrank E' (Ysp p (charRep ψE) 0 E') := by
      rcases Nat.eq_zero_or_pos (Module.finrank E' (Ysp p (charRep ψE) 0 E')) with h0 | h0
      · exact absurd (Submodule.finrank_eq_zero.mp h0) hne0
      · exact h0
    have := hle 0
    omega
  · rw [Multiset.count_singleton, if_neg hw]
    by_contra hne
    have hne' : Ysp p (charRep ψE) (-w) E' ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hne
      exact hne rfl
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
    have hli := linIndep_two p E' (charRep ψE) 0 (-w) (by omega) cv z hcv hz hcv0 hz0
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fin_fun] at this
    omega

set_option synthInstance.maxHeartbeats 400000 in
/-- **A finite Galois field of values.** If `ψ(σ)` lies in a finite `E₀` wherever a continuous `t` (here `tr ρ_g`) is
nonzero, and `t(1) ≠ 0`, then all values of `ψ` lie in a finite Galois `E ⊇ E₀` (an open normal subgroup `G_M` on which
`t ≠ 0`, and the finitely many values of `ψ` at coset representatives of `G_M`). -/
theorem exists_galois_values (E₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E₀]
    (ψL : ZInQ.Contrib.G9.PkgI4.GQp p →* (PadicAlgCl p)ˣ) (t : ZInQ.Contrib.G9.PkgI4.GQp p → PadicAlgCl p)
    (ht : Continuous t) (ht1 : t 1 ≠ 0) (hval : ∀ σ, t σ ≠ 0 → (ψL σ : PadicAlgCl p) ∈ E₀) :
    ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] E ∧ IsGalois ℚ_[p] E ∧ E₀ ≤ E ∧
      ∀ σ, (ψL σ : PadicAlgCl p) ∈ E := by
  classical
  have hU : IsOpen {σ : ZInQ.Contrib.G9.PkgI4.GQp p | t σ ≠ 0} := isOpen_ne_fun ht continuous_const
  obtain ⟨M, hMfd, hMn, hMsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[p] (PadicAlgCl p) _).mp (hU.mem_nhds ht1)
  haveI := hMfd
  let H : Subgroup (ZInQ.Contrib.G9.PkgI4.GQp p) := M.fixingSubgroup
  haveI : Finite (ZInQ.Contrib.G9.PkgI4.GQp p ⧸ H) :=
    Subgroup.quotient_finite_of_isOpen H (IntermediateField.fixingSubgroup_isOpen M)
  let R : Set (PadicAlgCl p) :=
    Set.range fun q : ZInQ.Contrib.G9.PkgI4.GQp p ⧸ H =>
      (ψL q.out : PadicAlgCl p)
  haveI : Finite R := Set.finite_range _ |>.to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] R) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let E₃ : IntermediateField ℚ_[p] (PadicAlgCl p) := E₀ ⊔ IntermediateField.adjoin ℚ_[p] R
  let E : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.normalClosure ℚ_[p] E₃ (PadicAlgCl p)
  have hle : E₃ ≤ E := IntermediateField.le_normalClosure E₃
  refine ⟨E, normalClosure.is_finiteDimensional ℚ_[p] E₃ (PadicAlgCl p),
    IsGalois.normalClosure ℚ_[p] E₃ (PadicAlgCl p), le_sup_left.trans hle, fun σ => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H σ
  have hσ : σ = (QuotientGroup.mk σ : ZInQ.Contrib.G9.PkgI4.GQp p ⧸ H).out * (h : _)⁻¹ := by
    rw [hh]; simp
  have hhinv : ((h : _)⁻¹ : ZInQ.Contrib.G9.PkgI4.GQp p) ∈ M.fixingSubgroup :=
    M.fixingSubgroup.inv_mem h.2
  have h1 : (ψL ((h : _)⁻¹) : PadicAlgCl p) ∈ E₃ :=
    (le_sup_left : E₀ ≤ E₃) (hval _ (hMsub hhinv))
  have h2 : (ψL (QuotientGroup.mk σ : ZInQ.Contrib.G9.PkgI4.GQp p ⧸ H).out : PadicAlgCl p) ∈ E₃ :=
    (le_sup_right : IntermediateField.adjoin ℚ_[p] R ≤ E₃)
      (IntermediateField.subset_adjoin ℚ_[p] R ⟨_, rfl⟩)
  apply hle
  rw [hσ, map_mul, Units.val_mul]
  exact E₃.mul_mem h2 h1

/-- **The determinant vector.** If `ρ_E` has Hodge–Tate weights `{0, −1}` over a finite Galois `E`, nonzero
`y₀ ∈ Y_0`, `y₁ ∈ Y_1` are `ℂ_p`-independent (Tate–Sen), and `d = det(y₀, y₁) ≠ 0` satisfies
`d · det ρ(σ) = χ(σ) σ(d)` on `G_E`. -/
theorem exists_det_vector (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    [IsGalois ℚ_[p] E] (ρE : ZInQ.Contrib.G9.PkgI4.GQp p →* GL (Fin 2) E)
    (hHT : ∀ w, ZInQ.Contrib.G9.PkgI4.htMult p ρE w = ({0, -1} : Multiset ℤ).count w) :
    ∃ d : ℂ_[p], d ≠ 0 ∧ ∀ σ ∈ E.fixingSubgroup,
      d * algebraMap E ℂ_[p] ((ρE σ : Matrix (Fin 2) (Fin 2) E).det) =
        algebraMap ℚ_[p] ℂ_[p] (ZInQ.Contrib.G9.PkgI4.cycPow p σ 1) * ZInQ.Contrib.G9.PkgI4.cpAct p σ d := by
  have hdim : ∀ i : ℤ, i = 0 ∨ i = 1 → Module.finrank E (Ysp p ρE i E) = 1 := by
    intro i hi
    have h := htMult_eq_finrank_Ysp p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
      ZInQ.Contrib.CloudB3W11.axSenTate_proof E ρE (-i)
    rw [neg_neg, hHT] at h
    rw [← h]
    rcases hi with rfl | rfl <;> decide
  have hne : ∀ i : ℤ, i = 0 ∨ i = 1 → ∃ y ∈ Ysp p ρE i E, y ≠ 0 := by
    intro i hi
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro h
    have := hdim i hi
    rw [h, finrank_bot] at this
    exact zero_ne_one this
  obtain ⟨y₀, hy₀, hy₀0⟩ := hne 0 (Or.inl rfl)
  obtain ⟨y₁, hy₁, hy₁0⟩ := hne 1 (Or.inr rfl)
  have hli := linIndep_two p E ρE 0 1 (by norm_num) y₀ y₁ hy₀ hy₁ hy₀0 hy₁0
  let A : Matrix (Fin 2) (Fin 2) ℂ_[p] := Matrix.of ![y₀, y₁]
  have hA : LinearIndependent ℂ_[p] A.row := by
    have e : A.row = ![y₀, y₁] := by
      funext i; fin_cases i <;> rfl
    rw [e]; exact hli
  have hdetA : A.det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det A |>.mp (Matrix.linearIndependent_row_iff_isUnit.mp hA)).ne_zero
  refine ⟨y₀ 0 * y₁ 1 - y₀ 1 * y₁ 0, ?_, fun σ hσ => ?_⟩
  · rw [Matrix.det_fin_two] at hdetA
    exact hdetA
  · set M := matC p (ρE σ : Matrix (Fin 2) (Fin 2) E) with hM
    have hdetM : algebraMap E ℂ_[p] ((ρE σ : Matrix (Fin 2) (Fin 2) E).det) = M.det := by
      rw [hM, matC, RingHom.map_det]; rfl
    have e0 := hy₀ σ hσ
    have e1 := hy₁ σ hσ
    have e00 := congrFun e0 0
    have e01 := congrFun e0 1
    have e10 := congrFun e1 0
    have e11 := congrFun e1 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply, Pi.smul_apply, vAct,
      cycPow_zero, Algebra.smul_def, map_one, one_mul] at e00 e01 e10 e11
    rw [hdetM, Matrix.det_fin_two, map_sub, map_mul, map_mul]
    linear_combination (ZInQ.Contrib.G9.PkgI4.cpAct p σ (y₀ 0)) * e11 -
      (ZInQ.Contrib.G9.PkgI4.cpAct p σ (y₀ 1)) * e10 + (M 0 1 * y₁ 0 + M 1 1 * y₁ 1) * e00 -
      (M 0 0 * y₁ 0 + M 1 0 * y₁ 1) * e01

end Local

/-! ## §3. `TwistCharHTWt0` -/

open ZInQ.Contrib.HodgeSplit in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- **`TwistCharHTWt0` proved** (on-the-spot step, N5 L758-760: "the twisting character is a de Rham subrepresentation
of the Hom representation"). R14 gives `ρ_g`, R13 its weights `{0, −1}`; Chebotarev gives `tr r = ψ tr ρ_g` and
`det r = ψ² det ρ_g` on `G_ℚ`; in Tate–Sen coordinates the determinants of `Y`-bases give `y ≠ 0` with
`σ(y) = ψ(σ)² y` on `G_E`; a square root of `y` in `ℂ_p` gives `σ(c) = ψ(σ) c` on an open subgroup, i.e. `ψ` is
Hodge–Tate of weight `0`. -/
theorem twistCharHTWt0_proof : TwistCharHTWt0 := by
  intro hR hHT r N χ g ψ ιC ιL S hN hg hr hatt
  obtain ⟨ρ₀, hss₀, hρatt₀⟩ := hR 5 ιC ιL N 2 χ g hN (by norm_num) hg
  let ρ : GaloisRep 5 2 := ⟨ρ₀.toHom, ρ₀.continuous_toHom⟩
  have hss : ρ.IsSemisimple := hss₀
  have hρatt : ρ.AttachedTo ιC ιL g := hρatt₀
  have hρHT : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ) 5 {0, -1} := by
    have h := hHT 5 ιC ιL N 2 χ g ρ hN le_rfl hg hss hρatt
    have e : (1 : ℤ) - 2 = -1 := by norm_num
    rw [e] at h
    exact h
  have htr := trace_eq_of_attached r ρ N g ψ ιC ιL S hatt hρatt hN
  have hdet := det_eq_of_trace_eq r ρ ψ htr
  obtain ⟨E₁, hE₁, r₁, hr₁, hrw⟩ := hr
  obtain ⟨E₂, hE₂, ρ₂, hρ₂, hρw⟩ := hρHT
  haveI := hE₁
  haveI := hE₂
  let rL := r.restrictLocal 5
  let ρL := ρ.restrictLocal 5
  let ψL : ZInQ.Contrib.G9.PkgI4.GQp 5 →* (PadicAlgCl 5)ˣ := ψ.toHom.comp (PkgI4.decomp 5)
  let E₀ : IntermediateField ℚ_[5] (PadicAlgCl 5) := E₁ ⊔ E₂
  have hdc : Continuous (PkgI4.decomp 5) :=
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[5])).continuous
  have hentr : ∀ σ i j, (rL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) i j ∈ E₀ := by
    intro σ i j
    have e : (((r₁ σ : Matrix (Fin 2) (Fin 2) E₁) i j : E₁) : PadicAlgCl 5) =
        (rL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) i j := by rw [← hr₁ σ]; rfl
    rw [← e]
    exact (le_sup_left : E₁ ≤ E₀) ((r₁ σ : Matrix (Fin 2) (Fin 2) E₁) i j).2
  have hentρ : ∀ σ i j, (ρL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) i j ∈ E₀ := by
    intro σ i j
    have e : (((ρ₂ σ : Matrix (Fin 2) (Fin 2) E₂) i j : E₂) : PadicAlgCl 5) =
        (ρL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) i j := by rw [← hρ₂ σ]; rfl
    rw [← e]
    exact (le_sup_right : E₂ ≤ E₀) ((ρ₂ σ : Matrix (Fin 2) (Fin 2) E₂) i j).2
  have htrmem : ∀ (f : ZInQ.Contrib.G9.PkgI4.GQp 5 →* GL (Fin 2) (PadicAlgCl 5)),
      (∀ σ i j, (f σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) i j ∈ E₀) →
      ∀ σ, (f σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)).trace ∈ E₀ := by
    intro f hf σ
    rw [Matrix.trace_fin_two]
    exact E₀.add_mem (hf σ 0 0) (hf σ 1 1)
  let t : ZInQ.Contrib.G9.PkgI4.GQp 5 → PadicAlgCl 5 := fun σ => (ρL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)).trace
  have ht : Continuous t := (continuous_trace_mat ρ).comp hdc
  have ht1 : t 1 ≠ 0 := by
    show (ρL 1 : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)).trace ≠ 0
    rw [map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin]
    norm_num
  have hval : ∀ σ, t σ ≠ 0 → (ψL σ : PadicAlgCl 5) ∈ E₀ := by
    intro σ hσ
    have e := htr (PkgI4.decomp 5 σ)
    have e' : (ψL σ : PadicAlgCl 5) = (rL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)).trace / t σ := by
      rw [eq_div_iff hσ]
      exact e.symm
    rw [e']
    exact E₀.div_mem (htrmem rL hentr σ) (htrmem ρL hentρ σ)
  obtain ⟨E, hEfd, hEgal, hE₀E, hψE⟩ := exists_galois_values 5 E₀ ψL t ht ht1 hval
  haveI := hEfd
  haveI := hEgal
  have hmemr : ∀ σ i j, (rL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) i j ∈ E := fun σ i j => hE₀E (hentr σ i j)
  have hmemρ : ∀ σ i j, (ρL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) i j ∈ E := fun σ i j => hE₀E (hentρ σ i j)
  let rE := ZInQ.Contrib.G9.liftGL E rL hmemr
  let ρE := ZInQ.Contrib.G9.liftGL E ρL hmemρ
  have hrEw : ∀ w, ZInQ.Contrib.G9.PkgI4.htMult 5 rE w = ({0, -1} : Multiset ℤ).count w := fun w =>
    (htMult_eq_of_lifts 5 rL rE r₁ (ZInQ.Contrib.G9.liftGL_map E rL hmemr) hr₁ w).trans (hrw w)
  have hρEw : ∀ w, ZInQ.Contrib.G9.PkgI4.htMult 5 ρE w = ({0, -1} : Multiset ℤ).count w := fun w =>
    (htMult_eq_of_lifts 5 ρL ρE ρ₂ (ZInQ.Contrib.G9.liftGL_map E ρL hmemρ) hρ₂ w).trans (hρw w)
  obtain ⟨dr, hdr0, hdr⟩ := exists_det_vector 5 E rE hrEw
  obtain ⟨dg, hdg0, hdg⟩ := exists_det_vector 5 E ρE hρEw
  have hdetE : ∀ (f : ZInQ.Contrib.G9.PkgI4.GQp 5 →* GL (Fin 2) (PadicAlgCl 5))
      (hf : ∀ σ i j, (f σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)) i j ∈ E) (σ : ZInQ.Contrib.G9.PkgI4.GQp 5),
      algebraMap E ℂ_[5] ((ZInQ.Contrib.G9.liftGL E f hf σ : Matrix (Fin 2) (Fin 2) E).det) =
        (((f σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)).det : PadicAlgCl 5) : ℂ_[5]) := by
    intro f hf σ
    rw [IsScalarTower.algebraMap_apply E (PadicAlgCl 5) ℂ_[5], RingHom.map_det, PadicComplex.coe_eq]
    congr 2
  let y : ℂ_[5] := dr / dg
  have hy0 : y ≠ 0 := div_ne_zero hdr0 hdg0
  have hy : ∀ σ ∈ E.fixingSubgroup,
      ZInQ.Contrib.G9.PkgI4.cpAct 5 σ y = ((ψL σ : PadicAlgCl 5) : ℂ_[5]) ^ 2 * y := by
    intro σ hσ
    have h1 := hdr σ hσ
    have h2 := hdg σ hσ
    rw [hdetE rL hmemr σ] at h1
    rw [hdetE ρL hmemρ σ] at h2
    have hd : (((rL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)).det : PadicAlgCl 5) : ℂ_[5]) =
        ((ψL σ : PadicAlgCl 5) : ℂ_[5]) ^ 2 *
          (((ρL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)).det : PadicAlgCl 5) : ℂ_[5]) := by
      have := hdet (PkgI4.decomp 5 σ)
      rw [PadicComplex.coe_eq, PadicComplex.coe_eq, PadicComplex.coe_eq, ← map_pow, ← map_mul]
      exact congrArg _ this
    rw [hd] at h1
    set Dg := (((ρL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl 5)).det : PadicAlgCl 5) : ℂ_[5]) with hDg
    set χσ := algebraMap ℚ_[5] ℂ_[5] (ZInQ.Contrib.G9.PkgI4.cycPow 5 σ 1) with hχσ
    set ψC := ((ψL σ : PadicAlgCl 5) : ℂ_[5]) with hψC
    have hχ0 : χσ ≠ 0 := by
      rw [hχσ, Ne, map_eq_zero_iff _ (algebraMap ℚ_[5] ℂ_[5]).injective]
      intro h0
      have := cycPow_neg_mul 5 σ 1
      rw [h0, mul_zero] at this
      exact zero_ne_one this
    have hDg0 : Dg ≠ 0 := by
      rw [hDg, PadicComplex.coe_eq, Ne, map_eq_zero_iff _ (algebraMap (PadicAlgCl 5) ℂ_[5]).injective]
      exact Matrix.GeneralLinearGroup.det_ne_zero _
    have ha : ZInQ.Contrib.G9.PkgI4.cpAct 5 σ dr = dr * (ψC ^ 2 * Dg) * χσ⁻¹ := by
      rw [h1]; field_simp
    have hb : ZInQ.Contrib.G9.PkgI4.cpAct 5 σ dg = dg * Dg * χσ⁻¹ := by
      rw [h2]; field_simp
    show ZInQ.Contrib.G9.PkgI4.cpAct 5 σ (dr / dg) = ψC ^ 2 * (dr / dg)
    rw [map_div₀, ha, hb]
    field_simp
  have hψc : Continuous fun σ => (ψL σ : PadicAlgCl 5) := (continuous_char ψ).comp hdc
  obtain ⟨E', hE'fd, hE'gal, hEE', c, hc0, hc⟩ := exists_sqrt_twist 5 E ψL hψc y hy0 hy
  haveI := hE'fd
  haveI := hE'gal
  obtain ⟨ψE, hψElift, hψEHT⟩ :=
    hasHTWeights_zero_of_twist 5 E' ψL (fun σ => hEE' (hψE σ)) c hc0 hc
  exact ⟨E', hE'fd, ψE, hψElift, hψEHT⟩

end TwistHT

/-- **`TwistCharHTWt0` proved** (provider name). -/
theorem twistCharHTWt0_proof : TwistCharHTWt0 := TwistHT.twistCharHTWt0_proof

end HDec.G0Galois.C8Conrad
