import ZInQKernel.Contrib.OneProof.RC.CMField2.Factorization
import ZInQKernel.Contrib.OneProof.RC.CMField2.Cyclic
import ZInQKernel.Contrib.OneProof.RC.CMField2.Lattices
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_jLattice_ofTau
import ZInQKernel.Contrib.OneProof.RC.CMField2.Diagonal
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_jLattice_surjective
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic

/-! The primitive triangular representatives give cyclic sublattices,
including at specialized j-values. On-the-spot calculation (c). -/

noncomputable section
open UpperHalfPlane Polynomial ModularCurve Module Matrix

namespace ZInQ.Manuscript.RC.CMField2

/-- Each root of the specialized modular polynomial comes from a cyclic
index-N sublattice of the period lattice with basis (τ,1). -/
theorem exists_cyclic_sublattice_of_modularPolynomial_root (N : ℕ) [NeZero N]
    (P : ModularPolynomialData N) (τ : ℍ) (j : ℂ)
    (hj : (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (X0Model.analyticJ τ))).IsRoot j) :
    let L := PeriodPair.ofTau τ
    ∃ M : PeriodPair, M.lattice ≤ L.lattice ∧ L.sublatticeIndex M = N ∧
      IsAddCyclic (L.sublatticeQuotient M) ∧ M.jLattice = j := by
  obtain ⟨⟨a,b,d⟩, ht, hv⟩ := exists_coset_of_modularPolynomial_root N P τ j hj
  obtain ⟨had, _, hprim⟩ := (mem_primCosetReps (NeZero.ne N)).mp ht
  have hd : d ≠ 0 := by intro hd; apply NeZero.ne N; simpa [hd] using had.symm
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  let u : ℂˣ := Units.mk0 _ hdC
  let τ' := cosetParameter (a,b,d) τ
  let M := (PeriodPair.ofTau τ').scale u
  let L := PeriodPair.ofTau τ
  let B := L.latticeBasis
  have hM0 : M.ω₁ = (a : ℂ) * (τ : ℂ) + (b : ℂ) := by
    change (d : ℂ) * (τ' : ℂ) = _
    rw [coe_cosetParameter (NeZero.ne N) ht]
    exact mul_div_cancel₀ _ hdC
  have hM1 : M.ω₂ = (d : ℂ) := by change (d : ℂ) * 1 = _; rw [mul_one]
  have hB0 : (B 0 : ℂ) = (τ : ℂ) := L.latticeBasis_zero
  have hB1 : (B 1 : ℂ) = 1 := L.latticeBasis_one
  let v : Fin 2 → L.lattice := ![(a : ℤ) • B 0 + (b : ℤ) • B 1, (d : ℤ) • B 1]
  have hv0 : (v 0 : ℂ) = M.ω₁ := by
    simp [v, hB0, hB1, hM0]
  have hv1 : (v 1 : ℂ) = M.ω₂ := by
    simp [v, hB1, hM1]
  have hsub : M.lattice ≤ L.lattice := by
    rw [PeriodPair.lattice]
    apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [← hv0]; exact (v 0).property
    · rw [← hv1]; exact (v 1).property
  have hrepr (i : Fin 2) :
      (⟨(M.latticeBasis i : ℂ), hsub (M.latticeBasis i).property⟩ : L.lattice) = v i := by
    apply Subtype.ext
    fin_cases i
    · simpa using hv0.symm
    · simpa using hv1.symm
  have hmat : B.toMatrix v = !![(a : ℤ), 0; (b : ℤ), (d : ℤ)] := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [Basis.toMatrix_apply, v, Basis.repr_self]
  have hi : L.sublatticeIndex M = N := by
    change M.lattice.toAddSubgroup.relIndex L.lattice.toAddSubgroup = N
    rw [AddSubgroup.relIndex_eq_natAbs_det (L₁ := M.lattice.toAddSubgroup)
      (L₂ := L.lattice.toAddSubgroup) (show M.lattice.toAddSubgroup ≤ L.lattice.toAddSubgroup from hsub)
      M.latticeBasis B]
    change (B.det (fun i => (⟨(M.latticeBasis i : ℂ), hsub (M.latticeBasis i).property⟩ :
      L.lattice))).natAbs = N
    simp_rw [hrepr]
    rw [Basis.det_apply, hmat, Matrix.det_fin_two_of]
    simpa only [zero_mul, sub_zero, Int.natAbs_mul, Int.natAbs_natCast] using had
  have hc : IsAddCyclic (L.sublatticeQuotient M) := by
    apply isAddCyclic_sublatticeQuotient_of_primitive L M hsub
    intro k hk h
    have hdvd (i r : Fin 2) : (k : ℤ) ∣ B.repr (v i) r := by
      let w := M.latticeBasis i
      obtain ⟨y,hy,he⟩ := h (w : ℂ) w.property
      have he' : v i = (k : ℤ) • (⟨y,hy⟩ : L.lattice) := by
        rw [← hrepr i]
        exact Subtype.ext he
      refine ⟨B.repr ⟨y,hy⟩ r, ?_⟩
      rw [he', map_smul, Finsupp.smul_apply, smul_eq_mul]
    have h₁ : k ∣ a := by
      apply Int.natCast_dvd_natCast.mp
      simpa [v, Basis.repr_self, Finsupp.single_apply] using hdvd 0 0
    have h₂ : k ∣ b := by
      apply Int.natCast_dvd_natCast.mp
      simpa [v, Basis.repr_self, Finsupp.single_apply] using hdvd 0 1
    have h₃ : k ∣ d := by
      apply Int.natCast_dvd_natCast.mp
      simpa [v, Basis.repr_self, Finsupp.single_apply] using hdvd 1 1
    have h₄ := Nat.dvd_gcd h₁ (Nat.dvd_gcd h₂ h₃)
    rw [hprim] at h₄
    exact (Nat.ne_of_gt hk) (Nat.dvd_one.mp h₄)
  exact ⟨M, hsub, hi, hc, (jLattice_scale _ _).trans ((PeriodPair.jLattice_ofTau _).trans hv)⟩

/-- Every complex number is the j-value of an upper half-plane parameter. -/
theorem exists_analyticJ_eq (j : ℂ) : ∃ τ : ℍ, X0Model.analyticJ τ = j := by
  obtain ⟨L, _, hL⟩ := PeriodPair.jLattice_surjective j
  have hi : L.sublatticeIndex L = 1 := AddSubgroup.relIndex_self _
  have hc : IsAddCyclic (L.sublatticeQuotient L) := by
    let : Subsingleton (L.sublatticeQuotient L) :=
      (Nat.card_eq_one_iff_unique.mp (by
        simpa only [PeriodPair.sublatticeIndex, AddSubgroup.index_eq_card] using hi)).1
    infer_instance
  obtain ⟨_, _, _, τ, _, _, _, hj, _⟩ :=
    PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic L L
      (fun _ h => h) hi hc
  exact ⟨τ, (PeriodPair.jLattice_ofTau τ).symm.trans (hj.symm.trans hL)⟩

/-- Every cyclic self-isogeny degree detected by the modular polynomial
remains visible in a conjugate j-value. -/
theorem conjugate_has_cyclic_self_of_root {F : Type*} [Field F] (x : F)
    (e f : F →+* ℂ) (N : ℕ) [NeZero N] (P : ModularPolynomialData N)
    (hroot : (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (e x))).IsRoot (e x)) :
    ∃ τ : ℍ, X0Model.analyticJ τ = f x ∧
      let L := PeriodPair.ofTau τ
      ∃ M : PeriodPair, M.lattice ≤ L.lattice ∧ L.sublatticeIndex M = N ∧
        IsAddCyclic (L.sublatticeQuotient M) ∧ M.jLattice = L.jLattice := by
  obtain ⟨τ, hτ⟩ := exists_analyticJ_eq (f x)
  have h : (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (f x))).IsRoot (f x) := by
    have hm := (rootMultiplicity_pos (P.monic.map
      (eval₂RingHom (Int.castRingHom ℂ) (e x))).ne_zero).mpr hroot
    rw [rootMultiplicity_specialization_eq_of_embeddings P.Φ e f x] at hm
    exact (rootMultiplicity_pos (P.monic.map
      (eval₂RingHom (Int.castRingHom ℂ) (f x))).ne_zero).mp hm
  refine ⟨τ, hτ, ?_⟩
  obtain ⟨M, hM, hi, hc, hj⟩ :=
    exists_cyclic_sublattice_of_modularPolynomial_root N P τ (f x) (by rwa [hτ])
  exact ⟨M, hM, hi, hc, hj.trans ((PeriodPair.jLattice_ofTau τ).trans hτ).symm⟩


end ZInQ.Manuscript.RC.CMField2
