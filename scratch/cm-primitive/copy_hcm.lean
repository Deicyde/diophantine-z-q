theorem shimuraMainCM_of_arithPrim (hM : MainTheoremCMSignPrim 1) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar) (hH : ZInQ.HomUnify.HomLatticeCorr) :
    T5Glue.ShimuraMainCM := by
  intro m _ hsq e he σ s hs 𝔞 P P' hP hP'
  obtain ⟨A, θ, U, x, y, hdim, hθ, hθU⟩ := hWA P
  let S : AddSubgroup (QNeg m) := P.lattice.toAddSubgroup.comap (kap m).toAddMonoidHom
  have hS : (S : Set (QNeg m)) = 𝔞 := by
    ext z
    change kap m z ∈ P.lattice ↔ z ∈ 𝔞
    rw [← SetLike.mem_coe, hP]
    constructor
    · rintro ⟨w, hw, hwz⟩
      rw [kap_apply] at hwz
      rwa [T5Glue.kappa_injective hwz] at hw
    · intro hz; exact ⟨z, hz, (kap_apply z).symm⟩
  obtain ⟨b₁, hb₁, hb₁'⟩ : ∃ b ∈ 𝔞, kappa m b = P.ω₁ := by
    have := P.ω₁_mem_lattice; rw [← SetLike.mem_coe, hP] at this; exact this
  obtain ⟨b₂, hb₂, hb₂'⟩ : ∃ b ∈ 𝔞, kappa m b = P.ω₂ := by
    have := P.ω₂_mem_lattice; rw [← SetLike.mem_coe, hP] at this; exact this
  have hb : ∀ z, z ∈ 𝔞 ↔ ∃ n₁ n₂ : ℤ, z = n₁ * b₁ + n₂ * b₂ := by
    intro z
    constructor
    · intro hz
      have hk : kappa m z ∈ P.lattice := by rw [← SetLike.mem_coe, hP]; exact ⟨z, hz, rfl⟩
      obtain ⟨n₁, n₂, hn⟩ := PeriodPair.mem_lattice.1 hk
      refine ⟨n₁, n₂, T5Glue.kappa_injective ?_⟩
      rw [T5Glue.kappa_add, T5Glue.kappa_intCast_mul, T5Glue.kappa_intCast_mul, hb₁', hb₂', hn]
    · rintro ⟨n₁, n₂, rfl⟩
      rw [← hS]
      have h1 : b₁ ∈ S := by rw [← SetLike.mem_coe, hS]; exact hb₁
      have h2 : b₂ ∈ S := by rw [← SetLike.mem_coe, hS]; exact hb₂
      rw [← zsmul_eq_mul, ← zsmul_eq_mul]
      exact add_mem (zsmul_mem h1 n₁) (zsmul_mem h2 n₂)
  -- `t = N(s)` and the lattice of `A^σ`
  set t : AQ ⊗[ℚ] QNeg m := ((reflexNorm rhoQ (IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s) ^
    ((1 : ℤˣ) : ℤ) : (AQ ⊗[ℚ] QNeg m)ˣ) : AQ ⊗[ℚ] QNeg m) with ht_def
  have ht : t = (eK m).symm (T5Glue.finPart s) := by
    rw [ht_def, Units.val_one, zpow_one, reflexNorm_rhoQ]; rfl
  have htmul : ∀ z : QNeg m, t * (1 ⊗ₜ z) =
      (eK m).symm (T5Glue.finPart s * algebraMap (QNeg m) (T5Glue.AfK m) z) := by
    intro z; rw [ht, map_mul, finiteAdeleBaseChangeAlgEquiv_symm_algebraMap]
  have hadel := adelic 𝔞 S hS b₁ b₂ hb
  have hlat : (latAct t S : Set (QNeg m)) = T5Glue.sInvLat m s 𝔞 := by
    ext z
    change t * Algebra.TensorProduct.includeRight z ∈ QMRecPrinted.latHat S ↔ _
    rw [Algebra.TensorProduct.includeRight_apply, htmul, hadel, AlgEquiv.apply_symm_apply]
    rfl
  -- the main theorem of CM
  obtain ⟨θ', hθ', hrel⟩ := hM (QNeg m) 1 (fun _ => kap m) (by rw [finrank_QNeg]) type_inj
    (isPrimitiveType_of_finrank_two _ finrank_QNeg type_inj) (QNeg m) (kap m)
    reflex_range 1 rhoQ jQ model σ s (artinCondC_of_artinCond e he σ s hs) A hdim S θ
    (by rw [cmLat_eq S P (by rw [hP, hS])]; exact hθ)
    (isOfType_of_corr hH A hdim θ P hθ S (by rw [hP, hS]))
    (bcC A (σ : ℂ →+* ℂ)) (projC A (σ : ℂ →+* ℂ)) (isPullback_bc σ A) (one_left_bc σ A)
  have hθ'' : IsUniformization (RingHom.id ℂ) (lat1 P') θ' := by
    rw [cmLat_eq _ P' (by rw [hP', hlat])] at hθ'
    exact hθ'
  obtain ⟨ν, hν, hcoord⟩ := core hWP hWU σ P P' A θ U x y hθ hθU θ' hθ''
  refine ⟨ν, hν, fun u v hu huv => ?_⟩
  have hmem : t * (1 ⊗ₜ v) - 1 ⊗ₜ u ∈ QMRecPrinted.latHat S := by
    rw [htmul, ← finiteAdeleBaseChangeAlgEquiv_symm_algebraMap, ← map_sub, hadel,
      AlgEquiv.apply_symm_apply]
    exact huv
  have hr := hrel u v hmem
  have hcv : ∀ z : QNeg m, cmVec (fun _ : Fin 1 => kap m) z = fun _ => kappa m z :=
    fun z => funext fun _ => kap_apply z
  rw [hcv, hcv] at hr
  exact hcoord (kappa m u) (kappa m v) hu hr


