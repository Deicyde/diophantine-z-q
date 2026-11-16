theorem qmReciprocityL3_of_ek (hM : ∃ ε : ℤˣ, MainTheoremCMEK ε) (hC : ZInQ.HomUnify.HomLatticeCorr) :
    QMReciprocityL3 := by
  obtain ⟨ε, hMain⟩ := hM
  refine ⟨ε, true, ?_⟩
  intro K _ _ _ hK κ q z hz σ s hs g P P' hbc hP
  simp only [if_true] at hz
  haveI : Fact (Irreducible (X ^ 2 - C (2 : K))) := ⟨irr_fE hK⟩
  haveI : IsCMField (EK K) := isCMField_EK hK
  obtain ⟨Φu, hU, hI, hL⟩ := hP
  obtain ⟨g0, hpb, hιbc, hηbc⟩ := hbc
  set Φ := PhiE κ with hΦ
  set 𝔞 : AddSubgroup (EK K) := (latB g).comap (beta q).toAddMonoidHom with h𝔞
  set u : BAQˣ := qHatU q s ^ (ε : ℤ) with hu
  set t : AQ ⊗[ℚ] EK K := ((reflexNorm rhoK (IdeleGroup.toFiniteIdele (𝓞 K) K s) ^ (ε : ℤ) :
      (AQ ⊗[ℚ] EK K)ˣ) : AQ ⊗[ℚ] EK K) with ht
  have hβ : ∀ x : LeafQM.B, beta q ((betaE hK hz).symm x) = x := fun x => by
    rw [← betaE_apply hK hz, LinearEquiv.apply_symm_apply]
  -- `θ = Φ_u ∘ D_z`, uniformizing `A` by `Φ(𝔞)`
  let θ : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ) := fun w => Φu (Dz z w)
  have hθ : ∀ e, θ (cmVec Φ e) = Φu ((iotaC (beta q e)).mulVec ![(z : ℂ), 1]) := fun e => by
    rw [vec_beta' hz]
  have hlat : cmLat Φ 𝔞 = (vecLat (z : ℂ) g).map ((Dz z).symm.toLinearMap.restrictScalars ℤ) := by
    rw [← cmLat_map_Dz hK hz 𝔞 g (fun e => Iff.rfl), map_symm_map]
  have hθU : IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ := by
    rw [hlat]
    convert HDec.HSyn.G0Split.FibreQM.isUniformization_comp hU (Dz z).symm using 2
    simp [θ]
  -- `(A, θ)` is of type `(E, Φ)`
  have hType : IsOfType Φ 𝔞 θ := by
    intro e he
    let M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := Matrix.mulVecLin (Matrix.diagonal fun i => Φ i e)
    have hMv : ∀ v, M v = fun i => Φ i e * v i := fun v => by
      funext i; simp [M, Matrix.mulVec_diagonal]
    have hMD : ∀ e', M (Dz z (cmVec Φ e')) = Dz z (cmVec Φ (e * e')) := fun e' => by
      rw [hMv]; funext i; fin_cases i <;> simp [Dz_apply, cmVec] <;> ring
    have hMΛ : ∀ v ∈ vecLat (z : ℂ) g, M v ∈ vecLat (z : ℂ) g := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := mem_vecLat.1 hv
      obtain ⟨e', rfl⟩ := (betaE hK hz).surjective x
      rw [betaE_apply, vec_beta' hz, hMD, ← vec_beta' hz]
      exact mem_vecLat.2 ⟨_, he _ hx, rfl⟩
    obtain ⟨f, hf, -⟩ := hC.2 P.A P.A 2 2 _ _ Φu Φu (dim_two P) (dim_two P) hU hU M hMΛ
    refine ⟨f, fun w => ?_⟩
    show Φu (Dz z (fun i => Φ i e * w i)) = Φu (Dz z w) ≫ f.hom
    rw [← hf]
    congr 1
    rw [hMv]; funext i; fin_cases i <;> simp [Dz_apply] <;> ring
  -- the identity sections correspond
  have h1pt : (1 : CPts P'.A (RingHom.id ℂ)).left ≫ g0 =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts P.A (RingHom.id ℂ)).left := by
    have e := hηbc 0
    simp only [map_zero, toMul_zero] at e
    exact e
  -- apply the main theorem of CM
  obtain ⟨θ', hθ'U, hrel⟩ := hMain K hK κ σ s hs P.A (dim_two P) 𝔞 θ hθU hType P'.A g0 hpb h1pt
  rw [← ht] at hθ'U hrel
  -- dictionary
  have hbt : ∀ w, betaHat q (t * w) = betaHat q w * u := betaHat_t q s ε
  have hact : ∀ e, e ∈ latAct t 𝔞 ↔ beta q e ∈ latB (u * g) := by
    intro e
    show t * (1 ⊗ₜ e) ∈ latHat 𝔞 ↔ bEmb (beta q e) * ((u * g : BAQˣ) : BAQ) ∈ OhatQ
    rw [mem_latHat_iff hK hz g, hbt, betaHat_one_tmul, Units.val_mul, mul_assoc]
  have hrelB : ∀ x y : EK K, (bEmb (beta q y) * u - bEmb (beta q x)) * g ∈ OhatQ →
      (θ' (cmVec Φ y)).left ≫ g0 = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫
        (Φu ((iotaC (beta q x)).mulVec ![(z : ℂ), 1])).left := by
    intro x y hxy
    rw [← hθ x]
    apply hrel x y
    rw [mem_latHat_iff hK hz g, map_sub, hbt, betaHat_one_tmul, betaHat_one_tmul]
    exact hxy
  -- `Φ_u' = θ' ∘ D_z⁻¹`
  let Φu' : (Fin 2 → ℂ) → CPts P'.A (RingHom.id ℂ) := fun v => θ' ((Dz z).symm v)
  have hθ' : ∀ e, Φu' ((iotaC (beta q e)).mulVec ![(z : ℂ), 1]) = θ' (cmVec Φ e) := fun e => by
    show θ' ((Dz z).symm _) = _
    rw [vec_beta' hz, LinearEquiv.symm_apply_apply]
  have hU' : IsUniformization (RingHom.id ℂ) (vecLat (z : ℂ) (u * g)) Φu' := by
    rw [← cmLat_map_Dz hK hz (latAct t 𝔞) (u * g) hact]
    exact HDec.HSyn.G0Split.FibreQM.isUniformization_comp hθ'U (Dz z)
  -- the conjugate of `Φ_u(v_x)` is `Φ_u'(v_y)`
  have hconj : ∀ x y : EK K, (bEmb (beta q y) * u - bEmb (beta q x)) * g ∈ OhatQ →
      (Φu' ((iotaC (beta q y)).mulVec ![(z : ℂ), 1])).left ≫ g0 =
        Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫
          (Φu ((iotaC (beta q x)).mulVec ![(z : ℂ), 1])).left := by
    intro x y hxy
    rw [hθ']
    exact hrelB x y hxy
  have hexists : ∀ y : EK K, ∃ x : EK K, (bEmb (beta q y) * u - bEmb (beta q x)) * g ∈ OhatQ := by
    intro y
    obtain ⟨x0, hx0⟩ := exists_approx (bEmb (beta q y) * u) g
    refine ⟨(betaE hK hz).symm x0, ?_⟩
    rw [hβ]
    have e : (bEmb (beta q y) * u - bEmb x0) * g = -((bEmb x0 - bEmb (beta q y) * u) * g) := by noncomm_ring
    rw [e]; exact OhatQ_neg hx0
  refine ⟨Φu', hU', ?_, ?_⟩
  · -- `ι`-compatibility
    intro a v
    obtain ⟨T, hT⟩ := hC.1 ℂ P'.A P'.A (RingHom.id ℂ) 2 2 _ _ Φu' Φu' (dim_two P') (dim_two P') hU' hU'
      (P'.q.iota a)
    let Dl : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := T - Matrix.mulVecLin (iotaC (a : LeafQM.B))
    have h1 : ∀ y : EK K, Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) ∈ vecLat (z : ℂ) (u * g) := by
      intro y
      obtain ⟨x, hxy⟩ := hexists y
      have hya : (iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) =
          (iotaC (beta q ((betaE hK hz).symm ((a : LeafQM.B) * beta q y)))).mulVec ![(z : ℂ), 1] := by
        rw [hβ, map_mul, ← Matrix.mulVec_mulVec]
      have hxa : (iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q x)).mulVec ![(z : ℂ), 1]) =
          (iotaC (beta q ((betaE hK hz).symm ((a : LeafQM.B) * beta q x)))).mulVec ![(z : ℂ), 1] := by
        rw [hβ, map_mul, ← Matrix.mulVec_mulVec]
      have hxya : (bEmb (beta q ((betaE hK hz).symm ((a : LeafQM.B) * beta q y))) * u -
          bEmb (beta q ((betaE hK hz).symm ((a : LeafQM.B) * beta q x)))) * g ∈ OhatQ := by
        rw [hβ, hβ, map_mul, map_mul, mul_assoc, ← mul_sub, mul_assoc]
        exact OhatQ_mul (bEmb_mem_of_inO a.2) hxy
      have heq : Φu' (T ((iotaC (beta q y)).mulVec ![(z : ℂ), 1])) =
          Φu' ((iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q y)).mulVec ![(z : ℂ), 1])) := by
        apply pt_ext hpb
        have hI' := hI a ((iotaC (beta q x)).mulVec ![(z : ℂ), 1])
        rw [qmMat_eq, hxa] at hI'
        rw [hT, Over.comp_left, Category.assoc, hιbc a, ← Category.assoc, hconj x y hxy, hya,
          hconj _ _ hxya, hI', Over.comp_left]
        exact Category.assoc _ _ _
      have hone : Φu' (Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1])) = 1 := by
        have e := hU'.1 (Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]))
          ((iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]))
        have e2 : Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) +
            (iotaC (a : LeafQM.B)).mulVec ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) =
            T ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) := by
          rw [LinearMap.sub_apply, Matrix.mulVecLin_apply, sub_add_cancel]
        rw [e2, heq] at e
        exact (mul_eq_right.1 e.symm)
      exact (hU'.2.1 _).1 hone
    have h2 : ∀ y : EK K, Dl ((iotaC (beta q y)).mulVec ![(z : ℂ), 1]) = 0 := by
      intro y
      obtain ⟨x0, -, hx0e⟩ := mem_vecLat.1 (h1 y)
      have hx0z : x0 = 0 := by
        apply eq_zero_of_forall_dvd (u * g) x0
        intro N hN
        obtain ⟨xN, hxN, hxNe⟩ := mem_vecLat.1 (h1 ((N : ℚ)⁻¹ • y))
        refine ⟨xN, hxN, vec_inj hK hz ?_⟩
        have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
        rw [iotaC_smul_mulVec, hxNe, hx0e, map_smul, iotaC_smul_mulVec, map_smul, smul_smul]
        push_cast
        rw [mul_inv_cancel₀ hN0, one_smul]
      rw [← hx0e, hx0z, map_zero, Matrix.zero_mulVec]
    have hDl : Dl = 0 := by
      apply LinearMap.ext
      intro w
      have e1 := h2 1
      have e2 := h2 (AdjoinRoot.root _)
      rw [vec_beta' hz] at e1 e2
      have hw := span_two κ ((Dz z).symm w)
      rw [LinearMap.zero_apply, ← LinearEquiv.apply_symm_apply (Dz z) w, hw, map_add, map_smul, map_smul,
        map_add, map_smul, map_smul, e1, e2, smul_zero, smul_zero, add_zero]
    have hTv : T v = (iotaC (a : LeafQM.B)).mulVec v := by
      have := LinearMap.congr_fun hDl v
      simp only [Dl, LinearMap.sub_apply, LinearMap.zero_apply, Matrix.mulVecLin_apply] at this
      exact sub_eq_zero.1 this
    rw [← hT v, hTv, qmMat_eq]
  · -- the level structure
    intro a
    obtain ⟨x0, ⟨y0, hy0, hx0⟩, hΦx0⟩ := hL a
    have hxE : beta q ((betaE hK hz).symm ((1 / 3 : ℚ) • x0)) = (1 / 3 : ℚ) • x0 := hβ _
    obtain ⟨y1, hy1⟩ := exists_approx (bEmb (beta q ((betaE hK hz).symm ((1 / 3 : ℚ) • x0))) *
      ((u⁻¹ : BAQˣ) : BAQ)) ((u * g : BAQˣ) : BAQ)
    have hyE : beta q ((betaE hK hz).symm y1) = y1 := hβ _
    set xE := (betaE hK hz).symm ((1 / 3 : ℚ) • x0) with hxEdef
    have hc : (bEmb (beta q ((betaE hK hz).symm y1)) * u - bEmb (beta q xE)) * g ∈ OhatQ := by
      have e : (bEmb (beta q ((betaE hK hz).symm y1)) * u - bEmb (beta q xE)) * g =
          (bEmb y1 - bEmb (beta q xE) * ((u⁻¹ : BAQˣ) : BAQ)) * ((u * g : BAQˣ) : BAQ) := by
        rw [hyE, Units.val_mul, sub_mul, sub_mul, mul_assoc, mul_assoc (bEmb (beta q xE)),
          ← mul_assoc ((u⁻¹ : BAQˣ) : BAQ), Units.inv_mul, one_mul, ← mul_assoc]
      rw [e]; exact hy1
    have hpt : Φu' ((iotaC y1).mulVec ![(z : ℂ), 1]) = Additive.toMul (P'.e.eta a) := by
      apply pt_ext hpb
      have h3 : (((1 / 3 : ℚ)) : ℂ) = (3 : ℂ)⁻¹ := by push_cast; ring
      rw [← hyE]
      refine (hconj xE _ hc).trans (Eq.trans ?_ (hηbc a).symm)
      rw [hxE, iotaC_smul_mulVec, h3, hΦx0]
    refine ⟨(3 : ℚ) • y1, ⟨(bEmb (beta q ((betaE hK hz).symm y1)) * u - bEmb (beta q xE)) * g + y0,
      OhatQ_add hc hy0, ?_⟩, ?_⟩
    · have h3 : (3 : BAQ) * (bEmb (beta q xE) * g) = bEmb (a : LeafQM.B) + 3 * y0 := by
        rw [hxE, map_smul, smul_mul_assoc, three_mul_eq_smul, smul_smul]
        norm_num
        exact hx0
      have e : bEmb (a : LeafQM.B) + 3 * ((bEmb (beta q ((betaE hK hz).symm y1)) * u - bEmb (beta q xE)) * g + y0) =
          bEmb (a : LeafQM.B) + 3 * (bEmb y1 * u * g) - (3 : BAQ) * (bEmb (beta q xE) * g) + 3 * y0 := by
        rw [hyE]; noncomm_ring
      rw [e, h3, map_smul, ← three_mul_eq_smul, Units.val_mul]
      noncomm_ring
    · rw [iotaC_smul_mulVec, smul_smul]
      push_cast
      rw [inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]
      exact hpt

