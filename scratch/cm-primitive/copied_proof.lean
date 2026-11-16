theorem mainTheoremCMSignPrim_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolPrimSign ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMSignPrim ε := by
  have hH : ZInQ.HomUnify.HomLatticeCorr := AvSplit.Final.h69 hUL hG
  intro E _ _ _ g Φ hdeg hinj hprim Er _ _ κr hκ n ρ j hρ σ s hs A hdimA 𝔞 θ hθ htype A' h hpb hone
  set t : AQ ⊗[ℚ] E := ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) :
    AQ ⊗[ℚ] E) with ht
  have hg : 0 < g := by
    have := Module.finrank_pos (R := ℚ) (M := E); omega
  obtain ⟨⟨N, hN, hNa⟩, ⟨d, hd, hda⟩⟩ := lattice_of_unif hUL Φ hg hdeg hθ
  -- the `𝓞_E`-lattice `𝔟 = N 𝓞_E ⊆ 𝔞`
  let 𝔟 : AddSubgroup E := nO N
  have hb_le : 𝔟 ≤ 𝔞 := fun x hx => by obtain ⟨o, rfl⟩ := mem_nO.1 hx; exact hNa o
  have hm : ∀ x ∈ 𝔞, ((N * d : ℕ) : E) * x ∈ 𝔟 := by
    intro x hx
    refine mem_nO.2 ⟨⟨(d : E) * x, hda x hx⟩, ?_⟩
    show (N : E) * ((d : E) * x) = _
    push_cast; ring
  have hmpos : 0 < N * d := Nat.mul_pos hN hd
  have hbdense : ∀ e : E, ∃ k : ℕ, 0 < k ∧ (k : E) * e ∈ 𝔟 := by
    intro e
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hye := natAbs_mul_integral (hy e (Finset.mem_singleton_self e))
    refine ⟨N * y.natAbs, Nat.mul_pos hN (Int.natAbs_pos.2 hy0), mem_nO.2 ⟨⟨_, hye⟩, ?_⟩⟩
    show (N : E) * ((y.natAbs : E) * e) = _
    push_cast; ring
  have hOL : IsOLattice 𝔟 := by
    refine ⟨fun o x hx => ?_, ⟨N, hN, fun o => mem_nO.2 ⟨o, rfl⟩⟩, ⟨1, one_pos, fun x hx => ?_⟩⟩
    · obtain ⟨o', rfl⟩ := mem_nO.1 hx
      exact mem_nO.2 ⟨o * o', by push_cast; ring⟩
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      have := coe_integral ((N : 𝓞 E) * o)
      push_cast at this
      rw [Nat.cast_one, _root_.one_mul]; exact this
  -- step (2): the Riemann-form datum
  obtain ⟨ζ0, hζc, hζi⟩ := exists_zeta Φ hinj
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {ζ0}
  have hyζ := hy ζ0 (Finset.mem_singleton_self ζ0)
  have hζint : IsIntegral ℤ ((y * y) • ζ0) := by
    rw [mul_smul, zsmul_eq_mul]
    exact (by simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := y)) : IsIntegral ℤ (y : E)).mul hyζ
  have hζ : IsRiemannDatum Φ 𝔟 ((y * y) • ζ0) := by
    refine ⟨by rw [map_zsmul, hζc, smul_neg], fun i => ?_, fun x hx x' hx' => ?_⟩
    · rw [map_zsmul, zsmul_eq_mul, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero]
      exact mul_pos (by exact_mod_cast mul_self_pos.2 hy0) (hζi i)
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      obtain ⟨o', rfl⟩ := mem_nO.1 hx'
      apply trace_int
      have h1 : IsIntegral ℤ ((N : E) * (o : E)) := by
        have := coe_integral ((N : 𝓞 E) * o); push_cast at this; exact this
      have h2 : IsIntegral ℤ ((N : E) * (o' : E)) := by
        have := coe_integral ((N : 𝓞 E) * o'); push_cast at this; exact this
      exact (hζint.mul h1).mul (h2.map (IsCMField.complexConj E))
  -- the abelian variety `B₀ = ℂ^g/Φ(N𝓞_E)` and the isogeny `μ : B₀ → A`
  obtain ⟨B, θB, hdimB, hθB⟩ := hX E g Φ hdeg hinj 𝔟 hOL ⟨_, hζ⟩
  have htypeB : IsOfType Φ 𝔟 θB := by
    intro e he
    let Me : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun w i => Φ i e * w i
        map_add' := fun w w' => by funext i; simp [mul_add]
        map_smul' := fun c w => by funext i; simp; ring }
    obtain ⟨f, hf, -⟩ := hH.2 B B g g (cmLat Φ 𝔟) (cmLat Φ 𝔟) θB θB hdimB hdimB hθB hθB Me
      (fun z hz => by
        obtain ⟨x, hx, rfl⟩ := mem_cmLat.1 hz
        exact mem_cmLat.2 ⟨e * x, he x hx, by funext i; simp [Me, cmVec]⟩)
    exact ⟨f, fun w => hf w⟩
  obtain ⟨mu, hμ, -⟩ := hH.2 B A g g (cmLat Φ 𝔟) (cmLat Φ 𝔞) θB θ hdimB hdimA hθB hθ LinearMap.id
    (fun z hz => by
      obtain ⟨x, hx, rfl⟩ := mem_cmLat.1 hz; exact mem_cmLat.2 ⟨x, hb_le hx, rfl⟩)
  have hμ' : ∀ z, θB z ≫ mu.hom = θ z := fun z => (hμ z).symm
  -- the main theorem for `B₀`
  obtain ⟨θB', hθB', hrelB⟩ := hP E g Φ hdeg hinj hprim Er κr hκ n ρ j hρ σ s hs B hdimB 𝔟 θB hθB htypeB hOL
    ⟨_, hζ⟩ (bcC B (σ : ℂ →+* ℂ)) (projC B (σ : ℂ →+* ℂ)) (isPullback_bc σ B) (one_left_bc σ B)
  -- the conjugate isogeny `μ^σ : B₀^σ → A'`
  have hsq : (projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left) ≫ A.X.hom =
      (bcC B (σ : ℂ →+* ℂ)).X.hom ≫ Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) := by
    rw [Category.assoc, Over.w mu.hom]; exact (isPullback_bc σ B).w
  let muL := hpb.lift (projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left) (bcC B (σ : ℂ →+* ℂ)).X.hom hsq
  have hmuL : muL ≫ h = projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left := hpb.lift_fst _ _ _
  let muO : (bcC B (σ : ℂ →+* ℂ)).X ⟶ A'.X := Over.homMk muL (hpb.lift_snd _ _ _)
  have hηB : η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ projC B (σ : ℂ →+* ℂ) =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[B.X].left := by
    have := one_left_bc σ B
    simp only [pl, one_left] at this
    exact this
  have hηA : η[A'.X].left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[A.X].left := by
    have := hone
    simp only [one_left] at this
    exact this
  have hμη : η[B.X].left ≫ mu.hom.left = η[A.X].left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hη : η[(bcC B (σ : ℂ →+* ℂ)).X] ≫ muO = η[A'.X] := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · calc (η[(bcC B (σ : ℂ →+* ℂ)).X] ≫ muO).left ≫ h
            = η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ muL ≫ h := by
              rw [Over.comp_left, Category.assoc]; rfl
          _ = η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left := by rw [hmuL]
          _ = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[A.X].left := by
              rw [← Category.assoc, hηB, Category.assoc, hμη]
          _ = η[A'.X].left ≫ h := hηA.symm
    · rw [Over.w, Over.w]
  haveI : IsMonHom muO := MulRigidity.isMonHom_of_geometricallyIntegral _ _ muO hη
  have key : ∀ P : CPts (bcC B (σ : ℂ →+* ℂ)) (RingHom.id ℂ),
      pl (P ≫ muO) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (dd σ B P ≫ mu.hom) := by
    intro P
    calc pl (P ≫ muO) ≫ h = (pl P ≫ muL) ≫ h := rfl
      _ = pl P ≫ (muL ≫ h) := Category.assoc _ _ _
      _ = pl P ≫ (projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left) := by rw [hmuL]
      _ = (pl P ≫ projC B (σ : ℂ →+* ℂ)) ≫ mu.hom.left := (Category.assoc _ _ _).symm
      _ = (sp (σ : ℂ →+* ℂ) ≫ pl (dd σ B P)) ≫ mu.hom.left := by rw [dd_key σ B P]
      _ = sp (σ : ℂ →+* ℂ) ≫ (pl (dd σ B P) ≫ mu.hom.left) := Category.assoc _ _ _
  have hone' : pl (1 : CPts A' (RingHom.id ℂ)) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (1 : CPts A (RingHom.id ℂ)) :=
    hone
  have hddrel : ∀ x y : E, t * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔟 →
      dd σ B (θB' (cmVec Φ y)) = θB (cmVec Φ x) := by
    intro x y hxy
    apply dd_unique σ B
    exact hrelB x y hxy
  have hsp : ∀ {P Q : CPts A (RingHom.id ℂ)},
      sp (σ : ℂ →+* ℂ) ≫ pl P = sp (σ : ℂ →+* ℂ) ≫ pl Q → P = Q := by
    intro P Q hPQ
    apply pl_ext
    have := congrArg (fun r => sp (σ.symm : ℂ →+* ℂ) ≫ r) hPQ
    rwa [← Category.assoc, ← Category.assoc, sp_symm_comp, Category.id_comp, Category.id_comp] at this
  let θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ) := fun z => θB' z ≫ muO
  -- the kernel
  have hker : ∀ z, θ' z = 1 ↔ z ∈ cmLat Φ (latAct t 𝔞) := by
    intro z
    constructor
    · intro hz
      have e2 : dd σ B (θB' z) ≫ mu.hom = 1 := by
        apply hsp
        rw [← key]
        show pl (θ' z) ≫ h = _
        rw [hz]; exact hone'
      obtain ⟨v, hv⟩ := hθB.2.2.1 (dd σ B (θB' z))
      have hv1 : θ v = 1 := by rw [← hμ', hv, e2]
      obtain ⟨x0, hx0, rfl⟩ := mem_cmLat.1 ((hθ.2.1 v).1 hv1)
      have hcm : ∀ (k : ℕ) (x : E), cmVec Φ ((k : E) * x) = k • cmVec Φ x := by
        intro k x; rw [← nsmul_eq_mul, map_nsmul]
      have hpow : θB' ((N * d) • z) = 1 := by
        rw [map_nsmul_of_hom hθB'.1]
        apply dd_injective σ B
        change ddHom σ B _ = ddHom σ B 1
        rw [map_pow, map_one]
        change (dd σ B (θB' z)) ^ (N * d) = 1
        rw [← hv, ← map_nsmul_of_hom hθB.1, ← hcm]
        exact (hθB.2.1 _).2 ((cmVec_mem_cmLat hg).2 (hm x0 hx0))
      obtain ⟨y1, hy1, hcy1⟩ := mem_cmLat.1 ((hθB'.2.1 _).1 hpow)
      let y : E := ((N * d : ℕ) : ℚ)⁻¹ • y1
      have hk0 : ((N * d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
      have hcy : cmVec Φ y = z := by
        show cmVec Φ (((N * d : ℕ) : ℚ)⁻¹ • y1) = z
        rw [cmVec_ratSmul, hcy1, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        push_cast
        rw [inv_mul_cancel₀ (by exact_mod_cast hk0), one_smul]
      obtain ⟨x, hx⟩ := exists_approx_latHat hbdense (t * (1 ⊗ₜ y))
      have h1 := hddrel x y hx
      rw [hcy] at h1
      have h2 : θB (cmVec Φ x) = θB (cmVec Φ x0) := by rw [← h1, hv]
      have hxx0 : x - x0 ∈ 𝔟 := by
        have := (hom_eq_iff hθB.1 _ _).1 h2
        rw [← map_sub] at this
        exact (cmVec_mem_cmLat hg).1 ((hθB.2.1 _).1 this)
      refine mem_cmLat.2 ⟨y, ?_, hcy⟩
      show t * (1 ⊗ₜ y) ∈ latHat 𝔞
      have e : t * (1 ⊗ₜ[ℚ] y) = (t * (1 ⊗ₜ y) - 1 ⊗ₜ x) + (1 : AQ) ⊗ₜ[ℚ] (x - x0) + (1 : AQ) ⊗ₜ[ℚ] x0 := by
        rw [TensorProduct.tmul_sub]; abel
      rw [e]
      exact add_mem (add_mem (latHat_mono hb_le hx) (latHat_mono hb_le (one_tmul_mem_latHat hxx0)))
        (one_tmul_mem_latHat hx0)
    · intro hz
      obtain ⟨y, hy, rfl⟩ := mem_cmLat.1 hz
      have hy' : t * (1 ⊗ₜ y) ∈ latHat 𝔞 := hy
      obtain ⟨x0, hx0, hrem⟩ := latHat_decomp hmpos hm hy'
      apply pt_ext hpb
      show pl (θB' (cmVec Φ y) ≫ muO) ≫ h = pl (1 : CPts A' (RingHom.id ℂ)) ≫ h
      rw [key, hddrel x0 y hrem, hμ', (hθ.2.1 _).2 (mem_cmLat.2 ⟨x0, hx0, rfl⟩), hone']
  -- surjectivity
  have hsurj : Function.Surjective θ' := by
    intro P
    have hQ : (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) ≫ A.X.hom = sp (RingHom.id ℂ) := by
      have hw : pl P ≫ A'.X.hom = sp (RingHom.id ℂ) := Over.w P
      rw [Category.assoc, Category.assoc, hpb.w, ← Category.assoc (pl P), hw, sp_id, Category.id_comp,
        sp_symm_comp]
    let Q : CPts A (RingHom.id ℂ) := Over.homMk (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) hQ
    obtain ⟨u, hu⟩ := hθ.2.2.1 Q
    obtain ⟨R, hR⟩ := dd_surjective σ B (θB u)
    obtain ⟨v, hv⟩ := hθB'.2.2.1 R
    refine ⟨v, pt_ext hpb ?_⟩
    show pl (θB' v ≫ muO) ≫ h = pl P ≫ h
    rw [key, hv, hR, hμ', hu]
    show sp (σ : ℂ →+* ℂ) ≫ (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) = pl P ≫ h
    rw [← Category.assoc, sp_comp_symm, Category.id_comp]
  -- the torsion relation
  have htors : ∀ x y : E, t * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
      (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left := by
    intro x y hxy
    obtain ⟨a, ha, hrem⟩ := latHat_decomp hmpos hm hxy
    have hrem' : t * (1 ⊗ₜ y) - 1 ⊗ₜ (x + a) ∈ latHat 𝔟 := by
      have e : t * (1 ⊗ₜ[ℚ] y) - (1 : AQ) ⊗ₜ[ℚ] (x + a) = t * (1 ⊗ₜ y) - 1 ⊗ₜ x - 1 ⊗ₜ a := by
        rw [TensorProduct.tmul_add]; abel
      rw [e]; exact hrem
    show pl (θB' (cmVec Φ y) ≫ muO) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (θ (cmVec Φ x))
    rw [key, hddrel _ _ hrem', hμ', map_add, hθ.1, (hθ.2.1 _).2 (mem_cmLat.2 ⟨a, ha, rfl⟩), _root_.mul_one]
  exact ⟨θ', (isUniformization_iff _ _ _).2
    ⟨isAnalyticHom_comp (isAnalyticHom_of_unif hθB') muO, hker, hsurj⟩, htors⟩

