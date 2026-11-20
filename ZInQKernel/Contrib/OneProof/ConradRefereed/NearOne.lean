import ZInQKernel.Contrib.OneProof.ConradRefereed.IdentityWeight

/-! A pure Hodge–Tate splitting supplies the periods for Serre's forward
implication. The resulting norm formula descends to a neighbourhood of 1 in `ℚ_pˣ`.
Provenance (c): tensor evaluation at the coefficient embeddings and descent of the norm formula. -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.SerreAppB

open HDec.G0Galois.C8Conrad.Bridges
open Module
open scoped TensorProduct Topology Filter

open _root_.ZInQ.Contrib.G9 (matRep)

variable (p : ℕ) [Fact p.Prime]

/-- A pure Hodge–Tate splitting gives a period for each coefficient embedding. -/
theorem serreTwistAdmissible_of_pureHT (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ) (h : PureHT p ψ n) (τ : K ≃ₐ[ℚ_[p]] K) :
    SerreTwistAdmissible p K ψ τ n := by
  classical
  obtain ⟨e, he⟩ := h
  let V := Fin 1 → K
  let T := ℂ_[p] ⊗[ℚ_[p]] V
  let D := Fin (finrank ℚ_[p] K)
  let ev : T →ₗ[ℂ_[p]] ℂ_[p] :=
    ((((IsScalarTower.toAlgHom ℚ_[p] K ℂ_[p]).toLinearMap).comp τ.toLinearMap).comp
      (LinearMap.proj (R := K) (φ := fun _ : Fin 1 => K) 0 |>.restrictScalars ℚ_[p])).liftBaseChange
        ℂ_[p]
  have ev_tmul (a : ℂ_[p]) (v : V) : ev (a ⊗ₜ[ℚ_[p]] v) = a * algebraMap K ℂ_[p] (τ (v 0)) := rfl
  have hev : ev ≠ 0 := by
    intro hzero
    have h1 := LinearMap.congr_fun hzero ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (fun _ : Fin 1 => (1 : K)))
    simp only [ev_tmul, map_one, mul_one, LinearMap.zero_apply, one_ne_zero] at h1
  obtain ⟨j, hj⟩ : ∃ j : D, ev (e.symm (Pi.single j 1)) ≠ 0 := by
    by_contra! hz
    apply hev
    apply ((Pi.basisFun ℂ_[p] D).map e.symm).ext
    intro k
    simpa only [Basis.map_apply, Pi.basisFun_apply, LinearMap.zero_apply] using hz k
  let z := e.symm (Pi.single j 1)
  refine ⟨ev z, hj, fun g => ?_⟩
  let σ := restrictGalois p K g
  have hσ : σ ∈ K.fixingSubgroup := (K.fixingSubgroupEquiv.symm g).2
  have hfix (k : K) :
      PkgI4.cpAct p σ (algebraMap K ℂ_[p] k) = algebraMap K ℂ_[p] k := by
    rw [IsScalarTower.algebraMap_apply K (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
      PkgI4.cpAct_coe]
    exact congrArg (fun x : PadicAlgCl p => (x : ℂ_[p])) (hσ k)
  let A0 : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] :=
    { toFun := PkgI4.cpAct p σ
      map_add' := map_add _
      map_smul' := fun a x => by simp only [RingHom.id_apply, Algebra.smul_def, map_mul,
        PkgI4.cpAct_algebraMap] }
  let A : T →ₗ[ℚ_[p]] T := TensorProduct.map A0 (matRep p (charRep ψ) σ)
  have A_tmul (a : ℂ_[p]) (v : V) : A (a ⊗ₜ[ℚ_[p]] v) =
      (PkgI4.cpAct p σ a) ⊗ₜ[ℚ_[p]]
        ((charRep ψ σ : Matrix (Fin 1) (Fin 1) K).mulVec v) := rfl
  have ev_A (x : T) :
      ev (A x) = algebraMap K ℂ_[p] (τ (ψ σ : K)) * PkgI4.cpAct p σ (ev x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a v =>
      rw [A_tmul, ev_tmul, ev_tmul, map_mul, hfix]
      have hm : ((charRep ψ σ : Matrix (Fin 1) (Fin 1) K).mulVec v) 0 = (ψ σ : K) * v 0 := by
        simp [Matrix.mulVec, dotProduct, charRep, Matrix.algebraMap_matrix_apply]
      rw [hm, map_mul τ, map_mul]
      ring
    | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  have e_A (x : T) (k : D) :
      e (A x) k = PkgI4.cycPow p σ n • PkgI4.cpAct p σ (e x k) := by
    induction x using TensorProduct.inductionOn with
    | tmul a v => simpa only [A_tmul] using he σ a v k
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, smul_add]
  have hAz : A z = PkgI4.cycPow p σ n • z := by
    apply e.injective
    ext k
    have hz : e z = Pi.single j 1 := e.apply_symm_apply _
    rw [e_A, LinearMapClass.map_smul_of_tower, Pi.smul_apply, hz]
    by_cases hk : k = j
    · subst k
      simp
    · simp [Pi.single_eq_of_ne hk]
  have eqn := ev_A z
  rw [hAz, LinearMapClass.map_smul_of_tower, Algebra.smul_def] at eqn
  have ha : algebraMap K ℂ_[p] (τ (ψ σ : K)) ≠ 0 :=
    (map_ne_zero _).mpr ((map_ne_zero τ).mpr (Units.ne_zero _))
  show _root_.ZInQ.Contrib.G9.PkgI4.cpAct p σ (ev z) =
    (algebraMap K ℂ_[p] (τ ((ψ σ : Kˣ) : K)))⁻¹ *
      algebraMap ℚ_[p] ℂ_[p] (_root_.ZInQ.Contrib.G9.PkgI4.cycPow p σ n) * ev z
  change algebraMap ℚ_[p] ℂ_[p] (_root_.ZInQ.Contrib.G9.PkgI4.cycPow p σ n) * ev z =
    algebraMap K ℂ_[p] (τ (ψ σ : K)) * _root_.ZInQ.Contrib.G9.PkgI4.cpAct p σ (ev z) at eqn
  rw [mul_assoc, eqn, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-- Ultrametric bound for a finite sum. Kind: proved. -/
theorem norm_sum_le_of_forall_le' {ι : Type*} (s : Finset ι) (f : ι → PadicAlgCl p) {r : ℝ}
    (hr0 : 0 ≤ r) (hf : ∀ i ∈ s, ‖f i‖ ≤ r) : ‖∑ i ∈ s, f i‖ ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A `d`-th root of unity in `ℚ̄_p` within `‖d‖` of `1` is `1`. Kind: proved. -/
theorem eq_one_of_pow_eq_one_of_norm_sub_lt {ζ : PadicAlgCl p} {d : ℕ} (hζ : ζ ^ d = 1)
    (h : ‖ζ - 1‖ < ‖(d : PadicAlgCl p)‖) : ζ = 1 := by
  by_contra hne
  have hd1 : ‖(d : PadicAlgCl p)‖ ≤ 1 :=
    (isUltrametricDist_iff_forall_norm_natCast_le_one).mp inferInstance d
  have hgeom : (∑ k ∈ Finset.range d, ζ ^ k) * (ζ - 1) = 0 := by
    rw [geom_sum_mul, hζ, sub_self]
  have hsum : ∑ k ∈ Finset.range d, ζ ^ k = 0 := by
    rcases mul_eq_zero.mp hgeom with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0) hne
  have hsplit : ∑ k ∈ Finset.range d, ζ ^ k =
      (d : PadicAlgCl p) + ∑ k ∈ Finset.range d, (ζ ^ k - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hk : ∀ k ∈ Finset.range d, ‖ζ ^ k - 1‖ ≤ ‖ζ - 1‖ := by
    intro k _
    have := norm_prod_sub_one_le p (Finset.range k) (fun _ => ζ) (norm_nonneg (ζ - 1))
      (h.le.trans hd1) (fun _ _ => le_rfl)
    simpa [Finset.prod_const, Finset.card_range] using this
  have hrest := norm_sum_le_of_forall_le' p (Finset.range d) (fun k => ζ ^ k - 1)
    (norm_nonneg _) hk
  have hlt : ‖∑ k ∈ Finset.range d, (ζ ^ k - 1)‖ < ‖(d : PadicAlgCl p)‖ := hrest.trans_lt h
  have hmax := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne'
  rw [← hsplit, hsum, norm_zero, max_eq_left hlt.le] at hmax
  exact absurd (h.trans_le hmax.symm.le) (not_lt.mpr (norm_nonneg _))

/-- **Conrad's near-one display from Serre.** `SerreA6NormEquivalence → ConradNearOne`.
Kind: proved from the named input `SerreA6NormEquivalence` (the proved norm form). -/
theorem conradNearOne_of_serre (h : SerreA6NormEquivalence) : ConradNearOne := by
  intro p _ K _ _ ψ i hc hHT
  refine ⟨i, (artinNearOneOnAbelianization_iff p ψ hc i).mp ?_⟩
  obtain ⟨U, hUo, hU⟩ := (h p K ψ hc (fun _ => i)).mp
    (fun τ => serreTwistAdmissible_of_pureHT p K ψ i hHT τ)
  have : Module.Free ℚ_[p] K := Module.Free.of_divisionRing _ _
  let d := finrank ℚ_[p] K
  let ι : ℚ_[p]ˣ →* Kˣ := Units.map (algebraMap ℚ_[p] K : ℚ_[p] →* K)
  have hιc : Continuous ι := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_induced_rng.mpr ((continuous_algebraMap ℚ_[p] (PadicAlgCl p)).comp
        Units.continuous_val))
    · exact (continuous_induced_rng.mpr ((continuous_algebraMap ℚ_[p] (PadicAlgCl p)).comp
        Units.continuous_coe_inv))
  have hV : ι ⁻¹' (U : Set Kˣ) ∈ 𝓝 (1 : ℚ_[p]ˣ) :=
    hιc.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by simp))
  let χA : ℚ_[p]ˣ →* Kˣ := (conradAbelianChar p ψ hc).toMonoidHom.comp
    (TauCeti.ClassFieldTheory.artinMap ℚ_[p])
  have hχAc : Continuous χA :=
    (conradAbelianChar p ψ hc).continuous.comp (TauCeti.ClassFieldTheory.continuous_artinMap _)
  let F : ℚ_[p]ˣ → K := fun y => ((χA y : Kˣ) : K) * algebraMap ℚ_[p] K (y : ℚ_[p]) ^ i
  have hFpow : ∀ y ∈ ι ⁻¹' (U : Set Kˣ), F y ^ d = 1 := by
    intro y hy
    obtain ⟨-, hy2⟩ := hU (ι y) hy
    have hN : TauCeti.Algebra.normUnits ℚ_[p] (ι y) = y ^ d :=
      TauCeti.Algebra.normUnits_unitsMap_algebraMap ℚ_[p] y
    have hprod : ∏ τ : K ≃ₐ[ℚ_[p]] K, τ.symm (((ι y : Kˣ) : K)) ^ i =
        (algebraMap ℚ_[p] K (y : ℚ_[p]) ^ i) ^ d := by
      have hc1 : ∀ τ : K ≃ₐ[ℚ_[p]] K, τ.symm (((ι y : Kˣ) : K)) = algebraMap ℚ_[p] K (y : ℚ_[p]) :=
        fun τ => τ.symm.commutes _
      simp only [hc1, Finset.prod_const, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    rw [hN, hprod] at hy2
    have hmap : ((χA (y ^ d) : Kˣ) : K) = ((χA y : Kˣ) : K) ^ d := by
      rw [map_pow, Units.val_pow_eq_pow_val]
    show (((χA y : Kˣ) : K) * algebraMap ℚ_[p] K (y : ℚ_[p]) ^ i) ^ d = 1
    rw [mul_pow, ← hmap]
    exact hy2
  -- continuity of `F` in `ℚ̄_p`
  let G : ℚ_[p]ˣ → PadicAlgCl p := fun y => (((χA y : Kˣ) : K) : PadicAlgCl p) *
    algebraMap ℚ_[p] (PadicAlgCl p) (y : ℚ_[p]) ^ i
  have hFG : ∀ y, ((F y : K) : PadicAlgCl p) = G y := by
    intro y
    show K.val (((χA y : Kˣ) : K) * algebraMap ℚ_[p] K (y : ℚ_[p]) ^ i) = G y
    rw [map_mul, map_zpow₀, AlgHom.commutes]
    rfl
  have hGc : Continuous G := by
    refine Continuous.mul ?_ ?_
    · exact continuous_subtype_val.comp (Units.continuous_val.comp hχAc)
    · exact Continuous.zpow₀ ((continuous_algebraMap ℚ_[p] (PadicAlgCl p)).comp
        Units.continuous_val) i (fun y => Or.inl ((map_ne_zero _).mpr (Units.ne_zero y)))
  have hG1 : G 1 = 1 := by
    simp only [G, map_one, Units.val_one, IntermediateField.coe_one, one_zpow, mul_one]
  have hdpos : 0 < ‖((d : ℕ) : PadicAlgCl p)‖ := by
    refine norm_pos_iff.mpr (Nat.cast_ne_zero.mpr ?_)
    exact (finrank_pos_intermediateField p K).ne'
  have hnear : ∀ᶠ y in 𝓝 (1 : ℚ_[p]ˣ), ‖G y - 1‖ < ‖((d : ℕ) : PadicAlgCl p)‖ := by
    have ht := hGc.tendsto (1 : ℚ_[p]ˣ)
    rw [hG1] at ht
    have hb : Metric.ball (1 : PadicAlgCl p) ‖((d : ℕ) : PadicAlgCl p)‖ ∈ 𝓝 (1 : PadicAlgCl p) :=
      Metric.ball_mem_nhds _ hdpos
    filter_upwards [ht hb] with y hy
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  unfold ArtinNearOneOnAbelianization
  filter_upwards [hV, hnear] with y hy hyn
  have hG : G y = 1 := by
    apply eq_one_of_pow_eq_one_of_norm_sub_lt p (d := d)
    · have h1 := congrArg K.val (hFpow y hy)
      rw [map_pow, map_one] at h1
      rw [← hFG y]
      exact h1
    · exact hyn
  have hF : F y = 1 := by
    apply K.val.injective
    rw [map_one]
    exact (hFG y).trans hG
  show ((χA y : Kˣ) : K) = algebraMap ℚ_[p] K (y : ℚ_[p]) ^ (-i)
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left hF

#print axioms serreTwistAdmissible_of_pureHT
#print axioms norm_sum_le_of_forall_le'
#print axioms eq_one_of_pow_eq_one_of_norm_sub_lt
#print axioms conradNearOne_of_serre

end HDec.G0Galois.C8Conrad.SerreAppB
