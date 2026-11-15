import ZInQKernel.HDecomp.QM.Polar

/-!
# sir-printed: the Hecke twists are automorphisms of the PEL datum (algebra, compiled)

For the PEL datum `(B, 𝒪, †, L = 𝒪, E₀)` of the leaf (`x† = μ⁻¹x̄μ`, `E₀(x, y) = trd(μ⁻¹xȳ)`):

* `trd_map`: every ring automorphism `α` of `𝒪` preserves the reduced trace; `star_map`: it commutes with
  the canonical involution;
* `rosati_twist`: with `α(μ) = μv` (rv-qm-polar `twist_type`), `v⁻¹ (α b)† v = α(b†)`, i.e. the Rosati
  involution of `λ ∘ ι(v)` on `ι ∘ α` is `†` (stated as `(α b)† v = v α(b†)`);
* `E0_twist`: `E₀(α x, v · α y) = E₀(x, y)`, so `α₃ ∘ α` is a level structure (a similitude, factor 1) for
  `λ ∘ ι(v)`;
* `trd_ne_zero_of_dag`: `trd v ≠ 0` (so the sign `ε = sign trd v` making `λ ∘ ι(εv)` positive is defined);
* `E0_rightMul`: `E₀(xu, yu) = nrd(u) E₀(x, y)`, so `α₃ ∘ r_u` is a level structure for `λ`.
-/

noncomputable section

namespace SIRPrinted.TwistAlg

open RvQMPolar
open LeafQM (B ofInt InO O)

theorem quad (x : B) : x * x = (trd x : B) * x - (nrd x : B) := by
  rw [QuaternionAlgebra.coe_mul_eq_smul]
  ext <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub,
    QuaternionAlgebra.imJ_sub, QuaternionAlgebra.imK_sub, QuaternionAlgebra.re_smul,
    QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul,
    QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe, smul_eq_mul] <;> simp only [trd, nrd] <;> ring

theorem star_eq (x : B) : star x = (trd x : B) - x := by
  rw [QuaternionAlgebra.star_eq_two_re_sub, trd, zero_mul, add_zero]

theorem trd_int {x : B} (hx : x ∈ O) : ∃ t : ℤ, trd x = t := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨2 * n 0 + n 2, by simp [trd, ofInt]; ring⟩

theorem nrd_int {x : B} (hx : x ∈ O) : ∃ m : ℤ, nrd x = m := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2, by
    simp [nrd, ofInt]; ring⟩

theorem scalar_of_mem {x : B} (hx : x ∈ O) (h1 : x.imI = 0) (h2 : x.imJ = 0) (h3 : x.imK = 0) :
    ∃ m : ℤ, x = (m : B) := by
  obtain ⟨n, rfl⟩ := hx
  simp only [ofInt] at h1 h2 h3
  have e2 : (n 2 : ℚ) = 0 := by linarith
  have e3 : (n 3 : ℚ) = 0 := by linarith
  have e1 : (n 1 : ℚ) = 0 := by rw [e3] at h1; linarith
  refine ⟨n 0, ?_⟩
  ext <;> simp [ofInt, e1, e2, e3]

theorem coe_intCast (m : ℤ) : ((m : O) : B) = (m : B) := by simp

theorem intCast_smul (k : ℤ) (y : B) : (k : B) * y = (k : ℚ) • y := by
  rw [← QuaternionAlgebra.coe_intCast, QuaternionAlgebra.coe_mul_eq_smul]

/-- **Ring automorphisms of `𝒪` preserve the reduced trace.** -/
theorem trd_map (α : O ≃+* O) (x : O) : trd (α x : B) = trd (x : B) := by
  obtain ⟨t, ht⟩ := trd_int x.2
  obtain ⟨n, hn⟩ := nrd_int x.2
  obtain ⟨t', ht'⟩ := trd_int (α x).2
  obtain ⟨n', hn'⟩ := nrd_int (α x).2
  have hx : x * x = (t : O) * x - (n : O) := by
    apply Subtype.ext
    simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, coe_intCast]
    rw [quad, ht, hn, QuaternionAlgebra.coe_intCast, QuaternionAlgebra.coe_intCast]
  have hy : α x * α x = (t' : O) * α x - (n' : O) := by
    apply Subtype.ext
    simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, coe_intCast]
    rw [quad, ht', hn', QuaternionAlgebra.coe_intCast, QuaternionAlgebra.coe_intCast]
  have hαx : α x * α x = (t : O) * α x - (n : O) := by
    rw [← map_mul, hx, map_sub, map_mul, map_intCast, map_intCast]
  have hdiff : ((t' - t : ℤ) : O) * α x = ((n' - n : ℤ) : O) := by
    have := hy.symm.trans hαx
    rw [sub_eq_sub_iff_sub_eq_sub] at this
    push_cast
    rw [sub_mul]
    exact this
  rw [ht, ht']
  by_contra hne
  have hk : ((t' - t : ℤ) : ℚ) ≠ 0 := by
    push_cast
    exact sub_ne_zero.mpr hne
  have hB := congrArg (fun z : O => (z : B)) hdiff
  simp only [Subring.coe_mul, coe_intCast] at hB
  rw [intCast_smul, ← QuaternionAlgebra.coe_intCast] at hB
  have h1 := congrArg QuaternionAlgebra.imI hB
  have h2 := congrArg QuaternionAlgebra.imJ hB
  have h3 := congrArg QuaternionAlgebra.imK hB
  simp only [QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul,
    QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe, QuaternionAlgebra.imK_coe, smul_eq_mul,
    mul_eq_zero] at h1 h2 h3
  obtain ⟨m, hm⟩ := scalar_of_mem (α x).2 (h1.resolve_left hk) (h2.resolve_left hk) (h3.resolve_left hk)
  have hαm : α x = (m : O) := Subtype.ext (by rw [hm, coe_intCast])
  have hxm : x = (m : O) := by
    have := congrArg α.symm hαm
    rwa [RingEquiv.symm_apply_apply, map_intCast] at this
  apply hne
  have e1 : trd (α x : B) = 2 * m := by
    rw [hαm, coe_intCast, ← QuaternionAlgebra.coe_intCast]; simp [trd]
  have e2 : trd (x : B) = 2 * m := by
    rw [hxm, coe_intCast, ← QuaternionAlgebra.coe_intCast]; simp [trd]
  rw [← ht, ← ht', e1, e2]

theorem star_mem {x : B} (hx : x ∈ O) : star x ∈ O := by
  obtain ⟨t, ht⟩ := trd_int hx
  rw [star_eq, ht]
  exact O.sub_mem (intCast_mem O t) hx

/-- **Ring automorphisms of `𝒪` commute with the canonical involution.** -/
theorem star_map (α : O ≃+* O) (x : O) :
    star (α x : B) = (α ⟨star (x : B), star_mem x.2⟩ : B) := by
  obtain ⟨t, ht⟩ := trd_int x.2
  have hs : (⟨star (x : B), star_mem x.2⟩ : O) = (t : O) - x :=
    Subtype.ext (by
      simp only [AddSubgroupClass.coe_sub, coe_intCast]; rw [star_eq, ht, QuaternionAlgebra.coe_intCast])
  rw [hs, map_sub, map_intCast, AddSubgroupClass.coe_sub, coe_intCast, star_eq, trd_map, ht,
    QuaternionAlgebra.coe_intCast]

/-- `6 x† = −μ x̄ μ`. -/
theorem six_eq : (6 : B) = ((6 : ℚ) : B) := by
  ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat]

theorem six_dag (x : B) : (6 : B) * dag x = -(mu * star x * mu) := by
  rw [six_eq, QuaternionAlgebra.coe_mul_eq_smul]
  simp only [dag, muInv, mu]; ext <;> simp <;> ring

theorem muInv_eq_smul : muInv = (-1/6 : ℚ) • mu := by
  ext <;> simp [muInv, mu] <;> norm_num

theorem sixth_mul_six : ((1/6 : ℚ) : B) * (6 : B) = 1 := by
  ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat]

theorem six_comm (z : B) : (6 : B) * z = z * 6 := (Nat.cast_commute 6 z)

/-- `α(μ)² = −6` gives `v μ v = μ` when `α(μ) = μ v`. -/
theorem v_mu_v (α : O ≃+* O) (v : B) (hαμ : ((α ⟨mu, mu_mem⟩ : O) : B) = mu * v) :
    v * mu * v = mu := by
  have hm6 : ((-6 : O) : B) = -6 := by push_cast; rfl
  have h1 : (⟨mu, mu_mem⟩ : O) * ⟨mu, mu_mem⟩ = -6 := by
    apply Subtype.ext; rw [Subring.coe_mul, hm6]; exact mu_mul_mu
  have h2 : α ((⟨mu, mu_mem⟩ : O) * ⟨mu, mu_mem⟩) = -6 := by rw [h1, map_neg, map_ofNat]
  rw [map_mul] at h2
  have h3 := congrArg (fun z : O => (z : B)) h2
  simp only [Subring.coe_mul, hαμ, hm6] at h3
  have h4 : mu * (v * mu * v) = mu * mu := by
    rw [mu_mul_mu, ← h3]; noncomm_ring
  have := congrArg (fun z => muInv * z) h4
  simpa only [← mul_assoc, muInv_mul_mu, one_mul] using this

/-- **The Rosati involution of `λ ∘ ι(v)` on `ι ∘ α` is `†`**: `(α b)† v = v α(b†)`, i.e.
`v⁻¹ (α b)† v = α(b†)`. -/
theorem rosati_twist (α : O ≃+* O) (v : B) (hαμ : ((α ⟨mu, mu_mem⟩ : O) : B) = mu * v) (b : O) :
    dag (α b : B) * v = v * (α ⟨dag (b : B), dag_mem b.2⟩ : B) := by
  have hvmv := v_mu_v α v hαμ
  have h6 : (6 : O) * ⟨dag (b : B), dag_mem b.2⟩ =
      -((⟨mu, mu_mem⟩ : O) * ⟨star (b : B), star_mem b.2⟩ * ⟨mu, mu_mem⟩) := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_neg]
    rw [show ((6 : O) : B) = 6 by push_cast; rfl, six_dag]
  have h6' := congrArg (fun z : O => (z : B)) (congrArg α h6)
  simp only [map_mul, map_neg, map_ofNat, Subring.coe_mul, Subring.coe_neg, hαμ] at h6'
  rw [← star_map] at h6'
  have h6'' : ((6 : O) : B) = 6 := by push_cast; rfl
  rw [h6''] at h6'
  suffices h : (6 : B) * (dag (α b : B) * v) = (6 : B) * (v * (α ⟨dag (b : B), dag_mem b.2⟩ : B)) by
    have := congrArg (fun z => ((1/6 : ℚ) : B) * z) h
    simpa only [← mul_assoc, sixth_mul_six, one_mul] using this
  rw [← mul_assoc, six_dag, ← mul_assoc, six_comm v, mul_assoc v 6, h6']
  have key : ∀ Z : B, v * (mu * (v * Z)) = mu * Z := fun Z => by
    rw [← mul_assoc, ← mul_assoc, hvmv]
  simp only [mul_assoc, neg_mul, mul_neg, key]

/-- **`α₃ ∘ α` is a level structure for `λ ∘ ι(v)`**: `E₀(α x, v · α y) = E₀(x, y)`. -/
theorem E0_twist (α : O ≃+* O) (v : B) (hαμ : ((α ⟨mu, mu_mem⟩ : O) : B) = mu * v) (x y : O) :
    E0 (α x : B) (v * (α y : B)) = E0 (x : B) (y : B) := by
  -- `v̄ = μ v μ⁻¹`
  have hsv : star v = mu * v * muInv := by
    have hm : star (mu * v) = -(mu * v) := by
      rw [← hαμ, star_map]
      have : (⟨star mu, star_mem mu_mem⟩ : O) = -⟨mu, mu_mem⟩ :=
        Subtype.ext (by simp only [Subring.coe_neg]; simp only [mu]; ext <;> simp)
      rw [this, map_neg, Subring.coe_neg]
    rw [star_mul] at hm
    have hsmu : star mu = -mu := by simp only [mu]; ext <;> simp
    rw [hsmu, mul_neg, neg_inj] at hm
    have := congrArg (fun z => z * muInv) hm
    simpa only [mul_assoc, mu_mul_muInv, mul_one] using this
  have hcomm : ∀ a b : B, trd (a * b) = trd (b * a) := trd_mul_comm
  unfold E0
  rw [star_mul, hsv]
  have e1 : muInv * (α x : B) * (star (α y : B) * (mu * v * muInv)) =
      (muInv * (α x : B) * star (α y : B) * (mu * v)) * muInv := by noncomm_ring
  rw [e1, hcomm, ← hαμ, star_map, muInv_eq_smul]
  have e2 : ∀ a b c : B, (-1/6 : ℚ) • mu * ((-1/6 : ℚ) • mu * a * b * c) =
      ((-1/6 : ℚ) * (-1/6 : ℚ)) • ((mu * mu) * (a * b * c)) := fun a b c => by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  rw [e2, mu_mul_mu, ← Subring.coe_mul, ← Subring.coe_mul, ← map_mul, ← map_mul]
  rw [show (-6 : B) * ((α (x * ⟨star (y : B), star_mem y.2⟩ * ⟨mu, mu_mem⟩) : O) : B) =
      (-6 : ℚ) • ((α (x * ⟨star (y : B), star_mem y.2⟩ * ⟨mu, mu_mem⟩) : O) : B) by
    rw [← QuaternionAlgebra.coe_mul_eq_smul]; push_cast; rfl]
  rw [smul_smul, trd_smul, trd_map]
  simp only [Subring.coe_mul]
  rw [smul_mul_assoc, smul_mul_assoc, trd_smul, mul_assoc mu, hcomm mu]
  ring

/-- `trd v ≠ 0` for `v† = v` with `nrd v = 1` (so `ε = sign trd v` is defined). -/
theorem trd_ne_zero_of_dag (v : B) (hn : nrd v = 1) (hd : dag v = v) : trd v ≠ 0 := by
  intro h
  have hq := quad v
  rw [h, hn] at hq
  have hv : v ≠ 0 := by
    rintro rfl
    simp [nrd] at hn
  have hpos := trd_mul_dag_pos hv
  rw [hd, hq] at hpos
  simp [trd] at hpos
  norm_num at hpos

/-- **`α₃ ∘ r_u` is a level structure for `λ`**: `E₀(xu, yu) = nrd(u) E₀(x, y)`. -/
theorem E0_rightMul (x y u : B) : E0 (x * u) (y * u) = nrd u * E0 x y := by
  unfold E0
  rw [star_mul, show muInv * (x * u) * (star u * star y) = muInv * x * (u * star u) * star y by
    noncomm_ring, mul_star_eq_nrd]
  rw [show (⟨nrd u, 0, 0, 0⟩ : B) = (nrd u : B) from rfl, QuaternionAlgebra.mul_coe_eq_smul,
    smul_mul_assoc, trd_smul]

end SIRPrinted.TwistAlg

#print axioms SIRPrinted.TwistAlg.trd_map
#print axioms SIRPrinted.TwistAlg.rosati_twist
#print axioms SIRPrinted.TwistAlg.E0_twist
#print axioms SIRPrinted.TwistAlg.trd_ne_zero_of_dag
#print axioms SIRPrinted.TwistAlg.E0_rightMul
