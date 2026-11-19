import ZInQKernel.Contrib.OneProof.ShimuraOrbitsAction

/-! Coprime multiplication with the full multiplicity of the triangular sums. -/

noncomputable section

namespace ShimuraSteps.Orbits
open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

theorem diamond_term {N : ℕ} (g h : Gamma0 N) (a b d : ℕ) (τ : ℍ) :
    diamond g (term h a b d τ) = term (g * h) a b d τ := by
  simp [term, mul_smul]

/-- Move the inner lift through the outer sum, using covariance before multiplying triangles. -/
theorem R_term {N : ℕ} (m : ℕ) (g : Gamma0 N) {c f : ℕ}
    (hc : 0 < c) (hf : 0 < f) (e : ℕ) (τ : ℍ) :
    R N m (term g c e f τ) =
      ∑ a : Div N m, ∑ b : Fin (m / a.val),
        term (g * repLift a) (a.val * c) (a.val * e + b.val * f) ((m / a.val) * f) τ := by
  rw [term, R_point, sumAt_covariant, sumAt_lifts repLift (by simp [repLift]), map_sum]
  simp only [map_sum, diamond_term]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [term, triAct_comp (div_spec a).1 hc (div_spec a).2.1 hf]

private def divOf {N n : ℕ} (hn : 0 < n) {a : ℕ} (ha : a ∣ n) (hN : a.Coprime N) : Div N n :=
  ⟨a, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨ha, hn.ne'⟩, hN⟩⟩

/-- An eligible divisor of a coprime product has a unique eligible factor in each index. -/
private def divMul {N m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) :
    Div N m × Div N n ≃ Div N (m * n) where
  toFun ac := divOf (Nat.mul_pos hm hn) (Nat.mul_dvd_mul
    (Nat.mem_divisors.mp (Finset.mem_filter.mp ac.1.property).1).1
    (Nat.mem_divisors.mp (Finset.mem_filter.mp ac.2.property).1).1)
    ((div_spec ac.1).2.2.2.mul_left (div_spec ac.2).2.2.2)
  invFun a := (divOf hm (Nat.gcd_dvd_right _ _) ((div_spec a).2.2.2.coprime_dvd_left (Nat.gcd_dvd_left _ _)),
    divOf hn (Nat.gcd_dvd_right _ _) ((div_spec a).2.2.2.coprime_dvd_left (Nat.gcd_dvd_left _ _)))
  left_inv := by
    rintro ⟨a, c⟩
    have ha := (Nat.mem_divisors.mp (Finset.mem_filter.mp a.property).1).1
    have hc := (Nat.mem_divisors.mp (Finset.mem_filter.mp c.property).1).1
    apply Prod.ext <;> apply Subtype.ext
    · change (a.val * c.val).gcd m = a.val
      rw [(h.symm.coprime_dvd_left hc).gcd_mul_right_cancel, Nat.gcd_eq_left ha]
    · change (a.val * c.val).gcd n = c.val
      rw [(h.coprime_dvd_left ha).gcd_mul_left_cancel, Nat.gcd_eq_left hc]
  right_inv := by
    intro a
    apply Subtype.ext
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2
      (Nat.mem_divisors.mp (Finset.mem_filter.mp a.property).1).1

/-- The offset of a product, reduced modulo the product of its denominators. -/
private def offsetMul {a d f : ℕ} (hd : 0 < d) (hf : 0 < f) (h : a.Coprime f) :
    Fin d × Fin f ≃ Fin (d * f) := by
  let F : Fin d × Fin f → Fin (d * f) :=
    fun be => ⟨(a * be.2.val + be.1.val * f) % (d * f), Nat.mod_lt _ (Nat.mul_pos hd hf)⟩
  refine Equiv.ofBijective F ((Fintype.bijective_iff_injective_and_card F).2 ⟨?_, by simp⟩)
  rintro ⟨b, e⟩ ⟨b', e'⟩ he
  have hm : a * e.val + b.val * f ≡ a * e'.val + b'.val * f [MOD d * f] := congrArg Fin.val he
  have hf' := hm.of_mul_left d
  have hmer : a * e.val ≡ a * e'.val [MOD f] := by
    simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using hf'
  have hee := Nat.ModEq.cancel_left_of_coprime h.symm.gcd_eq_one hmer
  have heq : e = e' := Fin.ext (by simpa [Nat.ModEq, Nat.mod_eq_of_lt e.isLt, Nat.mod_eq_of_lt e'.isLt] using hee)
  subst e'
  have hm' : b.val * f ≡ b'.val * f [MOD d * f] := hm.add_left_cancel' (a * e.val)
  have hbb := Nat.ModEq.mul_right_cancel' hf.ne' hm'
  exact Prod.ext (Fin.ext (by simpa [Nat.ModEq, Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt b'.isLt] using hbb)) rfl

theorem coprime_count_basis {N m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) (τ : ℍ) :
    R N m (R N n (point (orb N τ))) = R N (m * n) (point (orb N τ)) := by
  classical
  simp only [R_point]
  rw [sumAt_lifts (N := N) (n := n) repLift (by simp [repLift]),
    sumAt_lifts (N := N) (n := m * n) repLift (by simp [repLift]), map_sum]
  simp only [map_sum, R_term m (repLift _) (div_spec _).1 (div_spec _).2.1]
  conv_lhs =>
    arg 2
    ext c
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  let F (ac : Div N m × Div N n) : Divisors N :=
    ∑ e : Fin (n / ac.2.val), ∑ b : Fin (m / ac.1.val),
      term (repLift ac.2 * repLift ac.1) (ac.1.val * ac.2.val)
        (ac.1.val * e.val + b.val * (n / ac.2.val)) ((m / ac.1.val) * (n / ac.2.val)) τ
  change (∑ a : Div N m, ∑ c : Div N n, F (a, c)) = _
  rw [← Fintype.sum_prod_type F]
  refine Fintype.sum_equiv (divMul hm hn hmn) _ _ ?_
  rintro ⟨a, c⟩
  let d := m / a.val
  let f := n / c.val
  let A := divMul (N := N) hm hn hmn (a, c)
  have ha : A.val = a.val * c.val := rfl
  have hd : 0 < d := (div_spec a).2.1
  have hf : 0 < f := (div_spec c).2.1
  have hac : (m * n) / A.val = d * f := by
    apply Nat.eq_of_mul_eq_mul_left (div_spec A).1
    rw [(div_spec A).2.2.1, ha]
    calc m * n = (a.val * d) * (c.val * f) := by rw [(div_spec a).2.2.1, (div_spec c).2.2.1]
      _ = (a.val * c.val) * (d * f) := by ac_rfl
  have hv : a.val.Coprime f := (hmn.coprime_dvd_left
    (Nat.mem_divisors.mp (Finset.mem_filter.mp a.property).1).1).coprime_dvd_right
    ⟨c.val, by rw [mul_comm, (div_spec c).2.2.1]⟩
  change (∑ e : Fin f, ∑ b : Fin d,
      term (repLift c * repLift a) (a.val * c.val) (a.val * e.val + b.val * f) (d * f) τ) =
    ∑ j : Fin ((m * n) / A.val), term (repLift A) A.val j.val ((m * n) / A.val) τ
  let H (be : Fin d × Fin f) :=
    term (repLift c * repLift a) (a.val * c.val)
      (a.val * be.2.val + be.1.val * f) (d * f) τ
  change (∑ e : Fin f, ∑ b : Fin d, H (b, e)) = _
  rw [← Fintype.sum_prod_type_right H]
  refine Fintype.sum_equiv ((offsetMul hd hf hv).trans (finCongr hac.symm)) _ _ ?_
  rintro ⟨b, e⟩
  have hres : Gamma0Map N (repLift c * repLift a) = Gamma0Map N (repLift A) := by
    simp [repLift, ha, mul_comm]
  simp only [H, Equiv.trans_apply, finCongr_apply_coe]
  rw [term_residue hres, hac, ha]
  exact congrArg point (orb_triAct_mod (Nat.mul_pos (div_spec a).1 (div_spec c).1)
    (Nat.mul_pos hd hf) (repLift A) _ τ)

#print axioms diamond_term
#print axioms R_term
#print axioms coprime_count_basis

end ShimuraSteps.Orbits
