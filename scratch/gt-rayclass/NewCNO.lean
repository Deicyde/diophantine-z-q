/-! # gt-rayclass: Eichler's class number one in adelic form, proved

`ClassNumberOneB` (rayclass-cft's leaf) from the chain's `HDec.QMSplit.CNO.principal_of_lattice` (the
norm-Euclidean computation that proves `qmClassNumberOne_proof`): for `g ∈ (B ⊗ 𝔸_f)^×` the left ideal
`I = {x ∈ B : x g ∈ 𝒪̂}` is `𝒪α`, and then `u = α g ∈ 𝒪̂^×`, `g = α⁻¹ u`. The adelic inputs:
* `exists_den`: every finite adele has a denominator `d ∈ ℕ`, `d a ∈ ℤ̂`;
* `exists_int_approx`: `a ∈ ℤ̂`, `N ≥ 1` ⇒ `a = m + N b` with `m ∈ ℤ`, `b ∈ ℤ̂` (`ℤ̂ → ℤ/N` onto; Mathlib's
  `PadicInt.appr` at the primes dividing `N` and the Chinese remainder theorem). -/

noncomputable section

namespace RayClassCFT

open LeafQM NumberField IsDedekindDomain HeightOneSpectrum Rat.HeightOneSpectrum
open ShimuraCFT

/-! ## Adelic bookkeeping -/

theorem mem_ZhatQ {a : AQ} : a ∈ ZhatQ ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

/-- Evaluation of a finite adele at a place, as a ring hom. -/
def evQ (v : HeightOneSpectrum (𝓞 ℚ)) : AQ →+* v.adicCompletion ℚ where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evQ_apply (v : HeightOneSpectrum (𝓞 ℚ)) (a : AQ) : evQ v a = a v := rfl

section Den

/- As in the chain's `TailZ12`: prefer Mathlib's `instAlgebraAdicCompletion` (the instance in the statement of
`mul_nonZeroDivisor_mem_adicCompletionIntegers`). -/
attribute [local instance 2000] instAlgebraAdicCompletion

open scoped algebraMap in
/-- **Denominators**: every finite adele `a` has `d ≥ 1` with `d a ∈ ℤ̂`. -/
theorem exists_den (a : AQ) : ∃ d : ℕ, 0 < d ∧ (d : AQ) * a ∈ ZhatQ := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | ¬ a v ∈ v.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.1 (FiniteAdeleRing.cofinite_mem_adicCompletionIntegers a)
  choose b hb hab using fun v : HeightOneSpectrum (𝓞 ℚ) =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  set S := hfin.toFinset
  set D : 𝓞 ℚ := ∏ v ∈ S, b v with hDdef
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 (fun v _ => nonZeroDivisors.ne_zero (hb v))
  have hprod : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
      algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) (∏ v ∈ T, b v) ∈ w.adicCompletionIntegers ℚ := by
    intro w T
    rw [map_prod]
    exact prod_mem (fun v _ => coe_mem_adicCompletionIntegers w (b v))
  have hint : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      a w * algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) D ∈ w.adicCompletionIntegers ℚ := by
    intro w
    by_cases hw : w ∈ S
    · rw [hDdef, ← Finset.mul_prod_erase S b hw, map_mul, ← mul_assoc]
      exact mul_mem (hab w) (hprod w _)
    · have : a w ∈ w.adicCompletionIntegers ℚ := by
        by_contra hc
        exact hw (hfin.mem_toFinset.2 hc)
      exact mul_mem this (hprod w S)
  set n : ℤ := Rat.ringOfIntegersEquiv D
  have hDn : D = (n : 𝓞 ℚ) := by
    rw [show (n : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n from (eq_intCast _ n).symm]
    exact (Rat.ringOfIntegersEquiv.symm_apply_apply D).symm
  have hn0 : n ≠ 0 := by
    intro h0; apply hD0; rw [hDn, h0, Int.cast_zero]
  refine ⟨n.natAbs, Int.natAbs_pos.2 hn0, mem_ZhatQ.2 fun w => ?_⟩
  have h := hint w
  rw [hDn, map_intCast] at h
  change evQ w ((n.natAbs : AQ) * a) ∈ _
  rw [map_mul, map_natCast, evQ_apply, mul_comm]
  rcases Int.natAbs_eq n with h' | h'
  · rw [h'] at h; simpa using h
  · rw [h'] at h
    have := neg_mem h
    simpa using this

end Den

/-- In `ℤ_[q]`: if `q^{v_q(N)}` divides `m − appr(y)`, then `N` divides `y − m`. -/
theorem padic_div {q : ℕ} [Fact q.Prime] (y : ℤ_[q]) (m : ℤ) {N : ℕ} (hN : N ≠ 0)
    (h : (q : ℤ) ^ (N.factorization q) ∣ m - (y.appr (N.factorization q) : ℤ)) :
    ∃ c : ℤ_[q], y - m = N * c := by
  set k := N.factorization q
  obtain ⟨c1, hc1⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k y)
  obtain ⟨c2, hc2⟩ := h
  have hc2' : (m : ℤ_[q]) - ((y.appr k : ℕ) : ℤ_[q]) = (q : ℤ_[q]) ^ k * (c2 : ℤ_[q]) := by
    have := congrArg (Int.cast : ℤ → ℤ_[q]) hc2
    push_cast at this
    exact this
  have hcop : q.Coprime (N / q ^ k) := by
    rw [Nat.Prime.coprime_iff_not_dvd (Fact.out)]
    exact Nat.not_dvd_ordCompl (Fact.out) hN
  have hu : IsUnit ((N / q ^ k : ℕ) : ℤ_[q]) :=
    PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hcop)
  obtain ⟨u, hu⟩ := hu
  have hNf : (N : ℤ_[q]) = (q : ℤ_[q]) ^ k * ((N / q ^ k : ℕ) : ℤ_[q]) := by
    have := Nat.ordProj_mul_ordCompl_eq_self N q
    exact_mod_cast this.symm
  refine ⟨(↑u⁻¹ : ℤ_[q]) * (c1 - c2), ?_⟩
  rw [hNf, ← hu]
  have e : y - m = (q : ℤ_[q]) ^ k * (c1 - c2) := by linear_combination hc1.symm - hc2'
  rw [e]
  calc (q : ℤ_[q]) ^ k * (c1 - c2) = (q : ℤ_[q]) ^ k * ((u : ℤ_[q]) * ↑u⁻¹ * (c1 - c2)) := by
        rw [Units.mul_inv, one_mul]
    _ = (q : ℤ_[q]) ^ k * (u : ℤ_[q]) * (↑u⁻¹ * (c1 - c2)) := by ring

/-- **Approximation**: `a ∈ ℤ̂`, `N ≥ 1` ⇒ `a = m + N b` with `m ∈ ℤ`, `b ∈ ℤ̂`. -/
theorem exists_int_approx {a : AQ} (ha : a ∈ ZhatQ) (N : ℕ) (hN : 0 < N) :
    ∃ m : ℤ, ∃ b ∈ ZhatQ, a = (m : AQ) + (N : AQ) * b := by
  classical
  let loc : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v] :=
    fun v => (adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v :
      v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v])
  let x : ∀ v : HeightOneSpectrum (𝓞 ℚ), ℤ_[primesEquiv v] := fun v => loc v ⟨a v, ha v⟩
  let r : HeightOneSpectrum (𝓞 ℚ) → ℤ := fun v =>
    ((x v).appr (N.factorization (primesEquiv v : ℕ)) : ℤ)
  let vOf : N.primeFactors → HeightOneSpectrum (𝓞 ℚ) := fun p =>
    (primesEquiv (R := 𝓞 ℚ)).symm ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩
  let I : N.primeFactors → Ideal ℤ := fun p => Ideal.span {((p.1 : ℕ) : ℤ) ^ N.factorization p.1}
  have hI : Pairwise (Function.onFun IsCoprime I) := by
    intro p p' hpp'
    simp only [Function.onFun, I]
    rw [Ideal.isCoprime_span_singleton_iff, Int.isCoprime_iff_gcd_eq_one]
    have hp := Nat.prime_of_mem_primeFactors p.2
    have hp' := Nat.prime_of_mem_primeFactors p'.2
    have hne : p.1 ≠ p'.1 := fun h => hpp' (Subtype.ext h)
    have hc : Nat.Coprime (p.1 ^ N.factorization p.1) (p'.1 ^ N.factorization p'.1) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hp').2 hne)
    rw [← Nat.cast_pow, ← Nat.cast_pow, Int.gcd_natCast_natCast]
    exact hc
  obtain ⟨m, hm⟩ := Ideal.exists_forall_sub_mem_ideal hI (fun p => r (vOf p))
  -- local divisibility at every place
  have hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ c : ℤ_[primesEquiv v], x v - m = N * c := by
    intro v
    apply padic_div (x v) m hN.ne'
    by_cases hd : (primesEquiv v : ℕ) ∣ N
    · have hmem : (primesEquiv v : ℕ) ∈ N.primeFactors :=
        Nat.mem_primeFactors.2 ⟨(primesEquiv v).2, hd, hN.ne'⟩
      have hv : vOf ⟨_, hmem⟩ = v := (primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v
      have := hm ⟨_, hmem⟩
      rw [hv] at this
      exact Ideal.mem_span_singleton.1 this
    · rw [Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
      exact one_dvd _
  -- the adele `b`
  set cinv : AQ := algebraMap ℚ AQ ((N : ℚ)⁻¹) with hcinv
  have hNc : (N : AQ) * cinv = 1 := by
    rw [hcinv, ← map_natCast (algebraMap ℚ AQ) N, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hN.ne'),
      map_one]
  refine ⟨m, (a - m) * cinv, mem_ZhatQ.2 fun v => ?_, by linear_combination (-(a - (m : AQ))) * hNc⟩
  obtain ⟨c, hc⟩ := hloc v
  have e1 : (⟨a v, ha v⟩ : v.adicCompletionIntegers ℚ) - (m : v.adicCompletionIntegers ℚ) =
      (N : v.adicCompletionIntegers ℚ) * (loc v).symm c := by
    apply (loc v).injective
    rw [map_sub, map_intCast, map_mul, map_natCast, RingEquiv.apply_symm_apply]
    exact hc
  have e2 := congrArg (v.adicCompletionIntegers ℚ).subtype e1
  simp only [map_sub, map_mul, map_intCast, map_natCast] at e2
  have hNv := congrArg (evQ v) hNc
  rw [map_mul, map_natCast, map_one] at hNv
  change evQ v ((a - m) * cinv) ∈ _
  rw [map_mul, map_sub, map_intCast, evQ_apply]
  have e3 : (a v - (m : v.adicCompletion ℚ)) * evQ v cinv = ((loc v).symm c : v.adicCompletion ℚ) := by
    have e2' : a v - (m : v.adicCompletion ℚ) = (N : v.adicCompletion ℚ) * ((loc v).symm c : v.adicCompletion ℚ) :=
      e2
    rw [e2', mul_comm, ← mul_assoc, mul_comm (evQ v cinv), hNv, one_mul]
  rw [e3]
  exact ((loc v).symm c).2

/-! ## Lemmas on `B ⊗ 𝔸_f` -/

theorem OhatQ_neg {x : BAQ} (hx : x ∈ OhatQ) : -x ∈ OhatQ := by
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨-n, fun i => ZhatS.neg_mem (hn i), ShimuraGlue.ofQ_neg n⟩

theorem OhatQ_of_cQ {x : BAQ} (h : ∀ i, cQ x i ∈ ZhatQ) : x ∈ OhatQ :=
  ⟨cQ x, h, ShimuraGlue.ofQ_coords x⟩

theorem cQ_natCast_mul (d : ℕ) (x : BAQ) : cQ ((d : BAQ) * x) = fun i => (d : AQ) * cQ x i := by
  funext i
  fin_cases i <;> simp [cQ] <;> ring

theorem natCast_mul_ofQ (d : ℕ) (n : Fin 4 → AQ) :
    (d : BAQ) * ShimuraGlue.ofQ n = ShimuraGlue.ofQ (fun i => (d : AQ) * n i) := by
  ext <;> simp [ShimuraGlue.ofQ] <;> ring

/-- Every `x ∈ B ⊗ 𝔸_f` has `D ≥ 1` with `D x ∈ 𝒪̂`. -/
theorem exists_den_B (x : BAQ) : ∃ D : ℕ, 0 < D ∧ (D : BAQ) * x ∈ OhatQ := by
  classical
  choose d hd hdx using fun i => exists_den (cQ x i)
  refine ⟨∏ i, d i, Finset.prod_pos (fun i _ => hd i), OhatQ_of_cQ fun i => ?_⟩
  rw [cQ_natCast_mul]
  show ((∏ j, d j : ℕ) : AQ) * cQ x i ∈ ZhatQ
  rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i), Nat.cast_mul, mul_comm (d i : AQ),
    mul_assoc]
  exact ZhatS.mul_mem (natCast_mem ZhatS _) (hdx i)

theorem bEmb_ofInt (m : Fin 4 → ℤ) : bEmb (LeafQM.ofInt m) = ShimuraGlue.ofQ (fun i => ((m i : ℤ) : AQ)) := by
  have h1 := ShimuraGlue.ofQ_coords (bEmb (LeafQM.ofInt m))
  have h2 := cQ_bEmb (LeafQM.ofInt m)
  rw [cQ_ofInt] at h2
  conv_lhs => rw [h1]
  congr 1
  rw [show (![(bEmb (LeafQM.ofInt m)).re - (bEmb (LeafQM.ofInt m)).imJ,
      (bEmb (LeafQM.ofInt m)).imI - (bEmb (LeafQM.ofInt m)).imK,
      2 * (bEmb (LeafQM.ofInt m)).imJ, 2 * (bEmb (LeafQM.ofInt m)).imK] : Fin 4 → AQ) =
      cQ (bEmb (LeafQM.ofInt m)) from rfl, h2]
  funext i
  simp

theorem bEmb_natSmul (D : ℕ) (x : LeafQM.B) : bEmb ((D : ℚ) • x) = (D : BAQ) * bEmb x := by
  rw [map_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem inO_natSmul (D : ℕ) {x : LeafQM.B} (hx : InO x) : InO ((D : ℚ) • x) := by
  rw [Nat.cast_smul_eq_nsmul]
  exact (LeafQM.O.nsmul_mem (show x ∈ LeafQM.O from hx) D : _)

theorem nrd_natCast (D : ℕ) : ShimuraGlue.nrdQ ℚ ((D : ℕ) : LeafQM.B) = (D : ℚ) ^ 2 := by
  simp [ShimuraGlue.nrdQ_apply]

theorem nrd_smul (r : ℚ) (x : LeafQM.B) : ShimuraGlue.nrdQ ℚ (r • x) = r ^ 2 * ShimuraGlue.nrdQ ℚ x := by
  simp [ShimuraGlue.nrdQ_apply]; ring

theorem star_smul_B (r : ℚ) (x : LeafQM.B) : star (r • x) = r • star x := by
  ext <;> simp <;> ring

/-! ## Class number one -/

/-- **`ClassNumberOneB` proved** (Eichler's class number one for `𝒪`, adelic form), from the chain's
norm-Euclidean `HDec.QMSplit.CNO.principal_of_lattice`. -/
theorem classNumberOneB_proof : ClassNumberOneB := by
  intro g
  set h : BAQ := ((g⁻¹ : BAQˣ) : BAQ) with hh
  have hgh : (g : BAQ) * h = 1 := by simp [h]
  have hhg : h * (g : BAQ) = 1 := by simp [h]
  obtain ⟨D, hD, hDg, hDh⟩ : ∃ D : ℕ, 0 < D ∧ (D : BAQ) * g ∈ OhatQ ∧ (D : BAQ) * h ∈ OhatQ := by
    obtain ⟨D1, h1, e1⟩ := exists_den_B (g : BAQ)
    obtain ⟨D2, h2, e2⟩ := exists_den_B h
    refine ⟨D1 * D2, Nat.mul_pos h1 h2, ?_, ?_⟩
    · rw [show ((D1 * D2 : ℕ) : BAQ) = (D2 : BAQ) * D1 by rw [mul_comm D1 D2, Nat.cast_mul], mul_assoc]
      exact OhatQ_mul (OhatQ_natCast D2) e1
    · rw [Nat.cast_mul, mul_assoc]
      exact OhatQ_mul (OhatQ_natCast D1) e2
  -- the left ideal `I = B ∩ 𝒪̂ g⁻¹`
  let I : AddSubgroup LeafQM.B :=
    { carrier := {x | bEmb x * g ∈ OhatQ}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add, add_mul] at *
        exact OhatQ_add hx hy
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, zero_mul]
        exact OhatQ_zero
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, map_neg, neg_mul] at *
        exact OhatQ_neg hx }
  have hmemI : ∀ x, x ∈ I ↔ bEmb x * g ∈ OhatQ := fun x => Iff.rfl
  have hI : ∀ q ∈ LeafQM.O, ∀ x ∈ I, q * x ∈ I := by
    intro q hq x hx
    rw [hmemI, map_mul, mul_assoc]
    exact OhatQ_mul (bEmb_mem_of_inO hq) hx
  have hdI : ∀ x ∈ I, ((D : ℕ) : ℚ) • x ∈ LeafQM.O := by
    intro x hx
    apply inO_of_bEmb_mem
    rw [bEmb_natSmul]
    have e : (D : BAQ) * bEmb x = (bEmb x * g) * ((D : BAQ) * h) := by
      calc (D : BAQ) * bEmb x = (D : BAQ) * bEmb x * (g * h) := by rw [hgh, mul_one]
        _ = ((D : BAQ) * (bEmb x * g)) * h := by simp only [mul_assoc]
        _ = ((bEmb x * g) * (D : BAQ)) * h := by rw [Nat.cast_comm]
        _ = (bEmb x * g) * ((D : BAQ) * h) := by simp only [mul_assoc]
    rw [e]
    exact OhatQ_mul hx hDh
  obtain ⟨α, hαI, hαgen⟩ := HDec.QMSplit.CNO.principal_of_lattice I hI D hD hdI
  -- `D ∈ I`, so `α ≠ 0`
  have hDI : ((D : ℕ) : LeafQM.B) ∈ I := by
    rw [hmemI, map_natCast]
    exact hDg
  obtain ⟨q0, -, hq0⟩ := hαgen _ hDI
  have hnα : ShimuraGlue.nrdQ ℚ α ≠ 0 := by
    intro h0
    have h1 := congrArg (ShimuraGlue.nrdQ ℚ) hq0
    rw [map_mul, h0, mul_zero, nrd_natCast] at h1
    have : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    exact this ((pow_eq_zero_iff two_ne_zero).1 h1)
  -- an integer multiple of `α⁻¹` in `𝒪`
  have hDα : InO ((D : ℚ) • α) := hdI α hαI
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ShimuraGlue.nrdQ ℚ ((D : ℚ) • α) = M := by
    have := nrd_mem_of_mem (bEmb_mem_of_inO hDα)
    rw [nrd_bEmb] at this
    exact (rat_mem_zhat_iff _).1 this
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, nrd_smul] at hM
    have : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    exact hnα ((mul_eq_zero.1 hM).resolve_left (pow_ne_zero 2 this))
  have hMinv : InO ((M : ℚ) • binv α) := by
    have e : (M : ℚ) • binv α = (D : ℚ) • star ((D : ℚ) • α) := by
      rw [← hM, nrd_smul, binv, smul_smul, star_smul_B, smul_smul]
      congr 1
      field_simp
    rw [e]
    exact inO_natSmul D (inO_star hDα)
  set c : ℕ := M.natAbs with hcdef
  have hc : 0 < c := Int.natAbs_pos.2 hM0
  have hcO : InO ((c : ℚ) • binv α) := by
    rcases le_or_gt 0 M with hM' | hM'
    · have e : ((c : ℕ) : ℚ) = (M : ℚ) := by
        rw [hcdef, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hM' : (0 : ℚ) ≤ M)]
      rw [e]; exact hMinv
    · have e : ((c : ℕ) : ℚ) = -(M : ℚ) := by
        rw [hcdef, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hM' : (M : ℚ) < 0)]
      rw [e, neg_smul]
      exact LeafQM.O.neg_mem (show _ ∈ LeafQM.O from hMinv)
  -- approximation of `D g⁻¹` modulo `N = D² c`
  set N : ℕ := D * D * c with hNdef
  have hN : 0 < N := by positivity
  obtain ⟨nD, hnD, hDh'⟩ := hDh
  choose m b hb hmb using fun i => exists_int_approx (hnD i) N hN
  set w : BAQ := ShimuraGlue.ofQ b with hwdef
  have hw : w ∈ OhatQ := ⟨b, hb, rfl⟩
  have hsplit : (D : BAQ) * h = bEmb (LeafQM.ofInt m) + (N : BAQ) * w := by
    rw [hDh', hwdef, natCast_mul_ofQ, bEmb_ofInt, ShimuraGlue.ofQ_add]
    congr 1
    funext i
    exact hmb i
  set x0 : LeafQM.B := ((D : ℚ)⁻¹) • LeafQM.ofInt m with hx0def
  have hDu : IsUnit ((D : ℕ) : BAQ) := by
    rw [← map_natCast (algebraMap ℚ BAQ) D]
    exact (IsUnit.mk0 _ (by exact_mod_cast hD.ne' : (D : ℚ) ≠ 0)).map _
  have hx0 : bEmb x0 = h - ((D * c : ℕ) : BAQ) * w := by
    apply hDu.mul_left_cancel
    rw [← bEmb_natSmul, hx0def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hD.ne' : (D : ℚ) ≠ 0),
      one_smul, mul_sub, ← mul_assoc, ← Nat.cast_mul, ← mul_assoc D D c, ← hNdef, hsplit]
    abel
  have hx0I : x0 ∈ I := by
    rw [hmemI, hx0, sub_mul, hhg]
    have e : ((D * c : ℕ) : BAQ) * w * g = (c : BAQ) * (w * ((D : BAQ) * g)) := by
      rw [mul_comm D c, Nat.cast_mul, mul_assoc (c : BAQ), Nat.cast_comm D w]
      simp only [mul_assoc]
    rw [e, sub_eq_add_neg]
    exact OhatQ_add OhatQ_one (OhatQ_neg (OhatQ_mul (OhatQ_natCast c) (OhatQ_mul hw hDg)))
  obtain ⟨q, hq, hx0q⟩ := hαgen x0 hx0I
  -- the unit `u = α g`
  have hu0 : bEmb α * g ∈ OhatQ := hαI
  have hu1 : h * bEmb (binv α) ∈ OhatQ := by
    have e1 : h = bEmb x0 + ((D * c : ℕ) : BAQ) * w := by rw [hx0]; abel
    have e2 : h * bEmb (binv α) = bEmb q + (D : BAQ) * (w * bEmb ((c : ℚ) • binv α)) := by
      rw [e1, add_mul, hx0q, map_mul, mul_assoc, ← map_mul, mul_binv hnα, map_one, mul_one]
      congr 1
      rw [bEmb_natSmul, Nat.cast_mul, mul_assoc (D : BAQ), Nat.cast_comm c w]
      simp only [mul_assoc]
    rw [e2]
    exact OhatQ_add (bEmb_mem_of_inO hq)
      (OhatQ_mul (OhatQ_natCast D) (OhatQ_mul hw (bEmb_mem_of_inO hcO)))
  have hu01 : bEmb α * g * (h * bEmb (binv α)) = 1 := by
    rw [mul_assoc, ← mul_assoc (g : BAQ), hgh, one_mul, ← map_mul, mul_binv hnα, map_one]
  have hu10 : h * bEmb (binv α) * (bEmb α * g) = 1 := by
    rw [mul_assoc, ← mul_assoc (bEmb (binv α)), ← map_mul, binv_mul hnα, map_one, one_mul, hhg]
  let u : BAQˣ := ⟨bEmb α * g, h * bEmb (binv α), hu01, hu10⟩
  refine ⟨binv α, nrd_ne_zero_of_mul (binv_mul hnα), u, ⟨hu0, hu1⟩, ?_⟩
  show (g : BAQ) = bEmb (binv α) * (bEmb α * g)
  rw [← mul_assoc, ← map_mul, binv_mul hnα, map_one, one_mul]

end RayClassCFT
