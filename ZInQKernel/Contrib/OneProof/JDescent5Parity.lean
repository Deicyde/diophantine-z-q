import ZInQKernel.Contrib.OneProof.JDescent5Cubic
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Map

/-! Involutions that fix the marked place in a nonsingular short presentation. -/

namespace HDec.CMBranch.CMjBridges

open TauCeti TauCeti.AlgebraicGeometry

noncomputable section

set_option maxHeartbeats 800000

variable {k F : Type} [Field k] [Field F] [Algebra k F]

private abbrev parityPoleSpace (P : Place k F) (n : ℤ) : Submodule k F :=
  riemannRochSpace (n • WeilDivisor.ofPoint P)

private theorem parity_poleExpansion (P : Place k F) {m : ℕ} {n : ℤ}
    (d : Module.finrank k (parityPoleSpace P n) = m) (hm : 0 < m)
    {v : Fin m → F} (hv0 : ∀ i, v i ≠ 0) (hvi : Function.Injective fun i => P.ord (v i))
    (hv : ∀ i, v i ∈ parityPoleSpace P n) {z : F} (hz : z ∈ parityPoleSpace P n) :
    ∃ c : Fin m → k, z = ∑ i, algebraMap k F (c i) * v i := by
  let w (i : Fin m) : parityPoleSpace P n := ⟨v i, hv i⟩
  have hi : LinearIndependent k w :=
    (P.linearIndependent_of_injective_ord hv0 hvi).of_comp (parityPoleSpace P n).subtype
  have : Module.Finite k (parityPoleSpace P n) := Module.finite_of_finrank_pos (d ▸ hm)
  let B := basisOfLinearIndependentOfCardEqFinrank' w hi (by simp [d])
  refine ⟨fun i => B.repr ⟨z, hz⟩ i, ?_⟩
  have he := congrArg (fun f : parityPoleSpace P n => (f : F)) (B.sum_repr ⟨z, hz⟩)
  push_cast at he
  simpa only [B, coe_basisOfLinearIndependentOfCardEqFinrank', w, Algebra.smul_def] using he.symm

/-- A ground-field involution preserving the identity place fixes the normalized abscissa;
it either fixes or negates the ordinate. This uses only the dimensions at orders two and
three, the distinct orders of the six monomials, and the short equation. -/
theorem shortCubic_parity_of_place_involution [CharZero k] (P : Place k F)
    (d2 : Module.finrank k (parityPoleSpace P 2) = 2)
    (d3 : Module.finrank k (parityPoleSpace P 3) = 3)
    (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ) (hP : P.map σ = P)
    {x y : F} {a b : k} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxo : P.ord x = -2) (hyo : P.ord y = -3)
    (hreg : ∀ Q, Q ≠ P → 0 ≤ Q.ord x ∧ 0 ≤ Q.ord y)
    (heq : y ^ 2 = x ^ 3 + algebraMap k F a * x + algebraMap k F b) :
    σ x = x ∧ (σ y = y ∨ σ y = -y) := by
  classical
  let ι := algebraMap k F
  have horder (z : F) : P.ord (σ z) = P.ord z := by
    rw [← Place.ord_map_apply σ P z, hP]
  have move (z : F) (hz : ∀ Q, Q ≠ P → 0 ≤ Q.ord z) :
      ∀ Q, Q ≠ P → 0 ≤ Q.ord (σ z) := by
    intro Q hQ
    let R := Q.map σ.symm
    have he : R.map σ = Q := by simp [R, Place.map_map]
    have hn : R ≠ P := fun h => hQ (by rw [h, hP] at he; exact he.symm)
    rw [← he, Place.ord_map_apply]
    exact hz R hn
  have mem {n : ℤ} {z : F} (hz : z ≠ 0) (hp : -n ≤ P.ord z)
      (hr : ∀ Q, Q ≠ P → 0 ≤ Q.ord z) : z ∈ parityPoleSpace P n :=
    (mem_riemannRochSpace_zsmul_ofPoint_iff hz).2 ⟨hp, hr⟩
  have oneMem (n : ℤ) (hn : 0 ≤ n) : 1 ∈ parityPoleSpace P n :=
    mem one_ne_zero (by rw [P.ord_one]; omega) (fun Q _ => by rw [Q.ord_one])
  have hxMem (n : ℤ) (hn : 2 ≤ n) : x ∈ parityPoleSpace P n :=
    mem hx (by rw [hxo]; omega) (fun Q h => (hreg Q h).1)
  have hyMem : y ∈ parityPoleSpace P 3 :=
    mem hy (by rw [hyo]) (fun Q h => (hreg Q h).2)
  have hxσ : σ x ∈ parityPoleSpace P 2 :=
    mem (map_ne_zero σ |>.mpr hx) (by rw [horder, hxo]) (move x (fun Q h => (hreg Q h).1))
  have hyσ : σ y ∈ parityPoleSpace P 3 :=
    mem (map_ne_zero σ |>.mpr hy) (by rw [horder, hyo]) (move y (fun Q h => (hreg Q h).2))
  let v2 : Fin 2 → F := ![x, 1]
  have hv2 (i : Fin 2) : v2 i ≠ 0 := by fin_cases i <;> simp [v2, hx]
  have hi2 : Function.Injective fun i => P.ord (v2 i) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [v2, hxo, P.ord_one] at h ⊢
  have hm2 (i : Fin 2) : v2 i ∈ parityPoleSpace P 2 := by
    fin_cases i
    · exact hxMem 2 (by decide)
    · exact oneMem 2 (by decide)
  obtain ⟨c2, hc2⟩ := parity_poleExpansion P d2 (by decide) hv2 hi2 hm2 hxσ
  let α := c2 0
  let β := c2 1
  have hxσ' : σ x = ι α * x + ι β := by
    simpa [ι, α, β, v2, Fin.sum_univ_succ] using hc2
  let v3 : Fin 3 → F := ![y, x, 1]
  have hv3 (i : Fin 3) : v3 i ≠ 0 := by fin_cases i <;> simp [v3, hx, hy]
  have hi3 : Function.Injective fun i => P.ord (v3 i) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [v3, hyo, hxo, P.ord_one] at h ⊢
  have hm3 (i : Fin 3) : v3 i ∈ parityPoleSpace P 3 := by
    fin_cases i
    · exact hyMem
    · exact hxMem 3 (by decide)
    · exact oneMem 3 (by decide)
  obtain ⟨c3, hc3⟩ := parity_poleExpansion P d3 (by decide) hv3 hi3 hm3 hyσ
  let γ := c3 0
  let δ := c3 1
  let ε := c3 2
  have hyσ' : σ y = ι γ * y + ι δ * x + ι ε := by
    simpa [ι, γ, δ, ε, v3, Fin.sum_univ_succ, add_assoc] using hc3
  let v : Fin 6 → F := ![1, x, y, x ^ 2, x * y, x ^ 3]
  have hv (i : Fin 6) : v i ≠ 0 := by fin_cases i <;> simp [v, hx, hy]
  have ho (i : Fin 6) : P.ord (v i) = ![(0 : ℤ), -2, -3, -4, -5, -6] i := by
    fin_cases i <;> simp [v, P.ord_one, hxo, hyo, P.ord_pow, P.ord_mul hx hy]
  have hi : LinearIndependent k v := by
    apply P.linearIndependent_of_injective_ord hv
    intro i j h
    change P.ord (v i) = P.ord (v j) at h
    rw [ho, ho] at h
    exact (show ∀ i j : Fin 6, ![(0 : ℤ), -2, -3, -4, -5, -6] i =
        ![(0 : ℤ), -2, -3, -4, -5, -6] j → i = j by decide) i j h
  have elim {p q r s t u : k}
      (h : ι p + ι q * x + ι r * y + ι s * x ^ 2 + ι t * (x * y) + ι u * x ^ 3 = 0) :
      p = 0 ∧ q = 0 ∧ r = 0 ∧ s = 0 ∧ t = 0 ∧ u = 0 := by
    let c : Fin 6 → k := ![p, q, r, s, t, u]
    have hs : ∑ i, c i • v i = 0 := by
      simpa [c, v, ι, Algebra.smul_def, Fin.sum_univ_succ, add_assoc] using h
    have h' := (Fintype.linearIndependent_iff.mp hi) c hs
    exact ⟨h' 0, h' 1, h' 2, h' 3, h' 4, h' 5⟩
  have hconst (c : k) : σ (ι c) = ι c := σ.commutes c
  have hx_twice : x = ι α * (ι α * x + ι β) + ι β := by
    have h := congrArg (fun z : F => σ z) hxσ'
    rw [hσ x] at h
    simpa only [map_add, map_mul, hconst, hxσ'] using h
  have hy_twice : y = ι γ * (ι γ * y + ι δ * x + ι ε) + ι δ * (ι α * x + ι β) + ι ε := by
    have h := congrArg (fun z : F => σ z) hyσ'
    rw [hσ y] at h
    simpa only [map_add, map_mul, hconst, hxσ', hyσ'] using h
  have hαβ := elim (p := α * β + β) (q := α ^ 2 - 1) (r := 0) (s := 0) (t := 0) (u := 0) (by
    simp only [map_add, map_sub, map_pow, map_mul, map_one, map_zero, zero_mul, add_zero]
    linear_combination -hx_twice)
  have hγ := elim (p := γ * ε + δ * β + ε) (q := γ * δ + δ * α) (r := γ ^ 2 - 1)
      (s := 0) (t := 0) (u := 0) (by
    simp only [map_add, map_sub, map_pow, map_mul, map_one, map_zero, zero_mul, add_zero]
    linear_combination -hy_twice)
  have hnew : (ι γ * y + ι δ * x + ι ε) ^ 2 =
      (ι α * x + ι β) ^ 3 + ι a * (ι α * x + ι β) + ι b := by
    have h := congrArg (fun z : F => σ z) heq
    simp only [map_pow, map_add, map_mul, AlgEquiv.commutes] at h
    rw [hxσ', hyσ'] at h
    exact h
  have htop := elim (p := γ ^ 2 * b + ε ^ 2 - β ^ 3 - a * β - b)
    (q := γ ^ 2 * a + 2 * δ * ε - 3 * α * β ^ 2 - a * α) (r := 2 * γ * ε)
    (s := δ ^ 2 - 3 * α ^ 2 * β) (t := 2 * γ * δ) (u := γ ^ 2 - α ^ 3) (by
      simp only [map_add, map_sub, map_pow, map_mul, map_ofNat]
      linear_combination hnew - (ι γ) ^ 2 * heq)
  have ha2 : α ^ 2 = 1 := sub_eq_zero.mp hαβ.2.1
  have hg2 : γ ^ 2 = 1 := sub_eq_zero.mp hγ.2.2.1
  have ha3 : α ^ 3 = 1 := (sub_eq_zero.mp htop.2.2.2.2.2).symm.trans hg2
  have ha : α = 1 := by
    rw [pow_succ, ha2, one_mul] at ha3
    exact ha3
  have hb : β = 0 := by
    have h := hαβ.1
    rw [ha, one_mul, ← two_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hfix : σ x = x := by simpa [ha, hb] using hxσ'
  refine ⟨hfix, ?_⟩
  have hs : (σ y) ^ 2 = y ^ 2 := by
    have h := congrArg (fun z : F => σ z) heq
    simp only [map_pow, map_add, map_mul, AlgEquiv.commutes, hfix] at h
    exact h.trans heq.symm
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hs

#print axioms parity_poleExpansion
#print axioms shortCubic_parity_of_place_involution

end

end HDec.CMBranch.CMjBridges
