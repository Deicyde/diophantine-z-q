import ZInQKernel.Contrib.OneProof.JDescent3FunctionField
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-! The short cubic in the actual function field, constructed from its identity pole spaces. -/

namespace HDec.CMBranch.CMjBridges

open AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry

noncomputable section

set_option maxHeartbeats 800000

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

private abbrev PoleSpace {k F : Type} [Field k] [Field F] [Algebra k F]
    (P : Place k F) (n : ℤ) : Submodule k F :=
  riemannRochSpace (n • WeilDivisor.ofPoint P)

private theorem place_ord_add_of_lt {k F : Type} [Field k] [Field F] [Algebra k F]
    (P : Place k F) {f g : F} (h : P.ord f < P.ord g) (hf : f ≠ 0) :
    P.ord (f + g) = P.ord f := by
  by_cases hg : g = 0
  · simp [hg]
  · rw [P.ord_add_eq_min_of_ord_ne hf hg (ne_of_lt h), min_eq_left h.le]

private theorem abVar_cubicRelation {k F : Type} [Field k] [Field F] [Algebra k F]
    (P : Place k F) (hdim : Module.finrank k (PoleSpace P 6) = 6)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxo : P.ord x = -2) (hyo : P.ord y = -3)
    (hxr : ∀ Q, Q ≠ P → 0 ≤ Q.ord x) (hyr : ∀ Q, Q ≠ P → 0 ≤ Q.ord y) :
    ∃ C D E G H I : k, C ≠ 0 ∧ y ^ 2 =
      algebraMap k F C * x ^ 3 + algebraMap k F D * (x * y) + algebraMap k F E * x ^ 2 +
        algebraMap k F G * y + algebraMap k F H * x + algebraMap k F I := by
  classical
  let v : Fin 6 → F := ![x ^ 3, x * y, x ^ 2, y, x, 1]
  have hv0 (i : Fin 6) : v i ≠ 0 := by
    fin_cases i <;> simp [v, hx, hy]
  have hvo (i : Fin 6) : P.ord (v i) = ![-6, -5, -4, -3, -2, (0 : ℤ)] i := by
    fin_cases i <;> simp [v, P.ord_pow, P.ord_mul hx hy, hxo, hyo, P.ord_one]
  have hvr (Q : Place k F) (hQ : Q ≠ P) (i : Fin 6) : 0 ≤ Q.ord (v i) := by
    have hx' := hxr Q hQ
    have hy' := hyr Q hQ
    fin_cases i <;> simp [v, Q.ord_pow, Q.ord_mul hx hy, Q.ord_one] <;> omega
  have hv (i : Fin 6) : v i ∈ PoleSpace P 6 := by
    refine (mem_riemannRochSpace_zsmul_ofPoint_iff (hv0 i)).2 ⟨?_, fun Q hQ => hvr Q hQ i⟩
    rw [hvo]
    fin_cases i <;> decide
  let w (i : Fin 6) : PoleSpace P 6 := ⟨v i, hv i⟩
  have hli : LinearIndependent k w := by
    apply LinearIndependent.of_comp (PoleSpace P 6).subtype
    apply P.linearIndependent_of_injective_ord hv0
    intro i j h
    change P.ord (v i) = P.ord (v j) at h
    rw [hvo, hvo] at h
    exact (show ∀ i j : Fin 6, ![-6, -5, -4, -3, -2, (0 : ℤ)] i =
      ![-6, -5, -4, -3, -2, (0 : ℤ)] j → i = j by decide) i j h
  have : Module.Finite k (PoleSpace P 6) := Module.finite_of_finrank_pos (hdim ▸ by decide)
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hyMem : y ^ 2 ∈ PoleSpace P 6 := by
    refine (mem_riemannRochSpace_zsmul_ofPoint_iff (pow_ne_zero _ hy)).2
      ⟨by rw [P.ord_pow, hyo]; norm_num, fun Q hQ => ?_⟩
    rw [Q.ord_pow]
    have := hyr Q hQ
    omega
  let c : Fin 6 → k := fun i => B.repr ⟨y ^ 2, hyMem⟩ i
  have heq : y ^ 2 = ∑ i, algebraMap k F (c i) * v i := by
    have h := congrArg (fun z : PoleSpace P 6 => (z : F)) (B.sum_repr ⟨y ^ 2, hyMem⟩)
    push_cast at h
    simpa only [B, coe_basisOfLinearIndependentOfCardEqFinrank, w, c, Algebra.smul_def] using h.symm
  have hc : c 0 ≠ 0 := by
    intro hz
    have hm (i : Fin 6) : -5 ≤ P.ord (algebraMap k F (c i) * v i) := by
      by_cases h : c i = 0
      · simp [h, P.ord_zero]
      · rw [P.ord_mul (map_ne_zero (algebraMap k F) |>.mpr h) (hv0 i), P.ord_algebraMap,
          zero_add, hvo]
        have hi : i ≠ 0 := fun hi => h (hi ▸ hz)
        fin_cases i <;> first | contradiction | decide
    let R := PoleSpace P 5
    have hmem (i : Fin 6) : algebraMap k F (c i) * v i ∈ R := by
      by_cases h : c i = 0
      · simp [h]
      have hn := mul_ne_zero ((map_ne_zero (algebraMap k F)).mpr h) (hv0 i)
      refine (mem_riemannRochSpace_zsmul_ofPoint_iff hn).2 ⟨hm i, fun Q hQ => ?_⟩
      rw [Q.ord_mul ((map_ne_zero (algebraMap k F)).mpr h) (hv0 i), Q.ord_algebraMap, zero_add]
      exact hvr Q hQ i
    have hp := (mem_riemannRochSpace_zsmul_ofPoint_iff (pow_ne_zero 2 hy)).1
      (heq ▸ R.sum_mem (fun i (_ : i ∈ Finset.univ) => hmem i))
    rw [P.ord_pow, hyo] at hp
    norm_num at hp
  refine ⟨c 0, c 1, c 2, c 3, c 4, c 5, hc, ?_⟩
  simpa [Fin.sum_univ_succ, v, add_assoc] using heq

private theorem abVar_no_simplePole {k F : Type} [Field k] [Field F] [Algebra k F]
    (P : Place k F) (hdim : Module.finrank k (PoleSpace P 1) = 1)
    {f : F} (hf : f ≠ 0) (ho : P.ord f = -1) (hr : ∀ Q, Q ≠ P → 0 ≤ Q.ord f) :
    False := by
  let v : Fin 2 → F := ![1, f]
  have hi : LinearIndependent k v := by
    apply P.linearIndependent_of_injective_ord
    · intro i
      fin_cases i <;> simp [v, hf]
    · intro i j h
      change P.ord (v i) = P.ord (v j) at h
      fin_cases i <;> fin_cases j <;> simp [v, P.ord_one, ho] at h ⊢
  have hm (i : Fin 2) : v i ∈ PoleSpace P 1 := by
    fin_cases i
    · exact (mem_riemannRochSpace_zsmul_ofPoint_iff one_ne_zero).2
        ⟨by rw [P.ord_one]; decide, fun Q _ => by rw [Q.ord_one]⟩
    · exact (mem_riemannRochSpace_zsmul_ofPoint_iff hf).2 ⟨ho.ge, hr⟩
  let w (i : Fin 2) : PoleSpace P 1 := ⟨v i, hm i⟩
  have hw : LinearIndependent k w :=
    hi.of_comp (PoleSpace P 1).subtype
  have : Module.Finite k (PoleSpace P 1) := Module.finite_of_finrank_pos (hdim ▸ by decide)
  have h := hw.fintype_card_le_finrank
  rw [hdim, Fintype.card_fin] at h
  omega

private theorem abVar_shortCubic_nonsingular {k F : Type} [Field k] [CharZero k] [Field F]
    [Algebra k F] (P : Place k F) (hdim : Module.finrank k (PoleSpace P 1) = 1)
    {x y : F} {a b : k} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxo : P.ord x = -2) (hyo : P.ord y = -3)
    (hxr : ∀ Q, Q ≠ P → 0 ≤ Q.ord x)
    (heq : y ^ 2 = x ^ 3 + algebraMap k F a * x + algebraMap k F b) :
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve k).Δ ≠ 0 := by
  intro hΔ
  have hab : 4 * a ^ 3 + 27 * b ^ 2 = 0 := by
    have h : (⟨0, 0, 0, a, b⟩ : WeierstrassCurve k).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
      unfold WeierstrassCurve.Δ WeierstrassCurve.b₂ WeierstrassCurve.b₄ WeierstrassCurve.b₆
        WeierstrassCurve.b₈
      dsimp
      ring
    rw [h] at hΔ
    exact (mul_eq_zero.mp hΔ).resolve_left (by norm_num)
  obtain ⟨r, ha, hb⟩ : ∃ r : k, a = -3 * r ^ 2 ∧ b = 2 * r ^ 3 := by
    by_cases ha : a = 0
    · have hb : b = 0 := by simpa [ha] using hab
      exact ⟨0, by simp [ha], by simp [hb]⟩
    · refine ⟨-3 * b / (2 * a), ?_, ?_⟩
      · field_simp
        linear_combination hab
      · field_simp
        linear_combination b * hab
  let r' := algebraMap k F r
  have hq : P.ord (x - r') = -2 := by
    rw [sub_eq_add_neg, place_ord_add_of_lt P _ hx, hxo]
    rw [P.ord_neg, P.ord_algebraMap, hxo]
    decide
  have hq0 : x - r' ≠ 0 := by
    intro h
    rw [h, P.ord_zero] at hq
    omega
  have hf : y / (x - r') ≠ 0 := div_ne_zero hy hq0
  have hfactor : y ^ 2 = (x - r') ^ 2 * (x + 2 * r') := by
    rw [heq, ha, hb]
    simp only [map_mul, map_neg, map_ofNat, map_pow, r']
    ring
  have hsquare : (y / (x - r')) ^ 2 = x + 2 * r' := by
    rw [div_pow, hfactor, mul_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hq0)]
  apply abVar_no_simplePole P hdim hf
  · rw [P.ord_div hy hq0, hyo, hq]
    decide
  · intro Q hQ
    have hm : x + 2 * r' ∈ Q.integers := by
      apply Q.integers.toSubring.add_mem
      · exact Q.mem_integers_iff_ord_nonneg.mpr (hxr Q hQ)
      · apply Q.integers.toSubring.mul_mem
        · simpa only [ValuationSubring.mem_toSubring, map_ofNat] using Q.algebraMap_mem_integers (2 : k)
        · exact Q.algebraMap_mem_integers r
    have hn := Q.mem_integers_iff_ord_nonneg.mp hm
    rw [← hsquare, Q.ord_pow] at hn
    omega

/-- The genus-one pole spaces of the actual curve give a nonsingular short cubic over the
ground field. Its two coordinates have exact orders minus two and minus three at the identity
and are regular at every other place. -/
theorem abVar_shortCubic_of_genusOne {L : Type} [Field L] [NumberField L]
    (hgenus : AbVarFunctionFieldGenusOne) (A : PkgI3.AbVar L) (hdim : A.dim = 1) :
    ∃ (P : Place L (AbVarFunctionField A)) (x y : AbVarFunctionField A) (a b : L),
      (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
        P.integers.toSubring ∧
      x ≠ 0 ∧ y ≠ 0 ∧ P.ord x = -2 ∧ P.ord y = -3 ∧
      (∀ Q, Q ≠ P → 0 ≤ Q.ord x ∧ 0 ≤ Q.ord y) ∧
      y ^ 2 = x ^ 3 + algebraMap L (AbVarFunctionField A) a * x +
        algebraMap L (AbVarFunctionField A) b ∧
      (⟨0, 0, 0, a, b⟩ : WeierstrassCurve L).Δ ≠ 0 := by
  obtain ⟨P, _, hstalk, hd, hex⟩ := abVar_identityPoleSpaces_of_genusOne hgenus A hdim
  obtain ⟨x, hx, hxo, hxr⟩ := hex 2 (by decide)
  norm_num at hxo
  obtain ⟨y, hy, hyo, hyr⟩ := hex 3 (by decide)
  norm_num at hyo
  have hdim' (n : ℕ) (hn : 1 ≤ n) : Module.finrank L (PoleSpace P (n : ℤ)) = n := by
    simpa only [WeilDivisor.single_eq_zsmul_ofPoint, Divisor.dim_def] using hd n hn
  obtain ⟨C, D, E, G, H, I, hC, hrel⟩ :=
    abVar_cubicRelation P (hdim' 6 (by decide)) hx hy hxo hyo hxr hyr
  let F := AbVarFunctionField A
  let ι := algebraMap L F
  let q := E + D ^ 2 / 4
  let r := C * H + D * C * G / 2
  let s := C ^ 2 * I + (C * G) ^ 2 / 4
  let a := r - q ^ 2 / 3
  let b := s - q * r / 3 + 2 * q ^ 3 / 27
  let X := ι C * x + ι (q / 3)
  let Y := ι C * y - (ι (D / 2) * (ι C * x) + ι (C * G / 2))
  have hC' : ι C ≠ 0 := (map_ne_zero ι).mpr hC
  have hrel' : Y ^ 2 = X ^ 3 + ι a * X + ι b := by
    have : CharZero F := Algebra.charZero_of_charZero L F
    dsimp [X, Y, a, b, q, r, s, ι] at *
    simp only [map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat]
    linear_combination (algebraMap L F C) ^ 2 * hrel
  have hXo : P.ord X = -2 := by
    have ho : P.ord (ι C * x) = -2 := by
      rw [P.ord_mul hC' hx, P.ord_algebraMap, hxo, zero_add]
    dsimp [X]
    rw [place_ord_add_of_lt P _ (mul_ne_zero hC' hx), ho]
    rw [ho, P.ord_algebraMap]
    decide
  have hYo : P.ord Y = -3 := by
    have ho : P.ord (ι C * y) = -3 := by
      rw [P.ord_mul hC' hy, P.ord_algebraMap, hyo, zero_add]
    have hp : -2 ≤ P.ord (ι (D / 2) * (ι C * x)) := by
      by_cases h : D / 2 = 0
      · simp [ι, h, P.ord_zero]
      · rw [P.ord_mul ((map_ne_zero ι).mpr h) (mul_ne_zero hC' hx), P.ord_mul hC' hx,
          P.ord_algebraMap, P.ord_algebraMap, hxo]
        decide
    have htail : -2 ≤ P.ord (ι (D / 2) * (ι C * x) + ι (C * G / 2)) := by
      by_cases ht : ι (D / 2) * (ι C * x) + ι (C * G / 2) = 0
      · rw [ht, P.ord_zero]
        decide
      · have hm := P.min_ord_le_ord_add ht
        rw [P.ord_algebraMap] at hm
        exact (le_min hp (by decide)).trans hm
    dsimp [Y]
    rw [sub_eq_add_neg, place_ord_add_of_lt P _ (mul_ne_zero hC' hy), ho]
    rw [P.ord_neg, ho]
    omega
  have hX : X ≠ 0 := by
    intro h
    rw [h, P.ord_zero] at hXo
    omega
  have hY : Y ≠ 0 := by
    intro h
    rw [h, P.ord_zero] at hYo
    omega
  have hreg (Q : Place L F) (hQ : Q ≠ P) : 0 ≤ Q.ord X ∧ 0 ≤ Q.ord Y := by
    have hx' := Q.mem_integers_iff_ord_nonneg.mpr (hxr Q hQ)
    have hy' := Q.mem_integers_iff_ord_nonneg.mpr (hyr Q hQ)
    have hc (c : L) : ι c ∈ Q.integers := Q.algebraMap_mem_integers c
    exact ⟨Q.mem_integers_iff_ord_nonneg.mp (Q.integers.toSubring.add_mem (Q.integers.toSubring.mul_mem (hc C) hx')
        (hc _)), Q.mem_integers_iff_ord_nonneg.mp (Q.integers.toSubring.sub_mem
          (Q.integers.toSubring.mul_mem (hc C) hy') (Q.integers.toSubring.add_mem
            (Q.integers.toSubring.mul_mem (hc _) (Q.integers.toSubring.mul_mem (hc C) hx')) (hc _)))⟩
  exact ⟨P, X, Y, a, b, hstalk, hX, hY, hXo, hYo, hreg, hrel',
    abVar_shortCubic_nonsingular P (hdim' 1 (by decide)) hX hY hXo hYo
      (fun Q hQ => (hreg Q hQ).1) hrel'⟩

#print axioms place_ord_add_of_lt
#print axioms abVar_cubicRelation
#print axioms abVar_no_simplePole
#print axioms abVar_shortCubic_nonsingular
#print axioms abVar_shortCubic_of_genusOne

end

end HDec.CMBranch.CMjBridges
