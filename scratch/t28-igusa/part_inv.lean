
section Inv
variable {K : Type*} [Field K]
open Polynomial

theorem trP_eval (v : Fin 7 → K) (b : K) (i : Fin 7) : (trP v i).eval b = actC v 1 b 0 1 1 i := by
  fin_cases i <;> simp [trP, actC] <;> ring

theorem trP_eval_zero (v : Fin 7 → K) (i : Fin 7) : (trP v i).eval 0 = v i := by
  fin_cases i <;> simp [trP]

theorem trP_d0 (v : Fin 7 → K) : derivative (trP v 0) = trP v 1 := by
  simp [trP, map_ofNat] <;> ring
theorem trP_d1 (v : Fin 7 → K) : derivative (trP v 1) = 2 * trP v 2 := by
  simp [trP, map_ofNat] <;> ring
theorem trP_d2 (v : Fin 7 → K) : derivative (trP v 2) = 3 * trP v 3 := by
  simp [trP, map_ofNat] <;> ring
theorem trP_d3 (v : Fin 7 → K) : derivative (trP v 3) = 4 * trP v 4 := by
  simp [trP, map_ofNat] <;> ring
theorem trP_d4 (v : Fin 7 → K) : derivative (trP v 4) = 5 * trP v 5 := by
  simp [trP, map_ofNat] <;> ring
theorem trP_d5 (v : Fin 7 → K) : derivative (trP v 5) = 6 * trP v 6 := by
  simp [trP, map_ofNat] <;> ring
theorem trP_d6 (v : Fin 7 → K) : derivative (trP v 6) = 0 := by
  simp [trP]

/-- The four laws that, with the cocycle identity, give the transformation law. -/
structure IsInv (J : (Fin 7 → K) → K) (n : ℕ) : Prop where
  even : Even n
  homog : ∀ v e, J (fun i => e * v i) = e ^ n * J v
  diag : ∀ v s t, J (actC v s 0 0 t 1) = (s * t) ^ (3 * n) * J v
  swap : ∀ v, J (actC v 0 1 1 0 1) = J v
  trans : ∀ v b, J (actC v 1 b 0 1 1) = J v

theorem J2R_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (t : Fin 7 → R) :
    φ (J2R t) = J2R (fun i => φ (t i)) := by
  simp only [J2R, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one]

theorem J2R_homog (v : Fin 7 → K) (e : K) : J2R (fun i => e * v i) = e ^ 2 * J2R v := by
  simp only [J2R]; ring

theorem J2R_diag (v : Fin 7 → K) (s t : K) : J2R (actC v s 0 0 t 1) = (s * t) ^ (3 * 2) * J2R v := by
  simp only [J2R]; simp [actC]; ring

theorem J2R_swap (v : Fin 7 → K) : J2R (actC v 0 1 1 0 1) = J2R v := by
  simp only [J2R]; simp [actC]; ring

theorem J2R_deriv (t : Fin 7 → K[X]) (h0 : derivative (t 0) = t 1)
    (h1 : derivative (t 1) = 2 * t 2) (h2 : derivative (t 2) = 3 * t 3)
    (h3 : derivative (t 3) = 4 * t 4) (h4 : derivative (t 4) = 5 * t 5)
    (h5 : derivative (t 5) = 6 * t 6) (h6 : derivative (t 6) = 0) : derivative (J2R t) = 0 := by
  simp only [J2R, derivative_add, derivative_sub, derivative_neg, derivative_mul, derivative_pow,
    derivative_ofNat, derivative_one, map_natCast, map_ofNat, Nat.cast_ofNat, h0, h1, h2, h3, h4, h5, h6]
  ring

theorem J2R_trans [CharZero K] (v : Fin 7 → K) (b : K) : J2R (actC v 1 b 0 1 1) = J2R v := by
  have hc := eq_C_of_derivative_eq_zero (J2R_deriv (trP v) (trP_d0 v) (trP_d1 v) (trP_d2 v)
    (trP_d3 v) (trP_d4 v) (trP_d5 v) (trP_d6 v))
  have e1 : (evalRingHom b) (J2R (trP v)) = J2R (actC v 1 b 0 1 1) := by
    rw [J2R_map]; congr 1; funext i; exact trP_eval v b i
  have e0 : (evalRingHom 0) (J2R (trP v)) = J2R v := by
    rw [J2R_map]; congr 1; funext i; exact trP_eval_zero v i
  rw [hc] at e1 e0
  simp only [coe_evalRingHom, eval_C] at e1 e0
  rw [← e1, e0]

theorem J2R_isInv [CharZero K] : IsInv (fun v : Fin 7 → K => J2R v) 2 :=
  ⟨by decide, J2R_homog, J2R_diag, J2R_swap, J2R_trans⟩

theorem J4R_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (t : Fin 7 → R) :
    φ (J4R t) = J4R (fun i => φ (t i)) := by
  simp only [J4R, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one]

theorem J4R_homog (v : Fin 7 → K) (e : K) : J4R (fun i => e * v i) = e ^ 4 * J4R v := by
  simp only [J4R]; ring

theorem J4R_diag (v : Fin 7 → K) (s t : K) : J4R (actC v s 0 0 t 1) = (s * t) ^ (3 * 4) * J4R v := by
  simp only [J4R]; simp [actC]; ring

theorem J4R_swap (v : Fin 7 → K) : J4R (actC v 0 1 1 0 1) = J4R v := by
  simp only [J4R]; simp [actC]; ring

theorem J4R_deriv (t : Fin 7 → K[X]) (h0 : derivative (t 0) = t 1)
    (h1 : derivative (t 1) = 2 * t 2) (h2 : derivative (t 2) = 3 * t 3)
    (h3 : derivative (t 3) = 4 * t 4) (h4 : derivative (t 4) = 5 * t 5)
    (h5 : derivative (t 5) = 6 * t 6) (h6 : derivative (t 6) = 0) : derivative (J4R t) = 0 := by
  simp only [J4R, derivative_add, derivative_sub, derivative_neg, derivative_mul, derivative_pow,
    derivative_ofNat, derivative_one, map_natCast, map_ofNat, Nat.cast_ofNat, h0, h1, h2, h3, h4, h5, h6]
  ring

theorem J4R_trans [CharZero K] (v : Fin 7 → K) (b : K) : J4R (actC v 1 b 0 1 1) = J4R v := by
  have hc := eq_C_of_derivative_eq_zero (J4R_deriv (trP v) (trP_d0 v) (trP_d1 v) (trP_d2 v)
    (trP_d3 v) (trP_d4 v) (trP_d5 v) (trP_d6 v))
  have e1 : (evalRingHom b) (J4R (trP v)) = J4R (actC v 1 b 0 1 1) := by
    rw [J4R_map]; congr 1; funext i; exact trP_eval v b i
  have e0 : (evalRingHom 0) (J4R (trP v)) = J4R v := by
    rw [J4R_map]; congr 1; funext i; exact trP_eval_zero v i
  rw [hc] at e1 e0
  simp only [coe_evalRingHom, eval_C] at e1 e0
  rw [← e1, e0]

theorem J4R_isInv [CharZero K] : IsInv (fun v : Fin 7 → K => J4R v) 4 :=
  ⟨by decide, J4R_homog, J4R_diag, J4R_swap, J4R_trans⟩

theorem J6R_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (t : Fin 7 → R) :
    φ (J6R t) = J6R (fun i => φ (t i)) := by
  simp only [J6R, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one]

set_option maxHeartbeats 4000000 in
theorem J6R_homog (v : Fin 7 → K) (e : K) : J6R (fun i => e * v i) = e ^ 6 * J6R v := by
  simp only [J6R]; ring

set_option maxHeartbeats 4000000 in
theorem J6R_diag (v : Fin 7 → K) (s t : K) : J6R (actC v s 0 0 t 1) = (s * t) ^ (3 * 6) * J6R v := by
  simp only [J6R]; simp [actC]; ring

set_option maxHeartbeats 4000000 in
theorem J6R_swap (v : Fin 7 → K) : J6R (actC v 0 1 1 0 1) = J6R v := by
  simp only [J6R]; simp [actC]; ring

set_option maxHeartbeats 4000000 in
theorem J6R_deriv (t : Fin 7 → K[X]) (h0 : derivative (t 0) = t 1)
    (h1 : derivative (t 1) = 2 * t 2) (h2 : derivative (t 2) = 3 * t 3)
    (h3 : derivative (t 3) = 4 * t 4) (h4 : derivative (t 4) = 5 * t 5)
    (h5 : derivative (t 5) = 6 * t 6) (h6 : derivative (t 6) = 0) : derivative (J6R t) = 0 := by
  simp only [J6R, derivative_add, derivative_sub, derivative_neg, derivative_mul, derivative_pow,
    derivative_ofNat, derivative_one, map_natCast, map_ofNat, Nat.cast_ofNat, h0, h1, h2, h3, h4, h5, h6]
  ring

theorem J6R_trans [CharZero K] (v : Fin 7 → K) (b : K) : J6R (actC v 1 b 0 1 1) = J6R v := by
  have hc := eq_C_of_derivative_eq_zero (J6R_deriv (trP v) (trP_d0 v) (trP_d1 v) (trP_d2 v)
    (trP_d3 v) (trP_d4 v) (trP_d5 v) (trP_d6 v))
  have e1 : (evalRingHom b) (J6R (trP v)) = J6R (actC v 1 b 0 1 1) := by
    rw [J6R_map]; congr 1; funext i; exact trP_eval v b i
  have e0 : (evalRingHom 0) (J6R (trP v)) = J6R v := by
    rw [J6R_map]; congr 1; funext i; exact trP_eval_zero v i
  rw [hc] at e1 e0
  simp only [coe_evalRingHom, eval_C] at e1 e0
  rw [← e1, e0]

theorem J6R_isInv [CharZero K] : IsInv (fun v : Fin 7 → K => J6R v) 6 :=
  ⟨by decide, J6R_homog, J6R_diag, J6R_swap, J6R_trans⟩

theorem J10R_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (t : Fin 7 → R) :
    φ (J10R t) = J10R (fun i => φ (t i)) := by
  simp only [J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one]

set_option maxHeartbeats 4000000 in
theorem J10R_homog (v : Fin 7 → K) (e : K) : J10R (fun i => e * v i) = e ^ 10 * J10R v := by
  simp only [J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9]; ring

set_option maxHeartbeats 4000000 in
theorem J10R_diag (v : Fin 7 → K) (s t : K) : J10R (actC v s 0 0 t 1) = (s * t) ^ (3 * 10) * J10R v := by
  simp only [J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9]; simp [actC]; ring

set_option maxHeartbeats 4000000 in
theorem J10R_swap (v : Fin 7 → K) : J10R (actC v 0 1 1 0 1) = J10R v := by
  simp only [J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9]; simp [actC]; ring

set_option maxHeartbeats 4000000 in
theorem J10R_deriv (t : Fin 7 → K[X]) (h0 : derivative (t 0) = t 1)
    (h1 : derivative (t 1) = 2 * t 2) (h2 : derivative (t 2) = 3 * t 3)
    (h3 : derivative (t 3) = 4 * t 4) (h4 : derivative (t 4) = 5 * t 5)
    (h5 : derivative (t 5) = 6 * t 6) (h6 : derivative (t 6) = 0) : derivative (J10R t) = 0 := by
  simp only [J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9, derivative_add, derivative_sub, derivative_neg, derivative_mul, derivative_pow,
    derivative_ofNat, derivative_one, map_natCast, map_ofNat, Nat.cast_ofNat, h0, h1, h2, h3, h4, h5, h6]
  ring

theorem J10R_trans [CharZero K] (v : Fin 7 → K) (b : K) : J10R (actC v 1 b 0 1 1) = J10R v := by
  have hc := eq_C_of_derivative_eq_zero (J10R_deriv (trP v) (trP_d0 v) (trP_d1 v) (trP_d2 v)
    (trP_d3 v) (trP_d4 v) (trP_d5 v) (trP_d6 v))
  have e1 : (evalRingHom b) (J10R (trP v)) = J10R (actC v 1 b 0 1 1) := by
    rw [J10R_map]; congr 1; funext i; exact trP_eval v b i
  have e0 : (evalRingHom 0) (J10R (trP v)) = J10R v := by
    rw [J10R_map]; congr 1; funext i; exact trP_eval_zero v i
  rw [hc] at e1 e0
  simp only [coe_evalRingHom, eval_C] at e1 e0
  rw [← e1, e0]

theorem J10R_isInv [CharZero K] : IsInv (fun v : Fin 7 → K => J10R v) 10 :=
  ⟨by decide, J10R_homog, J10R_diag, J10R_swap, J10R_trans⟩

end Inv
