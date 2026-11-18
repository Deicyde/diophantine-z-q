import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Forms
import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Lattice

/-! The theta blocks at a common level, their weight-two realization as an
uncited input, and the integral diamond correction. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaCoeff

open Finset TraceLimits
open ZInQ.Manuscript.RC.Odd
open scoped Classical

variable {I K O G : Type} [Fintype I] [Field K] [CommRing O] [IsDomain O] [CharZero O]
  [Algebra O K] [Group G]
variable {M W R : ℕ} {S : AppF.ThetaStage (StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {m : Ideal O} {goodSet Q : ℕ → Prop}

/-- The finite collection used in a single invocation: all subsets of a fixed pool
of good stage primes within the operator budget. -/
structure Window (goodSet : ℕ → Prop) (S : AppF.ThetaStage (StageRing O M)) (W : ℕ) where
  pool : Finset ℕ
  card_le : pool.card ≤ W
  type_good : ∀ p ∈ pool, goodSet p
  stage_good : ∀ p ∈ pool, S.Good p

variable (P : Window goodSet S W)

theorem Window.admissible (U : Finset ℕ) (hU : U ⊆ P.pool) : Admissible S W U :=
  ⟨(Finset.card_le_card hU).trans P.card_le, fun p hp => P.stage_good p (hU hp)⟩

/-- The values of the characters on the common diamond group. `η` is the
extension of the stage character to the units of the common level. `symbol D`
is the quadratic character `(D/u)` on that group for the discriminants used
here. Integral units encode sign values. Tex 8422–8424, 9497–9555, 9618–9625. -/
structure DiamondCharacters (O G : Type) [CommRing O] [Group G] (ηsource : ℕ → O) where
  level : ℕ
  level_pos : 0 < level
  four_dvd : 4 ∣ level
  minusOne : G
  representative : G → ℕ
  representative_coprime : ∀ u, (representative u).Coprime level
  minusOne_rep : (representative minusOne + 1) % level = 0
  η : G →* Oˣ
  η_eval : ∀ u, (η u : O) = ηsource (representative u)
  symbol : ℤ → G →* ℤˣ
  symbol_eval : ∀ d u, (4 * d : ℤ) ∣ (level : ℤ) →
    (symbol d u : ℤ) = jacobiSym d (representative u)
  phase_order : ∀ u, ∃ e : ℕ, (η u : O) ^ (2 ^ e : ℕ) = 1

def DiamondCharacters.ψ {ηsource : ℕ → O} (C : DiamondCharacters O G ηsource) (U : Finset ℕ) (u : G) : O :=
  (C.η u : O) * (((C.symbol (-1) u * ∏ p ∈ U, C.symbol (p : ℤ) u : ℤˣ) : ℤ) : O)

def DiamondCharacters.unaryChar {ηsource : ℕ → O} (C : DiamondCharacters O G ηsource) (i : Fin 2) (j : ℕ) (u : G) : O :=
  (C.η u : O) * (((C.symbol (-1) u ^ i.val * C.symbol (-(j : ℤ)) u : ℤˣ) : ℤ) : O)

private theorem intUnit_sign (v : ℤˣ) : ((v : ℤ) : O) = 1 ∨ ((v : ℤ) : O) = -1 := by
  rcases Int.units_eq_one_or v with rfl | rfl <;> simp

private theorem DiamondCharacters.sign {ηsource : ℕ → O} (C : DiamondCharacters O G ηsource) (U : Finset ℕ)
    (i : Fin 2) (j : ℕ) (u : G) : C.unaryChar i j u = C.ψ U u ∨ C.unaryChar i j u = -C.ψ U u := by
  unfold DiamondCharacters.unaryChar DiamondCharacters.ψ
  rcases intUnit_sign (O := O) (C.symbol (-1) u * ∏ p ∈ U, C.symbol (p : ℤ) u) with h | h <;>
    rcases intUnit_sign (O := O) (C.symbol (-1) u ^ i.val * C.symbol (-(j : ℤ)) u) with h' | h' <;>
    rw [h, h'] <;> simp

private theorem twoPower_reduce (hm : m.IsPrime) (h2 : (2 : O) ∈ m) {x : O}
    (e : ℕ) (hx : x ^ (2 ^ e : ℕ) = 1) : x - 1 ∈ m := by
  induction e generalizing x with
  | zero => simp at hx; simp [hx]
  | succ e ih =>
    have hx' : (x ^ 2) ^ (2 ^ e : ℕ) = 1 := by
      rw [← pow_mul, mul_comm 2, ← pow_succ, hx]
    have hy : (x - 1) ^ 2 ∈ m := by
      rw [show (x - 1) ^ 2 = (x ^ 2 - 1) - 2 * (x - 1) by ring]
      exact m.sub_mem (ih hx') (m.mul_mem_right _ h2)
    exact hm.mem_of_pow_mem 2 hy

private theorem DiamondCharacters.ψ_reduce {ηsource : ℕ → O} (C : DiamondCharacters O G ηsource) (U : Finset ℕ)
    (u : G) (hm : m.IsPrime) (h2 : (2 : O) ∈ m) : C.ψ U u - 1 ∈ m := by
  obtain ⟨e, he⟩ := C.phase_order u
  have hη := twoPower_reduce hm h2 e he
  unfold DiamondCharacters.ψ
  rcases intUnit_sign (O := O) (C.symbol (-1) u * ∏ p ∈ U, C.symbol (p : ℤ) u) with h | h
  · rw [h, mul_one]; exact hη
  · rw [h, show (C.η u : O) * (-1 : O) - 1 = -((C.η u : O) - 1) - 2 by ring]
    exact m.sub_mem (m.neg_mem hη) h2

variable {P} (A : Basis I K G Q) (E : Lift S) (D₀ : Divisions E δ W R adm)
variable (C : DiamondCharacters O G E.η)

/-- ELLIOT (uncited, tex 9548–9555, 9620–9625, 9647–9654). The two actual
weight-two blocks `θ B_U` and `θ Θ_j` lie in the chosen constituent span, with
their indicated expansions and scalar characters. Their combination `F_U` is
constructed below. -/
structure Blocks where
  level_support : ∀ p ∈ P.pool, p ∣ C.level
  good_coprime : ∀ q, Q q → q.Coprime C.level
  atPrime_rep : ∀ q : {q // Q q}, C.representative (A.atPrime q) ≡ q.val [MOD C.level]
  /-- The character of the underlying unary theta series is odd (tex 9618). -/
  unary_odd : (C.η C.minusOne : O) * ((C.symbol (-1) C.minusOne : ℤ) : O) ^ E.parity.val = -1
  b : ∀ U : Finset ℕ, U ⊆ P.pool → I → K
  unary : ∀ U : Finset ℕ, U ⊆ P.pool → ℕ → I → K
  b_eval : ∀ U (hU : U ⊆ P.pool) n, A.eval n (b U hU) =
    algebraMap O K (E.FourierB D₀ (P.admissible U hU) n)
  unary_eval : ∀ U (hU : U ⊆ P.pool) j, j ∈ subscripts U → ∀ n,
    A.eval n (unary U hU j) = algebraMap O K (E.FourierUnary j n)
  b_diamond : ∀ U (hU : U ⊆ P.pool) u, A.diamond u (b U hU) =
    C.ψ U u • b U hU
  unary_diamond : ∀ U (hU : U ⊆ P.pool) j, j ∈ subscripts U → ∀ u,
    A.diamond u (unary U hU j) = C.unaryChar E.parity j u • unary U hU j

variable {A E D₀ C} (V : Blocks (P := P) A E D₀ C)

def Blocks.vector (U : Finset ℕ) (hU : U ⊆ P.pool) : I → K :=
  (2 : K)⁻¹ • (V.b U hU -
    ∑ j ∈ subscripts U, E.B D₀ (P.admissible U hU) j • V.unary U hU j)

def Blocks.seed (U : Finset ℕ) : I → K :=
  if hU : U ⊆ P.pool then V.vector U hU else 0

private def thetaMul : (ℕ → O) →ₗ[O] (ℕ → O) where
  toFun := timesTheta
  map_add' f g := by
    funext n
    simp only [timesTheta, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' r f := by
    funext n
    simp only [timesTheta, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

private theorem coeff_timesTheta (U : Finset ℕ) (hU : U ⊆ P.pool) (n : ℕ) :
    2 * E.FourierF D₀ (P.admissible U hU) n = E.FourierB D₀ (P.admissible U hU) n -
      ∑ j ∈ subscripts U, E.B D₀ (P.admissible U hU) j * E.FourierUnary j n := by
  have he : (2 : O) • E.HU D₀ (P.admissible U hU) = E.B D₀ (P.admissible U hU) -
      ∑ j ∈ subscripts U, E.B D₀ (P.admissible U hU) j • E.unary j := by
    funext k
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply] using
      HU_spec E D₀ (P.admissible U hU) k
  have he' := congrArg (thetaMul (O := O)) he
  rw [map_smul, map_sub, map_sum] at he'
  simp_rw [map_smul] at he'
  have h := congrFun he' n
  have hmul (f : ℕ → O) (n : ℕ) : thetaMul f n = timesTheta f n := rfl
  simpa only [map_smul, map_sub, map_sum, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul,
    hmul, Lift.FourierF, Lift.FourierB, Lift.FourierUnary] using h

theorem eval_smul_O (n : ℕ) (o : O) (v : I → K) :
    A.eval n (o • v) = algebraMap O K o * A.eval n v := by
  rw [← LinearMap.restrictScalars_apply O (A.eval n), map_smul,
    LinearMap.restrictScalars_apply, Algebra.smul_def]

theorem Blocks.vector_eval (hinj : Function.Injective (algebraMap O K))
    (U : Finset ℕ) (hU : U ⊆ P.pool) (n : ℕ) :
    A.eval n (V.vector U hU) = algebraMap O K (E.FourierF D₀ (P.admissible U hU) n) := by
  have h2 : (2 : K) ≠ 0 := by
    intro e
    exact (by norm_num : (2 : O) ≠ 0) (hinj (by rw [map_ofNat, map_zero, e]))
  rw [Blocks.vector, map_smul, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ h2, map_sub, V.b_eval, map_sum,
    ← map_ofNat (algebraMap O K), ← map_mul, coeff_timesTheta (E := E) (D₀ := D₀) U hU n, map_sub, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by
    rw [eval_smul_O, V.unary_eval U hU j hj n, map_mul]

/-- The actual integral correction coefficients in tex 9655–9660. -/
def Blocks.c (_V : Blocks (P := P) A E D₀ C) (U : Finset ℕ) (hU : U ⊆ P.pool) (u : G) (j : ℕ) : O :=
  (diamond_correction_integral (E.B D₀ (P.admissible U hU) j) (C.ψ U u)
    (C.unaryChar E.parity j u) (C.sign U E.parity j u)).choose

theorem Blocks.c_spec (U : Finset ℕ) (hU : U ⊆ P.pool) (u : G) (j : ℕ) :
    2 * V.c U hU u j = E.B D₀ (P.admissible U hU) j * (C.ψ U u - C.unaryChar E.parity j u) :=
  (diamond_correction_integral _ _ _ (C.sign U E.parity j u)).choose_spec

private theorem diamond_smul_O (u : G) (o : O) (v : I → K) :
    A.diamond u (o • v) = o • A.diamond u v :=
  ((A.diamond u).restrictScalars O).map_smul o v

theorem Blocks.diamond_vector (hinj : Function.Injective (algebraMap O K))
    (U : Finset ℕ) (hU : U ⊆ P.pool) (u : G) :
    A.diamond u (V.vector U hU) =
      C.ψ U u • V.vector U hU + ∑ j ∈ subscripts U, V.c U hU u j • V.unary U hU j := by
  have h2 : (2 : K) ≠ 0 := by
    intro e
    exact (by norm_num : (2 : O) ≠ 0) (hinj (by rw [map_ofNat, map_zero, e]))
  have hc (j) : algebraMap O K (V.c U hU u j) =
      (2 : K)⁻¹ * (algebraMap O K (E.B D₀ (P.admissible U hU) j) *
        (algebraMap O K (C.ψ U u) - algebraMap O K (C.unaryChar E.parity j u))) := by
    rw [eq_comm, inv_mul_eq_iff_eq_mul₀ h2]
    simpa only [map_mul, map_sub, map_ofNat, mul_comm (2 : K)] using
      (congrArg (algebraMap O K) (V.c_spec U hU u j)).symm
  unfold Blocks.vector
  simp only [map_smul, map_sub, map_sum, diamond_smul_O, V.b_diamond]
  funext i
  have hO (r : O) (v : I → K) : (r • v) i = algebraMap O K r * v i := by
    rw [Pi.smul_apply, Algebra.smul_def]
  have hK (r : K) (v : I → K) : (r • v) i = r * v i := by
    rw [Pi.smul_apply, smul_eq_mul]
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, hO, hK]
  let t := (2 : K)⁻¹
  let ψ := algebraMap O K (C.ψ U u)
  let b (j : ℕ) := algebraMap O K (E.B D₀ (P.admissible U hU) j)
  let a (j : ℕ) := V.unary U hU j i
  let c (j : ℕ) := algebraMap O K (C.unaryChar E.parity j u)
  have hu : (∑ j ∈ subscripts U, b j * (A.diamond u (V.unary U hU j)) i) =
      ∑ j ∈ subscripts U, b j * (c j * a j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [V.unary_diamond U hU j hj, hO]
  change t * (ψ * V.b U hU i - ∑ j ∈ subscripts U, b j * (A.diamond u (V.unary U hU j)) i) =
    ψ * (t * (V.b U hU i - ∑ j ∈ subscripts U, b j * a j)) +
      ∑ j ∈ subscripts U, algebraMap O K (V.c U hU u j) * a j
  rw [hu]
  have he : (∑ j ∈ subscripts U, algebraMap O K (V.c U hU u j) * a j) =
      (ψ * t) * (∑ j ∈ subscripts U, b j * a j) - t * (∑ j ∈ subscripts U, b j * (c j * a j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hc]
    change t * (b j * (ψ - c j)) * a j = _
    ring
  rw [he]
  ring

theorem Blocks.diamond_eval (hinj : Function.Injective (algebraMap O K))
    (U : Finset ℕ) (hU : U ⊆ P.pool) (u : G) (n : ℕ) :
    A.eval n (A.diamond u (V.vector U hU)) = algebraMap O K
      (C.ψ U u * E.FourierF D₀ (P.admissible U hU) n +
        ∑ j ∈ subscripts U, V.c U hU u j * E.FourierUnary j n) := by
  rw [V.diamond_vector hinj, map_add, map_sum, map_add, map_mul, map_sum]
  congr 1
  · rw [eval_smul_O, V.vector_eval hinj]
  · exact Finset.sum_congr rfl fun j hj => by
      rw [eval_smul_O, V.unary_eval U hU j hj n, map_mul]

theorem Blocks.integral_seed (hinj : Function.Injective (algebraMap O K)) (U : Finset ℕ) (u : G)
    (n : ℕ) : A.eval n (A.diamond u (V.seed U)) ∈ integralRange (O := O) := by
  unfold Blocks.seed
  split_ifs with hU
  · rw [V.diamond_eval hinj]
    exact ⟨_, rfl⟩
  · simp [integralRange]

def Blocks.F (U : Finset ℕ) : A.Λ (O := O) V.seed := ⟨V.seed U, A.mem_seed V.seed U⟩

/-- The coefficient family restricts to the computed theta series on the active forms. -/
theorem Blocks.coeff_F (hinj : Function.Injective (algebraMap O K))
    (U : Finset ℕ) (hU : U ⊆ P.pool) (n : ℕ) :
    A.coeff V.seed hinj (V.integral_seed hinj) n (V.F U) =
      E.FourierF D₀ (P.admissible U hU) n := by
  apply hinj
  rw [A.coeff_spec]
  change A.eval n (V.seed U) = _
  rw [Blocks.seed, dite_eq_left hU, V.vector_eval hinj]

theorem Blocks.hzero (U : Finset ℕ) (hU : ¬ ∀ p ∈ U, goodSet p) : V.F U = 0 := by
  apply Subtype.ext
  exact dite_eq_right (fun h => hU fun p hp => P.type_good p (h hp))

theorem DiamondCharacters.det_scalar {ηsource : ℕ → O} (C : DiamondCharacters O G ηsource) (u : G) (U : Finset ℕ) (r : ℕ)
    (hr : r.Prime) (hr2 : r ≠ 2) (hm : m.IsPrime) (h2 : (2 : O) ∈ m) :
    (r : O) * C.ψ U u - 1 ∈ m := by
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  have hr' : (r : O) - 1 ∈ m := by
    rw [hk]
    push_cast
    ring_nf
    exact m.mul_mem_left _ h2
  have he : (r : O) * C.ψ U u - 1 = (r : O) * (C.ψ U u - 1) + ((r : O) - 1) := by ring
  rw [he]
  exact m.add_mem (m.mul_mem_left _ (C.ψ_reduce U u hm h2)) hr'

#print axioms Window.admissible
#print axioms intUnit_sign
#print axioms DiamondCharacters.sign
#print axioms twoPower_reduce
#print axioms DiamondCharacters.ψ_reduce
#print axioms coeff_timesTheta
#print axioms eval_smul_O
#print axioms diamond_smul_O
#print axioms Blocks.vector_eval
#print axioms Blocks.c_spec
#print axioms Blocks.diamond_vector
#print axioms Blocks.diamond_eval
#print axioms Blocks.integral_seed
#print axioms Blocks.coeff_F
#print axioms Blocks.hzero
#print axioms DiamondCharacters.det_scalar

end ZInQ.Manuscript.RC.ThetaCoeff
