import Mathlib

open Polynomial Module

noncomputable section

namespace T

theorem linIndep_map {K E : Type*} [Field K] [Field E] [Algebra K E] {N d : Type*} [Fintype N]
    [Fintype d] [DecidableEq d] {v : d → N → K} (hv : LinearIndependent K v) :
    LinearIndependent E (fun i x => algebraMap K E (v i x)) := by
  classical
  let P : Matrix N d K := Matrix.of fun x i => v i x
  have hinj : LinearMap.ker (Matrix.toLin' P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have h0 : ∑ i, c i • v i = 0 := by
      ext x
      have := congrFun hc x
      simpa [P, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm] using this
    exact funext (Fintype.linearIndependent_iff.mp hv c h0)
  obtain ⟨g, hg⟩ := (Matrix.toLin' P).exists_leftInverse_of_injective hinj
  let Q : Matrix d N K := LinearMap.toMatrix' g
  have hQP : Q * P = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : (P.map (algebraMap K E)).mulVec c = 0 := by
    ext x
    have := congrFun hc x
    simpa [P, Matrix.mulVec, dotProduct, mul_comm] using this
  have h2 : Q.map (algebraMap K E) * P.map (algebraMap K E) = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  intro i
  have h3 := congrFun (congrArg (fun M => M.mulVec c) h2) i
  simp only [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero, Matrix.one_mulVec] at h3
  exact h3.symm

theorem linIndep_baseChange {K E W : Type*} [Field K] [Field E] [Algebra K E] [AddCommGroup W]
    [Module K W] {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Basis ι K W) {d : Type*} [Fintype d]
    [DecidableEq d] {f : d → Module.End K W} (hf : LinearIndependent K f) :
    LinearIndependent E (fun i => (f i).baseChange E) := by
  classical
  have h1 : LinearIndependent K (fun i (p : ι × ι) => LinearMap.toMatrix β β (f i) p.1 p.2) := by
    refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
    have h0 : ∑ i, c i • f i = 0 := by
      apply (LinearMap.toMatrix β β).injective
      rw [map_zero, map_sum]
      ext a b
      have := congrFun hc (a, b)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
      exact this
    exact Fintype.linearIndependent_iff.mp hf c h0
  have h2 := Fintype.linearIndependent_iff.mp
    (linIndep_map (K := K) (E := E) (N := ι × ι) (d := d)
      (v := fun i (p : ι × ι) => LinearMap.toMatrix β β (f i) p.1 p.2) h1)
  refine Fintype.linearIndependent_iffₛ.mpr fun c c' hc i => ?_
  refine sub_eq_zero.mp (h2 (c - c') ?_ i)
  funext p
  have h0 := congrArg (LinearMap.toMatrix (Algebra.TensorProduct.basis E β)
    (Algebra.TensorProduct.basis E β)) hc
  rw [map_sum, map_sum] at h0
  have h3 := congrFun (congrFun h0 p.1) p.2
  simp only [map_smul, LinearMap.toMatrix_baseChange, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul] at h3
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib, h3, sub_self]

/-- Polynomials in an endomorphism conjugate to `M ⊕ M`. -/
theorem aeval_intertwines {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (S : Module.End E V) (e : V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E)) (M : Matrix (Fin 2) (Fin 2) E)
    (hS : ∀ v, e (S v) = (M.mulVec (e v).1, M.mulVec (e v).2)) (G : E[X]) (v : V) :
    e (aeval S G v) = ((aeval M G).mulVec (e v).1, (aeval M G).mulVec (e v).2) := by
  induction G using Polynomial.induction_on generalizing v with
  | C a =>
    simp [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    rfl
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq, Matrix.add_mulVec, Prod.mk_add_mk]
  | monomial n a h =>
    have h' := h (S v)
    rw [hS] at h'
    rw [pow_succ, ← mul_assoc, map_mul (aeval S) (C a * X ^ n) X, map_mul (aeval M) (C a * X ^ n) X,
      aeval_X, aeval_X, Module.End.mul_apply, h']
    simp only [Matrix.mulVec_mulVec]

theorem aeval_eq_zero_iff {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (S : Module.End E V) (e : V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E)) (M : Matrix (Fin 2) (Fin 2) E)
    (hS : ∀ v, e (S v) = (M.mulVec (e v).1, M.mulVec (e v).2)) (G : E[X]) :
    aeval S G = 0 ↔ aeval M G = 0 := by
  constructor
  · intro h
    apply (Matrix.toLin' (R := E) (m := Fin 2) (n := Fin 2)).injective
    apply LinearMap.ext
    intro w
    have := aeval_intertwines S e M hS G (e.symm (w, 0))
    rw [h, LinearMap.zero_apply, map_zero, LinearEquiv.apply_symm_apply] at this
    rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
    have h2 := congrArg Prod.fst this
    rw [Prod.fst_zero] at h2
    exact h2.symm
  · intro h
    ext v : 1
    apply e.injective
    rw [aeval_intertwines S e M hS G v, h]
    simp

theorem trace_two {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (S : Module.End E V) (e : V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E)) (M : Matrix (Fin 2) (Fin 2) E)
    (hS : ∀ v, e (S v) = (M.mulVec (e v).1, M.mulVec (e v).2)) :
    LinearMap.trace E V S = 2 * M.trace := by
  have : Module.Finite E V := Module.Finite.equiv e.symm
  have hconj : e.conj S = LinearMap.prodMap (Matrix.toLin' M) (Matrix.toLin' M) := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hS, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, Matrix.toLin'_apply]
  rw [← LinearMap.trace_conj' S e, hconj, LinearMap.trace_prodMap', Matrix.trace_toLin'_eq]
  ring

/-- **The trace from the minimal polynomial.** -/
theorem trace_eq_of_minpoly {E V : Type*} [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (S : Module.End E V) (e : V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E)) (M : Matrix (Fin 2) (Fin 2) E)
    (hS : ∀ v, e (S v) = (M.mulVec (e v).1, M.mulVec (e v).2)) (m : ℚ[X]) (hmon : m.Monic)
    (hm : ∀ G : E[X], aeval S G = 0 ↔ m.map (Rat.castHom E) ∣ G) :
    LinearMap.trace E V S = ((-(4 / m.natDegree) * m.nextCoeff : ℚ) : E) := by
  have hiff := aeval_eq_zero_iff S e M hS
  have hmm : (m.map (Rat.castHom E)).Monic := hmon.map _
  have hdeg : (m.map (Rat.castHom E)).natDegree = m.natDegree :=
    natDegree_map_eq_of_injective (Rat.castHom E).injective m
  have hdvd : m.map (Rat.castHom E) ∣ M.charpoly :=
    (hm _).mp ((hiff _).mpr (Matrix.aeval_self_charpoly M))
  have hle : m.natDegree ≤ 2 := by
    have := natDegree_le_of_dvd hdvd (Matrix.charpoly_monic M).ne_zero
    rw [hdeg, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    exact this
  have hpos : m.natDegree ≠ 0 := by
    intro h0
    have h1 : m = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon h0
    have h2 : aeval S (1 : E[X]) = 0 := (hm 1).mpr (by rw [h1, Polynomial.map_one])
    rw [map_one] at h2
    have h3 := congrArg (fun f : Module.End E V => e (f (e.symm ((fun _ => 1), 0)))) h2
    simp only [Module.End.one_apply, LinearEquiv.apply_symm_apply, LinearMap.zero_apply,
      map_zero] at h3
    have := congrFun (congrArg Prod.fst h3) 0
    simp at this
  rw [trace_two S e M hS]
  rcases (show m.natDegree = 1 ∨ m.natDegree = 2 by omega) with h1 | h2
  · have hX : m = X + C (m.coeff 0) := hmon.eq_X_add_C h1
    have hM : aeval M (m.map (Rat.castHom E)) = 0 := (hiff _).mp ((hm _).mpr dvd_rfl)
    rw [hX] at hM
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, map_add, aeval_X,
      aeval_C] at hM
    have hMe : M = -(algebraMap E (Matrix (Fin 2) (Fin 2) E) ((Rat.castHom E) (m.coeff 0))) :=
      eq_neg_of_add_eq_zero_left hM
    have hnc : m.nextCoeff = m.coeff 0 := by
      rw [Polynomial.nextCoeff, h1]; simp
    rw [hMe, hnc, h1]
    simp [Matrix.trace_neg, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, Matrix.trace_one]
    ring
  · have heq : M.charpoly = m.map (Rat.castHom E) :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmm (Matrix.charpoly_monic M) hdvd
        (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hdeg, h2])
    have htr := Matrix.trace_eq_neg_charpoly_coeff M
    rw [heq, Fintype.card_fin, Polynomial.coeff_map] at htr
    have hnc : m.nextCoeff = m.coeff 1 := by
      rw [Polynomial.nextCoeff, h2]; simp
    rw [htr, hnc, h2]
    have hc : (Rat.castHom E) (m.coeff 1) = ((m.coeff 1 : ℚ) : E) := rfl
    rw [hc]
    push_cast
    ring




theorem aeval_baseChange_map {K E W : Type*} [Field K] [Field E] [Algebra K E] [AddCommGroup W]
    [Module K W] (S : Module.End K W) (P : K[X]) :
    aeval (S.baseChange E) (P.map (algebraMap K E)) = (aeval S P).baseChange E := by
  rw [aeval_map_algebraMap]
  exact Polynomial.aeval_algHom_apply (Module.End.baseChangeHom K E W) S P

/-- The powers `S^i`, `i < deg m`, are linearly independent when the polynomials killing `S` are the
multiples of `m`. -/
theorem powIndep_of_minpoly {K W : Type*} [Field K] [AddCommGroup W] [Module K W] (S : Module.End K W)
    (m : K[X]) (hm : ∀ G : K[X], aeval S G = 0 ↔ m ∣ G) :
    LinearIndependent K (fun i : Fin m.natDegree => S ^ (i : ℕ)) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
  let Q : K[X] := ∑ i : Fin m.natDegree, C (c i) * X ^ (i : ℕ)
  have hQ : aeval S Q = 0 := by
    simp only [Q, map_sum, map_mul, aeval_C, aeval_X_pow, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
    exact hc
  intro i
  have hpos : 0 < m.natDegree := i.pos
  have hdeg : Q.natDegree < m.natDegree := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := m.natDegree - 1) ?_) ?_
    · intro i _
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_X_pow]; omega
    · omega
  have hQ0 : Q = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt ((hm Q).mp hQ) hdeg
  have := congrArg (fun P : K[X] => P.coeff i) hQ0
  simp only [Q, finset_sum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [if_neg (fun h => hj (Fin.ext h.symm)), mul_zero])
    (fun h => absurd (Finset.mem_univ i) h)] at this
  simpa using this

/-- A polynomial of degree `< deg m` killing `S ⊗ E` is zero. -/
theorem eq_zero_of_aeval_baseChange {K E W : Type*} [Field K] [Field E] [Algebra K E] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (S : Module.End K W) (m : K[X])
    (hm : ∀ G : K[X], aeval S G = 0 ↔ m ∣ G) (R : E[X]) (hRdeg : R.natDegree < m.natDegree)
    (hR : aeval (S.baseChange E) R = 0) : R = 0 := by
  classical
  have hindE0 : LinearIndependent E (fun i : Fin m.natDegree => (S ^ (i : ℕ)).baseChange E) :=
    linIndep_baseChange (Module.finBasis K W) (powIndep_of_minpoly S m hm)
  have hindE : ∀ g : Fin m.natDegree → E, ∑ i, g i • (S ^ (i : ℕ)).baseChange E = 0 → ∀ i, g i = 0 :=
    fun g hg => (Fintype.linearIndependent_iff (R := E)
      (v := fun i : Fin m.natDegree => (S ^ (i : ℕ)).baseChange E)).mp hindE0 g hg
  rw [aeval_eq_sum_range' hRdeg, Finset.sum_range] at hR
  have hcoef : ∀ i : Fin m.natDegree, R.coeff i = 0 := by
    apply hindE (fun i => R.coeff i)
    rw [← hR]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.baseChange_pow]
  ext i
  by_cases hi : i < m.natDegree
  · exact hcoef ⟨i, hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_zero]

/-- **The minimal polynomial is invariant under extension of scalars** (finite-dimensional case). -/
theorem minpoly_baseChange_iff {K E W : Type*} [Field K] [Field E] [Algebra K E] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (S : Module.End K W) (m : K[X]) (hmon : m.Monic)
    (hm : ∀ G : K[X], aeval S G = 0 ↔ m ∣ G) (G : E[X]) :
    aeval (S.baseChange E) G = 0 ↔ m.map (algebraMap K E) ∣ G := by
  have hkill : aeval (S.baseChange E) (m.map (algebraMap K E)) = 0 := by
    rw [aeval_baseChange_map, (hm m).mpr dvd_rfl, LinearMap.baseChange_zero]
  constructor
  · intro hG
    by_cases h1 : m.map (algebraMap K E) = 1
    · rw [h1]; exact one_dvd _
    rw [← modByMonic_eq_zero_iff_dvd (hmon.map _)]
    have hRdeg : (G %ₘ m.map (algebraMap K E)).natDegree < m.natDegree := by
      have := natDegree_modByMonic_lt G (hmon.map (algebraMap K E)) h1
      rwa [natDegree_map_eq_of_injective (algebraMap K E).injective] at this
    have hR : aeval (S.baseChange E) (G %ₘ m.map (algebraMap K E)) = 0 := by
      have h2 := congrArg (aeval (S.baseChange E)) (modByMonic_add_div G (m.map (algebraMap K E)))
      rw [map_add, map_mul, hkill, zero_mul, add_zero, hG] at h2
      exact h2
    exact eq_zero_of_aeval_baseChange S m hm _ hRdeg hR
  · rintro ⟨q, rfl⟩
    rw [map_mul, hkill, zero_mul]


end T
