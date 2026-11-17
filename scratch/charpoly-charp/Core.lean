import ZInQKernel.HDecomp.C10.Link

/-! # charpoly-charp, Part 1 and 3: linear algebra (Mathlib only)

* `linIndep_map`: linear independence of vectors in `N → K` survives extension of scalars.
* `linIndep_baseChange`: linear independence of endomorphisms survives `baseChange` to a field `E ⊇ K`.
* `aeval_intertwines`, `trace_eq_of_minpoly`: if `e` conjugates `S` to `M ⊕ M` (`M` a `2 × 2` matrix) and
  the polynomials killing `S` are exactly the multiples of `m ∈ ℚ[X]` (monic), then
  `tr S = -(4 / deg m) · nextCoeff m`.
-/

open Polynomial Module

noncomputable section

namespace CharpolyCharp

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


/-! ## Part 2: the minimal polynomial of `α ∈ End(A)` on `E ⊗ V_ℓ(A)` is `ℓ`-independent

From Mumford §19 Thm 3 (`PkgI3.HomFreeFinite`: `End(A)` free of finite rank, `ℤ_ℓ ⊗ End(A) → End(T_ℓ A)`
injective) and I3.M0 (`PkgI3.TateModuleFree`). -/

section AV

open PkgI3 TensorProduct CategoryTheory
open CategoryTheory.MonObj

variable {k : Type} [Field k]

theorem homT_mul' (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar k) (e e' : A.End) :
    AbVar.homT (ℓ := ℓ) (e * e') = AbVar.homT (ℓ := ℓ) e ∘ₗ AbVar.homT (ℓ := ℓ) e' := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ (e'.hom ≫ e.hom)) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ e'.hom) ≫ e.hom)
  exact congrArg Additive.ofMul (CategoryTheory.Category.assoc _ _ _).symm

theorem homT_one' (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar k) :
    AbVar.homT (ℓ := ℓ) (1 : A.End) = LinearMap.id := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ 𝟙 _) = x.1 n
  rw [CategoryTheory.Category.comp_id]; rfl

/-- `End(A) → End_E(E ⊗ V_ℓ(A))`, `φ ↦ endE φ`, as a ring homomorphism. -/
def endEHom (A : AbVar k) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra ℚ_[ℓ] E] :
    A.End →+* Module.End E (E ⊗[ℚ_[ℓ]] A.V ℓ) where
  toFun φ := GlueC10Link.endE φ ℓ E
  map_one' := by
    change ((AbVar.homT (ℓ := ℓ) (1 : A.End)).baseChange ℚ_[ℓ]).baseChange E = 1
    rw [homT_one', LinearMap.baseChange_id, LinearMap.baseChange_id]; rfl
  map_mul' φ ψ := by
    change ((AbVar.homT (ℓ := ℓ) (φ * ψ)).baseChange ℚ_[ℓ]).baseChange E =
      ((AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange E *
        ((AbVar.homT (ℓ := ℓ) ψ).baseChange ℚ_[ℓ]).baseChange E
    rw [homT_mul', LinearMap.baseChange_comp, LinearMap.baseChange_comp]; rfl
  map_zero' := by
    change ((AbVar.tateHom ℓ A A 0).baseChange ℚ_[ℓ]).baseChange E = 0
    rw [map_zero, LinearMap.baseChange_zero, LinearMap.baseChange_zero]
  map_add' φ ψ := by
    change ((AbVar.tateHom ℓ A A (φ + ψ)).baseChange ℚ_[ℓ]).baseChange E =
      ((AbVar.tateHom ℓ A A φ).baseChange ℚ_[ℓ]).baseChange E +
        ((AbVar.tateHom ℓ A A ψ).baseChange ℚ_[ℓ]).baseChange E
    rw [map_add, LinearMap.baseChange_add, LinearMap.baseChange_add]

theorem aeval_endE_int (A : AbVar k) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E]
    [Algebra ℚ_[ℓ] E] (α : A.End) (Z : ℤ[X]) :
    aeval (GlueC10Link.endE α ℓ E) (Z.map (Int.castRingHom E)) =
      GlueC10Link.endE (aeval α Z) ℓ E := by
  simp only [aeval_def, eval₂_map]
  change _ = endEHom A ℓ E (eval₂ (algebraMap ℤ A.End) α Z)
  rw [Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

/-- The `ℤ`-coordinates of the powers of `α` are `ℚ`-linearly independent below the degree of the
minimal polynomial of `1 ⊗ α ∈ End⁰(A)`. -/
theorem linIndep_coords (A : AbVar k) [Module.Free ℤ A.End] [Module.Finite ℤ A.End] (α : A.End) :
    LinearIndependent ℚ (fun (i : Fin (minpoly ℚ ((1 : ℚ) ⊗ₜ[ℤ] α : A.End0)).natDegree)
      (j : Module.Free.ChooseBasisIndex ℤ A.End) =>
        (((Module.Free.chooseBasis ℤ A.End).repr (α ^ (i : ℕ)) j : ℤ) : ℚ)) := by
  classical
  set b := Module.Free.chooseBasis ℤ A.End
  set x : A.End0 := (1 : ℚ) ⊗ₜ[ℤ] α
  set m := minpoly ℚ x
  refine Fintype.linearIndependent_iff.mpr fun q hq => ?_
  let Q : ℚ[X] := ∑ i : Fin m.natDegree, C (q i) * X ^ (i : ℕ)
  have hQx : aeval x Q = 0 := by
    apply (Algebra.TensorProduct.basis ℚ b).repr.injective
    ext j
    have := congrFun hq j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Q, map_sum, map_mul, aeval_C, aeval_X, x, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, LinearEquiv.map_zero,
      Finsupp.coe_zero, Pi.zero_apply]
    simpa [algebraMap_int_eq] using this
  intro i
  have hpos : 0 < m.natDegree := i.pos
  have hdeg : Q.natDegree < m.natDegree := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := m.natDegree - 1) ?_) ?_
    · intro i _
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_X_pow]; omega
    · omega
  have hQ0 : Q = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt (minpoly.dvd ℚ x hQx) hdeg
  have := congrArg (fun P : ℚ[X] => P.coeff i) hQ0
  simp only [Q, finset_sum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [if_neg (fun h => hj (Fin.ext h.symm)), mul_zero])
    (fun h => absurd (Finset.mem_univ i) h)] at this
  simpa using this

end AV

end CharpolyCharp

end
