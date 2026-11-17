import ZInQKernel.OneProof.H.TailC

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

/-- **ℤ_ℓ-independence of `T_ℓ(α^i)`** below the degree of the minimal polynomial (homFree). -/
theorem homT_pow_indep (A : AbVar k) [Module.Free ℤ A.End] [Module.Finite ℤ A.End] (α : A.End)
    (ℓ : ℕ) [Fact ℓ.Prime] (hinj : Function.Injective (AbVar.tateHomZl ℓ A A))
    (c : Fin (minpoly ℚ ((1 : ℚ) ⊗ₜ[ℤ] α : A.End0)).natDegree → ℤ_[ℓ])
    (hc : ∑ i, c i • AbVar.homT (ℓ := ℓ) (α ^ (i : ℕ)) = 0) : c = 0 := by
  classical
  set b := Module.Free.chooseBasis ℤ A.End
  have h0 : (∑ i, c i ⊗ₜ[ℤ] (α ^ (i : ℕ)) : TensorProduct ℤ ℤ_[ℓ] A.End) = 0 := by
    apply (map_eq_zero_iff _ hinj).mp
    rw [map_sum]
    exact hc
  have h1 : ∀ j, ∑ i, c i * (((b.repr (α ^ (i : ℕ)) j : ℤ) : ℤ_[ℓ])) = 0 := by
    intro j
    have := congrArg (fun t => (Algebra.TensorProduct.basis ℤ_[ℓ] b).repr t j) h0
    simpa [Algebra.TensorProduct.basis_repr_tmul, Finsupp.coe_finsetSum, Finset.sum_apply,
      algebraMap_int_eq] using this
  have hq := Fintype.linearIndependent_iff.mp
    (linIndep_map (K := ℚ) (E := ℚ_[ℓ]) (linIndep_coords A α))
  funext i
  have h2 := hq (fun i => (c i : ℚ_[ℓ])) (by
    funext j
    have := congrArg (fun z : ℤ_[ℓ] => (z : ℚ_[ℓ])) (h1 j)
    simp only [PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_intCast, PadicInt.coe_zero] at this
    simpa [Finset.sum_apply, mul_comm] using this) i
  simpa using h2

/-- **ℚ_ℓ-independence of the matrices of `T_ℓ(α^i)`** (clearing denominators). -/
theorem matrix_pow_indep (A : AbVar k) [Module.Free ℤ A.End] [Module.Finite ℤ A.End] (α : A.End)
    (ℓ : ℕ) [Fact ℓ.Prime] (hinj : Function.Injective (AbVar.tateHomZl ℓ A A))
    {Ix : Type} [Fintype Ix] [DecidableEq Ix] (gb : Module.Basis Ix ℤ_[ℓ] (A.T ℓ)) :
    LinearIndependent ℚ_[ℓ] (fun (i : Fin (minpoly ℚ ((1 : ℚ) ⊗ₜ[ℤ] α : A.End0)).natDegree)
      (p : Ix × Ix) => ((LinearMap.toMatrix gb gb (AbVar.homT (ℓ := ℓ) (α ^ (i : ℕ))) p.1 p.2 : ℤ_[ℓ]) :
        ℚ_[ℓ])) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
  obtain ⟨⟨bb, hbb⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ_[ℓ]) c
  choose c' hc' using hb
  -- hc' i : algebraMap ℤ_[ℓ] ℚ_[ℓ] (c' i) = bb • c i
  have hc'' : ∀ i, ((c' i : ℤ_[ℓ]) : ℚ_[ℓ]) = (bb : ℚ_[ℓ]) * c i := by
    intro i
    have := hc' i
    simpa [Algebra.smul_def] using this
  have hsum : ∑ i, c' i • AbVar.homT (ℓ := ℓ) (α ^ (i : ℕ)) = 0 := by
    apply (LinearMap.toMatrix gb gb).injective
    rw [map_zero, map_sum]
    apply Matrix.ext
    intro a a'
    have := congrFun hc (a, a')
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    apply Subtype.ext
    simp only [PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_zero, hc'']
    simp only [_root_.mul_assoc, ← Finset.mul_sum, this, mul_zero]
  have h0 := homT_pow_indep A α ℓ hinj c' hsum
  intro i
  have h1 := hc' i
  rw [h0, Pi.zero_apply, map_zero, Algebra.smul_def] at h1
  have hbne : algebraMap ℤ_[ℓ] ℚ_[ℓ] bb ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbb
  exact (mul_eq_zero.mp h1.symm).resolve_left hbne

/-- **The minimal polynomial of `endE α` is one `m ∈ ℚ[X]` for every `ℓ ≠ char k`** (Mumford §19
Thm 3 and I3.M0 only). -/
theorem exists_minpoly_endE (hH : PkgI3.HomFreeFinite) (hT : PkgI3.TateModuleFree)
    (A : AbVar k) (α : A.End) :
    ∃ m : ℚ[X], m.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (E : Type) [Field E] [CharZero E] [Algebra ℚ_[ℓ] E] (G : E[X]),
        aeval (GlueC10Link.endE α ℓ E) G = 0 ↔ m.map (Rat.castHom E) ∣ G := by
  classical
  obtain ⟨hfree, hfin, -, hinj⟩ := hH k A A
  have hint : IsIntegral ℚ ((1 : ℚ) ⊗ₜ[ℤ] α : A.End0) := IsIntegral.of_finite ℚ _
  refine ⟨minpoly ℚ ((1 : ℚ) ⊗ₜ[ℤ] α : A.End0), minpoly.monic hint,
    fun ℓ _ hℓ E _ _ _ G => ?_⟩
  set x : A.End0 := (1 : ℚ) ⊗ₜ[ℤ] α with hx
  set m := minpoly ℚ x with hm
  set b := Module.Free.chooseBasis ℤ A.End
  have hmon : m.Monic := minpoly.monic hint
  -- injectivity of `End → End⁰`
  have hinc : ∀ y : A.End, (1 : ℚ) ⊗ₜ[ℤ] y = 0 → y = 0 := by
    intro y hy
    have := congrArg (Algebra.TensorProduct.basis ℚ b).repr hy
    rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, map_zero] at this
    apply b.repr.injective
    rw [map_zero]
    refine Finsupp.ext fun j => ?_
    have hj := congrArg (fun f => f j) this
    simpa [algebraMap_int_eq] using hj
  have hev : ∀ Z : ℤ[X], aeval x (Z.map (Int.castRingHom ℚ)) = (1 : ℚ) ⊗ₜ[ℤ] aeval α Z := by
    intro Z
    simp only [aeval_def, eval₂_map]
    change _ = (Algebra.TensorProduct.includeRight.toRingHom : A.End →+* A.End0)
      (eval₂ (algebraMap ℤ A.End) α Z)
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  -- (⇐): `m` kills `endE α`
  have hkill : aeval (GlueC10Link.endE α ℓ E) (m.map (Rat.castHom E)) = 0 := by
    obtain ⟨c, hc, hZ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) m
    set Z := IsLocalization.integerNormalization (nonZeroDivisors ℤ) m
    have hZ' : Z.map (Int.castRingHom ℚ) = C (c : ℚ) * m := by
      rw [← algebraMap_int_eq, hZ, ← algebraMap_smul ℚ c m, Polynomial.smul_eq_C_mul]
      rfl
    have hZx : aeval α Z = 0 := by
      apply hinc
      rw [← hev, hZ', map_mul, minpoly.aeval, mul_zero]
    have h2 := aeval_endE_int A ℓ E α Z
    rw [hZx] at h2
    have h3 : Z.map (Int.castRingHom E) = C (c : E) * m.map (Rat.castHom E) := by
      have := congrArg (Polynomial.map (Rat.castHom E)) hZ'
      rw [Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C] at this
      rw [show (Rat.castHom E).comp (Int.castRingHom ℚ) = Int.castRingHom E from
        RingHom.ext_int _ _] at this
      rw [this]
      congr 2
      simp
    have h0 : GlueC10Link.endE (0 : A.End) ℓ E = 0 := map_zero (endEHom A ℓ E)
    rw [h0, h3, map_mul, aeval_C] at h2
    have hc0 : (c : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hc
    rw [← Algebra.smul_def] at h2
    rw [← inv_smul_smul₀ hc0 (aeval (GlueC10Link.endE α ℓ E) (m.map (Rat.castHom E))), h2,
      smul_zero]
  -- (⇒): independence of the powers of `endE α` below `deg m`
  obtain ⟨hTf, hTfin, -⟩ := hT k A ℓ hℓ
  set gb := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  set βQ := Algebra.TensorProduct.basis ℚ_[ℓ] gb
  set βE := Algebra.TensorProduct.basis E βQ
  have hLI := Fintype.linearIndependent_iff.mp
    (linIndep_map (K := ℚ_[ℓ]) (E := E) (matrix_pow_indep A α ℓ (hinj ℓ hℓ) gb))
  have hpow : ∀ i : ℕ, (GlueC10Link.endE α ℓ E) ^ i = GlueC10Link.endE (α ^ i) ℓ E :=
    fun i => (map_pow (endEHom A ℓ E) α i).symm
  have hmat : ∀ (φ : A.End) (p : Module.Free.ChooseBasisIndex ℤ_[ℓ] (A.T ℓ) ×
      Module.Free.ChooseBasisIndex ℤ_[ℓ] (A.T ℓ)),
      LinearMap.toMatrix βE βE (GlueC10Link.endE φ ℓ E) p.1 p.2 =
        algebraMap ℚ_[ℓ] E ((LinearMap.toMatrix gb gb (AbVar.homT (ℓ := ℓ) φ) p.1 p.2 : ℤ_[ℓ]) :
          ℚ_[ℓ]) := by
    intro φ p
    change LinearMap.toMatrix βE βE (((AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange E)
      p.1 p.2 = _
    rw [LinearMap.toMatrix_baseChange, Matrix.map_apply, LinearMap.toMatrix_baseChange,
      Matrix.map_apply]
    rfl
  constructor
  · intro hG
    by_cases h1 : m.map (Rat.castHom E) = 1
    · rw [h1]; exact one_dvd _
    rw [← modByMonic_eq_zero_iff_dvd (hmon.map _)]
    set R := G %ₘ m.map (Rat.castHom E) with hRdef
    have hRdeg : R.natDegree < m.natDegree := by
      have := natDegree_modByMonic_lt G (hmon.map (Rat.castHom E)) h1
      rwa [natDegree_map_eq_of_injective (Rat.castHom E).injective] at this
    have hR : aeval (GlueC10Link.endE α ℓ E) R = 0 := by
      have h2 := congrArg (aeval (GlueC10Link.endE α ℓ E))
        (modByMonic_add_div G (m.map (Rat.castHom E)))
      rw [map_add, map_mul, hkill, zero_mul, add_zero, hG] at h2
      exact h2
    rw [aeval_eq_sum_range' hRdeg, Finset.sum_range] at hR
    simp only [hpow] at hR
    have hcoef : ∀ i : Fin m.natDegree, R.coeff i = 0 := by
      apply hLI (fun i => R.coeff i)
      funext p
      have := congrArg (fun f => LinearMap.toMatrix βE βE f p.1 p.2) hR
      simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hmat,
        map_zero, Matrix.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact this
    ext i
    by_cases hi : i < m.natDegree
    · exact hcoef ⟨i, hi⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_zero]
  · rintro ⟨q, rfl⟩
    rw [map_mul, hkill, zero_mul]

end AV

end CharpolyCharp


/-! ## Part 4: `common_trace` from homFree (no T7) -/

namespace HDec.G14Trace

open _root_.PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisRep)
open _root_.PkgI3 G0ModNewform _root_.GlueC10Link
open Polynomial

/-- **The trace of `r_ℓ(τ)` from the minimal polynomial of `α`.** -/
theorem trace_r_of_minpoly {ℓ : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (a β : GQ → Qbar)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ)) (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (he : Intertwines (GlueDescent.rho Tm (fun g => j (a g)) (fun g => j (β g))) r.mat e)
    {k : Type} [Field k] (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab) (N : ℕ) (hN : N ≠ 0)
    (τ : GQ) (hc : FrobCompare ℓ (Tm τ) α N) (m : ℚ[X]) (hmon : m.Monic)
    (hm : ∀ G : (PadicAlgCl ℓ)[X], aeval (endE α ℓ (PadicAlgCl ℓ)) G = 0 ↔
      m.map (Rat.castHom (PadicAlgCl ℓ)) ∣ G) :
    (r.mat τ).trace =
      j ((β τ)⁻¹ * a τ * (((-(4 / m.natDegree) * m.nextCoeff : ℚ) : Qbar) / N) / 2) := by
  set t : ℚ := -(4 / m.natDegree) * m.nextCoeff
  have h2 := trace_of_intertwines _ r.mat e he τ
  rw [GlueC10Link.trace_rho] at h2
  by_cases hdeg : a τ = 0 ∨ β τ = 0
  · have h0 : (β τ)⁻¹ * a τ = 0 := by
      rcases hdeg with h | h <;> simp [h]
    have hj0 : (j (β τ))⁻¹ * j (a τ) = 0 := by
      rw [← map_inv₀, ← map_mul, h0, map_zero]
    rw [hj0, zero_mul] at h2
    rw [h0, zero_mul, zero_div, map_zero]
    have : (2 : PadicAlgCl ℓ) ≠ 0 := two_ne_zero
    exact (mul_eq_zero.mp h2.symm).resolve_left this
  push Not at hdeg
  obtain ⟨ha, hb⟩ := hdeg
  have hja : j (a τ) ≠ 0 := (map_ne_zero j).mpr ha
  have hjb : j (β τ) ≠ 0 := (map_ne_zero j).mpr hb
  set E := PadicAlgCl ℓ
  -- `S = N • Tm τ` is conjugate to `M' ⊕ M'`
  set S : Module.End E (Vb A ℓ) := (N : E) • Tm τ
  set M' : Matrix (Fin 2) (Fin 2) E := ((N : E) * (j (a τ))⁻¹ * j (β τ)) • r.mat τ
  have hS : ∀ v, e (S v) = (M'.mulVec (e v).1, M'.mulVec (e v).2) := by
    intro v
    have hTm : Tm τ = ((j (a τ))⁻¹ * j (β τ)) •
        GlueDescent.rho Tm (fun g => j (a g)) (fun g => j (β g)) τ := by
      simp only [GlueDescent.rho, smul_smul]
      rw [show (j (a τ))⁻¹ * j (β τ) * ((j (β τ))⁻¹ * j (a τ)) = 1 by field_simp, one_smul]
    simp only [S, M', LinearMap.smul_apply, map_smul]
    rw [hTm, LinearMap.smul_apply, map_smul, he τ v]
    simp only [Prod.smul_mk, Matrix.smul_mulVec, smul_smul, mul_assoc]
  obtain ⟨Φ, hΦ⟩ := hc
  have hmS : ∀ G : E[X], aeval S G = 0 ↔ m.map (Rat.castHom E) ∣ G := by
    intro G
    rw [← hm G, ← hΦ]
    have hconj : ∀ f : Module.End E (Vb A ℓ), Φ.conj f = Φ.conjAlgEquiv E f := fun f => rfl
    have h1 := Polynomial.aeval_algHom_apply (Φ.conjAlgEquiv E).toAlgHom S G
    rw [hconj]
    change aeval S G = 0 ↔ aeval ((Φ.conjAlgEquiv E).toAlgHom S) G = 0
    rw [h1]
    exact (map_eq_zero_iff (Φ.conjAlgEquiv E).toAlgHom (Φ.conjAlgEquiv E).injective).symm
  have htr := CharpolyCharp.trace_eq_of_minpoly S e M' hS m hmon hmS
  rw [map_smul, smul_eq_mul] at htr
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hTr : LinearMap.trace E _ (Tm τ) = (t : E) / N := by
    rw [eq_div_iff hNE, mul_comm, htr]
  rw [hTr] at h2
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_ratCast, map_natCast, map_ofNat]
  linear_combination (-1 / 2 : E) * h2

/-- **The common trace without T7** (`common_trace` with `hM` replaced by Mumford §19 Thm 3 and I3.M0). -/
theorem common_trace_of_homFree (hH : PkgI3.HomFreeFinite) (hT : PkgI3.TateModuleFree)
    {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2)
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3)
    (hF : FrobTraceLink A Tm5 Tm3) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (r5.mat τ).trace = j5 x ∧ (r3.mat τ).trace = j3 x := by
  obtain ⟨S, hS⟩ := hF
  obtain ⟨-, e5, he5, -⟩ := h5
  obtain ⟨-, e3, he3, -⟩ := h3
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hp3 : p ≠ 3 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  have hp5 : p ≠ 5 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  obtain ⟨k, _, hk, Ab, α, N, hN, hc3, hc5⟩ := hS p hp hpS1 v τ hv hτ
  have hk3 : ((3 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp Nat.prime_three hp3
  have hk5 : ((5 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp (by norm_num) hp5
  obtain ⟨m, hmon, hm⟩ := CharpolyCharp.exists_minpoly_endE hH hT Ab α
  exact ⟨_, trace_r_of_minpoly A j5 a β Tm5 r5 e5 he5 Ab α N hN τ hc5 m hmon (hm 5 hk5 _),
    trace_r_of_minpoly A j3 a β Tm3 r3 e3 he3 Ab α N hN τ hc3 m hmon (hm 3 hk3 _)⟩

end HDec.G14Trace

end

#print axioms HDec.G14Trace.common_trace_of_homFree
