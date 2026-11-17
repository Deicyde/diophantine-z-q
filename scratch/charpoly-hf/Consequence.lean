import ZInQKernel.OneProof.H.TailC
import ZInQKernel.Contrib.AVB1.AlgClosed

/-! # charpoly-hf: `common_trace` from the minimal polynomial of one endomorphism in characteristic `p`

Task charpoly-hf (2026-11-16), report `docs/research/charpoly-hf.md`.

charpoly-charp (`docs/research/charpoly-charp.md`) proved `HDec.G14Trace.common_trace` without T7 (Mumford §19
Thm 4) from Mumford §19 Thm 3 (`PkgI3.HomFreeFinite`) at the characteristic-`p` abelian variety `Ā` that
`FrobTraceLink` supplies. What that argument reads at `Ā` is exactly one fact about one endomorphism `α'`: the
polynomials over `ℚ_ℓ` that kill `V_ℓ(α')` are the multiples of one monic `m ∈ ℚ[X]`, the same for every
`ℓ ≠ p`. This file states that fact as `MinpolyIndepOfEllCharP` and re-proves `common_trace` and its two consumers
from it (and I3.M0, `PkgI3.TateModuleFree`).

* `ZInQ.Contrib.OneProof.CharpolyHF.MinpolyIndepOfEllCharP` (the statement);
* `minpoly_baseChange_iff`: the minimal polynomial of an endomorphism of a finite-dimensional space does not change
  under extension of scalars;
* `HDec.G14Trace.common_trace_of_minpolyCharP`, `HDec.G14Trace.g14TraceCompat_of_link_minpolyCharP`,
  `HDec.HSyn.G0AssembleMod.linkedTateData_of_local_minpolyCharP`.

The linear algebra of Part 1 is charpoly-charp's (`ZInQKernel/Contrib/OneProof/CommonTraceHomFree.lean` on
wip/charpoly-charp), copied verbatim into this namespace. No `sorry`, no `axiom`.
-/

open Polynomial Module

noncomputable section

namespace ZInQ.Contrib.OneProof.CharpolyHF

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




/-! ## Part 2: the statement, and extension of scalars -/

section Stmt

open CategoryTheory CategoryTheory.MonObj

/-- **Minimal polynomial of `V_ℓ(α)` independent of `ℓ`, characteristic `p` (charpoly-hf; the input that
charpoly-charp's reroute of `common_trace` reads at `FrobTraceLink`'s `Ā`).** For an abelian variety `A` over a
field `k` of characteristic `p > 0` and `α ∈ End(A)` there is one monic `m ∈ ℚ[X]` such that, for every prime
`ℓ ≠ p`, the polynomials `G ∈ ℚ_ℓ[X]` with `G(V_ℓ(α)) = 0` are exactly the multiples of `m`.

Source: a consequence of D. Mumford, *Abelian varieties* (1970), §19, Theorem 3 (UNVERIFIED locator):
`Hom(X, Y)` is free of finite rank and `ℤ_ℓ ⊗ Hom(X, Y) → Hom(T_ℓ X, T_ℓ Y)` is injective for `ℓ ≠ char k`; then
`m` is the minimal polynomial of `α` in `End⁰(A)` (`minpolyIndepOfEllCharP_of_homFree`, with I3.M0). Not the printed
form: Mumford states injectivity on all of `ℤ_ℓ ⊗ End(A)`; this is its restriction to `ℤ_ℓ ⊗ ℤ[α]`, phrased by
minimal polynomials, and only in characteristic `p`. -/
def MinpolyIndepOfEllCharP : Prop :=
  ∀ (k : Type) [Field k] (p : ℕ), p.Prime → CharP k p → ∀ (A : PkgI3.AbVar k) (α : PkgI3.AbVar.End A),
    ∃ m : ℚ[X], m.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ G : ℚ_[ℓ][X], aeval ((PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]) G = 0 ↔
        m.map (Rat.castHom ℚ_[ℓ]) ∣ G

end Stmt

/-! ## Part 3: `MinpolyIndepOfEllCharP` is a consequence of Mumford §19 Thm 3 -/

section AV

open PkgI3 TensorProduct CategoryTheory
open CategoryTheory.MonObj

variable {k : Type} [Field k]

/-- **Mumford §19 Thm 3 in characteristic `p` (printed form, restricted).** D. Mumford, *Abelian varieties* (1970),
§19, Theorem 3 (UNVERIFIED locator), for an algebraically closed field `k` of characteristic `p > 0`: `Hom(X, Y)` is
free of finite rank `≤ 4 dim X dim Y` and `ℤ_ℓ ⊗ Hom(X, Y) → Hom(T_ℓ X, T_ℓ Y)` is injective for `ℓ ≠ p`. This is
`ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` restricted to characteristic `p` (homfree-proof's
`HomFreeFiniteAlgClosedNoEmb` covers these fields and the huge fields of characteristic `0`). -/
def HomFreeFiniteAlgClosedCharP : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ), p.Prime → CharP k p → ∀ (A B : PkgI3.AbVar k),
    Module.Free ℤ (PkgI3.AbVar.Hom A B) ∧ Module.Finite ℤ (PkgI3.AbVar.Hom A B) ∧
      ((Module.finrank ℤ (PkgI3.AbVar.Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → Function.Injective (PkgI3.AbVar.tateHomZl ℓ A B)

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


/-- `End(A) → End_{ℚ_ℓ}(V_ℓ(A))` as a ring homomorphism. -/
def vHom (A : AbVar k) (ℓ : ℕ) [Fact ℓ.Prime] : A.End →+* Module.End ℚ_[ℓ] (A.V ℓ) where
  toFun φ := (AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]
  map_one' := by
    change (AbVar.homT (ℓ := ℓ) (1 : A.End)).baseChange ℚ_[ℓ] = 1
    rw [homT_one', LinearMap.baseChange_id]; rfl
  map_mul' φ ψ := by
    change (AbVar.homT (ℓ := ℓ) (φ * ψ)).baseChange ℚ_[ℓ] =
      (AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ] * (AbVar.homT (ℓ := ℓ) ψ).baseChange ℚ_[ℓ]
    rw [homT_mul', LinearMap.baseChange_comp]; rfl
  map_zero' := by
    change (AbVar.tateHom ℓ A A 0).baseChange ℚ_[ℓ] = 0
    rw [map_zero, LinearMap.baseChange_zero]
  map_add' φ ψ := by
    change (AbVar.tateHom ℓ A A (φ + ψ)).baseChange ℚ_[ℓ] =
      (AbVar.tateHom ℓ A A φ).baseChange ℚ_[ℓ] + (AbVar.tateHom ℓ A A ψ).baseChange ℚ_[ℓ]
    rw [map_add, LinearMap.baseChange_add]

theorem aeval_V_int (A : AbVar k) (ℓ : ℕ) [Fact ℓ.Prime] (α : A.End) (Z : ℤ[X]) :
    aeval ((AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]) (Z.map (Int.castRingHom ℚ_[ℓ])) =
      (AbVar.homT (ℓ := ℓ) (aeval α Z)).baseChange ℚ_[ℓ] := by
  simp only [aeval_def, eval₂_map]
  change _ = vHom A ℓ (eval₂ (algebraMap ℤ A.End) α Z)
  rw [Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

/-- **The minimal polynomial of `V_ℓ(α)` is that of `α` in `End⁰(A)`, for every `ℓ ≠ char k`**, from
`End(A)` free of finite rank, `ℤ_ℓ ⊗ End(A) ↪ End(T_ℓ A)` and I3.M0 (charpoly-charp's `exists_minpoly_endE` at
`E = ℚ_ℓ`, with the hypotheses at one abelian variety). -/
theorem exists_minpoly_V (hT : PkgI3.TateModuleFree) (A : AbVar k) (α : A.End)
    [Module.Free ℤ A.End] [Module.Finite ℤ A.End]
    (hinj : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → Function.Injective (AbVar.tateHomZl ℓ A A)) :
    ∃ m : ℚ[X], m.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ G : ℚ_[ℓ][X], aeval ((AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]) G = 0 ↔
        m.map (Rat.castHom ℚ_[ℓ]) ∣ G := by
  classical
  have hint : IsIntegral ℚ ((1 : ℚ) ⊗ₜ[ℤ] α : A.End0) := IsIntegral.of_finite ℚ _
  refine ⟨minpoly ℚ ((1 : ℚ) ⊗ₜ[ℤ] α : A.End0), minpoly.monic hint, fun ℓ _ hℓ G => ?_⟩
  set x : A.End0 := (1 : ℚ) ⊗ₜ[ℤ] α with hx
  set m := minpoly ℚ x with hm
  set b := Module.Free.chooseBasis ℤ A.End
  have hmon : m.Monic := minpoly.monic hint
  set S := (AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ] with hS
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
  -- (⇐): `m` kills `S`
  have hkill : aeval S (m.map (Rat.castHom ℚ_[ℓ])) = 0 := by
    obtain ⟨c, hc, hZ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) m
    set Z := IsLocalization.integerNormalization (nonZeroDivisors ℤ) m
    have hZ' : Z.map (Int.castRingHom ℚ) = C (c : ℚ) * m := by
      rw [← algebraMap_int_eq, hZ, ← algebraMap_smul ℚ c m, Polynomial.smul_eq_C_mul]
      rfl
    have hZx : aeval α Z = 0 := by
      apply hinc
      rw [← hev, hZ', map_mul, minpoly.aeval, mul_zero]
    have h2 := aeval_V_int A ℓ α Z
    rw [hZx] at h2
    have h3 : Z.map (Int.castRingHom ℚ_[ℓ]) = C (c : ℚ_[ℓ]) * m.map (Rat.castHom ℚ_[ℓ]) := by
      have := congrArg (Polynomial.map (Rat.castHom ℚ_[ℓ])) hZ'
      rw [Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C] at this
      rw [show (Rat.castHom ℚ_[ℓ]).comp (Int.castRingHom ℚ) = Int.castRingHom ℚ_[ℓ] from
        RingHom.ext_int _ _] at this
      rw [this]
      congr 2
    have h0 : (AbVar.homT (ℓ := ℓ) (0 : A.End)).baseChange ℚ_[ℓ] = 0 := map_zero (vHom A ℓ)
    rw [h0, h3, map_mul, aeval_C] at h2
    have hc0 : (c : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hc
    rw [← Algebra.smul_def] at h2
    rw [← inv_smul_smul₀ hc0 (aeval S (m.map (Rat.castHom ℚ_[ℓ]))), h2, smul_zero]
  -- (⇒): independence of the powers of `S` below `deg m`
  obtain ⟨hTf, hTfin, -⟩ := hT k A ℓ hℓ
  set gb := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  set βQ := Algebra.TensorProduct.basis ℚ_[ℓ] gb
  have hLI := Fintype.linearIndependent_iff.mp (matrix_pow_indep A α ℓ (hinj ℓ hℓ) gb)
  have hpow : ∀ i : ℕ, S ^ i = (AbVar.homT (ℓ := ℓ) (α ^ i)).baseChange ℚ_[ℓ] :=
    fun i => (map_pow (vHom A ℓ) α i).symm
  have hmat : ∀ (φ : A.End) (p : Module.Free.ChooseBasisIndex ℤ_[ℓ] (A.T ℓ) ×
      Module.Free.ChooseBasisIndex ℤ_[ℓ] (A.T ℓ)),
      LinearMap.toMatrix βQ βQ ((AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]) p.1 p.2 =
        ((LinearMap.toMatrix gb gb (AbVar.homT (ℓ := ℓ) φ) p.1 p.2 : ℤ_[ℓ]) : ℚ_[ℓ]) := by
    intro φ p
    rw [LinearMap.toMatrix_baseChange, Matrix.map_apply]
    rfl
  constructor
  · intro hG
    by_cases h1 : m.map (Rat.castHom ℚ_[ℓ]) = 1
    · rw [h1]; exact one_dvd _
    rw [← modByMonic_eq_zero_iff_dvd (hmon.map _)]
    set R := G %ₘ m.map (Rat.castHom ℚ_[ℓ]) with hRdef
    have hRdeg : R.natDegree < m.natDegree := by
      have := natDegree_modByMonic_lt G (hmon.map (Rat.castHom ℚ_[ℓ])) h1
      rwa [natDegree_map_eq_of_injective (Rat.castHom ℚ_[ℓ]).injective] at this
    have hR : aeval S R = 0 := by
      have h2 := congrArg (aeval S) (modByMonic_add_div G (m.map (Rat.castHom ℚ_[ℓ])))
      rw [map_add, map_mul, hkill, zero_mul, add_zero, hG] at h2
      exact h2
    rw [aeval_eq_sum_range' hRdeg, Finset.sum_range] at hR
    simp only [hpow] at hR
    have hcoef : ∀ i : Fin m.natDegree, R.coeff i = 0 := by
      apply hLI (fun i => R.coeff i)
      funext p
      have := congrArg (fun f => LinearMap.toMatrix βQ βQ f p.1 p.2) hR
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

/-- **`MinpolyIndepOfEllCharP` from Mumford §19 Thm 3 in characteristic `p` and I3.M0.** -/
theorem minpolyIndepOfEllCharP_of_homFree (hH : HomFreeFiniteAlgClosedCharP) (hT : PkgI3.TateModuleFree) :
    MinpolyIndepOfEllCharP := by
  intro k _ p hp hk A α
  have : CharP k p := hk
  haveI : CharP (AlgebraicClosure k) p :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  obtain ⟨hfree, hfin, -, hinj⟩ := hH (AlgebraicClosure k) p hp inferInstance
    (A.baseChange (AlgebraicClosure k)) (A.baseChange (AlgebraicClosure k))
  set e := (ZInQ.Contrib.AVB1.bcHom (AlgebraicClosure k) A A).toIntLinearMap with he_def
  have he : Function.Injective e := ZInQ.Contrib.AVB1.bcHom_injective A A
  haveI : Module.Finite ℤ (PkgI3.AbVar.Hom A A) := Module.Finite.of_injective e he
  haveI : Module.IsTorsionFree ℤ (PkgI3.AbVar.Hom A A) :=
    Function.Injective.moduleIsTorsionFree e he (fun r m => map_zsmul e r m)
  haveI : Module.Free ℤ (PkgI3.AbVar.End A) := inferInstanceAs (Module.Free ℤ (PkgI3.AbVar.Hom A A))
  refine exists_minpoly_V hT A α fun ℓ _ hℓ => ?_
  haveI := ZInQ.Contrib.AVB1.flat_int_padicInt ℓ
  have hinjL := hinj ℓ (ZInQ.Contrib.AVB1.natCast_ne_zero_closure hℓ)
  have hlt : Function.Injective (LinearMap.lTensor ℤ_[ℓ] e) :=
    Module.Flat.lTensor_preserves_injective_linearMap e he
  rw [← LinearMap.ker_eq_bot (f := PkgI3.AbVar.tateHomZl ℓ A A), LinearMap.ker_eq_bot']
  intro x hx
  apply hlt
  rw [map_zero]
  apply hinjL
  rw [map_zero]
  apply LinearMap.ext
  intro t'
  obtain ⟨t, rfl⟩ := (ZInQ.Contrib.AVB1.tateBC_bijective_closure A ℓ).2 t'
  rw [he_def, ZInQ.Contrib.AVB1.tateHomZl_bc, hx, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

end AV

end ZInQ.Contrib.OneProof.CharpolyHF
