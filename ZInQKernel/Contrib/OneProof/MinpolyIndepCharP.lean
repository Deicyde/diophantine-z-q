import ZInQKernel.OneProof.H.TailC

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

section AV

open CategoryTheory CategoryTheory.MonObj

/-- **`MinpolyIndepOfEllCharP` on `E ⊗ V_ℓ(Ā)`** (the form charpoly-charp's trace computation reads). -/
theorem exists_minpoly_endE_charP (hM : MinpolyIndepOfEllCharP) (hT : PkgI3.TateModuleFree)
    {k : Type} [Field k] {p : ℕ} (hp : p.Prime) [CharP k p] (A : PkgI3.AbVar k)
    (α : PkgI3.AbVar.End A) :
    ∃ m : ℚ[X], m.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (E : Type) [Field E] [CharZero E] [Algebra ℚ_[ℓ] E] (G : E[X]),
        aeval (GlueC10Link.endE α ℓ E) G = 0 ↔ m.map (Rat.castHom E) ∣ G := by
  obtain ⟨m, hmon, hm⟩ := hM k p hp inferInstance A α
  refine ⟨m, hmon, fun ℓ _ hℓ E _ _ _ G => ?_⟩
  obtain ⟨hTf, hTfin, -⟩ := hT k A ℓ hℓ
  have hmap : m.map (Rat.castHom E) = (m.map (Rat.castHom ℚ_[ℓ])).map (algebraMap ℚ_[ℓ] E) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  rw [hmap]
  exact minpoly_baseChange_iff (E := E) _ _ (hmon.map _) (hm ℓ hℓ) G

end AV

end ZInQ.Contrib.OneProof.CharpolyHF


/-! ## Part 3: `common_trace` from `MinpolyIndepOfEllCharP` (no T7, no T6) -/

namespace HDec.G14Trace

open _root_.PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisRep)
open _root_.PkgI3 G0ModNewform _root_.GlueC10Link
open Polynomial

/-- **The trace of `r_ℓ(τ)` from the minimal polynomial of `α`.** -/
theorem trace_r_of_minpolyQ {ℓ : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [NumberField K]
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
  have htr := _root_.ZInQ.Contrib.OneProof.CharpolyHF.trace_eq_of_minpoly S e M' hS m hmon hmS
  rw [map_smul, smul_eq_mul] at htr
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hTr : LinearMap.trace E _ (Tm τ) = (t : E) / N := by
    rw [eq_div_iff hNE, mul_comm, htr]
  rw [hTr] at h2
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_ratCast, map_natCast, map_ofNat]
  linear_combination (-1 / 2 : E) * h2


/-- **The common trace from `MinpolyIndepOfEllCharP`** (`common_trace` with `hM` replaced by
`MinpolyIndepOfEllCharP` and I3.M0; the proof is charpoly-charp's `common_trace_of_homFree`). -/
theorem common_trace_of_minpolyCharP (hM : _root_.ZInQ.Contrib.OneProof.CharpolyHF.MinpolyIndepOfEllCharP)
    (hT : PkgI3.TateModuleFree)
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
  obtain ⟨m, hmon, hm⟩ :=
    _root_.ZInQ.Contrib.OneProof.CharpolyHF.exists_minpoly_endE_charP hM hT hp Ab α
  exact ⟨_, trace_r_of_minpolyQ A j5 a β Tm5 r5 e5 he5 Ab α N hN τ hc5 m hmon (hm 5 hk5 _),
    trace_r_of_minpolyQ A j3 a β Tm3 r3 e3 he3 Ab α N hN τ hc3 m hmon (hm 3 hk3 _)⟩

/-- `g14TraceCompat_of_link` with `hM` replaced by `MinpolyIndepOfEllCharP` and I3.M0. -/
theorem g14TraceCompat_of_link_minpolyCharP
    (hM : _root_.ZInQ.Contrib.OneProof.CharpolyHF.MinpolyIndepOfEllCharP) (hT : PkgI3.TateModuleFree)
    {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (γ : Qbar →ₐ[ℚ] Qbar) (hι5 : D.ι5 = j5.comp γ)
    (hι3 : D.ι3 = j3.comp γ) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3))
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) D.r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) D.r3)
    (hF : FrobTraceLink A Tm5 Tm3) : G14TraceCompat D :=
  g14TraceCompat_of_common D j5 j3 γ hι5 hι3
    (common_trace_of_minpolyCharP hM hT A j5 j3 a β Tm5 Tm3 D.r5 D.r3 h5 h3 hF)

end HDec.G14Trace

namespace HDec.HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **`LinkedTateData` from `LinkedTateLocal` without T7** (`linkedTateData_of_local` with `hM` replaced by
`MinpolyIndepOfEllCharP` and I3.M0; the proof is the original's, with `g14TraceCompat_of_link_minpolyCharP`). -/
theorem linkedTateData_of_local_minpolyCharP
    (hM : _root_.ZInQ.Contrib.OneProof.CharpolyHF.MinpolyIndepOfEllCharP)
    (hT : _root_.PkgI3.TateModuleFree) (h : LinkedTateLocal) : LinkedTateData := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  have h' := h Y Φ π u P hctx L A ε N χ β L' hLL' hD
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h5, h3, hF, hloc⟩ := h'
  refine ⟨Tm₅, c₅, ε₅, _, _, u₅, Tm₃, c₃, ε₃, _, _, u₃, h5, h3,
    fun r₅ r₃ h8₅ h8₃ i ιC ι5 => ?_⟩
  obtain ⟨γ, hγ⟩ := G14Trace.exists_comp_eq ι5 j5
  obtain ⟨hl5, hl3⟩ := hloc r₅ r₃ h8₅ h8₃
  exact ⟨j3.comp γ,
    G14Trace.g14TraceCompat_of_link_minpolyCharP hM hT ⟨i, ιC, ι5, j3.comp γ, r₅, r₃⟩ j5 j3 γ hγ rfl aQ βQ
      Tm₅ Tm₃ h8₅ h8₃ hF,
    G15Ram.g15RamWild_of_localData _ hl5 hl3⟩

end HDec.HSyn.G0AssembleMod

end
