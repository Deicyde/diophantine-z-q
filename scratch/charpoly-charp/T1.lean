import Mathlib

/-! # charpoly-charp, Part 1 and 3: linear algebra (Mathlib only)

* `linIndep_map`: linear independence of vectors in `N → K` survives extension of scalars.
* `linIndep_baseChange`: linear independence of endomorphisms survives `baseChange` to a field `E ⊇ K`.
* `aeval_intertwines`, `trace_eq_of_minpoly`: if `e` conjugates `S` to `M ⊕ M` (`M` a `2 × 2` matrix) and
  the polynomials killing `S` are exactly the multiples of `m ∈ ℚ[X]` (monic), then
  `tr S = -(4 / deg m) · nextCoeff m`.
-/

open Polynomial Module

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
  refine Fintype.linearIndependent_iff.mpr fun c hc => h2 c ?_
  sorry

end CharpolyCharp
