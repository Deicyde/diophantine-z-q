import ZInQKernel.HDecomp.LeafPush2.T

/-! # conj-twist: `ConjTwistNontrivial` and `ConjTwistFromLeaves` (glue step G10 core)

Check with `lake env lean scratch/conj-twist/ConjTwist.lean` (after
`lake build ZInQKernel.HDecomp.LeafPush2.T`).

* §1 copies **verbatim** from `scratch/g10-odd/G10Odd.lean`: `ConjTwistNontrivial`,
  `ConjTwistFromLeaves` and what they and the proofs below depend on (`resQ`, `qEmbRing`,
  `resQ_spec`, `isComplexConj_mul_self`, `qEmbRing_bijective`, `range_stable`, and the proved
  linear algebra `betti_skeleton_fd` with its lemmas).
* §2 proves the `ℚ_ℓ`-form of Faltings' theorem needed here (`faltingsV`): a `G_K`-equivariant
  map `V_ℓ(A) → V_ℓ(B)` lies in the `ℚ_ℓ`-span of `{V_ℓ(f) : f ∈ Hom(A, B)}`.
* §3 moves the complex conjugation `c ∈ G_ℚ` to an automorphism `cc` of `K̄` (`conjData`).
* §4 states the remaining glue `ConjBettiData` and proves `ConjTwistNontrivial` from
  `TateModuleFree` (leaf T26) and `ConjBettiData`, and `ConjTwistFromLeaves` from `ConjBettiData`.
-/

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj

/-! ## §1. Verbatim copies from `scratch/g10-odd/G10Odd.lean` -/

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- A complex conjugation is an involution. -/
theorem isComplexConj_mul_self {c : PkgI4.GQ} (hc : PkgI4.IsComplexConj c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  apply AlgEquiv.ext; intro x
  apply j.toRingHom.injective
  change j (c (c x)) = j x
  rw [hj, hj, Complex.conj_conj]

/-- `v ↦ 1 ⊗ v` is injective for a field extension (flatness of vector spaces). -/
theorem one_tmul_injective (k E V : Type*) [Field k] [Field E] [Algebra k E] [AddCommGroup V]
    [Module k V] : Function.Injective (fun v : V => (1 : E) ⊗ₜ[k] v) := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := V)
    (Algebra.linearMap k E) (algebraMap k E).injective
  intro x y hxy
  apply (TensorProduct.lid k V).symm.injective
  apply hinj
  simpa using hxy

/-- Base change along a field extension is injective on linear maps. -/
theorem baseChange_injective' (k E V : Type*) [Field k] [Field E] [Algebra k E] [AddCommGroup V]
    [Module k V] {f g : V →ₗ[k] V} (h : f.baseChange E = g.baseChange E) : f = g := by
  ext v
  apply one_tmul_injective k E V
  have := LinearMap.congr_fun h ((1 : E) ⊗ₜ[k] v)
  simpa using this

/-- **G10 core: complex conjugation twists the Tate representation of `G_K` nontrivially (GLUE,
unproved; STANDARD).** For a number field `K` Galois over `ℚ`, an abelian surface `A/K`, a prime
`ℓ` and a complex conjugation `c ∈ G_ℚ`, it is not the case that `ρ_ℓ(τ) = ρ_ℓ(σ)` on `V_ℓ(A)`
whenever `τ, σ ∈ G_K` satisfy `τ = c σ c⁻¹` in `G_ℚ` (`resQ`).

Proof (STANDARD; N5 L742-751, h-trust C5): suppose it is. Let `ι : ℚ̄ → ℂ` realize `c`, `c̄ = c|_K`
(`K` normal), `A^c = A ⊗_{K,c̄} K`. The `c`-semilinear bijection `A(K̄) → A^c(K̄)` gives
`c_* : V_ℓ(A) → V_ℓ(A^c)` with `c_* ρ_A(σ) = ρ_{A^c}(cσc⁻¹) c_*`; by the assumption `c_*` is
`G_K`-equivariant, so by Faltings (`PkgI3.FaltingsTate`, R9b) `c_* ∈ Hom(A, A^c) ⊗ ℚ_ℓ`. By the
Artin comparison at `ι` (T12, through the uniformization T35 and T5), `c_* = F_* ⊗ 1` for the
antiholomorphic `F : A(ℂ) → A^c(ℂ)`, `F_* : H₁(A(ℂ),ℚ) → H₁(A^c(ℂ),ℚ)` `ℚ`-rational; since
`(W ⊗ ℚ_ℓ) ∩ Hom_ℚ(H, H') = W` for the `ℚ`-subspace `W = Hom(A, A^c) ⊗ ℚ`, `F_* ∈ W`, so `F_*` is
`ℂ`-linear by T11 (`F_* J = J' F_*`) and `ℂ`-antilinear (`F_* J = −J' F_*`), hence `F_* = 0`,
contradicting `F_*` bijective and `H ≠ 0` (`dim A = 2`). The case `c ∈ G_K` (`c̄ = id`,
`A^c = A`) is the same with `c_* = ρ_A(c)`. -/
def ConjTwistNontrivial : Prop :=
  PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime], A.dim = 2 → ∀ c : PkgI4.GQ, PkgI4.IsComplexConj c →
    ¬ ∀ σ τ : Field.absoluteGaloisGroup K, resQ K τ = c * resQ K σ * c⁻¹ →
      A.galRep ℓ τ = A.galRep ℓ σ

open ZInQ.LeafPush2 in
/-- **G10 core from the leaves (GLUE, unproved; STANDARD).** `ConjTwistNontrivial` with T11(a),
T11(b), T35, T5 and T26 available: the leaves its proof (docstring of `ConjTwistNontrivial`, §6)
uses besides Faltings. The remaining work is glue: the conjugate variety `A^c`, the Artin
comparison `T_ℓ(A) ≅ Λ ⊗ ℤ_ℓ` at `ι` (from T35 and T5, as for `T12_ComplexConjEigen`) compatible
with `c_*` and `F_*`, and the instantiation of `betti_skeleton`. -/
def ConjTwistFromLeaves : Prop :=
  T11a_RiemannEnd → T11b_Rigidity → UniformizationExists → PkgI2.TorsionStructure.{0} →
  PkgI3.TateModuleFree → ConjTwistNontrivial

/-- Base change along a field extension is injective on linear maps `V → V'`. -/
theorem baseChange_injective₂ (k E V V' : Type*) [Field k] [Field E] [Algebra k E]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V'] {f g : V →ₗ[k] V'}
    (h : f.baseChange E = g.baseChange E) : f = g := by
  ext v
  apply one_tmul_injective k E V'
  have := LinearMap.congr_fun h ((1 : E) ⊗ₜ[k] v)
  simpa using this

/-- A map that is both linear and antilinear for complex structures (`J'` injective) is `0`. -/
theorem eq_zero_of_holo_of_antiholo {R M N : Type*} [Field R] [CharZero R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (J : M →ₗ[R] M) (J' : N →ₗ[R] N)
    (hJ' : Function.Injective J') (F : M →ₗ[R] N) (h1 : F ∘ₗ J = J' ∘ₗ F)
    (h2 : F ∘ₗ J = -(J' ∘ₗ F)) : F = 0 := by
  ext m
  have a := LinearMap.congr_fun h1 m
  have b := LinearMap.congr_fun h2 m
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.neg_apply] at a b
  have h3 : (2 : R) • J' (F m) = 0 := by
    rw [two_smul]
    have : J' (F m) = -J' (F m) := a.symm.trans b
    nth_rewrite 1 [this]; exact neg_add_cancel _
  have h4 : J' (F m) = J' 0 := by
    rw [map_zero]; exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  simpa using hJ' h4

/-- **Rationality for matrices (proved).** If `X.map (algebraMap k E)` lies in the `E`-span of
`W.map`, then `X ∈ W`. -/
theorem matrix_mem_of_map_mem_span {k E m n : Type*} [Field k] [Field E] [Algebra k E]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Submodule k (Matrix m n k))
    (X : Matrix m n k)
    (h : X.map (algebraMap k E) ∈
      Submodule.span E ((fun Y : Matrix m n k => Y.map (algebraMap k E)) '' (W : Set _))) :
    X ∈ W := by
  by_contra hX
  obtain ⟨mu, hmuX, hmuW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hX inferInstance
  have hmuW' : ∀ Y ∈ W, mu Y = 0 := fun Y hY => by
    have : mu Y ∈ W.map mu := ⟨Y, hY, rfl⟩
    rwa [hmuW, Submodule.mem_bot] at this
  let muE : Matrix m n E →ₗ[E] E := ∑ i, ∑ j,
    algebraMap k E (mu (Matrix.single i j 1)) • Matrix.entryLinearMap E E i j
  have key : ∀ Y : Matrix m n k, muE (Y.map (algebraMap k E)) = algebraMap k E (mu Y) := by
    intro Y
    conv_rhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [muE, LinearMap.sum_apply, LinearMap.smul_apply,
      Matrix.entryLinearMap_apply, Matrix.map_apply, map_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hs : Matrix.single i j (Y i j) = Y i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, _root_.mul_one]
    rw [hs, map_smul, smul_eq_mul, map_mul, mul_comm]
  have hle : Submodule.span E ((fun Y : Matrix m n k => Y.map (algebraMap k E)) '' (W : Set _)) ≤
      LinearMap.ker muE := by
    rw [Submodule.span_le]
    rintro _ ⟨Y, hY, rfl⟩
    simp [key, hmuW' Y hY]
  have h0 : muE (X.map (algebraMap k E)) = 0 := hle h
  rw [key] at h0
  exact hmuX ((algebraMap k E).injective (by rw [h0, map_zero]))

/-- **Rationality for linear maps (proved).** For finite-dimensional `H, H'`, if `F ⊗ 1` lies in
the `E`-span of `{φ ⊗ 1 : φ ∈ W}` inside `Hom_E(E ⊗ H, E ⊗ H')`, then `F ∈ W`. -/
theorem mem_of_baseChange_mem_span (k E : Type*) [Field k] [Field E] [Algebra k E]
    {H H' : Type*} [AddCommGroup H] [Module k H] [FiniteDimensional k H] [AddCommGroup H']
    [Module k H'] [FiniteDimensional k H'] (W : Submodule k (H →ₗ[k] H')) (F : H →ₗ[k] H')
    (hFal : F.baseChange E ∈
      Submodule.span E ((fun φ : H →ₗ[k] H' => φ.baseChange E) '' (W : Set (H →ₗ[k] H')))) :
    F ∈ W := by
  let b := Module.finBasis k H
  let b' := Module.finBasis k H'
  let T := LinearMap.toMatrix b b'
  let TE := LinearMap.toMatrix (Algebra.TensorProduct.basis E b) (Algebra.TensorProduct.basis E b')
  have hT : T F ∈ W.map T.toLinearMap := by
    apply matrix_mem_of_map_mem_span (E := E)
    have h1 := Submodule.mem_map_of_mem (f := TE.toLinearMap) hFal
    rw [Submodule.map_span, Set.image_image] at h1
    simp only [LinearEquiv.coe_coe, TE, LinearMap.toMatrix_baseChange] at h1
    rw [Submodule.map_coe, Set.image_image]
    exact h1
  obtain ⟨G, hG, hTG⟩ := hT
  rwa [T.injective hTG] at hG

/-- **The Betti skeleton, finite-dimensional form (proved).** As `betti_skeleton`, without the
canonical map: `H, H'` finite-dimensional, `F ⊗ 1` in the `E`-span of `{φ ⊗ 1 : φ ∈ W}`. -/
theorem betti_skeleton_fd (E : Type*) [Field E] [Algebra ℚ E] {H H' : Type*} [AddCommGroup H]
    [Module ℚ H] [FiniteDimensional ℚ H] [AddCommGroup H'] [Module ℚ H'] [FiniteDimensional ℚ H']
    (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H')
    (hJ' : Function.Injective J') (W : Submodule ℚ (H →ₗ[ℚ] H'))
    (hW : ∀ φ ∈ W, φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ)
    (F : H →ₗ[ℚ] H') (hF : F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ))
    (hFal : F.baseChange E ∈
      Submodule.span E ((fun φ : H →ₗ[ℚ] H' => φ.baseChange E) '' (W : Set (H →ₗ[ℚ] H')))) :
    F = 0 := by
  have hFW : F ∈ W := mem_of_baseChange_mem_span ℚ E W F hFal
  have h0 : F.baseChange ℝ = 0 :=
    eq_zero_of_holo_of_antiholo J J' hJ' (F.baseChange ℝ) (hW F hFW) hF
  apply baseChange_injective₂ ℚ ℝ H H'
  rw [h0, LinearMap.baseChange_zero]

/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
def qEmbRing (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom

/-- `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
lemma resQ_spec (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    qEmbRing K (resQ K τ x) = τ (qEmbRing K x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

/-- `qEmbRing K : ℚ̄ → K̄` is bijective (`K̄` is algebraic over `ℚ`). -/
theorem qEmbRing_bijective (K : Type) [Field K] [NumberField K] :
    Function.Bijective (qEmbRing K) := by
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)
  let g : AlgebraicClosure K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let h : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (g.toRingHom.comp (qEmbRing K)).toRatAlgHom
  have hb : Function.Bijective h := Algebra.IsAlgebraic.algHom_bijective h
  refine ⟨(qEmbRing K).injective, fun z => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (g z)
  exact ⟨x, g.toRingHom.injective hx⟩

/-- Elements of `ℚ̄` landing in `K` are fixed by `resQ K σ`. -/
theorem resQ_fix (K : Type) [Field K] [NumberField K] (σ : Field.absoluteGaloisGroup K)
    (u : AlgebraicClosure ℚ)
    (hu : qEmbRing K u ∈ (algebraMap K (AlgebraicClosure K)).range) : resQ K σ u = u := by
  obtain ⟨k, hk⟩ := hu
  apply (qEmbRing K).injective
  refine (resQ_spec K σ u).trans ?_
  rw [← hk]
  exact AlgEquiv.commutes (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) k

/-- For `K/ℚ` Galois, the elements of `ℚ̄` landing in `K` form a `G_ℚ`-stable set. -/
theorem range_stable (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (g : PkgI4.GQ)
    (u : AlgebraicClosure ℚ)
    (hu : qEmbRing K u ∈ (algebraMap K (AlgebraicClosure K)).range) :
    qEmbRing K (g u) ∈ (algebraMap K (AlgebraicClosure K)).range := by
  obtain ⟨k, hk⟩ := hu
  have hsplit : ((minpoly ℚ k).map (algebraMap ℚ K)).Splits :=
    Normal.splits (IsGalois.to_normal) k
  have hp0 : (minpoly ℚ k).map (algebraMap ℚ K) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral k))
  apply hsplit.mem_range_of_isRoot hp0
  rw [Polynomial.map_map, Polynomial.IsRoot, Polynomial.eval_map]
  have e1 : (algebraMap K (AlgebraicClosure K)).comp (algebraMap ℚ K) =
      (qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have e2 : (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
      (algebraMap ℚ (AlgebraicClosure ℚ)) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    Subsingleton.elim _ _
  have hu0 : Polynomial.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) u (minpoly ℚ k) = 0 := by
    apply (qEmbRing K).injective
    rw [Polynomial.hom_eval₂, ← e1, ← hk, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
      minpoly.aeval, map_zero, map_zero]
  rw [e1, ← Polynomial.hom_eval₂]
  have : Polynomial.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) (g u) (minpoly ℚ k) = 0 := by
    have := Polynomial.hom_eval₂ (minpoly ℚ k) (algebraMap ℚ (AlgebraicClosure ℚ))
      (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) u
    rw [e2, hu0, map_zero] at this
    exact this.symm
  rw [this, map_zero]
/-! ## §2. Faltings in `ℚ_ℓ`-form (proved from `FaltingsTate` and `TateModuleFree`) -/

/-- The `ℚ_ℓ`-span of `{V_ℓ(f) : f ∈ Hom_K(A, B)}` inside `Hom_{ℚ_ℓ}(V_ℓ A, V_ℓ B)`. -/
def homSpanV {K : Type} [Field K] (A B : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Submodule ℚ_[ℓ] (A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) :=
  Submodule.span ℚ_[ℓ] (Set.range fun f : PkgI3.AbVar.Hom A B =>
    (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ])

open PkgI3 PkgI3.AbVar in
/-- **Faltings, `ℚ_ℓ`-form (proved).** For abelian varieties `A, B` over a number field, every
`G_K`-equivariant `ℚ_ℓ`-linear map `V_ℓ(A) → V_ℓ(B)` lies in the `ℚ_ℓ`-span of
`{V_ℓ(f) : f ∈ Hom_K(A, B)}`. From `FaltingsTate` (Faltings 1983, Satz 4 / Kor. 1) and
`TateModuleFree` (T26): `T_ℓ A` is finitely presented, so `s • φ` maps `T_ℓ A` into `T_ℓ B` for
some `s ≠ 0`, and the lift is equivariant (the proof of `PkgI3.exists_hom_ne_zero_of_equivariant`). -/
theorem faltingsV (hF : FaltingsTate) (hT : TateModuleFree)
    {K : Type} [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ)
    (heq : ∀ σ, φ ∘ₗ A.galRep ℓ σ = B.galRep ℓ σ ∘ₗ φ) : φ ∈ homSpanV A B ℓ := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfinA, -⟩ := hT K A ℓ hℓK
  obtain ⟨hfreeB, -, -⟩ := hT K B ℓ hℓK
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  let ιA : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let ιB : B.T ℓ →ₗ[ℤ_[ℓ]] B.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (B.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) ιB := inferInstance
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (nonZeroDivisors ℤ_[ℓ]) ιB ((φ.restrictScalars ℤ_[ℓ]) ∘ₗ ιA)
  have hs0 : (s : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hιB : Function.Injective ιB := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) ιB).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  have hιAσ : ∀ σ x, ιA (A.galT σ x) = A.galRep ℓ σ (ιA x) := fun σ x => by
    simp [ιA, galRep, LinearMap.baseChange_tmul]
  have hιBσ : ∀ σ x, ιB (B.galT σ x) = B.galRep ℓ σ (ιB x) := fun σ x => by
    simp [ιB, galRep, LinearMap.baseChange_tmul]
  have hsφ : ∀ x, ιB (h x) = (s : ℤ_[ℓ]) • φ (ιA x) := fun x => by
    have := congrArg (fun g => g x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
    exact this
  have hheq : IsGalEquivariant h := by
    intro σ x
    apply hιB
    rw [hsφ, hιAσ, hιBσ, hsφ]
    have := congrArg (fun g => g (ιA x)) (heq σ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.map_smul_of_tower]
  obtain ⟨z, hz⟩ : h ∈ Set.range (tateHomZl ℓ A B) := by
    rw [(hF K A B ℓ).2]; exact hheq
  have hmem : ∀ z, (tateHomZl ℓ A B z).baseChange ℚ_[ℓ] ∈ homSpanV A B ℓ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      have e : tateHomZl ℓ A B (a ⊗ₜ f) = a • tateHom ℓ A B f := rfl
      rw [e, LinearMap.baseChange_smul]
      have : (a • (tateHom ℓ A B f).baseChange ℚ_[ℓ]) =
          (algebraMap ℤ_[ℓ] ℚ_[ℓ] a) • (tateHom ℓ A B f).baseChange ℚ_[ℓ] :=
        (algebraMap_smul ℚ_[ℓ] a _).symm
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
    | add y z hy hz =>
      rw [map_add, LinearMap.baseChange_add]; exact Submodule.add_mem _ hy hz
  have hc : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) ≠ 0 := by
    simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne hs0
  have hφ : φ = (algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹ • h.baseChange ℚ_[ℓ] := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    apply LinearMap.ext
    intro x
    change φ ((1 : ℚ_[ℓ]) ⊗ₜ x) =
      (algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹ • h.baseChange ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ x)
    rw [LinearMap.baseChange_tmul]
    have h1 : ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] h x : B.V ℓ) = (s : ℤ_[ℓ]) • φ ((1 : ℚ_[ℓ]) ⊗ₜ x) :=
      hsφ x
    rw [h1, ← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]), smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hφ, ← hz]
  exact Submodule.smul_mem _ _ (hmem z)

/-! ## §3. From `c ∈ G_ℚ` to an automorphism of `K̄` (proved) -/

/-- `σ ∈ G_K` as a `K`-automorphism of `K̄` (for application to elements). -/
abbrev gA {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- **Complex conjugation on `K̄` (proved).** For `K/ℚ` Galois and a complex conjugation
`c ∈ G_ℚ`, transport `c` along `qEmbRing K : ℚ̄ ≅ K̄` to `cc : K̄ ≅ K̄`. Then `cc` is complex
conjugation for the embedding `ι = j ∘ qEmbRing⁻¹` (`j` realizing `c`), maps `K` to itself (`K`
normal), is an involution, and `τ ∘ cc = cc ∘ σ` in `Aut(K̄)` implies
`resQ K τ = c · resQ K σ · c⁻¹` in `G_ℚ`. -/
theorem conjData (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (c : PkgI4.GQ)
    (hc : PkgI4.IsComplexConj c) :
    ∃ (cc : AlgebraicClosure K ≃+* AlgebraicClosure K) (emb : AlgebraicClosure K →+* ℂ),
      (∀ x, emb (cc x) = starRingEnd ℂ (emb x)) ∧
      (∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') ∧
      (∀ x, cc (cc x) = x) ∧
      (∀ σ τ : Field.absoluteGaloisGroup K, (∀ x, gA τ (cc x) = cc (gA σ x)) →
        resQ K τ = c * resQ K σ * c⁻¹) := by
  have c2 := isComplexConj_mul_self hc
  obtain ⟨j, hj⟩ := hc
  let Φ : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (qEmbRing K) (qEmbRing_bijective K)
  let cc : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    (Φ.symm.trans (c : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)).trans Φ
  have hcc : ∀ u, cc (Φ u) = Φ (c u) := fun u => by
    change Φ (c (Φ.symm (Φ u))) = _
    rw [Φ.symm_apply_apply]
  have hΦ : ∀ u, Φ u = qEmbRing K u := fun _ => rfl
  refine ⟨cc, j.toRingHom.comp Φ.symm.toRingHom, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨u, rfl⟩ := Φ.surjective x
    rw [hcc]
    change j (Φ.symm (Φ (c u))) = starRingEnd ℂ (j (Φ.symm (Φ u)))
    rw [Φ.symm_apply_apply, Φ.symm_apply_apply, hj]
  · intro k
    obtain ⟨u, hu⟩ := Φ.surjective (algebraMap K _ k)
    obtain ⟨k', hk'⟩ := range_stable K c u ⟨k, hu.symm⟩
    exact ⟨k', by rw [← hu, hcc]; exact hk'.symm⟩
  · intro x
    obtain ⟨u, rfl⟩ := Φ.surjective x
    rw [hcc, hcc]
    congr 1
    exact congrArg (fun g : PkgI4.GQ => g u) c2
  · intro σ τ hστ
    apply AlgEquiv.ext; intro u
    apply (qEmbRing K).injective
    have e1 : (c * resQ K σ * c⁻¹) u = c (resQ K σ (c⁻¹ u)) := rfl
    have a1 : qEmbRing K (resQ K τ u) = gA τ (Φ u) := resQ_spec K τ u
    have a2 : Φ (resQ K σ (c⁻¹ u)) = gA σ (Φ (c⁻¹ u)) := resQ_spec K σ _
    have a3 : Φ u = cc (Φ (c⁻¹ u)) := by
      rw [hcc]; congr 1; exact (AlgEquiv.apply_symm_apply c u).symm
    rw [a1, e1]
    change gA τ (Φ u) = Φ (c (resQ K σ (c⁻¹ u)))
    rw [← hcc, a2, ← hστ, ← a3]

/-- **Every `τ ∈ G_K` is a `cc`-twist (proved):** `σ = cc τ cc` fixes `K`. -/
theorem exists_twist (K : Type) [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k')
    (h2 : ∀ x, cc (cc x) = x) (τ : Field.absoluteGaloisGroup K) :
    ∃ σ : Field.absoluteGaloisGroup K, ∀ x, gA τ (cc x) = cc (gA σ x) := by
  let σr : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    (cc.trans ((gA τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : AlgebraicClosure K ≃+* AlgebraicClosure K)).trans cc
  have hfix : ∀ k : K, σr (algebraMap K _ k) = algebraMap K _ k := by
    intro k
    obtain ⟨k', hk'⟩ := hK k
    change cc (gA τ (cc (algebraMap K _ k))) = _
    rw [hk', AlgEquiv.commutes, ← hk', h2]
  refine ⟨AlgEquiv.ofRingEquiv (f := σr) hfix, fun x => ?_⟩
  change gA τ (cc x) = cc (cc (gA τ (cc x)))
  rw [h2]

/-! ## §4. The remaining glue and the reduction -/

/-- The `ℚ`-subspace of `Hom_ℚ(H, H')` of maps that are holomorphic for complex structures `J, J'`
on `H ⊗ ℝ`, `H' ⊗ ℝ`. -/
def holoSub {H H' : Type} [AddCommGroup H] [Module ℚ H] [AddCommGroup H'] [Module ℚ H']
    (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H') :
    Submodule ℚ (H →ₗ[ℚ] H') where
  carrier := {φ | φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ}
  add_mem' := by
    intro φ ψ hφ hψ
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.baseChange_add, LinearMap.add_comp, LinearMap.comp_add, hφ, hψ]
  zero_mem' := by simp
  smul_mem' := by
    intro q φ hφ
    simp only [Set.mem_setOf_eq] at *
    apply LinearMap.ext; intro x
    have := LinearMap.congr_fun hφ x
    simp only [LinearMap.coe_comp, Function.comp_apply] at this ⊢
    rw [LinearMap.baseChange_smul, LinearMap.smul_apply, LinearMap.smul_apply, this,
      LinearMap.map_smul_of_tower]

/-- **G10 core, geometric input (GLUE, unproved; STANDARD).** Conjugate variety plus Artin
comparison at a complex place, with holomorphy of homomorphisms. For a number field `K`, an
abelian surface `A/K`, a prime `ℓ`, a ring automorphism `cc` of `K̄` mapping `K` to itself and an
embedding `ι : K̄ → ℂ` with `ι ∘ cc = conj ∘ ι`, there are
* an abelian variety `B/K` and a `ℚ_ℓ`-linear `C : V_ℓ(A) → V_ℓ(B)` with the twisted equivariance
  `C ρ_A(σ) = ρ_B(τ) C` whenever `τ ∘ cc = cc ∘ σ`. Witness: `B = A^s = A ×_{K,s} K`, `s = cc|_K`,
  and `C = c_*`, the transport of `K̄`-points `P ↦ P ∘ Spec(cc)` (`A^s(K̄) = A(K̄ via s)`);
* finite-dimensional `ℚ`-spaces `H, H'` with `ℚ_ℓ ⊗ H ≅ V_ℓ(A)` (`α`), `ℚ_ℓ ⊗ H' ≅ V_ℓ(B)` (`β`),
  ℝ-linear `J, J'` on `ℝ ⊗ H, ℝ ⊗ H'` (`J'` injective) and a nonzero `ℚ`-linear `F : H → H'`.
  Witness: `H = H₁(A(ℂ)_ι, ℚ)`, `H' = H₁(B(ℂ)_ι, ℚ) = H₁(A(ℂ)_{conj ∘ ι}, ℚ)` (the lattices of
  the uniformizations T35, `ℝ ⊗ H = ℂ^g`), `J, J'` multiplication by `i`, `α, β` the Artin
  comparison through `ι` (`A(K̄)[ℓⁿ] ≅ A(ℂ)[ℓⁿ] = ℓ⁻ⁿΛ/Λ`, bijective by T5), `F = F_*` the map
  of complex conjugation `A(ℂ)_ι → A(ℂ)_{conj ∘ ι}` on `H₁` (bijective, `H ≠ 0` as `dim A = 2`);
such that `F` is antiholomorphic (`F J = −J' F`), `C` corresponds to `F ⊗ 1` (`ι ∘ cc = conj ∘ ι`),
and each `f ∈ Hom_K(A, B)` corresponds to `φ ⊗ 1` for a holomorphic `φ : H → H'` (`φ = H₁(f)`,
holomorphic as `f` is a morphism of varieties: T11(a) in Hom form, Mumford §1, Birkenhake–Lange
1.2.1; UNVERIFIED numbers). Sources: SGA 4 XI 4.4 (Artin comparison), Mumford §1, §4 (T35, T5);
N5 L742-751, h-trust C5. -/
def ConjBettiData : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (cc : AlgebraicClosure K ≃+* AlgebraicClosure K) (emb : AlgebraicClosure K →+* ℂ),
    A.dim = 2 → (∀ x, emb (cc x) = starRingEnd ℂ (emb x)) →
    (∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') →
    ∃ (B : PkgI3.AbVar K) (C : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ),
      (∀ σ τ : Field.absoluteGaloisGroup K, (∀ x, gA τ (cc x) = cc (gA σ x)) →
          C ∘ₗ A.galRep ℓ σ = B.galRep ℓ τ ∘ₗ C) ∧
      ∃ (H H' : Type) (_ : AddCommGroup H) (_ : Module ℚ H) (_ : FiniteDimensional ℚ H)
        (_ : AddCommGroup H') (_ : Module ℚ H') (_ : FiniteDimensional ℚ H')
        (α : ℚ_[ℓ] ⊗[ℚ] H ≃ₗ[ℚ_[ℓ]] A.V ℓ) (β : ℚ_[ℓ] ⊗[ℚ] H' ≃ₗ[ℚ_[ℓ]] B.V ℓ)
        (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H') (F : H →ₗ[ℚ] H'),
        Function.Injective J' ∧ F ≠ 0 ∧
        F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ) ∧
        β.symm.toLinearMap ∘ₗ C ∘ₗ α.toLinearMap = F.baseChange ℚ_[ℓ] ∧
        ∀ f : PkgI3.AbVar.Hom A B, ∃ φ : H →ₗ[ℚ] H',
          φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ ∧
          β.symm.toLinearMap ∘ₗ (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] ∘ₗ
            α.toLinearMap = φ.baseChange ℚ_[ℓ]

/-- **`ConjTwistNontrivial` from T26 and `ConjBettiData` (proved).** If `ρ_A(τ) = ρ_A(σ)` whenever
`resQ τ = c resQ σ c⁻¹`, the twisted-equivariant `C` is `G_K`-equivariant, so lies in the span of
`Hom(A, B)` (`faltingsV`); on the Betti side `F ⊗ 1` lies in the span of holomorphic `φ ⊗ 1`, so
`F = 0` (`betti_skeleton_fd`), a contradiction. -/
theorem conjTwistNontrivial_of_conjBettiData (hT : PkgI3.TateModuleFree)
    (hB : ConjBettiData) : ConjTwistNontrivial := by
  intro hF K _ _ _ A ℓ _ hdim c hc hall
  obtain ⟨cc, emb, hι, hK, h2, hres⟩ := conjData K c hc
  obtain ⟨B, C, htw, H, H', _, _, _, _, _, _, α, β, J, J', F, hJ', hF0, hanti, hCF, hhol⟩ :=
    hB K A ℓ cc emb hdim hι hK
  have heq : ∀ τ, C ∘ₗ A.galRep ℓ τ = B.galRep ℓ τ ∘ₗ C := by
    intro τ
    obtain ⟨σ, hσ⟩ := exists_twist K cc hK h2 τ
    rw [hall σ τ (hres σ τ hσ), htw σ τ hσ]
  have hCmem := faltingsV hF hT A B ℓ C heq
  let Tr : (A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) ≃ₗ[ℚ_[ℓ]] (ℚ_[ℓ] ⊗[ℚ] H →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] H') :=
    LinearEquiv.arrowCongr α.symm β.symm
  have hTr : ∀ M, Tr M = β.symm.toLinearMap ∘ₗ M ∘ₗ α.toLinearMap := fun M => by
    apply LinearMap.ext; intro x
    simp [Tr, LinearEquiv.arrowCongr_apply]
  have hle : homSpanV A B ℓ ≤ (Submodule.span ℚ_[ℓ]
      ((fun φ : H →ₗ[ℚ] H' => φ.baseChange ℚ_[ℓ]) ''
        (holoSub J J' : Set (H →ₗ[ℚ] H')))).comap Tr.toLinearMap := by
    rw [homSpanV, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    obtain ⟨φ, hφJ, hφ⟩ := hhol f
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, hTr]
    rw [hφ]
    exact Submodule.subset_span ⟨φ, hφJ, rfl⟩
  have hFmem := hle hCmem
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, hTr, hCF] at hFmem
  exact hF0 (betti_skeleton_fd ℚ_[ℓ] J J' hJ' (holoSub J J') (fun φ hφ => hφ) F hanti hFmem)

/-- **`ConjTwistFromLeaves` from `ConjBettiData` (proved).** T26 is among its hypotheses. -/
theorem conjTwistFromLeaves_of_conjBettiData (hB : ConjBettiData) : ConjTwistFromLeaves :=
  fun _ _ _ _ hT => conjTwistNontrivial_of_conjBettiData hT hB

/-! ## §5. The conjugate variety and the transport `c_*` (proved), and the Betti glue

`conjVar A s = A ×_{Spec K, Spec s} Spec K` for a ring endomorphism `s` of `K` (Mathlib's
`Over.pullback`, as `PkgI3.AbVar.baseChange`), and for an automorphism `cc` of `K̄` extending `s`,
the transport of points `A(K̄) → A^s(K̄)`, `P ↦ P ∘ Spec(cc)` read through the adjunction
`Over.map ⊣ Over.pullback` (the recipe of scratch/unram-tate/BCPoints.lean). It carries the
action of `σ` to that of `τ` whenever `τ ∘ cc = cc ∘ σ`. -/

open PkgI3 in
/-- `Spec(s) : Spec K → Spec K`. -/
abbrev specS {K : Type} [Field K] (s : K →+* K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom s)

/-- **The conjugate abelian variety** `A^s = A ×_{Spec K, Spec s} Spec K` (pullback along
`Spec(s)`; group structure transported by the monoidal functor `Over.pullback`). -/
def conjVar {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K) : PkgI3.AbVar K :=
  let f := specS s
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

section Transport

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K)
  (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k))

/-- The adjunction bijection for `Over.map (Spec s) ⊣ Over.pullback (Spec s)` is
multiplicative. -/
theorem homEquiv_mul_conj (X : Over (Spec (CommRingCat.of K)))
    (p q : (Over.map (specS s)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (specS s)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (specS s)).homEquiv X A.X p *
        (Over.mapPullbackAdj (specS s)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- `Spec(cc)`, as a morphism over `K` from `Spec K̄` (structure map `Spec(s) ∘ Spec(alg)`) to
`Spec K̄`. -/
def ccHom : (Over.map (specS s)).obj (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)) ⟶
    PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K))) (by
    simp only [Over.map_obj_hom, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact hs x)

/-- **The transport `c_*` on `K̄`-points (proved):** `A(K̄) → A^s(K̄)`, a group homomorphism. -/
def conjPt : A.Pt (AlgebraicClosure K) →* (conjVar A s).Pt (AlgebraicClosure K) :=
  MonoidHom.mk' (fun P => (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ P))
    (fun P Q => by
      change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ (P * Q)) = _
      rw [MonObj.comp_mul, homEquiv_mul_conj]
      rfl)

/-- **Twisted equivariance of `c_*` on points (proved):** if `τ ∘ cc = cc ∘ σ` then
`c_*(σ P) = τ c_*(P)`. -/
theorem conjPt_galAct (σ τ : Field.absoluteGaloisGroup K)
    (h : ∀ x, gA τ (cc x) = cc (gA σ x)) (P : A.Pt (AlgebraicClosure K)) :
    conjPt A s cc hs (A.galAct (gA σ) P) = (conjVar A s).galAct (gA τ) (conjPt A s cc hs P) := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ PkgI3.AbVar.galHom (gA σ) ≫ P) =
    PkgI3.AbVar.galHom (gA τ) ≫ (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ P)
  have hsq : ccHom s cc hs ≫ PkgI3.AbVar.galHom (gA σ) =
      (Over.map (specS s)).map (PkgI3.AbVar.galHom (gA τ)) ≫ ccHom s cc hs := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
        Spec.map (CommRingCat.ofHom ((gA σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →+* AlgebraicClosure K)) =
      Spec.map (CommRingCat.ofHom ((gA τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →+* AlgebraicClosure K)) ≫
        Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, hsq, Category.assoc, Adjunction.homEquiv_naturality_left]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`c_*` on Tate modules (proved):** `T_ℓ(A) → T_ℓ(A^s)`. -/
def conjT : A.T ℓ →ₗ[ℤ_[ℓ]] (conjVar A s).T ℓ :=
  PkgI3.Tate.map (MonoidHom.toAdditive (conjPt A s cc hs))

/-- **`c_*` on `V_ℓ` (proved):** `V_ℓ(A) → V_ℓ(A^s)`. -/
def conjV : A.V ℓ →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ :=
  (conjT A s cc hs ℓ).baseChange ℚ_[ℓ]

theorem conjT_galT (σ τ : Field.absoluteGaloisGroup K) (h : ∀ x, gA τ (cc x) = cc (gA σ x)) :
    conjT A s cc hs ℓ ∘ₗ A.galT σ = (conjVar A s).galT τ ∘ₗ conjT A s cc hs ℓ := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  exact congrArg Additive.ofMul (conjPt_galAct A s cc hs σ τ h (Additive.toMul (x.1 n)))

/-- **Twisted equivariance of `c_*` on `V_ℓ` (proved):** `c_* ρ_A(σ) = ρ_{A^s}(τ) c_*` whenever
`τ ∘ cc = cc ∘ σ`. -/
theorem conjV_galRep (σ τ : Field.absoluteGaloisGroup K)
    (h : ∀ x, gA τ (cc x) = cc (gA σ x)) :
    conjV A s cc hs ℓ ∘ₗ A.galRep ℓ σ = (conjVar A s).galRep ℓ τ ∘ₗ conjV A s cc hs ℓ := by
  change (conjT A s cc hs ℓ).baseChange ℚ_[ℓ] ∘ₗ (A.galT σ).baseChange ℚ_[ℓ] =
    ((conjVar A s).galT τ).baseChange ℚ_[ℓ] ∘ₗ (conjT A s cc hs ℓ).baseChange ℚ_[ℓ]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, conjT_galT A s cc hs ℓ σ τ h]

end Transport

/-- The function `cc|_K : K → K` for an automorphism `cc` of `K̄` mapping `K` into itself. -/
def sFun {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') (k : K) : K :=
  Classical.choose (hK k)

theorem sFun_spec {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') (k : K) :
    algebraMap K (AlgebraicClosure K) (sFun cc hK k) = cc (algebraMap K _ k) :=
  (Classical.choose_spec (hK k)).symm

/-- The ring endomorphism `s = cc|_K` of `K`. -/
def restrictK {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') : K →+* K where
  toFun := sFun cc hK
  map_one' := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [sFun_spec]; simp)
  map_mul' a b := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [map_mul, sFun_spec, sFun_spec, sFun_spec, map_mul, map_mul])
  map_zero' := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [sFun_spec]; simp)
  map_add' a b := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [map_add, sFun_spec, sFun_spec, sFun_spec, map_add, map_add])

theorem restrictK_spec {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') (k : K) :
    cc (algebraMap K _ k) = algebraMap K _ (restrictK cc hK k) :=
  (sFun_spec cc hK k).symm

/-- **G10 core, Betti input for the concrete `c_*` (GLUE, unproved; STANDARD).** For a number
field `K`, an abelian surface `A/K`, a prime `ℓ`, a ring endomorphism `s` of `K`, an automorphism
`cc` of `K̄` extending `s` and an embedding `ι : K̄ → ℂ` with `ι ∘ cc = conj ∘ ι`: there are
finite-dimensional `ℚ`-spaces `H, H'`, `ℚ_ℓ`-isomorphisms `α : ℚ_ℓ ⊗ H ≅ V_ℓ(A)`,
`β : ℚ_ℓ ⊗ H' ≅ V_ℓ(A^s)`, ℝ-linear `J, J'` on `ℝ ⊗ H, ℝ ⊗ H'` (`J'` injective) and a nonzero
`F : H → H'`, such that `F J = −J' F`, `β⁻¹ c_* α = F ⊗ 1` for the transport
`c_* = conjV A s cc hs ℓ` (§5), and every `f ∈ Hom_K(A, A^s)` acts as `φ ⊗ 1` with `φ J = J' φ`.
Witness (STANDARD): `H = H₁(A(ℂ)_ι, ℚ)`, `H' = H₁(A^s(ℂ)_ι, ℚ) = H₁(A(ℂ)_{conj∘ι}, ℚ)` (lattices
of the uniformizations T35, `ℝ ⊗ H = ℂ^g`), `J, J'` multiplication by `i`, `α, β` Artin's
comparison through `ι` (`A(K̄)[ℓⁿ] → A(ℂ)[ℓⁿ] = ℓ⁻ⁿΛ/Λ` bijective, by T5 over `K̄` and over `ℂ`;
SGA 4 XI 4.4), `F = F_*` for complex conjugation `A(ℂ)_ι → A(ℂ)_{conj∘ι}`, `P ↦ P ∘ Spec(conj)`,
antiholomorphic and bijective, `H ≠ 0` as `dim A = 2`; `β⁻¹ c_* α = F ⊗ 1` because
`P ∘ Spec(cc) ∘ Spec(ι) = P ∘ Spec(ι) ∘ Spec(conj)`; `φ = H₁(f)`, holomorphic because `f` is a
morphism of varieties (T11(a) in Hom form: Mumford §1, Birkenhake–Lange 1.2.1, UNVERIFIED
numbers). N5 L742-751, h-trust C5. -/
def ConjBettiComparison : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (s : K →+* K) (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k)) (emb : AlgebraicClosure K →+* ℂ),
    A.dim = 2 → (∀ x, emb (cc x) = starRingEnd ℂ (emb x)) →
      ∃ (H H' : Type) (_ : AddCommGroup H) (_ : Module ℚ H) (_ : FiniteDimensional ℚ H)
        (_ : AddCommGroup H') (_ : Module ℚ H') (_ : FiniteDimensional ℚ H')
        (α : ℚ_[ℓ] ⊗[ℚ] H ≃ₗ[ℚ_[ℓ]] A.V ℓ) (β : ℚ_[ℓ] ⊗[ℚ] H' ≃ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ)
        (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H') (F : H →ₗ[ℚ] H'),
        Function.Injective J' ∧ F ≠ 0 ∧
        F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ) ∧
        β.symm.toLinearMap ∘ₗ conjV A s cc hs ℓ ∘ₗ α.toLinearMap = F.baseChange ℚ_[ℓ] ∧
        ∀ f : PkgI3.AbVar.Hom A (conjVar A s), ∃ φ : H →ₗ[ℚ] H',
          φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ ∧
          β.symm.toLinearMap ∘ₗ (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] ∘ₗ
            α.toLinearMap = φ.baseChange ℚ_[ℓ]

/-- **`ConjBettiData` from `ConjBettiComparison` (proved):** `B = conjVar A s` with
`s = cc|_K`, `C = conjV`, twisted equivariance by `conjV_galRep`. -/
theorem conjBettiData_of_comparison (h : ConjBettiComparison) : ConjBettiData := by
  intro K _ _ A ℓ _ cc emb hdim hι hK
  obtain ⟨H, H', i1, i2, i3, i4, i5, i6, α, β, J, J', F, hrest⟩ :=
    h K A ℓ (restrictK cc hK) cc (restrictK_spec cc hK) emb hdim hι
  exact ⟨conjVar A (restrictK cc hK), conjV A (restrictK cc hK) cc (restrictK_spec cc hK) ℓ,
    fun σ τ hστ => conjV_galRep A _ cc _ ℓ σ τ hστ,
    H, H', i1, i2, i3, i4, i5, i6, α, β, J, J', F, hrest⟩

/-- **`ConjTwistNontrivial` from T26 and `ConjBettiComparison` (proved).** -/
theorem conjTwistNontrivial_of_comparison (hT : PkgI3.TateModuleFree)
    (h : ConjBettiComparison) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_conjBettiData hT (conjBettiData_of_comparison h)

/-- **`ConjTwistFromLeaves` from `ConjBettiComparison` (proved).** -/
theorem conjTwistFromLeaves_of_comparison (h : ConjBettiComparison) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_conjBettiData (conjBettiData_of_comparison h)

end G0Galois

#print axioms G0Galois.faltingsV
#print axioms G0Galois.conjData
#print axioms G0Galois.conjTwistNontrivial_of_conjBettiData
#print axioms G0Galois.conjTwistFromLeaves_of_conjBettiData
#print axioms G0Galois.conjV_galRep
#print axioms G0Galois.conjBettiData_of_comparison
#print axioms G0Galois.conjTwistNontrivial_of_comparison
#print axioms G0Galois.conjTwistFromLeaves_of_comparison
