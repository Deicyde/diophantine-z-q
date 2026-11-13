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

/-! ## §6. The next split of `ConjBettiComparison` (statements compile; the assembly is not
formalized)

`ConjBettiComparison` follows (STANDARD argument, docs/research/conj-twist.md §3) from T35
(`UniformizationExists`, applied to `A` and `A^s` at `σ = ι ∘ alg`) and the five Props below.
`toC` is the comparison of `K̄`-points with complex points through `ι : K̄ → ℂ`. -/

open ZInQ.LeafPush2 (CPts cptObj IsUniformization)

/-- `Spec(ι) : Spec ℂ → Spec K̄` over `K`. -/
def embHom {K : Type} [Field K] (emb : AlgebraicClosure K →+* ℂ) :
    cptObj (emb.comp (algebraMap K (AlgebraicClosure K))) ⟶
      PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom emb)) (by
    simp only [cptObj, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- **Comparison of points through `ι` (proved to be a homomorphism):** `A(K̄) → A(ℂ)_{ι∘alg}`,
`P ↦ P ∘ Spec(ι)`. -/
def toC {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) :
    A.Pt (AlgebraicClosure K) →* CPts A (emb.comp (algebraMap K (AlgebraicClosure K))) where
  toFun P := embHom emb ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- **`toC` is injective (proved).** -/
theorem toC_injective {K : Type} [Field K] (A : PkgI3.AbVar K)
    (emb : AlgebraicClosure K →+* ℂ) : Function.Injective (toC A emb) := by
  intro P P' h
  apply Over.OverMorphism.ext
  have hU : Spec.map (CommRingCat.ofHom emb) ≫ P.left =
      Spec.map (CommRingCat.ofHom emb) ≫ P'.left := by
    have := congrArg CommaMorphism.left h
    exact this
  haveI : IsReduced (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).left := by
    change IsReduced (Spec (CommRingCat.of (AlgebraicClosure K))); infer_instance
  have h0 : Surjective (Spec.map (CommRingCat.ofHom emb)) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint ℂ, Subsingleton.elim _ _⟩⟩
  let ι' : Spec (CommRingCat.of ℂ) ⟶ (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).left :=
    Spec.map (CommRingCat.ofHom emb)
  haveI : Surjective ι' := h0
  exact ext_of_isDominant_of_isSeparated A.X.hom (by rw [Over.w P, Over.w P']) ι' hU

/-- **N1. Torsion comparison (GLUE, unproved; STANDARD).** `toC` is injective (`Spec ℂ → Spec K̄`
is faithfully flat, hence an epimorphism of schemes) and every `n`-torsion complex point
(`n ≥ 1`) comes from `A(K̄)`: `A(K̄)[n]` and `A(ℂ)[n]` both have `n^{2g}` elements (T5 over `K̄`
and over `ℂ`) and `toC` is injective. Equivalently, `A[n]` is finite étale in characteristic `0`
(Mumford §4, §6; UNVERIFIED numbers). -/
def ArtinTorsion : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (n : ℕ), 0 < n →
    Function.Injective (toC A emb) ∧
      ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))), Q ^ n = 1 →
        ∃ P, toC A emb P = Q

/-- **N4. Tate module of a uniformized abelian variety (GLUE, unproved; STANDARD).** For a
uniformization `Φ : ℂ^g → A(ℂ)_{ι∘alg}` with lattice `Λ` (T35), there is a `ℤ_ℓ`-isomorphism
`α : ℤ_ℓ ⊗ Λ ≅ T_ℓ(A)` with `toC (α(1 ⊗ λ))ₙ = Φ(ℓ⁻ⁿ λ)` for `λ ∈ Λ`. (The sequence
`Φ(ℓ⁻ⁿλ)` is compatible and `Φ(λ) = 1`; it comes from `A(K̄)` by N1; bijectivity is
`T_ℓ = lim Λ/ℓⁿΛ = Λ ⊗ ℤ_ℓ`, `Λ ≅ ℤ^{2g}`. Mumford §1, §4; this is Artin's comparison for
abelian varieties, SGA 4 XI 4.4; UNVERIFIED numbers.) The formula pins `α` and makes it natural
for homomorphisms and for `c_*` (by injectivity of `toC`). -/
def TateLattice : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))),
    A.dim = (g : WithBot ℕ∞) → ∀ [DiscreteTopology Λ], IsZLattice ℝ Λ →
    IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ α : TensorProduct ℤ ℤ_[ℓ] Λ ≃ₗ[ℤ_[ℓ]] A.T ℓ,
      ∀ (lam : Λ) (n : ℕ), toC A emb (Additive.toMul ((α (1 ⊗ₜ lam)).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ))

/-- **N2. T11(a) in Hom form (textbook LEAF; Birkenhake–Lange, *Complex abelian varieties*,
Prop. 1.2.1, with holomorphy of algebraic morphisms; Mumford §1; UNVERIFIED numbers).** For
abelian varieties `A, B` over `K`, `σ : K → ℂ` and uniformizations `Φ_A, Φ_B` of `A(ℂ)_σ`,
`B(ℂ)_σ`, every homomorphism `f : A → B` lifts to a `ℂ`-linear map `M` with
`Φ_B(Mz) = f(Φ_A(z))`. (`T11a_RiemannEnd`'s second half is the case `A = B` over `ℂ`.) -/
def HomLinearLift : Prop :=
  ∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom

/-- `Spec(conj) : Spec ℂ → Spec ℂ`, over `K` from `σ ∘ s` to `σ`, when `σ ∘ s = conj ∘ σ`. -/
def conjHom {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : cptObj (σ.comp s) ⟶ cptObj σ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) (by
    simp only [cptObj, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

/-- Complex conjugation `A(ℂ)_σ → A(ℂ)_{σ∘s}` when `σ ∘ s = conj ∘ σ`: `Q ↦ Q ∘ Spec(conj)`. -/
def conjCs {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) : CPts A (σ.comp s) :=
  conjHom σ s h ≫ Q

/-- `(Over.map Spec(s)).obj (Spec ℂ via σ) ⟶ Spec ℂ via σ ∘ s` (the identity of `Spec ℂ`). -/
def mapPtIso {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K) :
    (Over.map (specS s)).obj (cptObj σ) ⟶ cptObj (σ.comp s) :=
  Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_hom, cptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- The map `A(ℂ)_σ → A^s(ℂ)_σ`, `Q ↦ Q ∘ Spec(conj)` read through `A^s(ℂ)_σ = A(ℂ)_{σ∘s}`
(adjunction `Over.map ⊣ Over.pullback`). -/
def twistC {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) : CPts (conjVar A s) σ :=
  (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjCs A σ s h Q)

/-- **N3. Complex conjugation is antiholomorphic (GLUE, unproved; STANDARD).** If
`σ ∘ s = conj ∘ σ`, then for uniformizations `Φ` of `A(ℂ)_σ` and `Φ'` of `A^s(ℂ)_σ` the map
`twistC` lifts to an injective `ℝ`-linear, `ℂ`-antilinear `N` (`N(iz) = −iN(z)`) with
`Φ'(Nz) = twistC(Φ z)`. (`z ↦ twistC(Φ(z̄))` is a holomorphic uniformization of
`A^s(ℂ)_σ = A(ℂ)_{conj∘σ}`; two uniformizations differ by a `ℂ`-linear isomorphism, BL 1.2.1.) -/
def ConjAntiLift : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) (Φ' : (Fin g → ℂ) → CPts (conjVar A s) σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ → IsUniformization σ Λ' Φ' →
    ∃ N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ z, N (Complex.I • z) = -(Complex.I • N z)) ∧
      Function.Injective N ∧ ∀ z, Φ' (N z) = twistC A σ s h (Φ z)

/-- **N5. Dimension of the conjugate (GLUE, unproved; STANDARD).** For a number field `K`, every
ring endomorphism `s` is an automorphism, so `Spec(s)` is an isomorphism and so is
`A^s → A`; Krull dimension is preserved. -/
def ConjVarDim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (s : K →+* K),
    (conjVar A s).dim = A.dim

/-- **`toC` intertwines `c_*` with `twistC` (proved):** `toC (c_* P) = twistC (toC P)` for
`σ = ι ∘ alg`, `ι ∘ cc = conj ∘ ι`. This is the identity `Spec(ι) ≫ Spec(cc) = Spec(conj) ≫ Spec(ι)`
read through the adjunction; it is the "`β⁻¹ c_* α = F ⊗ 1`" part of `ConjBettiComparison` at
the level of points. -/
theorem toC_conjPt {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K)
    (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k)) (emb : AlgebraicClosure K →+* ℂ)
    (hι : ∀ x, emb (cc x) = starRingEnd ℂ (emb x))
    (h : (emb.comp (algebraMap K _)).comp s = (starRingEnd ℂ).comp (emb.comp (algebraMap K _)))
    (P : A.Pt (AlgebraicClosure K)) :
    toC (conjVar A s) emb (conjPt A s cc hs P) =
      twistC A (emb.comp (algebraMap K _)) s h (toC A emb P) := by
  change embHom emb ≫ (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ P) =
    (Over.mapPullbackAdj (specS s)).homEquiv _ _
      (mapPtIso _ s ≫ conjCs A _ s h (embHom emb ≫ P))
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  simp only [conjCs, ← Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom emb) ≫
      Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K)) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom emb)
  rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact hι x

/-! ## §7. Naturality of the comparison of N4 (proved; uses `toC_injective`)

With N1, the formula of N4 pins `α`, and `α` is natural: for a homomorphism `f` with linear lift
`M` (N2), `T_ℓ(f) ∘ α_A = α_B ∘ (M ⊗ 1)` on `1 ⊗ Λ_A`; for `c_*` with antilinear lift `N` (N3),
`c_* ∘ α_A = α_{A^s} ∘ (N ⊗ 1)` on `1 ⊗ Λ_A`. These are the two compatibilities
`β⁻¹ V(f) α = φ ⊗ 1` and `β⁻¹ c_* α = F ⊗ 1` of `ConjBettiComparison`, before tensoring with `ℚ`
and `ℚ_ℓ`. -/

/-- The lattice point `λ` lies in the kernel of `Φ`, and a linear lift maps lattices to lattices:
`Φ_B(Mλ) = f(Φ_A(λ)) = f(1) = 1`. -/
theorem lift_mem_lattice {K : Type} [Field K] {A B : PkgI3.AbVar K} {σ : K →+* ℂ} {g h : ℕ}
    {ΛA : Submodule ℤ (Fin g → ℂ)} {ΛB : Submodule ℤ (Fin h → ℂ)}
    {ΦA : (Fin g → ℂ) → CPts A σ} {ΦB : (Fin h → ℂ) → CPts B σ}
    (hA : IsUniformization σ ΛA ΦA) (hB : IsUniformization σ ΛB ΦB) (f : PkgI3.AbVar.Hom A B)
    (M : (Fin g → ℂ) → (Fin h → ℂ)) (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (lam : ΛA) :
    M lam ∈ ΛB := by
  rw [← hB.2.1, hM, (hA.2.1 _).mpr lam.2]
  exact MonObj.one_comp f.hom

/-- **Naturality for homomorphisms (proved).** -/
theorem homT_tateLattice {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (emb : AlgebraicClosure K →+* ℂ) {g h : ℕ} {ΛA : Submodule ℤ (Fin g → ℂ)}
    {ΛB : Submodule ℤ (Fin h → ℂ)}
    {ΦA : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))}
    {ΦB : (Fin h → ℂ) → CPts B (emb.comp (algebraMap K (AlgebraicClosure K)))}
    (ℓ : ℕ) [Fact ℓ.Prime]
    (αA : TensorProduct ℤ ℤ_[ℓ] ΛA →ₗ[ℤ_[ℓ]] A.T ℓ)
    (hαA : ∀ (lam : ΛA) (n : ℕ), toC A emb (Additive.toMul ((αA (1 ⊗ₜ lam)).1 n)) =
        ΦA (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)))
    (αB : TensorProduct ℤ ℤ_[ℓ] ΛB →ₗ[ℤ_[ℓ]] B.T ℓ)
    (hαB : ∀ (lam : ΛB) (n : ℕ), toC B emb (Additive.toMul ((αB (1 ⊗ₜ lam)).1 n)) =
        ΦB (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin h → ℂ)))
    (f : PkgI3.AbVar.Hom A B) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (lam : ΛA) (hlam : M lam ∈ ΛB) :
    PkgI3.AbVar.homT f (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ ⟨M lam, hlam⟩) := by
  apply Subtype.ext; funext n
  apply Additive.toMul.injective
  apply toC_injective B emb
  change toC B emb (Additive.toMul ((αA (1 ⊗ₜ lam)).1 n) ≫ f.hom) = _
  rw [hαB]
  change embHom emb ≫ Additive.toMul ((αA (1 ⊗ₜ lam)).1 n) ≫ f.hom = _
  rw [← Category.assoc]
  change toC A emb (Additive.toMul ((αA (1 ⊗ₜ lam)).1 n)) ≫ f.hom = _
  rw [hαA, ← hM, map_smul]

/-- **Naturality for `c_*` (proved, from `toC_conjPt`).** -/
theorem conjT_tateLattice {K : Type} [Field K] (A : PkgI3.AbVar K)
    (s : K →+* K) (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k)) (emb : AlgebraicClosure K →+* ℂ)
    (hι : ∀ x, emb (cc x) = starRingEnd ℂ (emb x))
    (h : (emb.comp (algebraMap K _)).comp s = (starRingEnd ℂ).comp (emb.comp (algebraMap K _)))
    {g : ℕ} {Λ Λ' : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))}
    {Φ' : (Fin g → ℂ) → CPts (conjVar A s) (emb.comp (algebraMap K (AlgebraicClosure K)))}
    (ℓ : ℕ) [Fact ℓ.Prime]
    (α : TensorProduct ℤ ℤ_[ℓ] Λ →ₗ[ℤ_[ℓ]] A.T ℓ)
    (hα : ∀ (lam : Λ) (n : ℕ), toC A emb (Additive.toMul ((α (1 ⊗ₜ lam)).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)))
    (α' : TensorProduct ℤ ℤ_[ℓ] Λ' →ₗ[ℤ_[ℓ]] (conjVar A s).T ℓ)
    (hα' : ∀ (lam : Λ') (n : ℕ),
        toC (conjVar A s) emb (Additive.toMul ((α' (1 ⊗ₜ lam)).1 n)) =
        Φ' (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)))
    (N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (hN : ∀ z, Φ' (N z) = twistC A (emb.comp (algebraMap K _)) s h (Φ z))
    (lam : Λ) (hlam : N lam ∈ Λ') :
    conjT A s cc hs ℓ (α (1 ⊗ₜ lam)) = α' (1 ⊗ₜ ⟨N lam, hlam⟩) := by
  apply Subtype.ext; funext n
  apply Additive.toMul.injective
  apply toC_injective (conjVar A s) emb
  change toC (conjVar A s) emb (conjPt A s cc hs (Additive.toMul ((α (1 ⊗ₜ lam)).1 n))) = _
  rw [hα', toC_conjPt A s cc hs emb hι h, hα, ← hN]
  congr 1
  have e : ∀ v : Fin g → ℂ, ((ℓ : ℂ) ^ n)⁻¹ • v = (((ℓ : ℝ) ^ n)⁻¹ : ℝ) • v := fun v => by
    ext i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast; rfl
  rw [e, e, map_smul]

/-! ## §8. The linear algebra of the lattice argument (proved)

The lattices replace the abstract `H` of `ConjBettiComparison`: with `ℤ`-bases of `Λ_A`, `Λ_B`,
the matrices of `c_*` and of `V_ℓ(f)` on `ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)` (through `ℚ_ℓ ⊗ α`, §10) are the
integer matrices of the lifts `N` and `M_f` on the lattices (§7). Faltings puts the first in the `ℚ_ℓ`-span of the others,
rationality (`matrix_mem_of_map_mem_span`) in their `ℚ`-span, so `N` is a `ℚ`-combination of
`ℂ`-linear maps on a basis of `ℂ^g` over `ℝ`, hence `ℂ`-linear; it is antilinear and nonzero. -/

section LatticeAlgebra

open Module

/-- **A lattice map determines the real-linear map (proved).** -/
theorem toLin_of_lattice {g : ℕ} {ΛA ΛB : Submodule ℤ (Fin g → ℂ)} {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
    (bA : Basis ιA ℤ ΛA) (bB : Basis ιB ℤ ΛB) (bAℝ : Basis ιA ℝ (Fin g → ℂ))
    (bBℝ : Basis ιB ℝ (Fin g → ℂ)) (hbA : ∀ i, bAℝ i = bA i) (hbB : ∀ i, bBℝ i = bB i)
    (u : ΛA →ₗ[ℤ] ΛB) (Y : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (hu : ∀ lam, (u lam : Fin g → ℂ) = Y lam) :
    Matrix.toLin bAℝ bBℝ ((LinearMap.toMatrix bA bB u).map (Int.castRingHom ℝ)) = Y := by
  apply bAℝ.ext; intro j
  rw [Matrix.toLin_self, hbA j, ← hu]
  conv_rhs => rw [← bB.sum_repr (u (bA j))]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, hbB i, Submodule.coe_smul, eq_intCast,
    Int.cast_smul_eq_zsmul]

/-- **The lattice contradiction (proved).** If the integer matrix of an antilinear nonzero `N`
lies in the `E`-span (`E ⊇ ℚ`) of the integer matrices of `ℂ`-linear maps `M_f`, then `False`. -/
theorem lattice_contradiction {g : ℕ} {ΛA ΛB : Submodule ℤ (Fin g → ℂ)} {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
    (bA : Basis ιA ℤ ΛA) (bB : Basis ιB ℤ ΛB) (bAℝ : Basis ιA ℝ (Fin g → ℂ))
    (bBℝ : Basis ιB ℝ (Fin g → ℂ)) (hbA : ∀ i, bAℝ i = bA i) (hbB : ∀ i, bBℝ i = bB i)
    (E : Type*) [Field E] [CharZero E] {S : Type*} (uM : S → (ΛA →ₗ[ℤ] ΛB))
    (M : S → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (hM : ∀ f lam, (uM f lam : Fin g → ℂ) = M f lam)
    (uN : ΛA →ₗ[ℤ] ΛB) (N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (hN : ∀ lam, (uN lam : Fin g → ℂ) = N lam)
    (hanti : ∀ z, N (Complex.I • z) = -(Complex.I • N z)) (hN0 : N ≠ 0)
    (hspan : (LinearMap.toMatrix bA bB uN).map (Int.castRingHom E) ∈ Submodule.span E
      (Set.range fun f => (LinearMap.toMatrix bA bB (uM f)).map (Int.castRingHom E))) :
    False := by
  let W : Submodule ℚ (Matrix ιB ιA ℚ) := Submodule.span ℚ
    (Set.range fun f => (LinearMap.toMatrix bA bB (uM f)).map (Int.castRingHom ℚ))
  have hmapE : ∀ X : Matrix ιB ιA ℤ,
      (X.map (Int.castRingHom ℚ)).map (algebraMap ℚ E) = X.map (Int.castRingHom E) := by
    intro X; rw [Matrix.map_map]; congr 1; ext x; simp
  have hmapR : ∀ X : Matrix ιB ιA ℤ,
      (X.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) = X.map (Int.castRingHom ℝ) := by
    intro X; rw [Matrix.map_map]; congr 1
  have hXN : (LinearMap.toMatrix bA bB uN).map (Int.castRingHom ℚ) ∈ W := by
    apply matrix_mem_of_map_mem_span (E := E)
    rw [hmapE]
    refine Submodule.span_mono ?_ hspan
    rintro _ ⟨f, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨f, rfl⟩, hmapE _⟩
  have hP : ∀ X ∈ W, ∀ z, Matrix.toLin bAℝ bBℝ (X.map (algebraMap ℚ ℝ)) (Complex.I • z) =
      Complex.I • Matrix.toLin bAℝ bBℝ (X.map (algebraMap ℚ ℝ)) z := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      intro z
      rw [hmapR, toLin_of_lattice bA bB bAℝ bBℝ hbA hbB (uM f) ((M f).restrictScalars ℝ)
        (hM f)]
      exact (M f).map_smul Complex.I z
    | zero => intro z; simp
    | add x y _ _ hx hy =>
      intro z
      have e : (x + y).map (algebraMap ℚ ℝ) = x.map (algebraMap ℚ ℝ) + y.map (algebraMap ℚ ℝ) :=
        Matrix.map_add _ (map_add _) x y
      rw [e, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy, smul_add]
    | smul q x _ hx =>
      intro z
      have e : (q • x).map (algebraMap ℚ ℝ) = (q : ℝ) • x.map (algebraMap ℚ ℝ) := by
        ext i j; simp [Matrix.map_apply, Algebra.smul_def]
      rw [e, LinearEquiv.map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hx, smul_comm]
  have hNlin := hP _ hXN
  rw [hmapR, toLin_of_lattice bA bB bAℝ bBℝ hbA hbB uN N hN] at hNlin
  apply hN0
  apply LinearMap.ext; intro z
  have h1 : Complex.I • N z = -(Complex.I • N z) := (hNlin z).symm.trans (hanti z)
  have h2 : Complex.I • N z = 0 := by
    have : (2 : ℂ) • (Complex.I • N z) = 0 := by
      rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel _
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.mp h2).resolve_left Complex.I_ne_zero

end LatticeAlgebra

/-- `twistC` maps `1` to `1` (proved). -/
theorem twistC_one {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : twistC A σ s h 1 = 1 := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ 1) = 1
  rw [MonObj.comp_one, MonObj.comp_one, Adjunction.homEquiv_unit, Functor.map_one,
    MonObj.comp_one]
  rfl

/-! ## §9. N5 `ConjVarDim` (proved) -/

/-- A ring endomorphism of a number field is bijective. -/
theorem ringHom_bijective_of_numberField (K : Type) [Field K] [NumberField K] (s : K →+* K) :
    Function.Bijective s := by
  have hinj : Function.Injective s := s.injective
  refine ⟨hinj, ?_⟩
  have h := (LinearMap.injective_iff_surjective (f := s.toRatAlgHom.toLinearMap)).mp hinj
  exact h

/-- **N5 (proved).** For a number field, `dim A^s = dim A`: `Spec(s)` is an isomorphism, so the
projection `A^s → A` is an isomorphism of schemes, hence a homeomorphism. -/
theorem conjVarDim : ConjVarDim := by
  intro K _ _ A s
  have hb := ringHom_bijective_of_numberField K s
  let e : K ≃+* K := RingEquiv.ofBijective s hb
  haveI : IsIso (CommRingCat.ofHom s) :=
    ⟨⟨CommRingCat.ofHom (e.symm : K →+* K), by ext x; exact e.symm_apply_apply x,
      by ext x; exact e.apply_symm_apply x⟩⟩
  have : IsIso (specS s) := by unfold specS; infer_instance
  change topologicalKrullDim (conjVar A s).X.left = topologicalKrullDim A.X.left
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.Hom.homeomorph (Limits.pullback.fst A.X.hom (specS s))).isHomeomorph

/-! ## §9b. N3 from N2 and a smaller glue N3a (proved reduction)

`ConjAntiLiftLat` is N3 for number fields and full lattices (all that §10 uses). It follows from
N2 (`HomLinearLift` for the identity of `A^s`) and N3a (`ConjUniformization`): the conjugate
`z ↦ twistC(Φ z̄)` of a uniformization of `A(ℂ)_σ` is a uniformization of `A^s(ℂ)_σ`. -/

/-- Complex conjugation on `ℂ^g`, as an `ℝ`-linear map. -/
def conjL (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun z i := starRingEnd ℂ (z i)
  map_add' z w := by funext i; simp
  map_smul' r z := by funext i; simp

theorem conjL_conjL {g : ℕ} (z : Fin g → ℂ) : conjL g (conjL g z) = z := by
  funext i; simp [conjL]

theorem conjL_I {g : ℕ} (z : Fin g → ℂ) :
    conjL g (Complex.I • z) = -(Complex.I • conjL g z) := by
  funext i; simp [conjL]

/-- **N3a. The conjugate of a uniformization (GLUE, unproved; STANDARD).** If `σ ∘ s = conj ∘ σ`
and `Φ` uniformizes `A(ℂ)_σ` with kernel `Λ`, then `z ↦ twistC(Φ(z̄))` uniformizes `A^s(ℂ)_σ`
with kernel `Λ̄ = {z | z̄ ∈ Λ}`. (`A^s(ℂ)_σ = A(ℂ)_{σ∘s} = A(ℂ)_{conj∘σ}`, and on affine charts
`twistC` conjugates the values of regular functions, so `z ↦ s(twistC(Φ z̄)) = conj(s'(Φ z))`-type
compositions are holomorphic; the group-theoretic clauses follow from `twistC` being a bijective
homomorphism.) -/
def ConjUniformization : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    IsUniformization σ (Λ.comap ((conjL g).restrictScalars ℤ))
      (fun z => twistC A σ s h (Φ (conjL g z)))

/-- **N3 for number fields and full lattices (GLUE; implied by `ConjAntiLift`).** -/
def ConjAntiLiftLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) (Φ' : (Fin g → ℂ) → CPts (conjVar A s) σ),
    A.dim = (g : WithBot ℕ∞) → ∀ [DiscreteTopology Λ], IsZLattice ℝ Λ →
    IsUniformization σ Λ Φ → IsUniformization σ Λ' Φ' →
    ∃ N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ z, N (Complex.I • z) = -(Complex.I • N z)) ∧
      Function.Injective N ∧ ∀ z, Φ' (N z) = twistC A σ s h (Φ z)

theorem conjAntiLiftLat_of_conjAntiLift (h : ConjAntiLift) : ConjAntiLiftLat :=
  fun K _ _ A σ s hs g Λ Λ' Φ Φ' hd _ _ hΦ hΦ' => h K A σ s hs g Λ Λ' Φ Φ' hd hΦ hΦ'

/-- `Spec(conj)` back from `σ` to `σ ∘ s`. -/
def conjHomInv {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : cptObj σ ⟶ cptObj (σ.comp s) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) (by
    simp only [cptObj, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    congr 2
    ext x
    simp)

/-- The inverse of `mapPtIso`. -/
def mapPtIsoInv {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K) :
    cptObj (σ.comp s) ⟶ (Over.map (specS s)).obj (cptObj σ) :=
  Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_hom, cptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

theorem twistC_inj_aux {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) :
    conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
    Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) = 𝟙 _
  rw [Category.id_comp, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

/-- `twistC` is injective (proved). -/
theorem twistC_injective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : Function.Injective (twistC A σ s h) := by
  intro Q Q' hQ
  have h1 : mapPtIso σ s ≫ conjHom σ s h ≫ Q = mapPtIso σ s ≫ conjHom σ s h ≫ Q' :=
    ((Over.mapPullbackAdj (specS s)).homEquiv _ _).injective hQ
  calc Q = (conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h) ≫ Q := by
        rw [twistC_inj_aux, Category.id_comp]
    _ = conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ (mapPtIso σ s ≫ conjHom σ s h ≫ Q) := by
        simp only [Category.assoc]
    _ = conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ (mapPtIso σ s ≫ conjHom σ s h ≫ Q') := by
        rw [h1]
    _ = (conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h) ≫ Q' := by
        simp only [Category.assoc]
    _ = Q' := by rw [twistC_inj_aux, Category.id_comp]

/-- A vector all of whose real multiples lie in a full lattice is `0` (proved). -/
theorem eq_zero_of_real_smul_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (z : Fin g → ℂ) (hz : ∀ t : ℝ, t • z ∈ Λ) : z = 0 := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  let bℝ := b.ofZLatticeBasis ℝ Λ
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, bℝ.repr z j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (bℝ.repr.injective (Finsupp.ext fun j => by simp [hall j]))
  have hmem := hz (2 * bℝ.repr z j)⁻¹
  have e1 : bℝ.repr ((2 * bℝ.repr z j)⁻¹ • z) j = 1 / 2 := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    field_simp
  have e2 : bℝ.repr ((2 * bℝ.repr z j)⁻¹ • z) j = (b.repr ⟨_, hmem⟩ j : ℝ) :=
    Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b ⟨_, hmem⟩ j
  rw [e1] at e2
  have : (2 : ℝ) * (b.repr ⟨_, hmem⟩ j : ℝ) = 1 := by rw [← e2]; norm_num
  have h3 : (2 * b.repr ⟨_, hmem⟩ j : ℤ) = 1 := by exact_mod_cast this
  omega

/-- **`ConjAntiLiftLat` from N2 and N3a (proved).** -/
theorem conjAntiLiftLat_of (hN2 : HomLinearLift) (hN3a : ConjUniformization) :
    ConjAntiLiftLat := by
  intro K _ _ A σ s h g Λ Λ' Φ Φ' hd _ hlat hΦ hΦ'
  have hd' : (conjVar A s).dim = (g : WithBot ℕ∞) := by rw [conjVarDim]; exact hd
  have hψ := hN3a K A σ s h g Λ Φ hd hΦ
  obtain ⟨M, hM⟩ := hN2 K (conjVar A s) (conjVar A s) σ g g _ Λ' _ Φ' hd' hd' hψ hΦ' 1
  have hM' : ∀ z, Φ' (M z) = twistC A σ s h (Φ (conjL g z)) := fun z => by
    rw [hM z]; exact Category.comp_id _
  refine ⟨(M.restrictScalars ℝ) ∘ₗ conjL g, fun z => ?_, ?_, fun z => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [conjL_I, map_neg, M.map_smul]
  · intro z w hzw
    have key : ∀ v, M (conjL g v) = 0 → v = 0 := by
      intro v hv
      apply eq_zero_of_real_smul_mem Λ v
      intro t
      rw [← hΦ.2.1]
      apply twistC_injective A σ s h
      rw [twistC_one, ← conjL_conjL (t • v), ← hM', map_smul, ← Complex.coe_smul,
        M.map_smul, hv, smul_zero]
      exact (hΦ'.2.1 0).mpr (Submodule.zero_mem _)
    have : M (conjL g (z - w)) = 0 := by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars] at hzw
      rw [map_sub, map_sub, hzw, sub_self]
    exact sub_eq_zero.mp (key _ this)
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [hM', conjL_conjL]

/-! ## §10. A weaker N4 suffices: an injective comparison (proved reduction)

Only injectivity of `α` is used: `ℚ_ℓ` is flat over `ℤ_ℓ`, so `ι = ℚ_ℓ ⊗ α` is injective, and
postcomposition with `ι_B` is injective on `Hom` spaces. The matrices are then taken on
`ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)`, where `c_*` and `V_ℓ(f)` become the base changes of `N|_Λ` and `M_f|_Λ`. -/

/-- **N4' (GLUE; weaker than `TateLattice`).** As `TateLattice` with `α` only an injective
`ℤ_ℓ`-linear map. -/
def TateLatticeInj : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))),
    A.dim = (g : WithBot ℕ∞) → ∀ [DiscreteTopology Λ], IsZLattice ℝ Λ →
    IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ α : TensorProduct ℤ ℤ_[ℓ] Λ →ₗ[ℤ_[ℓ]] A.T ℓ,
      Function.Injective α ∧
      ∀ (lam : Λ) (n : ℕ), toC A emb (Additive.toMul ((α (1 ⊗ₜ lam)).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ))

theorem tateLatticeInj_of_tateLattice (h : TateLattice) : TateLatticeInj := by
  intro K _ A emb g Λ Φ hd _ hlat hΦ ℓ _
  obtain ⟨α, hα⟩ := h K A emb g Λ Φ hd hlat hΦ ℓ
  exact ⟨α.toLinearMap, α.injective, hα⟩

/-- **`ConjTwistNontrivial` from T26, T35, N2, N3 and N4' (proved).** -/
theorem conjTwistNontrivial_of_latticeInj (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLiftLat) (hN4 : TateLatticeInj) : ConjTwistNontrivial := by
  classical
  intro hF K _ _ _ A ℓ _ hdim c hc hall
  obtain ⟨cc, emb, hι, hK, h2, hres⟩ := conjData K c hc
  let s := restrictK cc hK
  have hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k) := restrictK_spec cc hK
  let σ : K →+* ℂ := emb.comp (algebraMap K (AlgebraicClosure K))
  have hσs : σ.comp s = (starRingEnd ℂ).comp σ := by
    apply RingHom.ext; intro k
    change emb (algebraMap K _ (s k)) = starRingEnd ℂ (emb (algebraMap K _ k))
    rw [← hs, hι]
  have hd2 : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hd2' : (conjVar A s).dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [conjVarDim]; exact hd2
  obtain ⟨ΛA, ΦA, hdA, hlatA, hA⟩ := h35 K A σ 2 hd2
  obtain ⟨ΛB, ΦB, hdB, hlatB, hB⟩ := h35 K (conjVar A s) σ 2 hd2'
  obtain ⟨N, hNanti, hNinj, hN⟩ := hN3 K A σ s hσs 2 ΛA ΛB ΦA ΦB hd2 hlatA hA hB
  obtain ⟨αA, -, hαA⟩ := hN4 K A emb 2 ΛA ΦA hd2 hlatA hA ℓ
  obtain ⟨αB, hαBinj, hαB⟩ := hN4 K (conjVar A s) emb 2 ΛB ΦB hd2' hlatB hB ℓ
  choose M hM using fun f => hN2 K A (conjVar A s) σ 2 2 ΛA ΛB ΦA ΦB hd2 hd2' hA hB f
  have heq : ∀ τ, conjV A s cc hs ℓ ∘ₗ A.galRep ℓ τ =
      (conjVar A s).galRep ℓ τ ∘ₗ conjV A s cc hs ℓ := by
    intro τ
    obtain ⟨σ', hσ'⟩ := exists_twist K cc hK h2 τ
    rw [hall σ' τ (hres σ' τ hσ'), conjV_galRep A s cc hs ℓ σ' τ hσ']
  have hspan := faltingsV hF hT A (conjVar A s) ℓ _ heq
  have hNlat : ∀ lam : ΛA, N lam ∈ ΛB := fun lam => by
    rw [← hB.2.1, hN, (hA.2.1 _).mpr lam.2]
    exact twistC_one A σ s hσs
  have hMlat : ∀ f (lam : ΛA), M f lam ∈ ΛB := fun f lam =>
    lift_mem_lattice hA hB f (M f) (hM f) lam
  let uN : ΛA →ₗ[ℤ] ΛB :=
    { toFun := fun lam => ⟨N lam, hNlat lam⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by
        simp only [RingHom.id_apply, Submodule.coe_smul]; exact map_zsmul N n _) }
  let uM : PkgI3.AbVar.Hom A (conjVar A s) → (ΛA →ₗ[ℤ] ΛB) := fun f =>
    { toFun := fun lam => ⟨M f lam, hMlat f lam⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by
        simp only [RingHom.id_apply, Submodule.coe_smul]; exact map_zsmul (M f) n _) }
  have hCN : ∀ lam, conjT A s cc hs ℓ (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ uN lam) := fun lam =>
    conjT_tateLattice A s cc hs emb hι hσs ℓ αA hαA αB hαB N hN lam (hNlat lam)
  have hMf : ∀ f lam, PkgI3.AbVar.homT f (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ uM f lam) :=
    fun f lam => homT_tateLattice emb ℓ αA hαA αB hαB f (M f) (hM f) lam (hMlat f lam)
  -- `ℚ_ℓ ⊗ α`
  let ιA := αA.baseChange ℚ_[ℓ]
  let ιB := αB.baseChange ℚ_[ℓ]
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  have hιB : Function.Injective ιB := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ_[ℓ]) αB hαBinj
    rwa [← LinearMap.baseChange_eq_lTensor] at this
  let lift : (ΛA →ₗ[ℤ] ΛB) → (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]]
      ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛB)) := fun u => (u.baseChange ℤ_[ℓ]).baseChange ℚ_[ℓ]
  have hcomp : ∀ (Tm : A.T ℓ →ₗ[ℤ_[ℓ]] (conjVar A s).T ℓ) (u : ΛA →ₗ[ℤ] ΛB),
      (∀ lam, Tm (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ u lam)) →
      Tm.baseChange ℚ_[ℓ] ∘ₗ ιA = ιB ∘ₗ lift u := by
    intro Tm u h
    simp only [ιA, ιB, lift, ← LinearMap.baseChange_comp]
    congr 1
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    apply LinearMap.ext
    intro lam
    change Tm (αA (1 ⊗ₜ lam)) = αB ((u.baseChange ℤ_[ℓ]) (1 ⊗ₜ lam))
    rw [h, LinearMap.baseChange_tmul]
  let Pre : (A.V ℓ →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ) →ₗ[ℚ_[ℓ]]
      (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ) :=
    { toFun := fun X => X ∘ₗ ιA
      map_add' := fun X Y => LinearMap.add_comp _ _ _
      map_smul' := fun a X => LinearMap.smul_comp _ _ _ }
  let Post : (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛB)) →ₗ[ℚ_[ℓ]]
      (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ) :=
    { toFun := fun Y => ιB ∘ₗ Y
      map_add' := fun X Y => LinearMap.comp_add _ _ _
      map_smul' := fun a X => LinearMap.comp_smul _ _ _ }
  have hPost : Function.Injective Post := fun Y Y' h =>
    LinearMap.ext fun x => hιB (LinearMap.congr_fun h x)
  have key : lift uN ∈ Submodule.span ℚ_[ℓ] (Set.range fun f => lift (uM f)) := by
    have h1 := Submodule.mem_map_of_mem (f := Pre) hspan
    rw [homSpanV, Submodule.map_span, ← Set.range_comp] at h1
    have e1 : (⇑Pre ∘ fun f : PkgI3.AbVar.Hom A (conjVar A s) =>
        (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ]) = ⇑Post ∘ fun f => lift (uM f) := by
      funext f
      exact hcomp _ _ (hMf f)
    have e2 : Pre (conjV A s cc hs ℓ) = Post (lift uN) := hcomp _ _ hCN
    rw [e1, Set.range_comp, ← Submodule.map_span, e2] at h1
    obtain ⟨y, hy, hyN⟩ := h1
    rwa [hPost hyN] at hy
  -- bases and matrices
  haveI := ZLattice.module_finite ℝ ΛA
  haveI := ZLattice.module_free ℝ ΛA
  haveI := ZLattice.module_finite ℝ ΛB
  haveI := ZLattice.module_free ℝ ΛB
  let bA := Module.Free.chooseBasis ℤ ΛA
  let bB := Module.Free.chooseBasis ℤ ΛB
  let bAℝ := bA.ofZLatticeBasis ℝ ΛA
  let bBℝ := bB.ofZLatticeBasis ℝ ΛB
  let TM := LinearMap.toMatrix (Algebra.TensorProduct.basis ℚ_[ℓ]
      (Algebra.TensorProduct.basis ℤ_[ℓ] bA))
    (Algebra.TensorProduct.basis ℚ_[ℓ] (Algebra.TensorProduct.basis ℤ_[ℓ] bB))
  have hTM : ∀ u, TM (lift u) = (LinearMap.toMatrix bA bB u).map (Int.castRingHom ℚ_[ℓ]) := by
    intro u
    simp only [TM, lift, LinearMap.toMatrix_baseChange, Matrix.map_map]
    congr 1
  have hspan' : (LinearMap.toMatrix bA bB uN).map (Int.castRingHom ℚ_[ℓ]) ∈
      Submodule.span ℚ_[ℓ]
        (Set.range fun f => (LinearMap.toMatrix bA bB (uM f)).map (Int.castRingHom ℚ_[ℓ])) := by
    have h1 := Submodule.mem_map_of_mem (f := TM.toLinearMap) key
    rw [Submodule.map_span, ← Set.range_comp] at h1
    rw [← hTM]
    convert h1 using 3
    funext f
    exact (hTM (uM f)).symm
  have hN0 : N ≠ 0 := by
    intro h0
    have : (Pi.single 0 1 : Fin 2 → ℂ) = 0 := hNinj (by rw [h0]; simp)
    have := congrFun this 0
    simp at this
  exact lattice_contradiction bA bB bAℝ bBℝ (fun i => by simp [bAℝ]) (fun i => by simp [bBℝ])
    ℚ_[ℓ] uM M (fun f lam => rfl) uN N (fun lam => rfl) hNanti hN0 hspan'

/-- **`ConjTwistNontrivial` from T26, T35, N2, N3 and N4 (proved; N5 is proved).** -/
theorem conjTwistNontrivial_of_lattice (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) (hN4 : TateLattice) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN2 (conjAntiLiftLat_of_conjAntiLift hN3)
    (tateLatticeInj_of_tateLattice hN4)

/-- **`ConjTwistFromLeaves` from N2, N3, N4' (proved):** T35 and T26 are among its
hypotheses. -/
theorem conjTwistFromLeaves_of_latticeInj (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) (hN4 : TateLatticeInj) : ConjTwistFromLeaves :=
  fun _ _ h35 _ hT => conjTwistNontrivial_of_latticeInj hT h35 hN2
    (conjAntiLiftLat_of_conjAntiLift hN3) hN4

/-- **`ConjTwistFromLeaves` from N2, N3, N4 (proved).** -/
theorem conjTwistFromLeaves_of_lattice (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) (hN4 : TateLattice) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_latticeInj hN2 hN3 (tateLatticeInj_of_tateLattice hN4)

/-! ## §11. N4' from N1 (proved): the injective comparison `ℤ_ℓ ⊗ Λ → T_ℓ(A)`

`x(λ)ₙ` is the unique `K̄`-point with `toC(x(λ)ₙ) = Φ(ℓ⁻ⁿλ)` (N1); `λ ↦ x(λ)` is additive, and its
`ℤ_ℓ`-linear extension is injective: if `Σ aᵢ x(bᵢ) = 0`, then `Φ(ℓ⁻ⁿ Σ (aᵢ mod ℓⁿ) bᵢ) = 1`, so
`Σ (aᵢ mod ℓⁿ) bᵢ ∈ ℓⁿΛ` and `ℓⁿ ∣ (aᵢ mod ℓⁿ)`, for every `n`. -/

section TateLatticeProof

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) {g : ℕ}
  (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))

theorem phi_zero (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  have := congrArg (fun x => (Φ 0)⁻¹ * x) h
  simp only [inv_mul_cancel, inv_mul_cancel_left] at this
  exact this.symm

theorem phi_nsmul (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (k : ℕ) (z : Fin g → ℂ) :
    Φ (k • z) = Φ z ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero, phi_zero A emb Φ hadd]
  | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem phi_sum (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) {J : Type*} (s : Finset J)
    (f : J → (Fin g → ℂ)) : Φ (∑ i ∈ s, f i) = ∏ i ∈ s, Φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phi_zero A emb Φ hadd]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem ell_ne_zero : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.out.ne_zero

theorem smul_inv_pow (n : ℕ) (v : Fin g → ℂ) : (ℓ ^ n : ℕ) • (((ℓ : ℂ) ^ n)⁻¹ • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  push_cast
  rw [mul_inv_cancel₀ (pow_ne_zero _ (ell_ne_zero ℓ)), one_smul]

theorem smul_inv_succ (n : ℕ) (v : Fin g → ℂ) :
    ℓ • (((ℓ : ℂ) ^ (n + 1))⁻¹ • v) = ((ℓ : ℂ) ^ n)⁻¹ • v := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have := ell_ne_zero ℓ
  field_simp
  ring

variable {Λ : Submodule ℤ (Fin g → ℂ)}
  (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)

include hadd hker in
theorem phi_tors (lam : Λ) (n : ℕ) : Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)) ^ (ℓ ^ n) = 1 := by
  rw [← phi_nsmul A emb Φ hadd, smul_inv_pow, (hker _).mpr lam.2]

variable (hsurj : ∀ n : ℕ, 0 < n → ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))),
    Q ^ n = 1 → ∃ P, toC A emb P = Q)

/-- `x(λ)ₙ ∈ A(K̄)` with `toC(x(λ)ₙ) = Φ(ℓ⁻ⁿλ)`. -/
def xPt (lam : Λ) (n : ℕ) : A.Pt (AlgebraicClosure K) :=
  Classical.choose (hsurj (ℓ ^ n) (pow_pos hℓ.out.pos n) _
    (phi_tors A emb Φ ℓ hadd hker lam n))

theorem xPt_spec (lam : Λ) (n : ℕ) :
    toC A emb (xPt A emb Φ ℓ hadd hker hsurj lam n) = Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)) :=
  Classical.choose_spec (hsurj (ℓ ^ n) (pow_pos hℓ.out.pos n) _
    (phi_tors A emb Φ ℓ hadd hker lam n))

/-- `x(λ) ∈ T_ℓ(A)`. -/
def xSeq (lam : Λ) : A.T ℓ :=
  ⟨fun n => Additive.ofMul (xPt A emb Φ ℓ hadd hker hsurj lam n), by
    refine ⟨?_, fun n => ?_⟩
    · apply Additive.toMul.injective
      change xPt A emb Φ ℓ hadd hker hsurj lam 0 = 1
      apply toC_injective A emb
      rw [xPt_spec, map_one, pow_zero, inv_one, one_smul]
      exact (hker _).mpr lam.2
    · apply Additive.toMul.injective
      change xPt A emb Φ ℓ hadd hker hsurj lam (n + 1) ^ ℓ = xPt A emb Φ ℓ hadd hker hsurj lam n
      apply toC_injective A emb
      rw [map_pow, xPt_spec, xPt_spec, ← phi_nsmul A emb Φ hadd, smul_inv_succ]⟩

theorem xSeq_apply (lam : Λ) (n : ℕ) :
    toC A emb (Additive.toMul ((xSeq A emb Φ ℓ hadd hker hsurj lam).1 n)) =
      Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)) :=
  xPt_spec A emb Φ ℓ hadd hker hsurj lam n

/-- `λ ↦ x(λ)`, additive. -/
def xHom : Λ →+ A.T ℓ :=
  AddMonoidHom.mk' (xSeq A emb Φ ℓ hadd hker hsurj) (fun a b => by
    apply Subtype.ext; funext n
    apply Additive.toMul.injective
    apply toC_injective A emb
    change toC A emb (Additive.toMul ((xSeq A emb Φ ℓ hadd hker hsurj (a + b)).1 n)) =
      toC A emb (Additive.toMul ((xSeq A emb Φ ℓ hadd hker hsurj a).1 n) *
        Additive.toMul ((xSeq A emb Φ ℓ hadd hker hsurj b).1 n))
    rw [map_mul, xSeq_apply, xSeq_apply, xSeq_apply, ← hadd, Submodule.coe_add, smul_add])

/-- `λ ↦ x(λ)`, `ℤ`-linear. -/
def xLin : Λ →ₗ[ℤ] A.T ℓ :=
  { xHom A emb Φ ℓ hadd hker hsurj with
    map_smul' := fun n x => by
      simp only [RingHom.id_apply]
      exact map_zsmul (xHom A emb Φ ℓ hadd hker hsurj) n x }

end TateLatticeProof

section TateLatticeInjProof

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) {g : ℕ}
  (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {Λ : Submodule ℤ (Fin g → ℂ)}
  (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
  (hsurj : ∀ n : ℕ, 0 < n → ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))),
    Q ^ n = 1 → ∃ P, toC A emb P = Q)

/-- **Injectivity of the comparison (proved from N1).** -/
theorem xLin_liftBaseChange_injective [Module.Free ℤ Λ] [Module.Finite ℤ Λ] :
    Function.Injective ((xLin A emb Φ ℓ hadd hker hsurj).liftBaseChange ℤ_[ℓ]) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let bZ := Algebra.TensorProduct.basis ℤ_[ℓ] b
  set α := (xLin A emb Φ ℓ hadd hker hsurj).liftBaseChange ℤ_[ℓ] with hαdef
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  apply bZ.repr.injective
  refine Finsupp.ext fun j => ?_
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [map_zero]
  set a : Module.Free.ChooseBasisIndex ℤ Λ → ℤ_[ℓ] := fun i => bZ.repr v i with ha
  set k : Module.Free.ChooseBasisIndex ℤ Λ → ℕ := fun i => (PadicInt.toZModPow n (a i)).val
    with hk
  have hαv : α v = ∑ i, a i • xLin A emb Φ ℓ hadd hker hsurj (b i) := by
    conv_lhs => rw [← bZ.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.TensorProduct.basis_apply, hαdef, LinearMap.liftBaseChange_one_tmul]
  have hent : Additive.toMul ((α v).1 n) =
      ∏ i, Additive.toMul ((xLin A emb Φ ℓ hadd hker hsurj (b i)).1 n) ^ k i := by
    rw [hαv, AddSubgroup.val_finset_sum, Finset.sum_apply, toMul_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [PkgI3.Tate.smul_apply, toMul_nsmul]
  have h0 : Additive.toMul ((α v).1 n) = 1 := by rw [hv]; rfl
  let w : Λ := ∑ i, k i • b i
  have hC : Φ (((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ)) = 1 := by
    have e1 : toC A emb (Additive.toMul ((α v).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ)) := by
      rw [hent, map_prod]
      simp only [map_pow]
      have e2 : ∀ i, toC A emb (Additive.toMul ((xLin A emb Φ ℓ hadd hker hsurj (b i)).1 n)) =
          Φ (((ℓ : ℂ) ^ n)⁻¹ • ((b i : Λ) : Fin g → ℂ)) := fun i =>
        xSeq_apply A emb Φ ℓ hadd hker hsurj (b i) n
      simp only [e2, ← phi_nsmul A emb Φ hadd]
      rw [← phi_sum A emb Φ hadd]
      congr 1
      simp only [w, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
    rw [← e1, h0, map_one]
  have hw : ((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ) ∈ Λ := (hker _).mp hC
  let mu : Λ := ⟨((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ), hw⟩
  have hwμ : w = (ℓ ^ n : ℕ) • mu := by
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower]
    exact (smul_inv_pow ℓ n (w : Fin g → ℂ)).symm
  have hrepr := congrArg (fun x => b.repr x j) hwμ
  simp only [w, map_sum, map_nsmul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hrepr
  have hdvd : (ℓ ^ n : ℕ) ∣ k j := by
    have h1 : ((ℓ ^ n : ℕ) : ℤ) ∣ ((k j : ℕ) : ℤ) := by
      refine ⟨b.repr mu j, ?_⟩
      simpa [nsmul_eq_mul] using hrepr
    exact Int.natCast_dvd_natCast.mp h1
  have hlt : k j < ℓ ^ n := ZMod.val_lt _
  exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hdvd hlt)

end TateLatticeInjProof

/-- **N4' from N1 (proved).** -/
theorem tateLatticeInj_of_artinTorsion (hN1 : ArtinTorsion) : TateLatticeInj := by
  intro K _ A emb g Λ Φ _ _ hlat hΦ ℓ _
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  have hsurj := fun n hn => (hN1 K A emb n hn).2
  refine ⟨(xLin A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj).liftBaseChange ℤ_[ℓ],
    xLin_liftBaseChange_injective A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj, fun lam n => ?_⟩
  rw [LinearMap.liftBaseChange_one_tmul]
  exact xSeq_apply A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj lam n

/-- **`ConjTwistNontrivial` from T26, T35, N1, N2, N3 (proved).** -/
theorem conjTwistNontrivial_of_N123 (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN2 (conjAntiLiftLat_of_conjAntiLift hN3)
    (tateLatticeInj_of_artinTorsion hN1)

/-- **`ConjTwistFromLeaves` from N1, N2, N3 (proved).** -/
theorem conjTwistFromLeaves_of_N123 (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_latticeInj hN2 hN3 (tateLatticeInj_of_artinTorsion hN1)

/-! ## §12. The injectivity half of N1 (proved)

`Spec ℂ → Spec K̄` is surjective, hence dominant, `Spec K̄` is reduced and `A → Spec K` is
separated (proper), so two `K̄`-points agreeing after `Spec ℂ → Spec K̄` are equal (Mathlib's
`ext_of_isDominant_of_isSeparated`). What remains of N1 is the torsion surjectivity. -/

/-- **N1-surj. Torsion comparison, surjectivity (GLUE, unproved; STANDARD).** Every `n`-torsion
point of `A(ℂ)_{ι∘alg}` (`n ≥ 1`) comes from `A(K̄)`. (`toC` is injective, `toC_injective`; both
`A(K̄)[n]` and `A(ℂ)[n]` have `n^{2g}` elements, by T5 over `K̄` and over `ℂ`; equivalently `A[n]`
is finite étale in characteristic `0`. Mumford §4, §6, UNVERIFIED numbers.) -/
def ArtinTorsionSurj : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (n : ℕ), 0 < n →
    ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))), Q ^ n = 1 →
      ∃ P, toC A emb P = Q

theorem artinTorsion_of_surj (h : ArtinTorsionSurj) : ArtinTorsion :=
  fun K _ A emb n hn => ⟨toC_injective A emb, h K A emb n hn⟩

/-- **`ConjTwistNontrivial` from T26, T35, N1-surj, N2, N3 (proved).** -/
theorem conjTwistNontrivial_of_surj (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_N123 hT h35 (artinTorsion_of_surj hS) hN2 hN3

/-- **`ConjTwistFromLeaves` from N1-surj, N2, N3 (proved).** -/
theorem conjTwistFromLeaves_of_surj (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_N123 (artinTorsion_of_surj hS) hN2 hN3

/-- **Main result: `ConjTwistNontrivial` from T26, T35, N1-surj, N2 and N3a (proved).** -/
theorem conjTwistNontrivial_main (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3a : ConjUniformization) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN2
    (conjAntiLiftLat_of hN2 hN3a) (tateLatticeInj_of_artinTorsion (artinTorsion_of_surj hS))

/-- **Main result: `ConjTwistFromLeaves` from N1-surj, N2 and N3a (proved).** -/
theorem conjTwistFromLeaves_main (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3a : ConjUniformization) : ConjTwistFromLeaves :=
  fun _ _ h35 _ hT => conjTwistNontrivial_main hT h35 hS hN2 hN3a

/-! ## §13. N1-surj from T5 and a uniformization (proved)

Given a uniformization `Φ : ℂ^g → A(ℂ)_σ` with full lattice `Λ`, `A(ℂ)[n]` injects into
`(ℤ/n)^{2g}` (`Q = Φ(z) ↦` the coordinates of `nz ∈ Λ` mod `n`), and `A(K̄)[n] ≅ (ℤ/n)^{2g}` by T5
(`PkgI2.TorsionStructure`). `toC` is injective, so it is a bijection on `n`-torsion. -/

/-- **Torsion surjectivity from T5 (proved).** -/
theorem torsion_surj_of_T5 (h5 : PkgI2.TorsionStructure.{0}) {K : Type} [Field K]
    (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))
    (hΦ : IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ)
    (hd : A.dim = (g : WithBot ℕ∞)) (n : ℕ) (hn : 0 < n)
    (Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))) (hQ : Q ^ n = 1) :
    ∃ P, toC A emb P = Q := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  have hnK : (n : K) ≠ 0 := by
    intro h0
    have := congrArg (emb.comp (algebraMap K (AlgebraicClosure K))) h0
    rw [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.mpr hn.ne') this
  obtain ⟨e, -⟩ := h5 K (ObjBridge.toGrp A) g n hd hn hnK
  let S := {P : A.Pt (AlgebraicClosure K) // P ^ n = 1}
  let T := {Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))) // Q ^ n = 1}
  let f : S → T := fun P => ⟨toC A emb P.1, by rw [← map_pow, P.2, map_one]⟩
  have hf : Function.Injective f := fun P P' h =>
    Subtype.ext (toC_injective A emb (congrArg Subtype.val h))
  have hpre : ∀ Q : T, ∃ z, Φ z = Q.1 := fun Q => hΦ.2.2.1 Q.1
  choose zz hzz using hpre
  have hnz : ∀ Q : T, n • zz Q ∈ Λ := fun Q => by
    rw [← hΦ.2.1, phi_nsmul A emb Φ hΦ.1, hzz, Q.2]
  let code : T → (Module.Free.ChooseBasisIndex ℤ Λ → ZMod n) := fun Q i =>
    ((b.repr ⟨n • zz Q, hnz Q⟩ i : ℤ) : ZMod n)
  have hcode : Function.Injective code := by
    intro Q Q' hQQ
    have hdvd : ∀ i, (n : ℤ) ∣ b.repr ⟨n • zz Q', hnz Q'⟩ i - b.repr ⟨n • zz Q, hnz Q⟩ i :=
      fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hQQ i)
    choose k hk using hdvd
    let mu : Λ := ∑ i, k i • b i
    have hmu : (⟨n • zz Q', hnz Q'⟩ : Λ) - ⟨n • zz Q, hnz Q⟩ = (n : ℤ) • mu := by
      apply b.repr.injective
      refine Finsupp.ext fun i => ?_
      rw [map_sub, Finsupp.sub_apply, hk i, map_smul, Finsupp.smul_apply, smul_eq_mul]
      congr 1
      exact (congrFun (b.repr_sum_self k) i).symm
    have hvec : n • zz Q' - n • zz Q = (n : ℤ) • (mu : Fin g → ℂ) := by
      have := congrArg Subtype.val hmu
      simpa using this
    have e3 : (n : ℂ) • (zz Q' - zz Q) = (n : ℂ) • (mu : Fin g → ℂ) := by
      rw [smul_sub, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hvec,
        natCast_zsmul]
    have e4 : zz Q' - zz Q = mu :=
      smul_right_injective (Fin g → ℂ) (Nat.cast_ne_zero.mpr hn.ne' : (n : ℂ) ≠ 0) e3
    apply Subtype.ext
    rw [← hzz Q, ← hzz Q', show zz Q' = zz Q + mu by rw [← e4]; abel, hΦ.1,
      (hΦ.2.1 _).mpr mu.2, _root_.mul_one]
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Finite T := Finite.of_injective code hcode
  have hcardS : Nat.card S = n ^ (2 * g) := by
    have hSe : Nat.card S = Nat.card (Fin (2 * g) → ZMod n) := Nat.card_congr e
    rw [hSe, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcardT : Nat.card T ≤ n ^ (2 * g) := by
    have h1 := Nat.card_le_card_of_injective code hcode
    rw [Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex ℤ Λ),
      ← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ Λ,
      Module.finrank_pi_fintype] at h1
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h1
    simpa [mul_comm] using h1
  have hbij := hf.bijective_of_nat_card_le (hcardS ▸ hcardT)
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, congrArg Subtype.val hP⟩

/-- **N4' from T5 (proved).** -/
theorem tateLatticeInj_of_T5 (h5 : PkgI2.TorsionStructure.{0}) : TateLatticeInj := by
  intro K _ A emb g Λ Φ hd _ hlat hΦ ℓ _
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  have hsurj := fun n hn Q hQ => torsion_surj_of_T5 h5 A emb g Λ Φ hΦ hd n hn Q hQ
  refine ⟨(xLin A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj).liftBaseChange ℤ_[ℓ],
    xLin_liftBaseChange_injective A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj, fun lam n => ?_⟩
  rw [LinearMap.liftBaseChange_one_tmul]
  exact xSeq_apply A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj lam n

/-- **Final: `ConjTwistNontrivial` from T5, T26, T35, N2 and N3a (proved).** -/
theorem conjTwistNontrivial_final (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) (hN3a : ConjUniformization) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN2 (conjAntiLiftLat_of hN2 hN3a)
    (tateLatticeInj_of_T5 h5)

/-- **Final: `ConjTwistFromLeaves` from N2 and N3a (proved).** T5, T26 and T35 are among the
hypotheses of `ConjTwistFromLeaves`. -/
theorem conjTwistFromLeaves_final (hN2 : HomLinearLift) (hN3a : ConjUniformization) :
    ConjTwistFromLeaves :=
  fun _ _ h35 h5 hT => conjTwistNontrivial_final h5 hT h35 hN2 hN3a

end G0Galois

#print axioms G0Galois.faltingsV
#print axioms G0Galois.conjData
#print axioms G0Galois.conjTwistNontrivial_of_conjBettiData
#print axioms G0Galois.conjTwistFromLeaves_of_conjBettiData
#print axioms G0Galois.conjV_galRep
#print axioms G0Galois.conjBettiData_of_comparison
#print axioms G0Galois.conjTwistNontrivial_of_comparison
#print axioms G0Galois.conjTwistFromLeaves_of_comparison
#print axioms G0Galois.toC_conjPt
#print axioms G0Galois.homT_tateLattice
#print axioms G0Galois.conjT_tateLattice
#print axioms G0Galois.lattice_contradiction
#print axioms G0Galois.conjTwistNontrivial_of_lattice
#print axioms G0Galois.conjTwistFromLeaves_of_lattice
#print axioms G0Galois.conjVarDim
#print axioms G0Galois.conjTwistNontrivial_of_latticeInj
#print axioms G0Galois.conjTwistFromLeaves_of_latticeInj
#print axioms G0Galois.tateLatticeInj_of_artinTorsion
#print axioms G0Galois.conjTwistNontrivial_of_N123
#print axioms G0Galois.conjTwistFromLeaves_of_N123
#print axioms G0Galois.toC_injective
#print axioms G0Galois.conjTwistNontrivial_of_surj
#print axioms G0Galois.conjTwistFromLeaves_of_surj
#print axioms G0Galois.conjAntiLiftLat_of
#print axioms G0Galois.conjTwistNontrivial_main
#print axioms G0Galois.conjTwistFromLeaves_main
#print axioms G0Galois.torsion_surj_of_T5
#print axioms G0Galois.conjTwistNontrivial_final
#print axioms G0Galois.conjTwistFromLeaves_final
