import ZInQKernel.Contrib.OneProof.MinpolyIndepCharP
import ZInQKernel.Contrib.AVB1.AlgClosed

/-! # charpoly-hf: `MinpolyIndepOfEllCharP` is a consequence of Mumford §19 Thm 3 in characteristic `p`

Task charpoly-hf (2026-11-16), report `docs/research/charpoly-hf.md`. Not on the route: this file certifies that
the statement `ZInQ.Contrib.OneProof.CharpolyHF.MinpolyIndepOfEllCharP` is a consequence of a printed theorem.

* `HomFreeFiniteAlgClosedCharP`: Mumford §19 Thm 3 (printed form, `k` algebraically closed) restricted to
  characteristic `p > 0`;
* `minpolyIndepOfEllCharP_of_homFree (hH : HomFreeFiniteAlgClosedCharP) (hT : PkgI3.TateModuleFree) :
  MinpolyIndepOfEllCharP`: `m` is the minimal polynomial of `1 ⊗ α` in `End⁰(A)`; the descent from `k̄` to `k`
  is av-b1's (`bcHom_injective`, `tateBC_bijective_closure`, flatness of `ℤ_ℓ`); the polynomial argument is
  charpoly-charp's `exists_minpoly_endE` at `E = ℚ_ℓ` (copied, with the hypotheses at one abelian variety).

No `sorry`, no `axiom`.
-/

open Polynomial Module

noncomputable section

namespace ZInQ.Contrib.OneProof.CharpolyHF

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
