import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Perm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Tame descent for a finite normal group of operators

Linear-algebra engine of a tame-descent proof that wild inertia acts trivially on
the rational Tate module of an abelian variety with semistable reduction.

* `isNilpotent_of_spectrum_zero`: over an algebraically closed field, an
  endomorphism of a finite-dimensional space whose spectrum is contained in `{0}`
  is nilpotent.
* `exists_pow_isNilpotent_sub_one`: Grothendieck's quasi-unipotence lemma. If an
  invertible operator `T` is conjugate to `T ^ q` with `q ≥ 2`, some positive power
  of `T` is unipotent.
* `fixed_of_unipotent_normalizer`: if a finite group `Q` of operators is normalized
  by `T`, `T ^ m` is unipotent, and every `T ^ m`-fixed vector is `Q`-fixed, then
  `Q` acts trivially (characteristic zero).
* `exists_pow_isNilpotent_sub_one_of_field`: quasi-unipotence over any field, by
  passing to an algebraic closure.
* `fixed_of_tame_descent`: the two combined, over any field of characteristic zero.
-/

noncomputable section
set_option autoImplicit false

open Polynomial Module

namespace WildTameDescent

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Over an algebraically closed field, an endomorphism of a finite-dimensional
space whose eigenvalues all vanish is nilpotent: its minimal polynomial splits
with all roots zero, so it is a power of `X`. -/
theorem isNilpotent_of_spectrum_zero [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) (h : ∀ μ ∈ spectrum K f, μ = 0) : IsNilpotent f := by
  have hint : IsIntegral K f := Algebra.IsIntegral.isIntegral f
  have hmon : (minpoly K f).Monic := minpoly.monic hint
  have hsplit := (IsAlgClosed.splits (minpoly K f)).eq_prod_roots_of_monic hmon
  have hroots : (minpoly K f).roots.map (fun r => X - C r) =
      (minpoly K f).roots.map (fun _ => (X : K[X])) := by
    apply Multiset.map_congr rfl
    intro r hr
    have hroot : (minpoly K f).IsRoot r := (mem_roots hmon.ne_zero).1 hr
    have hr0 : r = 0 := h r (Module.End.hasEigenvalue_iff_mem_spectrum.1
      (Module.End.hasEigenvalue_iff_isRoot.2 hroot))
    simp [hr0]
  refine ⟨Multiset.card (minpoly K f).roots, ?_⟩
  have h0 : aeval f ((minpoly K f).roots.map (fun r => X - C r)).prod = 0 := by
    rw [← hsplit]
    exact minpoly.aeval K f
  rw [hroots, Multiset.map_const', Multiset.prod_replicate, map_pow, aeval_X] at h0
  exact h0

/-- **Grothendieck's quasi-unipotence lemma.** Over an algebraically closed field,
if an invertible endomorphism `T` of a finite-dimensional space is conjugate to
`T ^ q` with `q ≥ 2`, then some positive power of `T` is unipotent. The spectrum
of `T` is a finite set of nonzero scalars permuted by `λ ↦ λ ^ q`; a power of that
permutation is the identity, so every eigenvalue is a root of unity of a common
order `m`. -/
theorem exists_pow_isNilpotent_sub_one [IsAlgClosed K] [FiniteDimensional K V]
    (S T : (Module.End K V)ˣ) (q : ℕ) (hq : 2 ≤ q)
    (hST : (S : Module.End K V) * T * (S⁻¹ : (Module.End K V)ˣ) = (T : Module.End K V) ^ q) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent ((T : Module.End K V) ^ m - 1) := by
  set t : Module.End K V := (T : Module.End K V) with ht
  set s : Set K := spectrum K t with hs
  have hfin : s.Finite := Module.End.finite_spectrum t
  have : Finite s := hfin.to_subtype
  have hq0 : 0 < q := by omega
  -- the spectrum is stable under `λ ↦ λ ^ q`
  have himage : (fun x : K => x ^ q) '' s = s := by
    rw [hs, ← spectrum.map_pow_of_pos t hq0, ← hST, spectrum.units_conjugate]
  have hzero : (0 : K) ∉ s := spectrum.zero_notMem K T.isUnit
  have hmaps : ∀ x ∈ s, x ^ q ∈ s := fun x hx => himage ▸ Set.mem_image_of_mem _ hx
  let f : s → s := fun x => ⟨x.1 ^ q, hmaps x.1 x.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← himage] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hsurj
  let e : Equiv.Perm s := Equiv.ofBijective f ⟨hinj, hsurj⟩
  set N := orderOf e with hN
  have hNpos : 0 < N := (isOfFinOrder_of_finite e).orderOf_pos
  have hpow : ∀ k : ℕ, ∀ x : s, ((e ^ k) x).1 = x.1 ^ (q ^ k) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      change ((e ^ k) x).1 ^ q = _
      rw [ih x, ← pow_mul, pow_succ]
  have hperiod : ∀ x ∈ s, x ^ (q ^ N) = x := by
    intro x hx
    have h1 := hpow N ⟨x, hx⟩
    rw [hN, pow_orderOf_eq_one, Equiv.Perm.one_apply] at h1
    exact h1.symm
  have hqN : 2 ≤ q ^ N := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ N := Nat.pow_le_pow_right hq0 hNpos
  refine ⟨q ^ N - 1, by omega, ?_⟩
  have hroot : ∀ x ∈ s, x ^ (q ^ N - 1) = 1 := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => hzero (h ▸ hx)
    have h1 : x ^ (q ^ N - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q ^ N), one_mul]
      exact hperiod x hx
    exact mul_right_cancel₀ hx0 h1
  apply isNilpotent_of_spectrum_zero
  intro μ hμ
  have hdeg : 0 < degree ((X : K[X]) ^ (q ^ N - 1) - C 1) := by
    rw [degree_X_pow_sub_C (by omega : 0 < q ^ N - 1)]
    exact_mod_cast (by omega : 0 < q ^ N - 1)
  have haeval : aeval t ((X : K[X]) ^ (q ^ N - 1) - C 1) = t ^ (q ^ N - 1) - 1 := by
    simp
  rw [← haeval, spectrum.map_polynomial_aeval_of_degree_pos t _ hdeg] at hμ
  obtain ⟨x, hx, rfl⟩ := hμ
  simp [hroot x hx]

/-- The averaging operator of a finite group of operators. -/
def average {ι : Type*} [Fintype ι] (g : ι → Module.End K V) : Module.End K V :=
  ((Fintype.card ι : K)⁻¹) • ∑ i, g i

/-- **Descent engine.** In characteristic zero, let `Q` be a finite group of
invertible operators normalized by `T`. If `T ^ m - 1` is nilpotent and every
`T ^ m`-fixed vector is `Q`-fixed, then `Q` acts trivially. Proof: the averaging
projector `e` of `Q` commutes with `T`; on its kernel `T ^ m` is unipotent, so a
nonzero kernel vector would produce a nonzero `T ^ m`-fixed vector in the kernel,
which is `Q`-fixed, hence fixed by `e`, a contradiction. -/
theorem fixed_of_unipotent_normalizer [CharZero K] (Q : Subgroup (Module.End K V)ˣ) [Fintype Q]
    (T : (Module.End K V)ˣ) (hT : T ∈ Subgroup.normalizer (Q : Set (Module.End K V)ˣ)) (m : ℕ)
    (hnil : IsNilpotent ((T : Module.End K V) ^ m - 1))
    (hfix : ∀ v : V, ((T : Module.End K V) ^ m) v = v →
      ∀ g ∈ Q, (g : Module.End K V) v = v) :
    ∀ g ∈ Q, ∀ v : V, (g : Module.End K V) v = v := by
  classical
  set e : Module.End K V := average (fun g : Q => ((g : (Module.End K V)ˣ) : Module.End K V))
    with he
  have hcard : (Fintype.card Q : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- `e` fixes `Q`-fixed vectors
  have he_fix : ∀ v : V, (∀ g ∈ Q, (g : Module.End K V) v = v) → e v = v := by
    intro v hv
    rw [he, average, LinearMap.smul_apply, LinearMap.sum_apply]
    have : ∀ g : Q, ((g : (Module.End K V)ˣ) : Module.End K V) v = v := fun g => hv g g.2
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  -- elements of `Q` absorb `e`
  have hg_e : ∀ g ∈ Q, ∀ v : V, (g : Module.End K V) (e v) = e v := by
    intro g hg v
    rw [he, average, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    congr 1
    let σ : Q ≃ Q := Equiv.mulLeft (⟨g, hg⟩ : Q)
    rw [← σ.sum_comp (fun d : Q => ((d : (Module.End K V)ˣ) : Module.End K V) v)]
    exact Finset.sum_congr rfl fun i _ => rfl
  -- `T` commutes with `e`
  have hTe : ∀ v : V, (T : Module.End K V) (e v) = e ((T : Module.End K V) v) := by
    intro v
    rw [he, average, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
      LinearMap.smul_apply, LinearMap.sum_apply]
    congr 1
    have hmem : ∀ h : Q, T * (h : (Module.End K V)ˣ) * T⁻¹ ∈ Q := fun h =>
      (Subgroup.mem_normalizer_iff.mp hT h).mp h.2
    have hmem' : ∀ h : Q, T⁻¹ * (h : (Module.End K V)ˣ) * T ∈ Q := by
      intro h
      apply (Subgroup.mem_normalizer_iff.mp hT _).mpr
      simp [mul_assoc]
    let σ : Q ≃ Q :=
      { toFun := fun h => ⟨T * h * T⁻¹, hmem h⟩
        invFun := fun h => ⟨T⁻¹ * h * T, hmem' h⟩
        left_inv := fun h => by ext1; simp [mul_assoc]
        right_inv := fun h => by ext1; simp [mul_assoc] }
    have hTinv : ∀ x : V,
        ((T⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((T : Module.End K V) x) = x := by
      intro x
      rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
    rw [← σ.sum_comp (fun d : Q => ((d : (Module.End K V)ˣ) : Module.End K V)
      ((T : Module.End K V) v))]
    refine Finset.sum_congr rfl fun h _ => ?_
    change _ = ((T * h * T⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((T : Module.End K V) v)
    simp only [Units.val_mul, Module.End.mul_apply, hTinv]
  have hTje : ∀ j : ℕ, ∀ v : V,
      ((T : Module.End K V) ^ j) (e v) = e (((T : Module.End K V) ^ j) v) := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, hTe, ih]
  set n : Module.End K V := (T : Module.End K V) ^ m - 1 with hn
  have hNe : ∀ v : V, n (e v) = e (n v) := by
    intro v
    rw [hn, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      hTje m v, map_sub]
  -- a vector killed by `e` and by a power of `n` vanishes
  have key : ∀ k : ℕ, ∀ y : V, e y = 0 → (n ^ k) y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y _ hy; simpa using hy
    | succ k ih =>
      intro y hey hy
      have hny : n y = 0 := by
        apply ih (n y)
        · rw [← hNe, hey, map_zero]
        · rw [← Module.End.mul_apply, ← pow_succ]; exact hy
      have hTy : ((T : Module.End K V) ^ m) y = y := by
        have h2 := hny
        rw [hn, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h2
        exact h2
      have hy' := he_fix y (hfix y hTy)
      rw [hey] at hy'
      exact hy'.symm
  obtain ⟨k, hk⟩ := hnil
  intro g hg v
  have hee : e (e v) = e v := he_fix (e v) (fun g' hg' => hg_e g' hg' v)
  have hy : v - e v = 0 := by
    apply key k (v - e v)
    · rw [map_sub, hee, sub_self]
    · rw [hk, LinearMap.zero_apply]
  have hv : v = e v := sub_eq_zero.mp hy
  rw [hv, hg_e g hg v]

/-- **Quasi-unipotence over an arbitrary field.** The hypotheses and the conclusion
are transported along the injective ring map from endomorphisms of `V` to
endomorphisms of `n`-tuples over an algebraic closure (choice of a basis, then
extension of scalars of matrices); nilpotence is reflected by injective maps. -/
theorem exists_pow_isNilpotent_sub_one_of_field [FiniteDimensional K V]
    (S T : (Module.End K V)ˣ) (q : ℕ) (hq : 2 ≤ q)
    (hST : (S : Module.End K V) * T * (S⁻¹ : (Module.End K V)ˣ) = (T : Module.End K V) ^ q) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent ((T : Module.End K V) ^ m - 1) := by
  classical
  let b := Module.finBasis K V
  let L := AlgebraicClosure K
  let ψ : Module.End K V →+* Module.End L (Fin (Module.finrank K V) → L) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) L ≃ₐ[L]
        _).toRingEquiv.toRingHom).comp
      (((algebraMap K L).mapMatrix).comp (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom)
  have hψ : Function.Injective ψ := by
    refine (Matrix.toLinAlgEquiv' (R := L)).injective.comp ?_
    refine (Matrix.map_injective (algebraMap K L).injective).comp ?_
    exact (LinearMap.toMatrixAlgEquiv b).injective
  have key : ψ (S : Module.End K V) * ψ (T : Module.End K V) *
      ψ ((S⁻¹ : (Module.End K V)ˣ) : Module.End K V) = (ψ (T : Module.End K V)) ^ q := by
    rw [← map_mul, ← map_mul, hST, map_pow]
  let ψm : Module.End K V →* Module.End L (Fin (Module.finrank K V) → L) := ψ.toMonoidHom
  obtain ⟨m, hm, hnil⟩ := exists_pow_isNilpotent_sub_one (K := L)
    (Units.map ψm S) (Units.map ψm T) q hq key
  refine ⟨m, hm, ?_⟩
  rw [← IsNilpotent.map_iff hψ, map_sub, map_pow, map_one]
  exact hnil

/-- **Tame descent.** Over an algebraically closed field of characteristic zero,
let `Q` be a finite group of operators on a finite-dimensional space, normalized
by an invertible `T` which is conjugate to `T ^ q` (`q ≥ 2`). If for every
positive `m` each `T ^ m`-fixed vector is `Q`-fixed, then `Q` acts trivially. -/
theorem fixed_of_tame_descent [IsAlgClosed K] [CharZero K] [FiniteDimensional K V]
    (Q : Subgroup (Module.End K V)ˣ) [Fintype Q]
    (S T : (Module.End K V)ˣ) (q : ℕ) (hq : 2 ≤ q)
    (hST : (S : Module.End K V) * T * (S⁻¹ : (Module.End K V)ˣ) = (T : Module.End K V) ^ q)
    (hT : T ∈ Subgroup.normalizer (Q : Set (Module.End K V)ˣ))
    (hrigid : ∀ m : ℕ, 0 < m → ∀ v : V, ((T : Module.End K V) ^ m) v = v →
      ∀ g ∈ Q, (g : Module.End K V) v = v) :
    ∀ g ∈ Q, ∀ v : V, (g : Module.End K V) v = v := by
  obtain ⟨m, hm, hnil⟩ := exists_pow_isNilpotent_sub_one S T q hq hST
  exact fixed_of_unipotent_normalizer Q T hT m hnil (hrigid m hm)

end WildTameDescent

namespace WildTameDescent

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Tame descent over any field of characteristic zero** (for instance `ℚ_ℓ`):
a finite group `Q` of operators normalized by an invertible `T` conjugate to
`T ^ q` (`q ≥ 2`) acts trivially as soon as, for every positive `m`, each
`T ^ m`-fixed vector is `Q`-fixed. -/
theorem fixed_of_tame_descent_field [CharZero K] [FiniteDimensional K V]
    (Q : Subgroup (Module.End K V)ˣ) [Fintype Q]
    (S T : (Module.End K V)ˣ) (q : ℕ) (hq : 2 ≤ q)
    (hST : (S : Module.End K V) * T * (S⁻¹ : (Module.End K V)ˣ) = (T : Module.End K V) ^ q)
    (hT : T ∈ Subgroup.normalizer (Q : Set (Module.End K V)ˣ))
    (hrigid : ∀ m : ℕ, 0 < m → ∀ v : V, ((T : Module.End K V) ^ m) v = v →
      ∀ g ∈ Q, (g : Module.End K V) v = v) :
    ∀ g ∈ Q, ∀ v : V, (g : Module.End K V) v = v := by
  obtain ⟨m, hm, hnil⟩ := exists_pow_isNilpotent_sub_one_of_field S T q hq hST
  exact fixed_of_unipotent_normalizer Q T hT m hnil (hrigid m hm)

end WildTameDescent
