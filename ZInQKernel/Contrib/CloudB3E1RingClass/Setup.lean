import ZInQKernel.Contrib.CloudB3E1RingClass.ClassGen

/-!
# The setup of the genuine moving data: chosen primes, support sets, a place over each prime

Manuscript `diophantine_zq.tex`, tex 3528–3534 (the chosen primes in distinct conjugate pairs) and
tex 3566, 3676 (the excluded primes).

`RingClassSetup.mk'` builds a `RingClassSetup` from any family of chosen primes `𝔭_j`, `𝔭̄_j` with
`𝔭_j 𝔭̄_j = (p_j)` and an old support `S₀`:
* the support at the moving prime `r` is `S_r = S₀ ∪ {v : r ∈ v}`, which contains every prime over
  `r` (`hSr`);
* the place over `r` is a maximal ideal containing `r`, chosen when `r` is not a unit.

Facts:
* `placeR_over'`: for a prime `r`, the chosen place lies over `r`. This is the input `placeR_over`.
* `p_mem_excl`: with the excluded set `excl p T₀ = T₀ ∪ {p_j}`, the input `p_mem` holds.
* `cls_gen_setup`: when the family contains split generators of `Cl(K)` (as produced by
  `exists_split_generators_distinct`), `cls_gen` holds.
* `exists_setup`: a setup with generating split primes in distinct conjugate pairs outside `T`,
  with `cls_gen` and `placeR_over`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- A natural number `> 1` is not a unit in `𝒪_K`. Kind: PROVED. -/
theorem natCast_not_isUnit {r : ℕ} (hr : 1 < r) : ¬ IsUnit (r : 𝓞 K) := by
  intro h
  have h1 : Ideal.absNorm (Ideal.span {(r : 𝓞 K)}) = 1 := by
    rw [Ideal.span_singleton_eq_top.mpr h, Ideal.absNorm_top]
  rw [Ideal.absNorm_span_singleton, show (r : 𝓞 K) = algebraMap ℤ (𝓞 K) (r : ℤ) by simp,
    Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h1
  rcases Nat.pow_eq_one.mp h1 with h2 | h2
  · omega
  · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 K)).ne' h2

theorem natCast_ne_zero' {r : ℕ} (hr : 0 < r) : (r : 𝓞 K) ≠ 0 := by
  exact_mod_cast hr.ne'

theorem exists_place_over {r : ℕ} (hr : 1 < r) :
    ∃ w : HeightOneSpectrum (𝓞 K), (r : 𝓞 K) ∈ w.asIdeal := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(r : 𝓞 K)})
    (fun h => natCast_not_isUnit hr (Ideal.span_singleton_eq_top.mp h))
  have hrM : (r : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, fun h0 => ?_⟩, hrM⟩
  rw [h0, Ideal.mem_bot] at hrM
  exact natCast_ne_zero' (K := K) (by omega) hrM

/-- **A place over `r`**, for `r > 1`; the given place `w₀` otherwise. Kind: definition. -/
def placeOver (r : ℕ) (w₀ : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) := by
  classical
  exact if h : 1 < r then (exists_place_over (K := K) h).choose else w₀

theorem placeOver_spec {r : ℕ} (hr : 1 < r) (w₀ : HeightOneSpectrum (𝓞 K)) :
    (r : 𝓞 K) ∈ (placeOver r w₀).asIdeal := by
  classical
  rw [placeOver, dite_eq_left_of_eq_true (eq_true hr)]
  exact (exists_place_over (K := K) hr).choose_spec

/-- **The setup from a family of chosen primes and an old support** (tex 3528–3534):
`S_r = S₀ ∪ {v : max r 1 ∈ v}` and the place over `r` from `placeOver`. Kind: definition. -/
def RingClassSetup.mk' {s : ℕ} (𝔭 𝔭bar : Fin s → HeightOneSpectrum (𝓞 K)) (p : Fin s → ℕ)
    (hp : ∀ j, (p j).Prime)
    (hmul : ∀ j, (𝔭 j).asIdeal * (𝔭bar j).asIdeal = Ideal.span {(((p j : ℤ)) : 𝓞 K)})
    (S₀ : Set (HeightOneSpectrum (𝓞 K))) (w₀ : HeightOneSpectrum (𝓞 K)) : RingClassSetup K s where
  𝔭 := 𝔭
  𝔭bar := 𝔭bar
  p := p
  p_prime := hp
  𝔭_mul := hmul
  Sr r := S₀ ∪ {v | ((max r 1 : ℕ) : 𝓞 K) ∈ v.asIdeal}
  hSr _ _ hv := Or.inr hv
  placeR r := placeOver r w₀

/-- **The place over a prime `r` lies over `r`** (the input `placeR_over`). Kind: PROVED. -/
theorem placeR_over' {s : ℕ} {𝔭 𝔭bar : Fin s → HeightOneSpectrum (𝓞 K)} {p : Fin s → ℕ}
    {hp : ∀ j, (p j).Prime}
    {hmul : ∀ j, (𝔭 j).asIdeal * (𝔭bar j).asIdeal = Ideal.span {(((p j : ℤ)) : 𝓞 K)}}
    {S₀ : Set (HeightOneSpectrum (𝓞 K))} {w₀ : HeightOneSpectrum (𝓞 K)} {r : ℕ} (hr : r.Prime) :
    ((r : ℤ) : 𝓞 K) ∈ ((RingClassSetup.mk' 𝔭 𝔭bar p hp hmul S₀ w₀).placeR r).asIdeal := by
  rw [Int.cast_natCast]
  exact placeOver_spec hr.one_lt w₀

/-- **The excluded primes** `T₀ ∪ {p_j}`. Kind: definition. -/
def excl {s : ℕ} (p : Fin s → ℕ) (T₀ : Finset ℕ) : Finset ℕ :=
  T₀ ∪ Finset.univ.image p

/-- The rational primes under the chosen primes are excluded (the input `p_mem`). Kind: PROVED. -/
theorem p_mem_excl {s : ℕ} (p : Fin s → ℕ) (T₀ : Finset ℕ) (j : Fin s) : p j ∈ excl p T₀ :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))

/-- **`cls_gen` for a setup whose chosen primes contain a generating family** (tex 3532–3534).
Kind: PROVED. -/
theorem cls_gen_setup {s : ℕ} (C : RingClassSetup K s)
    (hgen : Subgroup.closure (Set.range fun j =>
      ClassGroup.mk0 ⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩) = ⊤) :
    ∀ c : Additive (ClassGroup (𝓞 K)), ∃ v : Fin s → ℤ, ∑ j, v j • setupCls C j = c :=
  clsGen_of_closure C hgen

/-- **A setup with generating split primes in distinct conjugate pairs outside `T`** (tex
3528–3534): from `exists_split_generators_distinct`. The chosen primes generate `Cl(K)`, lie over
pairwise distinct rational primes and avoid `T`. Kind: PROVED. -/
theorem exists_setup (hK : Module.finrank ℚ K = 2) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (S₀ : Set (HeightOneSpectrum (𝓞 K))) (w₀ : HeightOneSpectrum (𝓞 K)) :
    ∃ (s : ℕ) (C : RingClassSetup K s), Function.Injective C.p ∧ (∀ j, C.𝔭 j ≠ C.𝔭bar j) ∧
      (∀ j, C.𝔭 j ∉ T ∧ C.𝔭bar j ∉ T) ∧
      (∀ c : Additive (ClassGroup (𝓞 K)), ∃ v : Fin s → ℤ, ∑ j, v j • setupCls C j = c) ∧
      ∀ r, r.Prime → ((r : ℤ) : 𝓞 K) ∈ (C.placeR r).asIdeal := by
  obtain ⟨s, 𝔭, 𝔭bar, p, hp, hinj, hne, hT, hmul, hcl⟩ := exists_split_generators_distinct hK T
  let C := RingClassSetup.mk' 𝔭 𝔭bar p hp hmul S₀ w₀
  exact ⟨s, C, hinj, hne, hT, cls_gen_setup C hcl, fun r hr => placeR_over' hr⟩

end ZInQ.Contrib.CloudB3E1RingClass
