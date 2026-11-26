import ZInQKernel.Contrib.OneProof.DeligneY3Bridges.Similitude

/-!
# The PEL condition on a level structure is automatic (`eq_smul_E0K`)

Deligne, *Travaux de Shimura*, Scholie 4.11 (c), p. 148: the level datum of a point of
`_K M_ℂ(G, h₀)` is "une classe mod K, k̄, de similitudes symplectiques L-linéaires
k : V̂(A) ≅ V ⊗ 𝔸^f". The kernel's level structure (`LevelPrint`) is only `𝒪`-linear. This file
shows that for `L = B = (2, −3 | ℚ)` the symplectic condition is automatic, one prime at a time:
over every field `K` of characteristic `0` (e.g. `ℚ_ℓ`), every alternating `K`-bilinear form on
`B ⊗ K` for which `B ⊗ K` acts with adjoint `x† = μ⁻¹ x̄ μ` is a scalar multiple of `ψ`
(`eq_smul_E0K`). Pulled back along a `B`-linear isomorphism `η : B ⊗ K ≅ W` from a form on `W` with
the same adjoint (the Weil pairing of a polarization inducing `†`), the form is `c ψ`, and
`c ≠ 0` if the form on `W` is not zero (`level_similitude`).

`BK`, `muK`, `muInvK`, `dagK`, `E0K`, `decompK` and `eq_smul_E0K` are ported from the file
`ZInQKernel/Contrib/OneProof/ShimuraY3StrictLemmaP.lean` of this repository's branch
`wip/y3abu-strict` (head `e0197d03acee9946ebfa74617cf661ec77238665`, section `LevelCompat`),
with these changes only: the namespace, line breaks, shortened docstrings (the docstring of
`muK` and `muInvK` split in two), and an `omit [CharZero K] in` before `decompK`. The proofs are
unchanged. `psi_eq_E0K` identifies `E0K` with `ψ` of `DeligneY3Bridges.Similitude`.
-/

noncomputable section

namespace DeligneY3Bridges.LevelCompat

variable {K : Type} [Field K] [CharZero K]

/-- `B ⊗ K` for `B = (2, −3 | ℚ)` (Mathlib's `QuaternionAlgebra K 2 0 (−3)`). -/
abbrev BK (K : Type) [Field K] := QuaternionAlgebra K 2 0 (-3)

/-- `μ = 2j + k` in `B ⊗ K`. -/
def muK : BK K := ⟨0, 0, 2, 1⟩

/-- `μ⁻¹ = −μ/6` in `B ⊗ K`. -/
def muInvK : BK K := ⟨0, 0, -1/3, -1/6⟩

/-- The Rosati involution of type `μ`, `x† = μ⁻¹ x̄ μ`, on `B ⊗ K`. -/
def dagK (x : BK K) : BK K := muInvK * star x * muK

/-- `E₀ ⊗ K = trd(μ⁻¹ x ȳ)` on `B ⊗ K` (the PEL datum's symplectic form `ψ`). -/
def E0K (x y : BK K) : K := 2 * (muInvK * x * star y).re

omit [CharZero K] in
theorem decompK (z : BK K) :
    z = z.re • (1 : BK K) + z.imI • (⟨0, 1, 0, 0⟩ : BK K) + z.imJ • (⟨0, 0, 1, 0⟩ : BK K) +
      z.imK • (⟨0, 0, 0, 1⟩ : BK K) := by
  ext <;> simp

/-- **Level compatibility is automatic (over any field `K` of characteristic 0, e.g. `ℚ_ℓ`).**
Every alternating `K`-bilinear form on `B ⊗ K` for which `B ⊗ K` acts with adjoint `†` (type `μ`)
is a scalar multiple of `ψ = E₀ ⊗ K`. -/
theorem eq_smul_E0K (E : LinearMap.BilinForm K (BK K)) (halt : ∀ x, E x x = 0)
    (hros : ∀ a x y, E (a * x) y = E x (dagK a * y)) :
    ∃ c : K, ∀ x y, E x y = c * E0K x y := by
  set f : BK K →ₗ[K] K := E 1 with hf
  have hE : ∀ x y, E x y = f (dagK x * y) := by
    intro x y; rw [hf, ← hros x 1 y, mul_one]
  have hf0 : ∀ x, f (dagK x * x) = 0 := fun x => by rw [← hE]; exact halt x
  have d1 : dagK (1 : BK K) * 1 = 1 := by
    simp only [dagK, muInvK, muK]; ext <;> simp <;> norm_num
  have r1 : f 1 = 0 := by simpa [d1] using hf0 1
  have e2 : dagK (⟨1, 1, 0, 0⟩ : BK K) * ⟨1, 1, 0, 0⟩ =
      (3 : K) • (1 : BK K) + (2 : K) • ⟨0, 1, 0, 0⟩ := by
    simp only [dagK, muInvK, muK]; ext <;> simp <;> norm_num
  have e3 : dagK (⟨1, 0, 1, 0⟩ : BK K) * ⟨1, 0, 1, 0⟩ =
      (10 : K) • (1 : BK K) + (6 : K) • ⟨0, 1, 0, 0⟩
      + (-2 : K) • (⟨0, 0, 1, 0⟩ + ⟨0, 0, 0, 1⟩) := by
    simp only [dagK, muInvK, muK]; ext <;> simp <;> norm_num
  have r2 : f ⟨0, 1, 0, 0⟩ = 0 := by
    have := hf0 ⟨1, 1, 0, 0⟩
    rw [e2, map_add, map_smul, map_smul, r1] at this
    simp at this
    exact this
  have r3 : f ⟨0, 0, 0, 1⟩ = - f ⟨0, 0, 1, 0⟩ := by
    have := hf0 ⟨1, 0, 1, 0⟩
    rw [e3, map_add, map_add, map_smul, map_smul, map_smul, map_add, r1, r2] at this
    simp at this
    linear_combination this
  refine ⟨-(f ⟨0, 0, 1, 0⟩) / 2, fun x y => ?_⟩
  rw [hE, decompK (dagK x * y)]
  simp only [map_add, map_smul, r1, r2, r3, smul_eq_mul]
  simp only [E0K, dagK, muInvK, muK]
  simp
  ring

/-- **`E0K` is Deligne's `ψ` over `K`** (`DeligneY3Bridges.psi`, with `R = K`). -/
theorem psi_eq_E0K (x y : BK K) : psi K x y = E0K x y := by
  simp only [psi, E0K, muInv, muInvK]
  congr 3
  ext <;> simp

/-- **The PEL level condition is automatic.** Let `W` be a `K`-vector space with an action
`ι : B ⊗ K → End_K W` and an alternating form `e` for which `ι(a)` has adjoint `ι(a†)` (the
Weil pairing of a polarization inducing `†`), and let `η : B ⊗ K → W` be `K`-linear and
`B`-linear (`η(a x) = ι(a)(η x)`). Then `e(η x, η y) = c ψ(x, y)` for one `c ∈ K`, and `c ≠ 0`
as soon as `e ∘ (η × η)` is not zero: `η` is a symplectic similitude. -/
theorem level_similitude {W : Type} [AddCommGroup W] [Module K W]
    (ι : BK K → Module.End K W) (e : LinearMap.BilinForm K W) (halt : ∀ w, e w w = 0)
    (hadj : ∀ a v w, e (ι a v) w = e v (ι (dagK a) w)) (η : BK K →ₗ[K] W)
    (hη : ∀ a x, η (a * x) = ι a (η x)) :
    ∃ c : K, (∀ x y, e (η x) (η y) = c * psi K x y) ∧
      ((∃ x y, e (η x) (η y) ≠ 0) → c ≠ 0) := by
  obtain ⟨c, hc⟩ := eq_smul_E0K (e.compl₁₂ η η) (fun x => halt (η x))
    (fun a x y => by
      simp only [LinearMap.compl₁₂_apply, hη, hadj])
  refine ⟨c, fun x y => by rw [psi_eq_E0K]; exact hc x y, ?_⟩
  rintro ⟨x, y, hxy⟩ rfl
  exact hxy (by simpa using hc x y)

end DeligneY3Bridges.LevelCompat
