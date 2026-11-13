import Mathlib

/-!
# metrization: the degree of a Hodge line is unique (pure algebra)

For a flat `R`-algebra `F` that is a field and any `R`-module `C`: if `F ⊗_R ⋀^g_R C` and
`F ⊗_R ⋀^{g'}_R C` are both `F`-lines and `0 < g`, `0 < g'`, then `g = g'`.
(Applied with `R = 𝓞_L`, `F = L`, `C = 𝔪_ξ/𝔪_ξ²`: `hodgeSpace g` determines `g ≥ 1`.)
-/

open scoped TensorProduct

namespace ZInQ.Metrization

variable {R F C : Type*} [CommRing R] [Field F] [Algebra R F] [AddCommGroup C] [Module R C]

/-- If `F ⊗ ⋀^n C ≠ 0` (positive finrank) some `1 ⊗ v₁ ∧ ⋯ ∧ vₙ` is nonzero. -/
theorem exists_one_tmul_ιMulti_ne_zero (n : ℕ)
    (h : Module.finrank F (F ⊗[R] ⋀[R]^n C) ≠ 0) :
    ∃ v : Fin n → C, (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R n v ≠ 0 := by
  by_contra! hv
  apply h
  have hall : ∀ x : F ⊗[R] ⋀[R]^n C, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m =>
      have hm : m ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
        rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        rw [show a ⊗ₜ[R] exteriorPower.ιMulti R n v =
          a • ((1 : F) ⊗ₜ[R] exteriorPower.ιMulti R n v) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], hv v, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, hx, hy, add_zero]
      | smul r x _ hx => rw [TensorProduct.tmul_smul, hx, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  haveI : Subsingleton (F ⊗[R] ⋀[R]^n C) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- The core: `F ⊗ ⋀^g C` and `F ⊗ ⋀^{g+n} C` cannot both be lines when `g, n ≥ 1`. -/
theorem not_finrank_one_of_add [Module.Flat R F] {g n : ℕ} (hg : 0 < g) (hn : 0 < n)
    (h : Module.finrank F (F ⊗[R] ⋀[R]^g C) = 1)
    (h' : Module.finrank F (F ⊗[R] ⋀[R]^(g + n) C) = 1) : False := by
  obtain ⟨v, hv⟩ := exists_one_tmul_ιMulti_ne_zero (R := R) (F := F) (C := C) (g + n)
    (by rw [h']; exact one_ne_zero)
  -- `Z = 1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀ C` (flatness)
  let ι' : ⋀[R]^(g + n) C →ₗ[R] ExteriorAlgebra R C := (⋀[R]^(g + n) C).subtype
  have hinj : Function.Injective (ι'.lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι' Subtype.val_injective
  have hZ : (1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v ≠ 0 := by
    intro h0
    apply hv
    apply hinj
    rw [LinearMap.lTensor_tmul, map_zero]
    exact h0
  let a : Fin g → C := fun i => v (Fin.castAdd n i)
  let b : Fin n → C := fun j => v (Fin.natAdd g j)
  have hab : Fin.append a b = v := Fin.append_castAdd_natAdd
  let i0 : Fin g := ⟨0, hg⟩
  let j0 : Fin n := ⟨0, hn⟩
  let a' : Fin g → C := Function.update a i0 (b j0)
  let b' : Fin n → C := Function.update b j0 (a i0)
  have hp : (Fin.castAdd n i0 : Fin (g + n)) ≠ Fin.natAdd g j0 := by
    intro hc
    have := congrArg Fin.val hc
    simp [i0, j0] at this
    omega
  -- the four products
  have h1 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a' b) = 0 := by
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hi
    apply hp
    apply hi
    simp [a', Fin.append_left, Fin.append_right]
  have h2 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a b') = 0 := by
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hi
    apply hp
    apply hi
    simp [b', Fin.append_left, Fin.append_right]
  have hswap : Fin.append a' b' = v ∘ Equiv.swap (Fin.castAdd n i0) (Fin.natAdd g j0) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Function.comp_apply]
      by_cases hi : i = i0
      · subst hi
        rw [Equiv.swap_apply_left]
        simp [a', b]
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [a', hi, a]
        · exact fun hc => hi (Fin.castAdd_injective _ _ hc)
        · intro hc
          have := congrArg Fin.val hc
          simp at this
          omega
    · rw [Fin.append_right, Function.comp_apply]
      by_cases hj : j = j0
      · subst hj
        rw [Equiv.swap_apply_right]
        simp [b', a]
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [b', hj, b]
        · intro hc
          have := congrArg Fin.val hc
          simp at this
          omega
        · exact fun hc => hj (Fin.natAdd_injective _ _ hc)
  have h3 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a' b') =
      -ExteriorAlgebra.ιMulti R (g + n) v := by
    rw [hswap]
    exact (ExteriorAlgebra.ιMulti R (g + n)).map_swap v hp
  -- the two wedge maps, base changed
  let Φ := (LinearMap.mulRight R (ExteriorAlgebra.ιMulti R n b) ∘ₗ (⋀[R]^g C).subtype).baseChange F
  let Ψ := (LinearMap.mulRight R (ExteriorAlgebra.ιMulti R n b') ∘ₗ (⋀[R]^g C).subtype).baseChange F
  set XS : F ⊗[R] ⋀[R]^g C := (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R g a
  set XT : F ⊗[R] ⋀[R]^g C := (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R g a'
  have hΦS : Φ XS = (1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v := by
    simp only [Φ, XS, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      hab]
  have hΨS : Ψ XS = 0 := by
    simp only [Ψ, XS, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      h2, TensorProduct.tmul_zero]
  have hΨT : Ψ XT = -((1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v) := by
    simp only [Ψ, XT, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      h3, TensorProduct.tmul_neg]
  have hXS : XS ≠ 0 := by
    intro h0
    apply hZ
    rw [← hΦS, h0, map_zero]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' XS hXS).mp h XT
  apply hZ
  have : Ψ XT = 0 := by rw [← hc, map_smul, hΨS, smul_zero]
  rw [hΨT, neg_eq_zero] at this
  exact this

/-- **The degree of a Hodge line is unique.** -/
theorem eq_of_finrank_one [Module.Flat R F] {g g' : ℕ} (hg : 0 < g) (hg' : 0 < g')
    (h : Module.finrank F (F ⊗[R] ⋀[R]^g C) = 1)
    (h' : Module.finrank F (F ⊗[R] ⋀[R]^g' C) = 1) : g = g' := by
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact (not_finrank_one_of_add hg (Nat.succ_pos n) h h').elim
  · exact heq
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    exact (not_finrank_one_of_add hg' (Nat.succ_pos n) h' h).elim

end ZInQ.Metrization

#print axioms ZInQ.Metrization.eq_of_finrank_one
