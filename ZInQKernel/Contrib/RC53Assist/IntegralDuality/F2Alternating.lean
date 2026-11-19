import Mathlib

/-!
# Nondegenerate alternating forms over 𝔽₂ in dimension two

Let `V` be a vector space over `ZMod 2` with `finrank V = 2`. An alternating
bilinear form `B : V →ₗ V →ₗ ZMod 2` with zero left radical (`ker B = ⊥`) is
unique: any two such forms are equal.

Proof. Pick a basis `b₀, b₁`. Alternation gives `B bᵢ bᵢ = 0`. If
`B b₀ b₁ = 0`, then `B b₀` vanishes on the basis, so `b₀ ∈ ker B = ⊥`, which is
impossible; similarly `B b₁ b₀ ≠ 0`. In `ZMod 2` a nonzero value is `1`, so the
Gram matrix of every such form in the basis `b` is `!![0, 1; 1, 0]`, and two
bilinear forms agreeing on a basis are equal.

Main results:
* `f2Alternating_apply_basis`: the Gram matrix of such a form in any basis
  indexed by `Fin 2`.
* `f2Alternating_unique`: uniqueness on any `V` with `finrank V = 2`.
* `f2Alternating_unique_fin_two`: the same on `Fin 2 → ZMod 2`.
* `f2Alternating_unique_of_linearEquiv`: for a linear isomorphism `e : V ≃ W`
  and such forms `B` on `V`, `C` on `W`, the pullback of `C` along `e` is `B`.
* `f2Alternating_unique_isAlt_separatingLeft`: the uniqueness statement phrased
  with Mathlib's `LinearMap.IsAlt` and `LinearMap.SeparatingLeft`.

Only Mathlib is imported.
-/

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open Module

section Basis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- In `ZMod 2`, every nonzero element is `1`. -/
theorem zmod_two_eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
  decide

/-- For a form with alternating diagonal and zero left radical, the pairing of
two distinct vectors of a `Fin 2` basis is nonzero. -/
theorem f2Alternating_apply_basis_ne_zero
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (hB : ∀ x, B x x = 0)
    (hk : LinearMap.ker B = ⊥) (b : Basis (Fin 2) (ZMod 2) V) (i j : Fin 2)
    (hij : i ≠ j) : B (b i) (b j) ≠ 0 := by
  intro h
  have hzero : B (b i) = 0 := by
    refine b.ext fun l => ?_
    rw [LinearMap.zero_apply]
    by_cases hl : l = i
    · subst hl
      exact hB _
    · have hlj : l = j := by
        fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
      subst hlj
      exact h
  have hmem : b i ∈ LinearMap.ker B := LinearMap.mem_ker.2 hzero
  rw [hk, Submodule.mem_bot] at hmem
  exact b.ne_zero i hmem

/-- The Gram matrix of a nondegenerate alternating form over `ZMod 2` in any
basis indexed by `Fin 2`: zero on the diagonal, one off it. -/
theorem f2Alternating_apply_basis
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (hB : ∀ x, B x x = 0)
    (hk : LinearMap.ker B = ⊥) (b : Basis (Fin 2) (ZMod 2) V) (i j : Fin 2) :
    B (b i) (b j) = if i = j then 0 else 1 := by
  split_ifs with hij
  · subst hij
    exact hB _
  · exact zmod_two_eq_one_of_ne_zero _
      (f2Alternating_apply_basis_ne_zero B hB hk b i j hij)

/-- Two nondegenerate alternating forms over `ZMod 2` are equal as soon as the
space has a basis indexed by `Fin 2`. -/
theorem f2Alternating_unique_of_basis
    (B C : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ x, B x x = 0) (hC : ∀ x, C x x = 0)
    (hBk : LinearMap.ker B = ⊥) (hCk : LinearMap.ker C = ⊥)
    (b : Basis (Fin 2) (ZMod 2) V) : B = C := by
  refine LinearMap.ext_basis b b fun i j => ?_
  rw [f2Alternating_apply_basis B hB hBk b i j,
    f2Alternating_apply_basis C hC hCk b i j]

end Basis

section Unique

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Uniqueness of nondegenerate alternating bilinear forms over `ZMod 2` on a
two-dimensional space: alternating forms with zero left radical are equal. -/
theorem f2Alternating_unique (hV : finrank (ZMod 2) V = 2)
    (B C : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ x, B x x = 0) (hC : ∀ x, C x x = 0)
    (hBk : LinearMap.ker B = ⊥) (hCk : LinearMap.ker C = ⊥) : B = C := by
  have : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  exact f2Alternating_unique_of_basis B C hB hC hBk hCk
    (Module.finBasisOfFinrankEq (ZMod 2) V hV)

/-- The same uniqueness statement with Mathlib's predicates `LinearMap.IsAlt`
and `LinearMap.SeparatingLeft`. -/
theorem f2Alternating_unique_isAlt_separatingLeft (hV : finrank (ZMod 2) V = 2)
    (B C : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hB : B.IsAlt) (hC : C.IsAlt)
    (hBs : B.SeparatingLeft) (hCs : C.SeparatingLeft) : B = C :=
  f2Alternating_unique hV B C hB hC
    (LinearMap.separatingLeft_iff_ker_eq_bot.1 hBs)
    (LinearMap.separatingLeft_iff_ker_eq_bot.1 hCs)

end Unique

/-- Uniqueness on the coordinate space `Fin 2 → ZMod 2`. -/
theorem f2Alternating_unique_fin_two
    (B C : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ x, B x x = 0) (hC : ∀ x, C x x = 0)
    (hBk : LinearMap.ker B = ⊥) (hCk : LinearMap.ker C = ⊥) : B = C :=
  f2Alternating_unique (Module.finrank_fin_fun (ZMod 2)) B C hB hC hBk hCk

section Transport

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The pullback of a form along a linear isomorphism keeps the alternating
property. -/
theorem compl₁₂_linearEquiv_alt (C : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hC : ∀ y, C y y = 0) (e : V ≃ₗ[ZMod 2] W) (x : V) :
    C.compl₁₂ (e : V →ₗ[ZMod 2] W) (e : V →ₗ[ZMod 2] W) x x = 0 := by
  simp [hC]

/-- The pullback of a form with zero left radical along a linear isomorphism
again has zero left radical. -/
theorem ker_compl₁₂_linearEquiv_eq_bot (C : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hCk : LinearMap.ker C = ⊥) (e : V ≃ₗ[ZMod 2] W) :
    LinearMap.ker (C.compl₁₂ (e : V →ₗ[ZMod 2] W) (e : V →ₗ[ZMod 2] W)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hCx : C (e x) = 0 := by
    ext z
    have := LinearMap.congr_fun hx (e.symm z)
    simpa using this
  have hmem : e x ∈ LinearMap.ker C := LinearMap.mem_ker.2 hCx
  rw [hCk, Submodule.mem_bot] at hmem
  exact e.map_eq_zero_iff.1 hmem

/-- Transport form: for a linear isomorphism `e : V ≃ W` with `finrank V = 2`,
and nondegenerate alternating forms `B` on `V` and `C` on `W`, the form `B` is
the pullback of `C` along `e`. -/
theorem f2Alternating_unique_of_linearEquiv (hV : finrank (ZMod 2) V = 2)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (C : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ x, B x x = 0) (hC : ∀ y, C y y = 0)
    (hBk : LinearMap.ker B = ⊥) (hCk : LinearMap.ker C = ⊥) (e : V ≃ₗ[ZMod 2] W) :
    B = C.compl₁₂ (e : V →ₗ[ZMod 2] W) (e : V →ₗ[ZMod 2] W) :=
  f2Alternating_unique hV B _ hB (compl₁₂_linearEquiv_alt C hC e) hBk
    (ker_compl₁₂_linearEquiv_eq_bot C hCk e)

/-- Pointwise form of `f2Alternating_unique_of_linearEquiv`. -/
theorem f2Alternating_apply_linearEquiv (hV : finrank (ZMod 2) V = 2)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (C : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ x, B x x = 0) (hC : ∀ y, C y y = 0)
    (hBk : LinearMap.ker B = ⊥) (hCk : LinearMap.ker C = ⊥) (e : V ≃ₗ[ZMod 2] W)
    (x y : V) : B x y = C (e x) (e y) := by
  rw [f2Alternating_unique_of_linearEquiv hV B C hB hC hBk hCk e]
  rfl

end Transport

end ZInQ.Contrib.RC53Assist.IntegralDuality

/-!
## Forms on additive groups

The statements below need no `ZMod 2`-module structure on the carrier. For an
additive group `V` with an additive isomorphism `e : V ≃+ ZMod 2 × ZMod 2`, a
biadditive map `B : V →+ V →+ ZMod 2` is pulled back to coordinates through
`e.symm`. An additive map between `ZMod 2`-modules is `ZMod 2`-linear
(`ZMod.map_smul`), so the coordinate form is bilinear. Injectivity of `B` gives
it a zero left radical, so the uniqueness theorem above applies.

Main results:
* `f2Alternating_unique_addEquiv`: two alternating, injective biadditive maps
  `V →+ V →+ ZMod 2` are equal when `V ≃+ ZMod 2 × ZMod 2`.
* `f2Alternating_eq_addPullback` and `f2Alternating_apply_addEquiv`: for an
  additive isomorphism `e : V ≃+ W` and such maps `B` on `V`, `C` on `W`, the
  map `B` is the pullback of `C` along `e`.
-/

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

section Additive

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- The coordinate form of a biadditive map on `V`, transported through an
additive isomorphism `e : V ≃+ ZMod 2 × ZMod 2`; it is `ZMod 2`-bilinear. -/
def f2CoordForm (B : V →+ V →+ ZMod 2) (e : V ≃+ (ZMod 2 × ZMod 2)) :
    (ZMod 2 × ZMod 2) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun u v => B (e.symm u) (e.symm v))
    (fun u₁ u₂ v => by simp only [map_add, AddMonoidHom.add_apply])
    (fun c u v => ZMod.map_smul ((B.flip (e.symm v)).comp e.symm.toAddMonoidHom) c u)
    (fun u v₁ v₂ => by simp only [map_add])
    (fun c u v => ZMod.map_smul ((B (e.symm u)).comp e.symm.toAddMonoidHom) c v)

theorem f2CoordForm_apply (B : V →+ V →+ ZMod 2) (e : V ≃+ (ZMod 2 × ZMod 2))
    (u v : ZMod 2 × ZMod 2) : f2CoordForm B e u v = B (e.symm u) (e.symm v) :=
  rfl

theorem f2CoordForm_alt (B : V →+ V →+ ZMod 2) (hB : ∀ x, B x x = 0)
    (e : V ≃+ (ZMod 2 × ZMod 2)) (u : ZMod 2 × ZMod 2) : f2CoordForm B e u u = 0 :=
  hB _

/-- Injectivity of a biadditive map gives its coordinate form a zero left
radical. -/
theorem ker_f2CoordForm_eq_bot (B : V →+ V →+ ZMod 2) (hBi : Function.Injective B)
    (e : V ≃+ (ZMod 2 × ZMod 2)) : LinearMap.ker (f2CoordForm B e) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  rw [LinearMap.mem_ker] at hu
  have h0 : B (e.symm u) = B 0 := by
    ext x
    have := DFunLike.congr_fun hu (e x)
    simpa [f2CoordForm_apply] using this
  exact e.symm.map_eq_zero_iff.1 (hBi h0)

/-- Uniqueness for biadditive maps: on an additive group `V` with
`V ≃+ ZMod 2 × ZMod 2`, two alternating, injective biadditive maps
`V →+ V →+ ZMod 2` are equal. No module structure on `V` is used. -/
theorem f2Alternating_unique_addEquiv (e : V ≃+ (ZMod 2 × ZMod 2))
    (B C : V →+ V →+ ZMod 2) (hB : ∀ x, B x x = 0) (hC : ∀ x, C x x = 0)
    (hBi : Function.Injective B) (hCi : Function.Injective C) : B = C := by
  have hF : Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) = 2 := by simp
  have h := f2Alternating_unique hF _ _ (f2CoordForm_alt B hB e)
    (f2CoordForm_alt C hC e) (ker_f2CoordForm_eq_bot B hBi e)
    (ker_f2CoordForm_eq_bot C hCi e)
  ext x y
  have := DFunLike.congr_fun (DFunLike.congr_fun h (e x)) (e y)
  simpa only [f2CoordForm_apply, AddEquiv.symm_apply_apply] using this

/-- The pullback of a biadditive map along an additive isomorphism. -/
def addPullback (C : W →+ W →+ ZMod 2) (e : V ≃+ W) : V →+ V →+ ZMod 2 :=
  (C.comp e.toAddMonoidHom).compl₂ e.toAddMonoidHom

theorem addPullback_apply (C : W →+ W →+ ZMod 2) (e : V ≃+ W) (x y : V) :
    addPullback C e x y = C (e x) (e y) :=
  rfl

theorem addPullback_alt (C : W →+ W →+ ZMod 2) (hC : ∀ y, C y y = 0) (e : V ≃+ W)
    (x : V) : addPullback C e x x = 0 :=
  hC _

/-- The pullback of an injective biadditive map along an additive isomorphism is
injective. -/
theorem addPullback_injective (C : W →+ W →+ ZMod 2) (hCi : Function.Injective C)
    (e : V ≃+ W) : Function.Injective (addPullback C e) := by
  refine (injective_iff_map_eq_zero (addPullback C e)).2 fun x hx => ?_
  have h0 : C (e x) = C 0 := by
    ext w
    have := DFunLike.congr_fun hx (e.symm w)
    simpa [addPullback_apply] using this
  exact e.map_eq_zero_iff.1 (hCi h0)

/-- Transport form for additive groups: if `e : V ≃+ W`, `V ≃+ ZMod 2 × ZMod 2`,
and `B` on `V`, `C` on `W` are alternating and injective, then `B` is the
pullback of `C` along `e`. -/
theorem f2Alternating_eq_addPullback (f : V ≃+ (ZMod 2 × ZMod 2)) (e : V ≃+ W)
    (B : V →+ V →+ ZMod 2) (C : W →+ W →+ ZMod 2)
    (hB : ∀ x, B x x = 0) (hC : ∀ y, C y y = 0)
    (hBi : Function.Injective B) (hCi : Function.Injective C) :
    B = addPullback C e :=
  f2Alternating_unique_addEquiv f B _ hB (addPullback_alt C hC e) hBi
    (addPullback_injective C hCi e)

/-- Pointwise form of `f2Alternating_eq_addPullback`. -/
theorem f2Alternating_apply_addEquiv (f : V ≃+ (ZMod 2 × ZMod 2)) (e : V ≃+ W)
    (B : V →+ V →+ ZMod 2) (C : W →+ W →+ ZMod 2)
    (hB : ∀ x, B x x = 0) (hC : ∀ y, C y y = 0)
    (hBi : Function.Injective B) (hCi : Function.Injective C) (x y : V) :
    B x y = C (e x) (e y) := by
  rw [f2Alternating_eq_addPullback f e B C hB hC hBi hCi]
  rfl

end Additive

end ZInQ.Contrib.RC53Assist.IntegralDuality
