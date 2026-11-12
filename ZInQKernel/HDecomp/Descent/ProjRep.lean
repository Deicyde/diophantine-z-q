import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-descent/ProjRep.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-descent: the algebraic core of B1 and C1 (N5 L632-664, L719-731)

All statements are over arbitrary groups, fields, vector spaces and algebras (genuine Mathlib
definitions). They are the steps of Glazer's scalar descent after the abelian surface has been
replaced by its Tate realization:

* `G` stands for `G_ℚ`, `E` for a finite extension of `ℚ_ℓ` containing the image of the
  coefficient field `C`, and `V` for `V_ℓ(A) ⊗ E`;
* `T σ = μ_σ ∘ σ ∈ GL(V)` (the Tate action of `σ` followed by the `B`-linear isogeny
  `μ_σ : ^σA → A`), so that `T σ * T τ = c(σ,τ) • T (σ τ)` with `c(σ,τ) ∈ ℚ^×` (N5 L640-644);
* `a σ = (deg μ_σ)^{-1/4}` and `ε = sign c` (N5 L645-664);
* `β` the cochain of B2-B3 with `β σ β τ = ε(σ,τ) β(στ)`.

The instantiation (Tate modules, the Galois action, `End⁰(A) = B`, Skolem–Noether) is not in
Mathlib; see `docs/research/glue-descent.md`.
-/

namespace GlueDescent

open scoped BigOperators

section Cocycle

variable {G : Type*} [Group G] {E : Type*} [Field E] {A : Type*} [Ring A] [Algebra E A]
  [Nontrivial A]

/-- **B1, cocycle identity.** A projective representation with scalar discrepancy `c`
(`T g * T h = c(g,h) • T(gh)`, with `T` valued in units) has `c` a 2-cocycle for the trivial
action: `c(gh,k) c(g,h) = c(h,k) c(g,hk)`. -/
theorem cocycle_of_projective (T : G → Aˣ) (c : G → G → E)
    (hT : ∀ g h, (T g : A) * T h = c g h • (T (g * h) : A)) (g h k : G) :
    c (g * h) k * c g h = c h k * c g (h * k) := by
  have h1 : ((T g : A) * T h) * T k = (c g h * c (g * h) k) • (T (g * h * k) : A) := by
    rw [hT, smul_mul_assoc, hT, smul_smul]
  have h2 : (T g : A) * (T h * T k) = (c h k * c g (h * k)) • (T (g * (h * k)) : A) := by
    rw [hT, mul_smul_comm, hT, smul_smul, mul_comm (c h k)]
  rw [mul_assoc, h2, mul_assoc g h k] at h1
  have hu : IsUnit (T (g * (h * k)) : A) := (T _).isUnit
  have key : ((c h k * c g (h * k)) - (c g h * c (g * h) k)) • (T (g * (h * k)) : A) = 0 := by
    rw [sub_smul, h1, sub_self]
  rw [smul_eq_zero] at key
  rcases key with key | key
  · rw [mul_comm (c (g * h) k)]; exact (sub_eq_zero.mp key).symm
  · exact absurd key hu.ne_zero

end Cocycle

section Sign

/-- **B1, sign normalization (real arithmetic).** If positive degrees satisfy
`deg σ · deg τ = c⁴ · deg(στ)` (multiplicativity of degree, `deg [c] = c⁴` on an abelian
surface) and `a = deg^{-1/4}`, then `a σ · a τ · c = sign(c) · a(στ)`. -/
theorem sign_normalization {dσ dτ dστ c : ℝ} (hσ : 0 < dσ) (hτ : 0 < dτ) (hστ : 0 < dστ)
    (hc : c ≠ 0) (hdeg : dσ * dτ = c ^ 4 * dστ) :
    dσ ^ (-(1 / 4 : ℝ)) * dτ ^ (-(1 / 4 : ℝ)) * c = SignType.sign c * dστ ^ (-(1 / 4 : ℝ)) := by
  have hc4 : (0 : ℝ) < c ^ 4 := by positivity
  have habs : (c ^ 4) ^ (-(1 / 4 : ℝ)) = |c|⁻¹ := by
    have h1 : c ^ 4 = |c| ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact (Even.pow_abs ⟨2, rfl⟩ c).symm
    rw [h1, ← Real.rpow_mul (abs_nonneg c)]
    norm_num [Real.rpow_neg_one]
  rw [← Real.mul_rpow hσ.le hτ.le, hdeg, Real.mul_rpow hc4.le hστ.le, habs]
  have hsign : (SignType.sign c : ℝ) = c / |c| := by
    rcases lt_or_gt_of_ne hc with h | h
    · rw [sign_neg h, abs_of_neg h]; field_simp; simp
    · rw [sign_pos h, abs_of_pos h]; field_simp; simp
  rw [hsign]
  have : |c| ≠ 0 := abs_ne_zero.mpr hc
  field_simp

/-- The sign of a nonzero real is `±1`. -/
theorem sign_sq_eq_one {c : ℝ} (hc : c ≠ 0) : (SignType.sign c : ℝ) ^ 2 = 1 := by
  rcases lt_or_gt_of_ne hc with h | h
  · simp [sign_neg h]
  · simp [sign_pos h]

/-- **B1, `ε` is a normalized cocycle.** If `c` is a 2-cocycle with values in `ℝ^×` (trivial
action) normalized by `c(1,·) = c(·,1) = 1`, then so is `ε = sign ∘ c`. -/
theorem sign_cocycle {G : Type*} [Group G] (c : G → G → ℝ)
    (hcoc : ∀ g h k, c (g * h) k * c g h = c h k * c g (h * k)) (g h k : G) :
    (SignType.sign (c (g * h) k) : ℝ) * SignType.sign (c g h) =
      SignType.sign (c h k) * SignType.sign (c g (h * k)) := by
  have := congrArg (fun x : ℝ => (SignType.sign x : ℝ)) (hcoc g h k)
  simpa [sign_mul] using this

end Sign

section Rho

variable {G : Type*} [Group G] {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

/-- The descended operator `ρ(g) = β(g)⁻¹ a(g) T(g)`. -/
def rho (T : G → Module.End E V) (a β : G → E) (g : G) : Module.End E V :=
  ((β g)⁻¹ * a g) • T g

/-- **C1, `ρ` is a representation.** With `T g * T h = c(g,h) • T(gh)`, scalars `a` with
`a g · a h · c(g,h) = ε(g,h) · a(gh)` and a cochain `β` with `β g · β h = ε(g,h) · β(gh)`
(`β` nonzero), `ρ(g) = β(g)⁻¹ a(g) T(g)` is multiplicative (N5 L723-729). -/
theorem rho_map_mul (T : G → Module.End E V) (c ε : G → G → E) (a β : G → E)
    (hT : ∀ g h, T g * T h = c g h • T (g * h))
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h))
    (hβ0 : ∀ g, β g ≠ 0) (g h : G) :
    rho T a β g * rho T a β h = rho T a β (g * h) := by
  unfold rho
  rw [smul_mul_smul_comm, hT, smul_smul]
  congr 1
  have hgh : β (g * h) ≠ 0 := hβ0 _
  have hg := hβ0 g
  have hh := hβ0 h
  have hε : ε g h ≠ 0 := by
    intro h0; apply mul_ne_zero hg hh; rw [hβ, h0, zero_mul]
  have key : (β g)⁻¹ * a g * ((β h)⁻¹ * a h) * c g h = (β g * β h)⁻¹ * (a g * a h * c g h) := by
    field_simp
  rw [key, ha, hβ]
  field_simp

/-- `ρ` as a group representation, given `ρ(1) = 1` (which holds when `T 1 = 1`, `a 1 = 1`,
`β 1 = 1`). -/
def rhoRep (T : G → Module.End E V) (c ε : G → G → E) (a β : G → E)
    (hT : ∀ g h, T g * T h = c g h • T (g * h))
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h))
    (hβ0 : ∀ g, β g ≠ 0) (h1 : rho T a β 1 = 1) : Representation E G V where
  toFun := rho T a β
  map_one' := h1
  map_mul' g h := (rho_map_mul T c ε a β hT ha hβ hβ0 g h).symm

/-- **C1, `ρ` commutes with `B`.** If every `T g` commutes with an endomorphism `b` (the
`B`-linearity of `μ_σ`), so does `ρ g`. -/
theorem rho_commute (T : G → Module.End E V) (a β : G → E) (b : Module.End E V)
    (hb : ∀ g, Commute (T g) b) (g : G) : Commute (rho T a β g) b :=
  (hb g).smul_left _

/-- **C1, `ρ` is the Tate action on `G_{L'}`.** On the elements where `μ_σ = 1` (so `T` is the
Tate action `act`), `a = 1` and `β = 1` (the kernel of `β|_{G_L}`), `ρ = act`. -/
theorem rho_eq_act (T act : G → Module.End E V) (a β : G → E) (g : G)
    (hT : T g = act g) (ha : a g = 1) (hβ : β g = 1) : rho T a β g = act g := by
  simp [rho, hT, ha, hβ]

end Rho

section Split

variable {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

/-- A system of `2 × 2` matrix units in `End_E(V)` (the image of `M₂(E) ≅ B ⊗ E`). -/
structure MatrixUnits2 (E V : Type*) [Field E] [AddCommGroup V] [Module E V] where
  e : Fin 2 → Fin 2 → Module.End E V
  mul_e : ∀ i j k l, e i j * e k l = if j = k then e i l else 0
  sum_diag : e 0 0 + e 1 1 = 1

namespace MatrixUnits2

variable (u : MatrixUnits2 E V)

/-- `W = e₀₀ V`. -/
def W : Submodule E V := LinearMap.range (u.e 0 0)

theorem e00_of_mem {w : V} (hw : w ∈ u.W) : u.e 0 0 w = w := by
  obtain ⟨v, rfl⟩ := hw
  have := u.mul_e 0 0 0 0
  simp only [ite_true] at this
  rw [← Module.End.mul_apply, this]

theorem e_apply_e (i j k l : Fin 2) (v : V) :
    u.e i j (u.e k l v) = if j = k then u.e i l v else 0 := by
  rw [← Module.End.mul_apply, u.mul_e]
  split_ifs <;> simp

theorem mem_W_of_e0 (j : Fin 2) (v : V) : u.e 0 j v ∈ u.W :=
  ⟨u.e 0 j v, by rw [u.e_apply_e]; simp⟩

/-- The linear isomorphism `V ≃ W × W`, `v ↦ (e₀₀ v, e₀₁ v)`, inverse `(w₁, w₂) ↦ w₁ + e₁₀ w₂`. -/
noncomputable def splitEquiv : V ≃ₗ[E] u.W × u.W :=
  LinearEquiv.ofLinearMap
    (LinearMap.prod ((u.e 0 0).codRestrict u.W (fun v => u.mem_W_of_e0 0 v))
      ((u.e 0 1).codRestrict u.W (fun v => u.mem_W_of_e0 1 v)))
    (LinearMap.coprod u.W.subtype (u.e 1 0 ∘ₗ u.W.subtype))
    (by
      ext ⟨w, hw⟩ <;> simp [u.e00_of_mem hw, u.e_apply_e]
      · obtain ⟨v, rfl⟩ := hw; simp [u.e_apply_e])
    (by
      ext v
      change u.e 0 0 v + u.e 1 0 (u.e 0 1 v) = v
      rw [u.e_apply_e]
      simp only [ite_true]
      have := congrArg (fun f : Module.End E V => f v) u.sum_diag
      simpa using this)

/-- A representation commuting with the matrix units preserves `W`. -/
theorem mapsTo_W {G : Type*} [Monoid G] (ρ : Representation E G V)
    (hc : ∀ g i j, Commute (ρ g) (u.e i j)) (g : G) {w : V} (hw : w ∈ u.W) : ρ g w ∈ u.W := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨ρ g v, by rw [← Module.End.mul_apply, ← (hc g 0 0).eq, Module.End.mul_apply]⟩

/-- **C1, `ρ ≅ r ⊕ r`.** If `ρ` commutes with the matrix units, the isomorphism `V ≃ W × W`
intertwines `ρ g` with `ρ g|_W × ρ g|_W`. (N5 L729-730: "matrix units give
`ρ_ℓ ≃ r_ℓ ⊕ r_ℓ`".) -/
theorem splitEquiv_intertwines {G : Type*} [Monoid G] (ρ : Representation E G V)
    (hc : ∀ g i j, Commute (ρ g) (u.e i j)) (g : G) (v : V) :
    u.splitEquiv (ρ g v) =
      (⟨ρ g (u.splitEquiv v).1, u.mapsTo_W ρ hc g (u.splitEquiv v).1.2⟩,
       ⟨ρ g (u.splitEquiv v).2, u.mapsTo_W ρ hc g (u.splitEquiv v).2.2⟩) := by
  ext <;> simp [splitEquiv, LinearEquiv.coe_ofLinearMap, ← Module.End.mul_apply,
    (hc g 0 0).eq, (hc g 0 1).eq]

/-- **C1, `dim r = 2`.** If `dim V = 4` then `dim W = 2`. -/
theorem finrank_W (h4 : Module.finrank E V = 4) [FiniteDimensional E V] :
    Module.finrank E u.W = 2 := by
  have := u.splitEquiv.finrank_eq
  rw [Module.finrank_prod, h4] at this
  omega

end MatrixUnits2

end Split

section Span

variable {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

/-- **C1, from `B` to `B ⊗ E`.** An endomorphism commuting with every element of `S` (the image
of `B`) commutes with the `E`-subalgebra generated by `S` (the image of `B ⊗_ℚ E ≅ M₂(E)`,
which contains the matrix units). -/
theorem commute_adjoin (f : Module.End E V) (S : Set (Module.End E V))
    (hS : ∀ s ∈ S, Commute f s) {x : Module.End E V} (hx : x ∈ Algebra.adjoin E S) :
    Commute f x := by
  have hle : Algebra.adjoin E S ≤ Subalgebra.centralizer E {f} := by
    apply Algebra.adjoin_le
    intro s hs
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (hS s hs).eq
  have := hle hx
  rw [Subalgebra.mem_centralizer_iff] at this
  exact this f rfl

end Span

end GlueDescent

