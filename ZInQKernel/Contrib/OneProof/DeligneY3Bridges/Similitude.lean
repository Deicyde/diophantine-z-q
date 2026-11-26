import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic

/-!
# Deligne's PEL datum for `B = (2, −3 | ℚ)`: the similitude group is `B^×`

P. Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), 4.9–4.12, pp. 147–149: a PEL datum is
a simple `ℚ`-algebra `L` with positive involution `*`, a faithful `L`-module `V` and an alternating
form `ψ` on `V` with `ψ(ℓx, y) = ψ(x, ℓ* y)`; `G` is the group of `L`-linear symplectic similitudes
of `(V, ψ)` (Scholie 4.11 (c): "similitudes symplectiques L-linéaires").

For the kernel's datum, `L = B = (2, −3 | ℚ)` (Mathlib's `QuaternionAlgebra ℚ 2 0 (−3)`), `V = B`
with `B` acting by left multiplication, the involution `x† = μ⁻¹ x̄ μ` with `μ = 2j + k`, and
`ψ(x, y) = trd(μ⁻¹ x ȳ)` (the kernel's `RvQMPolar.E0`). This file proves, over every commutative
`ℚ`-algebra `R` (so for `G(ℚ)`, `G(ℝ)` and `G(𝔸_f)` at once):

* `simGroup R`: Deligne's `G(R)`, the `B ⊗ R`-linear `R`-linear automorphisms `f` of `B ⊗ R` with
  `ψ(fx, fy) = ν ψ(x, y)` for a unit `ν ∈ R^×`;
* `psi_mul_right`: right multiplication by `c` is a similitude with multiplier `nrd c`;
* `simEquiv R : (B ⊗ R)^× ≃* G(R)`, `γ ↦ (x ↦ x γ⁻¹)`; every element of `G(R)` is of this form
  (`mem_simGroup_iff`), and the multiplier of `simEquiv R γ` is `nrd(γ)⁻¹` (`psi_simEquiv`).

The inverse in `γ ↦ (x ↦ x γ⁻¹)` makes the map a homomorphism; it matches the kernel's convention
that `g ∈ (B ⊗ 𝔸_f)^×` carries the lattice `𝒪̂` to `𝒪̂ g⁻¹` (`L_g = B ∩ 𝒪̂ g⁻¹`).
-/

noncomputable section

namespace DeligneY3Bridges

open QuaternionAlgebra

variable (R : Type) [CommRing R] [Algebra ℚ R]

/-- `B ⊗_ℚ R` for `B = (2, −3 | ℚ)`: Mathlib's quaternion algebra with `i² = 2`, `j² = −3`. -/
abbrev QB : Type := QuaternionAlgebra R 2 0 (-3)

/-- `μ⁻¹ = −μ/6` in `B ⊗ R`, where `μ = 2j + k`. -/
def muInv : QB R := ⟨0, 0, algebraMap ℚ R (-1 / 3), algebraMap ℚ R (-1 / 6)⟩

/-- **Deligne's symplectic form `ψ` on `V = B`** (4.9), `ψ(x, y) = trd(μ⁻¹ x ȳ)`, over `R`. -/
def psi (x y : QB R) : R := 2 * (muInv R * x * star y).re

/-- The reduced norm `nrd x = x x̄` (a scalar). -/
def nrd (x : QB R) : R := (x * star x).re

variable {R}

omit [Algebra ℚ R] in
theorem mul_star_eq_nrd (x : QB R) : x * star x = (nrd R x : QB R) :=
  QuaternionAlgebra.mul_star_eq_coe x

/-- **Right multiplication by `c` is a symplectic similitude with multiplier `nrd c`.** -/
theorem psi_mul_right (c x y : QB R) : psi R (x * c) (y * c) = nrd R c * psi R x y := by
  have h : muInv R * (x * c) * star (y * c) = (nrd R c : QB R) * (muInv R * x * star y) := by
    rw [star_mul, show muInv R * (x * c) * (star c * star y) =
      muInv R * x * (c * star c) * star y by simp only [mul_assoc], mul_star_eq_nrd,
      ← coe_commutes]
    simp only [mul_assoc]
  rw [psi, psi, h, QuaternionAlgebra.coe_mul_eq_smul, QuaternionAlgebra.re_smul, smul_eq_mul]
  ring

omit [Algebra ℚ R] in
/-- `nrd` of a unit is a unit: `nrd γ · nrd γ⁻¹ = 1`. -/
theorem nrd_mul_nrd_inv (γ : (QB R)ˣ) : nrd R (γ : QB R) * nrd R ((γ⁻¹ : (QB R)ˣ) : QB R) = 1 := by
  apply QuaternionAlgebra.coe_injective (c₁ := (2 : R)) (c₂ := 0) (c₃ := -3)
  rw [QuaternionAlgebra.coe_mul, ← mul_star_eq_nrd, ← mul_star_eq_nrd,
    QuaternionAlgebra.coe_one]
  calc (γ : QB R) * star (γ : QB R) * (((γ⁻¹ : (QB R)ˣ) : QB R) * star ((γ⁻¹ : (QB R)ˣ) : QB R))
      = ((γ⁻¹ : (QB R)ˣ) : QB R) * ((γ : QB R) * star (γ : QB R)) *
          star ((γ⁻¹ : (QB R)ˣ) : QB R) := by
        rw [mul_star_eq_nrd (γ : QB R), ← mul_assoc, coe_commutes]
    _ = star 1 := by
        rw [← mul_assoc, Units.inv_mul, one_mul, ← star_mul, Units.inv_mul]
    _ = 1 := star_one _

/-- `nrd γ` as a unit of `R`. -/
def nrdUnit (γ : (QB R)ˣ) : Rˣ where
  val := nrd R (γ : QB R)
  inv := nrd R ((γ⁻¹ : (QB R)ˣ) : QB R)
  val_inv := nrd_mul_nrd_inv γ
  inv_val := by rw [mul_comm]; exact nrd_mul_nrd_inv γ

variable (R)

/-- **Deligne's `G(R)` for the PEL datum `(B, B, ψ)`** (4.9; Scholie 4.11 (c)): the `R`-linear
automorphisms `f` of `V ⊗ R = B ⊗ R` that are `B`-linear (`f(a x) = a f(x)`) and symplectic
similitudes (`ψ(fx, fy) = ν ψ(x, y)` with `ν ∈ R^×`). -/
def simGroup : Subgroup (Module.End R (QB R))ˣ where
  carrier := {f | (∀ a x, (f : Module.End R (QB R)) (a * x) = a * (f : Module.End R (QB R)) x) ∧
    ∃ ν : Rˣ, ∀ x y,
      psi R ((f : Module.End R (QB R)) x) ((f : Module.End R (QB R)) y) = ν * psi R x y}
  mul_mem' := by
    rintro f g ⟨hf, ν, hν⟩ ⟨hg, μ, hμ⟩
    refine ⟨fun a x => ?_, ν * μ, fun x y => ?_⟩
    · simp only [Units.val_mul, Module.End.mul_apply, hg, hf]
    · simp only [Units.val_mul, Module.End.mul_apply, hν, hμ, Units.val_mul]
      ring
  one_mem' := ⟨fun a x => rfl, 1, fun x y => by simp⟩
  inv_mem' := by
    rintro f ⟨hf, ν, hν⟩
    have h1 : ∀ x, (f : Module.End R (QB R)) (((f⁻¹ : (Module.End R (QB R))ˣ) :
        Module.End R (QB R)) x) = x := fun x => by
      rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    have h2 : ∀ x, ((f⁻¹ : (Module.End R (QB R))ˣ) : Module.End R (QB R))
        ((f : Module.End R (QB R)) x) = x := fun x => by
      rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
    refine ⟨fun a x => ?_, ν⁻¹, fun x y => ?_⟩
    · conv_lhs => rw [← h1 x, ← hf, h2]
    · conv_rhs => rw [← h1 x, ← h1 y, hν, ← mul_assoc, Units.inv_mul, one_mul]

variable {R}

theorem simGroup_linear {f : (Module.End R (QB R))ˣ} (hf : f ∈ simGroup R) (x : QB R) :
    (f : Module.End R (QB R)) x = x * (f : Module.End R (QB R)) 1 := by
  simpa using hf.1 x 1

/-- `x ↦ x γ⁻¹` as a unit of `End_R(B ⊗ R)`. -/
def toSim (γ : (QB R)ˣ) : (Module.End R (QB R))ˣ where
  val := LinearMap.mulRight R ((γ⁻¹ : (QB R)ˣ) : QB R)
  inv := LinearMap.mulRight R (γ : QB R)
  val_inv := LinearMap.ext fun x => by
    show x * (γ : QB R) * ((γ⁻¹ : (QB R)ˣ) : QB R) = x
    rw [mul_assoc, Units.mul_inv, mul_one]
  inv_val := LinearMap.ext fun x => by
    show x * ((γ⁻¹ : (QB R)ˣ) : QB R) * (γ : QB R) = x
    rw [mul_assoc, Units.inv_mul, mul_one]

omit [Algebra ℚ R] in
theorem toSim_apply (γ : (QB R)ˣ) (x : QB R) :
    (toSim γ : Module.End R (QB R)) x = x * ((γ⁻¹ : (QB R)ˣ) : QB R) := rfl

omit [Algebra ℚ R] in
theorem toSim_inv_apply (γ : (QB R)ˣ) (x : QB R) :
    (((toSim γ)⁻¹ : (Module.End R (QB R))ˣ) : Module.End R (QB R)) x = x * (γ : QB R) := rfl

theorem toSim_mem (γ : (QB R)ˣ) : toSim γ ∈ simGroup R :=
  ⟨fun a x => by simp only [toSim_apply, mul_assoc], nrdUnit γ⁻¹,
    fun x y => by simp only [toSim_apply, psi_mul_right]; rfl⟩

/-- The element `c = f⁻¹(1)` of `B ⊗ R` attached to `f ∈ G(R)`, with `f = (x ↦ x c⁻¹)`. -/
def ofSim (f : simGroup R) : (QB R)ˣ where
  val := (((f : (Module.End R (QB R))ˣ)⁻¹ : (Module.End R (QB R))ˣ) : Module.End R (QB R)) 1
  inv := ((f : (Module.End R (QB R))ˣ) : Module.End R (QB R)) 1
  val_inv := by
    rw [← simGroup_linear f.2, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  inv_val := by
    rw [← simGroup_linear (inv_mem f.2), ← Module.End.mul_apply, Units.inv_mul,
      Module.End.one_apply]

variable (R)

/-- **The identification `(B ⊗ R)^× ≅ G(R)`**, `γ ↦ (x ↦ x γ⁻¹)`: Deligne's group of `B`-linear
symplectic similitudes of `(B ⊗ R, ψ)` is `(B ⊗ R)^×` acting by inverse right multiplication. -/
def simEquiv : (QB R)ˣ ≃* simGroup R where
  toFun γ := ⟨toSim γ, toSim_mem γ⟩
  invFun := ofSim
  left_inv γ := by
    apply Units.ext
    show (((toSim γ)⁻¹ : (Module.End R (QB R))ˣ) : Module.End R (QB R)) 1 = _
    rw [toSim_inv_apply, one_mul]
  right_inv f := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    show x * ((ofSim f)⁻¹ : (QB R)ˣ) = _
    rw [simGroup_linear f.2 x]
    rfl
  map_mul' γ δ := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    show x * ((γ * δ)⁻¹ : (QB R)ˣ) = (x * ((δ⁻¹ : (QB R)ˣ) : QB R)) * ((γ⁻¹ : (QB R)ˣ) : QB R)
    rw [mul_inv_rev, Units.val_mul, mul_assoc]

variable {R}

@[simp] theorem simEquiv_apply (γ : (QB R)ˣ) (x : QB R) :
    (((simEquiv R γ : simGroup R) : (Module.End R (QB R))ˣ) : Module.End R (QB R)) x =
      x * ((γ⁻¹ : (QB R)ˣ) : QB R) := rfl

@[simp] theorem simEquiv_inv_apply (γ : (QB R)ˣ) (x : QB R) :
    ((((simEquiv R γ : simGroup R) : (Module.End R (QB R))ˣ)⁻¹ : (Module.End R (QB R))ˣ) :
      Module.End R (QB R)) x = x * (γ : QB R) := rfl

/-- **Every `B`-linear symplectic similitude is a right multiplication by a unit.** -/
theorem mem_simGroup_iff (f : (Module.End R (QB R))ˣ) :
    f ∈ simGroup R ↔ ∃ c : (QB R)ˣ, ∀ x, (f : Module.End R (QB R)) x = x * (c : QB R) := by
  constructor
  · intro hf
    refine ⟨(ofSim ⟨f, hf⟩)⁻¹, fun x => ?_⟩
    rw [simGroup_linear hf x]
    rfl
  · rintro ⟨c, hc⟩
    have : f = toSim c⁻¹ := Units.ext (LinearMap.ext fun x => by rw [hc, toSim_apply, inv_inv])
    exact this ▸ toSim_mem c⁻¹

/-- **The multiplier of `simEquiv R γ` is `nrd(γ)⁻¹`**: `ψ(xγ⁻¹, yγ⁻¹) = nrd(γ⁻¹) ψ(x, y)`. -/
theorem psi_simEquiv (γ : (QB R)ˣ) (x y : QB R) :
    psi R ((((simEquiv R γ : simGroup R) : (Module.End R (QB R))ˣ) : Module.End R (QB R)) x)
      ((((simEquiv R γ : simGroup R) : (Module.End R (QB R))ˣ) : Module.End R (QB R)) y) =
      nrd R ((γ⁻¹ : (QB R)ˣ) : QB R) * psi R x y := by
  simp only [simEquiv_apply, psi_mul_right]

omit [Algebra ℚ R] in
/-- `nrd(γ⁻¹) = nrd(γ)⁻¹` in `R`. -/
theorem nrd_inv_eq (γ : (QB R)ˣ) :
    nrd R ((γ⁻¹ : (QB R)ˣ) : QB R) = (((nrdUnit γ)⁻¹ : Rˣ) : R) := rfl

/-! ## Elements of `G(R)` as maps, base change, and the lattice conditions of 4.12 -/

/-- An element of `G(R)` as a map of `V ⊗ R = B ⊗ R`. -/
def app (f : simGroup R) (x : QB R) : QB R :=
  (((f : (Module.End R (QB R))ˣ) : Module.End R (QB R)) x)

theorem app_mul (f g : simGroup R) (x : QB R) : app (f * g) x = app f (app g x) := rfl

theorem app_one (x : QB R) : app (1 : simGroup R) x = x := rfl

/-- `f(x) = x f(1)` for `f ∈ G(R)`. -/
theorem app_eq_mul (f : simGroup R) (x : QB R) : app f x = x * app f 1 :=
  simGroup_linear f.2 x

@[simp] theorem app_simEquiv (γ : (QB R)ˣ) (x : QB R) :
    app (simEquiv R γ) x = x * ((γ⁻¹ : (QB R)ˣ) : QB R) := rfl

theorem app_simEquiv_inv (γ : (QB R)ˣ) (x : QB R) :
    app (simEquiv R γ)⁻¹ x = x * (γ : QB R) := rfl

theorem simEquiv_symm_apply (f : simGroup R) :
    (((simEquiv R).symm f)⁻¹ : (QB R)ˣ) = (app f 1 : QB R) := rfl

omit [Algebra ℚ R] in
/-- An element of `B ⊗ R` whose reduced norm is a unit is a unit. -/
theorem isUnit_of_isUnit_nrd {x : QB R} (h : IsUnit (nrd R x)) : IsUnit x := by
  obtain ⟨n, hn⟩ := h
  have hs : star x * x = ((n : R) : QB R) := by
    rw [star_comm_self', mul_star_eq_nrd, hn]
  have hx : x * star x = ((n : R) : QB R) := by rw [mul_star_eq_nrd, hn]
  refine ⟨⟨x, star x * ((↑n⁻¹ : R) : QB R), ?_, ?_⟩, rfl⟩
  · rw [← mul_assoc, hx, ← QuaternionAlgebra.coe_mul, Units.mul_inv, QuaternionAlgebra.coe_one]
  · rw [mul_assoc, coe_commutes, ← mul_assoc, hs, ← QuaternionAlgebra.coe_mul, Units.mul_inv,
      QuaternionAlgebra.coe_one]

variable {S : Type} [CommRing S] [Algebra ℚ S]

/-- **Base change `G(ℚ) → G(S)`** along a multiplicative map `φ : B → B ⊗ S` (for `S = 𝔸_f`, the
coordinatewise embedding): `(x ↦ x γ⁻¹) ↦ (x ↦ x φ(γ)⁻¹)`. -/
def baseChangeOf (φ : QB ℚ →* QB S) : simGroup ℚ →* simGroup S :=
  (simEquiv S).toMonoidHom.comp ((Units.map φ).comp (simEquiv ℚ).symm.toMonoidHom)

/-- The base change of `f` extends `f`: `f_S(φ x) = φ(f x)`. -/
theorem app_baseChangeOf (φ : QB ℚ →* QB S) (f : simGroup ℚ) (x : QB ℚ) :
    app (baseChangeOf φ f) (φ x) = φ (app f x) := by
  rw [app_eq_mul f x, map_mul, ← simEquiv_symm_apply]
  rfl

/-- **The base change of `f` is the unique element of `G(S)` extending `f`** along `φ`. -/
theorem eq_baseChangeOf (φ : QB ℚ →* QB S) (f : simGroup ℚ) (h : simGroup S)
    (hh : ∀ x, app h (φ x) = φ (app f x)) : h = baseChangeOf φ f := by
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro y
  show app h y = app (baseChangeOf φ f) y
  rw [app_eq_mul h y, app_eq_mul (baseChangeOf φ f) y, ← map_one φ, hh, app_baseChangeOf]

/-- **`g V_Ẑ = V_Ẑ`** for a lattice `O` (Deligne 4.12: `V̂_ℤ` is `K`-invariant). -/
def IsStab (O : Set (QB R)) (g : simGroup R) : Prop :=
  (∀ x ∈ O, app g x ∈ O) ∧ ∀ x ∈ O, app g⁻¹ x ∈ O

/-- **Deligne's congruence condition `(g − 1) V̂_ℤ ⊂ n V̂_ℤ`** (4.12, p. 148:
`K_n = {g ∈ G(𝔸^f) | (g − 1) V̂_ℤ ⊂ n V̂_ℤ}`). -/
def IsCongr (O : Set (QB R)) (n : ℕ) (g : simGroup R) : Prop :=
  ∀ x ∈ O, ∃ y ∈ O, app g x - x = (n : QB R) * y

section Lattice

variable (O : Set (QB R)) (h1 : (1 : QB R) ∈ O) (hm : ∀ x y, x ∈ O → y ∈ O → x * y ∈ O)
include h1 hm

/-- **Units of an order are its stabilizer**: `γ, γ⁻¹ ∈ O` iff `x ↦ x γ⁻¹` preserves `O` both
ways. -/
theorem unit_iff (γ : (QB R)ˣ) :
    ((γ : QB R) ∈ O ∧ ((γ⁻¹ : (QB R)ˣ) : QB R) ∈ O) ↔ IsStab O (simEquiv R γ) := by
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun x hx => hm _ _ hx hb, fun x hx => hm _ _ hx ha⟩
  · rintro ⟨ha, hb⟩
    refine ⟨?_, ?_⟩
    · simpa [app_simEquiv_inv] using hb 1 h1
    · simpa using ha 1 h1

variable (hn : ∀ x, x ∈ O → -x ∈ O)
include hn

/-- **The kernel's level group is `G(Ẑ) ∩ K_n`**: `γ ∈ O^×` with `γ ≡ 1 mod n O` iff `x ↦ x γ⁻¹`
stabilizes `O` and satisfies Deligne's congruence condition `(g − 1) O ⊂ n O`. -/
theorem level_iff (n : ℕ) (γ : (QB R)ˣ) :
    ((γ : QB R) ∈ O ∧ ((γ⁻¹ : (QB R)ˣ) : QB R) ∈ O ∧ ∃ y ∈ O, (γ : QB R) = 1 + (n : QB R) * y) ↔
      IsStab O (simEquiv R γ) ∧ IsCongr O n (simEquiv R γ) := by
  have hc : ∀ z : QB R, z * (n : QB R) = (n : QB R) * z := fun z => (Nat.cast_commute n z).symm
  constructor
  · rintro ⟨ha, hb, y, hy, hγ⟩
    refine ⟨(unit_iff O h1 hm γ).1 ⟨ha, hb⟩, fun x hx => ⟨-(x * ((γ⁻¹ : (QB R)ˣ) : QB R) * y),
      hn _ (hm _ _ (hm _ _ hx hb) hy), ?_⟩⟩
    have e : x * ((γ⁻¹ : (QB R)ˣ) : QB R) * (γ : QB R) = x := by
      rw [mul_assoc, Units.inv_mul, mul_one]
    have e3 : x * ((γ⁻¹ : (QB R)ˣ) : QB R) * ((n : QB R) * y) =
        (n : QB R) * (x * ((γ⁻¹ : (QB R)ˣ) : QB R) * y) := by
      rw [← mul_assoc, hc, mul_assoc]
    rw [app_simEquiv]
    calc x * ((γ⁻¹ : (QB R)ˣ) : QB R) - x
        = x * ((γ⁻¹ : (QB R)ˣ) : QB R) - x * ((γ⁻¹ : (QB R)ˣ) : QB R) * (γ : QB R) := by rw [e]
      _ = x * ((γ⁻¹ : (QB R)ˣ) : QB R) -
          x * ((γ⁻¹ : (QB R)ˣ) : QB R) * (1 + (n : QB R) * y) := by rw [← hγ]
      _ = (n : QB R) * -(x * ((γ⁻¹ : (QB R)ˣ) : QB R) * y) := by
        rw [mul_add, mul_one, e3, mul_neg]; abel
  · rintro ⟨hs, hcg⟩
    obtain ⟨ha, hb⟩ := (unit_iff O h1 hm γ).2 hs
    obtain ⟨y, hy, hxy⟩ := hcg 1 h1
    rw [app_simEquiv, one_mul] at hxy
    refine ⟨ha, hb, -((γ : QB R) * y), hn _ (hm _ _ ha hy), ?_⟩
    have e : (γ : QB R) * ((γ⁻¹ : (QB R)ˣ) : QB R) = 1 := Units.mul_inv γ
    have e2 : (γ : QB R) * (((γ⁻¹ : (QB R)ˣ) : QB R) - 1) = (γ : QB R) * ((n : QB R) * y) := by
      rw [hxy]
    rw [mul_sub, e, mul_one, ← mul_assoc, hc] at e2
    calc (γ : QB R) = 1 - (1 - (γ : QB R)) := by abel
      _ = 1 + (n : QB R) * -((γ : QB R) * y) := by rw [e2]; noncomm_ring

end Lattice

/-- Moving a double coset from `K \ G / Γ` to `Γ \ G / K` by `g ↦ g⁻¹`:
`g' = k g b ↔ g⁻¹ = b g'⁻¹ k`. -/
theorem rel_inv_iff {G : Type} [Group G] (g g' k b : G) :
    g' = k * g * b ↔ g⁻¹ = b * g'⁻¹ * k := by
  constructor
  · rintro rfl
    group
  · intro h
    have e : g = (b * g'⁻¹ * k)⁻¹ := by rw [← h, inv_inv]
    rw [e]
    group

end DeligneY3Bridges
