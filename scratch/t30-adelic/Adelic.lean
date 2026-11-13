import Mathlib
import ZInQKernel.HDecomp.Vigneras.Local

/-!
# t30-adelic, part G1-adelic (b): the adelic normalizer quotient of A3

`B̂ = B ⊗ 𝔸_f` is the restricted product of the `B_p = ℍ[ℚ_p, 2, 0, -3]` with respect to N5's
lattices `𝒪_p` (`GlueVigneras.Op`), `𝒪̂ = ∏_p 𝒪_p`, `N` the normalizer of `𝒪̂` in `B̂^×`,
`K₀ = 𝒪̂^×` and `Z = 𝔸_f^×` (the central scalars). Main results:

* `normalizer_component`: `x ∈ N` ⇒ every component `x_p` normalizes `𝒪_p`;
* `mem_sup_iff`: `x ∈ N` lies in `Z K₀` iff `x_p ∈ ℚ_p^× 𝒪_p^×` at `p = 2, 3` (at `p ∤ 6` this
  holds automatically by `unramified_normalizer`): the identification of `N/(Z K₀)` with the
  restricted product of the local quotients, which are trivial at `p ∤ 6`;
* `relIndex_eq_four`: `[N : Z K₀] = 4`.
-/

open GlueVigneras
open scoped RestrictedProduct

namespace G1Adelic

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

section Local

variable (p : ℕ) [Fact p.Prime]

/-- Multiplication in N5's basis (the integer formula of `GlueRepo.A1.combMul`). -/
noncomputable def combMulp (n m : Fin 4 → ℤ_[p]) : Fin 4 → ℤ_[p] :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

theorem combp_mul (n m : Fin 4 → ℤ_[p]) : combp p n * combp p m = combp p (combMulp p n m) := by
  ext <;> simp [combp, combMulp] <;> ring

theorem combp_add (n m : Fin 4 → ℤ_[p]) : combp p n + combp p m = combp p (n + m) := by
  ext <;> simp [combp] <;> ring

theorem combp_neg (n : Fin 4 → ℤ_[p]) : -combp p n = combp p (-n) := by
  ext <;> simp [combp] <;> ring

theorem combp_one : combp p ![1, 0, 0, 0] = 1 := by
  ext <;> simp [combp]

theorem combp_zero : combp p 0 = 0 := by
  ext <;> simp [combp]

/-- `𝒪_p` as a subring of `B_p`. -/
noncomputable def OpSub : Subring (Bp p) where
  carrier := Op p
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨_, (combp_mul p n m).symm⟩
  one_mem' := ⟨_, combp_one p⟩
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨_, (combp_add p n m).symm⟩
  zero_mem' := ⟨_, combp_zero p⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, (combp_neg p n).symm⟩

theorem mem_OpSub {x : Bp p} : x ∈ OpSub p ↔ x ∈ Op p := Iff.rfl

end Local

/-- `B̂ = B ⊗ 𝔸_f`: the restricted product of the `B_p` with respect to the `𝒪_p`. -/
abbrev BA := Πʳ p : Nat.Primes, [Bp (p : ℕ), OpSub (p : ℕ)]

/-- The component `x_p ∈ B_p^×` of `x ∈ B̂^×`. -/
noncomputable def comp (p : Nat.Primes) : BAˣ →* (Bp (p : ℕ))ˣ :=
  Units.map (RestrictedProduct.evalRingHom _ p).toMonoidHom

theorem comp_val (p : Nat.Primes) (x : BAˣ) : ((comp p x : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) =
    (x : BA) p := rfl

theorem comp_inv_val (p : Nat.Primes) (x : BAˣ) :
    (((comp p x)⁻¹ : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) = ((x⁻¹ : BAˣ) : BA) p := rfl

/-- `𝒪̂ = ∏_p 𝒪_p ⊆ B̂`. -/
def Ohat : Set BA := {y | ∀ p : Nat.Primes, y p ∈ Op (p : ℕ)}

/-- The normalizer `N` of `𝒪̂` in `B̂^×`. -/
noncomputable def Nhat : Subgroup BAˣ where
  carrier := {x | ∀ y : BA, y ∈ Ohat ↔ (x : BA) * y * ((x⁻¹ : BAˣ) : BA) ∈ Ohat}
  one_mem' := by intro y; simp
  mul_mem' := by
    intro a b ha hb y
    rw [hb y, ha]
    simp only [Units.val_mul, mul_inv_rev]
    simp only [mul_assoc]
  inv_mem' := by
    intro a ha y
    simp only [inv_inv]
    have : (a : BA) * ((((a⁻¹ : BAˣ) : BA)) * y * (a : BA)) * ((a⁻¹ : BAˣ) : BA) = y := by
      simp only [← mul_assoc, Units.mul_inv, one_mul]
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [ha (((a⁻¹ : BAˣ) : BA) * y * (a : BA)), this]

/-- `K₀ = 𝒪̂^×`. -/
noncomputable def K0 : Subgroup BAˣ where
  carrier := {x | (x : BA) ∈ Ohat ∧ ((x⁻¹ : BAˣ) : BA) ∈ Ohat}
  one_mem' := ⟨fun p => (OpSub (p : ℕ)).one_mem, fun p => (OpSub (p : ℕ)).one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun p => (OpSub (p : ℕ)).mul_mem (ha1 p) (hb1 p), fun p => ?_⟩
    rw [mul_inv_rev]
    exact (OpSub (p : ℕ)).mul_mem (hb2 p) (ha2 p)
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨ha2, by rw [inv_inv]; exact ha1⟩

/-- `Z = 𝔸_f^×`, the central scalars of `B̂^×` (componentwise in `ℚ_p^×`). -/
noncomputable def Zhat : Subgroup BAˣ where
  carrier := {x | ∀ p : Nat.Primes, ∃ c : ℚ_[(p : ℕ)], (x : BA) p = algebraMap _ _ c}
  one_mem' := fun p => ⟨1, by simp⟩
  mul_mem' := by
    intro a b ha hb p
    obtain ⟨c, hc⟩ := ha p
    obtain ⟨d, hd⟩ := hb p
    exact ⟨c * d, by rw [Units.val_mul, RestrictedProduct.mul_apply, hc, hd, map_mul]⟩
  inv_mem' := by
    intro a ha p
    obtain ⟨c, hc⟩ := ha p
    refine ⟨c⁻¹, ?_⟩
    have h1 : (a : BA) p * ((a⁻¹ : BAˣ) : BA) p = 1 := by
      rw [← RestrictedProduct.mul_apply, Units.mul_inv]; rfl
    rw [hc] at h1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at h1
      exact zero_ne_one h1
    calc ((a⁻¹ : BAˣ) : BA) p = algebraMap _ _ c⁻¹ * (algebraMap _ _ c * ((a⁻¹ : BAˣ) : BA) p) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      _ = algebraMap _ _ c⁻¹ := by rw [h1, mul_one]

/-! ### Components of the normalizer -/

open Classical in
/-- The element of `B̂` with component `y` at `p` and `0` elsewhere. -/
noncomputable def single (p : Nat.Primes) (y : Bp (p : ℕ)) : BA :=
  RestrictedProduct.single (fun q : Nat.Primes => OpSub (q : ℕ)) p y

theorem single_apply_self (p : Nat.Primes) (y : Bp (p : ℕ)) : single p y p = y := by
  classical
  simp [single]

theorem single_apply_ne {p q : Nat.Primes} (h : q ≠ p) (y : Bp (p : ℕ)) : single p y q = 0 := by
  classical
  simp [single, h]

theorem conj_apply (x : BAˣ) (y : BA) (q : Nat.Primes) :
    ((x : BA) * y * ((x⁻¹ : BAˣ) : BA)) q =
      ((comp q x : (Bp (q : ℕ))ˣ) : Bp (q : ℕ)) * y q * (((comp q x)⁻¹ : (Bp (q : ℕ))ˣ) :
        Bp (q : ℕ)) := by
  rw [comp_val, comp_inv_val, RestrictedProduct.mul_apply, RestrictedProduct.mul_apply]

theorem single_mem_Ohat (p : Nat.Primes) {y : Bp (p : ℕ)} (hy : y ∈ Op (p : ℕ)) :
    single p y ∈ Ohat := by
  intro q
  by_cases h : q = p
  · subst h; rw [single_apply_self]; exact hy
  · rw [single_apply_ne h]; exact (OpSub (q : ℕ)).zero_mem

/-- **Components of the normalizer.** If `x ∈ N`, every `x_p` normalizes `𝒪_p`. -/
theorem normalizer_component {x : BAˣ} (hx : x ∈ Nhat) (p : Nat.Primes) :
    comp p x ∈ normalizerOp (p : ℕ) := by
  intro y
  have key : ∀ q : Nat.Primes, ((x : BA) * single p y * ((x⁻¹ : BAˣ) : BA)) q ∈ Op (q : ℕ) ↔
      (q = p → ((comp p x : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) * y *
        (((comp p x)⁻¹ : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) ∈ Op (p : ℕ)) := by
    intro q
    rw [conj_apply]
    by_cases h : q = p
    · subst h; rw [single_apply_self]; simp
    · rw [single_apply_ne h, mul_zero, zero_mul]
      simp only [h, IsEmpty.forall_iff, iff_true]
      exact (OpSub (q : ℕ)).zero_mem
  constructor
  · intro hy
    have := (hx (single p y)).mp (single_mem_Ohat p hy) p
    exact (key p).mp this rfl
  · intro hy
    have h1 : (x : BA) * single p y * ((x⁻¹ : BAˣ) : BA) ∈ Ohat := fun q => (key q).mpr
      (fun h => by subst h; exact hy)
    have := (hx (single p y)).mpr h1 p
    rwa [single_apply_self] at this

/-! ### `Z K₀` is detected componentwise -/

theorem Zhat_le_center : Zhat ≤ Subgroup.center BAˣ := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  apply RestrictedProduct.ext
  intro p
  obtain ⟨c, hc⟩ := hz p
  rw [Units.val_mul, Units.val_mul, RestrictedProduct.mul_apply, RestrictedProduct.mul_apply, hc,
    Algebra.commutes]

instance Zhat_normal : Zhat.Normal := Subgroup.normal_of_le_center Zhat_le_center

theorem comp_mem_OpUnits {k : BAˣ} (hk : k ∈ K0) (p : Nat.Primes) :
    comp p k ∈ OpUnits (p : ℕ) := ⟨hk.1 p, hk.2 p⟩

/-- Elements of `Z K₀` are componentwise in `ℚ_p^× 𝒪_p^×`. -/
theorem comp_mem_scal_of_mem_sup {x : BAˣ} (hx : x ∈ Zhat ⊔ K0) (p : Nat.Primes) :
    comp p x ∈ scalOpUnits (p : ℕ) := by
  have hx' : x ∈ ((Zhat ⊔ K0 : Subgroup BAˣ) : Set BAˣ) := hx
  rw [Subgroup.normal_mul] at hx'
  obtain ⟨z, hz, k, hk, rfl⟩ := hx'
  obtain ⟨c, hc⟩ := hz p
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : (z : BA) p * ((z⁻¹ : BAˣ) : BA) p = 1 := by
      rw [← RestrictedProduct.mul_apply, Units.mul_inv]; rfl
    rw [hc, map_zero, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨Units.mk0 c hc0, comp p k, comp_mem_OpUnits hk p, ?_⟩
  rw [map_mul, Units.val_mul, comp_val p z, hc, Units.val_mk0, Algebra.smul_def]

/-- At `p ∤ 6`, components of the normalizer are in `ℚ_p^× 𝒪_p^×` (`unramified_normalizer`). -/
theorem comp_mem_scal_of_unramified {x : BAˣ} (hx : x ∈ Nhat) (p : Nat.Primes)
    (h2 : (p : ℕ) ≠ 2) (h3 : (p : ℕ) ≠ 3) : comp p x ∈ scalOpUnits (p : ℕ) :=
  unramified_normalizer (p : ℕ) h2 h3 (comp p x)
    (fun y hy => (normalizer_component hx p y).mp hy)

/-- Componentwise `ℚ_p^× 𝒪_p^×` implies `Z K₀` (the scalars are chosen `1` at the cofinitely
many `p` where `x_p ∈ 𝒪_p^×`). -/
theorem mem_sup_of_forall {x : BAˣ}
    (hx : ∀ p : Nat.Primes, comp p x ∈ scalOpUnits (p : ℕ)) : x ∈ Zhat ⊔ K0 := by
  classical
  have hcof : ∀ᶠ p : Nat.Primes in Filter.cofinite, comp p x ∈ OpUnits (p : ℕ) := by
    filter_upwards [(x : BA).2, ((x⁻¹ : BAˣ) : BA).2] with p h1 h2
    exact ⟨h1, h2⟩
  let c : ∀ p : Nat.Primes, ℚ_[(p : ℕ)]ˣ := fun p =>
    if h : comp p x ∈ OpUnits (p : ℕ) then 1 else (hx p).choose
  have hc1 : ∀ p : Nat.Primes, comp p x ∈ OpUnits (p : ℕ) → c p = 1 := fun p h => dite_eq_left h
  have hcu : ∀ p : Nat.Primes, ∃ u ∈ OpUnits (p : ℕ), ((comp p x : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) =
      ((c p : ℚ_[(p : ℕ)]ˣ) : ℚ_[(p : ℕ)]) • (u : Bp (p : ℕ)) := by
    intro p
    by_cases h : comp p x ∈ OpUnits (p : ℕ)
    · exact ⟨comp p x, h, by rw [hc1 p h]; simp⟩
    · have := (hx p).choose_spec
      simp only [c, dite_eq_right h]
      exact this
  let z : BA := ⟨fun p => algebraMap ℚ_[(p : ℕ)] (Bp (p : ℕ)) ((c p : ℚ_[(p : ℕ)]ˣ) : ℚ_[(p : ℕ)]),
    by
      filter_upwards [hcof] with p hp
      rw [hc1 p hp, Units.val_one, map_one]
      exact (OpSub (p : ℕ)).one_mem⟩
  let z' : BA := ⟨fun p => algebraMap ℚ_[(p : ℕ)] (Bp (p : ℕ))
      (((c p)⁻¹ : ℚ_[(p : ℕ)]ˣ) : ℚ_[(p : ℕ)]), by
      filter_upwards [hcof] with p hp
      rw [hc1 p hp, inv_one, Units.val_one, map_one]
      exact (OpSub (p : ℕ)).one_mem⟩
  have hzz' : z * z' = 1 := by
    refine RestrictedProduct.ext _ _ (fun p => ?_)
    rw [RestrictedProduct.mul_apply, RestrictedProduct.one_apply]
    show algebraMap ℚ_[(p : ℕ)] (Bp (p : ℕ)) _ * algebraMap ℚ_[(p : ℕ)] (Bp (p : ℕ)) _ = 1
    rw [← map_mul, Units.mul_inv, map_one]
  have hz'z : z' * z = 1 := by
    refine RestrictedProduct.ext _ _ (fun p => ?_)
    rw [RestrictedProduct.mul_apply, RestrictedProduct.one_apply]
    show algebraMap ℚ_[(p : ℕ)] (Bp (p : ℕ)) _ * algebraMap ℚ_[(p : ℕ)] (Bp (p : ℕ)) _ = 1
    rw [← map_mul, Units.inv_mul, map_one]
  let zU : BAˣ := ⟨z, z', hzz', hz'z⟩
  have hzZ : zU ∈ Zhat := fun p => ⟨_, rfl⟩
  have hk : zU⁻¹ * x ∈ K0 := by
    constructor
    · intro p
      obtain ⟨u, hu, hxu⟩ := hcu p
      show z' p * (x : BA) p ∈ Op (p : ℕ)
      show algebraMap _ _ (((c p)⁻¹ : ℚ_[(p : ℕ)]ˣ) : ℚ_[(p : ℕ)]) * (x : BA) p ∈ Op (p : ℕ)
      rw [← comp_val, hxu, ← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
      exact hu.1
    · intro p
      obtain ⟨u, hu, hxu⟩ := hcu p
      rw [mul_inv_rev, inv_inv]
      show ((x⁻¹ : BAˣ) : BA) p * z p ∈ Op (p : ℕ)
      show ((x⁻¹ : BAˣ) : BA) p * algebraMap _ _ ((c p : ℚ_[(p : ℕ)]ˣ) : ℚ_[(p : ℕ)]) ∈
        Op (p : ℕ)
      rw [← comp_inv_val]
      have e : (((comp p x)⁻¹ : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) =
          (((c p)⁻¹ : ℚ_[(p : ℕ)]ˣ) : ℚ_[(p : ℕ)]) • ((u⁻¹ : (Bp (p : ℕ))ˣ) : Bp (p : ℕ)) := by
        apply Units.inv_eq_of_mul_eq_one_right
        rw [hxu, smul_mul_smul_comm, Units.mul_inv, Units.mul_inv, one_smul]
      rw [e, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, Units.mul_inv, one_smul]
      exact hu.2
  have e : x = zU * (zU⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hzZ hk

/-- **The identification of `N/(Z K₀)` with the restricted product of the local quotients.**
`x ∈ N` lies in `Z K₀` iff each component `x_p` lies in `ℚ_p^× 𝒪_p^×`. -/
theorem mem_sup_iff_forall {x : BAˣ} :
    x ∈ Zhat ⊔ K0 ↔ ∀ p : Nat.Primes, comp p x ∈ scalOpUnits (p : ℕ) :=
  ⟨fun h => comp_mem_scal_of_mem_sup h, mem_sup_of_forall⟩

/-- The primes `2` and `3`. -/
def P2 : Nat.Primes := ⟨2, Nat.prime_two⟩
def P3 : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- **The local quotients are trivial at `p ∤ 6`**: for `x ∈ N`, `x ∈ Z K₀` iff
`x_2 ∈ ℚ_2^× 𝒪_2^×` and `x_3 ∈ ℚ_3^× 𝒪_3^×`. -/
theorem mem_sup_iff {x : BAˣ} (hx : x ∈ Nhat) :
    x ∈ Zhat ⊔ K0 ↔ comp P2 x ∈ scalOpUnits ((P2 : Nat.Primes) : ℕ) ∧
      comp P3 x ∈ scalOpUnits ((P3 : Nat.Primes) : ℕ) := by
  rw [mem_sup_iff_forall]
  refine ⟨fun h => ⟨h P2, h P3⟩, fun ⟨h2, h3⟩ p => ?_⟩
  by_cases hp2 : (p : ℕ) = 2
  · have : p = P2 := Subtype.ext hp2
    subst this; exact h2
  by_cases hp3 : (p : ℕ) = 3
  · have : p = P3 := Subtype.ext hp3
    subst this; exact h3
  exact comp_mem_scal_of_unramified hx p hp2 hp3

/-! ### The index `[N : Z K₀] = 4` -/

theorem hP2 : ((P2 : Nat.Primes) : ℕ) = 2 ∨ ((P2 : Nat.Primes) : ℕ) = 3 := Or.inl rfl
theorem hP3 : ((P3 : Nat.Primes) : ℕ) = 2 ∨ ((P3 : Nat.Primes) : ℕ) = 3 := Or.inr rfl

/-- `ℚ_p^× 𝒪_p^×` at `p = 2, 3`. -/
noncomputable abbrev Hloc (p : Nat.Primes) (hp : (p : ℕ) = 2 ∨ (p : ℕ) = 3) :
    Subgroup (Bp (p : ℕ))ˣ :=
  scalOpUnitsSubgroup (p : ℕ) hp

instance Hloc_normal (p : Nat.Primes) (hp : (p : ℕ) = 2 ∨ (p : ℕ) = 3) : (Hloc p hp).Normal :=
  Subgroup.normal_of_index_eq_two (index_scalOpUnits (p : ℕ) hp)

theorem mem_Hloc {p : Nat.Primes} {hp : (p : ℕ) = 2 ∨ (p : ℕ) = 3} {g : (Bp (p : ℕ))ˣ} :
    g ∈ Hloc p hp ↔ g ∈ scalOpUnits (p : ℕ) := Iff.rfl

/-- The map `N → ∏_{p | 6} B_p^×/ℚ_p^×𝒪_p^×` (the restricted product of the local quotients,
which are trivial at `p ∤ 6`). -/
noncomputable def Phi : Nhat →* ((Bp 2)ˣ ⧸ Hloc P2 hP2) × ((Bp 3)ˣ ⧸ Hloc P3 hP3) :=
  MonoidHom.prod ((QuotientGroup.mk' (Hloc P2 hP2)).comp ((comp P2).comp Nhat.subtype))
    ((QuotientGroup.mk' (Hloc P3 hP3)).comp ((comp P3).comp Nhat.subtype))

theorem ker_Phi : Phi.ker = (Zhat ⊔ K0).subgroupOf Nhat := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sup_iff x.2]
  simp only [Phi, MonoidHom.prod_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    Prod.mk_eq_one, QuotientGroup.eq_one_iff]
  rfl

theorem not_mem_scal_of_pi {p : Nat.Primes} (hp : (p : ℕ) = 2 ∨ (p : ℕ) = 3)
    {π : (Bp (p : ℕ))ˣ} (hπ : ‖nrd (p : ℕ) π‖ = ((p : ℕ) : ℝ)⁻¹) : π ∉ scalOpUnits (p : ℕ) := by
  rw [mem_scalOpUnits_iff (p : ℕ) hp]
  rintro ⟨m, hm⟩
  have p0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have p1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  rw [hπ, ← zpow_neg_one] at hm
  have := zpow_right_injective₀ p0 p1.ne' hm
  omega

open Classical in
/-- The element of `B̂^×` with component `g` at `p` and `1` elsewhere. -/
noncomputable def unitSingle (p : Nat.Primes) (g : (Bp (p : ℕ))ˣ) : BAˣ where
  val := RestrictedProduct.mulSingle (fun q : Nat.Primes => OpSub (q : ℕ)) p (g : Bp (p : ℕ))
  inv := RestrictedProduct.mulSingle (fun q : Nat.Primes => OpSub (q : ℕ)) p
    ((g⁻¹ : (Bp (p : ℕ))ˣ) : Bp (p : ℕ))
  val_inv := by rw [← RestrictedProduct.mulSingle_mul, Units.mul_inv,
    RestrictedProduct.mulSingle_one]
  inv_val := by rw [← RestrictedProduct.mulSingle_mul, Units.inv_mul,
    RestrictedProduct.mulSingle_one]

theorem comp_unitSingle_self (p : Nat.Primes) (g : (Bp (p : ℕ))ˣ) : comp p (unitSingle p g) = g := by
  classical
  apply Units.ext
  rw [comp_val]
  simp [unitSingle]

theorem comp_unitSingle_ne {p q : Nat.Primes} (h : q ≠ p) (g : (Bp (p : ℕ))ˣ) :
    comp q (unitSingle p g) = 1 := by
  classical
  apply Units.ext
  rw [comp_val]
  simp [unitSingle, h]

theorem unitSingle_mem (p : Nat.Primes) (hp : (p : ℕ) = 2 ∨ (p : ℕ) = 3) (g : (Bp (p : ℕ))ˣ) :
    unitSingle p g ∈ Nhat := by
  intro y
  have key : ∀ q : Nat.Primes, y q ∈ Op (q : ℕ) ↔
      ((unitSingle p g : BA) * y * (((unitSingle p g)⁻¹ : BAˣ) : BA)) q ∈ Op (q : ℕ) := by
    intro q
    rw [conj_apply]
    by_cases h : q = p
    · subst h
      rw [comp_unitSingle_self]
      have := normalizerOp_eq_univ (q : ℕ) hp
      have hg : g ∈ normalizerOp (q : ℕ) := by rw [this]; trivial
      exact hg (y q)
    · rw [comp_unitSingle_ne h]
      simp
  exact forall_congr' key

/-- Every class in the local quotient at `p = 2, 3` is the image of `1` or of a uniformizer. -/
theorem quot_cases (p : Nat.Primes) (hp : (p : ℕ) = 2 ∨ (p : ℕ) = 3) {π : (Bp (p : ℕ))ˣ}
    (hπ : π ∉ scalOpUnits (p : ℕ)) (a : (Bp (p : ℕ))ˣ ⧸ Hloc p hp) :
    a = 1 ∨ a = QuotientGroup.mk π := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  by_cases hg : g ∈ scalOpUnits (p : ℕ)
  · left
    exact (QuotientGroup.eq_one_iff g).mpr hg
  · right
    rw [QuotientGroup.eq]
    have h2 := Subgroup.mul_mem_iff_of_index_two (index_scalOpUnits (p : ℕ) hp) (a := g⁻¹) (b := π)
    rw [mem_Hloc, mem_Hloc] at h2
    have hg' : g⁻¹ ∉ Hloc p hp := fun h => hg (by
      have := (Hloc p hp).inv_mem h
      rw [inv_inv] at this
      exact this)
    exact h2.mpr (iff_of_false hg' hπ)

theorem Phi_surjective : Function.Surjective Phi := by
  obtain ⟨π2, hπ2⟩ := exists_pi ((P2 : Nat.Primes) : ℕ) hP2
  obtain ⟨π3, hπ3⟩ := exists_pi ((P3 : Nat.Primes) : ℕ) hP3
  have hn2 := not_mem_scal_of_pi hP2 hπ2
  have hn3 := not_mem_scal_of_pi hP3 hπ3
  have h23 : P3 ≠ P2 := by
    intro h; have := congrArg Subtype.val h; simp [P2, P3] at this
  let s2 : Nhat := ⟨unitSingle P2 π2, unitSingle_mem P2 hP2 π2⟩
  let s3 : Nhat := ⟨unitSingle P3 π3, unitSingle_mem P3 hP3 π3⟩
  have e2 : Phi s2 = (QuotientGroup.mk π2, 1) := by
    simp only [Phi, MonoidHom.prod_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      Subgroup.coe_subtype, s2]
    rw [comp_unitSingle_self, comp_unitSingle_ne h23]
    rfl
  have e3 : Phi s3 = (1, QuotientGroup.mk π3) := by
    simp only [Phi, MonoidHom.prod_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      Subgroup.coe_subtype, s3]
    rw [comp_unitSingle_self, comp_unitSingle_ne h23.symm]
    rfl
  rintro ⟨a, b⟩
  have ha : ∃ x : Nhat, Phi x = (a, 1) := by
    rcases quot_cases P2 hP2 hn2 a with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨s2, e2⟩
  have hb : ∃ x : Nhat, Phi x = (1, b) := by
    rcases quot_cases P3 hP3 hn3 b with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨s3, e3⟩
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  exact ⟨x * y, by rw [map_mul, hx, hy]; exact Prod.ext (mul_one a) (one_mul b)⟩

/-- **`[N : 𝔸_f^× K₀] = 4`** (A3(a), adelic form): `N/(𝔸_f^× K₀) ≅ ∏_{p | 6} B_p^×/ℚ_p^×𝒪_p^×
≅ (ℤ/2)²`. -/
theorem relIndex_eq_four : (Zhat ⊔ K0).relIndex Nhat = 4 := by
  rw [Subgroup.relIndex, ← ker_Phi, Subgroup.index_ker, MonoidHom.range_eq_top.mpr Phi_surjective,
    Subgroup.card_top, Nat.card_prod]
  have h2 : Nat.card ((Bp 2)ˣ ⧸ Hloc P2 hP2) = 2 := index_scalOpUnits _ hP2
  have h3 : Nat.card ((Bp 3)ˣ ⧸ Hloc P3 hP3) = 2 := index_scalOpUnits _ hP3
  rw [h2, h3]

instance sup_subgroupOf_normal : ((Zhat ⊔ K0).subgroupOf Nhat).Normal :=
  ker_Phi ▸ Phi.normal_ker

/-- `N/(𝔸_f^× K₀)` is isomorphic to the product of the two nontrivial local quotients. -/
noncomputable def quotEquiv : Nhat ⧸ (Zhat ⊔ K0).subgroupOf Nhat ≃*
    ((Bp 2)ˣ ⧸ Hloc P2 hP2) × ((Bp 3)ˣ ⧸ Hloc P3 hP3) :=
  (QuotientGroup.quotientMulEquivOfEq ker_Phi.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Phi Phi_surjective)

end G1Adelic

#print axioms G1Adelic.relIndex_eq_four
#print axioms G1Adelic.mem_sup_iff_forall
#print axioms G1Adelic.normalizer_component
