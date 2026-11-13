import Mathlib
import ZInQKernel.HDecomp.Vigneras.Local
import ZInQKernel.HDecomp.Repo.A1Quaternion

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

/-! ### The level-3 subgroup `K₃` and the count `|Γ'| = 4 · [K₀ : (Z ∩ K₀) K₃]` -/

/-- The prime `3` as a natural number, the index of `P3`. -/
abbrev q3 : ℕ := ((P3 : Nat.Primes) : ℕ)

/-- `3 𝒪_3 ⊆ B_3`. -/
def I3 : Set (Bp q3) := {y | ∃ n : Fin 4 → ℤ_[q3], y = (3 : ℚ_[q3]) • combp q3 n}

theorem I3_zero : (0 : Bp q3) ∈ I3 := ⟨0, by rw [combp_zero, smul_zero]⟩

theorem I3_add {a b : Bp q3} (ha : a ∈ I3) (hb : b ∈ I3) : a + b ∈ I3 := by
  obtain ⟨n, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  exact ⟨n + m, by rw [← smul_add, combp_add]⟩

theorem I3_neg {a : Bp q3} (ha : a ∈ I3) : -a ∈ I3 := by
  obtain ⟨n, rfl⟩ := ha
  exact ⟨-n, by rw [← smul_neg, combp_neg]⟩

theorem I3_mul_left {a y : Bp q3} (ha : a ∈ Op q3) (hy : y ∈ I3) : a * y ∈ I3 := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hy
  exact ⟨combMulp q3 m n, by rw [mul_smul_comm, combp_mul]⟩

theorem I3_mul_right {a y : Bp q3} (ha : a ∈ Op q3) (hy : y ∈ I3) : y * a ∈ I3 := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hy
  exact ⟨combMulp q3 n m, by rw [smul_mul_assoc, combp_mul]⟩

theorem I3_conj {g : (Bp q3)ˣ} (hg : g ∈ normalizerOp q3) {y : Bp q3} (hy : y ∈ I3) :
    (g : Bp q3) * y * ((g⁻¹ : (Bp q3)ˣ) : Bp q3) ∈ I3 := by
  obtain ⟨n, rfl⟩ := hy
  obtain ⟨m, hm⟩ := (hg (combp q3 n)).mp ⟨n, rfl⟩
  exact ⟨m, by rw [mul_smul_comm, smul_mul_assoc, ← hm]⟩

/-- `K₃ = ker(K₀ → (𝒪/3𝒪)^×)`: units of `𝒪̂` congruent to `1` modulo `3𝒪_3`. -/
noncomputable def K3 : Subgroup BAˣ where
  carrier := {u | u ∈ K0 ∧ (u : BA) P3 - 1 ∈ I3}
  one_mem' := ⟨K0.one_mem, by
    rw [Units.val_one, RestrictedProduct.one_apply, sub_self]; exact I3_zero⟩
  mul_mem' := by
    rintro u v ⟨hu, hu3⟩ ⟨hv, hv3⟩
    refine ⟨K0.mul_mem hu hv, ?_⟩
    rw [Units.val_mul, RestrictedProduct.mul_apply,
      show (u : BA) P3 * (v : BA) P3 - 1 = ((u : BA) P3 - 1) * (v : BA) P3 + ((v : BA) P3 - 1)
        by rw [sub_mul, one_mul]; abel]
    exact I3_add (I3_mul_right (hv.1 P3) hu3) hv3
  inv_mem' := by
    rintro u ⟨hu, hu3⟩
    refine ⟨K0.inv_mem hu, ?_⟩
    have h1 : ((u⁻¹ : BAˣ) : BA) P3 * (u : BA) P3 = 1 := by
      rw [← RestrictedProduct.mul_apply, Units.inv_mul]; rfl
    rw [show ((u⁻¹ : BAˣ) : BA) P3 - 1 = -(((u⁻¹ : BAˣ) : BA) P3 * ((u : BA) P3 - 1)) by
      rw [mul_sub, h1, mul_one, neg_sub]]
    exact I3_neg (I3_mul_left (hu.2 P3) hu3)

theorem K3_le_K0 : K3 ≤ K0 := fun _ h => h.1

theorem K0_le_Nhat : K0 ≤ Nhat := by
  rintro u ⟨hu1, hu2⟩ y
  constructor
  · intro hy p
    rw [RestrictedProduct.mul_apply, RestrictedProduct.mul_apply]
    exact (OpSub (p : ℕ)).mul_mem ((OpSub (p : ℕ)).mul_mem (hu1 p) (hy p)) (hu2 p)
  · intro hy p
    have e : y = ((u⁻¹ : BAˣ) : BA) * ((u : BA) * y * ((u⁻¹ : BAˣ) : BA)) * (u : BA) := by
      simp only [← mul_assoc, Units.inv_mul, one_mul]
      rw [mul_assoc, Units.inv_mul, mul_one]
    rw [e, RestrictedProduct.mul_apply, RestrictedProduct.mul_apply]
    exact (OpSub (p : ℕ)).mul_mem ((OpSub (p : ℕ)).mul_mem (hu2 p) (hy p)) (hu1 p)

theorem Zhat_le_Nhat : Zhat ≤ Nhat := by
  intro z hz y
  have hc := Subgroup.mem_center_iff.mp (Zhat_le_center hz)
  have e : (z : BA) * y * ((z⁻¹ : BAˣ) : BA) = y := by
    have h1 : (z : BA) * y = y * (z : BA) := by
      apply RestrictedProduct.ext _ _ (fun p => ?_)
      obtain ⟨c, hc⟩ := hz p
      rw [RestrictedProduct.mul_apply, RestrictedProduct.mul_apply, hc, Algebra.commutes]
    rw [h1, mul_assoc, Units.mul_inv, mul_one]
  rw [e]

/-- `N` normalizes `K₃`. -/
theorem conj_mem_K3 {g : BAˣ} (hg : g ∈ Nhat) {k : BAˣ} (hk : k ∈ K3) : g * k * g⁻¹ ∈ K3 := by
  obtain ⟨⟨hk1, hk2⟩, hk3⟩ := hk
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (hg (k : BA)).mp hk1
  · rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc]
    exact (hg ((k⁻¹ : BAˣ) : BA)).mp hk2
  · rw [Units.val_mul, Units.val_mul, RestrictedProduct.mul_apply, RestrictedProduct.mul_apply]
    have h1 : (g : BA) P3 * ((g⁻¹ : BAˣ) : BA) P3 = 1 := by
      rw [← RestrictedProduct.mul_apply, Units.mul_inv]; rfl
    rw [show (g : BA) P3 * (k : BA) P3 * ((g⁻¹ : BAˣ) : BA) P3 - 1 =
        (g : BA) P3 * ((k : BA) P3 - 1) * ((g⁻¹ : BAˣ) : BA) P3 by
      rw [mul_sub, sub_mul, mul_one, h1]]
    rw [← comp_val, ← comp_inv_val]
    exact I3_conj (normalizer_component hg P3) hk3

instance sup_K3_normal : ((Zhat ⊔ K3).subgroupOf Nhat).Normal where
  conj_mem := by
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' : (n : BAˣ) ∈ ((Zhat ⊔ K3 : Subgroup BAˣ) : Set BAˣ) := hn
    rw [Subgroup.normal_mul] at hn'
    obtain ⟨z, hz, k, hk, hzk⟩ := hn'
    have hzc := Subgroup.mem_center_iff.mp (Zhat_le_center hz)
    have e : ((g * n * g⁻¹ : Nhat) : BAˣ) = z * ((g : BAˣ) * k * (g : BAˣ)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hzk]
      rw [← mul_assoc, ← mul_assoc, hzc (g : BAˣ)]
      group
    rw [e]
    exact Subgroup.mul_mem_sup hz (conj_mem_K3 g.2 hk)

/-- Dedekind's modular law for a normal `Z` (copied from `G1Count.lean`). -/
theorem sup_inf_eq {G : Type*} [Group G] (Z K₀ K₃ : Subgroup G) [Z.Normal] (hK : K₃ ≤ K₀) :
    (Z ⊔ K₃) ⊓ K₀ = (Z ⊓ K₀) ⊔ K₃ := by
  apply le_antisymm
  · rintro x ⟨hx, hx0⟩
    have hx' : x ∈ ((Z ⊔ K₃ : Subgroup G) : Set G) := hx
    rw [Subgroup.normal_mul] at hx'
    obtain ⟨z, hz, k, hk, rfl⟩ := hx'
    have hz0 : z ∈ K₀ := by
      have := K₀.mul_mem hx0 (K₀.inv_mem (hK hk))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hz, hz0⟩) (Subgroup.mem_sup_right hk)
  · refine sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hK)

/-- **The count of A3: `|Γ'| = [N : 𝔸_f^× K₃] = 4 · [K₀ : (𝔸_f^× ∩ K₀) K₃]`.** -/
theorem gamma_count :
    (Zhat ⊔ K3).relIndex Nhat = 4 * ((Zhat ⊓ K0) ⊔ K3).relIndex K0 := by
  have hZN := Zhat_le_Nhat
  have hK0N := K0_le_Nhat
  have hK3N : K3 ≤ Nhat := K3_le_K0.trans hK0N
  have hle : Zhat ⊔ K3 ≤ Zhat ⊔ K0 := sup_le_sup_left K3_le_K0 Zhat
  have hZK0N : Zhat ⊔ K0 ≤ Nhat := sup_le hZN hK0N
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle hZK0N, relIndex_eq_four, mul_comm]
  congr 1
  rw [← Subgroup.relIndex_subgroupOf hZK0N]
  have hsup : K0.subgroupOf Nhat ⊔ (Zhat ⊔ K3).subgroupOf Nhat = (Zhat ⊔ K0).subgroupOf Nhat := by
    rw [← Subgroup.subgroupOf_sup hK0N (sup_le hZN hK3N)]
    congr 1
    apply le_antisymm
    · exact sup_le le_sup_right hle
    · exact sup_le (le_sup_of_le_right le_sup_left) le_sup_left
  rw [← hsup, Subgroup.relIndex_sup_right, Subgroup.relIndex_subgroupOf hK0N,
    ← Subgroup.inf_relIndex_right, sup_inf_eq Zhat K0 K3 K3_le_K0]

/-! ### `[K₀ : ℤ̂^× K₃] = 36`, hence `|Γ'| = 144` -/

open GlueRepo.A1 (mul3 one3 nrd3 isUnit3_iff card_units_mod3)

/-- `𝒪/3𝒪` in N5's coordinates (glue-repo's `mul3`, `one3`). -/
def R3 : Type := Fin 4 → ZMod 3

instance : Monoid R3 where
  mul := mul3
  one := one3
  mul_assoc a b c := by
    show mul3 (mul3 a b) c = mul3 a (mul3 b c)
    funext k; fin_cases k <;> simp [mul3] <;> ring
  one_mul a := by
    show mul3 one3 a = a
    funext k; fin_cases k <;> simp [mul3, one3]
  mul_one a := by
    show mul3 a one3 = a
    funext k; fin_cases k <;> simp [mul3, one3]

/-- The identity `(Fin 4 → ZMod 3) → R3`. -/
def R3.mk (f : Fin 4 → ZMod 3) : R3 := f

theorem R3_mul_def (a b : R3) : a * b = R3.mk (mul3 a b) := rfl
theorem R3_one_def : (1 : R3) = R3.mk one3 := rfl

theorem card_units_R3 : Nat.card R3ˣ = 72 := by
  let e : R3ˣ ≃ {x : Fin 4 → ZMod 3 // ∃ y, mul3 x y = one3 ∧ mul3 y x = one3} :=
    { toFun := fun u => ⟨u.val, u.inv, u.val_inv, u.inv_val⟩
      invFun := fun x => ⟨x.1, x.2.choose, x.2.choose_spec.1, x.2.choose_spec.2⟩
      left_inv := fun u => Units.ext rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, card_units_mod3]

theorem q3_eq : q3 = 3 := rfl

/-- Reduction `ℤ_3 → ℤ/3`. -/
noncomputable def t3 : ℤ_[q3] →+* ZMod 3 :=
  (ZMod.ringEquivCongr q3_eq).toRingHom.comp PadicInt.toZMod

theorem t3_eq_zero_iff (z : ℤ_[q3]) : t3 z = 0 ↔ PadicInt.toZMod z = 0 := by
  constructor
  · intro h
    apply (ZMod.ringEquivCongr q3_eq).injective
    rw [map_zero]; exact h
  · intro h
    show (ZMod.ringEquivCongr q3_eq) (PadicInt.toZMod z) = 0
    rw [h, map_zero]

theorem t3_three : t3 (3 : ℤ_[q3]) = 0 := by
  rw [map_ofNat]; decide

/-- Coordinates of `x ∈ B_3` in N5's basis, as `3`-adic integers when integral. -/
noncomputable def zc (x : Bp q3) (k : Fin 4) : ℤ_[q3] :=
  if h : ‖coord q3 x k‖ ≤ 1 then ⟨coord q3 x k, h⟩ else 0

theorem coord_combp (n : Fin 4 → ℤ_[q3]) (k : Fin 4) : coord q3 (combp q3 n) k = n k := by
  fin_cases k <;> simp [coord, combp] <;> ring

theorem zc_combp (n : Fin 4 → ℤ_[q3]) : zc (combp q3 n) = n := by
  funext k
  have h := coord_combp n k
  have hn : ‖coord q3 (combp q3 n) k‖ ≤ 1 := by rw [h]; exact PadicInt.norm_le_one _
  simp only [zc, hn, ↓reduceDIte]
  apply Subtype.ext
  exact h

theorem combp_injective : Function.Injective (combp q3) := by
  intro n m h
  rw [← zc_combp n, ← zc_combp m, h]

/-- Reduction `𝒪_3 → 𝒪/3𝒪`. -/
noncomputable def red (x : Bp q3) : R3 := fun k => t3 (zc x k)

theorem red_combp (n : Fin 4 → ℤ_[q3]) : red (combp q3 n) = R3.mk (fun k => t3 (n k)) := by
  unfold red R3.mk
  rw [zc_combp]

theorem t3_two : t3 (2 : ℤ_[q3]) = 2 := map_ofNat t3 2

theorem red_mul {x y : Bp q3} (hx : x ∈ Op q3) (hy : y ∈ Op q3) : red (x * y) = red x * red y := by
  obtain ⟨n, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  rw [combp_mul, red_combp, red_combp, red_combp, R3_mul_def]
  congr 1
  funext k; fin_cases k <;> simp [combMulp, mul3, R3.mk, t3_two]

theorem red_one : red 1 = 1 := by
  rw [← combp_one, red_combp, R3_one_def]
  congr 1
  funext k; fin_cases k <;> simp [one3]

theorem smul_combp (w : Fin 4 → ℤ_[q3]) :
    (3 : ℚ_[q3]) • combp q3 w = combp q3 (fun k => 3 * w k) := by
  have h3 : ((3 : ℤ_[q3]) : ℚ_[q3]) = 3 := by
    rw [show (3 : ℤ_[q3]) = ((3 : ℕ) : ℤ_[q3]) by norm_num, PadicInt.coe_natCast]; norm_num
  ext <;> simp [combp, h3] <;> ring

theorem combp_mem_I3_iff (m : Fin 4 → ℤ_[q3]) :
    combp q3 m ∈ I3 ↔ ∀ k, t3 (m k) = 0 := by
  constructor
  · rintro ⟨w, hw⟩ k
    rw [smul_combp] at hw
    have := congrFun (combp_injective hw) k
    rw [this, map_mul, t3_three, zero_mul]
  · intro h
    have hw : ∀ k, ∃ w : ℤ_[q3], m k = 3 * w := by
      intro k
      have hm : m k ∈ IsLocalRing.maximalIdeal ℤ_[q3] := by
        rw [← PadicInt.ker_toZMod]; exact (t3_eq_zero_iff _).mp (h k)
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
      obtain ⟨w, hw⟩ := hm
      exact ⟨w, by rw [hw]; rfl⟩
    choose w hw using hw
    exact ⟨w, by rw [smul_combp]; congr 1; funext k; exact hw k⟩

/-- The reduction `K₀ → (𝒪/3𝒪)^×`. -/
noncomputable def redHom : K0 →* R3ˣ where
  toFun u :=
    { val := red (((u : BAˣ) : BA) P3)
      inv := red ((((u : BAˣ)⁻¹ : BAˣ) : BA) P3)
      val_inv := by
        rw [← red_mul (u.2.1 P3) (u.2.2 P3), ← RestrictedProduct.mul_apply, Units.mul_inv,
          RestrictedProduct.one_apply, red_one]
      inv_val := by
        rw [← red_mul (u.2.2 P3) (u.2.1 P3), ← RestrictedProduct.mul_apply, Units.inv_mul,
          RestrictedProduct.one_apply, red_one] }
  map_one' := by
    apply Units.ext
    show red (((1 : BAˣ) : BA) P3) = 1
    rw [Units.val_one, RestrictedProduct.one_apply, red_one]
  map_mul' u v := by
    apply Units.ext
    show red ((((u : BAˣ) * (v : BAˣ) : BAˣ) : BA) P3) = red (((u : BAˣ) : BA) P3) *
      red (((v : BAˣ) : BA) P3)
    rw [Units.val_mul, RestrictedProduct.mul_apply, red_mul (u.2.1 P3) (v.2.1 P3)]

theorem redHom_val (u : K0) : ((redHom u : R3ˣ) : R3) = red (((u : BAˣ) : BA) P3) := rfl

theorem redHom_eq_one_iff (u : K0) : redHom u = 1 ↔ (u : BAˣ) ∈ K3 := by
  obtain ⟨n, hn⟩ := u.2.1 P3
  have e1 : ((u : BAˣ) : BA) P3 - 1 = combp q3 (n - ![1, 0, 0, 0]) := by
    rw [← hn, ← combp_one, sub_eq_add_neg, combp_neg, combp_add, sub_eq_add_neg]
  constructor
  · intro h
    refine ⟨u.2, ?_⟩
    rw [e1, combp_mem_I3_iff]
    have h' := congrArg Units.val h
    rw [redHom_val, ← hn, red_combp, Units.val_one, R3_one_def] at h'
    have h'' : (fun k => t3 (n k)) = one3 := h'
    intro k
    have := congrFun h'' k
    fin_cases k <;> simp_all [one3]
  · rintro ⟨-, h3⟩
    rw [e1, combp_mem_I3_iff] at h3
    apply Units.ext
    rw [redHom_val, ← hn, red_combp, Units.val_one, R3_one_def]
    congr 1
    funext k
    have := h3 k
    fin_cases k <;> simp_all [one3, sub_eq_zero]

theorem star_mul_eq3 (x : Bp q3) : star x * x = algebraMap ℚ_[q3] (Bp q3) (nrd q3 x) := by
  ext <;> simp [nrd, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring

theorem redHom_surjective : Function.Surjective redHom := by
  intro a
  let n : Fin 4 → ℤ_[q3] := fun k => (((a : R3) k).val : ℤ_[q3])
  have hn : ∀ k, t3 (n k) = (a : R3) k := fun k => by
    simp only [n, map_natCast, ZMod.natCast_zmod_val]
  have hnrd3 : nrd3 (a : R3) ≠ 0 := (isUnit3_iff (a : R3)).mp ⟨a.inv, a.val_inv, a.inv_val⟩
  set N0 : ℤ_[q3] := (n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2) + (-2) * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)
    with hN0
  have hnrd : nrd q3 (combp q3 n) = (N0 : ℚ_[q3]) := by
    have h2 : ((2 : ℤ_[q3]) : ℚ_[q3]) = 2 := by
      rw [show (2 : ℤ_[q3]) = ((2 : ℕ) : ℤ_[q3]) by norm_num, PadicInt.coe_natCast]; norm_num
    rw [nrd_coord]
    simp only [coord_combp, hN0, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_neg, h2]
  have hN0z : t3 N0 = nrd3 (a : R3) := by
    simp only [hN0, map_add, map_mul, map_pow, map_neg, hn, nrd3]
    have : t3 (2 : ℤ_[q3]) = 2 := map_ofNat _ 2
    rw [this]; ring
  have hN1 : ‖N0‖ = 1 := norm_eq_one_of_toZMod_ne (fun h0 => hnrd3 (by
    rw [← hN0z]; exact (t3_eq_zero_iff N0).mpr h0))
  have hnrd1 : ‖nrd q3 (combp q3 n)‖ = 1 := by rw [hnrd, PadicInt.norm_coe, hN1]
  have hne : nrd q3 (combp q3 n) ≠ 0 := by
    intro h; rw [h, norm_zero] at hnrd1; exact zero_ne_one hnrd1
  let X : (Bp q3)ˣ :=
    { val := combp q3 n
      inv := (nrd q3 (combp q3 n))⁻¹ • star (combp q3 n)
      val_inv := by
        rw [mul_smul_comm, mul_star_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hne, map_one]
      inv_val := by
        rw [smul_mul_assoc, star_mul_eq3, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hne,
          map_one] }
  have hX : X ∈ OpUnits q3 := (mem_OpUnits_iff q3 (Or.inr rfl) X).mpr hnrd1
  have hk : unitSingle P3 X ∈ K0 := by
    constructor
    · intro q
      rw [← comp_val]
      by_cases h : q = P3
      · subst h; rw [comp_unitSingle_self]; exact hX.1
      · rw [comp_unitSingle_ne h]; exact (OpSub (q : ℕ)).one_mem
    · intro q
      rw [← comp_inv_val]
      by_cases h : q = P3
      · subst h; rw [comp_unitSingle_self]; exact hX.2
      · rw [comp_unitSingle_ne h, inv_one]; exact (OpSub (q : ℕ)).one_mem
  refine ⟨⟨unitSingle P3 X, hk⟩, Units.ext ?_⟩
  rw [redHom_val]
  show red (((unitSingle P3 X : BAˣ) : BA) P3) = (a : R3)
  rw [← comp_val, comp_unitSingle_self]
  show red (combp q3 n) = (a : R3)
  rw [red_combp]
  change (fun k => t3 (n k)) = _
  funext k
  exact hn k

/-- `-1 ∈ (𝒪/3𝒪)^×`. -/
def m1 : R3ˣ where
  val := fun k => -one3 k
  inv := fun k => -one3 k
  val_inv := by
    show mul3 _ _ = one3
    funext k; fin_cases k <;> simp [mul3, one3]
  inv_val := by
    show mul3 _ _ = one3
    funext k; fin_cases k <;> simp [mul3, one3]

theorem m1_sq : m1 ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_two, Units.val_one, R3_mul_def, R3_one_def]
  congr 1

theorem m1_ne_one : m1 ≠ 1 := by
  intro h
  have h1 : ((m1 : R3ˣ) : R3) = ((1 : R3ˣ) : R3) := congrArg Units.val h
  have h2 : (fun k => -one3 k : Fin 4 → ZMod 3) = one3 := h1
  have h3 := congrFun h2 0
  simp [one3] at h3
  exact absurd h3 (by decide)

theorem mem_zpowers_m1 {g : R3ˣ} : g ∈ Subgroup.zpowers m1 ↔ g = 1 ∨ g = m1 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · left; rw [zpow_mul, zpow_ofNat, m1_sq, one_zpow]
    · right; rw [zpow_add, zpow_mul, zpow_ofNat, m1_sq, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers m1

theorem card_zpowers_m1 : Nat.card (Subgroup.zpowers m1) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime m1_sq m1_ne_one

/-- The scalar `-1 ∈ 𝔸_f^× ∩ K₀`. -/
theorem neg_one_mem_Zhat : (-1 : BAˣ) ∈ Zhat := fun p => ⟨-1, by
  rw [Units.val_neg, Units.val_one, map_neg, map_one]; rfl⟩

theorem neg_one_mem_K0 : (-1 : BAˣ) ∈ K0 := by
  refine ⟨fun p => ?_, fun p => ?_⟩
  · rw [Units.val_neg, Units.val_one]
    exact (OpSub (p : ℕ)).neg_mem (OpSub (p : ℕ)).one_mem
  · rw [inv_neg, inv_one, Units.val_neg, Units.val_one]
    exact (OpSub (p : ℕ)).neg_mem (OpSub (p : ℕ)).one_mem

theorem redHom_neg_one : redHom ⟨-1, neg_one_mem_K0⟩ = m1 := by
  apply Units.ext
  rw [redHom_val]
  show red ((((-1 : BAˣ) : BAˣ) : BA) P3) = (m1 : R3)
  rw [Units.val_neg, Units.val_one]
  show red (-1 : Bp q3) = _
  rw [← combp_one, combp_neg, red_combp]
  change (fun k => t3 ((-![1, 0, 0, 0] : Fin 4 → ℤ_[q3]) k)) = (fun k => -one3 k)
  funext k; fin_cases k <;> simp [one3]

/-- Scalars in `K₀` reduce to `±1`. -/
theorem redHom_scalar {z : BAˣ} (hz : z ∈ Zhat) (hz0 : z ∈ K0) :
    redHom ⟨z, hz0⟩ = 1 ∨ redHom ⟨z, hz0⟩ = m1 := by
  obtain ⟨c, hc⟩ := hz P3
  obtain ⟨d, hd⟩ := (Zhat.inv_mem hz) P3
  have hcO := hz0.1 P3
  have hdO := hz0.2 P3
  rw [hc] at hcO
  rw [hd] at hdO
  have hcoord : ∀ e : ℚ_[q3], coord q3 (algebraMap ℚ_[q3] (Bp q3) e) = ![e, 0, 0, 0] := by
    intro e; funext k; fin_cases k <;> simp [coord]
  have hc1 : ‖c‖ ≤ 1 := by
    have := (mem_Op_iff_coord q3 _).mp hcO 0; rw [hcoord] at this; simpa using this
  have hd1 : ‖d‖ ≤ 1 := by
    have := (mem_Op_iff_coord q3 _).mp hdO 0; rw [hcoord] at this; simpa using this
  have hcd : c * d = 1 := by
    have h1 : ((z : BAˣ) : BA) P3 * ((z⁻¹ : BAˣ) : BA) P3 = 1 := by
      rw [← RestrictedProduct.mul_apply, Units.mul_inv]; rfl
    rw [hc, hd, ← map_mul] at h1
    exact (algebraMap ℚ_[q3] (Bp q3)).injective (by rw [h1, map_one])
  let c' : ℤ_[q3] := ⟨c, hc1⟩
  let d' : ℤ_[q3] := ⟨d, hd1⟩
  have hcd' : c' * d' = 1 := Subtype.ext hcd
  have hcomb : algebraMap ℚ_[q3] (Bp q3) c = combp q3 ![c', 0, 0, 0] := by
    ext <;> simp [combp, c']
  have hred : ((redHom ⟨z, hz0⟩ : R3ˣ) : R3) = R3.mk ![t3 c', 0, 0, 0] := by
    rw [redHom_val]
    show red (((z : BAˣ) : BA) P3) = _
    rw [hc, hcomb, red_combp]
    congr 1
    funext k; fin_cases k <;> simp
  have hne : t3 c' ≠ 0 := by
    intro h0
    have := congrArg t3 hcd'
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hcases : ∀ t : ZMod 3, t ≠ 0 → t = 1 ∨ t = -1 := by decide
  rcases hcases _ hne with h | h
  · left
    apply Units.ext
    rw [hred, h, Units.val_one, R3_one_def]
    congr 1
  · right
    apply Units.ext
    rw [hred, h]
    change (![(-1 : ZMod 3), 0, 0, 0] : Fin 4 → ZMod 3) = (fun k => -one3 k)
    funext k; fin_cases k <;> simp [one3]

instance Zhat_inf_K0_normal : (Zhat ⊓ K0).Normal :=
  Subgroup.normal_of_le_center (inf_le_left.trans Zhat_le_center)

theorem subgroupOf_eq_comap :
    ((Zhat ⊓ K0) ⊔ K3).subgroupOf K0 = (Subgroup.zpowers m1).comap redHom := by
  ext u
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_zpowers_m1]
  constructor
  · intro hu
    have hu' : (u : BAˣ) ∈ (((Zhat ⊓ K0) ⊔ K3 : Subgroup BAˣ) : Set BAˣ) := hu
    rw [Subgroup.normal_mul] at hu'
    obtain ⟨z, ⟨hzZ, hzK⟩, k, hk, hzk⟩ := hu'
    have e : u = ⟨z, hzK⟩ * ⟨k, hk.1⟩ := Subtype.ext hzk.symm
    rw [e, map_mul, (redHom_eq_one_iff ⟨k, hk.1⟩).mpr hk, mul_one]
    exact redHom_scalar hzZ hzK
  · rintro (h | h)
    · exact Subgroup.mem_sup_right ((redHom_eq_one_iff u).mp h)
    · have h1 : redHom (⟨-1, neg_one_mem_K0⟩ * u) = 1 := by
        rw [map_mul, redHom_neg_one, h, ← pow_two, m1_sq]
      have hk := (redHom_eq_one_iff _).mp h1
      have e : (u : BAˣ) = (-1 : BAˣ) * ((-1 : BAˣ) * (u : BAˣ)) := by
        rw [← mul_assoc, neg_one_mul, neg_neg, one_mul]
      rw [e]
      exact Subgroup.mul_mem_sup ⟨neg_one_mem_Zhat, neg_one_mem_K0⟩ hk

/-- **`[K₀ : ℤ̂^× K₃] = 36`** (`ℤ̂^× = 𝔸_f^× ∩ K₀`): `(𝒪/3𝒪)^×` has 72 elements and `ℤ̂^×`
reduces onto `{±1}`. -/
theorem relIndex_K3 : ((Zhat ⊓ K0) ⊔ K3).relIndex K0 = 36 := by
  rw [Subgroup.relIndex, subgroupOf_eq_comap, Subgroup.index_comap_of_surjective _ redHom_surjective]
  have h := Subgroup.index_mul_card (Subgroup.zpowers m1)
  rw [card_zpowers_m1, card_units_R3] at h
  omega

/-- **`|Γ'| = [N : 𝔸_f^× K₃] = 144 = 2⁴ 3²`** (h-b1 M3). -/
theorem gamma_order : (Zhat ⊔ K3).relIndex Nhat = 144 := by
  rw [gamma_count, relIndex_K3]

/-! ### `𝔸_f^× ∩ K₀ = ℤ̂^×` -/

/-- `ℤ̂^× = ∏_p ℤ_p^×`, as central scalars of `B̂^×`. -/
noncomputable def Zint : Subgroup BAˣ where
  carrier := {x | ∀ p : Nat.Primes, ∃ c : ℤ_[(p : ℕ)]ˣ,
    (x : BA) p = algebraMap ℚ_[(p : ℕ)] (Bp (p : ℕ)) ((c : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)])}
  one_mem' := fun p => ⟨1, by simp⟩
  mul_mem' := by
    intro a b ha hb p
    obtain ⟨c, hc⟩ := ha p
    obtain ⟨d, hd⟩ := hb p
    exact ⟨c * d, by rw [Units.val_mul, RestrictedProduct.mul_apply, hc, hd, ← map_mul]; simp⟩
  inv_mem' := by
    intro a ha p
    obtain ⟨c, hc⟩ := ha p
    refine ⟨c⁻¹, ?_⟩
    have h1 : (a : BA) p * ((a⁻¹ : BAˣ) : BA) p = 1 := by
      rw [← RestrictedProduct.mul_apply, Units.mul_inv]; rfl
    rw [hc] at h1
    have hcc : ((c : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)]) * (((c⁻¹ : ℤ_[(p : ℕ)]ˣ) : ℤ_[(p : ℕ)]) :
        ℚ_[(p : ℕ)]) = 1 := by
      rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
    calc ((a⁻¹ : BAˣ) : BA) p
        = algebraMap _ _ (((c⁻¹ : ℤ_[(p : ℕ)]ˣ) : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)]) *
          (algebraMap _ _ ((c : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)]) * ((a⁻¹ : BAˣ) : BA) p) := by
          rw [← mul_assoc, ← map_mul, mul_comm, hcc, map_one, one_mul]
      _ = _ := by rw [h1, mul_one]

theorem coord_algebraMap (p : ℕ) [Fact p.Prime] (e : ℚ_[p]) :
    coord p (algebraMap ℚ_[p] (Bp p) e) = ![e, 0, 0, 0] := by
  funext k; fin_cases k <;> simp [coord]

theorem algebraMap_mem_Op_iff (p : ℕ) [Fact p.Prime] (e : ℚ_[p]) :
    algebraMap ℚ_[p] (Bp p) e ∈ Op p ↔ ‖e‖ ≤ 1 := by
  rw [mem_Op_iff_coord, coord_algebraMap]
  constructor
  · intro h; simpa using h 0
  · intro h k; fin_cases k <;> simp [h]

/-- **`𝔸_f^× ∩ K₀ = ℤ̂^×`.** -/
theorem Zhat_inf_K0 : Zhat ⊓ K0 = Zint := by
  ext x
  constructor
  · rintro ⟨hz, hk⟩ p
    obtain ⟨c, hc⟩ := hz p
    obtain ⟨d, hd⟩ := (Zhat.inv_mem hz) p
    have hc1 : ‖c‖ ≤ 1 := (algebraMap_mem_Op_iff _ c).mp (hc ▸ hk.1 p)
    have hd1 : ‖d‖ ≤ 1 := (algebraMap_mem_Op_iff _ d).mp (hd ▸ hk.2 p)
    have hcd : c * d = 1 := by
      have h1 : (x : BA) p * ((x⁻¹ : BAˣ) : BA) p = 1 := by
        rw [← RestrictedProduct.mul_apply, Units.mul_inv]; rfl
      rw [hc, hd, ← map_mul] at h1
      exact (algebraMap ℚ_[(p : ℕ)] (Bp (p : ℕ))).injective (by rw [h1, map_one])
    let cu : ℤ_[(p : ℕ)]ˣ := ⟨⟨c, hc1⟩, ⟨d, hd1⟩, Subtype.ext hcd,
      Subtype.ext (by rw [mul_comm] at hcd; exact hcd)⟩
    exact ⟨cu, hc⟩
  · intro hx
    refine ⟨fun p => ?_, fun p => ?_, fun p => ?_⟩
    · obtain ⟨c, hc⟩ := hx p
      exact ⟨_, hc⟩
    · obtain ⟨c, hc⟩ := hx p
      rw [hc, algebraMap_mem_Op_iff]
      exact PadicInt.norm_le_one _
    · obtain ⟨c, hc⟩ := Zint.inv_mem hx p
      rw [hc, algebraMap_mem_Op_iff]
      exact PadicInt.norm_le_one _

/-- **A3's count with `ℤ̂^×` named:** `|Γ'| = [N : 𝔸_f^× K₃] = [N : 𝔸_f^× K₀] · [K₀ : ℤ̂^× K₃]
= 4 · 36 = 144`. -/
theorem gamma_count_Zint :
    (Zhat ⊔ K3).relIndex Nhat = (Zhat ⊔ K0).relIndex Nhat * (Zint ⊔ K3).relIndex K0 ∧
      (Zhat ⊔ K0).relIndex Nhat = 4 ∧ (Zint ⊔ K3).relIndex K0 = 36 := by
  rw [← Zhat_inf_K0, relIndex_eq_four, relIndex_K3]
  exact ⟨gamma_order, rfl, rfl⟩

end G1Adelic

#print axioms G1Adelic.relIndex_eq_four
#print axioms G1Adelic.mem_sup_iff_forall
#print axioms G1Adelic.normalizer_component
#print axioms G1Adelic.gamma_count
#print axioms G1Adelic.gamma_order
#print axioms G1Adelic.gamma_count_Zint
