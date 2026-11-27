import ZInQKernel.HDecomp.QM.Structures
import Mathlib

/-!
# The order `O` reduced modulo a positive integer

For `M : ℕ` this file defines

* `modRel M : RingCon O`, the two-sided congruence `x ~ y ↔ ∃ c : O, x - y = M * c`;
* `OMod M := (modRel M).Quotient`, a ring;
* `finite_OMod : 0 < M → Finite (OMod M)`;
* `G M := (OMod M)ˣ`, a finite group when `M ≠ 0`;
* a chosen lift `σ : G M → O` with the congruences
  `σ g * σ h ≡ σ (g * h)`, `σ 1 ≡ 1`, `σ g⁻¹ * σ g ≡ 1`, `σ g * σ g⁻¹ ≡ 1` modulo `M`.

Integers are central in `O`; this is what makes the left ideal `M * O` two-sided.
-/

namespace Y3OrderMod

open LeafQM

/-! ## Membership helpers -/

/-- Every `ofInt n` lies in `O`. -/
theorem ofInt_mem (n : Fin 4 → ℤ) : ofInt n ∈ O := by
  first
    | exact ⟨n, rfl⟩
    | exact (show InO (ofInt n) from ⟨n, rfl⟩)

/-- Every element of `O` is some `ofInt n`. -/
theorem exists_ofInt (x : O) : ∃ n : Fin 4 → ℤ, (x : B) = ofInt n := by
  first
    | exact x.2
    | exact (show InO (x : B) from x.2)

/-- Natural number casts are central in `O`. -/
theorem natCast_mul_comm (M : ℕ) (x : O) : (M : O) * x = x * (M : O) :=
  Nat.cast_comm M x

/-- Moving the central factor `M` to the front. -/
theorem mul_natCast_mul (M : ℕ) (x d : O) : x * ((M : O) * d) = (M : O) * (x * d) := by
  rw [← mul_assoc, ← natCast_mul_comm M x, mul_assoc]

/-! ## The congruence modulo `M` -/

/-- The two-sided congruence `x ~ y ↔ ∃ c : O, x - y = M * c`. -/
def modRel (M : ℕ) : RingCon O where
  r x y := ∃ c : O, x - y = (M : O) * c
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := fun {x y} h => by
        obtain ⟨c, hc⟩ := h
        exact ⟨-c, show y - x = (M : O) * -c by rw [mul_neg, ← hc, neg_sub]⟩
      trans := fun {x y z} h₁ h₂ => by
        obtain ⟨c, hc⟩ := h₁
        obtain ⟨d, hd⟩ := h₂
        exact ⟨c + d, show x - z = (M : O) * (c + d) by rw [mul_add, ← hc, ← hd]; abel⟩ }
  mul' := by
    intro w x y z h₁ h₂
    obtain ⟨c, hc⟩ := h₁
    obtain ⟨d, hd⟩ := h₂
    refine ⟨c * y + x * d, ?_⟩
    show w * y - x * z = (M : O) * (c * y + x * d)
    calc w * y - x * z = (w - x) * y + x * (y - z) := by
          first
            | (rw [sub_mul, mul_sub]; abel)
            | noncomm_ring
      _ = (M : O) * c * y + x * ((M : O) * d) := by rw [hc, hd]
      _ = (M : O) * (c * y + x * d) := by
          rw [mul_add, mul_assoc, mul_natCast_mul M x d]
  add' := by
    intro w x y z h₁ h₂
    obtain ⟨c, hc⟩ := h₁
    obtain ⟨d, hd⟩ := h₂
    refine ⟨c + d, ?_⟩
    show w + y - (x + z) = (M : O) * (c + d)
    rw [mul_add, ← hc, ← hd]
    abel

theorem modRel_iff {M : ℕ} {x y : O} :
    modRel M x y ↔ ∃ c : O, x - y = (M : O) * c :=
  Iff.rfl

/-- The quotient ring `O / M O`. -/
abbrev OMod (M : ℕ) := (modRel M).Quotient

theorem coe_eq_coe_iff {M : ℕ} {x y : O} :
    (x : OMod M) = (y : OMod M) ↔ ∃ c : O, x - y = (M : O) * c :=
  RingCon.eq (modRel M)

theorem coe_surjective (M : ℕ) : Function.Surjective (fun x : O => (x : OMod M)) := by
  intro q
  first
    | exact Quotient.exists_rep q
    | exact Quot.exists_rep q

/-- A relation in `O` from an identity in `B`. -/
theorem rel_of_B {M : ℕ} (x : O) (y z : B) (hy : y ∈ O) (hz : z ∈ O)
    (h : (x : B) - y = (M : B) * z) :
    ∃ c : O, x - ⟨y, hy⟩ = (M : O) * c := by
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  have hM : ((M : O) : B) = (M : B) := by
    first
      | exact SubringClass.coe_natCast O M
      | norm_cast
      | simp
  calc ((x - ⟨y, hy⟩ : O) : B) = (x : B) - y := by first | rfl | simp
    _ = (M : B) * z := h
    _ = ((M : O) : B) * z := by rw [hM]
    _ = (((M : O) * ⟨z, hz⟩ : O) : B) := by first | rfl | simp

/-! ## Arithmetic of `ofInt` -/

theorem ofInt_add (n m : Fin 4 → ℤ) : ofInt (n + m) = ofInt n + ofInt m := by
  apply QuaternionAlgebra.ext <;>
    first
      | (simp only [ofInt, Pi.add_apply, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add,
          QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add] <;>
        push_cast <;> ring1)
      | (simp [ofInt] <;> ring1)

theorem ofInt_smul (M : ℕ) (n : Fin 4 → ℤ) : ofInt (M • n) = (M : B) * ofInt n := by
  apply QuaternionAlgebra.ext <;>
    first
      | (simp only [ofInt, Pi.smul_apply, nsmul_eq_mul, QuaternionAlgebra.re_mul,
          QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
          QuaternionAlgebra.re_natCast, QuaternionAlgebra.imI_natCast,
          QuaternionAlgebra.imJ_natCast, QuaternionAlgebra.imK_natCast] <;>
        push_cast <;> ring1)
      | (simp [ofInt] <;> ring1)

/-! ## Finiteness of `OMod M` -/

theorem finite_OMod (M : ℕ) (hM : 0 < M) : Finite (OMod M) := by
  have hMz : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  refine Finite.of_surjective
    (fun r : Fin 4 → Fin M =>
      ((⟨ofInt (fun i => ((r i : ℕ) : ℤ)), Y3OrderMod.ofInt_mem _⟩ : O) : OMod M)) ?_
  intro q
  obtain ⟨x, rfl⟩ := coe_surjective M q
  obtain ⟨n, hn⟩ := Y3OrderMod.exists_ofInt x
  -- reduce each coefficient of `n` modulo `M`
  obtain ⟨r, hr⟩ : ∃ r : Fin 4 → Fin M, ∀ i, ((r i : ℕ) : ℤ) = n i % (M : ℤ) :=
    ⟨fun i => ⟨(n i % (M : ℤ)).toNat, by
        have h₀ := Int.toNat_of_nonneg (Int.emod_nonneg (n i) hMz.ne')
        have h₁ := Int.emod_lt_of_pos (n i) hMz
        generalize n i % (M : ℤ) = t at h₀ h₁ ⊢
        first
          | omega
          | (rw [← h₀] at h₁; exact_mod_cast h₁)⟩,
      fun i => Int.toNat_of_nonneg (Int.emod_nonneg (n i) hMz.ne')⟩
  refine ⟨r, ?_⟩
  beta_reduce
  apply Eq.symm
  apply coe_eq_coe_iff.2
  refine rel_of_B x _ (ofInt (fun i => n i / (M : ℤ))) _ (Y3OrderMod.ofInt_mem _) ?_
  -- `n = (n mod M) + M * (n / M)` componentwise
  have hsplit : ofInt n
      = ofInt (fun i => ((r i : ℕ) : ℤ)) + (M : B) * ofInt (fun i => n i / (M : ℤ)) := by
    rw [← Y3OrderMod.ofInt_smul, ← Y3OrderMod.ofInt_add]
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, hr]
    first
      | exact (Int.emod_add_mul_ediv (n i) (M : ℤ)).symm
      | exact (Int.emod_add_ediv (n i) (M : ℤ)).symm
      | exact (Int.emod_add_ediv' (n i) (M : ℤ)).symm
  rw [hn, hsplit]
  abel

instance instFiniteOMod (M : ℕ) [NeZero M] : Finite (OMod M) :=
  finite_OMod M (Nat.pos_of_ne_zero (NeZero.ne M))

/-! ## The finite unit group -/

/-- The unit group of `O / M O`. -/
abbrev G (M : ℕ) := (OMod M)ˣ

instance instFiniteG (M : ℕ) [NeZero M] : Finite (G M) := inferInstance

theorem finite_G (M : ℕ) (hM : 0 < M) : Finite (G M) := by
  haveI := finite_OMod M hM
  exact inferInstance

/-! ## A lift of units to `O` -/

/-- A chosen representative in `O` of a unit modulo `M`. -/
noncomputable def σ {M : ℕ} (g : G M) : O :=
  Classical.choose (coe_surjective M (g : OMod M))

theorem σ_spec {M : ℕ} (g : G M) : ((σ g : O) : OMod M) = (g : OMod M) :=
  Classical.choose_spec (coe_surjective M (g : OMod M))

theorem σ_mul {M : ℕ} (g h : G M) :
    ∃ c : O, σ g * σ h - σ (g * h) = (M : O) * c := by
  apply coe_eq_coe_iff.1
  simp only [RingCon.coe_mul, σ_spec, Units.val_mul]

theorem σ_one {M : ℕ} : ∃ c : O, σ (1 : G M) - 1 = (M : O) * c := by
  apply coe_eq_coe_iff.1
  simp only [σ_spec, Units.val_one, RingCon.coe_one]

theorem σ_inv_mul {M : ℕ} (g : G M) :
    ∃ d : O, σ g⁻¹ * σ g - 1 = (M : O) * d := by
  apply coe_eq_coe_iff.1
  simp only [RingCon.coe_mul, RingCon.coe_one, σ_spec, Units.inv_mul]

theorem σ_mul_inv {M : ℕ} (g : G M) :
    ∃ d : O, σ g * σ g⁻¹ - 1 = (M : O) * d := by
  apply coe_eq_coe_iff.1
  simp only [RingCon.coe_mul, RingCon.coe_one, σ_spec, Units.mul_inv]

end Y3OrderMod
