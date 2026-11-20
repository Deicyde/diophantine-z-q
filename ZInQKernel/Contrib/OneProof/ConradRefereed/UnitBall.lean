import ZInQKernel.Contrib.OneProof.ConradRefereed.NormForm

/-! Norm estimates on a small open subgroup of units of a finite Galois
extension. Provenance (c): on-the-spot bounds for passing a near-one identity through the norm. -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.SerreAppB

open HDec.G0Galois.C8Conrad.Bridges
open Module

variable (p : ℕ) [Fact p.Prime]

/-- A point of `ℚ̄_p` within distance `< 1` of `1` has norm `1`. Kind: proved. -/
theorem norm_eq_one_of_norm_sub_one_lt {x : PadicAlgCl p} (hx : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (show ‖x - 1‖ ≠ ‖(1 : PadicAlgCl p)‖ by rw [norm_one]; exact hx.ne)
  rw [sub_add_cancel, norm_one, max_eq_right hx.le] at h
  exact h

/-- The ultrametric bound for a product of two points near `1`. Kind: proved. -/
theorem norm_mul_sub_one_le {a b : PadicAlgCl p} {r : ℝ} (hr : r ≤ 1)
    (ha : ‖a - 1‖ ≤ r) (hb : ‖b - 1‖ ≤ r) : ‖a * b - 1‖ ≤ r := by
  have hna : ‖a‖ ≤ 1 := by
    calc ‖a‖ = ‖(a - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖a - 1‖ ‖(1 : PadicAlgCl p)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [norm_one]; exact max_le (ha.trans hr) le_rfl
  have hab : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  calc ‖a * b - 1‖ = ‖a * (b - 1) + (a - 1)‖ := by rw [hab]
    _ ≤ max ‖a * (b - 1)‖ ‖a - 1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ r := by
      refine max_le ?_ ha
      rw [norm_mul]
      calc ‖a‖ * ‖b - 1‖ ≤ 1 * r := mul_le_mul hna hb (norm_nonneg _) zero_le_one
        _ = r := one_mul r

/-- The ultrametric bound for a finite product of points near `1`. Kind: proved. -/
theorem norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → PadicAlgCl p) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 1) (hf : ∀ i ∈ s, ‖f i - 1‖ ≤ r) :
    ‖(∏ i ∈ s, f i) - 1‖ ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr0
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact norm_mul_sub_one_le p hr (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A `ℚ_p`-automorphism of `K ⊆ ℚ̄_p` preserves the norm of `ℚ̄_p`: it extends to an element
of `G_{ℚ_p}` (`AlgEquiv.liftNormal`), which is an isometry. Kind: proved. -/
theorem norm_algEquiv_apply (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (σ : K ≃ₐ[ℚ_[p]] K) (k : K) :
    ‖((σ k : K) : PadicAlgCl p)‖ = ‖(k : PadicAlgCl p)‖ := by
  have h := AlgEquiv.liftNormal_commutes σ (PadicAlgCl p) k
  have h2 := PkgI4.norm_gqp_apply p (σ.liftNormal (PadicAlgCl p)) (algebraMap K (PadicAlgCl p) k)
  rw [h] at h2
  exact h2

/-- The open subgroup `{u ∈ Kˣ : ‖u - 1‖ < r}` of `Kˣ`, for `0 < r ≤ 1`. Kind: definition. -/
def unitBall (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℝ) (hr0 : 0 < r) (hr : r ≤ 1) :
    Subgroup Kˣ where
  carrier := {u | ‖(((u : Kˣ) : K) : PadicAlgCl p) - 1‖ < r}
  one_mem' := by simpa using hr0
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, IntermediateField.coe_mul] at ha hb ⊢
    have hm := norm_mul_sub_one_le p (r := max ‖(((a : Kˣ) : K) : PadicAlgCl p) - 1‖
      ‖(((b : Kˣ) : K) : PadicAlgCl p) - 1‖) ((max_lt ha hb).le.trans hr) (le_max_left _ _)
      (le_max_right _ _)
    exact hm.trans_lt (max_lt ha hb)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h1 : ‖(((a : Kˣ) : K) : PadicAlgCl p)‖ = 1 :=
      norm_eq_one_of_norm_sub_one_lt p (ha.trans_le hr)
    have hne : (((a : Kˣ) : K) : PadicAlgCl p) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : ((((a⁻¹ : Kˣ) : Kˣ) : K) : PadicAlgCl p) = ((((a : Kˣ) : K) : PadicAlgCl p))⁻¹ := by
      rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
    rw [hinv]
    have heq : ((((a : Kˣ) : K) : PadicAlgCl p))⁻¹ - 1 =
        -((((a : Kˣ) : K) : PadicAlgCl p) - 1) * ((((a : Kˣ) : K) : PadicAlgCl p))⁻¹ := by
      field_simp
      ring
    rw [heq, norm_mul, norm_neg, norm_inv, h1, inv_one, mul_one]
    exact ha

theorem mem_unitBall (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {r : ℝ} (hr0 : 0 < r)
    (hr : r ≤ 1) (u : Kˣ) :
    u ∈ unitBall p K r hr0 hr ↔ ‖(((u : Kˣ) : K) : PadicAlgCl p) - 1‖ < r := Iff.rfl

theorem isOpen_unitBall (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {r : ℝ} (hr0 : 0 < r)
    (hr : r ≤ 1) : IsOpen ((unitBall p K r hr0 hr : Subgroup Kˣ) : Set Kˣ) := by
  have hf : Continuous (fun u : Kˣ => (((u : Kˣ) : K) : PadicAlgCl p)) :=
    continuous_subtype_val.comp Units.continuous_val
  exact isOpen_lt (continuous_norm.comp (hf.sub continuous_const)) continuous_const

/-- `‖N_{K/ℚ_p}(u) - 1‖ ≤ ‖u - 1‖` for `‖u - 1‖ ≤ 1`, `K/ℚ_p` finite Galois. Kind: proved. -/
theorem norm_normUnits_sub_one_le (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K] (u : Kˣ)
    (hu : ‖(((u : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ 1) :
    ‖((TauCeti.Algebra.normUnits ℚ_[p] u : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ ≤
      ‖(((u : Kˣ) : K) : PadicAlgCl p) - 1‖ := by
  rw [TauCeti.Algebra.coe_normUnits]
  have hN := Algebra.norm_eq_prod_automorphisms ℚ_[p] ((u : Kˣ) : K)
  rw [← norm_algebraMap' (PadicAlgCl p) (Algebra.norm ℚ_[p] ((u : Kˣ) : K) - 1), map_sub, map_one,
    IsScalarTower.algebraMap_apply ℚ_[p] K (PadicAlgCl p), hN, map_prod]
  refine norm_prod_sub_one_le p _ _ (norm_nonneg _) hu ?_
  intro σ _
  have h := norm_algEquiv_apply p K σ (((u : Kˣ) : K) - 1)
  rw [map_sub, map_one] at h
  have e1 : (((σ ((u : Kˣ) : K) - 1 : K)) : PadicAlgCl p) =
      algebraMap K (PadicAlgCl p) (σ ((u : Kˣ) : K)) - 1 := rfl
  have e2 : (((((u : Kˣ) : K) - 1 : K)) : PadicAlgCl p) = (((u : Kˣ) : K) : PadicAlgCl p) - 1 := rfl
  rw [e1, e2] at h
  exact h.le

#print axioms norm_eq_one_of_norm_sub_one_lt
#print axioms norm_mul_sub_one_le
#print axioms norm_prod_sub_one_le
#print axioms norm_algEquiv_apply
#print axioms mem_unitBall
#print axioms isOpen_unitBall
#print axioms norm_normUnits_sub_one_le

end HDec.G0Galois.C8Conrad.SerreAppB
