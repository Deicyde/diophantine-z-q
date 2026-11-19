import ZInQKernel.Contrib.OneProof.RC.Adelic.Ideal

/-!
# Right multiplication on adelic classes
Proved here: the normalizer quotient argument for tex 8487–8490, 9331–9358.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler

variable {a b : ℚ} {R : Order a b}

/-- The adele with the given entry at one prime and the identity at every other prime. -/
def single (R : Order a b) (p : Prime) (u : (Bp p.val a b)ˣ) : FiniteUnits R := by
  classical
  refine ⟨Function.update (fun _ => 1) p u, (Set.finite_singleton p).subset ?_⟩
  intro q hq
  by_contra h
  exact hq (by simp [Function.update_of_ne (show q ≠ p from h)])

@[simp] theorem single_same (p : Prime) (u : (Bp p.val a b)ˣ) :
    (single R p u).val p = u := by
  classical
  change Function.update (β := fun q : Prime => (Bp q.val a b)ˣ) (fun _ => 1) p u p = u
  exact Function.update_self (β := fun q : Prime => (Bp q.val a b)ˣ) p u _

theorem single_away {p q : Prime} (hq : q ≠ p) (u : (Bp p.val a b)ˣ) :
    (single R p u).val q = 1 := by
  classical
  change Function.update (β := fun q : Prime => (Bp q.val a b)ˣ) (fun _ => 1) p u q = 1
  exact Function.update_of_ne (β := fun q : Prime => (Bp q.val a b)ˣ) hq u _

/-- A local conjugation normalizing the completed order also normalizes its unit group. -/
theorem localUnits_conj (p : Prime) (u : (Bp p.val a b)ˣ)
    (hu : ∀ x : Bp p.val a b, (↑u⁻¹ : Bp p.val a b) * x * (u : Bp p.val a b) ∈
      R.completion p.val ↔ x ∈ R.completion p.val) (v : (Bp p.val a b)ˣ) :
    u⁻¹ * v * u ∈ localUnits R p ↔ v ∈ localUnits R p := by
  change ((_ : Bp p.val a b) ∈ R.completion p.val ∧
    (_ : Bp p.val a b) ∈ R.completion p.val) ↔ _
  simp only [mul_inv_rev, inv_inv, Units.val_mul, ← mul_assoc, hu]
  rfl

/-- The property needed for the right action on double cosets, in both directions. -/
def Normalizes (k : FiniteUnits R) : Prop :=
  ∀ r : FiniteUnits R, k⁻¹ * r * k ∈ integralUnits R ↔ r ∈ integralUnits R

theorem normalizes_single (p : Prime) (u : (Bp p.val a b)ˣ)
    (hu : ∀ x : Bp p.val a b, (↑u⁻¹ : Bp p.val a b) * x * (u : Bp p.val a b) ∈
      R.completion p.val ↔ x ∈ R.completion p.val) :
    Normalizes (single R p u) := by
  intro r
  change (∀ q : Prime, ((single R p u).val q)⁻¹ * r.val q * (single R p u).val q ∈
    localUnits R q) ↔ ∀ q : Prime, r.val q ∈ localUnits R q
  apply forall_congr'
  intro q
  by_cases hq : q = p
  · subst q
    rw [single_same, localUnits_conj p u hu]
  · simp [single_away hq]

theorem normalizes_inv {k : FiniteUnits R} (h : Normalizes k) :
    Normalizes k⁻¹ := by
  intro r
  have he := (h (k * r * k⁻¹)).symm
  rw [show k⁻¹ * (k * r * k⁻¹) * k = r by group] at he
  simpa only [inv_inv] using he

private theorem right_respects (k : FiniteUnits R) (h : Normalizes k)
    {z w : FiniteUnits R} (he : (doubleCosetRel R).r z w) :
    (doubleCosetRel R).r (z * k) (w * k) := by
  obtain ⟨u, r, rfl⟩ := he
  refine ⟨u, ⟨k⁻¹ * r.val * k, (h r.val).mpr r.prop⟩, ?_⟩
  change _ = diagonal R u * (z * k) * (k⁻¹ * r.val * k)
  simp [mul_assoc]

/-- Right multiplication by a normalizer, on the adelic class set. -/
def rightPerm (k : FiniteUnits R) (h : Normalizes k) : Equiv.Perm (DoubleCosets R) where
  toFun := Quotient.map (· * k) (fun _ _ => right_respects k h)
  invFun := Quotient.map (· * k⁻¹) (fun _ _ => right_respects k⁻¹ (normalizes_inv h))
  left_inv := by intro z; induction z using Quotient.inductionOn with | _ z =>
                   exact congrArg (Quotient.mk _) (mul_inv_cancel_right z k)
  right_inv := by intro z; induction z using Quotient.inductionOn with | _ z =>
                    exact congrArg (Quotient.mk _) (inv_inv k ▸ mul_inv_cancel_right z k⁻¹)

theorem rightPerm_mk (k : FiniteUnits R) (h : Normalizes k) (z : FiniteUnits R) :
    rightPerm k h (Quotient.mk _ z) = Quotient.mk _ (z * k) := rfl

/-- The same permutation transported to the ideal class set. -/
def rightClassPerm (k : FiniteUnits R) (h : Normalizes k) : Equiv.Perm (ClassSet R) :=
  (classesEquiv R).trans ((rightPerm k h).trans (idealsEquiv R))

theorem rightClassPerm_mk (k : FiniteUnits R) (h : Normalizes k) (z : FiniteUnits R) :
    rightClassPerm k h (Quotient.mk _ (fromAdelic z)) = Quotient.mk _ (fromAdelic (z * k)) := by
  change idealsEquiv R (rightPerm k h ((idealsEquiv R).symm
    (idealsEquiv R (Quotient.mk _ z)))) = _
  rw [Equiv.symm_apply_apply, rightPerm_mk, idealsEquiv_mk]

/-- The local square may be removed by a central rational unit and an integral adele. -/
theorem rightClassPerm_involutive (k : FiniteUnits R) (h : Normalizes k)
    (u : (B a b)ˣ) (hu : ∀ z : FiniteUnits R, Commute z (diagonal R u))
    (r : integralUnits R) (hr : k * k = diagonal R u * r.val) :
    Function.Involutive (rightClassPerm k h) := by
  intro i
  obtain ⟨z, rfl⟩ := (idealsEquiv R).surjective i
  induction z using Quotient.inductionOn with
  | _ z =>
    rw [idealsEquiv_mk, rightClassPerm_mk, rightClassPerm_mk]
    apply (classesEquiv R).injective
    change (idealsEquiv R).symm (idealsEquiv R (Quotient.mk _ ((z * k) * k))) =
      (idealsEquiv R).symm (idealsEquiv R (Quotient.mk _ z))
    simp only [Equiv.symm_apply_apply]
    symm
    apply Quotient.sound
    exact ⟨u, r, by rw [mul_assoc, hr, ← mul_assoc, (hu z).eq]⟩


end ZInQ.Manuscript.RC.Adelic
