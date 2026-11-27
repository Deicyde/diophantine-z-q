import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.OrderMod
set_option autoImplicit false
noncomputable section
open LeafQM
namespace Y3OrderMod

/-!
# `O / 3 O` has 81 elements

The map `(Fin 4 → ZMod 3) → O / 3 O` sending `c` to the class of `ofInt (fun i => (c i).val)`
is a bijection. `O` is the image of the injective map `ofInt` on `ℤ⁴`, and `ofInt` is additive
and commutes with multiplication by 3.
-/

/-- The class of the standard lift of `c`. -/
def liftMod3 (c : Fin 4 → ZMod 3) : OMod 3 :=
  ((⟨ofInt (fun i => ((c i).val : ℤ)), ofInt_mem _⟩ : O) : OMod 3)

theorem liftMod3_injective : Function.Injective liftMod3 := by
  intro c c' h
  unfold liftMod3 at h
  obtain ⟨d, hd⟩ := coe_eq_coe_iff.1 h
  obtain ⟨k, hk⟩ := exists_ofInt d
  have h33 : (((3 : ℕ) : O) : B) = (3 : B) := by
    first
      | exact (SubringClass.coe_natCast O 3).trans (by norm_num)
      | norm_num
      | simp
  have h3 : ofInt (fun i => ((c i).val : ℤ)) - ofInt (fun i => ((c' i).val : ℤ)) =
      (3 : B) * ofInt k := by
    have := congrArg Subtype.val hd
    calc ofInt (fun i => ((c i).val : ℤ)) - ofInt (fun i => ((c' i).val : ℤ))
        = (((⟨ofInt (fun i => ((c i).val : ℤ)), ofInt_mem _⟩ : O) -
            ⟨ofInt (fun i => ((c' i).val : ℤ)), ofInt_mem _⟩ : O) : B) := by
          first
            | rfl
            | simp
      _ = ((((3 : ℕ) : O) * d : O) : B) := this
      _ = (((3 : ℕ) : O) : B) * (d : B) := by
          first
            | rfl
            | simp
      _ = (3 : B) * ofInt k := by rw [h33, hk]
  rw [LeafQM.AV.ofInt_sub, LeafQM.AV.three_mul_ofInt] at h3
  have h4 := LeafQM.AV.ofInt_injective h3
  funext i
  have h5 := congrFun h4 i
  simp only [Pi.sub_apply] at h5
  have h6 : (((c i).val : ℤ) : ZMod 3) - (((c' i).val : ℤ) : ZMod 3) = 0 := by
    rw [← Int.cast_sub, h5]
    push_cast
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
  simpa [sub_eq_zero] using h6

theorem liftMod3_surjective : Function.Surjective liftMod3 := by
  intro q
  obtain ⟨x, rfl⟩ := coe_surjective 3 q
  obtain ⟨n, hn⟩ := exists_ofInt x
  refine ⟨fun i => ((n i : ℤ) : ZMod 3), ?_⟩
  have hr : ∀ i, ((((n i : ℤ) : ZMod 3).val : ℕ) : ℤ) = n i % ((3 : ℕ) : ℤ) := by
    intro i
    first
      | exact ZMod.val_intCast (n i)
      | simp [ZMod.val_intCast]
  unfold liftMod3
  apply Eq.symm
  apply coe_eq_coe_iff.2
  refine rel_of_B x _ (ofInt (fun i => n i / ((3 : ℕ) : ℤ))) _ (ofInt_mem _) ?_
  have hsplit : ofInt n
      = ofInt (fun i => ((((n i : ℤ) : ZMod 3).val : ℕ) : ℤ)) +
        ((3 : ℕ) : B) * ofInt (fun i => n i / ((3 : ℕ) : ℤ)) := by
    rw [← Y3OrderMod.ofInt_smul, ← Y3OrderMod.ofInt_add]
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, hr]
    first
      | exact (Int.emod_add_mul_ediv (n i) ((3 : ℕ) : ℤ)).symm
      | exact (Int.emod_add_ediv (n i) ((3 : ℕ) : ℤ)).symm
      | exact (Int.emod_add_ediv' (n i) ((3 : ℕ) : ℤ)).symm
      | omega
  rw [hn, hsplit]
  abel

theorem card_fun_zmod3 : Nat.card (Fin 4 → ZMod 3) = 81 := by
  first
    | (rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]; norm_num)
    | simp
    | (rw [Nat.card_eq_fintype_card]; decide)

/-- `O / 3 O` has 81 elements. -/
theorem card_OMod3 : Nat.card (OMod 3) = 81 :=
  (Nat.card_congr (Equiv.ofBijective liftMod3 ⟨liftMod3_injective, liftMod3_surjective⟩)).symm.trans
    card_fun_zmod3

end Y3OrderMod
