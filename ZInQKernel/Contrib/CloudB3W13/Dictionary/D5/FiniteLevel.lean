import ZInQKernel.HDecomp.QM.Structures

/-!
# D5: the actual 81 level representatives

Original dictionary proof, 2026-11-16, W13 D5 with Metamate/agentcloud assistance.
The representative calculation reuses `LeafQM.AV.liftO`, `ofInt_injective`, and
`three_mul_ofInt` from the existing kernel. No torsion theorem is assumed here.
The final counting lemma takes the cardinality of the genuine torsion group;
its geometric provider is supplied separately, without changing any level point.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D5

open CategoryTheory AlgebraicGeometry
open LeafQM

variable {G : Type} [AddCommGroup G]

/-- Kernel exactly `3𝒪` makes the 81 standard representatives distinct. -/
theorem representatives_injective (eta : O →+ G)
    (hker : ∀ a : O, eta a = 0 ↔ ∃ b : O, a = 3 * b) :
    Function.Injective (fun c : Fin 4 → ZMod 3 => eta (AV.liftO c)) := by
  intro c c' h
  change eta (AV.liftO c) = eta (AV.liftO c') at h
  have hzero : eta (AV.liftO c - AV.liftO c') = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨d, hd⟩ := (hker _).mp hzero
  obtain ⟨k, hk⟩ := d.2
  have h3 : ofInt (fun i => ((c i).val : ℤ)) -
      ofInt (fun i => ((c' i).val : ℤ)) = 3 * ofInt k := by
    have hv := congrArg Subtype.val hd
    have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
    simpa only [AV.liftO, hk, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33] using hv
  rw [AV.ofInt_sub, AV.three_mul_ofInt] at h3
  have h4 := AV.ofInt_injective h3
  funext i
  have h5 := congrFun h4 i
  simp only [Pi.sub_apply] at h5
  have h6 : (((c i).val : ℤ) : ZMod 3) - (((c' i).val : ℤ) : ZMod 3) = 0 := by
    rw [← Int.cast_sub, h5]
    push_cast
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
  simpa [sub_eq_zero] using h6

/-- Every point of a kernel level structure is genuinely killed by three. -/
theorem eta_three (eta : O →+ G)
    (hker : ∀ a : O, eta a = 0 ↔ ∃ b : O, a = 3 * b) (a : O) :
    (3 : ℕ) • eta a = 0 := by
  rw [← map_nsmul, hker]
  exact ⟨a, by simp [nsmul_eq_mul]⟩

/-- The original level map, restricted to its original standard representatives. -/
def representativeTorsion (eta : O →+ G)
    (hker : ∀ a : O, eta a = 0 ↔ ∃ b : O, a = 3 * b) :
    (Fin 4 → ZMod 3) → {x : G // (3 : ℕ) • x = 0} :=
  fun c => ⟨eta (AV.liftO c), eta_three eta hker _⟩

theorem representativeTorsion_injective (eta : O →+ G)
    (hker : ∀ a : O, eta a = 0 ↔ ∃ b : O, a = 3 * b) :
    Function.Injective (representativeTorsion eta hker) := by
  intro c c' h
  exact representatives_injective eta hker (congrArg Subtype.val h)

/-- Cardinality 81 of the actual torsion group proves geometric generation.
No alternate choice of generator or replacement of the supplied level data occurs. -/
theorem eta_surjective_of_torsion_card (eta : O →+ G)
    (hker : ∀ a : O, eta a = 0 ↔ ∃ b : O, a = 3 * b)
    (hcard : Nat.card {x : G // (3 : ℕ) • x = 0} = 81)
    (x : G) (hx : (3 : ℕ) • x = 0) : ∃ a : O, eta a = x := by
  haveI : Finite {x : G // (3 : ℕ) • x = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : Fintype {x : G // (3 : ℕ) • x = 0} := Fintype.ofFinite _
  have hbij : Function.Bijective (representativeTorsion eta hker) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨representativeTorsion_injective eta hker, by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
          ZMod.card, Nat.reducePow] using hcard.symm⟩
  obtain ⟨c, hc⟩ := hbij.surjective ⟨x, hx⟩
  exact ⟨AV.liftO c, congrArg Subtype.val hc⟩

#print axioms representatives_injective
#print axioms eta_surjective_of_torsion_card

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D5
