import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Primitivity of a rank-two lattice inclusion implies its quotient is cyclic.
On-the-spot calculation (c). -/

noncomputable section

open Module

namespace ZInQ.Manuscript.RC.CMField2

/-- If a full-rank sublattice in rank two is not contained in any integer dilation
by a factor greater than 1, then the quotient is cyclic. -/
theorem isAddCyclic_quotient_of_primitive {M : Type*} [AddCommGroup M]
    (b : Basis (Fin 2) ℤ M) (S : Submodule ℤ M) (hS : finrank ℤ S = finrank ℤ M)
    (hp : ∀ k : ℕ, 1 < k → ¬ ∀ x ∈ S, ∃ y : M, x = (k : ℤ) • y) :
    IsAddCyclic (M ⧸ S) := by
  let a := S.smithNormalFormCoeffs b hS
  let v := S.smithNormalFormBotBasis b hS
  let w := S.smithNormalFormTopBasis b hS
  have hd (i : Fin 2) : (v i : M) = a i • w i := S.smithNormalFormBotBasis_def b hS i
  let k := (a 0).natAbs.gcd (a 1).natAbs
  have hk : k = 1 := by
    have hk0 : k ≠ 0 := by
      exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr
        (S.smithNormalFormCoeffs_ne_zero b hS 0)))
    by_contra he
    refine hp k (by omega) ?_
    have h0 : (k : ℤ) ∣ a 0 := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    have h1 : (k : ℤ) ∣ a 1 := Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
    obtain ⟨e0, he0⟩ := h0
    obtain ⟨e1, he1⟩ := h1
    intro x hx
    let z : S := ⟨x, hx⟩
    have hz := congrArg (fun z : S => (z : M)) (v.sum_repr z).symm
    rw [Fin.sum_univ_two] at hz
    refine ⟨v.repr z 0 • (e0 • w 0) + v.repr z 1 • (e1 • w 1), ?_⟩
    simpa only [Submodule.coe_add, Submodule.coe_smul, hd, he0, he1, mul_smul,
      smul_add, smul_comm (v.repr z 0) (k : ℤ), smul_comm (v.repr z 1) (k : ℤ)] using hz
  let e := (S.quotientEquivPiZMod b hS).trans
    (LinearEquiv.piFinTwo ℤ (fun i : Fin 2 => ZMod ((a i).natAbs))).toAddEquiv
  have : IsAddCyclic (ZMod ((a 0).natAbs) × ZMod ((a 1).natAbs)) := by
    apply AddGroup.isAddCyclic_prod_iff.mpr
    exact ⟨inferInstance, inferInstance, by simpa [Nat.card_zmod, Nat.coprime_iff_gcd_eq_one, k] using hk⟩
  exact e.isAddCyclic.mpr this

/-- Apply the primitive criterion to the period-lattice quotient. -/
theorem isAddCyclic_sublatticeQuotient_of_primitive (L M : PeriodPair)
    (h : M.lattice ≤ L.lattice)
    (hp : ∀ k : ℕ, 1 < k → ¬ ∀ x ∈ M.lattice, ∃ y ∈ L.lattice, x = (k : ℤ) • y) :
    IsAddCyclic (L.sublatticeQuotient M) := by
  let S := (M.lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup).toIntSubmodule
  let e₀ : S ≃+ M.lattice := AddSubgroup.addSubgroupOfEquivOfLe
    (show M.lattice.toAddSubgroup ≤ L.lattice.toAddSubgroup from h)
  let e : S ≃ₗ[ℤ] M.lattice := e₀.toIntLinearEquiv
  change IsAddCyclic (L.lattice ⧸ S)
  apply isAddCyclic_quotient_of_primitive L.latticeBasis S
  · exact e.finrank_eq.trans (M.finrank_lattice.trans L.finrank_lattice.symm)
  · intro k hk hincl
    apply hp k hk
    intro x hx
    obtain ⟨y, hy⟩ := hincl ⟨x, h hx⟩ hx
    exact ⟨y, y.property, congrArg Subtype.val hy⟩

/-- A cyclic rank-two quotient cannot come from a sublattice inside a
nontrivial integer dilation. -/
theorem primitive_of_isAddCyclic_quotient {M : Type*} [AddCommGroup M]
    (b : Basis (Fin 2) ℤ M) (S : Submodule ℤ M) (hS : finrank ℤ S = finrank ℤ M)
    (hc : IsAddCyclic (M ⧸ S)) (k : ℕ) (hk : 1 < k)
    (hd : ∀ x ∈ S, ∃ y : M, x = (k : ℤ) • y) : False := by
  let a := S.smithNormalFormCoeffs b hS
  let v := S.smithNormalFormBotBasis b hS
  let w := S.smithNormalFormTopBasis b hS
  let e := (S.quotientEquivPiZMod b hS).trans
    (LinearEquiv.piFinTwo ℤ (fun i : Fin 2 => ZMod ((a i).natAbs))).toAddEquiv
  obtain ⟨_, _, hcp⟩ := AddGroup.isAddCyclic_prod_iff.mp (e.isAddCyclic.mp hc)
  simp only [Nat.card_zmod, Nat.coprime_iff_gcd_eq_one] at hcp
  have ha (i : Fin 2) : k ∣ (a i).natAbs := by
    obtain ⟨y, hy⟩ := hd (v i) (v i).property
    have h := congrArg (fun x => w.repr x i)
      ((S.smithNormalFormBotBasis_def b hS i).symm.trans hy)
    have h' : (k : ℤ) ∣ a i := ⟨w.repr y i, by simpa [w, a] using h⟩
    exact Int.natCast_dvd.mp h'
  have hg := Nat.dvd_gcd (ha 0) (ha 1)
  rw [hcp] at hg
  exact (Nat.ne_of_gt hk) (Nat.dvd_one.mp hg)

/-- The converse primitive criterion on the period-lattice quotient. -/
theorem primitive_of_isAddCyclic_sublatticeQuotient (L M : PeriodPair)
    (h : M.lattice ≤ L.lattice) (hc : IsAddCyclic (L.sublatticeQuotient M))
    (k : ℕ) (hk : 1 < k)
    (hd : ∀ x ∈ M.lattice, ∃ y ∈ L.lattice, x = (k : ℤ) • y) : False := by
  let S := (M.lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup).toIntSubmodule
  let e₀ : S ≃+ M.lattice := AddSubgroup.addSubgroupOfEquivOfLe
    (show M.lattice.toAddSubgroup ≤ L.lattice.toAddSubgroup from h)
  let e : S ≃ₗ[ℤ] M.lattice := e₀.toIntLinearEquiv
  refine primitive_of_isAddCyclic_quotient L.latticeBasis S
    (e.finrank_eq.trans (M.finrank_lattice.trans L.finrank_lattice.symm)) hc k hk ?_
  intro x hx
  obtain ⟨y, hy, he⟩ := hd x hx
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩


end ZInQ.Manuscript.RC.CMField2
