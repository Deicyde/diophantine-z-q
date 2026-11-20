import ZInQKernel.Contrib.CMSerreTateSupport.CompatibleTateApproximationClosed

/-!
# A finite-free Tate module from finite first torsion

The basis is derived from the actual first projection image. Projection
onto all ell-torsion is not assumed, and no rank, complete module, basis,
compatible lift, or cardinality formula is supplied to this theorem.
-/

noncomputable section
set_option autoImplicit false

namespace FiniteProjectionTate

variable {ell : ℕ} [Fact ell.Prime] {M : Type*} [AddCommGroup M]

def firstProjection : TT (ell := ell) (M := M) →+ M :=
  (Pi.evalAddMonoidHom (fun _ : ℕ => M) 1).comp (PkgI3.Tate.T ell M).subtype

def firstImage : AddSubgroup M := (firstProjection (ell := ell) (M := M)).range

theorem firstImage_killed (x : firstImage (ell := ell) (M := M)) : ell • x = 0 := by
  apply Subtype.ext
  obtain ⟨t, ht⟩ := x.2
  change ell • x.1 = 0
  rw [← ht]
  change ell • t.1 1 = 0
  simpa only [pow_one] using PkgI3.Tate.pow_smul_eq_zero t.2 1

theorem integral_coeff_apply {r : ℕ} (X : Fin r → TT (ell := ell) (M := M))
    (c : Fin r → ℤ) (n : ℕ) :
    (Fintype.linearCombination ℤ_[ell] X (fun i => (c i : ℤ_[ell]))).1 n =
      ∑ i, c i • (X i).1 n := by
  rw [Fintype.linearCombination_apply]
  let E : TT (ell := ell) (M := M) →+ M :=
    (Pi.evalAddMonoidHom (fun _ : ℕ => M) n).comp (PkgI3.Tate.T ell M).subtype
  change E (∑ i, (c i : ℤ_[ell]) • X i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul, map_zsmul]
  rfl

/-- No exact torsion count is needed: finiteness of actual first torsion
constructs a finite basis of the entire actual compatible Tate module. -/
theorem tate_equiv_of_finite_first_torsion
    [Finite (AddSubgroup.torsionBy M (ell : ℤ))] :
    ∃ r : ℕ, Nonempty (TT (ell := ell) (M := M) ≃ₗ[ℤ_[ell]] (Fin r → ℤ_[ell])) := by
  classical
  let P := firstImage (ell := ell) (M := M)
  let emb : P → AddSubgroup.torsionBy M (ell : ℤ) := fun x =>
    ⟨x.1, AddSubgroup.torsionBy.nsmul_iff.mpr (by
      have h := congrArg (fun z : P => z.1) (firstImage_killed x)
      exact h)⟩
  have hemb : Function.Injective emb := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : AddSubgroup.torsionBy M (ell : ℤ) => z.1) h
  haveI : Finite P := Finite.of_injective emb hemb
  haveI : Module (ZMod ell) P := AddCommGroup.zmodModule (fun x => firstImage_killed x)
  haveI : Module.Finite (ZMod ell) P := Module.Finite.of_finite
  let r := Module.finrank (ZMod ell) P
  let b : Module.Basis (Fin r) (ZMod ell) P := Module.finBasis (ZMod ell) P
  have hlift : ∀ i : Fin r, ∃ t : TT (ell := ell) (M := M), t.1 1 = (b i).1 := by
    intro i
    obtain ⟨t, ht⟩ := (b i).2
    exact ⟨t, ht⟩
  choose X hX using hlift
  have hind : ∀ c : Fin r → ℤ, ∑ i, c i • (X i).1 1 = 0 → ∀ i, (ell : ℤ) ∣ c i := by
    intro c hc i
    have hcP : ∑ j, c j • b j = 0 := by
      apply Subtype.ext
      rw [AddSubgroup.val_finsetSum]
      simpa only [AddSubgroup.coe_zsmul, AddSubgroup.coe_zero, ← hX] using hc
    have hcZ : ∑ j, (c j : ZMod ell) • b j = 0 := by
      simpa only [Int.cast_smul_eq_zsmul] using hcP
    have hzero := Fintype.linearIndependent_iff.mp b.linearIndependent
      (fun j => (c j : ZMod ell)) hcZ i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (c i) ell).mp hzero
  have hspan : ∀ t : TT (ell := ell) (M := M), ∃ a : Fin r → ℤ_[ell],
      (Fintype.linearCombination ℤ_[ell] X a).1 1 = t.1 1 := by
    intro t
    let p : P := ⟨t.1 1, ⟨t, rfl⟩⟩
    let c : Fin r → ℤ := fun i => (b.repr p i).val
    have heZ : ∑ i, (c i : ZMod ell) • b i = p := by
      simpa only [c, Int.cast_natCast, ZMod.natCast_zmod_val] using b.sum_repr p
    have heI : ∑ i, c i • b i = p := by
      simpa only [Int.cast_smul_eq_zsmul] using heZ
    have heM := congrArg (fun z : P => z.1) heI
    rw [AddSubgroup.val_finsetSum] at heM
    refine ⟨fun i => (c i : ℤ_[ell]), ?_⟩
    rw [integral_coeff_apply]
    simpa only [AddSubgroup.coe_zsmul, ← hX] using heM
  have hinj := linearCombination_injective X hind
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  have hsurj := linearCombination_surjective X hspan
  exact ⟨r, ⟨(LinearEquiv.ofBijective (Fintype.linearCombination ℤ_[ell] X) ⟨hinj, hsurj⟩).symm⟩⟩

theorem tate_finite_free_of_finite_first_torsion
    [Finite (AddSubgroup.torsionBy M (ell : ℤ))] :
    Module.Free ℤ_[ell] (TT (ell := ell) (M := M)) ∧
    Module.Finite ℤ_[ell] (TT (ell := ell) (M := M)) := by
  obtain ⟨r, ⟨E⟩⟩ := tate_equiv_of_finite_first_torsion (ell := ell) (M := M)
  exact ⟨Module.Free.of_equiv E.symm, Module.Finite.equiv E.symm⟩

#check tate_equiv_of_finite_first_torsion
#print axioms tate_equiv_of_finite_first_torsion
#print axioms tate_finite_free_of_finite_first_torsion

end FiniteProjectionTate
