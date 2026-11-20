import ZInQKernel.Contrib.OneProof.SZThm33.SemistableTateRank
import ZInQKernel.Contrib.OneProof.SZThm33.RationalFixedTate

/-!
# Lift a prescribed level of a Tate tower

The construction needs only surjectivity of each multiplication transition
between the torsion groups, as supplied by the semiabelian counts.
-/

noncomputable section

open T5Torsion.TateFree (tb exists_lift pow_smul_add)
open scoped TensorProduct

namespace SZRaynaud

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M]

omit [Fact ℓ.Prime] in
/-- Every point at a finite torsion level lifts to a compatible Tate tower
when all the transition maps are surjective. -/
theorem tate_level_surjective_of_transition_surjective
    (hstep : ∀ n (y : M), ℓ ^ n • y = 0 →
      ∃ x : M, ℓ ^ (n + 1) • x = 0 ∧ ℓ • x = y)
    (n : ℕ) (x : M) (hx : ℓ ^ n • x = 0) :
    ∃ t : PkgI3.Tate.T ℓ M, t.1 n = x := by
  classical
  let F (j : ℕ) := {y : M // ℓ ^ (n + j) • y = 0}
  have extend (j : ℕ) (y : F j) : ∃ z : F (j + 1), ℓ • z.1 = y.1 := by
    obtain ⟨z, hz, hz'⟩ := hstep (n + j) y.1 y.2
    exact ⟨⟨z, by simpa only [Nat.add_assoc] using hz⟩, hz'⟩
  let s : (j : ℕ) → F j := fun j =>
    Nat.rec ⟨x, by simpa only [Nat.add_zero] using hx⟩ (fun j y => (extend j y).choose) j
  have hs (j : ℕ) : ℓ • (s (j + 1)).1 = (s j).1 := (extend j (s j)).choose_spec
  let u (m : ℕ) := if m ≤ n then ℓ ^ (n - m) • x else (s (m - n)).1
  refine ⟨⟨u, ?_, ?_⟩, ?_⟩
  · show u 0 = 0
    simp only [u, Nat.zero_le, ite_true, Nat.sub_zero, hx]
  · intro m
    show ℓ • u (m + 1) = u m
    by_cases h : m + 1 ≤ n
    · simp only [u, h, ite_true, show m ≤ n by omega]
      rw [← mul_smul, ← pow_succ', show n - (m + 1) + 1 = n - m by omega]
    · by_cases h' : m = n
      · subst h'
        simp only [u, h, ite_false, le_refl, ite_true, Nat.sub_self, pow_zero, one_smul]
        rw [show m + 1 - m = 0 + 1 by omega, hs 0]
        rfl
      · simp only [u, h, ite_false, show ¬ m ≤ n by omega]
        rw [show m + 1 - n = (m - n) + 1 by omega, hs]
  · show u n = x
    simp [u]

/-- Power-law torsion counts imply that every finite-level torsion point
is the coordinate of a Tate tower. -/
theorem tate_level_surjective_of_counts (r : ℕ)
    (hc : ∀ n : ℕ, Nat.card (tb ℓ M n) = ℓ ^ (n * r))
    (n : ℕ) (x : M) (hx : ℓ ^ n • x = 0) :
    ∃ t : PkgI3.Tate.T ℓ M, t.1 n = x :=
  tate_level_surjective_of_transition_surjective (exists_lift r hc) n x hx

/-- Surjectivity after inverting the prime already puts every coordinate
of every target Tate tower in the image of the underlying point map. -/
theorem mem_range_of_coord_of_rationalTate_surjective {N : Type*} [AddCommGroup N]
    (f : M →+ N)
    (hf : Function.Surjective ((PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]))
    (t : PkgI3.Tate.T ℓ N) (n : ℕ) :
    t.1 n ∈ f.range := by
  let R := ℤ_[ℓ]
  let Q := ℚ_[ℓ]
  let φ := PkgI3.Tate.map (ℓ := ℓ) f
  let u := TensorProduct.mk R Q (PkgI3.Tate.T ℓ M) 1
  let v := TensorProduct.mk R Q (PkgI3.Tate.T ℓ N) 1
  obtain ⟨a, ha⟩ := hf (v t)
  obtain ⟨⟨s, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors R) u a
  have e : φ s = (c : R) • t := by
    apply tate_one_tmul_injective
    change (1 : Q) ⊗ₜ[R] φ s = (1 : Q) ⊗ₜ[R] ((c : R) • t)
    have hc' : φ.baseChange Q (c • a) = φ.baseChange Q (u s) := congrArg (φ.baseChange Q) hc
    rw [LinearMap.map_smul_of_tower, ha] at hc'
    change (c : R) • v t = φ.baseChange Q ((1 : Q) ⊗ₜ[R] s) at hc'
    rw [LinearMap.baseChange_tmul, ← v.map_smul] at hc'
    exact hc'.symm
  obtain ⟨m, α, hα⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero c.2) PadicInt.irreducible_p
  let y := ((↑(α⁻¹) : R)) • s
  have hy : φ y = (ℓ ^ m) • t := by
    change φ (((↑(α⁻¹) : R)) • s) = _
    rw [map_smul, e, hα, ← mul_smul, ← mul_assoc, Units.inv_mul, one_mul,
      ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine ⟨y.1 (n + m), ?_⟩
  have h := congrArg (fun q : PkgI3.Tate.T ℓ N => q.1 (n + m)) hy
  change f (y.1 (n + m)) = (ℓ ^ m) • t.1 (n + m) at h
  exact h.trans (pow_smul_add t.2 n m)

#print axioms tate_level_surjective_of_counts
#print axioms mem_range_of_coord_of_rationalTate_surjective

end SZRaynaud
