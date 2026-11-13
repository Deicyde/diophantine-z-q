import ZInQKernel.Contrib.BrauerCohomology.Galois

set_option autoImplicit false

/-!
# The real place: `H²(G_ℝ, ℤ/2)` has exactly two elements

`Field.absoluteGaloisGroup ℝ = Gal(ℝ̄/ℝ)` has order `2` (`ℝ̄ ≅ ℂ` has degree `2`) and its Krull
topology is discrete. For a discrete group `{1, s}` of order two, an inhomogeneous
`ZMod 2`-valued 2-cocycle `ε` satisfies `ε 1 x = ε x 1 = ε 1 1`, and it is a coboundary iff
`ε s s = ε 1 1`; the cocycle `ε a b = [a = s ∧ b = s]` is not a coboundary. Hence
`PkgI6.H2TwoClasses (Field.absoluteGaloisGroup ℝ)` holds, and through the comparison of
`Galois.lean` the real component of the bundle target `PkgI6.LocalH2Card` (frozen reference T15)
holds as well. No class field theory is used at this place.
-/

open CategoryTheory PkgI6

namespace ZInQ.Contrib.BrauerCohomology

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

section CardTwo

variable {G : Type*} [Group G] [TopologicalSpace G]

omit [TopologicalSpace G] in
/-- In a group with exactly two elements there is `s ≠ 1` with `G = {1, s}` and `s * s = 1`. -/
theorem exists_eq_one_or_eq_of_natCard_eq_two (h2 : Nat.card G = 2) :
    ∃ s : G, s ≠ 1 ∧ (∀ z : G, z = 1 ∨ z = s) ∧ s * s = 1 := by
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp h2
  have mem : ∀ z : G, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set G) := huniv ▸ Set.mem_univ z
    simpa using this
  have key : ∃ s : G, s ≠ 1 ∧ ∀ z : G, z = 1 ∨ z = s := by
    rcases mem 1 with h1 | h1
    · refine ⟨y, fun hy => hxy (h1.symm.trans hy.symm), fun z => ?_⟩
      rcases mem z with hz | hz
      · exact Or.inl (hz.trans h1.symm)
      · exact Or.inr hz
    · refine ⟨x, fun hx => hxy (hx.trans h1), fun z => ?_⟩
      rcases mem z with hz | hz
      · exact Or.inr hz
      · exact Or.inl (hz.trans h1.symm)
  obtain ⟨s, hs1, hall⟩ := key
  refine ⟨s, hs1, hall, ?_⟩
  rcases hall (s * s) with h | h
  · exact h
  · exact absurd (mul_eq_left.mp h) hs1

/-- Normal form of a cocycle: `ε 1 x = ε 1 1`. -/
theorem cocycle2_one_left {ε : G → G → ZMod 2} (hε : IsCocycle2 ε) (x : G) :
    ε 1 x = ε 1 1 := by
  have h := hε.2 1 1 x
  simp only [one_mul] at h
  rw [← sub_eq_zero, ← h]
  abel

/-- Normal form of a cocycle: `ε x 1 = ε 1 1`. -/
theorem cocycle2_one_right {ε : G → G → ZMod 2} (hε : IsCocycle2 ε) (x : G) :
    ε x 1 = ε 1 1 := by
  have h := hε.2 x 1 1
  simp only [mul_one] at h
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  abel

/-- For a group `{1, s}` of order two, a cocycle is a coboundary iff `ε s s = ε 1 1`. -/
theorem isCoboundary2_iff_of_order_two {s : G} (hall : ∀ z : G, z = 1 ∨ z = s)
    (hss : s * s = 1) {ε : G → G → ZMod 2} (hε : IsCocycle2 ε) :
    IsCoboundary2 ε ↔ ε s s = ε 1 1 := by
  constructor
  · rintro ⟨f, -, e⟩
    rw [e, e, hss, one_mul]
    generalize f s = u
    generalize f 1 = w
    revert u w
    decide
  · intro h
    refine ⟨fun _ => ε 1 1, continuous_const, fun a b => ?_⟩
    simp only [sub_self, zero_add]
    rcases hall a with rfl | rfl
    · exact cocycle2_one_left hε b
    · rcases hall b with rfl | rfl
      · exact cocycle2_one_right hε a
      · exact h

/-- **A discrete group of order two has exactly two classes in `H²(G, ℤ/2)`.** -/
theorem h2TwoClasses_of_natCard_eq_two [DiscreteTopology G] (h2 : Nat.card G = 2) :
    H2TwoClasses G := by
  classical
  obtain ⟨s, hs1, hall, hss⟩ := exists_eq_one_or_eq_of_natCard_eq_two h2
  have hdisc : ∀ ε : G → G → ZMod 2, Continuous (fun x : G × G => ε x.1 x.2) :=
    fun _ => continuous_of_discreteTopology
  refine ⟨?_, fun ε₁ ε₂ h₁ h₂ n₁ n₂ => ?_⟩
  · let ε₀ : G → G → ZMod 2 := fun a b => if a = s ∧ b = s then 1 else 0
    have hc : IsCocycle2 ε₀ := by
      refine ⟨hdisc ε₀, fun a b c => ?_⟩
      have hs1' : (1 : G) ≠ s := fun h => hs1 h.symm
      rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl <;>
        rcases hall c with rfl | rfl <;>
        simp [ε₀, hss, hs1', zmod2_one_add_one]
    refine ⟨ε₀, hc, fun hcob => ?_⟩
    have := (isCoboundary2_iff_of_order_two hall hss hc).1 hcob
    have hs1' : (1 : G) ≠ s := fun h => hs1 h.symm
    simp [ε₀, hs1'] at this
  · have c := h₁.sub h₂
    rw [isCoboundary2_iff_of_order_two hall hss c]
    have e₁ : ε₁ s s ≠ ε₁ 1 1 := fun h => n₁ ((isCoboundary2_iff_of_order_two hall hss h₁).2 h)
    have e₂ : ε₂ s s ≠ ε₂ 1 1 := fun h => n₂ ((isCoboundary2_iff_of_order_two hall hss h₂).2 h)
    simp only [Pi.sub_apply]
    revert e₁ e₂
    generalize ε₁ s s = x
    generalize ε₁ 1 1 = y
    generalize ε₂ s s = z
    generalize ε₂ 1 1 = w
    revert x y z w
    decide

end CardTwo

section Real

/-- `ℂ` is an algebraic closure of `ℝ`. -/
theorem isAlgClosure_real_complex : IsAlgClosure ℝ ℂ :=
  ⟨Complex.isAlgClosed, Algebra.IsAlgebraic.of_finite ℝ ℂ⟩

/-- The algebraic closure of `ℝ` has degree `2`. -/
theorem finrank_algebraicClosure_real : Module.finrank ℝ (AlgebraicClosure ℝ) = 2 := by
  have := isAlgClosure_real_complex
  rw [(IsAlgClosure.equiv ℝ (AlgebraicClosure ℝ) ℂ).toLinearEquiv.finrank_eq]
  exact Complex.finrank_real_complex

theorem finiteDimensional_algebraicClosure_real :
    FiniteDimensional ℝ (AlgebraicClosure ℝ) :=
  Module.finite_of_finrank_eq_succ finrank_algebraicClosure_real

/-- `G_ℝ` has exactly two elements. -/
theorem natCard_absoluteGaloisGroup_real : Nat.card (Field.absoluteGaloisGroup ℝ) = 2 := by
  have := finiteDimensional_algebraicClosure_real
  show Nat.card (AlgebraicClosure ℝ ≃ₐ[ℝ] AlgebraicClosure ℝ) = 2
  rw [IsGalois.card_aut_eq_finrank, finrank_algebraicClosure_real]

/-- The Krull topology on `G_ℝ` is discrete. -/
theorem discreteTopology_absoluteGaloisGroup_real :
    DiscreteTopology (Field.absoluteGaloisGroup ℝ) :=
  have := finiteDimensional_algebraicClosure_real
  krullTopology_discreteTopology_of_finiteDimensional ℝ (AlgebraicClosure ℝ)

/-- **Cochain form of T15 at the real place** (`PkgI6.LocalH2CardC`, second component). -/
theorem h2TwoClasses_real : H2TwoClasses (Field.absoluteGaloisGroup ℝ) :=
  have := discreteTopology_absoluteGaloisGroup_real
  h2TwoClasses_of_natCard_eq_two natCard_absoluteGaloisGroup_real

/-- **Bundle form of T15 at the real place** (`PkgI6.LocalH2Card`, second component): Mathlib's
`continuousCohomology 2` of `ℤ/2`, restricted from `G_ℚ` to `G_ℝ`, has exactly two elements. -/
theorem natCard_h2_real :
    Nat.card (continuousCohomology 2
        (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ) :
          Field.absoluteGaloisGroup ℝ →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ))) = 2 :=
  (natCard_Z2res_eq_two_iff ℝ).2 h2TwoClasses_real

/-- With the real place proved, the bundle target T15 (`PkgI6.LocalH2Card`) is exactly its
`p`-adic part. -/
theorem localH2Card_iff_padic :
    LocalH2Card ↔ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card (continuousCohomology 2
        (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) :
          Field.absoluteGaloisGroup ℚ_[p] →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ))) = 2 :=
  ⟨fun h => h.1, fun h => ⟨h, natCard_h2_real⟩⟩

/-- With the real place proved, the cochain target `PkgI6.LocalH2CardC` is exactly its `p`-adic
part. -/
theorem localH2CardC_iff_padic :
    LocalH2CardC ↔ ∀ (p : ℕ) [Fact p.Prime], H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p]) :=
  ⟨fun h => h.1, fun h => ⟨h, h2TwoClasses_real⟩⟩

end Real

end ZInQ.Contrib.BrauerCohomology
