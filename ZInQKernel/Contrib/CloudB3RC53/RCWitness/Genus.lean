import ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves

/-!
# RC inhabitability witnesses, group D: the pre-leaves of the genus and odd side

Witnesses for the leaves of `PreLeaves` / `PostLeaves` that do not need genuine arithmetic data,
over explicit interface data `W₀ ℓ c` (support `S₀ ℓ`, the prepared filter and the stage support
`{1}`, the hyperfilter, `M_θ = θ + c + 1`, the odd coefficients `a_θ(D) = c₀`, `δ_o = v₂ c₀`):

* `preDataSpec_W₀`, `preparedSpec_W₀`: the data specification and the prepared filter (non-vacuous:
  the prepared filter is `{1}`).
* `visibilityInputs_zero`: `VisibilityInputs` (non-vacuous stage support `{1}`, with `λ = 0` and
  `a_θ = 0`).
* `witnessLeaf_W₀`: `WitnessLeaf` (`D_w = 1`, `c = v₂ c₀`).
* `joint_W₀` (**conditional joint witness**): if `E_ℓ` has analytic rank one, then `PreDataSpec`,
  `PreparedSpec`, `VisibilityInputs` and `WitnessLeaf` hold together for `W₀` (`λ = 1`, `ω = 0`).
  The rank hypothesis cannot be dropped: (O.7) with the native-index bound and the torsion clause
  force every admissible `D` with `v₂ a_θ(D) < M_θ` to be a simple zero, and the visible witness is
  such a `D`.
* `companionLeaf_W₀`: `CompanionLeaf` (vacuous: the odd symbol is a unit at the empty
  configuration).
* `evenUpper_of_scalar`: `EvenUpperRC11Inputs` from its clause (3.2) alone (the other clauses
  vacuous); (3.2) for the genuine normalization of `L_*` is genuine arithmetic.

Probe file; nothing here is used by the proof.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RCWitness.Genus

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring ZInQ.Contrib.CloudB3RC53 Filter

/-- The interface data of the check. -/
def W₀ (ℓ : ℕ) (c : ℤ) (a : ℤ) : WData ℓ where
  S := S0 ℓ
  prepared h := h = 1
  Lstar _ := 1
  jgen _ := 0
  jrc _ _ := 0
  hstar := -7
  stages := hyperfilter ℕ
  Mθ θ := θ + c.toNat + 1
  aθ _ _ := a
  admissible _ D := D = 1
  δo := c
  kfin := -7
  uPrim _ _ := 0
  uTilde _ _ := 0
  Partitionable _ := False

theorem preDataSpec_W₀ (ℓ : ℕ) (c a : ℤ) : PreDataSpec (W₀ ℓ c a) where
  support_prime p hp := by
    simp only [W₀, S0, Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_of_mem_primeFactors hp
  support_base := le_rfl
  stages_hyper := rfl
  stages_index θ := by simp only [W₀]; omega
  admissible_split := ⟨fun _ _ => True, fun _ _ => by simp [W₀], fun _ => trivial⟩
  prepared_one := rfl

theorem preparedSpec_W₀ (ℓ : ℕ) (c a : ℤ) : PreparedSpec (W₀ ℓ c a) := by
  rintro h rfl
  refine ⟨one_pos, squarefree_one, rfl, fun p hp hd => ?_⟩
  have hp' : p.Prime := (preDataSpec_W₀ ℓ c a).support_prime p hp
  have : (p : ℤ) ∣ 1 := hd
  exact hp'.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

/-- `VisibilityInputs` with the stage support `{1}`, `λ = 0`, `a_θ = 0`. -/
theorem visibilityInputs_zero (ℓ : ℕ) (c : ℤ) : VisibilityInputs (W₀ ℓ c 0).toRCData := by
  refine ⟨fun _ _ => 0, 0, 0, fun θ D _ => ⟨1, odd_one, by simp [W₀]⟩, ?_, ?_⟩
  · intro θ Dd _ _ k _ _; exact dvd_zero _
  · intro θ Dd _ _; exact dvd_zero _

/-- The `2`-adic valuation of `c₀`, a finite integer. -/
theorem exists_vZ_c0 : ∃ c : ℤ, vZ (Odd.c0 : ℤ) = c := by
  have h0 : ((Odd.c0 : ℤ) : ℚ_[2]) ≠ 0 := by
    exact_mod_cast (show (Odd.c0 : ℤ) ≠ 0 by simp [Odd.c0])
  exact ⟨Padic.valuation ((Odd.c0 : ℤ) : ℚ_[2]), by
    rw [vZ, v2, Padic.addValuation.apply (by exact_mod_cast h0)]⟩

/-- The valuation `c = v₂ c₀`. -/
def cw : ℤ := Classical.choose exists_vZ_c0

theorem vZ_c0 : vZ (Odd.c0 : ℤ) = cw := Classical.choose_spec exists_vZ_c0

theorem witnessLeaf_W₀ (ℓ : ℕ) : WitnessLeaf (W₀ ℓ cw Odd.c0) := by
  refine ⟨1, cw, Eventually.of_forall fun θ => ⟨rfl, vZ_c0, ?_⟩⟩
  change (cw : WithTop ℤ) < ((θ + cw.toNat + 1 : ℕ) : ℤ)
  exact_mod_cast (show cw < ((θ + cw.toNat + 1 : ℕ) : ℤ) by push_cast; omega)

/-- **Conditional joint witness**: given that `E_ℓ` has analytic rank one, the four pre-leaves
hold together. -/
theorem joint_W₀ (ℓ : ℕ) (hR : AnalyticRank (Etw ℓ 1) 1) :
    PreDataSpec (W₀ ℓ cw Odd.c0) ∧ PreparedSpec (W₀ ℓ cw Odd.c0) ∧
      VisibilityInputs (W₀ ℓ cw Odd.c0).toRCData ∧ WitnessLeaf (W₀ ℓ cw Odd.c0) := by
  refine ⟨preDataSpec_W₀ _ _ _, preparedSpec_W₀ _ _ _, ?_, witnessLeaf_W₀ ℓ⟩
  refine ⟨fun _ _ => 1, 0, 1, fun θ D _ => ⟨1, odd_one, by simp [W₀]⟩, ?_, ?_⟩
  · intro θ Dd _ _ k _ hk
    simp only [W₀] at hk
    omega
  · intro θ Dd hD hnot
    change Dd = 1 at hD
    subst hD
    exact absurd hR hnot

/-- `CompanionLeaf` (vacuous: the odd symbol is a unit at the empty configuration). -/
theorem companionLeaf_W₀ (ℓ : ℕ) : CompanionLeaf (W₀ ℓ cw Odd.c0) := by
  intro hU
  exact absurd (Eventually.of_forall fun _ => vZ_c0) hU

/-- `EvenUpperRC11Inputs` from its clause (3.2) alone (`unitSym = ∅`, nothing partitionable). -/
theorem evenUpper_of_scalar (ℓ : ℕ) (c a : ℤ)
    (h32 : ∀ L : Even.CentralNormalization (Ecurve ℓ), L.Lstar = (W₀ ℓ c a).Lstar →
      Even.EvenScalar32 (Ecurve ℓ) 0 L) :
    EvenUpperRC11Inputs (W₀ ℓ c a) :=
  ⟨fun _ => False, 0, 0, fun _ h => h.elim, h32, fun _ _ h => h.elim⟩

/-- `Even.CentralLengthInput` (not reachable from `RCLeaves`; listed in the check request): the
zero modules, all lengths `0`, `v₂ u = 1`. -/
def centralLengthInput_zero : Even.CentralLengthInput where
  X₁ := PUnit
  X₂ := PUnit
  X₃ := PUnit
  Xloc := PUnit
  XR := PUnit
  X₅ := PUnit
  f₁ := 0
  f₂ := 0
  f₃ := 0
  f₄ := 0
  ex₁ _ _ _ := rfl
  ex₁₂ _ := ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  ex₂₃ _ := ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  ex₃₄ _ := ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  ex₄ _ := ⟨0, Subsingleton.elim _ _⟩
  i := 0
  s := 0
  G := 0
  r₂ := 0
  g := 0
  len₁ := Module.length_eq_zero
  len₂ := Module.length_eq_zero
  lenloc := Module.length_eq_zero
  lenR := Module.length_eq_zero
  len₅ := Module.length_eq_zero
  M := PUnit
  HR1 := PUnit
  ρ := 0
  r₁ := 0
  k := 0
  m := 0
  lenHR1 := Module.length_eq_zero
  lenTors := Module.length_eq_zero
  lenK := Module.length_eq_zero
  lenFree := Module.length_eq_zero
  Tp := PUnit
  P := PUnit
  a := 0
  π := 0
  exa _ _ _ := rfl
  exaπ _ := ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  exπ _ := ⟨0, Subsingleton.elim _ _⟩
  torsFree := Subsingleton.elim _ _
  p₀ := 0
  aₛ := 0
  lenP := Module.length_eq_zero
  lenSat := Module.length_eq_zero
  H2p := PUnit
  j₁ := 0
  j₂ := 0
  j₃ := 0
  exj₁ _ _ _ := Subsingleton.elim _ _
  exj₁₂ _ := ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  exj₂₃ _ := ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  exj₃ _ := ⟨0, Subsingleton.elim _ _⟩
  lH2p := 0
  lenH2p := Module.length_eq_zero
  v2u := 1
  vfree := 0
  e₂ := 0
  v2exp := 0
  wedge := by norm_num
  expStar := by norm_num

end ZInQ.Contrib.CloudB3RC53.RCWitness.Genus
