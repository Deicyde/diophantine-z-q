import ZInQKernel.Contrib.OneProof.RC.O12Local.Newvector
import Mathlib.Topology.Instances.Matrix

/-! The conductor-one argument, separated from Casselman's printed inputs (tex 9799–9811,
9857–9861). The local tests use the lower-right convention throughout. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Local

open Matrix

variable (p : ℕ) [Fact p.Prime]
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

abbrev LocalCharacter (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] := ℚ_[p]ˣ →* Eˣ
abbrev LocalAction (p : ℕ) [Fact p.Prime] (E V : Type*) [Field E] [AddCommGroup V]
    [Module E V] := GL (Fin 2) ℚ_[p] →* (V →ₗ[E] V)

/-- Units congruent to one modulo (p^n), with the full unit group at (n=0). -/
def unitAtLevel (n : ℕ) (u : ℚ_[p]ˣ) : Prop :=
  ‖(u : ℚ_[p])‖ = 1 ∧ (n = 0 ∨ ‖(u : ℚ_[p]) - 1‖ ≤ ((p : ℝ)⁻¹)^n)

def charTrivialAt (χ : LocalCharacter p E) (n : ℕ) : Prop :=
  ∀ u, unitAtLevel p n u → χ u = 1

def charConductor (χ : LocalCharacter p E) (n : ℕ) : Prop :=
  charTrivialAt p χ n ∧ ∀ m < n, ¬ charTrivialAt p χ m

/-- The lower-right (K_1(p^n)) test inside (mathrm{GL}_2(mathbb Q_p)). -/
def atK1 (n : ℕ) (g : GL (Fin 2) ℚ_[p]) : Prop :=
  let M : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
  (∀ i j, ‖M i j‖ ≤ 1) ∧ ‖M.det‖ = 1 ∧
    (n = 0 ∨ (‖M 1 0‖ ≤ ((p : ℝ)⁻¹)^n ∧ ‖M 1 1 - 1‖ ≤ ((p : ℝ)⁻¹)^n))

/-- The (K_1(p^n))-fixed space. A subgroup construction is not needed for this test. -/
def levelSpace (π : LocalAction p E V) (n : ℕ) : Submodule E V where
  carrier := {v | ∀ g, atK1 p n g → π g v = v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw g hg
    rw [map_add, hv g hg, hw g hg]
  smul_mem' := by
    intro c v hv g hg
    rw [map_smul, hv g hg]

def hasLevel (π : LocalAction p E V) (n : ℕ) : Prop :=
  ∃ v : V, v ∈ levelSpace p π n ∧ v ≠ 0

def repConductor (π : LocalAction p E V) (n : ℕ) : Prop :=
  hasLevel p π n ∧ ∀ m < n, ¬ hasLevel p π m

def centralAction (π : LocalAction p E V) (χ : LocalCharacter p E) : Prop :=
  ∀ u v, π (upper u u 0) v = (χ u : E) • v

/-- The central scalar (u1_2) is in the level group whenever (uequiv1mod p^n). -/
theorem central_mem_atK1 {n : ℕ} {u : ℚ_[p]ˣ} (hu : unitAtLevel p n u) :
    atK1 p n (upper u u 0) := by
  obtain ⟨hu, hn⟩ := hu
  change (∀ i j : Fin 2, ‖(!![(u : ℚ_[p]), 0; 0, (u : ℚ_[p])] :
    Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1) ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hu]
  · simp [upper, det_fin_two, norm_mul, hu]
  · rcases hn with hn | hn
    · exact Or.inl hn
    · exact Or.inr ⟨by simp [upper], by simpa [upper] using hn⟩

/-- A nonzero fixed vector forces the central character to pass the same level test. -/
theorem central_trivial_of_level (π : LocalAction p E V) (χ : LocalCharacter p E)
    (hc : centralAction p π χ) {n : ℕ} (h : hasLevel p π n) :
    charTrivialAt p χ n := by
  obtain ⟨v, hv, hne⟩ := h
  intro u hu
  have e := hv (upper u u 0) (central_mem_atK1 p hu)
  rw [hc] at e
  apply Units.ext
  exact smul_left_injective E hne (e.trans (one_smul E v).symm)

/-- The representation conductor is bounded below by the central character conductor
and above by the level in which the constituent occurs (tex 9799–9801). -/
theorem conductor_bounds (π : LocalAction p E V) (χ : LocalCharacter p E)
    (hc : centralAction p π χ) {a c n : ℕ} (hχ : charConductor p χ a)
    (hπ : repConductor p π c) (hn : hasLevel p π n) :
    a ≤ c ∧ c ≤ n :=
  ⟨le_of_not_gt fun h => hχ.2 c h (central_trivial_of_level p π χ hc hπ.1),
    le_of_not_gt fun h => hπ.2 n h hn⟩

/-- The normalized principal-series model of the given local action. The target
of the injection, as specified by `full`, is the space of locally constant
functions satisfying the normalized left covariance. -/
structure InducedModel (π : LocalAction p E V) (halfMod μ₁ μ₂ : LocalCharacter p E) where
  realize : V →ₗ[E] (GL (Fin 2) ℚ_[p] → E)
  injective : Function.Injective realize
  covariance : ∀ v a d x g, realize v (upper a d x * g) =
    (μ₁ a : E) * (μ₂ d : E) * (halfMod (a / d) : E) * realize v g
  locallyConstant : ∀ v, @IsLocallyConstant _ _ (TopologicalSpace.induced
    (fun g : GL (Fin 2) ℚ_[p] => (g : Matrix (Fin 2) (Fin 2) ℚ_[p])) inferInstance) (realize v)
  full : ∀ f : GL (Fin 2) ℚ_[p] → E, @IsLocallyConstant _ _ (TopologicalSpace.induced
      (fun g : GL (Fin 2) ℚ_[p] => (g : Matrix (Fin 2) (Fin 2) ℚ_[p])) inferInstance) f →
    (∀ a d x g, f (upper a d x * g) =
      (μ₁ a : E) * (μ₂ d : E) * (halfMod (a / d) : E) * f g) → ∃ v, realize v = f
  right_translate : ∀ v g t, realize (π t v) g = realize v (g * t)

/-- PRINT: Casselman, Theorem 1, pp. 302–306 (UNVERIFIED), the conductor cases
used at tex 9802–9809. The two special cases are distinguished by the twisting character.
This is the classification for an irreducible generic cuspidal local component. -/
inductive CasselmanCases (π : LocalAction p E V) (halfMod χ : LocalCharacter p E)
    (c : ℕ) : Prop
  | principal (μ₁ μ₂ : LocalCharacter p E) (a₁ a₂ : ℕ)
      (cond₁ : charConductor p μ₁ a₁) (cond₂ : charConductor p μ₂ a₂)
      (cond : c = a₁ + a₂) (central : χ = μ₁ * μ₂)
      (model : Nonempty (InducedModel p π halfMod μ₁ μ₂))
  | specialUnramified (cond : c = 1) (central : charTrivialAt p χ 0)
  | specialRamified (cond : 2 ≤ c)
  | supercuspidal (cond : 2 ≤ c)

/-- PRINT: Casselman, Corollary p. 306 and Theorem 4 p. 313 (UNVERIFIED),
tex 9859–9861. The fixed-space dimension at level (p^n) is (n+1-c) for (nge c)
and zero below the conductor. -/
def CasselmanOldspace (π : LocalAction p E V) (c : ℕ) : Prop :=
  ∀ n, Module.Finite E (levelSpace p π n) ∧
    Module.finrank E (levelSpace p π n) = n + 1 - c

/-- ELLIOT (tex 9825–9827): interchange of the inducing characters of the
irreducible principal series. Only the ordering from ramified to unramified first
is used. -/
def PrincipalInterchange (π : LocalAction p E V) (halfMod : LocalCharacter p E) : Prop :=
  ∀ μ₁ μ₂ : LocalCharacter p E, charConductor p μ₁ 1 → charConductor p μ₂ 0 →
    Nonempty (InducedModel p π halfMod μ₁ μ₂) →
    Nonempty (InducedModel p π halfMod μ₂ μ₁)

theorem conductor_one (π : LocalAction p E V) (χ : LocalCharacter p E)
    (hc : centralAction p π χ) {c n : ℕ} (hχ : charConductor p χ 1)
    (hπ : repConductor p π c) (hn : hasLevel p π n) (hn₁ : n ≤ 1) : c = 1 := by
  have h := conductor_bounds p π χ hc hχ hπ hn
  omega

/-- At conductor one with ramified central character, the only possible case
has a conductor-zero character first and a conductor-one character second. -/
theorem ordered_principal (π : LocalAction p E V) (halfMod χ : LocalCharacter p E)
    (hχ : charConductor p χ 1) (hclass : CasselmanCases p π halfMod χ 1)
    (hswap : PrincipalInterchange p π halfMod) :
    ∃ μ₁ μ₂ : LocalCharacter p E, charConductor p μ₁ 0 ∧ charConductor p μ₂ 1 ∧
      χ = μ₁ * μ₂ ∧ Nonempty (InducedModel p π halfMod μ₁ μ₂) := by
  cases hclass with
  | principal μ₁ μ₂ a₁ a₂ h₁ h₂ hsum hcentral hm =>
      by_cases h : a₁ = 0
      · have h' : a₂ = 1 := by omega
        exact ⟨μ₁, μ₂, h ▸ h₁, h' ▸ h₂, hcentral, hm⟩
      · have h' : a₁ = 1 ∧ a₂ = 0 := by omega
        refine ⟨μ₂, μ₁, h'.2 ▸ h₂, h'.1 ▸ h₁, hcentral.trans ?_,
          hswap μ₁ μ₂ (h'.1 ▸ h₁) (h'.2 ▸ h₂) hm⟩
        ext u
        exact mul_comm _ _
  | specialUnramified _ hu => exact False.elim (hχ.2 0 Nat.zero_lt_one hu)
  | specialRamified h | supercuspidal h => omega

/-- The allowed level is already the conductor, so its local fixed space is a line. -/
theorem newspace_one (π : LocalAction p E V) {n : ℕ}
    (hπ : repConductor p π 1) (hn : hasLevel p π n) (hn₁ : n ≤ 1)
    (hCass : CasselmanOldspace p π 1) :
    n = 1 ∧ Module.Finite E (levelSpace p π n) ∧ Module.finrank E (levelSpace p π n) = 1 := by
  have h : n = 1 := by
    by_contra h
    exact hπ.2 n (by omega) hn
  subst n
  exact ⟨rfl, (hCass 1).1, (hCass 1).2⟩

#print axioms central_mem_atK1
#print axioms central_trivial_of_level
#print axioms conductor_bounds
#print axioms conductor_one
#print axioms ordered_principal
#print axioms newspace_one

end ZInQ.Manuscript.RC.O12Local
