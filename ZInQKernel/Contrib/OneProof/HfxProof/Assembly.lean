import ZInQKernel.Contrib.OneProof.T21Proof.BrandtValue

/-!
# hfx-proof: a test vector from a partition of TYZ's 8 classes

Task hfx-proof. For `n`, `τ` and the place `v` above `2`, let `H = ⟨U_n, ℚ̂^×⟩ ≤ B̂^×` and
`DC x = B^× x H`. Suppose
* (surjectivity, TYZ Lemma 2.5 with `B̂^× = B^× Ô_B^×`) every unit of `B̂` lies in some `DC (twoRep v t)`;
* `F : T8 → ℤ` has level sets equal to the classes: `F t = F t'` iff `twoRep v t ∈ DC (twoRep v t')`;
* `F` is orthogonal to `1` and `χ₀`, nonzero, and spans every `G` constant on its level sets and
  orthogonal to `1`, `χ₀`.
Then `π_ℤ^{U_n}` has a nonzero generator (`testVector_of_partition`): the function equal to `F t` on
`DC (twoRep v t)`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

/-- TYZ's index set `{0,1}³` of the 8 classes. -/
abbrev T8 : Type := Fin 2 × Fin 2 × Fin 2

/-- `H = ⟨U_n, ℚ̂^×⟩`. -/
def HgrpN (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) : Subgroup ℍ[AQ]ˣ :=
  Subgroup.closure ((Un n τ : Set ℍ[AQ]ˣ) ∪ Set.range (Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom))

/-- The double coset `B^× x H`. -/
def DC (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (x : ℍ[AQ]) : Set ℍ[AQ] :=
  {y | ∃ γ : ℍ[ℚ], γ ≠ 0 ∧ ∃ h ∈ HgrpN n τ, y = qι γ * x * ↑h}

section DC

variable {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]}

theorem mem_DC_self (x : ℍ[AQ]) : x ∈ DC n τ x :=
  ⟨1, one_ne_zero, 1, Subgroup.one_mem _, by simp⟩

theorem DC_trans {x y z : ℍ[AQ]} (hy : y ∈ DC n τ x) (hz : z ∈ DC n τ y) : z ∈ DC n τ x := by
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hy
  obtain ⟨γ', hγ', h', hh', rfl⟩ := hz
  refine ⟨γ' * γ, mul_ne_zero hγ' hγ, h * h', Subgroup.mul_mem _ hh hh', ?_⟩
  rw [map_mul, Units.val_mul]; noncomm_ring

theorem DC_symm {x y : ℍ[AQ]} (hy : y ∈ DC n τ x) : x ∈ DC n τ y := by
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hy
  refine ⟨γ⁻¹, inv_ne_zero hγ, h⁻¹, Subgroup.inv_mem _ hh, ?_⟩
  have e1 : qι γ⁻¹ * qι γ = 1 := by rw [← map_mul, inv_mul_cancel₀ hγ, map_one]
  calc x = (qι γ⁻¹ * qι γ) * x * ((h : ℍ[AQ]) * ↑h⁻¹) := by rw [e1, Units.mul_inv]; simp
    _ = qι γ⁻¹ * (qι γ * x * ↑h) * ↑h⁻¹ := by noncomm_ring

theorem qι_mul_mem_DC {x y : ℍ[AQ]} {γ : ℍ[ℚ]} (hγ : γ ≠ 0) :
    qι γ * y ∈ DC n τ x ↔ y ∈ DC n τ x := by
  constructor
  · intro h
    refine DC_trans h ⟨γ⁻¹, inv_ne_zero hγ, 1, Subgroup.one_mem _, ?_⟩
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hγ, map_one]; simp
  · intro h
    exact DC_trans h ⟨γ, hγ, 1, Subgroup.one_mem _, by simp⟩

theorem mul_unit_mem_DC {x y : ℍ[AQ]} {u : ℍ[AQ]ˣ} (hu : u ∈ HgrpN n τ) :
    y * ↑u ∈ DC n τ x ↔ y ∈ DC n τ x := by
  constructor
  · intro h
    refine DC_trans h ⟨1, one_ne_zero, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    rw [map_one, one_mul, mul_assoc, Units.mul_inv, mul_one]
  · intro h
    exact DC_trans h ⟨1, one_ne_zero, u, hu, by rw [map_one, one_mul]⟩

/-- A function in `π_ℤ^{U_n}` is right `H`-invariant on units. -/
theorem inPiZ_mul_H {g : ℍ[AQ] → ℤ} (hg : InPiZ n τ g) {h : ℍ[AQ]ˣ} (hh : h ∈ HgrpN n τ) :
    ∀ x : ℍ[AQ]ˣ, g ((x : ℍ[AQ]) * ↑h) = g x := by
  induction hh using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with hu | ⟨z, rfl⟩
    · exact fun x => hg.2.1 x u hu
    · exact fun x => hg.2.2.1 x z
  | one => intro x; simp
  | mul a b _ _ ha hb =>
    intro x
    calc g (↑x * ↑(a * b)) = g (↑(x * a) * ↑b) := by rw [Units.val_mul, Units.val_mul, mul_assoc]
      _ = g ↑(x * a) := hb _
      _ = g ↑x := by rw [Units.val_mul]; exact ha x
  | inv a _ ha =>
    intro x
    have := ha (x * a⁻¹)
    rw [Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one] at this
    exact this.symm

/-- A function in `π_ℤ^{U_n}` is constant on double cosets of units. -/
theorem inPiZ_eq_of_mem_DC {g : ℍ[AQ] → ℤ} (hg : InPiZ n τ g) {x y : ℍ[AQ]ˣ}
    (hy : (y : ℍ[AQ]) ∈ DC n τ x) : g y = g x := by
  obtain ⟨γ, hγ, h, hh, e⟩ := hy
  rw [e, mul_assoc, ← Units.val_mul, hg.1 γ hγ]
  exact inPiZ_mul_H hg hh x

end DC

/-- `twoRep v t` as a unit. -/
def twoRepU (v : HeightOneSpectrum (𝓞 ℚ)) (t : T8) : ℍ[AQ]ˣ :=
  ιAtU v (twoRepQ t) (twoRepQ_ne_zero t)

theorem twoRepU_coe (v : HeightOneSpectrum (𝓞 ℚ)) (t : T8) :
    ((twoRepU v t : ℍ[AQ]ˣ) : ℍ[AQ]) = twoRep v t := rfl

section Assembly

variable {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {v : HeightOneSpectrum (𝓞 ℚ)}

open Classical in
/-- The candidate test vector: `F t` on `DC (twoRep v t)`, `0` off the 8 double cosets. -/
def fOf (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (v : HeightOneSpectrum (𝓞 ℚ)) (F : T8 → ℤ)
    (y : ℍ[AQ]) : ℤ :=
  if h : ∃ t, y ∈ DC n τ (twoRep v t) then F h.choose else 0

theorem fOf_eq (F : T8 → ℤ)
    (hN : ∀ t t', F t ≠ F t' → twoRep v t ∉ DC n τ (twoRep v t'))
    {y : ℍ[AQ]} {t : T8} (hy : y ∈ DC n τ (twoRep v t)) : fOf n τ v F y = F t := by
  have h : ∃ t, y ∈ DC n τ (twoRep v t) := ⟨t, hy⟩
  rw [fOf, dif_pos h]
  by_contra hne
  exact hN _ _ (Ne.symm hne) (DC_trans h.choose_spec (DC_symm hy))

/-- **The assembly.** -/
theorem testVector_of_partition (hv : IsPlaceTwo v) (F : T8 → ℤ)
    (hS : ∀ x : ℍ[AQ]ˣ, ∃ t, (x : ℍ[AQ]) ∈ DC n τ (twoRep v t))
    (hM : ∀ t t', F t = F t' → twoRep v t ∈ DC n τ (twoRep v t'))
    (hN : ∀ t t', F t ≠ F t' → twoRep v t ∉ DC n τ (twoRep v t'))
    (hsum : ∑ t : T8, F t = 0 ∧ ∑ t : T8, chi0Rep t * F t = 0)
    (hrk : ∀ G : T8 → ℤ, (∀ t t', F t = F t' → G t = G t') → ∑ t : T8, G t = 0 →
      ∑ t : T8, chi0Rep t * G t = 0 → ∃ c : ℤ, ∀ t, G t = c * F t)
    (hne : ∃ t, F t ≠ 0) :
    ∃ f : ℍ[AQ] → ℤ, IsTestVector n τ f ∧ ∃ x : ℍ[AQ]ˣ, f x ≠ 0 := by
  have hval : ∀ t, fOf n τ v F (twoRep v t) = F t := fun t => fOf_eq F hN (mem_DC_self _)
  have hinv : ∀ {x y : ℍ[AQ]}, y ∈ DC n τ x → x ∈ DC n τ y →
      fOf n τ v F y = fOf n τ v F x := by
    intro x y hxy hyx
    classical
    by_cases h : ∃ t, x ∈ DC n τ (twoRep v t)
    · obtain ⟨t, ht⟩ := h
      rw [fOf_eq F hN ht, fOf_eq F hN (DC_trans ht hxy)]
    · have h' : ¬ ∃ t, y ∈ DC n τ (twoRep v t) := fun ⟨t, ht⟩ => h ⟨t, DC_trans ht hyx⟩
      rw [fOf, dif_neg h', fOf, dif_neg h]
  have hplace : ∀ v', IsPlaceTwo v' → v' = v := fun v' hv' =>
    eq_of_Pw_eq (by rw [Pw_eq_two hv', Pw_eq_two hv])
  have hpi : InPiZ n τ (fOf n τ v F) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro γ hγ x
      exact hinv ⟨γ, hγ, 1, Subgroup.one_mem _, by simp⟩
        ⟨γ⁻¹, inv_ne_zero hγ, 1, Subgroup.one_mem _, by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hγ, map_one]; simp⟩
    · intro x u hu
      have hu' : u ∈ HgrpN n τ := Subgroup.subset_closure (Or.inl hu)
      exact hinv ⟨1, one_ne_zero, u, hu', by simp⟩ ⟨1, one_ne_zero, u⁻¹, Subgroup.inv_mem _ hu', by
        rw [map_one, one_mul, mul_assoc, Units.mul_inv, mul_one]⟩
    · intro x z
      have hz : Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom z ∈ HgrpN n τ :=
        Subgroup.subset_closure (Or.inr ⟨z, rfl⟩)
      have e : algebraMap AQ ℍ[AQ] (z : AQ) =
          ((Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom z : ℍ[AQ]ˣ) : ℍ[AQ]) := rfl
      rw [e]
      exact hinv ⟨1, one_ne_zero, _, hz, by simp⟩ ⟨1, one_ne_zero, _, Subgroup.inv_mem _ hz, by
        rw [map_one, one_mul, mul_assoc, Units.mul_inv, mul_one]⟩
    · intro v' hv'
      obtain rfl := hplace v' hv'
      simp only [hval]
      exact hsum
  refine ⟨fOf n τ v F, ⟨hpi, ?_⟩, ?_⟩
  · intro g hg
    set G : T8 → ℤ := fun t => g (twoRep v t)
    have hG : ∀ t t', F t = F t' → G t = G t' := by
      intro t t' h
      exact inPiZ_eq_of_mem_DC hg (x := twoRepU v t') (y := twoRepU v t) (hM t t' h)
    have hg4 := hg.2.2.2 v hv
    obtain ⟨c, hc⟩ := hrk G hG hg4.1 hg4.2
    refine ⟨c, fun x => ?_⟩
    obtain ⟨t, ht⟩ := hS x
    rw [inPiZ_eq_of_mem_DC hg (x := twoRepU v t) ht, fOf_eq F hN ht]
    exact hc t
  · obtain ⟨t, ht⟩ := hne
    exact ⟨twoRepU v t, by rw [twoRepU_coe, hval]; exact ht⟩

end Assembly

end ZInQ.Contrib.HfxProof
