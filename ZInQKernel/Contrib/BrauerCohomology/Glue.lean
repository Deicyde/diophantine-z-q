import ZInQKernel.Contrib.BrauerCohomology.Real
import ZInQKernel.HDecomp.Descent.B2Glue

set_option autoImplicit false

/-!
# From T14/T15 to the descent leaves `LeafHasse` and `LeafLocalTwo`

The B2 glue (`ZInQKernel/HDecomp/Descent/B2Glue.lean`) consumes the Brauer inputs in a third
spelling: `ℂˣ`-valued **sign** cochains (`η x y ^ 2 = 1`), *locally constant* rather than
continuous, at the **finite** places only:

* `GlueDescent.B2Q.LeafHasse`: a sign 2-cocycle on `G_ℚ` that is a coboundary at every finite
  prime is a coboundary;
* `GlueDescent.B2Q.LeafLocalTwo`: two non-trivial sign 2-cocycles on `G_{ℚ_p}` differ by a
  coboundary.

`ofSign : {±1} → ZMod 2` turns sign cochains into the `ZMod 2`-valued cochains of `PkgI6`
(`isCocycle2_signToZMod`, `signCob_iff_isCoboundary2`); locally constant `ℂˣ`-valued maps are
exactly continuous `ZMod 2`-valued maps after this translation, since `ZMod 2` is discrete.
`LeafHasse` follows from T14(a)+(b): reciprocity forces the real place to vanish once all finite
places do (no input at `∞` beyond T14(b) is needed). `LeafLocalTwo` follows from the `p`-adic part
of T15 (every prime, including `p = 2`). Both are derived from the cochain forms and, through
`Galois.lean`, from the bundle forms (the frozen reference targets).
-/

open CategoryTheory PkgI6 GlueDescent.B2 GlueDescent.B2Q

namespace ZInQ.Contrib.BrauerCohomology

section Signs

/-- `{±1} ⊂ ℂˣ → ZMod 2` (`1 ↦ 0`, anything else `↦ 1`). -/
noncomputable def ofSign (u : ℂˣ) : ZMod 2 := by
  classical exact if u = 1 then 0 else 1

/-- `ZMod 2 → {±1} ⊂ ℂˣ`. -/
noncomputable def toSign (a : ZMod 2) : ℂˣ := if a = 0 then 1 else -1

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem neg_one_ne_one_units : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have := congrArg Units.val h
  norm_num at this

theorem sign_cases {u : ℂˣ} (h : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  have h' : (u : ℂ) * u = 1 := by
    have := congrArg Units.val h
    simpa [pow_two] using this
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · exact Or.inl (Units.ext (by simpa using h1))
  · exact Or.inr (Units.ext (by simpa using h1))

@[simp] theorem ofSign_one : ofSign 1 = 0 := by simp [ofSign]

@[simp] theorem ofSign_neg_one : ofSign (-1) = 1 := by
  simp [ofSign]

@[simp] theorem toSign_zero : toSign 0 = 1 := by simp [toSign]

@[simp] theorem toSign_one : toSign 1 = -1 := by
  simp [toSign, show (1 : ZMod 2) ≠ 0 by decide]

theorem toSign_sq (a : ZMod 2) : toSign a ^ 2 = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp

theorem toSign_ofSign {u : ℂˣ} (h : u ^ 2 = 1) : toSign (ofSign u) = u := by
  rcases sign_cases h with rfl | rfl <;> simp

theorem ofSign_mul {u v : ℂˣ} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) :
    ofSign (u * v) = ofSign u + ofSign v := by
  rcases sign_cases hu with rfl | rfl <;> rcases sign_cases hv with rfl | rfl <;>
    simp [zmod2_one_add_one]

theorem ofSign_inv {u : ℂˣ} (hu : u ^ 2 = 1) : ofSign u⁻¹ = ofSign u := by
  rcases sign_cases hu with rfl | rfl <;> simp

theorem sq_inv_eq_one {u : ℂˣ} (hu : u ^ 2 = 1) : u⁻¹ ^ 2 = 1 := by
  rw [inv_pow, hu, inv_one]

theorem sq_mul_eq_one {u v : ℂˣ} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) : (u * v) ^ 2 = 1 := by
  rw [mul_pow, hu, hv, one_mul]

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- The `ZMod 2`-valued cochain of a sign-valued 2-cochain. -/
noncomputable def signToZMod (η : Γ → Γ → ℂˣ) : Γ → Γ → ZMod 2 := fun a b => ofSign (η a b)

/-- A sign 2-cocycle (locally constant, values `±1`) gives a `PkgI6.IsCocycle2`. -/
theorem isCocycle2_signToZMod {η : Γ → Γ → ℂˣ} (hη : IsSignCocycle η) :
    IsCocycle2 (signToZMod η) := by
  refine ⟨(hη.1.comp ofSign).continuous, fun a b c => ?_⟩
  have e := congrArg ofSign (hη.2.2 a b c)
  rw [ofSign_mul (hη.2.1 _ _) (hη.2.1 _ _), ofSign_mul (hη.2.1 _ _) (hη.2.1 _ _)] at e
  simp only [signToZMod]
  revert e
  generalize ofSign (η (a * b) c) = A
  generalize ofSign (η a b) = B
  generalize ofSign (η b c) = C
  generalize ofSign (η a (b * c)) = D
  revert A B C D
  decide

/-- **A sign 2-cochain is a sign coboundary (`SignCob`) iff its `ZMod 2` translate is a
`PkgI6.IsCoboundary2`.** -/
theorem signCob_iff_isCoboundary2 {η : Γ → Γ → ℂˣ} (hη : ∀ x y, η x y ^ 2 = 1) :
    SignCob η ↔ IsCoboundary2 (signToZMod η) := by
  constructor
  · rintro ⟨γ, hγl, hγs, e⟩
    refine ⟨fun x => ofSign (γ x), (hγl.comp ofSign).continuous, fun a b => ?_⟩
    simp only [signToZMod, e a b, dB]
    rw [ofSign_mul (sq_mul_eq_one (hγs a) (hγs b)) (sq_inv_eq_one (hγs _)),
      ofSign_mul (hγs a) (hγs b), ofSign_inv (hγs _)]
    generalize ofSign (γ a) = A
    generalize ofSign (γ b) = B
    generalize ofSign (γ (a * b)) = C
    revert A B C
    decide
  · rintro ⟨f, hf, e⟩
    have hfl : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hf
    refine ⟨fun x => toSign (f x), hfl.comp toSign, fun x => toSign_sq _, fun x y => ?_⟩
    rw [← toSign_ofSign (hη x y)]
    change toSign (signToZMod η x y) = _
    rw [e x y]
    simp only [dB]
    generalize f x = A
    generalize f y = B
    generalize f (x * y) = C
    rcases zmod2_cases A with rfl | rfl <;> rcases zmod2_cases B with rfl | rfl <;>
      rcases zmod2_cases C with rfl | rfl <;> simp [zmod2_one_add_one]

end Signs

section Leaves

/-- **`LeafHasse` from the cochain forms of T14(a), T14(b).** -/
theorem leafHasse_of_cochain (hH : BrauerHasse2C) (hR : BrauerReciprocity2C) : LeafHasse := by
  intro η hη hloc
  have hε : IsCocycle2 (signToZMod η) := isCocycle2_signToZMod hη
  have hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] (signToZMod η)) := by
    intro p hp
    have h := hloc ⟨p, hp.out⟩
    exact (signCob_iff_isCoboundary2 (fun x y => hη.2.1 _ _)).1 h
  have hinf : IsCoboundary2 (resC ℝ (signToZMod η)) := by
    obtain ⟨-, hev⟩ := hR _ hε
    have hempty : {q : Nat.Primes | haveI : Fact (q : ℕ).Prime := ⟨q.2⟩;
        ¬ IsCoboundary2 (resC ℚ_[(q : ℕ)] (signToZMod η))} = ∅ := by
      ext q
      have : Fact (q : ℕ).Prime := ⟨q.2⟩
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun h => h (hp q)
    rw [hempty, Set.ncard_empty, zero_add] at hev
    by_contra hne
    rw [ite_eq_right hne] at hev
    exact Nat.not_even_one hev
  exact (signCob_iff_isCoboundary2 hη.2.1).2 (hH _ hε hinf hp)

/-- **`LeafLocalTwo` from the cochain form of T15 at the primes.** -/
theorem leafLocalTwo_of_cochain
    (hC : ∀ (p : ℕ) [Fact p.Prime], H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])) :
    LeafLocalTwo := by
  intro p η₁ η₂ h₁ h₂ n₁ n₂
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hc := (hC p).2 (signToZMod η₁) (signToZMod η₂) (isCocycle2_signToZMod h₁)
    (isCocycle2_signToZMod h₂) (fun h => n₁ ((signCob_iff_isCoboundary2 h₁.2.1).2 h))
    (fun h => n₂ ((signCob_iff_isCoboundary2 h₂.2.1).2 h))
  have hs : ∀ x y, (η₁ x y * (η₂ x y)⁻¹) ^ 2 = 1 := fun x y =>
    sq_mul_eq_one (h₁.2.1 x y) (sq_inv_eq_one (h₂.2.1 x y))
  rw [signCob_iff_isCoboundary2 hs]
  have heq : signToZMod (fun x y => η₁ x y * (η₂ x y)⁻¹) = signToZMod η₁ - signToZMod η₂ := by
    funext x y
    simp only [signToZMod, Pi.sub_apply]
    rw [ofSign_mul (h₁.2.1 x y) (sq_inv_eq_one (h₂.2.1 x y)), ofSign_inv (h₂.2.1 x y)]
    generalize ofSign (η₁ x y) = A
    generalize ofSign (η₂ x y) = B
    revert A B
    decide
  rw [heq]
  exact hc

/-- **`LeafHasse` from the bundle forms of T14** (`PkgI6.BrauerHasse2`, `PkgI6.BrauerReciprocity2`,
i.e. the frozen reference targets T14a, T14b). -/
theorem leafHasse_of_bundle (hH : BrauerHasse2) (hR : BrauerReciprocity2) : LeafHasse :=
  leafHasse_of_cochain (brauerHasse2_iff.1 hH) (brauerReciprocity2_iff.1 hR)

/-- **`LeafLocalTwo` from the bundle form of T15 at the primes.** -/
theorem leafLocalTwo_of_bundle
    (hC : ∀ (p : ℕ) [Fact p.Prime],
      Nat.card (continuousCohomology 2
        (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) :
          Field.absoluteGaloisGroup ℚ_[p] →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ))) = 2) :
    LeafLocalTwo :=
  leafLocalTwo_of_cochain fun p _ => (natCard_Z2res_eq_two_iff ℚ_[p]).1 (hC p)

/-- **GLUE-01.** The bundle targets T14 (`BrauerHasse2 ∧ BrauerReciprocity2`) and T15
(`LocalH2Card`) imply the two Brauer leaves consumed by the B2 descent glue. -/
theorem glueLeaves_of_T14_T15 (h14 : BrauerHasse2 ∧ BrauerReciprocity2) (h15 : LocalH2Card) :
    LeafHasse ∧ LeafLocalTwo :=
  ⟨leafHasse_of_bundle h14.1 h14.2, leafLocalTwo_of_bundle h15.1⟩

end Leaves

end ZInQ.Contrib.BrauerCohomology
