import ZInQKernel.HDecomp.QM.Leaves
import Mathlib.FieldTheory.Galois.Infinite

/-!
# pi0-x6: the Galois-component core of `π₀(X₆) = 1`

See `docs/research/pi0-x6.md`. §1 (copied from `Field.lean`): an automorphism of `ℚ̄` fixing
`√−3` and moving `i`. §2: the stabilizer of a `ℚ̄`-point under `Aut(ℚ̄/ℚ)` is the fixing group of
its residue field. §3: the core: a Galois-compatible map `c` from `X(ℚ̄)` to any type `S` whose
every value is taken over `0` and over `∞` is constant, given that the fibre over `0` has at most
two points with residue fields `ℚ(i)` and the points over `∞` have residue fields `ℚ(√−3)`.
For `S` the connected components of `X_ℚ̄` this is `π₀(X_ℚ̄) = 1`.
No `sorry`, no `axiom`.
-/

noncomputable section

namespace Pi0X6

/-! ## §1 Galois input -/



local notation "Qb" => AlgebraicClosure ℚ

open Polynomial IntermediateField

theorem not_isSquare_three_int (m : ℤ) : m * m ≠ 3 := by
  intro h
  have h1 : -2 < m := by nlinarith
  have h2 : m < 2 := by nlinarith
  interval_cases m <;> omega

theorem rat_sq_ne_three (q : ℚ) : q * q ≠ 3 := by
  intro h
  have hsq : IsSquare (3 : ℚ) := ⟨q, h.symm⟩
  rw [Rat.isSquare_iff] at hsq
  obtain ⟨⟨m, hm⟩, -⟩ := hsq
  exact not_isSquare_three_int m (by simpa using hm.symm)

/-- `ℚ(√−3)` contains no square root of `−1`. -/
theorem sqrt_neg_one_not_mem (z s : Qb) (hz : z ^ 2 = -1) (hs : s ^ 2 = -3) :
    z ∉ ℚ⟮s⟯ := by
  intro hmem
  have hint : IsIntegral ℚ s := Algebra.IsIntegral.isIntegral s
  let pb := IntermediateField.adjoin.powerBasis hint
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨z, hmem⟩
  have hdim : pb.dim ≤ 2 := by
    rw [IntermediateField.adjoin.powerBasis_dim]
    have hp : (X ^ 2 + C (3 : ℚ)) ≠ 0 := by
      intro h0
      have := congrArg natDegree h0
      rw [natDegree_X_pow_add_C] at this
      simp at this
    have hdvd : minpoly ℚ s ∣ X ^ 2 + C (3 : ℚ) := by
      apply minpoly.dvd
      simp [hs]
    have := natDegree_le_of_dvd hdvd hp
    rwa [natDegree_X_pow_add_C] at this
  have hf1 : f.natDegree ≤ 1 := by omega
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf1
  have hz' : z = (a : Qb) * s + (b : Qb) := by
    have := congrArg Subtype.val hf
    simp only [map_add, map_mul, aeval_C, aeval_X] at this
    rw [this]
    simp [eq_ratCast, pb, IntermediateField.adjoin.powerBasis_gen]
  rw [hz'] at hz
  have key : ((2 * a * b : ℚ) : Qb) * s = ((-1 + 3 * a ^ 2 - b ^ 2 : ℚ) : Qb) := by
    push_cast
    linear_combination hz - (a : Qb) ^ 2 * hs
  by_cases hab : (2 * a * b : ℚ) = 0
  · rw [hab] at key
    simp only [Rat.cast_zero, zero_mul] at key
    have key' : (-1 + 3 * a ^ 2 - b ^ 2 : ℚ) = 0 := by exact_mod_cast key.symm
    rcases mul_eq_zero.1 hab with ha | hb
    · have ha0 : a = 0 := by linarith
      subst ha0; nlinarith [sq_nonneg b]
    · subst hb
      exact rat_sq_ne_three (3 * a) (by nlinarith)
  · set q : ℚ := (-1 + 3 * a ^ 2 - b ^ 2) / (2 * a * b)
    have hsq : s = (q : Qb) := by
      have hne : ((2 * a * b : ℚ) : Qb) ≠ 0 := by exact_mod_cast hab
      rw [show q = (-1 + 3 * a ^ 2 - b ^ 2) / (2 * a * b) from rfl, Rat.cast_div, ← key]
      field_simp
    rw [hsq] at hs
    have : q ^ 2 = -3 := by exact_mod_cast hs
    nlinarith [sq_nonneg q]

/-- **Galois input**: for `z² = −1` and `s² = −3` in `ℚ̄` there is `σ ∈ Aut(ℚ̄/ℚ)` fixing `s` and
moving `z` (so `Gal(ℚ̄/ℚ(√−3)) ⊄ Gal(ℚ̄/ℚ(i))`). -/
theorem exists_fix_moves (z s : Qb) (hz : z ^ 2 = -1) (hs : s ^ 2 = -3) :
    ∃ σ : Qb ≃ₐ[ℚ] Qb, σ s = s ∧ σ z ≠ z := by
  by_contra h
  push Not at h
  apply sqrt_neg_one_not_mem z s hz hs
  rw [← InfiniteGalois.fixedField_fixingSubgroup ℚ⟮s⟯]
  intro σ
  apply h σ.1
  exact σ.2 ⟨s, IntermediateField.mem_adjoin_simple_self ℚ s⟩


/-! ## §2 Stabilizers of `ℚ̄`-points -/

open CategoryTheory AlgebraicGeometry LeafQM LeafQM.AV

variable {X : Over (Spec (CommRingCat.of ℚ))}

/-- `Aut(ℚ̄/ℚ)` acting on `X(ℚ̄)`: `x ↦ x ∘ Spec σ`. -/
def galPt (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) : fieldPt Qbar ⟶ X :=
  fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x

theorem galPt_left (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) :
    (galPt σ x).left = Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ x.left := rfl

/-- If `σ` fixes `F` pointwise it fixes `F`'s generators' adjunction (helper). -/
theorem fixes_adjoin (σ : Qbar ≃ₐ[ℚ] Qbar) (S : Set Qbar) (hS : ∀ z ∈ S, σ z = z) :
    ∀ z ∈ IntermediateField.adjoin ℚ S, σ z = z := by
  have hle : IntermediateField.adjoin ℚ S ≤
      IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : σ ∈ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) z := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hS z hz
    have := (Subgroup.zpowers_le.2 hst) hf
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  intro z hz
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hz) σ (Subgroup.mem_zpowers σ)

/-- The stabilizer of a `ℚ̄`-point of a scheme (as a morphism `Spec ℚ̄ → X`). -/
theorem spec_comp_eq_self_iff {Z : Scheme.{0}} (σ : Qbar ≃ₐ[ℚ] Qbar)
    (y : Spec (CommRingCat.of Qbar) ⟶ Z) :
    Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y = y ↔
      ∀ z ∈ residueImage (X := Z) y, σ z = z := by
  rw [← (Scheme.SpecToEquivOfField Qbar Z).injective.eq_iff, specToEquivOfField_comp]
  set p := Scheme.SpecToEquivOfField Qbar Z y with hp
  constructor
  · intro h z hz
    have h2 : p.2 ≫ CommRingCat.ofHom (σ : Qbar →+* Qbar) = p.2 := by
      have := (Sigma.mk.inj_iff.1 h).2
      exact eq_of_heq this
    refine fixes_adjoin σ _ ?_ z hz
    rintro _ ⟨t, rfl⟩
    exact congrArg (fun g => g.hom t) h2
  · intro h
    have h2 : p.2 ≫ CommRingCat.ofHom (σ : Qbar →+* Qbar) = p.2 := by
      ext t
      exact h _ (IntermediateField.subset_adjoin ℚ _ ⟨t, rfl⟩)
    rw [h2]

/-- **The stabilizer of a `ℚ̄`-point is the fixing group of its residue field**: `σx = x` iff
`σ` fixes `ℚ(x)` (`residueImage`) pointwise. -/
theorem galPt_eq_self_iff (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) :
    galPt σ x = x ↔ ∀ z ∈ residueImage (X := X.left) x.left, σ z = z := by
  have hx : ∀ y y' : fieldPt Qbar ⟶ X, y = y' ↔ y.left = y'.left :=
    fun y y' => ⟨fun h => h ▸ rfl, fun h => Over.OverMorphism.ext h⟩
  rw [hx, galPt_left]
  exact spec_comp_eq_self_iff σ x.left

/-- If `ℚ(x) = ℚ⟮z⟯` then `σx = x ↔ σ z = z`. -/
theorem galPt_eq_self_iff_of_eq_adjoin (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) (z : Qbar)
    (hz : residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {z}) :
    galPt σ x = x ↔ σ z = z := by
  rw [galPt_eq_self_iff, hz]
  constructor
  · intro h; exact h z (IntermediateField.mem_adjoin_simple_self ℚ z)
  · intro h; exact fixes_adjoin σ {z} (by simpa using h)

/-- `π`-values are rational at a `ℚ`-rational value: `π(σx) = σ(π x)`. -/
theorem val_galPt (π : ToP1 X.left) (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) :
    π.val (K := Qbar) (galPt σ x).left = (π.val (K := Qbar) x.left).map (σ : Qbar →+* Qbar) :=
  π.val_comp (σ : Qbar →+* Qbar) x.left

/-! ## §3 The core -/

/-- **The `π₀`-core (glue, compiled).** Let `c : X(ℚ̄) → S` be compatible with `Aut(ℚ̄/ℚ)` (two
points in one class stay in one class after `σ`), and suppose every class contains a point over
`0` and a point over `∞`. Suppose the fibre of `π` over `0` has at most two `ℚ̄`-points, each with
residue field `ℚ⟮z⟯`, `z² = −1`, and every point over `∞` has residue field `ℚ⟮s⟯`, `s² = −3`.
Then `S` has at most one element.

Application (docs/research/pi0-x6.md §3): `S = π₀(X_ℚ̄)`, `c x` = the component of `x`; the
residue fields come from `R5ptProps` (`k = ℚ(i)`, `ℚ(√−3)`), the count from `R5fpCount`
(`#CM(ℤ[i]) = 2`). -/
theorem subsingleton_of_galois (π : ToP1 X.left) {S : Type*} (c : (fieldPt Qbar ⟶ X) → S)
    (hc : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x x' : fieldPt Qbar ⟶ X), c x = c x' →
      c (galPt σ x) = c (galPt σ x'))
    (h0 : ∀ t : S, ∃ x : fieldPt Qbar ⟶ X, c x = t ∧ π.val (K := Qbar) x.left = OnePoint.some 0)
    (hinf : ∀ t : S, ∃ y : fieldPt Qbar ⟶ X, c y = t ∧ π.val (K := Qbar) y.left = OnePoint.infty)
    (hcount : ∀ x x' x'' : fieldPt Qbar ⟶ X, π.val (K := Qbar) x.left = OnePoint.some 0 →
      π.val (K := Qbar) x'.left = OnePoint.some 0 → π.val (K := Qbar) x''.left = OnePoint.some 0 →
      x = x' ∨ x = x'' ∨ x' = x'')
    (hres0 : ∀ x : fieldPt Qbar ⟶ X, π.val (K := Qbar) x.left = OnePoint.some 0 →
      ∃ z : Qbar, z ^ 2 = -1 ∧ residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {z})
    (hresinf : ∀ y : fieldPt Qbar ⟶ X, π.val (K := Qbar) y.left = OnePoint.infty →
      ∃ s : Qbar, s ^ 2 = -3 ∧ residueImage (X := X.left) y.left = IntermediateField.adjoin ℚ {s}) :
    Subsingleton S := by
  refine ⟨fun t₁ t₂ => ?_⟩
  obtain ⟨x₁, rfl, hx₁⟩ := h0 t₁
  obtain ⟨x₂, rfl, hx₂⟩ := h0 t₂
  obtain ⟨y, hy, hyv⟩ := hinf (c x₁)
  obtain ⟨z, hz, hzr⟩ := hres0 x₁ hx₁
  obtain ⟨s, hs, hsr⟩ := hresinf y hyv
  obtain ⟨σ, hσs, hσz⟩ := exists_fix_moves z s hz hs
  have hσy : galPt σ y = y := (galPt_eq_self_iff_of_eq_adjoin σ y s hsr).2 hσs
  have hσx : galPt σ x₁ ≠ x₁ := fun h => hσz ((galPt_eq_self_iff_of_eq_adjoin σ x₁ z hzr).1 h)
  have hv : π.val (K := Qbar) (galPt σ x₁).left = OnePoint.some 0 := by
    rw [val_galPt, hx₁]; simp
  rcases hcount x₁ x₂ (galPt σ x₁) hx₁ hx₂ hv with h | h | h
  · rw [h]
  · exact (hσx h.symm).elim
  · have := hc σ y x₁ hy
    rw [hσy, ← h] at this
    rw [← hy, this]

end Pi0X6

#print axioms Pi0X6.exists_fix_moves
#print axioms Pi0X6.galPt_eq_self_iff
#print axioms Pi0X6.subsingleton_of_galois
