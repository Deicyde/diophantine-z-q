import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Descent.B1Quat
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# pi0-x6: `π₀(X₆) = 1` from the bundle's clauses, modulo exact CM and algebraic geometry

See `docs/research/pi0-x6.md`.
* §1-§4: the Galois input, stabilizers of `ℚ̄`-points, the core `subsingleton_of_galois`, and
  its hypotheses from `R5ptProps`, `R5fpCount` (`subsingleton_of_bundle`).
* §5: the closed facts for `ℚ(i) = ℚ(ζ₄)`.
* §6: the closed facts for `ℚ(√−3) = ℚ(ζ₃)`.
* §7: the exact-CM clause `R2X6CMExact` (input (c), option c1), the Galois action on
  `X_ℚ̄` and the proved compatibility `compOf_galois`, the algebraic-geometry inputs `AGInputs`
  (input (d) minus Galois compatibility; unproved glue), and the final theorem
  `r1pi0Props_of_bundle : R5ptProps → R5fpCount → R2X6CMExact → AGInputs → R1pi0Props`.
No `sorry`, no `axiom`.
-/

noncomputable section

namespace AGIn

section CoreSec


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

/-! ## §4 The hypotheses of the core from the bundle's clauses `R5ptProps`, `R5fpCount`

The concrete facts about `ℚ(i)` and `ℚ(√−3)` (`inertCount6 = 1`, `#Pic 𝒪 = 1`, conductor 1) are
hypotheses here (closed number-theoretic facts, glue not done). "CM by `R`" at the points over a
branch value is the hypothesis `hexact` (`com ≅ R`; the bundle's `HasCM4` only gives `φ² = −1`
in `com`). -/

variable {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}

/-- A degree-2 subfield of `ℚ̄` receiving `k ∋ w`, `w² = d` non-square, is `ℚ⟮z⟯`, `z² = d`. -/
theorem eq_adjoin_of_finrank_two (F : IntermediateField ℚ Qbar) (hdeg : Module.finrank ℚ F = 2)
    (k : Type) [Field k] [Algebra ℚ k] (φ : k →ₐ[ℚ] F) (w : k) (d : ℚ) (hw : w ^ 2 = (d : k))
    (hd : ¬ IsSquare d) :
    ∃ z : Qbar, z ^ 2 = (d : Qbar) ∧ F = IntermediateField.adjoin ℚ {z} := by
  have hz : ((φ w : F) : Qbar) ^ 2 = (d : Qbar) := by
    have h1 : φ (w ^ 2) = φ (d : k) := by rw [hw]
    rw [map_pow, map_ratCast] at h1
    have h2 := congrArg (fun t : F => (t : Qbar)) h1
    simpa using h2
  refine ⟨(φ w : Qbar), hz, ?_⟩
  have : FiniteDimensional ℚ F := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  have hle : IntermediateField.adjoin ℚ {(φ w : Qbar)} ≤ F :=
    IntermediateField.adjoin_simple_le_iff.2 (φ w).2
  symm
  refine IntermediateField.eq_of_le_of_finrank_le hle ?_
  rw [hdeg]
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(φ w : Qbar)}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  have hpos : 0 < Module.finrank ℚ (IntermediateField.adjoin ℚ {(φ w : Qbar)}) :=
    Module.finrank_pos
  have hne : Module.finrank ℚ (IntermediateField.adjoin ℚ {(φ w : Qbar)}) ≠ 1 := by
    intro h1
    rw [IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff,
      IntermediateField.mem_bot] at h1
    obtain ⟨q, hq⟩ := h1
    apply hd
    refine ⟨q, ?_⟩
    rw [← hq, eq_ratCast] at hz
    have : ((q * q : ℚ) : Qbar) = (d : Qbar) := by push_cast; rw [← hz]; ring
    exact (Rat.cast_injective this).symm
  omega

/-- **Residue fields from `R5ptProps`.** If `b(k) = 1`, `#Pic R = 1` and `k = ℚ(w)` with
`w² = d` (`d` not a square), a `ℚ̄`-point of `X₆` with `com ≅ R` has residue field `ℚ⟮z⟯`,
`z² = d`. -/
theorem residue_eq_adjoin_of_R5pt (h5 : R5ptProps X Ψ)
    (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k]
    (hk : Module.finrank ℚ k = 2) (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (conductor R) 6) (hb : inertCount6 k = 1)
    (hh : Nat.card (CommRing.Pic R) = 1) (w : k) (d : ℚ) (hw : w ^ 2 = (d : k))
    (hd : ¬ IsSquare d) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar) (hP : Ψ x = Quotient.mk _ P)
    (hRP : Nonempty (com P.q ≃+* R)) :
    ∃ z : Qbar, z ^ 2 = (d : Qbar) ∧
      residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {z} := by
  obtain ⟨hdeg, hemb⟩ := h5 k hk R hR hc x P hP hRP
  rw [hb, hh] at hdeg
  simp only [one_ne_zero, ite_false, mul_one] at hdeg
  obtain ⟨φ⟩ := hemb (by rw [hb]; exact one_ne_zero)
  exact eq_adjoin_of_finrank_two _ hdeg k φ w d hw hd

/-- **At most two points over a value, from `R5fpCount`.** If every `ℚ̄`-point over `t` has
`com ≅ R` (`hexact`) with `b(k) = 1` and `#Pic R = 1`, there are at most `2^1·1 = 2` of them. -/
theorem fibre_le_two_of_R5count (hcnt : R5fpCount) (π : ToP1 X.left) (t : OnePoint Qbar)
    (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k]
    (hk : Module.finrank ℚ k = 2) (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (conductor R) 6) (hb : inertCount6 k = 1)
    (hh : Nat.card (CommRing.Pic R) = 1)
    (hexact : ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
      π.val (K := Qbar) x.left = t → Nonempty (com P.q ≃+* R))
    (x x' x'' : fieldPt Qbar ⟶ X) (h : π.val (K := Qbar) x.left = t)
    (h' : π.val (K := Qbar) x'.left = t) (h'' : π.val (K := Qbar) x''.left = t) :
    x = x' ∨ x = x'' ∨ x' = x'' := by
  have hm : ∀ y : fieldPt Qbar ⟶ X, π.val (K := Qbar) y.left = t →
      ∃ P : QMPair Qbar, Quotient.mk _ P = Ψ y ∧ Nonempty (com P.q ≃+* R) := fun y hy =>
    ⟨(Ψ y).out, Quotient.out_eq _, hexact y _ (Quotient.out_eq _).symm hy⟩
  have hcard := hcnt k hk R hR hc (by
    obtain ⟨P, -, hP⟩ := hm x h
    exact ⟨P, hP⟩)
  rw [hb, hh] at hcard
  norm_num at hcard
  let T := {c : Quotient (pairSetoid Qbar) //
    ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)}
  have hT : Nat.card T = 2 := hcard
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  let e := Finite.equivFin T
  let a : T := ⟨Ψ x, hm x h⟩
  let b : T := ⟨Ψ x', hm x' h'⟩
  let c : T := ⟨Ψ x'', hm x'' h''⟩
  have ha := (e a).isLt
  have hb' := (e b).isLt
  have hc' := (e c).isLt
  have key : (e a).val = (e b).val ∨ (e a).val = (e c).val ∨ (e b).val = (e c).val := by omega
  rcases key with k1 | k1 | k1
  · exact Or.inl (Ψ.injective (congrArg Subtype.val (e.injective (Fin.ext k1))))
  · exact Or.inr (Or.inl (Ψ.injective (congrArg Subtype.val (e.injective (Fin.ext k1)))))
  · exact Or.inr (Or.inr (Ψ.injective (congrArg Subtype.val (e.injective (Fin.ext k1)))))

/-- **`π₀`-core from the bundle's clauses (glue, compiled).** `R5ptProps` and `R5fpCount` at
`k₄ = ℚ(i)` (`R₄ = ℤ[i]`) and `k₃ = ℚ(√−3)` (`R₃ = ℤ[ζ₃]`), with the closed facts about these
two fields as hypotheses, and "CM exactly by `R₄` over `0`, by `R₃` over `∞`" (`hexact₄`,
`hexact₃`): every Galois-compatible map `c` whose classes all meet the fibres over `0` and `∞`
is constant. With `S = π₀(X_ℚ̄)` (the algebraic-geometry inputs `hc`, `h0`, `hinf`) this is
`π₀(X₆_ℚ̄) = 1`. -/
theorem subsingleton_of_bundle (h5 : R5ptProps X Ψ) (hcnt : R5fpCount) (π : ToP1 X.left)
    (k₄ : Type) [Field k₄] [NumberField k₄] [NumberField.IsTotallyComplex k₄]
    (hk₄ : Module.finrank ℚ k₄ = 2) (R₄ : Subring k₄)
    (hR₄ : R₄ ≤ (integralClosure ℤ k₄).toSubring) (hc₄ : Nat.Coprime (conductor R₄) 6)
    (hb₄ : inertCount6 k₄ = 1) (hh₄ : Nat.card (CommRing.Pic R₄) = 1) (i₄ : k₄)
    (hi₄ : i₄ ^ 2 = ((-1 : ℚ) : k₄))
    (k₃ : Type) [Field k₃] [NumberField k₃] [NumberField.IsTotallyComplex k₃]
    (hk₃ : Module.finrank ℚ k₃ = 2) (R₃ : Subring k₃)
    (hR₃ : R₃ ≤ (integralClosure ℤ k₃).toSubring) (hc₃ : Nat.Coprime (conductor R₃) 6)
    (hb₃ : inertCount6 k₃ = 1) (hh₃ : Nat.card (CommRing.Pic R₃) = 1) (s₃ : k₃)
    (hs₃ : s₃ ^ 2 = ((-3 : ℚ) : k₃))
    (hexact₄ : ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
      π.val (K := Qbar) x.left = OnePoint.some 0 → Nonempty (com P.q ≃+* R₄))
    (hexact₃ : ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
      π.val (K := Qbar) x.left = OnePoint.infty → Nonempty (com P.q ≃+* R₃))
    {S : Type*} (c : (fieldPt Qbar ⟶ X) → S)
    (hc : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x x' : fieldPt Qbar ⟶ X), c x = c x' →
      c (galPt σ x) = c (galPt σ x'))
    (h0 : ∀ t : S, ∃ x : fieldPt Qbar ⟶ X, c x = t ∧ π.val (K := Qbar) x.left = OnePoint.some 0)
    (hinf : ∀ t : S, ∃ y : fieldPt Qbar ⟶ X, c y = t ∧
      π.val (K := Qbar) y.left = OnePoint.infty) :
    Subsingleton S := by
  have hsq1 : ¬ IsSquare (-1 : ℚ) := by
    rintro ⟨q, hq⟩; nlinarith [mul_self_nonneg q]
  have hsq3 : ¬ IsSquare (-3 : ℚ) := by
    rintro ⟨q, hq⟩; nlinarith [mul_self_nonneg q]
  refine subsingleton_of_galois π c hc h0 hinf
    (fun x x' x'' h h' h'' => fibre_le_two_of_R5count hcnt π _ k₄ hk₄ R₄ hR₄ hc₄ hb₄ hh₄
      hexact₄ x x' x'' h h' h'') (fun x hx => ?_) (fun y hy => ?_)
  · obtain ⟨z, hz, hzr⟩ := residue_eq_adjoin_of_R5pt h5 k₄ hk₄ R₄ hR₄ hc₄ hb₄ hh₄ i₄ (-1) hi₄
      hsq1 x _ (Quotient.out_eq _).symm (hexact₄ x _ (Quotient.out_eq _).symm hx)
    exact ⟨z, by rw [hz]; push_cast; ring, hzr⟩
  · obtain ⟨s, hs, hsr⟩ := residue_eq_adjoin_of_R5pt h5 k₃ hk₃ R₃ hR₃ hc₃ hb₃ hh₃ s₃ (-3) hs₃
      hsq3 y _ (Quotient.out_eq _).symm (hexact₃ y _ (Quotient.out_eq _).symm hy)
    exact ⟨s, by rw [hs]; push_cast; ring, hsr⟩


end CoreSec

/-! ## §5 Closed facts for `ℚ(i)` -/

section QiSec


open NumberField LeafQM LeafQM.AV

/-! ## The closed facts for `k₄ = ℚ(i) = ℚ(ζ₄)` -/

abbrev K4 := CyclotomicField 4 ℚ

instance : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {4} ℚ K4 := CyclotomicField.isCyclotomicExtension 4 ℚ

theorem hζ4 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 4 ℚ K4) 4 :=
  IsCyclotomicExtension.zeta_spec 4 ℚ K4

theorem zeta4_sq : (IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 = -1 := by
  have h := hζ4.pow_eq_one
  have h2 : (IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 ≠ 1 := by
    intro h2
    have := hζ4.pow_eq_one_iff_dvd 2
    rw [this] at h2
    norm_num at h2
  have : ((IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 - 1) *
      ((IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 this with h3 | h3
  · exact (h2 (sub_eq_zero.1 h3)).elim
  · exact eq_neg_of_add_eq_zero_left h3

instance : NumberField.IsTotallyComplex K4 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) K4 (by norm_num)

theorem finrank_K4 : Module.finrank ℚ K4 = 2 := by
  rw [IsCyclotomicExtension.finrank K4 (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

/-- `i := ζ₄ ∈ 𝓞 ℚ(ζ₄)`, with `i² = −1`. -/
def iInt : 𝓞 K4 := hζ4.toInteger

theorem alg_iInt : algebraMap (𝓞 K4) K4 iInt = IsCyclotomicExtension.zeta 4 ℚ K4 := rfl

theorem iInt_mul_self : iInt * iInt = ((-1 : ℤ) : 𝓞 K4) := by
  apply RingOfIntegers.coe_injective
  rw [map_mul, alg_iInt, map_intCast]; push_cast; rw [← pow_two, zeta4_sq]

/-- `ℤ[i] → 𝓞 ℚ(ζ₄)`, `a + bi ↦ a + bζ₄`. -/
def gaussToO : GaussianInt →+* 𝓞 K4 := Zsqrtd.lift ⟨iInt, iInt_mul_self⟩

theorem gaussToO_apply (z : GaussianInt) :
    gaussToO z = (z.re : 𝓞 K4) + (z.im : 𝓞 K4) * iInt := by
  simp [gaussToO, Zsqrtd.lift]

theorem gaussToO_bijective : Function.Bijective gaussToO := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    rw [gaussToO_apply] at hz
    have hK := congrArg (algebraMap (𝓞 K4) K4) hz
    rw [map_add, map_mul, alg_iInt, map_intCast, map_intCast, map_zero] at hK
    have him : z.im = 0 := by
      by_contra hb
      have hb' : ((z.im : ℚ) : K4) ≠ 0 := by exact_mod_cast hb
      have hζ : IsCyclotomicExtension.zeta 4 ℚ K4 = ((-(z.re : ℚ) / z.im : ℚ) : K4) := by
        push_cast
        field_simp
        linear_combination hK
      have := zeta4_sq
      rw [hζ] at this
      have h' : ((-(z.re : ℚ) / z.im) ^ 2 : ℚ) = -1 := by exact_mod_cast this
      nlinarith [sq_nonneg (-(z.re : ℚ) / z.im)]
    have hre : z.re = 0 := by
      rw [him] at hK
      simp at hK
      exact_mod_cast hK
    exact Zsqrtd.ext hre him
  · intro y
    let pb := hζ4.integralPowerBasis
    obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval y
    have hdim : pb.dim = 2 := by
      simp only [pb, IsPrimitiveRoot.integralPowerBasis_dim]; decide
    have hf1 : f.natDegree ≤ 1 := by omega
    obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hf1
    refine ⟨⟨b, a⟩, ?_⟩
    rw [gaussToO_apply, hf]
    simp only [map_add, map_mul, Polynomial.aeval_X,
      IsPrimitiveRoot.integralPowerBasis_gen, pb, iInt, eq_intCast, map_intCast]
    ring

/-- `ℤ[i] ≃ 𝓞 ℚ(ζ₄)`. -/
def gaussEquiv : GaussianInt ≃+* 𝓞 K4 := RingEquiv.ofBijective gaussToO gaussToO_bijective

theorem gaussEquiv_natCast (n : ℕ) : gaussEquiv (n : GaussianInt) = (n : 𝓞 K4) := map_natCast _ n

theorem prime_three_O4 : Prime (3 : 𝓞 K4) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 3).2 (by norm_num)
  have := (MulEquiv.prime_iff gaussEquiv.toMulEquiv).2 h
  have e3 : gaussEquiv.toMulEquiv ((3 : ℕ) : GaussianInt) = (3 : 𝓞 K4) := by
    change gaussEquiv ((3 : ℕ) : GaussianInt) = 3
    rw [map_natCast]; norm_num
  rwa [e3] at this

theorem not_prime_two_O4 : ¬ Prime (2 : 𝓞 K4) := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  intro h2
  have h := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 2).1
  have : Prime ((2 : ℕ) : GaussianInt) := by
    have := (MulEquiv.prime_iff gaussEquiv.symm.toMulEquiv).2 h2
    have e2 : gaussEquiv.symm.toMulEquiv (2 : 𝓞 K4) = ((2 : ℕ) : GaussianInt) := by
      change gaussEquiv.symm 2 = _
      rw [map_ofNat]; norm_num
    rwa [e2] at this
  have := h this
  norm_num at this

theorem inertCount6_K4 : inertCount6 K4 = 1 := by
  unfold inertCount6
  have h2 : ¬ (Ideal.span {(2 : 𝓞 K4)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact not_prime_two_O4
  have h3 : (Ideal.span {(3 : 𝓞 K4)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact prime_three_O4
  simp [h2, h3]

/-- `R₄ = 𝓞 ℚ(ζ₄)` as a subring. -/
abbrev R4 : Subring K4 := (integralClosure ℤ K4).toSubring

theorem conductor_R4 : conductor R4 = 1 := AddSubgroup.relIndex_self _

theorem pic_R4 : Nat.card (CommRing.Pic R4) = 1 := by
  have e : GaussianInt ≃+* R4 := gaussEquiv.trans (RingEquiv.refl _)
  have : IsPrincipalIdealRing R4 := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have : Subsingleton (CommRing.Pic R4) := inferInstance
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

theorem zeta4_sq' : (IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 = (((-1 : ℚ)) : K4) := by
  rw [zeta4_sq]; push_cast; ring


end QiSec

/-! ## §6 Closed facts for `ℚ(√−3)` -/

section Q3Sec


open NumberField LeafQM LeafQM.AV

/-! ## The closed facts for `k₃ = ℚ(√−3) = ℚ(ζ₃)` -/

abbrev K3 := CyclotomicField 3 ℚ

instance : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ

theorem hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K3) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K3

local notation "ζ₃" => IsCyclotomicExtension.zeta 3 ℚ K3

theorem zeta3_sq : ζ₃ ^ 2 + ζ₃ + 1 = 0 := by
  have h := hζ3.pow_eq_one
  have h1 : ζ₃ ≠ 1 := hζ3.ne_one (by norm_num)
  have : (ζ₃ - 1) * (ζ₃ ^ 2 + ζ₃ + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h3 | h3
  · exact (h1 (sub_eq_zero.1 h3)).elim
  · exact h3

instance : NumberField.IsTotallyComplex K3 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) K3 (by norm_num)

theorem finrank_K3 : Module.finrank ℚ K3 = 2 := by
  rw [IsCyclotomicExtension.finrank K3 (Polynomial.cyclotomic.irreducible_rat (n := 3) (by norm_num))]
  decide

/-- `√−3 = 2ζ₃ + 1`. -/
theorem sqrt3_sq : (2 * ζ₃ + 1) ^ 2 = (((-3 : ℚ)) : K3) := by
  push_cast; linear_combination 4 * zeta3_sq

/-- `ζ₃ ∈ 𝓞 ℚ(ζ₃)`. -/
def zInt : 𝓞 K3 := hζ3.toInteger

theorem alg_zInt : algebraMap (𝓞 K3) K3 zInt = ζ₃ := rfl

theorem zInt_sq : zInt ^ 2 = -zInt - 1 := by
  apply RingOfIntegers.coe_injective
  rw [map_pow, map_sub, map_neg, map_one, alg_zInt]
  linear_combination zeta3_sq

/-- `1, ζ₃` are independent over `ℤ`. -/
theorem coord_eq_zero (a b : ℤ) (h : (a : 𝓞 K3) + (b : 𝓞 K3) * zInt = 0) : a = 0 ∧ b = 0 := by
  have hK := congrArg (algebraMap (𝓞 K3) K3) h
  rw [map_add, map_mul, alg_zInt, map_intCast, map_intCast, map_zero] at hK
  have hb : b = 0 := by
    by_contra hb
    have hb' : ((b : ℚ) : K3) ≠ 0 := by exact_mod_cast hb
    have hζ : ζ₃ = ((-(a : ℚ) / b : ℚ) : K3) := by
      push_cast
      field_simp
      linear_combination hK
    have := zeta3_sq
    rw [hζ] at this
    have h' : ((-(a : ℚ) / b) ^ 2 + (-(a : ℚ) / b) + 1 : ℚ) = 0 := by exact_mod_cast this
    nlinarith [sq_nonneg (-(a : ℚ) / b + 1 / 2)]
  refine ⟨?_, hb⟩
  rw [hb] at hK
  simp at hK
  exact_mod_cast hK

/-- Every element of `𝓞 ℚ(ζ₃)` is `a + bζ₃`. -/
theorem exists_coord (y : 𝓞 K3) : ∃ a b : ℤ, y = (a : 𝓞 K3) + (b : 𝓞 K3) * zInt := by
  let pb := hζ3.integralPowerBasis
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval y
  have hdim : pb.dim = 2 := by
    simp only [pb, IsPrimitiveRoot.integralPowerBasis_dim]; decide
  have hf1 : f.natDegree ≤ 1 := by omega
  obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hf1
  refine ⟨b, a, ?_⟩
  rw [hf]
  simp only [map_add, map_mul, Polynomial.aeval_X,
    IsPrimitiveRoot.integralPowerBasis_gen, pb, zInt, eq_intCast, map_intCast]
  ring

theorem coord_eq (a b c d : ℤ)
    (h : (a : 𝓞 K3) + (b : 𝓞 K3) * zInt = (c : 𝓞 K3) + (d : 𝓞 K3) * zInt) : a = c ∧ b = d := by
  have := coord_eq_zero (a - c) (b - d) (by push_cast; linear_combination h)
  omega

theorem dvd_iff_coord (n a b : ℤ) :
    (n : 𝓞 K3) ∣ (a : 𝓞 K3) + (b : 𝓞 K3) * zInt ↔ n ∣ a ∧ n ∣ b := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, d, rfl⟩ := exists_coord y
    have := coord_eq a b (n * c) (n * d) (by rw [hy]; push_cast; ring)
    exact ⟨⟨c, this.1⟩, ⟨d, this.2⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    exact ⟨(c : 𝓞 K3) + (d : 𝓞 K3) * zInt, by push_cast; ring⟩

theorem not_prime_three_O3 : ¬ Prime (3 : 𝓞 K3) := by
  intro h
  -- `λ = ζ − 1`, `λ² = −3ζ`
  have hl : (3 : 𝓞 K3) ∣ (zInt - 1) * (zInt - 1) :=
    ⟨-zInt, by linear_combination zInt_sq⟩
  have h1 := h.dvd_or_dvd hl
  have h2 : ¬ ((3 : ℤ) : 𝓞 K3) ∣ ((-1 : ℤ) : 𝓞 K3) + ((1 : ℤ) : 𝓞 K3) * zInt := by
    rw [dvd_iff_coord]; omega
  apply h2
  have e : ((-1 : ℤ) : 𝓞 K3) + ((1 : ℤ) : 𝓞 K3) * zInt = zInt - 1 := by push_cast; ring
  rw [e]
  rcases h1 with h1 | h1 <;> exact_mod_cast h1

theorem parity_lemma : ∀ a b c d : ZMod 2, a * c - b * d = 0 → a * d + b * c - b * d = 0 →
    (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0) := by decide

theorem prime_two_O3 : Prime (2 : 𝓞 K3) := by
  refine ⟨two_ne_zero, ?_, ?_⟩
  · intro hu
    have : ((2 : ℤ) : 𝓞 K3) ∣ ((1 : ℤ) : 𝓞 K3) + ((0 : ℤ) : 𝓞 K3) * zInt := by
      have : (2 : 𝓞 K3) ∣ 1 := hu.dvd
      push_cast; simpa using this
    rw [dvd_iff_coord] at this; omega
  · intro x y hxy
    obtain ⟨a, b, rfl⟩ := exists_coord x
    obtain ⟨c, d, rfl⟩ := exists_coord y
    have hprod : ((a : 𝓞 K3) + (b : 𝓞 K3) * zInt) * ((c : 𝓞 K3) + (d : 𝓞 K3) * zInt) =
        ((a * c - b * d : ℤ) : 𝓞 K3) + ((a * d + b * c - b * d : ℤ) : 𝓞 K3) * zInt := by
      push_cast; linear_combination (b : 𝓞 K3) * d * zInt_sq
    rw [hprod, show (2 : 𝓞 K3) = ((2 : ℤ) : 𝓞 K3) by norm_num, dvd_iff_coord] at hxy
    rw [show (2 : 𝓞 K3) = ((2 : ℤ) : 𝓞 K3) by norm_num, dvd_iff_coord, dvd_iff_coord]
    obtain ⟨h1, h2⟩ := hxy
    have e : ∀ n : ℤ, (2 : ℤ) ∣ n ↔ ((n : ZMod 2) = 0) := fun n => by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num
    simp only [e] at h1 h2 ⊢
    push_cast at h1 h2
    exact parity_lemma _ _ _ _ h1 h2

theorem inertCount6_K3 : inertCount6 K3 = 1 := by
  unfold inertCount6
  have h2 : (Ideal.span {(2 : 𝓞 K3)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact prime_two_O3
  have h3 : ¬ (Ideal.span {(3 : 𝓞 K3)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact not_prime_three_O3
  simp [h2, h3]

/-- `R₃ = 𝓞 ℚ(ζ₃)` as a subring. -/
abbrev R3 : Subring K3 := (integralClosure ℤ K3).toSubring

theorem conductor_R3 : conductor R3 = 1 := AddSubgroup.relIndex_self _

theorem pic_R3 : Nat.card (CommRing.Pic R3) = 1 := by
  have e : 𝓞 K3 ≃+* R3 := RingEquiv.refl _
  have : IsPrincipalIdealRing (𝓞 K3) := IsCyclotomicExtension.Rat.three_pid K3
  have : IsPrincipalIdealRing R3 := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have : Subsingleton (CommRing.Pic R3) := inferInstance
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩


end Q3Sec

/-! ## §7 The exact-CM clause, the algebraic-geometry inputs, and the final theorem -/

section Final

open CategoryTheory AlgebraicGeometry Limits NumberField LeafQM LeafQM.AV

variable {X : Over (Spec (CommRingCat.of ℚ))}

/-- **R2's CM clauses at `0` and `∞` with "CM by `R`" in its printed meaning** (`End_𝒪(A) ≅ R`,
not merely `φ ∈ com` with `φ² = −1`): a `ℚ̄`-point lies over `0` iff its pair has `com ≅ ℤ[i]`,
and over `∞` iff `com ≅ ℤ[ζ₃]`. *Published*: Baba–Granath 2008 Thm 2.1 and the §3.1 table (the
fibres over `0`, `∞` are the CM points of discriminants `−4`, `−3`), as for `R2X6PropsIff`; a
consequence of the same statement. Only the forward directions are used. -/
def R2X6CMExact (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (π₆ : ToP1 X.left) : Prop :=
  ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
    (π₆.val (K := Qbar) x.left = OnePoint.some 0 ↔ Nonempty (com P.q ≃+* R4)) ∧
    (π₆.val (K := Qbar) x.left = OnePoint.infty ↔ Nonempty (com P.q ≃+* R3))

/-- `X_ℚ̄ = X ×_ℚ Spec ℚ̄`. -/
abbrev Xbar (X : Over (Spec (CommRingCat.of ℚ))) : Scheme :=
  pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

/-- The section `Spec ℚ̄ → X_ℚ̄` of a morphism `y : Spec ℚ̄ → X` over `ℚ`. -/
def secOf (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (w : y ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) :
    Spec (CommRingCat.of Qbar) ⟶ Xbar X :=
  pullback.lift y (𝟙 _) (by rw [w, Category.id_comp])

/-- The point of `Spec ℚ̄`. -/
def ptQ : Spec (CommRingCat.of Qbar) := (IsLocalRing.closedPoint Qbar : PrimeSpectrum Qbar)

/-- The point of `X_ℚ̄` of a `ℚ̄`-point `x` (the image of the section `(x, id)`). -/
def ptOf (x : fieldPt Qbar ⟶ X) : Xbar X :=
  secOf x.left (Over.w x) ptQ

/-- The connected component of `X_ℚ̄` containing the point of `x`. -/
def compOf (x : fieldPt Qbar ⟶ X) : _root_.ConnectedComponents (Xbar X) :=
  _root_.ConnectedComponents.mk (ptOf x)

/-- `σ ∈ Aut(ℚ̄/ℚ)` acting on `X_ℚ̄ = X ×_ℚ Spec ℚ̄` through the second factor (`id × Spec σ⁻¹`). -/
def galXbar (σ : Qbar ≃ₐ[ℚ] Qbar) : Xbar X ⟶ Xbar X :=
  pullback.map X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) (𝟙 _)
    (Spec.map (CommRingCat.ofHom ((σ.symm : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar))) (𝟙 _)
    (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext q
      simp)

theorem specMap_sigma_comp_symm (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom ((σ.symm : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : ((σ : Qbar →+* Qbar)).comp ((σ.symm : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar) =
      RingHom.id Qbar := by
    ext q; simp
  rw [this]
  exact Spec.map_id _

theorem secOf_comp (σ : Qbar ≃ₐ[ℚ] Qbar) (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (w : y ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
    (w' : (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) :
    secOf (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y) w' =
      Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ secOf y w ≫ galXbar σ := by
  apply pullback.hom_ext
  · simp only [secOf, galXbar, Category.assoc, pullback.lift_fst, pullback.map,
      Category.comp_id]
  · simp only [secOf, galXbar, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      pullback.map, Category.id_comp]
    rw [specMap_sigma_comp_symm]

theorem secOf_galois_apply (σ : Qbar ≃ₐ[ℚ] Qbar) (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (w : y ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
    (w' : (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))) :
    secOf (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y) w'
        ptQ =
      galXbar σ (secOf y w ptQ) := by
  rw [secOf_comp σ y w w', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  congr 2
  exact Subsingleton.elim _ _

/-- **The Galois action on `X(ℚ̄)` is the action on `X_ℚ̄`**: `pt(σ · x) = galXbar σ (pt x)`. -/
theorem ptOf_galPt (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) :
    ptOf (galPt σ x) = galXbar σ (ptOf x) :=
  secOf_galois_apply σ x.left (Over.w x) (Over.w (galPt σ x))

theorem compOf_galois (σ : Qbar ≃ₐ[ℚ] Qbar) (x x' : fieldPt Qbar ⟶ X)
    (h : compOf x = compOf x') : compOf (galPt σ x) = compOf (galPt σ x') := by
  unfold compOf at *
  rw [ptOf_galPt, ptOf_galPt, ← (galXbar σ).continuous.connectedComponentsMap_mk,
    ← (galXbar σ).continuous.connectedComponentsMap_mk, h]

/-- **The algebraic-geometry inputs (input (d) of docs/research/pi0-x6.md §2; glue, NOT proved,
Mathlib v4.35 lacks the theory).** For `X₆` with `π₆`:
(the Galois compatibility of components is NOT an input: it is proved, `compOf_galois`);
(i)-(ii) every connected component of `X_ℚ̄` contains a `ℚ̄`-point over `0` and one over `∞`
(components are smooth proper irreducible curves over `ℚ̄`; `π₆` is nonconstant on each since its
fibres are finite twist orbits, `Aut(𝒪)/Inn(𝒪^×) ≅ (ℤ/2)²`; the image is closed, irreducible, not
a point, hence `P¹`; closed points are `ℚ̄`-points);
(iii) connected over `ℚ̄` implies geometrically connected, for any `ℚ`-scheme (Stacks, Varieties,
"geometrically connected"; UNVERIFIED tag). -/
structure AGInputs (π₆ : ToP1 X.left) : Prop where
  over0 : ∀ t : _root_.ConnectedComponents (Xbar X), ∃ x : fieldPt Qbar ⟶ X,
    compOf x = t ∧ π₆.val (K := Qbar) x.left = OnePoint.some 0
  overInf : ∀ t : _root_.ConnectedComponents (Xbar X), ∃ y : fieldPt Qbar ⟶ X,
    compOf y = t ∧ π₆.val (K := Qbar) y.left = OnePoint.infty
  descend : ConnectedSpace (Xbar X) → GeometricallyConnected X.hom

/-- **`π₀(X₆_ℚ̄) = 1` (glue, compiled) from the bundle's clauses `R5ptProps`, `R5fpCount`, the
exact-CM clause `R2X6CMExact`, and the algebraic-geometry inputs `AGInputs` (unproved).** The
closed facts about `ℚ(i)` and `ℚ(√−3)` are proved (§5, §6). -/
theorem subsingleton_components_of_bundle {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {π₆ : ToP1 X.left} (h5 : R5ptProps X Ψ) (hcnt : R5fpCount) (hex : R2X6CMExact Ψ π₆)
    (hag : AGInputs π₆) : Subsingleton (_root_.ConnectedComponents (Xbar X)) :=
  subsingleton_of_bundle h5 hcnt π₆ K4 finrank_K4 R4 le_rfl (by rw [conductor_R4]; norm_num)
    inertCount6_K4 pic_R4 (IsCyclotomicExtension.zeta 4 ℚ K4) zeta4_sq'
    K3 finrank_K3 R3 le_rfl (by rw [conductor_R3]; norm_num) inertCount6_K3 pic_R3
    (2 * IsCyclotomicExtension.zeta 3 ℚ K3 + 1) sqrt3_sq
    (fun x P hP h0 => ((hex x P hP).1).1 h0) (fun x P hP hi => ((hex x P hP).2).1 hi)
    compOf compOf_galois hag.over0 hag.overInf

/-- Subsingleton components and a point give a connected space. -/
theorem connectedSpace_of_subsingleton {α : Type*} [TopologicalSpace α] (x : α)
    (h : Subsingleton (_root_.ConnectedComponents α)) : ConnectedSpace α := by
  have hu : connectedComponent x = Set.univ := Set.eq_univ_of_forall fun y =>
    ConnectedComponents.coe_eq_coe'.1 (Subsingleton.elim (ConnectedComponents.mk y) _)
  exact { isPreconnected_univ := hu ▸ isPreconnected_connectedComponent, toNonempty := ⟨x⟩ }

/-- **The clause `R1pi0Props X` (`GeometricallyConnected X.hom`) from `R5ptProps`, `R5fpCount`,
`R2X6CMExact`, `AGInputs` and one `ℚ̄`-point of `X` (`X6Props` supplies it).** -/
theorem r1pi0Props_of_bundle {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {π₆ : ToP1 X.left} (h5 : R5ptProps X Ψ) (hcnt : R5fpCount) (hex : R2X6CMExact Ψ π₆)
    (hag : AGInputs π₆) (x₀ : fieldPt Qbar ⟶ X) : GeometricallyConnected X.hom :=
  hag.descend (connectedSpace_of_subsingleton (ptOf x₀)
    (subsingleton_components_of_bundle h5 hcnt hex hag))

/-- **The same, from the repaired bundle's clauses on one `X₆`**: `X6Props` (for the `ℚ̄`-point),
`R5ptProps`, plus `R5fpCount`, `R2X6CMExact`, `AGInputs`. -/
theorem r1pi0Props_of_X6Props {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X} {π₆ : ToP1 X.left}
    (h6 : X6Props Y Φ X Ψ fY) (h5 : R5ptProps X Ψ) (hcnt : R5fpCount)
    (hex : R2X6CMExact Ψ π₆) (hag : AGInputs π₆) : GeometricallyConnected X.hom := by
  obtain ⟨-, -, ⟨x₀⟩, -, -, -⟩ := h6
  exact r1pi0Props_of_bundle h5 hcnt hex hag x₀

end Final

/-! ## §8 `descend` from a standard leaf (ag-inputs)

`AGInputs.descend` (`X_ℚ̄` connected ⇒ `X` geometrically connected over `ℚ`) is proved from the
leaf `ConnectedGeomConnected`: a proper scheme over an algebraically closed field that is
connected is geometrically connected. The reduction: for a field `K ⊇ ℚ` with algebraic closure
`L`, choose `ℚ̄ ↪ L`; then `X_L = X_ℚ̄ ×_ℚ̄ L` is connected by the leaf, and `X_L → X_K` is onto. -/

section Descend

open CategoryTheory AlgebraicGeometry Limits LeafQM.AV

/-- **Leaf AG-GC (STANDARD).** Let `k` be an algebraically closed field and `f : Y → Spec k`
proper with `Y` connected. Then `f` is geometrically connected (`Y ×_k Spec K` is connected for
every field `K` over `k`). *Published*: EGA IV₂ (4.5.1) and Cor. (4.5.8) (UNVERIFIED numbers);
Stacks Project, Varieties, Lemma "Let `k` be separably algebraically closed; `X` connected over `k`
⇒ geometrically connected" (UNVERIFIED tag 0389/0385). The published statement has neither the
properness hypothesis nor algebraic (rather than separable) closedness; this form is a
consequence. -/
def ConnectedGeomConnected : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of k)),
    IsProper f → ConnectedSpace Y → GeometricallyConnected f

/-- Two morphisms `Spec L → Spec ℚ` agree. -/
theorem spec_rat_ext {L : Type} [Field L]
    (f g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of ℚ)) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact Subsingleton.elim _ _

/-- **`descend`, proved from the leaf `ConnectedGeomConnected`.** For a proper `X` over `ℚ`, if
`X_ℚ̄` is connected then `X → Spec ℚ` is geometrically connected (Mathlib's definition: every
base change to a field is connected). -/
theorem descend_of_leaf (hL : ConnectedGeomConnected) (X : Over (Spec (CommRingCat.of ℚ)))
    (hp : IsProper X.hom) (hc : ConnectedSpace (Xbar X)) : GeometricallyConnected X.hom := by
  set q := Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
  have hg : GeometricallyConnected (pullback.snd X.hom q) := hL Qbar _ _ inferInstance hc
  constructor
  intro K _ y Z fst snd hpb
  let φ : ℚ →+* K := (Spec.preimage y).hom
  have : CharZero K := (RingHom.charZero_iff φ.injective).1 inferInstance
  let L := AlgebraicClosure K
  have : CharZero L := (RingHom.charZero_iff (algebraMap K L).injective).1 inferInstance
  let e : Qbar →ₐ[ℚ] L := IsAlgClosed.lift
  let ι : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let se : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of Qbar) :=
    Spec.map (CommRingCat.ofHom (e : Qbar →+* L))
  have hsq : IsPullback (pullback.fst snd ι ≫ fst) (pullback.snd snd ι) X.hom (ι ≫ y) :=
    (IsPullback.of_hasPullback snd ι).paste_horiz hpb
  have hcomm : se ≫ q = ι ≫ y := spec_rat_ext _ _
  let u : pullback snd ι ⟶ Xbar X := pullback.lift (pullback.fst snd ι ≫ fst)
    (pullback.snd snd ι ≫ se) (by rw [hsq.w, Category.assoc, hcomm])
  have hsq' : IsPullback u (pullback.snd snd ι) (pullback.snd X.hom q) se := by
    refine IsPullback.of_right (h₁₂ := pullback.fst X.hom q) (h₂₂ := q) ?_ ?_
      (IsPullback.of_hasPullback X.hom q)
    · rw [pullback.lift_fst, hcomm]; exact hsq
    · rw [pullback.lift_snd]
  let P : Scheme := pullback snd ι
  have : ConnectedSpace P :=
    hg.geometrically_connectedSpace se u (pullback.snd snd ι) hsq'
  have : Surjective ι := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : Surjective (pullback.fst snd ι) := inferInstance
  exact (Surjective.surj (f := pullback.fst snd ι)).connectedSpace
    (pullback.fst snd ι).continuous

end Descend

/-! ## §9 `over0`, `overInf` from a standard leaf and finite fibres (ag-inputs) -/

section Over

open CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV

/-- **Leaf AG-CD (STANDARD; a consequence of textbook theorems).** Let `X` be proper and smooth
of relative dimension 1 over `ℚ` and `π : X → P¹` a morphism (by charts, `ToP1`). For every
connected component `t` of `X_ℚ̄`, either `π` takes every value `v ∈ P¹(ℚ̄)` at a `ℚ̄`-point of `t`,
or some value is taken at infinitely many `ℚ̄`-points of `t`.
*Why true* (each step published): `X_ℚ̄` is smooth over `ℚ̄`, hence normal, so its connected
components are irreducible (Stacks, Properties, "normal Noetherian: connected components are
irreducible"; UNVERIFIED tag 033M); each is a proper integral curve `C` over `ℚ̄` (smooth of
relative dimension 1); `C → P¹_ℚ̄` is either constant or surjective (Hartshorne, *Algebraic
Geometry*, II.6.8, UNVERIFIED number; or: proper ⇒ closed irreducible image); closed points of
a finite-type `ℚ̄`-scheme are `ℚ̄`-points (Nullstellensatz) and a 1-dimensional irreducible one
has infinitely many. In the constant case all of them lie over one value. -/
def CurveComponentDichotomy : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℚ))), IsProper X.hom → SmoothOfRelativeDimension 1 X.hom →
    ∀ (π : ToP1 X.left) (t : _root_.ConnectedComponents (Xbar X)),
      (∀ v : OnePoint Qbar, ∃ x : fieldPt Qbar ⟶ X,
          compOf x = t ∧ π.val (K := Qbar) x.left = v) ∨
      (∃ v : OnePoint Qbar, Set.Infinite
          {x : fieldPt Qbar ⟶ X | compOf x = t ∧ π.val (K := Qbar) x.left = v})

variable {X : Over (Spec (CommRingCat.of ℚ))}

/-- **Every component meets every fibre**, from the leaf and finite fibres. -/
theorem meets_fibre_of_finite (hD : CurveComponentDichotomy) (hp : IsProper X.hom)
    (hs : SmoothOfRelativeDimension 1 X.hom) (π : ToP1 X.left)
    (hfin : ∀ v : OnePoint Qbar, Set.Finite {x : fieldPt Qbar ⟶ X | π.val (K := Qbar) x.left = v})
    (t : _root_.ConnectedComponents (Xbar X)) (v : OnePoint Qbar) :
    ∃ x : fieldPt Qbar ⟶ X, compOf x = t ∧ π.val (K := Qbar) x.left = v := by
  rcases hD X hp hs π t with h | ⟨w, hw⟩
  · exact h v
  · exact (hw ((hfin w).subset fun x hx => hx.2)).elim

/-- An isomorphism of QM structures on the same `A` from a conjugation: if
`q₁(a) = q₂(u a u⁻¹)` then `q₂(u⁻¹) : (A, q₁) ≅ (A, q₂)`. -/
def qmIsoOfConj {K : Type} [Field K] {A : PkgI3.AbVar K} (q₁ q₂ : QMStr A) (u : LeafQM.Oˣ)
    (h : ∀ a : LeafQM.O, q₁.iota a = q₂.iota (u * a * ↑u⁻¹)) : QMIso q₁ q₂ where
  φ := q₂.iota ↑u⁻¹
  ψ := q₂.iota ↑u
  left := by
    change (q₂.iota ↑u * q₂.iota ↑u⁻¹).hom = 𝟙 _
    rw [← map_mul, Units.mul_inv, map_one]; rfl
  right := by
    change (q₂.iota ↑u⁻¹ * q₂.iota ↑u).hom = 𝟙 _
    rw [← map_mul, Units.inv_mul, map_one]; rfl
  equivariant a := by
    change (q₂.iota ↑u⁻¹ * q₁.iota a).hom = (q₂.iota a * q₂.iota ↑u⁻¹).hom
    rw [h, ← map_mul, ← map_mul]
    congr 2
    calc (↑u⁻¹ : LeafQM.O) * (↑u * a * ↑u⁻¹) = (↑u⁻¹ * ↑u) * a * ↑u⁻¹ := by noncomm_ring
      _ = a * ↑u⁻¹ := by rw [Units.inv_mul, _root_.one_mul]

/-- **Leaf AutO (STANDARD; consequence of two published theorems).** `Aut(𝒪)` is finite modulo
inner automorphisms by units: there is a finite set `S` of automorphisms such that every `α` is
`s ∘ Ad(u)` for some `s ∈ S`, `u ∈ 𝒪^×`.
*Why true*: by Skolem–Noether (leaf T13, **proved** in `scratch/t-skolem-kw/SkolemNoether.lean`)
every `α` extends to `B` and is `Ad(b)` with `b ∈ N_{B^×}(𝒪)`; and `N_{B^×}(𝒪)/ℚ^×𝒪^×` is finite,
`≅ (ℤ/2)^{#\{p ∣ 6\}} = (ℤ/2)²` (the Atkin–Lehner group of the maximal order of discriminant 6:
Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800 (1980), Ch. II–III; Voight,
*Quaternion Algebras*, GTM 288 (2021), §18.5 / §28.9; all UNVERIFIED locators). With
`S` = representatives of that group this is the statement. -/
def AutModInnFinite : Prop :=
  ∃ S : Set (LeafQM.O ≃+* LeafQM.O), S.Finite ∧
    ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ s ∈ S, ∃ u : LeafQM.Oˣ, ∀ a, α a = s (u * a * ↑u⁻¹)

/-- **Finitely many twist classes** (glue, proved from `AutModInnFinite`). -/
theorem twistClasses_finite (hW : AutModInnFinite) (P : QMPair Qbar) :
    Set.Finite (Set.range fun α : LeafQM.O ≃+* LeafQM.O =>
      (Quotient.mk (pairSetoid Qbar) (P.twist α))) := by
  obtain ⟨S, hS, hW⟩ := hW
  refine (hS.image fun s => (Quotient.mk (pairSetoid Qbar) (P.twist s))).subset ?_
  rintro _ ⟨α, rfl⟩
  obtain ⟨s, hs, u, hu⟩ := hW α
  refine ⟨s, hs, Quotient.sound ⟨(qmIsoOfConj (P.twist α).q (P.twist s).q u ?_).symm⟩⟩
  intro a
  exact congrArg P.q.iota (hu a)

/-- **Finite fibres of `π₆` on `ℚ̄`-points** (glue, proved), from the fibre clause of R2 (twist
orbits; `R2X6Props`, implied by the bundle's `R2X6PropsIff`) and `AutModInnFinite`. -/
theorem fibres_finite {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {π₆ : ToP1 X.left}
    (h2 : R2X6Props X Ψ π₆) (hW : AutModInnFinite) (v : OnePoint Qbar) :
    Set.Finite {x : fieldPt Qbar ⟶ X | π₆.val (K := Qbar) x.left = v} := by
  by_cases hne : ∃ x₀ : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x₀.left = v
  · obtain ⟨x₀, hx₀⟩ := hne
    let P := (Ψ x₀).out
    refine ((twistClasses_finite hW P).preimage Ψ.injective.injOn).subset ?_
    intro x hx
    have hfib := (h2 x₀ x P (Ψ x).out (Quotient.out_eq _).symm (Quotient.out_eq _).symm).1
    obtain ⟨α, ⟨i⟩⟩ := hfib.1 (hx₀.trans hx.symm)
    refine ⟨α, ?_⟩
    change Quotient.mk _ (P.twist α) = Ψ x
    rw [← Quotient.out_eq (Ψ x)]
    exact Quotient.sound ⟨i⟩
  · push Not at hne
    convert Set.finite_empty
    ext x
    simp [hne x]

/-- **`AGInputs` from the leaves** `ConnectedGeomConnected`, `CurveComponentDichotomy`,
`AutModInnFinite`, the fibre clause of R2 and `X` proper smooth of relative dimension 1. -/
theorem agInputs_of_leaves {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {π₆ : ToP1 X.left} (hL : ConnectedGeomConnected) (hD : CurveComponentDichotomy)
    (hW : AutModInnFinite) (hp : IsProper X.hom) (hs : SmoothOfRelativeDimension 1 X.hom)
    (h2 : R2X6Props X Ψ π₆) : AGInputs π₆ where
  over0 t := meets_fibre_of_finite hD hp hs π₆ (fibres_finite h2 hW) t _
  overInf t := meets_fibre_of_finite hD hp hs π₆ (fibres_finite h2 hW) t _
  descend := descend_of_leaf hL X hp

/-- **The clause `R1pi0Props X` (`GeometricallyConnected X.hom`) from the bundle's clauses and
three standard leaves.** Bundle clauses: `X6Props` (properness, smoothness, a `ℚ̄`-point),
`R2X6Props` (fibre clause; implied by `R2X6PropsIff`), `R5ptProps`; plus `R5fpCount` and the
exact-CM clause `R2X6CMExact`. Standard leaves: `ConnectedGeomConnected` (EGA IV₂ 4.5),
`CurveComponentDichotomy` (Hartshorne II.6.8 and Nullstellensatz), `AutModInnFinite`
(Skolem–Noether, proved elsewhere, and the finiteness of the Atkin–Lehner group). -/
theorem r1pi0Props_of_leaves {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X} {π₆ : ToP1 X.left}
    (h6 : X6Props Y Φ X Ψ fY) (h2 : R2X6Props X Ψ π₆) (h5 : R5ptProps X Ψ) (hcnt : R5fpCount)
    (hex : R2X6CMExact Ψ π₆) (hL : ConnectedGeomConnected) (hD : CurveComponentDichotomy)
    (hW : AutModInnFinite) : GeometricallyConnected X.hom := by
  obtain ⟨hp, hs, ⟨x₀⟩, -, -, -⟩ := h6
  exact r1pi0Props_of_bundle h5 hcnt hex (agInputs_of_leaves hL hD hW hp hs h2) x₀

end Over

end AGIn


/-! ## §10 Leaf AutO as glue: extension of `Aut(𝒪)` to `B`, Skolem–Noether, Atkin–Lehner -/

namespace AGInO

open LeafQM

theorem int_coord (r : ℚ) (k : ℕ) (h : r.den ∣ k) : ∃ z : ℤ, (k : ℚ) * r = z := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨t * r.num, ?_⟩
  push_cast
  rw [mul_comm (r.den : ℚ) t, mul_assoc, Rat.den_mul_eq_num]

theorem mem_O_of_int (z0 z1 z2 z3 : ℤ) : (⟨z0, z1, z2, z3⟩ : B) ∈ O := by
  refine ⟨![z0 - z2, z1 - z3, 2 * z2, 2 * z3], ?_⟩
  ext <;> simp [ofInt]

theorem exists_nat_smul_mem (b : B) : ∃ n : ℕ, 0 < n ∧ ((n : ℚ) • b) ∈ O := by
  refine ⟨b.re.den * b.imI.den * b.imJ.den * b.imK.den, by positivity, ?_⟩
  obtain ⟨z0, h0⟩ := int_coord b.re (b.re.den * b.imI.den * b.imJ.den * b.imK.den)
    ⟨b.imI.den * b.imJ.den * b.imK.den, by ring⟩
  obtain ⟨z1, h1⟩ := int_coord b.imI (b.re.den * b.imI.den * b.imJ.den * b.imK.den)
    ⟨b.re.den * b.imJ.den * b.imK.den, by ring⟩
  obtain ⟨z2, h2⟩ := int_coord b.imJ (b.re.den * b.imI.den * b.imJ.den * b.imK.den)
    ⟨b.re.den * b.imI.den * b.imK.den, by ring⟩
  obtain ⟨z3, h3⟩ := int_coord b.imK (b.re.den * b.imI.den * b.imJ.den * b.imK.den)
    ⟨b.re.den * b.imI.den * b.imJ.den, by ring⟩
  have : ((b.re.den * b.imI.den * b.imJ.den * b.imK.den : ℕ) : ℚ) • b = ⟨z0, z1, z2, z3⟩ := by
    ext
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  rw [this]
  exact mem_O_of_int z0 z1 z2 z3

/-- A denominator for `b`. -/
def nOf (b : B) : ℕ := Classical.choose (exists_nat_smul_mem b)

theorem nOf_pos (b : B) : 0 < nOf b := (Classical.choose_spec (exists_nat_smul_mem b)).1

theorem nOf_mem (b : B) : ((nOf b : ℚ) • b) ∈ O := (Classical.choose_spec (exists_nat_smul_mem b)).2

/-- The `ℚ`-linear extension of `α ∈ Aut(𝒪)` to `B`, as a function. -/
def extFun (α : O ≃+* O) (b : B) : B := ((nOf b : ℚ)⁻¹) • (α ⟨(nOf b : ℚ) • b, nOf_mem b⟩ : B)

theorem natCast_mul_eq_smul (n : ℕ) (y : B) : (n : B) * y = (n : ℚ) • y := by
  rw [Algebra.smul_def, map_natCast]

theorem coe_alpha_natCast_mul (α : O ≃+* O) (n : ℕ) (x : O) :
    (α ((n : O) * x) : B) = (n : ℚ) • (α x : B) := by
  rw [map_mul, map_natCast, Subring.coe_mul, Subring.coe_natCast, natCast_mul_eq_smul]

/-- Independence of the denominator. -/
theorem extFun_eq (α : O ≃+* O) (b : B) (n : ℕ) (hn : 0 < n) (x : O)
    (hx : (x : B) = (n : ℚ) • b) : extFun α b = ((n : ℚ)⁻¹) • (α x : B) := by
  set m := nOf b
  have hm : (0 : ℚ) < m := by exact_mod_cast nOf_pos b
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  set y : O := ⟨(m : ℚ) • b, nOf_mem b⟩
  have hxy : (n : O) * y = (m : O) * x := by
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast, Subring.coe_natCast, hx,
      natCast_mul_eq_smul, natCast_mul_eq_smul]
    change (n : ℚ) • ((m : ℚ) • b) = (m : ℚ) • ((n : ℚ) • b)
    rw [smul_smul, smul_smul, mul_comm]
  have key : (n : ℚ) • (α y : B) = (m : ℚ) • (α x : B) := by
    rw [← coe_alpha_natCast_mul, ← coe_alpha_natCast_mul, hxy]
  unfold extFun
  change ((m : ℚ)⁻¹) • (α y : B) = _
  have := congrArg (fun z : B => ((n : ℚ)⁻¹ * (m : ℚ)⁻¹) • z) key
  simp only [smul_smul] at this
  rw [show (n : ℚ)⁻¹ * (m : ℚ)⁻¹ * n = (m : ℚ)⁻¹ by field_simp,
    show (n : ℚ)⁻¹ * (m : ℚ)⁻¹ * m = (n : ℚ)⁻¹ by field_simp] at this
  exact this

theorem extFun_coe (α : O ≃+* O) (a : O) : extFun α a = α a := by
  rw [extFun_eq α a 1 one_pos a (by simp)]
  simp

/-- The extension as a `ℚ`-algebra map. -/
def extHom (α : O ≃+* O) : B →ₐ[ℚ] B where
  toFun := extFun α
  map_one' := by
    have := extFun_coe α 1
    simpa using this
  map_zero' := by
    have := extFun_coe α 0
    simpa using this
  map_mul' b c := by
    set nb := nOf b
    set nc := nOf c
    have hb : (0 : ℚ) < nb := by exact_mod_cast nOf_pos b
    have hc : (0 : ℚ) < nc := by exact_mod_cast nOf_pos c
    set xb : O := ⟨(nb : ℚ) • b, nOf_mem b⟩
    set xc : O := ⟨(nc : ℚ) • c, nOf_mem c⟩
    rw [extFun_eq α (b * c) (nb * nc) (Nat.mul_pos (nOf_pos b) (nOf_pos c)) (xb * xc) (by
      rw [Subring.coe_mul]
      change ((nb : ℚ) • b) * ((nc : ℚ) • c) = _
      rw [smul_mul_smul_comm]; push_cast; rfl)]
    change _ = ((nb : ℚ)⁻¹ • (α xb : B)) * ((nc : ℚ)⁻¹ • (α xc : B))
    rw [smul_mul_smul_comm, map_mul, Subring.coe_mul]
    push_cast
    rw [mul_inv]
  map_add' b c := by
    set nb := nOf b
    set nc := nOf c
    have hb : (0 : ℚ) < nb := by exact_mod_cast nOf_pos b
    have hc : (0 : ℚ) < nc := by exact_mod_cast nOf_pos c
    set xb : O := ⟨(nb : ℚ) • b, nOf_mem b⟩
    set xc : O := ⟨(nc : ℚ) • c, nOf_mem c⟩
    rw [extFun_eq α (b + c) (nb * nc) (Nat.mul_pos (nOf_pos b) (nOf_pos c))
      ((nc : O) * xb + (nb : O) * xc) (by
        rw [Subring.coe_add, Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast,
          Subring.coe_natCast, natCast_mul_eq_smul, natCast_mul_eq_smul]
        change (nc : ℚ) • ((nb : ℚ) • b) + (nb : ℚ) • ((nc : ℚ) • c) = _
        rw [smul_smul, smul_smul, smul_add]; push_cast; ring_nf)]
    change _ = ((nb : ℚ)⁻¹ • (α xb : B)) + ((nc : ℚ)⁻¹ • (α xc : B))
    rw [map_add, Subring.coe_add, coe_alpha_natCast_mul, coe_alpha_natCast_mul, smul_add,
      smul_smul, smul_smul]
    congr 1
    · congr 1; push_cast; field_simp
    · congr 1; push_cast; field_simp
  commutes' q := by
    change extFun α (algebraMap ℚ B q) = algebraMap ℚ B q
    have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    rw [extFun_eq α _ q.den q.den_pos ((q.num : ℤ) : O) (by
      rw [Subring.coe_intCast, Algebra.smul_def, ← map_mul, mul_comm, Rat.mul_den_eq_num,
        map_intCast])]
    rw [map_intCast, Subring.coe_intCast, ← map_intCast (algebraMap ℚ B), Algebra.smul_def,
      ← map_mul]
    congr 1
    rw [← Rat.mul_den_eq_num]; field_simp

theorem extHom_coe (α : O ≃+* O) (a : O) : extHom α a = α a := extFun_coe α a

theorem extHom_symm_comp (α : O ≃+* O) (b : B) : extHom α (extHom α.symm b) = b := by
  set n := nOf b
  have hn : (0 : ℚ) < n := by exact_mod_cast nOf_pos b
  set x : O := ⟨(n : ℚ) • b, nOf_mem b⟩
  change extFun α (extFun α.symm b) = b
  have h1 : extFun α.symm b = (n : ℚ)⁻¹ • (α.symm x : B) := rfl
  rw [extFun_eq α _ (nOf b) (nOf_pos b) (α.symm x) (by rw [h1, smul_smul, mul_inv_cancel₀ hn.ne', one_smul])]
  rw [RingEquiv.apply_symm_apply]
  change (n : ℚ)⁻¹ • ((n : ℚ) • b) = b
  rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul]

/-- **The `ℚ`-algebra automorphism of `B` extending `α ∈ Aut(𝒪)`.** -/
def extAut (α : O ≃+* O) : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofAlgHom (extHom α) (extHom α.symm)
    (AlgHom.ext fun b => extHom_symm_comp α b)
    (AlgHom.ext fun b => by simpa using extHom_symm_comp α.symm b)

theorem extAut_coe (α : O ≃+* O) (a : O) : extAut α a = α a := extFun_coe α a


/-! ### `AutModInnFinite` from Skolem–Noether and the Atkin–Lehner finiteness -/

/-- **Leaf AL (STANDARD): the Atkin–Lehner group of `𝒪` is finite.** There is a finite set `T`
of units of `B` such that every `b ∈ B^×` normalizing `𝒪` (`b𝒪b⁻¹ = 𝒪`) is `r·t·u` with
`r ∈ ℚ`, `t ∈ T`, `u ∈ 𝒪^×`; i.e. `N_{B^×}(𝒪)/ℚ^×𝒪^×` is finite.
*Published*: for a maximal order in a quaternion algebra over `ℚ` of discriminant `D`,
`N(𝒪)/ℚ^×𝒪^×` is an elementary abelian 2-group of rank at most `#{p ∣ D}`, generated by elements
of reduced norm dividing `D` (Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800
(1980), Ch. II–III; Voight, *Quaternion Algebras*, GTM 288 (2021), Ch. 18 and §28.9; all
UNVERIFIED locators). Finiteness is a consequence. -/
def AtkinLehnerFinite : Prop :=
  ∃ T : Set Bˣ, T.Finite ∧ ∀ b : Bˣ,
    (∀ a : B, a ∈ O ↔ (b : B) * a * ((b⁻¹ : Bˣ) : B) ∈ O) →
      ∃ t ∈ T, ∃ (r : ℚ) (u : Oˣ), (b : B) = r • ((t : B) * ((u : O) : B))

/-- Conjugation by a unit normalizing `𝒪`, as an automorphism of `𝒪`. -/
def conjAut (t : Bˣ) (ht : ∀ a : B, a ∈ O ↔ (t : B) * a * ((t⁻¹ : Bˣ) : B) ∈ O) : O ≃+* O where
  toFun a := ⟨(t : B) * a * ((t⁻¹ : Bˣ) : B), (ht a).1 a.2⟩
  invFun a := ⟨((t⁻¹ : Bˣ) : B) * a * (t : B), (ht _).2 (by
    have : (t : B) * (((t⁻¹ : Bˣ) : B) * (a : B) * (t : B)) * ((t⁻¹ : Bˣ) : B) = a := by
      simp [mul_assoc]
    rw [this]; exact a.2)⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a c := by
    apply Subtype.ext
    simp only [Subring.coe_mul]
    calc (t : B) * (↑a * ↑c) * ((t⁻¹ : Bˣ) : B)
        = (t : B) * ↑a * (((t⁻¹ : Bˣ) : B) * (t : B)) * ↑c * ((t⁻¹ : Bˣ) : B) := by
          simp [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_add' a c := by
    apply Subtype.ext
    simp only [Subring.coe_add]
    noncomm_ring

open Classical in
/-- The finite set of automorphisms: conjugations by the normalizing elements of `T`. -/
def autSet (T : Set Bˣ) : Set (O ≃+* O) :=
  (fun t : Bˣ => if h : ∀ a : B, a ∈ O ↔ (t : B) * a * ((t⁻¹ : Bˣ) : B) ∈ O then conjAut t h
    else RingEquiv.refl O) '' T

/-- **Leaf AutO is glue** from Skolem–Noether (`GlueDescent.LeafSkolemNoether`, **proved** by
t-skolem-kw as `TSkolemKW.leafSkolemNoether`, same statement) and leaf AL. -/
theorem autModInnFinite_of (hSN : GlueDescent.LeafSkolemNoether) (hAL : AtkinLehnerFinite) :
    AGIn.AutModInnFinite := by
  obtain ⟨T, hT, hAL⟩ := hAL
  refine ⟨autSet T, hT.image _, fun α => ?_⟩
  obtain ⟨b, hb⟩ := GlueDescent.B6_inner hSN (extAut α)
  have hnorm : ∀ a : B, a ∈ O ↔ (b : B) * a * ((b⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    constructor
    · intro ha
      rw [← hb a, show a = ((⟨a, ha⟩ : O) : B) from rfl, extAut_coe]
      exact (α ⟨a, ha⟩).2
    · intro hc
      have h1 : extAut α ((α.symm ⟨_, hc⟩ : O) : B) = extAut α a := by
        rw [extAut_coe, RingEquiv.apply_symm_apply, hb a]
      rw [← (extAut α).injective h1]
      exact (α.symm ⟨_, hc⟩).2
  obtain ⟨t, htT, r, u, hbr⟩ := hAL b hnorm
  have hr : r ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hbr
    exact b.ne_zero hbr
  have huu : ((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  have huu' : (((u⁻¹ : Oˣ) : O) : B) * ((u : O) : B) = 1 := by
    rw [← Subring.coe_mul, Units.inv_mul, Subring.coe_one]
  have hbinv : ((b⁻¹ : Bˣ) : B) = r⁻¹ • ((((u⁻¹ : Oˣ) : O) : B) * ((t⁻¹ : Bˣ) : B)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hbr, smul_mul_smul_comm, mul_inv_cancel₀ hr, one_smul]
    calc (t : B) * ((u : O) : B) * ((((u⁻¹ : Oˣ) : O) : B) * ((t⁻¹ : Bˣ) : B))
        = (t : B) * (((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B)) * ((t⁻¹ : Bˣ) : B) := by
          simp only [mul_assoc]
      _ = 1 := by rw [huu, mul_one, Units.mul_inv]
  have hformula : ∀ a : B, (b : B) * a * ((b⁻¹ : Bˣ) : B) =
      (t : B) * (((u : O) : B) * a * (((u⁻¹ : Oˣ) : O) : B)) * ((t⁻¹ : Bˣ) : B) := by
    intro a
    rw [hbr, hbinv, smul_mul_assoc, smul_mul_smul_comm, mul_inv_cancel₀ hr, one_smul]
    simp only [mul_assoc]
  have ht : ∀ a : B, a ∈ O ↔ (t : B) * a * ((t⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    have e : (t : B) * a * ((t⁻¹ : Bˣ) : B) =
        (b : B) * ((((u⁻¹ : Oˣ) : O) : B) * a * ((u : O) : B)) * ((b⁻¹ : Bˣ) : B) := by
      rw [hformula]
      congr 2
      calc a = (((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B)) * a *
            ((((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B))) := by rw [huu, one_mul, mul_one]
        _ = _ := by simp only [mul_assoc]
    rw [e, ← hnorm]
    constructor
    · intro ha
      exact O.mul_mem (O.mul_mem ((u⁻¹ : Oˣ) : O).2 ha) (u : O).2
    · intro h
      have : a = ((u : O) : B) * ((((u⁻¹ : Oˣ) : O) : B) * a * ((u : O) : B)) *
          (((u⁻¹ : Oˣ) : O) : B) := by
        calc a = (((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B)) * a *
              ((((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B))) := by rw [huu, one_mul, mul_one]
          _ = _ := by simp only [mul_assoc]
      rw [this]
      exact O.mul_mem (O.mul_mem (u : O).2 h) ((u⁻¹ : Oˣ) : O).2
  refine ⟨conjAut t ht, ⟨t, htT, by classical exact dif_pos ht⟩, u, fun a => ?_⟩
  apply Subtype.ext
  rw [← extAut_coe, hb, hformula]
  rfl


/-- **`R1pi0Props` from the bundle's clauses, (c), and four standard leaves**, with AutO replaced
by Skolem–Noether (proved by t-skolem-kw, `TSkolemKW.leafSkolemNoether`, same statement) and the
Atkin–Lehner finiteness. -/
theorem r1pi0Props_of_leaves' {X Y : CategoryTheory.Over
      (AlgebraicGeometry.Spec (CommRingCat.of ℚ))} {Φ : LeafQM.AV.PtEquiv Y}
    {Ψ : (LeafQM.AV.fieldPt LeafQM.AV.Qbar ⟶ X) ≃ Quotient (LeafQM.AV.pairSetoid LeafQM.AV.Qbar)}
    {fY : Y ⟶ X} {π₆ : LeafQM.AV.ToP1 X.left}
    (h6 : LeafQM.AV.X6Props Y Φ X Ψ fY) (h2 : LeafQM.AV.R2X6Props X Ψ π₆)
    (h5 : LeafQM.AV.R5ptProps X Ψ) (hcnt : LeafQM.AV.R5fpCount) (hex : AGIn.R2X6CMExact Ψ π₆)
    (hL : AGIn.ConnectedGeomConnected) (hD : AGIn.CurveComponentDichotomy)
    (hSN : GlueDescent.LeafSkolemNoether) (hAL : AtkinLehnerFinite) :
    AlgebraicGeometry.GeometricallyConnected X.hom :=
  AGIn.r1pi0Props_of_leaves h6 h2 h5 hcnt hex hL hD (autModInnFinite_of hSN hAL)

end AGInO


/-! ## §11 The bundle without the clause `R1pi0Props` (integration form)

`R1pi0Props`, `R2X6PropsIff`, `R1R2fpRep` are verbatim copies of `LeafAdopt.R1pi0Props`,
`LeafAdopt.R2X6PropsIff`, `LeafAdopt.R1R2fpRep` (`scratch/h-decomposition/Leaves.lean`,
L18651, L18661, L18724; scratch files cannot import each other). `R1R2fpRepNoPi0` is
`R1R2fpRep` with its last clause `R1pi0Props X` replaced by the exact-CM clause (c). -/

namespace AGInLA

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

def R1pi0Props (X : Over (Spec (CommRingCat.of ℚ))) : Prop :=
  GeometricallyConnected X.hom

def R2X6PropsIff (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (π₆ : ToP1 X.left) : Prop :=
  ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
      (π₆.val (K := Qbar) x.left = π₆.val (K := Qbar) x'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.some 0) ∧
      (HasCM3 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.infty) ∧
      (HasCM24 P.q ↔ π₆.val (K := Qbar) x.left = OnePoint.some (-16 / 27))

def R1R2fpRep : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ ∧ R1pi0Props X

/-- **The repaired bundle with `R1pi0Props` replaced by (c) `R2X6CMExact`.** -/
def R1R2fpRepNoPi0 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ ∧ AGIn.R2X6CMExact Ψ π₆

/-- **Glue (proved): the bundle clause `R1pi0Props` is a consequence.** The repaired bundle
without `R1pi0Props`, with (c), plus the leaf `R5fpCount` and the standard leaves AG-GC, AG-CD,
Skolem–Noether (proved by t-skolem-kw) and AL, gives the repaired bundle `R1R2fpRep`. -/
theorem r1R2fpRep_of_noPi0 (h : R1R2fpRepNoPi0) (hcnt : R5fpCount)
    (hL : AGIn.ConnectedGeomConnected) (hD : AGIn.CurveComponentDichotomy)
    (hSN : GlueDescent.LeafSkolemNoether) (hAL : AGInO.AtkinLehnerFinite) : R1R2fpRep := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, hex⟩ := h
  have h2' : R2X6Props X Ψ π₆ := by
    intro x x' P Q hP hQ
    obtain ⟨hf, h4, h3, h24⟩ := h2 x x' P Q hP hQ
    exact ⟨hf, h4.1, h3.1, h24.1⟩
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5,
    AGInO.r1pi0Props_of_leaves' h6 h2' h5 hcnt hex hL hD hSN hAL⟩

end AGInLA

#print axioms AGIn.subsingleton_of_galois
#print axioms AGIn.subsingleton_of_bundle
#print axioms AGIn.inertCount6_K4
#print axioms AGIn.pic_R4
#print axioms AGIn.inertCount6_K3
#print axioms AGIn.pic_R3
#print axioms AGIn.subsingleton_components_of_bundle
#print axioms AGIn.r1pi0Props_of_bundle
#print axioms AGIn.compOf_galois
#print axioms AGIn.r1pi0Props_of_X6Props
#print axioms AGIn.descend_of_leaf
#print axioms AGIn.twistClasses_finite
#print axioms AGIn.fibres_finite
#print axioms AGIn.agInputs_of_leaves
#print axioms AGIn.r1pi0Props_of_leaves
#print axioms AGInO.extAut
#print axioms AGInO.autModInnFinite_of
#print axioms AGInO.r1pi0Props_of_leaves'
#print axioms AGInLA.r1R2fpRep_of_noPi0
