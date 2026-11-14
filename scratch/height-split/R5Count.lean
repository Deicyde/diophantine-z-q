import ZInQKernel.HDecomp.QM.Leaves

/-!
# height-split: the row H-3 (`r5count : LeafQM.AV.R5fpCount`) split into Eichler's count of optimal
embeddings (published form) and the moduli correspondence (glue)

The row (imported, not restated): for an order `R` of conductor prime to `6` in an imaginary
quadratic field `k`, occurring as some `End_𝒪(A)`, the number of isomorphism classes of QM pairs over
`ℚ̄` with `End_𝒪(A) ≅ R` is `2^{b(k)} h(R)`, `b(k) = #{p ∣ 6 inert in k}`.

* **Leaf `EichlerOptimalEmbeddingCount`** (published form): the optimal embeddings `φ : k → B`
  with `φ⁻¹(𝒪) = R`, modulo conjugation by `𝒪^×`, are finite in number, and their number is
  `h(R) ∏_{p ∣ 6} (1 − (k/p))` (Eichler's local factors: `2` for `p` inert, `1` ramified, `0` split).
* **Glue `QMPairEmbeddingCorrespondence`**: the classes of QM pairs over `ℚ̄` with `End_𝒪(A) ≅ R`
  are in bijection with those embedding classes (Shimura's complex uniformization of QM abelian
  surfaces; not proved).
* **Proved**: the row from the two (`r5fpCount_of`): a QM pair exists, so the embedding classes are
  nonempty, so no local factor vanishes, so each factor is `2^{[p inert]}`.

No `sorry`, no `axiom`.
-/

namespace ZInQ.HeightSplit.R5

open LeafQM LeafQM.AV NumberField

variable (k : Type) [Field k] [NumberField k]

/-- **Optimal embeddings** of `R ⊆ k` in the maximal order `𝒪` of `B = (2, −3)_ℚ` (discriminant
`6`, the kernel's `LeafQM.B`, `LeafQM.O`): `ℚ`-algebra maps `φ : k → B` with `φ⁻¹(𝒪) = R`. -/
def OptEmb (R : Subring k) : Type :=
  {φ : k →ₐ[ℚ] B // ∀ x : k, φ x ∈ O ↔ x ∈ R}

/-- Conjugacy by units of `𝒪`: `φ ~ ψ` iff `ψ = u φ u⁻¹` for some `u ∈ 𝒪^×`. -/
def embSetoid (R : Subring k) : Setoid (OptEmb k R) where
  r φ ψ := ∃ u : (↥O)ˣ, ∀ x : k, ψ.1 x = ((u : ↥O) : B) * φ.1 x * ((u⁻¹ : (↥O)ˣ) : ↥O)
  iseqv := by
    refine ⟨fun φ => ⟨1, fun x => by simp⟩, fun {φ ψ} ⟨u, hu⟩ => ⟨u⁻¹, fun x => ?_⟩,
      fun {φ ψ χ} ⟨u, hu⟩ ⟨v, hv⟩ => ⟨v * u, fun x => ?_⟩⟩
    · rw [hu x, inv_inv]
      have h1 : ((u⁻¹ : (↥O)ˣ) : ↥O) * (u : ↥O) = 1 := by simp
      have h1' : ((((u⁻¹ : (↥O)ˣ) : ↥O)) : B) * ((u : ↥O) : B) = 1 := by
        rw [← Subring.coe_mul, h1]; rfl
      calc φ.1 x = (((u⁻¹ : (↥O)ˣ) : ↥O) : B) * ((u : ↥O) : B) * φ.1 x *
            ((((u⁻¹ : (↥O)ˣ) : ↥O) : B) * ((u : ↥O) : B)) := by rw [h1']; simp
        _ = _ := by simp only [mul_assoc]
    · rw [hv x, hu x]
      simp only [Units.val_mul, mul_inv_rev, Subring.coe_mul]
      noncomm_ring

/-- Eichler's local factor `1 − (k/p)` at `p ∈ 𝓞_k`: `2` if `p𝓞_k` is prime (inert), `1` if
`p𝓞_k = 𝔓²` (ramified), `0` otherwise (split). -/
noncomputable def eichlerFactor (p : 𝓞 k) : ℕ := by
  classical
  exact if (Ideal.span {p}).IsPrime then 2
    else if ∃ P : Ideal (𝓞 k), P.IsPrime ∧ Ideal.span {p} = P ^ 2 then 1 else 0

/-- **Leaf. Eichler's count of optimal embeddings** (M. Eichler, *Zur Zahlentheorie der
Quaternionen-Algebren*, J. reine angew. Math. 195 (1955); M.-F. Vignéras, *Arithmétique des algèbres
de quaternions*, LNM 800 (1980), Ch. III, Thm 5.11 and Cor. 5.12; J. Voight, *Quaternion algebras*,
GTM 288 (2021), Ch. 30; all numbers UNVERIFIED), specialized to the indefinite algebra `B` of
discriminant `6` over `ℚ` and its maximal order `𝒪` (class number one, Eichler's condition): for an
order `R` of conductor `f` prime to `6` in an imaginary quadratic field `k`, the optimal embeddings
`R ↪ 𝒪` modulo `𝒪^×` are finite in number and
`m(R, 𝒪; 𝒪^×) = h(R) ∏_{p ∣ 6} (1 − {R/p})`, `{R/p} = (k/p)` for `p ∤ f` (Eichler symbol),
`h(R) = #Pic(R)`. Caveat (UNVERIFIED which form is printed): some sources count modulo the
norm-one units `𝒪¹`, with the extra factor `[n(𝒪^×) : n(R^×)] = 2` (a unit of norm `−1` exists in
`𝒪` and acts freely); the form below is the `𝒪^×` count. Checked by hand (leaf-review-a §5.6):
`ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` give `2`, the maximal order of discriminant `−19` gives `4`. -/
def EichlerOptimalEmbeddingCount : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      Finite (Quotient (embSetoid k R)) ∧
      Nat.card (Quotient (embSetoid k R)) =
        eichlerFactor k 2 * eichlerFactor k 3 * Nat.card (CommRing.Pic R)

/-- The classes of QM pairs over `ℚ̄` with `End_𝒪(A) ≅ R` (the set counted by the row). -/
def QMClasses (R : Subring k) : Type 1 :=
  {c : Quotient (pairSetoid Qbar) //
    ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)}

/-- **Glue `QMPairEmbeddingCorrespondence`.** The classes of QM pairs `(A, ι)` over `ℚ̄` with
`End_𝒪(A) ≅ R` are in bijection with the optimal embeddings `R ↪ 𝒪` modulo `𝒪^×`. Needs: Shimura's
complex uniformization (over `ℂ`, `H₁(A, ℤ)` is a free rank-one `𝒪`-module since `𝒪` has class
number one, so `(A, ι) ≅ (ℂ²/ι(𝒪)v_τ, ι)`, and `(A, ι) ↦ τ` identifies the classes with
`𝒪^× \ (ℂ ∖ ℝ) = 𝒪¹ \ ℍ`, a unit of norm `−1` swapping the half planes); the CM points by `R` are
the fixed points of `φ(k^×)` for the optimal embeddings `φ` of `R`, `End_𝒪 ≅ φ(k) ∩ 𝒪 = φ(R)`, and
abstract isomorphism classes of imaginary quadratic orders are determined by `(k, f)`; descent
from `ℂ` to `ℚ̄` (CM abelian surfaces and their isomorphisms are defined over `ℚ̄`); algebraicity of
the QM tori (a type-`μ` Riemann form, Lemma P of rv-qm-polar). Shimura, Ann. Math. 85 (1967);
González–Rotger, J. Math. Soc. Japan 58 (2006) §5 (UNVERIFIED locators). -/
def QMPairEmbeddingCorrespondence : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      Nonempty (QMClasses k R ≃ Quotient (embSetoid k R))

omit [NumberField k] in
/-- A nonzero Eichler factor is `2^{[p inert]}`. -/
theorem eichlerFactor_eq_of_ne_zero (p : 𝓞 k) (h : eichlerFactor k p ≠ 0) :
    eichlerFactor k p = 2 ^ (by classical exact if (Ideal.span {p}).IsPrime then 1 else 0) := by
  classical
  unfold eichlerFactor at h ⊢
  by_cases hp : (Ideal.span {p}).IsPrime
  · simp [hp]
  · by_cases hr : ∃ P : Ideal (𝓞 k), P.IsPrime ∧ Ideal.span {p} = P ^ 2
    · simp [hp, hr]
    · simp [hp, hr] at h

/-- **H-3: the row `R5fpCount` from Eichler's count and the moduli correspondence.** -/
theorem r5fpCount_of (hE : EichlerOptimalEmbeddingCount) (hC : QMPairEmbeddingCorrespondence) :
    R5fpCount := by
  classical
  intro k _ _ _ hk R hR hc hex
  obtain ⟨e⟩ := hC k hk R hR hc
  obtain ⟨hfin, hcard⟩ := hE k hk R hR hc
  obtain ⟨P, hP⟩ := hex
  have hne : Nonempty (Quotient (embSetoid k R)) := ⟨e ⟨Quotient.mk _ P, P, rfl, hP⟩⟩
  have hpos : 0 < Nat.card (Quotient (embSetoid k R)) := Nat.card_pos
  have hcongr : Nat.card (QMClasses k R) = Nat.card (Quotient (embSetoid k R)) := Nat.card_congr e
  show Nat.card (QMClasses k R) = _
  rw [hcongr, hcard]
  rw [hcard] at hpos
  have h2 : eichlerFactor k 2 ≠ 0 := fun h => by simp [h] at hpos
  have h3 : eichlerFactor k 3 ≠ 0 := fun h => by simp [h] at hpos
  rw [eichlerFactor_eq_of_ne_zero k 2 h2, eichlerFactor_eq_of_ne_zero k 3 h3, inertCount6, pow_add]

end ZInQ.HeightSplit.R5

#print axioms ZInQ.HeightSplit.R5.r5fpCount_of
