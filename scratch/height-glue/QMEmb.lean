import ZInQKernel.HDecomp.QM.Leaves

/-! # height-glue: `QMPairEmbeddingCorrespondence` (height-split, H-3) reduced

§0 is a verbatim copy of `scratch/height-split/R5Count.lean` (task height-split), its whole
`namespace ZInQ.HeightSplit.R5` block: the glue Prop `QMPairEmbeddingCorrespondence` (never
restated), the leaf `EichlerOptimalEmbeddingCount` and `r5fpCount_of`. §1 onward is new. -/

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

/-! ## §1. Shimura's half planes `ℂ ∖ ℝ` for `B = (2, −3)_ℚ` -/

namespace ZInQ.HeightGlue.QM

open LeafQM LeafQM.AV NumberField ZInQ.HeightSplit.R5 Matrix

/-- The real splitting `B ⊗ ℝ ≅ M₂(ℝ)` (inside `M₂(ℂ)`): `i ↦ diag(√2, −√2)`,
`j ↦ [[0, −3], [1, 0]]` (`i² = 2`, `j² = −3`, `ji = −ij`). -/
noncomputable def rhoBasis : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℂ) (2 : ℚ) 0 (-3) where
  i := !![(Real.sqrt 2 : ℂ), 0; 0, -(Real.sqrt 2 : ℂ)]
  j := !![0, -3; 1, 0]
  k := !![(Real.sqrt 2 : ℂ), 0; 0, -(Real.sqrt 2 : ℂ)] * !![0, -3; 1, 0]
  i_mul_i := by
    have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, h, Matrix.smul_apply]
  j_mul_j := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.smul_apply]
  i_mul_j := rfl
  j_mul_i := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, mul_comm]

/-- `ρ : B → M₂(ℂ)`, the real splitting. -/
noncomputable def rho : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℂ := rhoBasis.liftHom

/-- `ℂ ∖ ℝ = ℍ⁺ ∪ ℍ⁻`. -/
def HalfPlanes : Type := {τ : ℂ // τ.im ≠ 0}

/-- `τ ~ τ'` iff `ρ(u)·(τ, 1)ᵀ = c·(τ', 1)ᵀ` for some `u ∈ 𝒪^×` and `c ∈ ℂ^×`, i.e. `τ' = u·τ`
for the Möbius action of `ρ(𝒪^×) ⊆ GL₂(ℝ)` on `ℂ ∖ ℝ`. -/
def cmRel (τ τ' : HalfPlanes) : Prop :=
  ∃ (u : (↥O)ˣ) (c : ℂ), c ≠ 0 ∧ rho ((u : ↥O) : B) *ᵥ ![τ.1, 1] = c • ![τ'.1, 1]

theorem rho_unit_inv_mul (u : (↥O)ˣ) :
    rho (((u⁻¹ : (↥O)ˣ) : ↥O) : B) * rho ((u : ↥O) : B) = 1 := by
  rw [← map_mul, ← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Subring.coe_one, map_one]

/-- The orbit relation of `𝒪^×` on `ℂ ∖ ℝ`. -/
def cmSetoid : Setoid HalfPlanes where
  r := cmRel
  iseqv := by
    refine ⟨fun τ => ⟨1, 1, one_ne_zero, by simp⟩, fun {τ τ'} ⟨u, c, hc, h⟩ => ?_,
      fun {τ τ' τ''} ⟨u, c, hc, h⟩ ⟨v, d, hd, h'⟩ => ?_⟩
    · refine ⟨u⁻¹, c⁻¹, inv_ne_zero hc, ?_⟩
      have := congrArg (fun w => rho (((u⁻¹ : (↥O)ˣ) : ↥O) : B) *ᵥ w) h
      simp only [mulVec_mulVec, rho_unit_inv_mul, one_mulVec, mulVec_smul] at this
      rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
    · refine ⟨v * u, d * c, mul_ne_zero hd hc, ?_⟩
      rw [Units.val_mul, Subring.coe_mul, map_mul, ← mulVec_mulVec, h, mulVec_smul, h', smul_smul,
        mul_comm]

/-- **The CM order at `τ`**: `𝒪_τ = {b ∈ 𝒪 : (τ, 1)ᵀ is an eigenvector of ρ(b)}` (`= ℤ` unless `τ`
is a CM point). For the QM torus `A_τ = ℂ²/ρ(𝒪)(τ, 1)ᵀ`, `End_𝒪(A_τ) ≅ 𝒪_τ` via the eigenvalue. -/
def ordAt (τ : ℂ) : Subring B where
  carrier := {b | b ∈ O ∧ ∃ c : ℂ, rho b *ᵥ ![τ, 1] = c • ![τ, 1]}
  mul_mem' := by
    rintro a b ⟨ha, c, hc⟩ ⟨hb, d, hd⟩
    exact ⟨O.mul_mem ha hb, d * c, by
      rw [map_mul, ← mulVec_mulVec, hd, mulVec_smul, hc, smul_smul]⟩
  one_mem' := ⟨O.one_mem, 1, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, c, hc⟩ ⟨hb, d, hd⟩
    exact ⟨O.add_mem ha hb, c + d, by rw [map_add, add_mulVec, hc, hd, add_smul]⟩
  zero_mem' := ⟨O.zero_mem, 0, by simp⟩
  neg_mem' := by
    rintro a ⟨ha, c, hc⟩
    exact ⟨O.neg_mem ha, -c, by rw [map_neg, neg_mulVec, hc, neg_smul]⟩


/-! ## §2. The three Props -/

/-- **LEAF `QMUniformizationC` (Shimura's moduli interpretation of `𝒪^× \ (ℂ ∖ ℝ)`).**
G. Shimura, *On analytic families of polarized abelian varieties and automorphic functions*,
Ann. of Math. 78 (1963), §§2-4; K. Hashimoto, Osaka J. Math. 32 (1995) (explicit splitting and
normalized lattices); V. Rotger, Trans. AMS 356 (2004) (forgetting the polarization); J. Voight,
*Quaternion algebras*, GTM 288 (2021), Ch. 43; locators UNVERIFIED. Not one printed statement: the
published forms are for principally polarized surfaces and `𝒪¹ \ ℍ`; this leaf bundles with them
the standard facts that QM tori are algebraic, GAGA for homomorphisms, and the passage to the
unpolarized `𝒪^×` form (independent review, RISK). For the maximal order `𝒪` of the indefinite algebra `B = (2, −3)_ℚ`
(discriminant `6`, class number one): every QM abelian surface `(A, ι)` over `ℂ` is
`A_τ = ℂ²/ρ(𝒪)(τ, 1)ᵀ` with `ι(b) = ρ(b)`, for some `τ ∈ ℂ ∖ ℝ` (`H₁(A, ℤ)` is a free rank-one
`𝒪`-module, and `QM tori are algebraic`); `A_τ ≅ A_τ'` compatibly with `ι` iff `τ' ∈ 𝒪^×·τ`; and
`End_𝒪(A_τ) ≅ 𝒪_τ` (an `𝒪`-linear endomorphism is a scalar `λ` with `λ(τ,1)ᵀ ∈ ρ(𝒪)(τ,1)ᵀ`).
Stated as: an equivalence of the isomorphism classes of QM pairs over `ℂ` (the kernel's
`pairSetoid ℂ`) with the `𝒪^×`-orbits on `ℂ ∖ ℝ`, matching `com` with `ordAt`. -/
def QMUniformizationC : Prop :=
  ∃ Ψ : Quotient (pairSetoid ℂ) ≃ Quotient cmSetoid,
    ∀ (P : QMPair ℂ) (τ : HalfPlanes), Ψ (Quotient.mk _ P) = Quotient.mk _ τ →
      Nonempty (com P.q ≃+* ordAt τ.1)

/-- **LEAF `QMDescentCM` (CM QM pairs over `ℂ` come from `ℚ̄`, rigidity).** For an embedding
`ε : ℚ̄ → ℂ`, base change of QM pairs (the kernel's relation `IsBaseChangeOfPair`):
(a) exists; (b) preserves `End_𝒪` up to isomorphism and (c) reflects and preserves isomorphism
(rigidity: `Hom_ℚ̄ = Hom_ℂ`, Conrad 2006 §3 / the kernel's `T11b_Rigidity`); (d) a QM pair over
`ℂ` whose `End_𝒪` is an imaginary quadratic order is a base change from `ℚ̄` (abelian varieties
with CM, and their endomorphisms, are defined over `ℚ̄`: Shimura–Taniyama 1961, §12.4 Prop. 26;
locators UNVERIFIED). (d) is stated only for the orders of the target. -/
def QMDescentCM : Prop :=
  ∃ ε : Qbar →+* ℂ,
    (∀ P : QMPair Qbar, ∃ Q : QMPair ℂ, IsBaseChangeOfPair ε P Q) ∧
    (∀ (P : QMPair Qbar) (Q : QMPair ℂ), IsBaseChangeOfPair ε P Q →
      Nonempty (com Q.q ≃+* com P.q)) ∧
    (∀ (P P' : QMPair Qbar) (Q Q' : QMPair ℂ), IsBaseChangeOfPair ε P Q →
      IsBaseChangeOfPair ε P' Q' → (Nonempty (QMIso Q.q Q'.q) ↔ Nonempty (QMIso P.q P'.q))) ∧
    (∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
      Module.finrank ℚ k = 2 →
      ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      ∀ Q : QMPair ℂ, Nonempty (com Q.q ≃+* R) → ∃ P : QMPair Qbar, IsBaseChangeOfPair ε P Q)

variable (k : Type) [Field k]

/-- The classes of QM pairs over `ℂ` with `End_𝒪 ≅ R`. -/
def QMClassesC (R : Subring k) : Type 1 :=
  {c : Quotient (pairSetoid ℂ) // ∃ Q : QMPair ℂ, Quotient.mk _ Q = c ∧ Nonempty (com Q.q ≃+* R)}

/-- The `𝒪^×`-orbits of CM points `τ ∈ ℂ ∖ ℝ` with `𝒪_τ ≅ R`. -/
def CMPoints (R : Subring k) : Type :=
  {c : Quotient cmSetoid // ∃ τ : HalfPlanes, Quotient.mk _ τ = c ∧ Nonempty (ordAt τ.1 ≃+* R)}

/-- **GLUE `CMPointEmbeddingCorrespondence` (normalized optimal embeddings; quaternion
arithmetic).** The `𝒪^×`-orbits of points `τ ∈ ℂ ∖ ℝ` with `𝒪_τ ≅ R` are in bijection with the
optimal embeddings `R ↪ 𝒪` modulo `𝒪^×`. Why true: for such `τ`, `B_τ = ℚ𝒪_τ` is a quadratic field
`≅ k`, and the eigenvalue `b ↦ λ_b` (`ρ(b)(τ,1)ᵀ = λ_b(τ,1)ᵀ`) is a ring embedding `B_τ ↪ ℂ`; fixing
an embedding `σ₀ : k ↪ ℂ`, the *normalized* embedding `φ_τ : k → B` with `λ ∘ φ_τ = σ₀` is unique
and optimal (`φ_τ⁻¹(𝒪) = R`: an order of `k` abstractly isomorphic to `R` equals `R`, orders being
stable under conjugation); `φ_{u·τ} = u φ_τ u⁻¹`; conversely `φ(k^×)` acting on `ℂ ∖ ℝ` has exactly
two fixed points `τ, τ̄`, exactly one of them with `λ ∘ φ = σ₀`. (Shimura 1967; Voight GTM 288,
§30.4 and Ch. 43; locators UNVERIFIED.) Unproved here. -/
def CMPointEmbeddingCorrespondence : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      Nonempty (CMPoints k R ≃ Quotient (embSetoid k R))

/-! ## §3. The reduction (proved) -/

/-- **Descent of classes**: `QMDescentCM` gives `QMClasses k R ≃ QMClassesC k R`. -/
theorem nonempty_qmClasses_equiv (hD : QMDescentCM) [NumberField k]
    [NumberField.IsTotallyComplex k] (hk : Module.finrank ℚ k = 2) (R : Subring k)
    (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6) :
    Nonempty (QMClasses k R ≃ QMClassesC k R) := by
  classical
  obtain ⟨ε, hex, hcom, hiso, hdesc⟩ := hD
  choose bc hbc using hex
  let f : Quotient (pairSetoid Qbar) → Quotient (pairSetoid ℂ) :=
    Quotient.lift (fun P => Quotient.mk (pairSetoid ℂ) (bc P)) (fun P P' hPP' =>
      Quotient.sound ((hiso P P' (bc P) (bc P') (hbc P) (hbc P')).mpr hPP'))
  have hf : ∀ P, f (Quotient.mk _ P) = Quotient.mk _ (bc P) := fun P => rfl
  have hfi : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with | h P => ?_
    induction y using Quotient.inductionOn with | h P' => ?_
    rw [hf, hf] at hxy
    exact Quotient.sound ((hiso P P' (bc P) (bc P') (hbc P) (hbc P')).mp (Quotient.exact hxy))
  let F : QMClasses k R → QMClassesC k R := fun c => ⟨f c.1, by
    obtain ⟨P, hP, ⟨e⟩⟩ := c.2
    obtain ⟨e'⟩ := hcom P (bc P) (hbc P)
    exact ⟨bc P, by rw [← hP, hf], ⟨e'.trans e⟩⟩⟩
  refine ⟨Equiv.ofBijective F ⟨fun c d hcd => Subtype.ext (hfi (congrArg Subtype.val hcd)), ?_⟩⟩
  rintro ⟨c', Q, hQ, ⟨e⟩⟩
  obtain ⟨P, hPQ⟩ := hdesc k hk R hR hc Q ⟨e⟩
  obtain ⟨e'⟩ := hcom P Q hPQ
  refine ⟨⟨Quotient.mk _ P, P, rfl, ⟨e'.symm.trans e⟩⟩, Subtype.ext ?_⟩
  show f (Quotient.mk _ P) = c'
  rw [hf, ← hQ]
  exact Quotient.sound ((hiso P P (bc P) Q (hbc P) hPQ).mpr ⟨QMIso.refl P.q⟩)

/-- **Uniformization of classes**: `QMUniformizationC` gives `QMClassesC k R ≃ CMPoints k R`. -/
theorem nonempty_qmClassesC_equiv (hU : QMUniformizationC) (R : Subring k) :
    Nonempty (QMClassesC k R ≃ CMPoints k R) := by
  obtain ⟨Ψ, hΨ⟩ := hU
  refine ⟨Equiv.subtypeEquiv Ψ fun c => ⟨?_, ?_⟩⟩
  · rintro ⟨Q, rfl, ⟨e⟩⟩
    obtain ⟨τ, hτ⟩ := Quotient.exists_rep (Ψ (Quotient.mk _ Q))
    obtain ⟨e'⟩ := hΨ Q τ hτ.symm
    exact ⟨τ, hτ, ⟨e'.symm.trans e⟩⟩
  · rintro ⟨τ, hτ, ⟨e⟩⟩
    obtain ⟨Q, hQ⟩ := Quotient.exists_rep c
    subst hQ
    obtain ⟨e'⟩ := hΨ Q τ hτ.symm
    exact ⟨Q, rfl, ⟨e'.trans e⟩⟩

/-- **height-split's glue `QMPairEmbeddingCorrespondence` from the leaves `QMDescentCM`,
`QMUniformizationC` and the glue `CMPointEmbeddingCorrespondence`** (proved). -/
theorem qmPairEmbeddingCorrespondence_of (hD : QMDescentCM) (hU : QMUniformizationC)
    (hC : CMPointEmbeddingCorrespondence) : QMPairEmbeddingCorrespondence := by
  intro k _ _ _ hk R hR hc
  obtain ⟨e₁⟩ := nonempty_qmClasses_equiv k hD hk R hR hc
  obtain ⟨e₂⟩ := nonempty_qmClassesC_equiv k hU R
  obtain ⟨e₃⟩ := hC k hk R hR hc
  exact ⟨(e₁.trans e₂).trans e₃⟩

end ZInQ.HeightGlue.QM


/-! ## §4. Toward `CMPointEmbeddingCorrespondence`: linear algebra of `ρ` -/

namespace ZInQ.HeightGlue.QM

open LeafQM LeafQM.AV NumberField ZInQ.HeightSplit.R5 Matrix ComplexConjugate

/-- `√2 ∈ ℂ`. -/
noncomputable abbrev s2 : ℂ := (Real.sqrt 2 : ℂ)

theorem s2_ne_zero : s2 ≠ 0 := by
  simp [s2]

theorem conj_s2 : conj s2 = s2 := Complex.conj_ofReal _

/-- The explicit matrix of `ρ(b)`. -/
theorem rho_apply (b : B) : rho b =
    !![(b.re : ℂ) + b.imI * s2, -3 * (b.imJ : ℂ) - 3 * s2 * b.imK;
      (b.imJ : ℂ) - s2 * b.imK, (b.re : ℂ) - b.imI * s2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, rhoBasis, QuaternionAlgebra.Basis.lift, Matrix.mul_apply,
      Algebra.algebraMap_eq_smul_one, Rat.smul_def] <;> ring

/-- The entries of `ρ(b)` are real. -/
theorem conj_rho (b : B) (i j : Fin 2) : conj (rho b i j) = rho b i j := by
  rw [rho_apply]
  fin_cases i <;> fin_cases j <;> simp [map_add, map_sub, map_mul, map_ofNat]

/-- `ρ` is injective. -/
theorem rho_eq_zero {b : B} (h : rho b = 0) : b = 0 := by
  rw [rho_apply] at h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp at e00 e01 e10 e11
  have hre : (b.re : ℂ) = 0 := by linear_combination (e00 + e11) / 2
  have hI : (b.imI : ℂ) * s2 = 0 := by linear_combination (e00 - e11) / 2
  have hJ : (b.imJ : ℂ) = 0 := by linear_combination (e10 * 3 - e01) / 6
  have hK : s2 * (b.imK : ℂ) = 0 := by linear_combination (-e10 * 3 - e01) / 6
  have hI' : (b.imI : ℂ) = 0 := (mul_eq_zero.mp hI).resolve_right s2_ne_zero
  have hK' : (b.imK : ℂ) = 0 := (mul_eq_zero.mp hK).resolve_left s2_ne_zero
  ext <;> simp_all

theorem rho_injective : Function.Injective rho := fun a b h =>
  sub_eq_zero.mp (rho_eq_zero (by rw [map_sub, h, sub_self]))

/-- The eigenvector equation for `(τ, 1)ᵀ`, coordinatewise. -/
theorem eig_iff (M : Matrix (Fin 2) (Fin 2) ℂ) (τ μ : ℂ) :
    M *ᵥ ![τ, 1] = μ • ![τ, 1] ↔ M 0 0 * τ + M 0 1 = μ * τ ∧ M 1 0 * τ + M 1 1 = μ := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, h0, h1]

/-- The complex conjugate eigenvector. -/
theorem eig_conj {b : B} {τ μ : ℂ} (h : rho b *ᵥ ![τ, 1] = μ • ![τ, 1]) :
    rho b *ᵥ ![conj τ, 1] = conj μ • ![conj τ, 1] := by
  rw [eig_iff] at h ⊢
  obtain ⟨h0, h1⟩ := h
  have c0 := congrArg conj h0
  have c1 := congrArg conj h1
  simp only [map_add, map_mul, conj_rho] at c0 c1
  exact ⟨c0, c1⟩

/-- A matrix killing `(τ, 1)ᵀ` and `(τ̄, 1)ᵀ`, `τ ∉ ℝ`, is zero. -/
theorem eq_zero_of_kill (N : Matrix (Fin 2) (Fin 2) ℂ) {τ : ℂ} (hτ : τ.im ≠ 0)
    (h1 : N *ᵥ ![τ, 1] = 0) (h2 : N *ᵥ ![conj τ, 1] = 0) : N = 0 := by
  have h1' : N *ᵥ ![τ, 1] = (0 : ℂ) • ![τ, 1] := by rw [h1, zero_smul]
  have h2' : N *ᵥ ![conj τ, 1] = (0 : ℂ) • ![conj τ, 1] := by rw [h2, zero_smul]
  rw [eig_iff] at h1' h2'
  have hne : τ - conj τ ≠ 0 := by
    intro h
    apply hτ
    have := congrArg Complex.im h
    simp [Complex.sub_im, Complex.conj_im] at this
    linarith
  have a00 : N 0 0 = 0 := by
    have : N 0 0 * (τ - conj τ) = 0 := by linear_combination h1'.1 - h2'.1
    exact (mul_eq_zero.mp this).resolve_right hne
  have a10 : N 1 0 = 0 := by
    have : N 1 0 * (τ - conj τ) = 0 := by linear_combination h1'.2 - h2'.2
    exact (mul_eq_zero.mp this).resolve_right hne
  have a01 : N 0 1 = 0 := by linear_combination h1'.1 - τ * a00
  have a11 : N 1 1 = 0 := by linear_combination h1'.2 - τ * a10
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a00, a01, a10, a11]

/-- **Same eigenvalue at `(τ, 1)ᵀ`, `τ ∉ ℝ`, means equal.** -/
theorem eq_of_eig {a b : B} {τ μ : ℂ} (hτ : τ.im ≠ 0) (ha : rho a *ᵥ ![τ, 1] = μ • ![τ, 1])
    (hb : rho b *ᵥ ![τ, 1] = μ • ![τ, 1]) : a = b := by
  apply sub_eq_zero.mp
  apply rho_eq_zero
  apply eq_zero_of_kill _ hτ
  · rw [map_sub, sub_mulVec, ha, hb, sub_self]
  · rw [map_sub, sub_mulVec, eig_conj ha, eig_conj hb, sub_self]

/-- Two elements with `(τ, 1)ᵀ` as common eigenvector commute (`τ ∉ ℝ`). -/
theorem commute_of_eig {a b : B} {τ μ ν : ℂ} (hτ : τ.im ≠ 0)
    (ha : rho a *ᵥ ![τ, 1] = μ • ![τ, 1]) (hb : rho b *ᵥ ![τ, 1] = ν • ![τ, 1]) :
    a * b = b * a := by
  have hab : rho (a * b) *ᵥ ![τ, 1] = (ν * μ) • ![τ, 1] := by
    rw [map_mul, ← mulVec_mulVec, hb, mulVec_smul, ha, smul_smul]
  have hba : rho (b * a) *ᵥ ![τ, 1] = (ν * μ) • ![τ, 1] := by
    rw [map_mul, ← mulVec_mulVec, ha, mulVec_smul, hb, smul_smul, mul_comm]
  exact eq_of_eig hτ hab hba

/-- **The centralizer of a non-scalar element `β` of `B` is `ℚ + ℚβ`.** -/
theorem exists_eq_of_commute {β b : B} (hβ : ∀ r : ℚ, β ≠ (r : B)) (h : b * β = β * b) :
    ∃ r t : ℚ, b = (r : B) + t • β := by
  have e := congrArg (fun x : B => (x.imI, x.imJ, x.imK)) h
  simp only [QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  -- the pure parts are parallel: `b.imJ β.imK = b.imK β.imJ` etc.
  have p1 : b.imJ * β.imK = b.imK * β.imJ := by nlinarith
  have p2 : b.imI * β.imK = b.imK * β.imI := by nlinarith
  have p3 : b.imI * β.imJ = b.imJ * β.imI := by nlinarith
  have hpure : β.imI ≠ 0 ∨ β.imJ ≠ 0 ∨ β.imK ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hβ β.re
    ext <;> simp [hc.1, hc.2.1, hc.2.2]
  rcases hpure with h1 | h1 | h1
  · refine ⟨b.re - b.imI / β.imI * β.re, b.imI / β.imI, ?_⟩
    ext <;> simp <;> field_simp <;> linarith
  · refine ⟨b.re - b.imJ / β.imJ * β.re, b.imJ / β.imJ, ?_⟩
    ext <;> simp <;> field_simp <;> linarith
  · refine ⟨b.re - b.imK / β.imK * β.re, b.imK / β.imK, ?_⟩
    ext <;> simp <;> field_simp <;> linarith


/-! ## §5. The imaginary quadratic field: coordinates, lifts, conjugation -/

section Field

variable {k : Type} [Field k] [NumberField k]

/-- Every element of a quadratic field is `r + s y` for a non-rational `y`. -/
theorem exists_rat_repr (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (x : k) :
    ∃ r s : ℚ, x = r + s * y := by
  have hli : LinearIndependent ℚ ![(1 : k), y] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at h
      exact ⟨h, rfl⟩
    · exfalso
      apply hy (-a / t)
      rw [Rat.smul_def, Rat.smul_def, mul_one] at h
      push_cast
      field_simp
      linear_combination h
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [hk])
  have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : k), y]) := hsp ▸ Submodule.mem_top
  have hr : Set.range ![(1 : k), y] = {1, y} := by
    ext z; simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hr] at hx
  obtain ⟨r, t, hrt⟩ := Submodule.mem_span_pair.mp hx
  exact ⟨r, t, by rw [← hrt, Rat.smul_def, Rat.smul_def, mul_one]⟩

theorem repr_unique {y : k} (hy : ∀ r : ℚ, y ≠ r) {r s r' s' : ℚ}
    (h : (r : k) + s * y = r' + s' * y) : r = r' ∧ s = s' := by
  by_cases hs : s = s'
  · subst hs
    refine ⟨?_, rfl⟩
    exact_mod_cast add_right_cancel h
  · exfalso
    apply hy ((r' - r) / (s - s'))
    have hs' : ((s : k) - s') ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hs
    push_cast
    field_simp
    linear_combination h

/-- The coordinates of `x` in the basis `(1, y)`. -/
noncomputable def coord0 (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (x : k) : ℚ :=
  (exists_rat_repr hk hy x).choose

noncomputable def coord1 (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (x : k) : ℚ :=
  (exists_rat_repr hk hy x).choose_spec.choose

theorem coord_spec (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (x : k) :
    x = (coord0 hk hy x : k) + (coord1 hk hy x : k) * y :=
  (exists_rat_repr hk hy x).choose_spec.choose_spec

theorem coord_eq (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (r s : ℚ) :
    coord0 hk hy ((r : k) + s * y) = r ∧ coord1 hk hy ((r : k) + s * y) = s :=
  repr_unique hy (coord_spec hk hy _).symm

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- **The `ℚ`-algebra map `k → A` sending a non-rational `y` (root of `X² + PX + Q`) to a root `b`
of the same polynomial**, `r + s y ↦ r + s b`. -/
noncomputable def liftQuad (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r)
    {P Q : ℚ} (hyq : y * y + P * y + Q = 0) (b : A)
    (hb : b * b + P • b + algebraMap ℚ A Q = 0) : k →ₐ[ℚ] A :=
  let F : k → A := fun x => algebraMap ℚ A (coord0 hk hy x) + coord1 hk hy x • b
  have hF : ∀ r s : ℚ, F ((r : k) + s * y) = algebraMap ℚ A r + s • b := fun r s => by
    simp only [F, (coord_eq hk hy r s).1, (coord_eq hk hy r s).2]
  have hx := coord_spec hk hy
  { toFun := F
    map_one' := by
      have : (1 : k) = ((1 : ℚ) : k) + ((0 : ℚ) : k) * y := by push_cast; ring
      rw [this, hF]; simp
    map_mul' := fun x x' => by
      rw [hx x, hx x']
      set r := coord0 hk hy x; set s := coord1 hk hy x
      set r' := coord0 hk hy x'; set s' := coord1 hk hy x'
      have e : ((r : k) + s * y) * ((r' : k) + s' * y) =
          ((r * r' - s * s' * Q : ℚ) : k) + ((r * s' + r' * s - s * s' * P : ℚ) : k) * y := by
        push_cast; linear_combination (s * s' : k) * hyq
      rw [e, hF, hF, hF]
      have hb' : b * b = -(P • b) - Q • (1 : A) := by
        rw [Algebra.algebraMap_eq_smul_one] at hb
        rw [← sub_eq_zero, ← hb]; abel
      simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one, smul_smul, hb', smul_sub, smul_neg]
      module
    map_zero' := by
      have : (0 : k) = ((0 : ℚ) : k) + ((0 : ℚ) : k) * y := by push_cast; ring
      rw [this, hF]; simp
    map_add' := fun x x' => by
      rw [hx x, hx x']
      have e : ((coord0 hk hy x : k) + coord1 hk hy x * y) +
          ((coord0 hk hy x' : k) + coord1 hk hy x' * y) =
          ((coord0 hk hy x + coord0 hk hy x' : ℚ) : k) +
            ((coord1 hk hy x + coord1 hk hy x' : ℚ) : k) * y := by push_cast; ring
      rw [e, hF, hF, hF, map_add, add_smul]; abel
    commutes' := fun r => by
      have : (algebraMap ℚ k r) = (r : k) + ((0 : ℚ) : k) * y := by simp
      rw [this, hF]; simp }

theorem liftQuad_apply (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r)
    {P Q : ℚ} (hyq : y * y + P * y + Q = 0) (b : A)
    (hb : b * b + P • b + algebraMap ℚ A Q = 0) (r s : ℚ) :
    liftQuad hk hy hyq b hb ((r : k) + s * y) = algebraMap ℚ A r + s • b := by
  show algebraMap ℚ A (coord0 hk hy _) + coord1 hk hy _ • b = _
  rw [(coord_eq hk hy r s).1, (coord_eq hk hy r s).2]

theorem liftQuad_gen (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r)
    {P Q : ℚ} (hyq : y * y + P * y + Q = 0) (b : A)
    (hb : b * b + P • b + algebraMap ℚ A Q = 0) : liftQuad hk hy hyq b hb y = b := by
  have h := liftQuad_apply hk hy hyq b hb 0 1
  simp only [Rat.cast_zero, Rat.cast_one, zero_add, one_mul, map_zero, one_smul] at h
  exact h

end Field

/-! ## §6. Orders: integrality, a good generator, conjugation -/

section Order

variable {k : Type} [Field k] [NumberField k]

/-- A rational number integral over `ℤ` (in `k`) is an integer. -/
theorem exists_int_of_isIntegral {r : ℚ} (h : IsIntegral ℤ (r : k)) : ∃ n : ℤ, r = n := by
  have h' : IsIntegral ℤ r := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := k)]
    simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨n, by rw [← hn]; simp⟩

theorem isIntegral_of_mem {R : Subring k} (hR : R ≤ (integralClosure ℤ k).toSubring) {x : k}
    (hx : x ∈ R) : IsIntegral ℤ x := hR hx

/-- `R` contains an element outside `ℚ` (its conductor is finite). -/
theorem exists_mem_not_rat (hk : Module.finrank ℚ k = 2) (R : Subring k)
    (hc : Nat.Coprime (conductor R) 6) : ∃ x ∈ R, ∀ r : ℚ, x ≠ r := by
  by_contra hcon
  push_neg at hcon
  -- an element of `k` outside `ℚ`
  obtain ⟨z, hz⟩ : ∃ z : k, ∀ r : ℚ, z ≠ r := by
    by_contra h
    push_neg at h
    let bs := Module.finBasisOfFinrankEq ℚ k hk
    obtain ⟨r0, h0⟩ := h (bs 0)
    obtain ⟨r1, h1⟩ := h (bs 1)
    have hli := bs.linearIndependent
    rw [show (⇑bs : Fin 2 → k) = ![bs 0, bs 1] from by ext i; fin_cases i <;> rfl,
      LinearIndependent.pair_iff] at hli
    have hb0 : bs 0 ≠ 0 := bs.ne_zero 0
    have hr0 : r0 ≠ 0 := by rintro rfl; exact hb0 (by simpa using h0)
    have := hli r1 (-r0) (by rw [h0, h1, Rat.smul_def, Rat.smul_def]; push_cast; ring)
    exact hr0 (neg_eq_zero.mp this.2)
  -- an integral element outside `ℚ`
  obtain ⟨ω, hωi, hω⟩ : ∃ ω : k, IsIntegral ℤ ω ∧ ∀ r : ℚ, ω ≠ r := by
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 k) z
    by_cases ha : ∀ r : ℚ, (algebraMap (𝓞 k) k a) ≠ r
    · exact ⟨_, (a.2 : IsIntegral ℤ (a : k)), ha⟩
    by_cases hb' : ∀ r : ℚ, (algebraMap (𝓞 k) k b) ≠ r
    · exact ⟨_, (b.2 : IsIntegral ℤ (b : k)), hb'⟩
    exfalso
    push_neg at ha hb'
    obtain ⟨ra, hra⟩ := ha
    obtain ⟨rb, hrb⟩ := hb'
    apply hz (ra / rb)
    rw [← hab, hra, hrb]; push_cast; rfl
  -- the conductor is `0`
  have hidx : conductor R = 0 := by
    unfold LeafQM.AV.conductor AddSubgroup.relIndex AddSubgroup.index
    have hωK : ω ∈ (integralClosure ℤ k).toSubring.toAddSubgroup := hωi
    let w : (integralClosure ℤ k).toSubring.toAddSubgroup := ⟨ω, hωK⟩
    haveI : Infinite (_ ⧸ R.toAddSubgroup.addSubgroupOf
        (integralClosure ℤ k).toSubring.toAddSubgroup) := by
      refine Infinite.of_injective (fun m : ℕ => (QuotientAddGroup.mk (m • w) :
        _ ⧸ R.toAddSubgroup.addSubgroupOf (integralClosure ℤ k).toSubring.toAddSubgroup)) ?_
      intro m m' hmm
      simp only at hmm
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hmm
      obtain ⟨r, hr⟩ := hcon _ hmm
      by_contra hne
      apply hω (r / ((m' : ℚ) - m))
      have hsub : ((m' : k) - m) ≠ 0 := by
        rw [sub_ne_zero]; exact_mod_cast (Ne.symm hne)
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_nsmul, w,
        nsmul_eq_mul] at hr
      push_cast
      field_simp
      linear_combination hr
    exact Nat.card_eq_zero_of_infinite
  rw [hidx] at hc
  exact absurd ((Nat.coprime_zero_left 6).mp hc) (by norm_num)

theorem num_cast_eq (p : ℚ) : ((p.num : ℤ) : k) = (p : k) * (p.den : k) := by
  have := congrArg (fun z : ℚ => (z : k)) (Rat.mul_den_eq_num p)
  push_cast at this
  exact this.symm

/-- **A good generator**: `y ∈ R ∖ ℚ` with `y² + Py + Q = 0`, `P, Q ∈ ℤ`. -/
theorem exists_good_gen (hk : Module.finrank ℚ k = 2) (R : Subring k)
    (hc : Nat.Coprime (conductor R) 6) :
    ∃ y ∈ R, (∀ r : ℚ, y ≠ r) ∧ ∃ P Q : ℤ, y * y + P * y + Q = 0 := by
  obtain ⟨x, hxR, hx⟩ := exists_mem_not_rat hk R hc
  obtain ⟨r, t, hrt⟩ := exists_rat_repr hk hx (x * x)
  set p : ℚ := -t with hp
  set q : ℚ := -r with hq
  set m : ℕ := p.den * q.den with hm
  have hm0 : (m : k) ≠ 0 := by
    rw [hm]; push_cast
    exact mul_ne_zero (Nat.cast_ne_zero.mpr p.den_nz) (Nat.cast_ne_zero.mpr q.den_nz)
  refine ⟨(m : k) * x, R.mul_mem (natCast_mem R m) hxR, ?_, q.den * p.num,
    p.den ^ 2 * q.den * q.num, ?_⟩
  · intro r' h
    apply hx (r' / m)
    push_cast
    field_simp
    linear_combination h
  · push_cast
    rw [num_cast_eq p, num_cast_eq q, hm]
    push_cast
    rw [hp, hq]
    push_cast
    linear_combination ((p.den : k) * q.den) ^ 2 * hrt

variable [NumberField.IsTotallyComplex k]

/-- The value of an embedding at a non-rational root `y` of `X² + PX + Q` is not real. -/
theorem im_ne_zero_of_gen (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r)
    (σ : k →+* ℂ) : (σ y).im ≠ 0 := by
  intro him
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal σ
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext x
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  obtain ⟨r, t, rfl⟩ := exists_rat_repr hk hy x
  have hc : conj (σ y) = σ y := Complex.conj_eq_iff_im.mpr him
  simp [map_add, map_mul, hc, map_ratCast]

end Order

/-! ## §7. The roots `λ`, `λ̄` -/

section Roots

variable {P Q : ℂ} {lam : ℂ}

theorem vieta (hl : lam * lam + P * lam + Q = 0) (hP : conj P = P) (hQ : conj Q = Q)
    (him : lam.im ≠ 0) : lam + conj lam = -P ∧ lam * conj lam = Q := by
  have hc : conj lam * conj lam + P * conj lam + Q = 0 := by
    have := congrArg conj hl
    simpa [map_add, map_mul, hP, hQ] using this
  have hne : lam - conj lam ≠ 0 := by
    intro h
    apply him
    have := congrArg Complex.im h
    simp [Complex.sub_im, Complex.conj_im] at this
    linarith
  have hsum : lam + conj lam = -P := by
    have : (lam - conj lam) * (lam + conj lam + P) = 0 := by linear_combination hl - hc
    linear_combination (mul_eq_zero.mp this).resolve_left hne
  refine ⟨hsum, ?_⟩
  linear_combination lam * hsum - hl

theorem eq_or_eq_conj (hl : lam * lam + P * lam + Q = 0) (hP : conj P = P) (hQ : conj Q = Q)
    (him : lam.im ≠ 0) {z : ℂ} (hz : z * z + P * z + Q = 0) : z = lam ∨ z = conj lam := by
  obtain ⟨h1, h2⟩ := vieta hl hP hQ him
  have : (z - lam) * (z - conj lam) = 0 := by linear_combination hz - z * h1 + h2
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

theorem not_real_root (hl : lam * lam + P * lam + Q = 0) (hP : conj P = P) (hQ : conj Q = Q)
    (him : lam.im ≠ 0) {z : ℂ} (hz : z * z + P * z + Q = 0) (hzr : conj z = z) : False := by
  rcases eq_or_eq_conj hl hP hQ him hz with h | h
  · apply him; rw [← h]; exact Complex.conj_eq_iff_im.mp hzr
  · apply him
    have : conj z = lam := by rw [h, Complex.conj_conj]
    rw [← this, hzr, h, Complex.conj_im]
    have := Complex.conj_eq_iff_im.mp (h ▸ hzr : conj (conj lam) = conj lam)
    simpa using this

end Roots

/-! ## §8. The normalized fixed point of an embedding `k → B` -/

/-- The data fixed once and for all: a non-rational root `y` of `X² + PX + Q` (`P, Q ∈ ℤ`) and an
embedding `σ : k → ℂ`. -/
structure Gen (k : Type) [Field k] where
  y : k
  hy : ∀ r : ℚ, y ≠ r
  P : ℤ
  Q : ℤ
  hq : y * y + P * y + Q = 0
  σ : k →+* ℂ

section FixedPoint

variable {k : Type} [Field k] [NumberField k] [NumberField.IsTotallyComplex k]
variable (hk : Module.finrank ℚ k = 2) (G : Gen k)

/-- `λ = σ(y)`. -/
noncomputable def Gen.lam : ℂ := G.σ G.y

theorem Gen.lam_quad : G.lam * G.lam + (G.P : ℂ) * G.lam + G.Q = 0 := by
  have := congrArg G.σ G.hq
  simpa [Gen.lam, map_add, map_mul, map_intCast] using this

include hk in
theorem Gen.lam_im : G.lam.im ≠ 0 := im_ne_zero_of_gen hk G.hy G.σ

theorem conj_intCast' (n : ℤ) : conj (n : ℂ) = n := by simp

/-- The two entry equations of `ρ(φ y)² + P ρ(φ y) + Q = 0`. -/
theorem phi_entries (φ : k →ₐ[ℚ] B) :
    rho (φ G.y) 0 0 * rho (φ G.y) 0 0 + rho (φ G.y) 0 1 * rho (φ G.y) 1 0 +
        G.P * rho (φ G.y) 0 0 + G.Q = 0 ∧
      rho (φ G.y) 1 0 * rho (φ G.y) 0 0 + rho (φ G.y) 1 1 * rho (φ G.y) 1 0 +
        G.P * rho (φ G.y) 1 0 = 0 := by
  have h := congrArg (fun x => rho (φ x)) G.hq
  simp only [map_add, map_mul, map_intCast, map_zero] at h
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.intCast_apply] at h00 h10
  exact ⟨by linear_combination h00, by linear_combination h10⟩

include hk in
theorem phi_c_ne_zero (φ : k →ₐ[ℚ] B) : rho (φ G.y) 1 0 ≠ 0 := by
  intro hc
  have h00 := (phi_entries G φ).1
  rw [hc, mul_zero, add_zero] at h00
  exact not_real_root G.lam_quad (conj_intCast' _) (conj_intCast' _) (G.lam_im hk) h00
    (conj_rho _ 0 0)

/-- **The normalized fixed point** `τ_φ = (λ − d)/c` of `ρ(φ(k^×))`. -/
noncomputable def fpt (φ : k →ₐ[ℚ] B) : ℂ := (G.lam - rho (φ G.y) 1 1) / rho (φ G.y) 1 0

include hk in
theorem fpt_eig_gen (φ : k →ₐ[ℚ] B) :
    rho (φ G.y) *ᵥ ![fpt G φ, 1] = G.lam • ![fpt G φ, 1] := by
  have hc := phi_c_ne_zero hk G φ
  obtain ⟨e00, e10⟩ := phi_entries G φ
  have hsum : rho (φ G.y) 0 0 + rho (φ G.y) 1 1 + G.P = 0 := by
    have : rho (φ G.y) 1 0 * (rho (φ G.y) 0 0 + rho (φ G.y) 1 1 + G.P) = 0 := by
      linear_combination e10
    exact (mul_eq_zero.mp this).resolve_left hc
  rw [eig_iff]
  unfold fpt
  constructor
  · field_simp
    linear_combination e00 - G.lam_quad + (G.lam - rho (φ G.y) 0 0) * hsum
  · field_simp
    ring

include hk in
theorem fpt_im (φ : k →ₐ[ℚ] B) : (fpt G φ).im ≠ 0 := by
  intro h
  have hr : conj (fpt G φ) = fpt G φ := Complex.conj_eq_iff_im.mpr h
  have h2 := ((eig_iff _ _ _).mp (fpt_eig_gen hk G φ)).2
  apply G.lam_im hk
  apply Complex.conj_eq_iff_im.mp
  rw [← h2]
  simp only [map_add, map_mul, conj_rho, hr]

include hk in
theorem fpt_unique (φ : k →ₐ[ℚ] B) {τ : ℂ} (h : rho (φ G.y) *ᵥ ![τ, 1] = G.lam • ![τ, 1]) :
    τ = fpt G φ := by
  have hc := phi_c_ne_zero hk G φ
  have h2 := ((eig_iff _ _ _).mp h).2
  unfold fpt
  field_simp
  linear_combination h2

include hk in
/-- `ρ(φ x)(τ_φ, 1)ᵀ = σ(x)(τ_φ, 1)ᵀ` for every `x ∈ k`. -/
theorem fpt_eig (φ : k →ₐ[ℚ] B) (x : k) :
    rho (φ x) *ᵥ ![fpt G φ, 1] = G.σ x • ![fpt G φ, 1] := by
  obtain ⟨r, t, rfl⟩ := exists_rat_repr hk G.hy x
  have hφ : φ ((r : k) + t * G.y) = algebraMap ℚ B r + t • φ G.y := by
    rw [map_add, map_mul, ← map_ratCast (algebraMap ℚ k) r, AlgHom.commutes,
      ← map_ratCast (algebraMap ℚ k) t, AlgHom.commutes, Algebra.smul_def]
    simp
  rw [hφ, map_add, map_smul, AlgHom.commutes, add_mulVec, smul_mulVec, fpt_eig_gen hk G φ,
    Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec]
  have hσ : G.σ ((r : k) + t * G.y) = (r : ℂ) + (t : ℂ) * G.lam := by
    simp [Gen.lam, map_ratCast]
  rw [hσ, add_smul, mul_smul, Rat.cast_smul_eq_qsmul, Rat.cast_smul_eq_qsmul]

end FixedPoint

/-! ## §9. Optimal embeddings and CM points -/

section Corr

variable {k : Type} [Field k] [NumberField k] [NumberField.IsTotallyComplex k]
variable (hk : Module.finrank ℚ k = 2) (G : Gen k)

theorem phi_ratCast (φ : k →ₐ[ℚ] B) (r : ℚ) : φ (r : k) = (r : B) := by
  rw [← map_ratCast (algebraMap ℚ k) r, AlgHom.commutes, QuaternionAlgebra.coe_algebraMap]
  simp

theorem phi_repr (φ : k →ₐ[ℚ] B) (r t : ℚ) : φ ((r : k) + t * G.y) = (r : B) + t • φ G.y := by
  rw [map_add, map_mul, phi_ratCast, phi_ratCast, ← QuaternionAlgebra.coe_algebraMap,
    ← Algebra.smul_def]

theorem phi_y_not_scalar (φ : k →ₐ[ℚ] B) : ∀ r : ℚ, φ G.y ≠ (r : B) := by
  intro r h
  apply G.hy r
  apply φ.toRingHom.injective
  show φ G.y = φ (r : k)
  rw [h, phi_ratCast]

include hk in
/-- **(i)** For an optimal `φ`, `𝒪_{τ_φ} = φ(R) ≅ R`. -/
theorem nonempty_ordAt_fpt (R : Subring k) (φ : k →ₐ[ℚ] B) (hopt : ∀ x, φ x ∈ O ↔ x ∈ R) :
    Nonempty (ordAt (fpt G φ) ≃+* R) := by
  let f : R →+* ordAt (fpt G φ) :=
    { toFun := fun x => ⟨φ x, (hopt x).mpr x.2, G.σ x, fpt_eig hk G φ x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (φ.toRingHom.injective (congrArg Subtype.val hab))
  have hsurj : Function.Surjective f := by
    rintro ⟨b, hbO, μ, hμ⟩
    have hcomm := commute_of_eig (fpt_im hk G φ) hμ (fpt_eig_gen hk G φ)
    obtain ⟨r, t, hrt⟩ := exists_eq_of_commute (phi_y_not_scalar G φ) hcomm
    have hφx : φ ((r : k) + t * G.y) = b := by rw [phi_repr, hrt]
    have hxR : (r : k) + t * G.y ∈ R := (hopt _).mp (hφx ▸ hbO)
    exact ⟨⟨_, hxR⟩, Subtype.ext hφx⟩
  exact ⟨(RingEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

theorem rho_unit_mul_inv (u : (↥O)ˣ) :
    rho ((u : ↥O) : B) * rho (((u⁻¹ : (↥O)ˣ) : ↥O) : B) = 1 := by
  rw [← map_mul, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Subring.coe_one, map_one]

include hk in
/-- **(ii) Equivariance**: `τ_{uφu⁻¹} = u·τ_φ`. -/
theorem cmRel_fpt_conj (φ ψ : k →ₐ[ℚ] B) (u : (↥O)ˣ)
    (hu : ∀ x, ψ x = ((u : ↥O) : B) * φ x * (((u⁻¹ : (↥O)ˣ) : ↥O) : B)) :
    rho ((u : ↥O) : B) *ᵥ ![fpt G φ, 1] = (rho ((u : ↥O) : B) *ᵥ ![fpt G φ, 1]) 1 •
      ![fpt G ψ, 1] ∧ (rho ((u : ↥O) : B) *ᵥ ![fpt G φ, 1]) 1 ≠ 0 := by
  set w := rho ((u : ↥O) : B) *ᵥ ![fpt G φ, 1] with hwdef
  have hw : rho (ψ G.y) *ᵥ w = G.lam • w := by
    rw [hu, map_mul, map_mul, hwdef, mulVec_mulVec, mul_assoc, mul_assoc, rho_unit_inv_mul,
      mul_one, ← mulVec_mulVec, fpt_eig_gen hk G φ, mulVec_smul]
  have hc' := phi_c_ne_zero hk G ψ
  have hw1 : w 1 ≠ 0 := by
    intro h1
    have e1 := congrFun hw 1
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, h1, mul_zero,
      add_zero] at e1
    have hw0 : w 0 = 0 := (mul_eq_zero.mp e1).resolve_left hc'
    have hw00 : w = 0 := by funext i; fin_cases i <;> simp [hw0, h1]
    have hv : ![fpt G φ, (1 : ℂ)] = 0 := by
      have e : rho (((u⁻¹ : (↥O)ˣ) : ↥O) : B) *ᵥ w = ![fpt G φ, 1] := by
        rw [hwdef, mulVec_mulVec, rho_unit_inv_mul, one_mulVec]
      rw [← e, hw00, mulVec_zero]
    simpa using congrFun hv 1
  refine ⟨?_, hw1⟩
  have hwv : w = w 1 • ![w 0 / w 1, 1] := by
    funext i; fin_cases i <;> simp [hw1]; field_simp
  have heig : rho (ψ G.y) *ᵥ ![w 0 / w 1, 1] = G.lam • ![w 0 / w 1, 1] := by
    have := hw
    rw [hwv, mulVec_smul, smul_comm] at this
    exact smul_right_injective _ hw1 this
  rw [← fpt_unique hk G ψ heig]
  exact hwv

include hk in
/-- **(iii)** If `τ_ψ = u·τ_φ` then `ψ = uφu⁻¹`. -/
theorem conj_of_cmRel (φ ψ : k →ₐ[ℚ] B) (u : (↥O)ˣ) (c : ℂ) (hc : c ≠ 0)
    (h : rho ((u : ↥O) : B) *ᵥ ![fpt G φ, 1] = c • ![fpt G ψ, 1]) (x : k) :
    ψ x = ((u : ↥O) : B) * φ x * (((u⁻¹ : (↥O)ˣ) : ↥O) : B) := by
  have hinv : rho (((u⁻¹ : (↥O)ˣ) : ↥O) : B) *ᵥ ![fpt G ψ, 1] = c⁻¹ • ![fpt G φ, 1] := by
    have := congrArg (fun z => rho (((u⁻¹ : (↥O)ˣ) : ↥O) : B) *ᵥ z) h
    simp only [mulVec_mulVec, rho_unit_inv_mul, one_mulVec, mulVec_smul] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine eq_of_eig (fpt_im hk G ψ) (fpt_eig hk G ψ x) ?_
  rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hinv, mulVec_smul, fpt_eig hk G φ x,
    mulVec_smul, mulVec_smul, h, smul_smul, smul_smul]
  congr 1
  field_simp

/-! ### (iv) Surjectivity -/

theorem Gen.hq_rat : G.y * G.y + ((G.P : ℚ) : k) * G.y + ((G.Q : ℚ) : k) = 0 := by
  push_cast; exact G.hq

theorem Gen.conj_root : (-(G.P : k) - G.y) * (-(G.P : k) - G.y) + (G.P : ℚ) • (-(G.P : k) - G.y) +
    algebraMap ℚ k (G.Q : ℚ) = 0 := by
  rw [Rat.smul_def, eq_ratCast]
  push_cast
  linear_combination G.hq

/-- The conjugation of `k`, `y ↦ −P − y`. -/
noncomputable def conjK : k →ₐ[ℚ] k := liftQuad hk G.hy G.hq_rat _ G.conj_root

theorem conjK_apply (r t : ℚ) :
    conjK hk G ((r : k) + t * G.y) = ((r - t * G.P : ℚ) : k) + ((-t : ℚ) : k) * G.y := by
  rw [conjK, liftQuad_apply, eq_ratCast, Rat.smul_def]
  push_cast; ring

theorem conjK_conjK (x : k) : conjK hk G (conjK hk G x) = x := by
  obtain ⟨r, t, rfl⟩ := exists_rat_repr hk G.hy x
  rw [conjK_apply, conjK_apply]
  push_cast; ring

/-- An order is stable under conjugation (`x + x̄` is a rational integer). -/
theorem conjK_mem (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring) {x : k}
    (hx : x ∈ R) : conjK hk G x ∈ R := by
  have hi : IsIntegral ℤ x := hR hx
  have hi2 : IsIntegral ℤ (conjK hk G x) := hi.map (conjK hk G).toRingHom.toIntAlgHom
  obtain ⟨r, t, hrt⟩ := exists_rat_repr hk G.hy x
  have hsum : x + conjK hk G x = ((2 * r - t * G.P : ℚ) : k) := by
    rw [hrt, conjK_apply]; push_cast; ring
  obtain ⟨n, hn⟩ := exists_int_of_isIntegral (k := k) (hsum ▸ hi.add hi2)
  have : conjK hk G x = (n : k) - x := by
    rw [eq_sub_iff_add_eq, add_comm, hsum, hn]; push_cast; rfl
  rw [this]
  exact R.sub_mem (intCast_mem R n) hx

include hk in
/-- Any ring map `g : R → ℂ` with `g(y) = λ` is `σ` on `R`. -/
theorem eq_sigma_of_gen (R : Subring k) (hyR : G.y ∈ R) (g : R →+* ℂ)
    (hg : g ⟨G.y, hyR⟩ = G.lam) (x : R) : g x = G.σ x := by
  obtain ⟨r, t, hx⟩ := exists_rat_repr hk G.hy (x : k)
  set N : ℕ := r.den * t.den with hN
  have hN0 : (N : ℂ) ≠ 0 := by
    rw [hN]; push_cast
    exact mul_ne_zero (Nat.cast_ne_zero.mpr r.den_nz) (Nat.cast_ne_zero.mpr t.den_nz)
  have key : (N : R) * x = ((r.num * t.den : ℤ) : R) + ((r.den * t.num : ℤ) : R) * ⟨G.y, hyR⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_add, SubringClass.coe_natCast, SubringClass.coe_intCast]
    rw [hx]
    push_cast
    rw [num_cast_eq r, num_cast_eq t, hN]
    push_cast; ring
  have hg' := congrArg g key
  have hσ' := congrArg (fun z : R => G.σ (z : k)) key
  simp only [map_mul, map_add, map_natCast, map_intCast, hg] at hg'
  simp only [Subring.coe_mul, Subring.coe_add, SubringClass.coe_natCast,
    SubringClass.coe_intCast, map_mul, map_add, map_natCast, map_intCast] at hσ'
  have : (N : ℂ) * g x = (N : ℂ) * G.σ x := by
    rw [hg', hσ']; rfl
  exact mul_left_cancel₀ hN0 this

/-- The eigenvalue at `(τ, 1)ᵀ`, a ring map `𝒪_τ → ℂ`. -/
noncomputable def evHom (τ : ℂ) : ordAt τ →+* ℂ where
  toFun b := (rho (b : B) *ᵥ ![τ, 1]) 1
  map_one' := by simp
  map_mul' a b := by
    obtain ⟨_, ca, hca⟩ := a.2
    obtain ⟨_, cb, hcb⟩ := b.2
    simp only [Subring.coe_mul, map_mul, ← mulVec_mulVec, hcb, mulVec_smul, hca, smul_smul]
    simp [mul_comm]
  map_zero' := by simp
  map_add' a b := by simp [add_mulVec]

theorem evHom_spec (τ : ℂ) (b : ordAt τ) :
    rho (b : B) *ᵥ ![τ, 1] = evHom τ b • ![τ, 1] := by
  obtain ⟨_, c, hc⟩ := b.2
  have : evHom τ b = c := by
    show (rho (b : B) *ᵥ ![τ, 1]) 1 = c
    rw [hc]; simp
  rw [this, hc]

include hk in
/-- **(iv)** Every CM point with `𝒪_τ ≅ R` is `τ_φ` for an optimal `φ`. -/
theorem exists_opt_of_cmPoint (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hyR : G.y ∈ R) (τ : ℂ) (hτ : τ.im ≠ 0) (e : ordAt τ ≃+* R) :
    ∃ φ : k →ₐ[ℚ] B, (∀ x, φ x ∈ O ↔ x ∈ R) ∧ fpt G φ = τ := by
  let h : R →+* ℂ := (evHom τ).comp e.symm.toRingHom
  let y' : R := ⟨G.y, hyR⟩
  have hyq' : y' * y' + (G.P : R) * y' + (G.Q : R) = 0 := Subtype.ext (by
    simp only [Subring.coe_mul, Subring.coe_add, SubringClass.coe_intCast, y']
    exact G.hq)
  have hhq : h y' * h y' + (G.P : ℂ) * h y' + G.Q = 0 := by
    have := congrArg h hyq'
    simpa [map_add, map_mul, map_intCast] using this
  let cR : R →+* R := (conjK hk G).toRingHom.restrict R R (fun x hx => conjK_mem hk G R hR hx)
  have hcR : ∀ x, cR (cR x) = x := fun x => Subtype.ext (conjK_conjK hk G x)
  obtain ⟨ε, hεε, hε⟩ : ∃ ε : R →+* R, (∀ x, ε (ε x) = x) ∧ h (ε y') = G.lam := by
    rcases eq_or_eq_conj G.lam_quad (conj_intCast' _) (conj_intCast' _) (G.lam_im hk) hhq with
      h1 | h1
    · exact ⟨RingHom.id R, fun _ => rfl, h1⟩
    · refine ⟨cR, hcR, ?_⟩
      have hc : cR y' = -(G.P : R) - y' := by
        apply Subtype.ext
        have := conjK_apply hk G 0 1
        simp only [Rat.cast_zero, zero_add, Rat.cast_one, one_mul] at this
        show conjK hk G G.y = ((-(G.P : R) - y' : R) : k)
        rw [this]
        push_cast; ring
      rw [hc, map_sub, map_neg, map_intCast, h1]
      have hv := (vieta G.lam_quad (conj_intCast' _) (conj_intCast' _) (G.lam_im hk)).1
      linear_combination -hv
  have hg : ∀ x : R, h (ε x) = G.σ x := eq_sigma_of_gen hk G R hyR (h.comp ε) hε
  set b₁ : ordAt τ := e.symm (ε y') with hb₁
  have hb₁eig : rho (b₁ : B) *ᵥ ![τ, 1] = G.lam • ![τ, 1] := by
    rw [evHom_spec]; congr 1
  have hb₁q : (b₁ : B) * b₁ + (G.P : ℚ) • (b₁ : B) + algebraMap ℚ B (G.Q : ℚ) = 0 := by
    have h0 : b₁ * b₁ + (G.P : ordAt τ) * b₁ + (G.Q : ordAt τ) = 0 := by
      have := congrArg (fun z => e.symm (ε z)) hyq'
      simpa [map_add, map_mul, map_intCast] using this
    have := congrArg Subtype.val h0
    simp only [Subring.coe_add, Subring.coe_mul, SubringClass.coe_intCast,
      Subring.coe_zero] at this
    rw [Algebra.smul_def, map_intCast, map_intCast]
    exact this
  let φ := liftQuad hk G.hy G.hq_rat (b₁ : B) hb₁q
  have hφy : φ G.y = b₁ := liftQuad_gen hk G.hy G.hq_rat _ hb₁q
  have hfpt : fpt G φ = τ := (fpt_unique hk G φ (by rw [hφy]; exact hb₁eig)).symm
  refine ⟨φ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hfpt⟩
  · have hxo : φ x ∈ ordAt τ := ⟨hx, G.σ x, by rw [← hfpt]; exact fpt_eig hk G φ x⟩
    set z := e ⟨φ x, hxo⟩ with hz
    have h1 : h z = G.σ x := by
      have hs := evHom_spec τ ⟨φ x, hxo⟩
      have hf : rho (φ x) *ᵥ ![τ, 1] = G.σ x • ![τ, 1] := hfpt ▸ fpt_eig hk G φ x
      have := congrFun (hs.symm.trans hf) 1
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero,
        mul_one] at this
      show evHom τ (e.symm z) = _
      rw [hz, RingEquiv.symm_apply_apply]
      exact this
    have h2 : h z = G.σ (ε z) := by
      have := hg (ε z)
      rwa [hεε z] at this
    have : x = (ε z : k) := G.σ.injective (h1.symm.trans h2)
    rw [this]; exact (ε z).2
  · have heq : φ x = (e.symm (ε ⟨x, hx⟩) : B) := by
      refine eq_of_eig hτ (hfpt ▸ fpt_eig hk G φ x) ?_
      rw [evHom_spec]
      congr 1
      exact hg ⟨x, hx⟩
    rw [heq]; exact (e.symm _).2.1

end Corr

/-! ## §10. `CMPointEmbeddingCorrespondence`, proved -/

/-- **The glue `CMPointEmbeddingCorrespondence`, proved** (no hypotheses): `φ ↦ τ_φ` (the
normalized fixed point for a fixed embedding `σ : k → ℂ`) induces the bijection between the
optimal embeddings modulo `𝒪^×` and the `𝒪^×`-orbits of CM points with `𝒪_τ ≅ R`. -/
theorem cmPointEmbeddingCorrespondence : CMPointEmbeddingCorrespondence := by
  intro k _ _ _ hk R hR hc
  obtain ⟨y, hyR, hy, P, Q, hq⟩ := exists_good_gen hk R hc
  obtain ⟨σ⟩ : Nonempty (k →+* ℂ) := ⟨(IsAlgClosed.lift : k →ₐ[ℚ] ℂ).toRingHom⟩
  let G : Gen k := ⟨y, hy, P, Q, hq, σ⟩
  let pt : OptEmb k R → HalfPlanes := fun φ => ⟨fpt G φ.1, fpt_im hk G φ.1⟩
  let F : Quotient (embSetoid k R) → CMPoints k R :=
    Quotient.lift (fun φ => (⟨Quotient.mk _ (pt φ), pt φ, rfl,
      nonempty_ordAt_fpt hk G R φ.1 φ.2⟩ : CMPoints k R))
      (fun φ ψ ⟨u, hu⟩ => Subtype.ext (Quotient.sound (by
        obtain ⟨h1, h2⟩ := cmRel_fpt_conj hk G φ.1 ψ.1 u hu
        exact ⟨u, _, h2, h1⟩)))
  have hFi : Function.Injective F := by
    intro a b hab
    induction a using Quotient.inductionOn with | h φ => ?_
    induction b using Quotient.inductionOn with | h ψ => ?_
    have hrel : cmRel (pt φ) (pt ψ) := Quotient.exact (congrArg Subtype.val hab)
    obtain ⟨u, c, hc0, hu⟩ := hrel
    exact Quotient.sound ⟨u, conj_of_cmRel hk G φ.1 ψ.1 u c hc0 hu⟩
  have hFs : Function.Surjective F := by
    rintro ⟨c, τ, hτ, ⟨e⟩⟩
    obtain ⟨φ, hopt, hfpt⟩ := exists_opt_of_cmPoint hk G R hR hyR τ.1 τ.2 e
    refine ⟨Quotient.mk _ ⟨φ, hopt⟩, Subtype.ext ?_⟩
    show Quotient.mk _ (pt ⟨φ, hopt⟩) = c
    rw [← hτ]
    congr 1
    exact Subtype.ext hfpt
  exact ⟨(Equiv.ofBijective F ⟨hFi, hFs⟩).symm⟩

/-- **height-split's glue `QMPairEmbeddingCorrespondence` from the two leaves alone.** -/
theorem qmPairEmbeddingCorrespondence_of_leaves (hD : QMDescentCM) (hU : QMUniformizationC) :
    QMPairEmbeddingCorrespondence :=
  qmPairEmbeddingCorrespondence_of hD hU cmPointEmbeddingCorrespondence

/-- **The row H-3 (`R5fpCount`) from Eichler's count and the two QM leaves** (height-split's
`r5fpCount_of` with the correspondence supplied). -/
theorem r5fpCount_of_leaves (hE : EichlerOptimalEmbeddingCount) (hD : QMDescentCM)
    (hU : QMUniformizationC) : LeafQM.AV.R5fpCount :=
  r5fpCount_of hE (qmPairEmbeddingCorrespondence_of_leaves hD hU)

end ZInQ.HeightGlue.QM

#print axioms ZInQ.HeightGlue.QM.cmPointEmbeddingCorrespondence
#print axioms ZInQ.HeightGlue.QM.qmPairEmbeddingCorrespondence_of_leaves
#print axioms ZInQ.HeightGlue.QM.r5fpCount_of_leaves
