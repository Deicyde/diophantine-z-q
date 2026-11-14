import ZInQKernel.HDecomp.QM.Leaves

/-! # height-glue: `QMPairEmbeddingCorrespondence` (height-split, H-3) reduced

§0 is a verbatim copy of `scratch/height-split/R5Count.lean` (task height-split) from
`namespace ZInQ.HeightSplit.R5` up to its definition of `QMPairEmbeddingCorrespondence` (the
glue Prop, never restated). §1 onward is new. -/

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

end Order

end ZInQ.HeightGlue.QM
