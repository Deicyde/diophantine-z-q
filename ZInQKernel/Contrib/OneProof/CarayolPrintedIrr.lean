import ZInQKernel.Contrib.OneProof.CarayolPrinted

/-!
# r17-rebase: Carayol's leaf with Ribet's plain irreducibility (the Burnside step proved)

Task r17-rebase (2026-11-17), report `docs/research/r17-rebase.md`, scratch `scratch/r17-rebase/`.

r17-print (`CarayolPrinted.lean`) proved `r17 : LadicCond.CarayolR17'` from the leaf
`CarayolPrinted.CarayolThmA`, whose irreducibility clause is absolute irreducibility in **Burnside's
form** (the `K_{f,λ}`-algebra spanned by the image is `M₂(K_{f,λ})`). Burnside's form is a theorem step
away from the printed word "irreducible" (Ribet 1977). This file proves that step for
two-dimensional odd representations, so the leaf can be stated in the printed form:

* `adjoin_eq_top_of_irreducible_odd` (new, proved): if `ρ : G → GL₂(K)` (`2 ≠ 0` in `K`) has no
  invariant subspace other than `0` and `K²`, and some `c` with `c² = 1` has `det ρ(c) = -1`, then the
  `K`-algebra spanned by `ρ(G)` is `M₂(K)`. Proof: `e = (1 + ρ(c))/2`, `f = (1 - ρ(c))/2` are
  nonzero complementary idempotents in the span `A`; irreducibility gives `a, b ∈ A` with `e a f ≠ 0`,
  `f b e ≠ 0`; then `e, f, e a f, f b e` are linearly independent, so `dim A = 4`.
* `CarayolThmAIrr` (the leaf): `CarayolThmA` with the Burnside clause replaced by the printed
  properties "irreducible" (no `ρ(G_ℚ)`-stable `K_{f,λ}`-subspace other than `0` and `K_{f,λ}²`)
  and "odd" (some involution `c ∈ G_ℚ`, complex conjugation, has `det ρ(c) = -1`).
* `carayolThmA_of_irr : CarayolThmAIrr → CarayolThmA` and
  `carayolR17'_of_printedIrr : CarayolThmAIrr → EigenformCoeffFieldFinite → LadicCond.CarayolR17'`.
* The conductor clause is **not** changed here: it is Carayol's Théorème (A) together with
  Casselman 1973 (`a(π_p) = v_p(N)`), see the report. `CarayolExistence` and `CarayolConductor`
  below split it off as named statements, and `carayolThmAIrr_of_split` reassembles the leaf.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace CarayolPrinted

open PkgI4 LadicCond

/-! ## §1. Irreducible and odd implies Burnside's form (dimension 2) -/

section Odd

variable {K : Type*} [Field K]

/-- If `q` is a nonzero idempotent with `p = 1 - q` nonzero, and the family `M` has no invariant
subspace other than `0` and `K²`, then some element `a` of the algebra spanned by `M` has `p a q ≠ 0`.
(Otherwise the range of `q` is a nonzero proper invariant subspace.) -/
theorem exists_mul_mul_ne_zero {ι : Type*} (M : ι → Matrix (Fin 2) (Fin 2) K)
    (hirr : ∀ W : Submodule K (Fin 2 → K), (∀ i, ∀ v ∈ W, (M i).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (p q : Matrix (Fin 2) (Fin 2) K) (hpq : p + q = 1) (hqq : q * q = q) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ a ∈ Algebra.adjoin K (Set.range M), p * a * q ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set W : Submodule K (Fin 2 → K) := LinearMap.range (Matrix.toLin' q) with hWdef
  have hinv : ∀ i, ∀ v ∈ W, (M i).mulVec v ∈ W := by
    intro i v hv
    obtain ⟨u, rfl⟩ := hv
    have h0 : p * M i * q = 0 := hcon _ (Algebra.subset_adjoin ⟨i, rfl⟩)
    have hq' : M i * q = q * (M i * q) := by
      calc M i * q = (p + q) * (M i * q) := by rw [hpq, one_mul]
        _ = p * M i * q + q * (M i * q) := by rw [add_mul, mul_assoc]
        _ = q * (M i * q) := by rw [h0, zero_add]
    refine ⟨(M i * q).mulVec u, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [← hq']
  rcases hirr W hinv with hb | ht
  · apply hq
    have : Matrix.toLin' q = 0 := LinearMap.range_eq_bot.mp hb
    simpa using this
  · apply hp
    have hq1 : q = 1 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      have hv : v ∈ W := ht ▸ Submodule.mem_top
      obtain ⟨u, rfl⟩ := hv
      simp only [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply, Matrix.mulVec_mulVec,
        hqq]
    rw [hq1, add_eq_right] at hpq
    exact hpq

/-- **Irreducible + odd implies Burnside's form, in dimension 2.** -/
theorem adjoin_eq_top_of_irreducible_odd {ι : Type*} (M : ι → Matrix (Fin 2) (Fin 2) K)
    (h2 : (2 : K) ≠ 0)
    (hirr : ∀ W : Submodule K (Fin 2 → K), (∀ i, ∀ v ∈ W, (M i).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (C : Matrix (Fin 2) (Fin 2) K) (hCA : C ∈ Algebra.adjoin K (Set.range M)) (hCC : C * C = 1)
    (hdet : C.det = -1) :
    Algebra.adjoin K (Set.range M) = ⊤ := by
  set A := Algebra.adjoin K (Set.range M) with hAdef
  set e : Matrix (Fin 2) (Fin 2) K := (2⁻¹ : K) • (1 + C) with hedef
  set f : Matrix (Fin 2) (Fin 2) K := (2⁻¹ : K) • (1 - C) with hfdef
  have h22 : (2⁻¹ : K) * 2⁻¹ + 2⁻¹ * 2⁻¹ = 2⁻¹ := by field_simp; ring
  have hef1 : e + f = 1 := by
    rw [hedef, hfdef, ← smul_add]
    rw [show (1 + C) + (1 - C) = (2 : K) • (1 : Matrix (Fin 2) (Fin 2) K) by
      rw [two_smul]; abel]
    rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hee : e * e = e := by
    rw [hedef, smul_mul_smul_comm, add_mul, one_mul, mul_add, mul_one, hCC]
    rw [show (1 + C + (C + 1) : Matrix (Fin 2) (Fin 2) K) = (2 : K) • (1 + C) by
      rw [two_smul]; abel]
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ h2, mul_one]
  have hff : f * f = f := by
    rw [hfdef, smul_mul_smul_comm, sub_mul, one_mul, mul_sub, mul_one, hCC]
    rw [show (1 - C - (C - 1) : Matrix (Fin 2) (Fin 2) K) = (2 : K) • (1 - C) by
      rw [two_smul]; abel]
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ h2, mul_one]
  have hef : e * f = 0 := by
    rw [hedef, hfdef, smul_mul_smul_comm, add_mul, one_mul, mul_sub, mul_one, hCC]
    simp
  have hfe : f * e = 0 := by
    rw [hedef, hfdef, smul_mul_smul_comm, sub_mul, one_mul, mul_add, mul_one, hCC]
    have h0 : (1 + C - (C + 1) : Matrix (Fin 2) (Fin 2) K) = 0 := by abel
    rw [h0, smul_zero]
  have hdet1 : (1 : Matrix (Fin 2) (Fin 2) K).det ≠ -1 := by
    rw [Matrix.det_one]
    intro h
    apply h2
    rw [show (2 : K) = 1 + 1 by norm_num]
    nth_rewrite 2 [h]
    ring
  have hdetm1 : (-1 : Matrix (Fin 2) (Fin 2) K).det ≠ -1 := by
    rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    intro h
    apply h2
    rw [show (2 : K) = 1 + 1 by norm_num]
    nth_rewrite 2 [show (1 : K) = -1 by simpa using h]
    ring
  have he0 : e ≠ 0 := by
    intro he
    apply hdetm1
    have : (1 : Matrix (Fin 2) (Fin 2) K) + C = 0 := by
      have := congrArg (fun X => (2 : K) • X) he
      simpa [hedef, smul_smul, mul_inv_cancel₀ h2] using this
    rw [show (-1 : Matrix (Fin 2) (Fin 2) K) = C from (neg_eq_of_add_eq_zero_right this), hdet]
  have hf0 : f ≠ 0 := by
    intro hf
    apply hdet1
    have : (1 : Matrix (Fin 2) (Fin 2) K) - C = 0 := by
      have := congrArg (fun X => (2 : K) • X) hf
      simpa [hfdef, smul_smul, mul_inv_cancel₀ h2] using this
    rw [show (1 : Matrix (Fin 2) (Fin 2) K) = C from sub_eq_zero.mp this, hdet]
  have heA : e ∈ A := A.smul_mem (add_mem (one_mem A) hCA) _
  have hfA : f ∈ A := A.smul_mem (sub_mem (one_mem A) hCA) _
  obtain ⟨a, haA, ha⟩ := exists_mul_mul_ne_zero M hirr e f hef1 hff he0 hf0
  obtain ⟨b, hbA, hb⟩ := exists_mul_mul_ne_zero M hirr f e (by rw [add_comm]; exact hef1) hee hf0 he0
  set x := e * a * f with hxdef
  set y := f * b * e with hydef
  have hxA : x ∈ A := mul_mem (mul_mem heA haA) hfA
  have hyA : y ∈ A := mul_mem (mul_mem hfA hbA) heA
  -- right-associated forms
  have hee' : ∀ X, e * (e * X) = e * X := fun X => by rw [← mul_assoc, hee]
  have hff' : ∀ X, f * (f * X) = f * X := fun X => by rw [← mul_assoc, hff]
  have hef' : ∀ X, e * (f * X) = 0 := fun X => by rw [← mul_assoc, hef, zero_mul]
  have hfe' : ∀ X, f * (e * X) = 0 := fun X => by rw [← mul_assoc, hfe, zero_mul]
  let v : Fin 4 → Matrix (Fin 2) (Fin 2) K := ![e, f, x, y]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg : g 0 • e + g 1 • f + g 2 • x + g 3 • y = 0 := by
      simpa [Fin.sum_univ_four, v] using hg
    have k1 := congrArg (fun X => e * X * e) hg
    have k2 := congrArg (fun X => f * X * f) hg
    have k3 := congrArg (fun X => e * X * f) hg
    have k4 := congrArg (fun X => f * X * e) hg
    simp only [hxdef, hydef, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, hee, hff,
      hef, hfe, hee', hff', hef', hfe', mul_zero, zero_mul, smul_zero, add_zero, zero_add] at k1 k2 k3 k4
    have hx' : e * (a * f) ≠ 0 := by rw [← mul_assoc]; exact ha
    have hy' : f * (b * e) ≠ 0 := by rw [← mul_assoc]; exact hb
    intro i
    fin_cases i
    · simpa using (smul_eq_zero.mp k1).resolve_right he0
    · simpa using (smul_eq_zero.mp k2).resolve_right hf0
    · simpa using (smul_eq_zero.mp k3).resolve_right hx'
    · simpa using (smul_eq_zero.mp k4).resolve_right hy'
  have hspan : Submodule.span K (Set.range v) ≤ Subalgebra.toSubmodule A := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact heA
    · exact hfA
    · exact hxA
    · exact hyA
  have h4 : Module.finrank K (Submodule.span K (Set.range v)) = 4 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hM : Module.finrank K (Matrix (Fin 2) (Fin 2) K) = 4 := by
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]
  rw [← Algebra.toSubmodule_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  rw [hM, ← h4]
  exact Submodule.finrank_mono hspan

end Odd

/-! ## §2. The leaf in printed form and its passage to `CarayolThmA` -/

section Leaf

open HeckeRing.GL2 NumberField IsDedekindDomain

/-- **LEAF (published; printed form modulo the conductor packaging, see the report): Carayol 1986,
Théorème (A), for `F = ℚ`, weight 2, with Ribet's irreducibility and the oddness of `ρ_{f,λ}`.**

For a newform `f ∈ S₂(Γ₁(N))` (Tau Ceti's `Newform N 2`) whose coefficient field `K_f` is a number field,
a prime `ℓ` and a place `λ ∣ ℓ` of `K_f`, there is a continuous `ρ = ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})` that is

* **irreducible**: no `ρ(G_ℚ)`-stable `K_{f,λ}`-subspace of `K_{f,λ}²` other than `0` and `K_{f,λ}²`
  (Ribet, *Galois representations attached to eigenforms with Nebentypus*, LNM 601 (1977), Thm 2.3,
  UNVERIFIED locator; also Darmon–Diamond–Taylor 1997 §3.1, UNVERIFIED);
* **odd**: some `c ∈ G_ℚ` with `c² = 1` (complex conjugation) has `det ρ(c) = -1` (from
  `det ρ_{f,λ} = ψ·χ_ℓ`, the nebentypus `ψ` even in weight 2 and `χ_ℓ(c) = -1`; Deligne 1971,
  Shimura 1971 Thm 7.14 for weight 2, DDT 1997 Thm 3.1; UNVERIFIED locators);
* unramified at every `p ∤ Nℓ`, with arithmetic Frobenius trace `a_p(f)` (Eichler–Shimura, Shimura 1971
  Thm 7.14; Carayol 1986 Théorème (A) at unramified `p`);
* of Serre–Tate conductor exponent `v_p(N)` at every prime `p ≠ ℓ`: Carayol 1986, Ann. Sci. ÉNS (4) 19,
  Théorème (A), pp. 409–411 (local–global compatibility with `π_{f,p}` through the local Langlands
  correspondence, every `p ≠ ℓ`, every `ℓ`; read by the locator audit, row R17), **with** Casselman,
  Math. Ann. 201 (1973) (`a(π_{f,p}) = v_p(N)` for a newform) and the conductor compatibility of the local
  correspondence. Packaged as one statement ("`ρ_{f,λ}` has conductor `N` away from `ℓ`") in DDT 1997
  Thm 3.1 and Carayol §0.8 (UNVERIFIED).

Every other object is as in `CarayolThmA`. Not stronger than the print: it asserts one representation
and only the listed properties of it. -/
def CarayolThmAIrr : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2)
    [NumberField (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
    (ℓ : 𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
      Continuous ρ ∧
      (∀ W : Submodule (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
          (Fin 2 → lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
        (∀ σ : GQ, ∀ v ∈ W, (ρ σ : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).mulVec v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      (∃ c : GQ, c * c = 1 ∧ (ρ c : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).det = -1) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2)
            (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).trace =
            algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
              (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
              ⟨coeff (f.toCuspForm : CF N 2) p, DSCoeffExt.coeff_mem_coeffField _ p⟩) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        condExp (ρ.comp (decomp p)) = (N.factorization p : ℚ)

/-- `CarayolThmAIrr` implies r17-print's `CarayolThmA` (Burnside's form from irreducible + odd). -/
theorem carayolThmA_of_irr (h : CarayolThmAIrr) : CarayolThmA := by
  intro N _ f _ ℓ _ lam hlam
  obtain ⟨ρ, hc, hirr, ⟨c, hcc, hdet⟩, hatt, hcond⟩ := h N f ℓ lam hlam
  refine ⟨ρ, hc, ?_, hatt, hcond⟩
  have h2 : (2 : lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ≠ 0 := by
    have : (2 : lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) =
        algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) 2 := by
      rw [map_ofNat]
    rw [this]
    exact (map_ne_zero_iff _ (algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
      (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).injective).mpr two_ne_zero
  refine adjoin_eq_top_of_irreducible_odd _ h2 hirr _ (Algebra.subset_adjoin ⟨c, rfl⟩) ?_ hdet
  rw [← Units.val_mul, ← map_mul, hcc, map_one, Units.val_one]

/-- **`r17` from Carayol's Théorème (A) with Ribet's irreducibility and oddness (printed form) and the
bundle leaf `EigenformCoeffFieldFinite`.** -/
theorem carayolR17'_of_printedIrr (h : CarayolThmAIrr) (hK : DSCoeffExt.EigenformCoeffFieldFinite) :
    LadicCond.CarayolR17' :=
  carayolR17'_of_printed (carayolThmA_of_irr h) hK

/-! ## §3. The conductor clause split off (for the statement check) -/

/-- **Existence part of `CarayolThmAIrr` (LEAF, printed: Eichler–Shimura–Deligne for weight 2 with Ribet's
irreducibility).** A continuous, irreducible, odd `ρ : G_ℚ → GL₂(K_{f,λ})`, unramified at `p ∤ Nℓ`
with Frobenius trace `a_p(f)`. Sources: Shimura, *Introduction to the arithmetic theory of automorphic
functions* (1971), Thm 7.14 (weight 2); Deligne, Sém. Bourbaki 355 (1971); Ribet, LNM 601 (1977),
Thm 2.3 (irreducibility); DDT 1997 Thm 3.1 (all, packaged). UNVERIFIED locators. -/
def CarayolExistence : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2)
    [NumberField (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
    (ℓ : 𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
      Continuous ρ ∧
      (∀ W : Submodule (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
          (Fin 2 → lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
        (∀ σ : GQ, ∀ v ∈ W, (ρ σ : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).mulVec v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      (∃ c : GQ, c * c = 1 ∧ (ρ c : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).det = -1) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2)
            (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).trace =
            algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
              (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
              ⟨coeff (f.toCuspForm : CF N 2) p, DSCoeffExt.coeff_mem_coeffField _ p⟩)

/-- **Conductor part (consequence of two prints: Carayol 1986 Théorème (A) with Casselman 1973).** Every
continuous, irreducible, odd `ρ : G_ℚ → GL₂(K_{f,λ})` that is unramified at `p ∤ Nℓ` with Frobenius
trace `a_p(f)` (by Chebotarev and Brauer–Nesbitt such a `ρ` is isomorphic to Carayol's `σ_λ(π_f)` or its
contragredient) has Serre–Tate conductor exponent `v_p(N)` at every prime `p ≠ ℓ`. Carayol, Ann. Sci. ÉNS
(4) 19 (1986), Théorème (A), pp. 409–411 (local–global compatibility, read by the locator audit, row R17),
with Casselman, Math. Ann. 201 (1973) (`a(π_p) = v_p(N)`). Packaged (UNVERIFIED): DDT 1997 Thm 3.1,
Carayol §0.8. -/
def CarayolConductor : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2)
    [NumberField (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
    (ℓ : 𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ∈ lam.asIdeal →
    ∀ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
      Continuous ρ →
      (∀ W : Submodule (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
          (Fin 2 → lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
        (∀ σ : GQ, ∀ v ∈ W, (ρ σ : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).mulVec v ∈ W) →
        W = ⊥ ∨ W = ⊤) →
      (∃ c : GQ, c * c = 1 ∧ (ρ c : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).det = -1) →
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2)
            (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).trace =
            algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
              (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
              ⟨coeff (f.toCuspForm : CF N 2) p, DSCoeffExt.coeff_mem_coeffField _ p⟩) →
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        condExp (ρ.comp (decomp p)) = (N.factorization p : ℚ)

/-- The two parts give the leaf. -/
theorem carayolThmAIrr_of_split (hE : CarayolExistence) (hC : CarayolConductor) : CarayolThmAIrr := by
  intro N _ f _ ℓ _ lam hlam
  obtain ⟨ρ, hc, hirr, hodd, hatt⟩ := hE N f ℓ lam hlam
  exact ⟨ρ, hc, hirr, hodd, hatt, hC N f ℓ lam hlam ρ hc hirr hodd hatt⟩

/-- `r17` from the split form. -/
theorem carayolR17'_of_split (hE : CarayolExistence) (hC : CarayolConductor)
    (hK : DSCoeffExt.EigenformCoeffFieldFinite) : LadicCond.CarayolR17' :=
  carayolR17'_of_printedIrr (carayolThmAIrr_of_split hE hC) hK

end Leaf

end CarayolPrinted
