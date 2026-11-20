import ZInQKernel.Contrib.OneProof.CarayolHerbrand
import TauCeti.NumberTheory.ModularForms.Parity
import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# carirr-odd: Carayol's leaf as a transcription of Darmon–Diamond–Taylor 1997, Thm 3.1

Task carirr-odd (2026-11-17), report `docs/research/carirr-odd.md`, scratch `scratch/carirr-odd/`.

r17-rebase's leaf `CarayolPrinted.CarayolThmAIrr` (and carayol-herbrand's `CarayolHerbrand.CarayolThmAIrrDDT`,
the same with DDT's form of the conductor) has two clauses that are not printed as stated:

* **odd** (`∃ c, c² = 1 ∧ det ρ(c) = -1`) is derived in the sources from `det ρ_{f,λ} = ψ·χ_ℓ`;
* **irreducible over `K_{f,λ}`** is a consequence of the printed **absolutely irreducible**.

This file states the leaf with the printed clauses and proves the passage, all in Lean:

* `cycN N`, `cycL ℓ`: the mod-`N` and `ℓ`-adic cyclotomic characters of `G_ℚ` (Mathlib's
  `modularCyclotomicCharacter` and `cyclotomicCharacter` on `Gal(ℚ̄/ℚ)`);
* `exists_complexConj`: complex conjugation, an involution `c ∈ G_ℚ` inverting every root of unity
  (transported from `ℂ` along an embedding `ℚ̄ → ℂ`);
* `cycL_eq_neg_one`: **`χ_ℓ(c) = -1`**; `cycN_eq_neg_one`: `c ↦ -1 ∈ (ℤ/N)ˣ`;
* `chi_neg_one_eq_one`: the nebentypus of a weight-2 newform is even (Tau Ceti's parity lemma);
* `odd_of_det`: `det ρ = ψ(cycN)·χ_ℓ` with `ψ` even gives the odd clause;
* `irreducible_of_absIrreducible`: irreducible over an extension field (here `K̄_{f,λ}`) implies
  irreducible over `K_{f,λ}`;
* the leaves `CarayolDDT31` (conductor in DDT's form, carayol-herbrand) and `CarayolDDT31Cond`
  (conductor as `condExp`), and `carayolThmA_of_DDT31`, `carayolThmA_of_DDT31Cond` discharging main's
  open field `carayolThmA : CarayolPrinted.CarayolThmA` (Burnside's form from irreducible + odd is
  r17-rebase's `adjoin_eq_top_of_irreducible_odd`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace CarayolDDT

open PkgI4 LadicCond

/-! ## Cyclotomic characters of `G_ℚ` -/

theorem natCard_rootsOfUnity_Qbar (N : ℕ) [NeZero N] : Nat.card (rootsOfUnity N Qbar) = N := by
  have : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar N

/-- The mod-`N` cyclotomic character of `G_ℚ`. -/
def cycN (N : ℕ) [NeZero N] : GQ →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Qbar (natCard_rootsOfUnity_Qbar N)).comp
    (MulSemiringAction.toRingAut GQ Qbar)

/-- The `ℓ`-adic cyclotomic character of `G_ℚ`. -/
def cycL (ℓ : ℕ) [Fact ℓ.Prime] : GQ →* ℤ_[ℓ]ˣ :=
  (cyclotomicCharacter Qbar ℓ).comp (MulSemiringAction.toRingAut GQ Qbar)

/-! ## Complex conjugation -/

/-- Some `c ∈ G_ℚ` is an involution inverting every root of unity (complex conjugation). -/
theorem exists_complexConj :
    ∃ c : GQ, c * c = 1 ∧ ∀ (n : ℕ) (t : Qbar), t ^ n = 1 → n ≠ 0 → c t * t = 1 := by
  let ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let φ : Qbar →ₐ[ℚ] ℂ := (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp ιC
  have hrange : ∀ x : Qbar, φ x ∈ ιC.fieldRange := fun x =>
    DSCoeffExt.mem_fieldRange_of_isIntegral ιC
      ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map φ)
  choose g hg using hrange
  have hgι : ∀ x, ιC (g x) = φ x := hg
  have hφφ : ∀ z : ℂ, Complex.conjAe (Complex.conjAe z) = z := fun z => by simp
  -- `g` is a ring hom
  have hinj := ιC.toRingHom.injective
  let g' : Qbar →ₐ[ℚ] Qbar :=
    { toFun := g
      map_one' := hinj (by simp [hgι, φ])
      map_mul' := fun a b => hinj (by
        show ιC (g (a * b)) = ιC (g a * g b)
        rw [map_mul, hgι, hgι, hgι, map_mul])
      map_zero' := hinj (by simp [hgι, φ])
      map_add' := fun a b => hinj (by
        show ιC (g (a + b)) = ιC (g a + g b)
        rw [map_add, hgι, hgι, hgι, map_add])
      commutes' := fun q => hinj (by
        show ιC (g (algebraMap ℚ Qbar q)) = ιC (algebraMap ℚ Qbar q)
        rw [hgι, AlgHom.commutes, AlgHom.commutes]) }
  have hgg : ∀ x, g' (g' x) = x := fun x => hinj (by
    show ιC (g (g x)) = ιC x
    rw [hgι]
    simp only [φ, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
    show Complex.conjAe.toAlgHom (ιC (g x)) = ιC x
    rw [hgι]
    simp [φ])
  let c : GQ := AlgEquiv.ofBijective g' ⟨fun a b h => by rw [← hgg a, ← hgg b, h],
    fun y => ⟨g' y, hgg y⟩⟩
  refine ⟨c, ?_, ?_⟩
  · ext x
    exact hgg x
  · intro n t ht hn
    apply hinj
    show ιC (g t * t) = ιC 1
    rw [map_mul, hgι, map_one]
    simp only [φ, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
    have hz : (ιC t) ^ n = 1 := by rw [← map_pow, ht, map_one]
    have hnorm : ‖ιC t‖ = 1 := by
      have := congrArg (‖·‖) hz
      simp only [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this
    show (starRingEnd ℂ) (ιC t) * ιC t = 1
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    simp


/-- **`χ_ℓ(c) = -1`**: the `ℓ`-adic cyclotomic character of an automorphism inverting the roots of unity. -/
theorem cycL_eq_neg_one (ℓ : ℕ) [Fact ℓ.Prime] {c : GQ}
    (hc : ∀ (n : ℕ) (t : Qbar), t ^ n = 1 → n ≠ 0 → c t * t = 1) : cycL ℓ c = -1 := by
  have : NeZero (ℓ : ℚ) := ⟨Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero⟩
  exact TauCeti.cyclotomicCharacter_eq_neg_one ℓ fun n t ht =>
    hc _ t ht (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)

/-- The mod-`N` cyclotomic character of an automorphism inverting the roots of unity is `-1`. -/
theorem cycN_eq_neg_one (N : ℕ) [NeZero N] {c : GQ}
    (hc : ∀ (n : ℕ) (t : Qbar), t ^ n = 1 → n ≠ 0 → c t * t = 1) : cycN N c = -1 := by
  have key := modularCyclotomicCharacter.unique Qbar (natCard_rootsOfUnity_Qbar N)
    (MulSemiringAction.toRingAut GQ Qbar c) (c := (-1 : ZMod N)) (fun t ht => by
      have htN : (t : Qbar) ^ N = 1 := by
        have := (mem_rootsOfUnity N t).1 ht
        rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
      have h1 := hc N t htN (NeZero.ne N)
      have h2 : ((t ^ (-1 : ZMod N).val : Qbarˣ) : Qbar) * t = 1 := by
        rw [Units.val_pow_eq_pow_val, ← pow_succ]
        refine orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one htN).trans ?_)
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_succ, ZMod.natCast_zmod_val, neg_add_cancel]
      have ht0 : (t : Qbar) ≠ 0 := t.ne_zero
      show c t = _
      exact mul_right_cancel₀ ht0 (h1.trans h2.symm))
  exact Units.ext (key.symm.trans (by simp))

/-! ## Parity of the nebentypus in weight 2 -/

open HeckeRing.GL2 in
theorem chi_neg_one_eq_one {N : ℕ} [NeZero N] (f : Newform N 2) : ((f.χ (-1) : ℂˣ) : ℂ) = 1 := by
  rw [TauCeti.char_neg_one_of_mem_cuspFormCharSpace f.mem_charSpace f.ne_zero]
  norm_num

/-! ## Absolute irreducibility implies irreducibility -/

theorem irreducible_of_absIrreducible {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    {ι : Type*} (M : ι → Matrix (Fin n) (Fin n) K)
    (h : ∀ W : Submodule L (Fin n → L),
      (∀ i, ∀ v ∈ W, ((M i).map (algebraMap K L)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule K (Fin n → K)) (hW : ∀ i, ∀ v ∈ W, (M i).mulVec v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hb, ht⟩ := hcon
  let φ : (Fin n → K) → (Fin n → L) := fun v => algebraMap K L ∘ v
  let W' : Submodule L (Fin n → L) := Submodule.span L (φ '' W)
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K),
      (A.map (algebraMap K L)).mulVec (φ v) = φ (A.mulVec v) := by
    intro A v
    funext i
    simp only [φ, Function.comp_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
      map_mul]
  have hW' : ∀ i, ∀ v ∈ W', ((M i).map (algebraMap K L)).mulVec v ∈ W' := by
    intro i v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hmap]
      exact Submodule.subset_span ⟨_, hW i y hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact W'.add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact W'.smul_mem a hx
  rcases h W' hW' with h1 | h1
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    have : φ w ∈ W' := Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h1, Submodule.mem_bot] at this
    apply hw0
    funext j
    have := congrFun this j
    simpa [φ] using this
  · obtain ⟨g, hg0, hle⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 ht)
    let r : Fin n → K := fun j => g (Pi.single j 1)
    have hgr : ∀ v, g v = ∑ j, v j * r j := by
      intro v
      conv_lhs => rw [show v = ∑ j, v j • Pi.single j (1 : K) by
        funext a; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, r]
    obtain ⟨j0, hj0⟩ : ∃ j, r j ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hg0
      ext v
      simp [hgr, hc]
    let G : (Fin n → L) →ₗ[L] L :=
      { toFun := fun v => ∑ j, v j * algebraMap K L (r j)
        map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun a b => by simp [mul_assoc, Finset.mul_sum] }
    have hWG : W' ≤ LinearMap.ker G := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hy0 : g y = 0 := hle hy
      rw [hgr] at hy0
      show ∑ j, algebraMap K L (y j) * algebraMap K L (r j) = 0
      simp_rw [← map_mul, ← map_sum, hy0, map_zero]
    have : (Pi.single j0 1 : Fin n → L) ∈ W' := h1 ▸ Submodule.mem_top
    have h0 := hWG this
    rw [LinearMap.mem_ker] at h0
    simp only [G, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h0
    exact hj0 ((map_eq_zero_iff _ (algebraMap K L).injective).1 h0)

/-! ## Continuous ring homs out of `ℤ_ℓ` are unique -/

/-- So the leaf's "some continuous `ι : ℤ_ℓ → K_λ`" names the canonical embedding: it is unique. -/
theorem padicInt_ringHom_ext {ℓ : ℕ} [Fact ℓ.Prime] {R : Type*} [Ring R] [TopologicalSpace R]
    [T2Space R] {ι ι' : ℤ_[ℓ] →+* R} (h : Continuous ι) (h' : Continuous ι') : ι = ι' := by
  have := (PadicInt.denseRange_intCast (p := ℓ)).equalizer h h' (funext fun z => by simp)
  exact RingHom.ext (congrFun this)

/-! ## Oddness from the determinant -/

/-- **Odd from `det ρ = ψ·χ_ℓ`.** If `det ρ(σ) = ψ(σ mod N)·ι(χ_ℓ(σ))` (whenever the value of `ψ` lies in
the coefficient field `K ⊆ ℂ`), and `ψ(-1) = 1`, then complex conjugation `c` has `c² = 1` and
`det ρ(c) = -1`. -/
theorem odd_of_det {E : Type*} [Field E] [TopologicalSpace E] (K : IntermediateField ℚ ℂ)
    [Algebra K E] {ℓ : ℕ} [Fact ℓ.Prime] {N : ℕ} [NeZero N] (ψ : (ZMod N)ˣ →* ℂˣ)
    (hψ : ((ψ (-1) : ℂˣ) : ℂ) = 1) (ρ : GQ →* GL (Fin 2) E)
    (hdet : ∃ ι : ℤ_[ℓ] →+* E, Continuous ι ∧ ∀ σ : GQ,
      ∀ h : ((ψ (cycN N σ) : ℂˣ) : ℂ) ∈ K,
        (ρ σ : Matrix (Fin 2) (Fin 2) E).det = algebraMap K E ⟨_, h⟩ * ι (cycL ℓ σ : ℤ_[ℓ])) :
    ∃ c : GQ, c * c = 1 ∧ (ρ c : Matrix (Fin 2) (Fin 2) E).det = -1 := by
  obtain ⟨ι, -, hι⟩ := hdet
  obtain ⟨c, hcc, hc⟩ := exists_complexConj
  refine ⟨c, hcc, ?_⟩
  have hval : ((ψ (cycN N c) : ℂˣ) : ℂ) = 1 := by rw [cycN_eq_neg_one N hc, hψ]
  have hmem : ((ψ (cycN N c) : ℂˣ) : ℂ) ∈ K := by rw [hval]; exact one_mem K
  rw [hι c hmem, cycL_eq_neg_one ℓ hc]
  have h1 : (⟨_, hmem⟩ : K) = 1 := Subtype.ext hval
  rw [h1, map_one, one_mul, Units.val_neg, Units.val_one, map_neg, map_one]

/-! ## The leaf -/

section Leaf

open HeckeRing.GL2 NumberField IsDedekindDomain

/-- **LEAF (published, printed form): Darmon–Diamond–Taylor 1997, Theorem 3.1, for weight 2 (Shimura,
Deligne, Ribet, Carayol), with the conductor in DDT's form.**

H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, in Elliptic curves, modular forms & Fermat's
Last Theorem (1997), §3.1, Theorem 3.1 (locator and clause letters UNVERIFIED here: no network; the
reviewer's verdict found every clause below printed in 3.1 (a)–(d), absolute irreducibility as 3.1(c)).
Originals: Eichler–Shimura, Shimura 1971 Thm 7.14 (weight 2: existence, unramified, traces); Deligne 1971
(`det = ψ χ_ℓ^{k-1}`); Ribet, LNM 601 (1977) (absolute irreducibility); Carayol 1986, Théorème (A) with
Casselman 1973 (the conductor). UNVERIFIED locators.

For a newform `f ∈ S₂(Γ₁(N), ψ)` (Tau Ceti's `Newform N 2`, nebentypus `ψ = f.χ`) whose coefficient field
`K_f = ℚ(a_n) ⊆ ℂ` is a number field, a prime `ℓ` and a place `λ ∣ ℓ` of `K_f`, there is a continuous
`ρ = ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})` (Mathlib's `adicCompletion`) such that

* **absolutely irreducible**: after extending scalars to an algebraic closure `K̄_{f,λ}`, no
  `ρ(G_ℚ)`-stable subspace of `K̄_{f,λ}²` other than `0` and the whole space;
* **`det ρ_{f,λ} = ψ·χ_ℓ`** (weight 2: `χ_ℓ^{k-1} = χ_ℓ`): `det ρ(σ) = ψ(σ mod N)·χ_ℓ(σ)`, where
  `σ mod N ∈ (ℤ/N)ˣ` is the mod-`N` cyclotomic character (`σ ζ_N = ζ_N^{σ mod N}`), `χ_ℓ : G_ℚ → ℤ_ℓˣ` the
  `ℓ`-adic cyclotomic character (Mathlib's), `ℤ_ℓ → K_{f,λ}` the canonical continuous embedding
  (unique: `padicInt_ringHom_ext`), and the value `ψ(σ mod N) ∈ ℂ` read in `K_f ⊆ ℂ`. The clause is
  stated only at those `σ` for which `ψ(σ mod N) ∈ K_f`; that is every `σ` (the values of `ψ` lie in
  `ℚ(a_n)`), but the restriction keeps the clause a consequence of the print with no further input;
* unramified at every `p ∤ Nℓ`, with arithmetic Frobenius trace `a_p(f)`;
* conductor (DDT's form): for every prime `p ≠ ℓ`,
  `codim V^{I_p} + ∫₀^∞ codim V^{G_p^u} du = v_p(N)` (carayol-herbrand's clause, equal to the Serre–Tate
  `condExp` by Herbrand's theorem, `CarayolHerbrand.condExp_decomp_eq_ddt`).

Normalization: arithmetic Frobenius has trace `a_p` and determinant `ψ(p)·p`, consistent with
`χ_ℓ(Frob_p) = p` and `Frob_p mod N = p`. It asserts one representation and only listed properties
of it: not stronger than the print. -/
def CarayolDDT31 : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2)
    [NumberField (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
    (ℓ : 𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
      Continuous ρ ∧
      (∀ W : Submodule
          (AlgebraicClosure (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))))
          (Fin 2 → AlgebraicClosure
            (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
        (∀ σ : GQ, ∀ v ∈ W, ((ρ σ : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).map
            (algebraMap (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
              (AlgebraicClosure
                (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))))).mulVec v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      (∃ ι : ℤ_[ℓ] →+* lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)),
        Continuous ι ∧ ∀ σ : GQ,
          ∀ h : ((f.χ (cycN N σ) : ℂˣ) : ℂ) ∈ DSCoeffExt.coeffField (f.toCuspForm : CF N 2),
            (ρ σ : Matrix (Fin 2) (Fin 2)
              (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).det =
              algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
                (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ⟨_, h⟩ *
              ι (cycL ℓ σ : ℤ_[ℓ])) ∧
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
        (codimInv (ρ.comp (decomp p)) inertiaSet : ℝ) +
          ∫ u in Set.Ioi (0 : ℝ), (codimInv (ρ.comp (decomp p)) (upperAbs p u) : ℝ) =
          (N.factorization p : ℝ)

/-- **LEAF (published, printed form modulo the conductor's form): `CarayolDDT31` with the conductor
clause as the Serre–Tate `condExp`** (r17-rebase's form of that clause; equal to DDT's form by Herbrand's
theorem, `CarayolHerbrand.condExp_decomp_eq_ddt`). Every other clause as in `CarayolDDT31`. -/
def CarayolDDT31Cond : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2)
    [NumberField (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
    (ℓ : 𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
      Continuous ρ ∧
      (∀ W : Submodule
          (AlgebraicClosure (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))))
          (Fin 2 → AlgebraicClosure
            (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
        (∀ σ : GQ, ∀ v ∈ W, ((ρ σ : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).map
            (algebraMap (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
              (AlgebraicClosure
                (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))))).mulVec v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      (∃ ι : ℤ_[ℓ] →+* lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)),
        Continuous ι ∧ ∀ σ : GQ,
          ∀ h : ((f.χ (cycN N σ) : ℂˣ) : ℂ) ∈ DSCoeffExt.coeffField (f.toCuspForm : CF N 2),
            (ρ σ : Matrix (Fin 2) (Fin 2)
              (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).det =
              algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
                (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ⟨_, h⟩ *
              ι (cycL ℓ σ : ℤ_[ℓ])) ∧
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

/-- **GLUE (proved): DDT 3.1 gives carayol-herbrand's `CarayolThmAIrrDDT`** (irreducible from absolutely
irreducible; odd from `det = ψ χ_ℓ`, `χ_ℓ(c) = -1`, `ψ(-1) = 1`). -/
theorem carayolThmAIrrDDT_of_DDT31 (h : CarayolDDT31) : CarayolHerbrand.CarayolThmAIrrDDT := by
  intro N _ f _ ℓ _ lam hlam
  obtain ⟨ρ, hc, habs, hdet, hatt, hcond⟩ := h N f ℓ lam hlam
  exact ⟨ρ, hc, irreducible_of_absIrreducible _ habs,
    odd_of_det _ f.χ (chi_neg_one_eq_one f) ρ hdet, hatt, hcond⟩

/-- **GLUE (proved): the `condExp` form gives r17-rebase's `CarayolThmAIrr`.** -/
theorem carayolThmAIrr_of_DDT31Cond (h : CarayolDDT31Cond) : CarayolPrinted.CarayolThmAIrr := by
  intro N _ f _ ℓ _ lam hlam
  obtain ⟨ρ, hc, habs, hdet, hatt, hcond⟩ := h N f ℓ lam hlam
  exact ⟨ρ, hc, irreducible_of_absIrreducible _ habs,
    odd_of_det _ f.χ (chi_neg_one_eq_one f) ρ hdet, hatt, hcond⟩

/-- The two forms of the leaf are equivalent (Herbrand's theorem, carayol-herbrand). -/
theorem carayolDDT31_iff_cond : CarayolDDT31 ↔ CarayolDDT31Cond := by
  constructor
  · intro h N _ f _ ℓ _ lam hlam
    obtain ⟨ρ, hc, habs, hdet, hatt, hcond⟩ := h N f ℓ lam hlam
    refine ⟨ρ, hc, habs, hdet, hatt, fun p _ hp => ?_⟩
    have e := (CarayolHerbrand.condExp_decomp_eq_ddt lam hlam ρ hc p hp).trans (hcond p hp)
    exact_mod_cast e
  · intro h N _ f _ ℓ _ lam hlam
    obtain ⟨ρ, hc, habs, hdet, hatt, hcond⟩ := h N f ℓ lam hlam
    refine ⟨ρ, hc, habs, hdet, hatt, fun p _ hp => ?_⟩
    rw [← CarayolHerbrand.condExp_decomp_eq_ddt lam hlam ρ hc p hp, hcond p hp, Rat.cast_natCast]

/-- **Main's open field `carayolThmA` from DDT 1997 Thm 3.1 (weight 2, DDT's conductor).** -/
theorem carayolThmA_of_DDT31 (h : CarayolDDT31) : CarayolPrinted.CarayolThmA :=
  CarayolPrinted.carayolThmA_of_irr
    (CarayolHerbrand.carayolThmAIrr_of_DDT (carayolThmAIrrDDT_of_DDT31 h))

/-- **Main's open field `carayolThmA` from the `condExp` form of the leaf.** -/
theorem carayolThmA_of_DDT31Cond (h : CarayolDDT31Cond) : CarayolPrinted.CarayolThmA :=
  CarayolPrinted.carayolThmA_of_irr (carayolThmAIrr_of_DDT31Cond h)

/-- `r17` (`LadicCond.CarayolR17'`) from DDT 3.1 and the bundle leaf `EigenformCoeffFieldFinite`. -/
theorem carayolR17'_of_DDT31 (h : CarayolDDT31) (hK : DSCoeffExt.EigenformCoeffFieldFinite) :
    LadicCond.CarayolR17' :=
  CarayolPrinted.carayolR17'_of_printed (carayolThmA_of_DDT31 h) hK

end Leaf

end CarayolDDT
