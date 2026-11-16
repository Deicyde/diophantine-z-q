import ZInQKernel.Contrib.OneProof.H.TailG

/-!
# sgr-direct: the consumer of `shimuraIntegralModelRep` without the integral model (route NV)

The field `shimuraIntegralModelRep` enters the H chain only through `HDec.HeckeRestNV.HeckeVertWitness`
(no vertical ramification of the Hecke cover `E/ℚ(X)` at the primes `p > 324`). This file proves
`HeckeVertWitness` along h-b1's Lemma NV, simplified to one branch point, from fields already in the
bundles (`r1r2`, `t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints`) and five named Props:

* `NVLocalInertia` (GLUE, local algebra of tame covers; h-b1 §3 step 3): if the residue fields over a
  rational branch point `b` are unramified at `p`, a conjugate of each vertical inertia element lies in an
  inertia group over `b`;
* `RamifiedSqrtInertia` (textbook Hilbert theory): over a point with ramification index `∣ 2`, a
  nontrivial inertia element moves `√(c (X − b))`. **Proved below** (`ramifiedSqrtInertia`, from Mathlib's
  `card_inertia_eq_ramificationIdxIn` and `ramificationIdx_tower`);
* `VertInertiaTrivial` (textbook Hilbert theory): trivial vertical inertia gives an unramified vertical prime.
  **Proved below** (`vertInertiaTrivial`, over the DVR `ℤ[X]_{(p)}`);
* `HeckeBranchFibreUnram` (h-b1 §3 step 2): the residue fields of the Hecke cover over `−16/27` (CM points by
  `ℤ[√−6]`) are unramified at `p > 324`. **Proved below** (`heckeBranchFibreUnram`) from the bundle field `r1r2`
  (`R1R2fp`, its reciprocity clause via the kernel's `residue_unramified_over_branch`) and T5 (`MobiusGlue`);
* `HeckeSqrtBranch` (GLUE from Elkies' model of `X₆`, the field `elkiesX6StarPrinted`): `E` contains a
  square root of `a (27X + 16)` with `a` a unit at every `p > 324`.

Compiled here (standard axioms): `heckeVertWitness_of_nv` (the composite from the five Props),
`ramifiedSqrtInertia`, `vertInertiaTrivial`, and `heckeVertWitness_of_nvLocal`: `HeckeVertWitness` from the bundle
fields and the three Props `NVLocalInertia`, `HeckeBranchFibreUnram`, `HeckeSqrtBranch`; `heckeBranchFibreUnram`;
`heckeVertWitness_of_nvSqrt`: `HeckeVertWitness` from the bundle fields and the two named Props `NVLocalInertia`
and `HeckeSqrtBranch`; and the final form `heckeVertWitness_of_nvSqrtAny`, with `HeckeSqrtBranch` weakened to the
constant-free `HeckeSqrtBranchAny` (`E ∋ √(c (27X + 16))` for some `c ≠ 0`): the constant is shown to be a `p`-adic
square times a unit by `exists_good_sqrt` (the residue fields over `0` are unramified and contain `√c`;
`even_padicValRat_of_sq_mem`).
-/

set_option linter.style.haveILetI false

noncomputable section

open Polynomial CategoryTheory AlgebraicGeometry
open GlueDescent.B2Q NumberField
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV HDec.TSHecke LeafQM LeafQM.AV

namespace SGRDirect

/-! ## Inertia sets -/

/-- The inertia set of a prime `Q` of the integral closure of `ℚ[X]` in `E`: the `σ ∈ Gal(E/ℚ(X))` with
`σ b ∈ B` and `σ b ≡ b mod Q` for every `b ∈ B`. -/
def InertiaQ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    (Q : Ideal (integralClosure ℚ[X] E)) : Set Gal(E/RatFunc ℚ) :=
  {σ | ∀ b : integralClosure ℚ[X] E, ∃ c : integralClosure ℚ[X] E, (c : E) = σ (b : E) ∧ c - b ∈ Q}

/-- The inertia set of a prime `q` of the integral closure of `ℤ[X]` in `E` (through `ℚ[X]`). -/
def InertiaZ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E] :
    letI := intPolyAlg E
    Ideal (integralClosure ℤ[X] E) → Set Gal(E/RatFunc ℚ) :=
  letI := intPolyAlg E
  fun q => {σ | ∀ b : integralClosure ℤ[X] E, ∃ c : integralClosure ℤ[X] E,
    (c : E) = σ (b : E) ∧ c - b ∈ q}

/-! ## The named Props -/

/-- **GLUE (local algebra of tame covers; h-b1 §3, Lemma NV step 3).** Let `E/ℚ(X)` be finite Galois of
degree `< p`, with branch data in `S ∪ {∞}`, the points of `S` `p`-integral and pairwise distinct mod `p`.
If every residue field of `E` over a point `b ∈ S` is unramified at `p`, then for every prime `q` of the
integral closure of `ℤ[X]` in `E` over `p ℤ[X]` and every `τ` in the inertia of `q`, some conjugate
`g τ g⁻¹` lies in the inertia of a prime over `X − b`.
*Proof route* (not compiled): near the closed point `(p, X − b)` of `ℤ_(p)[X]` only the divisors `p = 0` and
`X = b` can ramify (`p`-integrality, distinctness); both tamely (degree `< p`, characteristic 0). By
Abhyankar's lemma (SGA 1 XIII 5.3; the kernel's T2 for the DVR form) and Zariski–Nagata purity (proved in
the chain, `PropTSGlue.PurityGlobalDim2`, t-purity3) the cover is, strictly henselian locally, a quotient of
`ℤ_p^{sh}[z^{1/n}, p^{1/n}]`; the residue field of the branch over `z = 0` is then `k_p(p^{1/c})` with
`c = [I_𝔓 : I_{Q_b}]`, so unramified residue fields force `I_𝔓 = I_{Q_b}`, and `I_q ⊆ I_𝔓`. -/
def NVLocalInertia : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf → Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    ∀ b ∈ S,
    (∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime → 𝔓.under ℚ[X] = Ideal.span {X - C b} →
      ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
        UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p) →
    letI := intPolyAlg E
    ∀ q : Ideal (integralClosure ℤ[X] E), q.IsPrime → q.under ℤ[X] = vertPrime p →
    ∀ τ ∈ InertiaZ E q, ∃ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime ∧
      Q.under ℚ[X] = Ideal.span {X - C b} ∧ ∃ g : Gal(E/RatFunc ℚ), g * τ * g⁻¹ ∈ InertiaQ E Q

/-- **GLUE (textbook Hilbert theory).** Over a prime `Q` above `X − b` with ramification index dividing `2`,
an inertia element fixing a square root of `c (X − b)` (`c ≠ 0`) is trivial. (`|I_Q| = e_Q ≤ 2`; if `I_Q`
fixed `s` then `s` would lie in the inertia field, over which `X − b` is unramified, but `v(s²) = 1` is odd.) -/
def RamifiedSqrtInertia : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (b c : ℚ), c ≠ 0 → ∀ s : E,
    s ^ 2 = algebraMap ℚ[X] E (C c * (X - C b)) →
    ∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime → Q.under ℚ[X] = Ideal.span {X - C b} →
    Q.ramificationIdx ℚ[X] ∣ 2 → ∀ σ ∈ InertiaQ E Q, σ s = s → σ = 1

/-- **Textbook Hilbert theory (proved below, `vertInertiaTrivial`).** For `E/ℚ(X)` finite Galois of degree `< p`,
if every prime of the integral closure of `ℤ[X]` in `E` over `p ℤ[X]` has trivial inertia set, some such prime has
ramification index `1` (over the DVR `ℤ[X]_{(p)}`: `|I_q| = e_q` since the residue extensions, of degree `< p`,
are separable). -/
def VertInertiaTrivial : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (p : ℕ), p.Prime → Module.finrank (RatFunc ℚ) E < p →
    (letI := intPolyAlg E
     ∀ q : Ideal (integralClosure ℤ[X] E), q.IsPrime → q.under ℤ[X] = vertPrime p →
       ∀ τ ∈ InertiaZ E q, τ = 1) →
    VertUnramWitness E p

/-- **GLUE from the field `shimuraMainThmIDeligneY3AbU` (Shimura's reciprocity law at CM points on `Y₃`;
h-b1 §3 step 2).** For a triple with R1fp,
R1hecke, R2fp and any `E` carrying the normalization chart, every residue field of `E` over the branch value
`−16/27` (whose points are CM points by the maximal order `ℤ[√−6]`, conductor `1`) is unramified at every
prime `p > 324`: by Shimura reciprocity the field of definition of a level-3 CM point lies in the ray class
field of conductor `3` of its CM field, unramified outside `{2, 3}`. -/
def HeckeBranchFibreUnram : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∀ p : ℕ, p.Prime → 324 < p →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C (-16 / 27)} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
          UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p

/-- **GLUE from Elkies' model of `X₆` (the field `elkiesX6StarPrinted`).** For a triple with R1fp, R1hecke,
R2fp and any `E` carrying the normalization chart, `E` contains a square root of `a (27X + 16)` for an integer
`a` prime to every `p > 324`. Elkies' coordinate `t` on `X₆/W` (`t = 0, 1, ∞` at the CM points of discriminant
`−24, −4, −3`) is `t = (27X + 16)/16` in the coordinate `X` of R2fp (branch values `−16/27, 0, ∞` with the same
CM types), and Elkies' chart `s² = −t` gives `(4s)² = −(27X + 16)` in `ℚ(X₆) ⊆ E` (`Y₃ → X₆` is dominant), so
`a = −1` (rv-h-b1 §2: `ℚ(X₆) = ℚ(X)(√X, √(−(27X + 16)))`, constants `−1, 3`). -/
def HeckeSqrtBranch : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∃ (a : ℤ) (s : E), (∀ p : ℕ, p.Prime → 324 < p → ¬ (p : ℤ) ∣ a) ∧
        s ^ 2 = algebraMap ℚ[X] E (C (a : ℚ) * (C 27 * X + C 16))


/-! ## Helpers -/

section Helpers

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E]

theorem gal_fix (σ : Gal(E/RatFunc ℚ)) (f : ℚ[X]) :
    σ (algebraMap ℚ[X] E f) = algebraMap ℚ[X] E f := by
  rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E, AlgEquiv.commutes]

theorem gal_sq (σ : Gal(E/RatFunc ℚ)) {s : E} {f : ℚ[X]} (hs : s ^ 2 = algebraMap ℚ[X] E f) :
    σ s = s ∨ σ s = -s := by
  have h : (σ s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, gal_fix]
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

theorem conj_fix (g τ : Gal(E/RatFunc ℚ)) {s : E} {f : ℚ[X]} (hs : s ^ 2 = algebraMap ℚ[X] E f)
    (hτ : τ s = s) : (g * τ * g⁻¹) s = s := by
  have hgg : g (g⁻¹ s) = s := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rcases gal_sq g⁻¹ hs with h | h
  · rw [h] at hgg
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, hτ, hgg]
  · rw [h, map_neg] at hgg
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, map_neg, hτ, map_neg]
    exact hgg

theorem algebraMap_int_injective :
    letI := intPolyAlg E
    Function.Injective (algebraMap ℤ[X] E) := by
  letI := intPolyAlg E
  have h1 : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  exact h1.comp (Polynomial.map_injective _ (Int.cast_injective (α := ℚ)))

theorem exists_vertPrime (p : ℕ) (hp : p.Prime) :
    letI := intPolyAlg E
    ∃ q : Ideal (integralClosure ℤ[X] E), q.IsPrime ∧ q.under ℤ[X] = vertPrime p := by
  letI := intPolyAlg E
  haveI := vertPrime_isPrime p hp
  refine Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (vertPrime p) ?_
  intro f hf
  rw [RingHom.mem_ker] at hf
  have : algebraMap ℤ[X] E f = 0 := by
    rw [IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E) E, hf, map_zero]
  rw [algebraMap_int_injective (E := E) (this.trans (map_zero _).symm)]
  exact Ideal.zero_mem _

/-- A vertical inertia element fixes a square root of `a (27X + 16)` (`p ∤ 2·3·a`). -/
theorem vert_fix (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (s : E)
    (hs : s ^ 2 = algebraMap ℚ[X] E (C (a : ℚ) * (C 27 * X + C 16))) :
    letI := intPolyAlg E
    ∀ q : Ideal (integralClosure ℤ[X] E), q.under ℤ[X] = vertPrime p →
    ∀ τ ∈ InertiaZ E q, τ s = s := by
  letI := intPolyAlg E
  intro q hq τ hτ
  set f : ℤ[X] := C a * (C 27 * X + C 16) with hfdef
  have hf : algebraMap ℤ[X] E f = s ^ 2 := by
    rw [hs]
    show algebraMap ℚ[X] E (f.map (Int.castRingHom ℚ)) = _
    congr 1
    rw [hfdef, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
    simp
  have hint : IsIntegral ℤ[X] s := by
    refine ⟨X ^ 2 - C f, monic_X_pow_sub_C f (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hf, sub_self]
  let sZ : integralClosure ℤ[X] E := ⟨s, hint⟩
  obtain ⟨c, hc, hcq⟩ := hτ sZ
  rcases gal_sq τ hs with h | h
  · exact h
  · exfalso
    have hc' : c = -sZ := Subtype.ext (by rw [hc]; exact h)
    rw [hc'] at hcq
    have h2 : (2 : integralClosure ℤ[X] E) * sZ ∈ q := by
      have := q.neg_mem_iff.mpr hcq
      convert this using 1
      ring
    have h4 : algebraMap ℤ[X] (integralClosure ℤ[X] E) (4 * f) ∈ q := by
      have := q.mul_mem_left (2 * sZ) h2
      convert this using 1
      apply Subtype.ext
      show algebraMap ℤ[X] E (4 * f) = 2 * s * (2 * s)
      rw [map_mul, hf, map_ofNat]
      ring
    have hv : 4 * f ∈ vertPrime p := by
      rw [← hq]; exact h4
    rw [vertPrime, Ideal.mem_map_C_iff] at hv
    have h0 := hv 0
    simp [hfdef] at h0
    rw [Ideal.mem_span_singleton] at h0
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h64 : (p : ℤ) ∣ 64 * a := by
      convert h0 using 1
      ring
    rcases hpz.dvd_or_dvd h64 with h | h
    · have h' : p ∣ 2 ^ 6 := by exact_mod_cast h
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h'
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact ha h

end Helpers

/-! ## The composite -/

/-- **One unramified vertical prime from route NV** (compiled), for one `E` with the Hecke cover's branch data,
degree, branch fibre at `−16/27` and square root. -/
theorem vertUnramWitness_of_nv (hL : NVLocalInertia) (hR : RamifiedSqrtInertia)
    (hV : VertInertiaTrivial)
    (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] [IsGalois (RatFunc ℚ) E]
    (p : ℕ) (hp : p.Prime) (hp324 : 324 < p)
    (hB : BranchData E {0, -16 / 27} nY3 6) (hD : Module.finrank (RatFunc ℚ) E ≤ 324)
    (hF : ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C (-16 / 27)} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
          UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p)
    (a : ℤ) (s : E) (ha : ¬ (p : ℤ) ∣ a)
    (hs : s ^ 2 = algebraMap ℚ[X] E (C (a : ℚ) * (C 27 * X + C 16))) :
    VertUnramWitness E p := by
  letI := intPolyAlg E
  haveI : Fact p.Prime := ⟨hp⟩
  refine hV E p hp (by omega) ?_
  intro q hq hqu τ hτ
  have hτs : τ s = s := vert_fix p hp (by omega) a ha s hs q hqu τ hτ
  have hmem : (-16 / 27 : ℚ) ∈ ({0, -16 / 27} : Finset ℚ) := by simp
  have h1627 : padicValRat p (16 / 27) = 0 := padicValRat_16_27 p (by omega)
  have hint : ∀ b ∈ ({0, -16 / 27} : Finset ℚ), 0 ≤ padicValRat p b := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · simp
    · rw [neg_div, padicValRat.neg, h1627]
  have hdist : ∀ b ∈ ({0, -16 / 27} : Finset ℚ), ∀ b' ∈ ({0, -16 / 27} : Finset ℚ), b ≠ b' →
      padicValRat p (b - b') = 0 := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · rw [zero_sub, neg_div, neg_neg, h1627]
    · rw [sub_zero, neg_div, padicValRat.neg, h1627]
    · exact absurd rfl hne
  obtain ⟨Q, hQ, hQu, g, hg⟩ := hL E {0, -16 / 27} nY3 6 p hp hB (by omega) hint hdist
    (-16 / 27) hmem hF q hq hqu τ hτ
  have ha0 : (a : ℚ) ≠ 0 := by
    rintro h
    exact ha (by rw [Int.cast_eq_zero.mp h]; exact dvd_zero _)
  have hs' : s ^ 2 = algebraMap ℚ[X] E (C (27 * (a : ℚ)) * (X - C (-16 / 27))) := by
    rw [hs]
    congr 1
    have e1 : (X - C (-16 / 27 : ℚ) : ℚ[X]) = X + C (16 / 27) := by
      rw [show (-16 / 27 : ℚ) = -(16 / 27) by norm_num, C_neg, sub_neg_eq_add]
    have e2 : (C (27 : ℚ) * C (16 / 27) : ℚ[X]) = C 16 := by rw [← C_mul]; norm_num
    rw [e1, C_mul]
    linear_combination (-C (a : ℚ)) * e2
  have hram : Q.ramificationIdx ℚ[X] ∣ 2 := by
    have := hB.2.1 (-16 / 27) hmem Q hQ hQu
    simpa [nY3] using this
  have h1 := hR E (-16 / 27) (27 * a) (mul_ne_zero (by norm_num) ha0) s hs' Q hQ hQu hram
    (g * τ * g⁻¹) hg (conj_fix g τ hs' hτs)
  have : τ = g⁻¹ * (g * τ * g⁻¹) * g := by group
  rw [this, h1]
  group

/-- **`HeckeVertWitness` by route NV, without the integral model of the Shimura curve** (compiled). Inputs:
the bundle fields `r1r2` (as `R1R2fp`), `t5` (as `TorsionStructure`), `qmAutCard`, `serreRigidity3`,
`alFixedPoints` (the same inputs as `HeckeRestAll.coverModelOfHecke_of_heckeRest`, which give `HeckeBranch`
and `HeckeDegree`), and the five named Props above. -/
theorem heckeVertWitness_of_nv (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : NVLocalInertia) (hR : RamifiedSqrtInertia) (hV : VertInertiaTrivial)
    (hF : HeckeBranchFibreUnram) (hQ : HeckeSqrtBranch) : HeckeVertWitness := by
  have hB : HeckeBranch :=
    heckeBranch_of' hRR HeckeRestCurve.curveChartInf (HeckeRest.heckeFibreSizes_of hT hA hS hW) hT
  have hD : HeckeDegree := heckeDegree_of_torsion hT
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324
  obtain ⟨a, s, ha, hs⟩ := hQ Y Φ π h1 hh h2 E hN
  exact vertUnramWitness_of_nv hL hR hV E p hp hp324 (hB Y Φ π h1 hh h2 E hN)
    (hD Y Φ π h1 hh h2 E hN) (hF Y Φ π h1 hh h2 E hN p hp hp324) a s (ha p hp hp324) hs

/-! ## `RamifiedSqrtInertia` is proved (Mathlib's Hilbert theory) -/

section Ram

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]

/-- The inclusion of the integral closure of `ℚ[X]` in an intermediate field into that in `E`. -/
def incl (K' : IntermediateField (RatFunc ℚ) E) :
    integralClosure ℚ[X] K' →+* integralClosure ℚ[X] E where
  toFun x := ⟨((x : K') : E), by
    have h := x.2
    exact h.map (IsScalarTower.toAlgHom ℚ[X] K' E)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

example (K' : IntermediateField (RatFunc ℚ) E) : IsDedekindDomain (integralClosure ℚ[X] K') :=
  integralClosure.isDedekindDomain (A := ℚ[X]) (K := RatFunc ℚ) (L := K')


/-- **`RamifiedSqrtInertia` is a theorem** (compiled). With `H'` the fixing group of the ring of integers `A'` of
the fixed field of `σ`: `|I_{H'}(Q)| = e(Q|A') ≥ 2` (`σ ∈ I_{H'}(Q)`, `σ ≠ 1`), so `e(Q ∩ A' | X − b) = 1` by the
tower and `e(Q | X − b) ∣ 2`; but `s ∈ Q ∩ A'` and `X − b = c⁻¹ s²` give `e(Q ∩ A' | X − b) ≥ 2`. -/
theorem ramifiedSqrtInertia : RamifiedSqrtInertia := by
  intro E _ _ _ _ _ _ b c hc s hs Q hQ hQu he σ hσ hσs
  by_contra hne
  haveI := hQ
  -- the base `A = ℚ[X]`, `(integralClosure ℚ[X] E)` its integral closure in `E`, `G = Gal(E/ℚ(X))`
  haveI hinjE : Module.IsTorsionFree ℚ[X] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : IsFractionRing (integralClosure ℚ[X] E) E := IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  haveI : SMulCommClass Gal(E/RatFunc ℚ) ℚ[X] E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E, AlgEquiv.commutes]⟩
  haveI hG : IsGaloisGroup Gal(E/RatFunc ℚ) ℚ[X] (integralClosure ℚ[X] E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/RatFunc ℚ) ℚ[X] (integralClosure ℚ[X] E) (RatFunc ℚ) E
  -- the intermediate field fixed by `σ` and its ring of integers `A'`
  set K' : IntermediateField (RatFunc ℚ) E := IntermediateField.fixedField (Subgroup.zpowers σ)
  set A' := integralClosure ℚ[X] K'
  haveI : IsDedekindDomain A' := integralClosure.isDedekindDomain (A := ℚ[X]) (K := RatFunc ℚ) (L := K')
  letI : Algebra A' (integralClosure ℚ[X] E) := (incl K').toAlgebra
  haveI : IsScalarTower ℚ[X] A' (integralClosure ℚ[X] E) := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    show algebraMap ℚ[X] E a = (((algebraMap ℚ[X] A' a : A') : K') : E)
    rw [IsScalarTower.algebraMap_apply ℚ[X] K' E]
    rfl)
  have hincl_inj : Function.Injective (algebraMap A' (integralClosure ℚ[X] E)) := by
    intro x y hxy
    have h1 : (((x : K') : E)) = (((y : K') : E)) :=
      congrArg (fun z : (integralClosure ℚ[X] E) => (z : E)) hxy
    exact Subtype.ext (Subtype.ext h1)
  have hQE : Function.Injective (algebraMap ℚ[X] E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mp hinjE
  have hQB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro x y h
    apply hQE
    rw [IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E x,
      IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E y, h]
  have hQA' : Function.Injective (algebraMap ℚ[X] A') := by
    intro x y h
    apply hQB
    rw [IsScalarTower.algebraMap_apply ℚ[X] A' (integralClosure ℚ[X] E) x,
      IsScalarTower.algebraMap_apply ℚ[X] A' (integralClosure ℚ[X] E) y, h]
  haveI : FaithfulSMul ℚ[X] A' := (faithfulSMul_iff_algebraMap_injective _ _).mpr hQA'
  haveI : Module.IsTorsionFree ℚ[X] A' := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  haveI : FaithfulSMul A' (integralClosure ℚ[X] E) := (faithfulSMul_iff_algebraMap_injective A' (integralClosure ℚ[X] E)).mpr hincl_inj
  haveI hH : IsGaloisGroup (fixingSubgroup Gal(E/RatFunc ℚ) (Set.range (algebraMap A' (integralClosure ℚ[X] E)))) A' (integralClosure ℚ[X] E) :=
    IsGaloisGroup.of_isScalarTower Gal(E/RatFunc ℚ) ℚ[X] (integralClosure ℚ[X] E) A'
  set H' := fixingSubgroup Gal(E/RatFunc ℚ) (Set.range (algebraMap A' (integralClosure ℚ[X] E))) with hH'def
  have hσK' : ∀ x : E, x ∈ K' → σ x = x := fun x hx =>
    (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.mem_zpowers σ)
  have hσH' : σ ∈ H' := by
    rw [hH'def, mem_fixingSubgroup_iff]
    rintro _ ⟨a, rfl⟩
    apply Subtype.ext
    show σ (((a : K') : E)) = ((a : K') : E)
    exact hσK' _ (a : K').2
  -- the instances of the cardinality formula
  haveI : Module.Finite ℚ[X] (integralClosure ℚ[X] E) := IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
  haveI : Module.Finite A' (integralClosure ℚ[X] E) := Module.Finite.of_restrictScalars_finite ℚ[X] A' (integralClosure ℚ[X] E)
  haveI : Module.IsTorsionFree A' (integralClosure ℚ[X] E) := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  haveI : Algebra.IsIntegral A' (integralClosure ℚ[X] E) := Algebra.IsInvariant.isIntegral A' (integralClosure ℚ[X] E) H'
  set Q' : Ideal A' := Q.under A' with hQ'def
  haveI : Q'.IsPrime := Ideal.IsPrime.under A' Q
  haveI : Q.LiesOver Q' := ⟨rfl⟩
  haveI : CharZero Q'.ResidueField := by
    let f : ℚ →+* Q'.ResidueField :=
      ((algebraMap A' Q'.ResidueField).comp (algebraMap ℚ[X] A')).comp Polynomial.C
    exact charZero_of_injective_ringHom f.injective
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := H') Q' Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q' Q H'] at hcard
  -- `σ` lies in the inertia of `Q` in `H'`, and is nontrivial
  have hσI : (⟨σ, hσH'⟩ : H') ∈ Q.inertia H' := by
    intro x
    obtain ⟨c', hc', hc'Q⟩ := hσ x
    have : (⟨σ, hσH'⟩ : H') • x = c' := by
      apply Subtype.ext
      rw [hc']
      rfl
    rw [this]
    exact hc'Q
  have hIne : Q.inertia H' ≠ ⊥ := by
    intro h
    have h1 : (⟨σ, hσH'⟩ : H') ∈ (⊥ : Subgroup H') := h ▸ hσI
    rw [Subgroup.mem_bot] at h1
    exact hne (congrArg Subtype.val h1)
  have h2le : 1 < Q.ramificationIdx A' := by
    rw [← hcard]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hIne
  -- the tower `ℚ[X] ⊆ A' ⊆ B`
  have htow := Ideal.ramificationIdx_tower (R := ℚ[X]) Q' Q
  have he0 : Q.ramificationIdx ℚ[X] ≠ 0 := by
    rintro h0
    rw [h0, zero_dvd_iff] at he
    exact two_ne_zero he
  have he2 : Q.ramificationIdx ℚ[X] ≤ 2 := Nat.le_of_dvd two_pos he
  have he1 : Q'.ramificationIdx ℚ[X] = 1 := by
    have hpos : Q'.ramificationIdx ℚ[X] ≠ 0 := by
      intro h0; rw [htow, h0, zero_mul] at he0; exact he0 rfl
    rw [htow] at he2
    have : Q'.ramificationIdx ℚ[X] * 2 ≤ 2 :=
      le_trans (Nat.mul_le_mul_left _ h2le) he2
    omega
  -- `s` lies in `A'`
  have hsK' : s ∈ K' := by
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, hσs, ih (Subgroup.zpow_mem_zpowers σ n)]
    | pred n ih =>
      have h1 : (σ ^ (-(n : ℤ) - 1)) (σ s) = (σ ^ (-(n : ℤ))) s := by
        rw [← AlgEquiv.mul_apply, ← zpow_add_one, sub_add_cancel]
      rw [hσs] at h1
      rw [h1, ih (Subgroup.zpow_mem_zpowers σ _)]
  have hintE : IsIntegral ℚ[X] s := by
    refine ⟨X ^ 2 - Polynomial.C (C c * (X - C b)), monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hs, sub_self]
  have hintK : IsIntegral ℚ[X] (⟨s, hsK'⟩ : K') := by
    exact isIntegral_algebraMap_iff.mp hintE
  set s' : A' := ⟨⟨s, hsK'⟩, hintK⟩ with hs'def
  have hs'B : ((algebraMap A' (integralClosure ℚ[X] E) s' : integralClosure ℚ[X] E) : E) = s := rfl
  have hs'sq : s' ^ 2 = algebraMap ℚ[X] A' (C c * (X - C b)) := by
    apply hincl_inj
    apply Subtype.ext
    rw [map_pow, ← IsScalarTower.algebraMap_apply]
    show (((algebraMap A' (integralClosure ℚ[X] E) s' : integralClosure ℚ[X] E) : E)) ^ 2 = _
    rw [hs'B, hs]
    rfl
  -- `s' ∈ Q'`
  have hpQ : C c * (X - C b) ∈ Q.under ℚ[X] := by
    rw [hQu, Ideal.mem_span_singleton]
    exact dvd_mul_left _ _
  have hs'Q : s' ∈ Q' := by
    apply (inferInstance : Q'.IsPrime).mem_of_pow_mem 2
    rw [hs'sq, ← Ideal.mem_comap, ← Ideal.under_def, hQ'def, Ideal.under_under]
    exact hpQ
  -- `p A' ⊆ Q'²`
  have hle : Ideal.map (algebraMap ℚ[X] A') (Ideal.span {X - C b}) ≤ Q' ^ 2 := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    rw [Set.mem_singleton_iff] at hf
    subst hf
    have : algebraMap ℚ[X] A' (X - C b) = algebraMap ℚ[X] A' (C c⁻¹) * s' ^ 2 := by
      rw [hs'sq, ← map_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hs'Q 2)
  -- contradiction with `e(Q' | p) = 1`
  haveI : Q'.LiesOver (Ideal.span {X - C b}) := ⟨by rw [hQ'def, Ideal.under_under, hQu]⟩
  have hp0 : (Ideal.span {X - C b} : Ideal ℚ[X]) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero b
  have he1' := Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {X - C b}) Q' hp0
  rw [he1] at he1'
  have h2mem : 2 ∈ {n | Ideal.map (algebraMap ℚ[X] A') (Ideal.span {X - C b}) ≤ Q' ^ n} := hle
  by_cases hbdd : BddAbove {n | Ideal.map (algebraMap ℚ[X] A') (Ideal.span {X - C b}) ≤ Q' ^ n}
  · have := le_csSup hbdd h2mem
    rw [Ideal.ramificationIdx'] at he1'
    omega
  · rw [Ideal.ramificationIdx', Nat.sSup_of_not_bddAbove hbdd] at he1'
    exact zero_ne_one he1'

end Ram

/-- **`HeckeVertWitness` by route NV, with `RamifiedSqrtInertia` proved** (compiled): the bundle fields `r1r2`,
`t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints` and four named Props. -/
theorem heckeVertWitness_of_nv' (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : NVLocalInertia) (hV : VertInertiaTrivial)
    (hF : HeckeBranchFibreUnram) (hQ : HeckeSqrtBranch) : HeckeVertWitness :=
  heckeVertWitness_of_nv hRR hT hA hS hW hL ramifiedSqrtInertia hV hF hQ

/-! ## `VertInertiaTrivial` is proved (Hilbert theory over `ℤ[X]_{(p)}`) -/

/-- A finite extension of degree `< p` of a field in which `p = 0` is separable. -/
theorem isSeparable_of_finrank_lt {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) (hp : p.Prime) (hK : (p : K) = 0)
    (h : Module.finrank K L < p) : Algebra.IsSeparable K L := by
  have hchar : ringChar K = p := by
    have hd : ringChar K ∣ p := (ringChar.spec K p).mp hK
    rcases (Nat.dvd_prime hp).mp hd with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact h1
  constructor
  intro x
  have hint : IsIntegral K x := IsIntegral.of_finite K x
  have hirr := minpoly.irreducible hint
  show (minpoly K x).Separable
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  intro hd
  set d := (minpoly K x).natDegree with hddef
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hdle : d ≤ Module.finrank K L := minpoly.natDegree_le x
  have hcoeff := congrArg (fun f => Polynomial.coeff f (d - 1)) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hcoeff
  rw [Nat.sub_add_cancel hd0] at hcoeff
  have hmon : (minpoly K x).coeff d = 1 := minpoly.monic hint
  rw [hmon, one_mul] at hcoeff
  have hcast : ((d - 1 : ℕ) : K) + 1 = (d : K) := by
    rw [← Nat.cast_succ]
    congr 1
    omega
  rw [hcast] at hcoeff
  have := (ringChar.spec K d).mp hcoeff
  rw [hchar] at this
  have := Nat.le_of_dvd hd0 this
  omega

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **`VertInertiaTrivial` is a theorem** (compiled): over the DVR `R₀ = ℤ[X]_{(p)}` and `S₀` its integral closure in
`E`, Mathlib's `card_inertia_eq_ramificationIdxIn` (residue extensions separable: degree `< p`) gives
`e(q₂ | R₀) = |I(q₂)| = 1` for a prime `q₂` over the maximal ideal (its inertia lies in that of `q₂ ∩ B`); so `p`
generates the maximal ideal of `S₀_{q₂}`, a local-ring witness (`vertUnramWitness_of_local`). -/
theorem vertInertiaTrivial : VertInertiaTrivial := by
  intro E _ _ _ _ _ _ p hp hdeg hI
  letI := intPolyAlg E
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  haveI := isFractionRing_int
  haveI := vertPrime_isPrime p hp
  -- the DVR `R₀ = ℤ[X]_{(p)}`
  set R₀ := Localization.AtPrime (vertPrime p) with hR₀def
  letI : CommRing R₀ := inferInstanceAs (CommRing (Localization.AtPrime (vertPrime p)))
  have hunit : ∀ y : (vertPrime p).primeCompl, IsUnit (algebraMap ℤ[X] (RatFunc ℚ) y) := by
    intro y
    rw [isUnit_iff_ne_zero, Ne, map_eq_zero_iff _ (IsFractionRing.injective ℤ[X] (RatFunc ℚ))]
    intro h0
    exact y.2 (h0 ▸ Ideal.zero_mem _)
  letI : Algebra R₀ (RatFunc ℚ) := (IsLocalization.lift hunit).toAlgebra
  haveI : IsScalarTower ℤ[X] R₀ (RatFunc ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  haveI : IsFractionRing R₀ (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (vertPrime p).primeCompl R₀ (RatFunc ℚ)
  letI : Algebra R₀ E := ((algebraMap (RatFunc ℚ) E).comp (algebraMap R₀ (RatFunc ℚ))).toAlgebra
  haveI : IsScalarTower R₀ (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℤ[X] R₀ E := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply ℤ[X] (RatFunc ℚ) E, IsScalarTower.algebraMap_apply ℤ[X] R₀ (RatFunc ℚ)]
    rfl)
  haveI : IsNoetherianRing R₀ := IsLocalization.isNoetherianRing (vertPrime p).primeCompl R₀ inferInstance
  haveI : IsIntegrallyClosed R₀ :=
    isIntegrallyClosed_of_isLocalization R₀ (vertPrime p).primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors _)
  haveI : IsDomain R₀ :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (vertPrime p))
  have hpmem : C (p : ℤ) ∈ vertPrime p := Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  have hp0 : algebraMap ℤ[X] R₀ (C (p : ℤ)) ≠ 0 := by
    intro h
    have := congrArg (algebraMap R₀ (RatFunc ℚ)) h
    rw [← IsScalarTower.algebraMap_apply, map_zero,
      map_eq_zero_iff _ (IsFractionRing.injective ℤ[X] (RatFunc ℚ))] at this
    exact hp.ne_zero (by exact_mod_cast (C_eq_zero.mp this))
  have hpm : algebraMap ℤ[X] R₀ (C (p : ℤ)) ∈ IsLocalRing.maximalIdeal R₀ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hpmem
  have hnf : ¬ IsField R₀ := by
    intro hf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.1 hf] at hpm
    exact hp0 (Ideal.mem_bot.1 hpm)
  have huniq : ∃! P : Ideal R₀, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal R₀, ⟨?_, inferInstance⟩, ?_⟩
    · intro h
      rw [h] at hpm
      exact hp0 (Ideal.mem_bot.1 hpm)
    · rintro P' ⟨hne, hprime⟩
      set Q' := P'.comap (algebraMap ℤ[X] R₀) with hQ'def
      haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
      have hQ'le : Q' ≤ vertPrime p := by
        intro b hb
        by_contra hbQ
        have hu : IsUnit (algebraMap ℤ[X] R₀ b) :=
          IsLocalization.map_units R₀ (⟨b, hbQ⟩ : (vertPrime p).primeCompl)
        exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hb hu)
      have hmc : Q'.map (algebraMap ℤ[X] R₀) = P' :=
        IsLocalization.map_under (vertPrime p).primeCompl R₀ P'
      have hQ'ne : Q' ≠ ⊥ := by
        intro h0
        apply hne
        rw [← hmc, h0, Ideal.map_bot]
      have hQ'eq : Q' = vertPrime p := eq_vertPrime hp Q' hQ'ne hQ'le
      rw [← hmc, hQ'eq]
      exact Localization.AtPrime.map_eq_maximalIdeal
  have key : (IsIntegrallyClosed R₀ ∧ ∃! P : Ideal R₀, P ≠ ⊥ ∧ P.IsPrime) ↔
      IsDiscreteValuationRing R₀ := (IsDiscreteValuationRing.TFAE R₀ hnf).out 4 1
  haveI : IsDiscreteValuationRing R₀ := key.mp ⟨inferInstance, huniq⟩
  -- `S₀`, the integral closure of `R₀` in `E`, and the Galois group
  have hR₀E : Function.Injective (algebraMap R₀ E) :=
    (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective R₀ (RatFunc ℚ))
  haveI : Module.IsTorsionFree R₀ E := Module.isTorsionFree_iff_algebraMap_injective.mpr hR₀E
  haveI : Module.Finite R₀ (integralClosure R₀ E) :=
    IsIntegralClosure.finite R₀ (RatFunc ℚ) E (integralClosure R₀ E)
  haveI : Algebra.IsAlgebraic R₀ E :=
    (IsFractionRing.comap_isAlgebraic_iff (K := RatFunc ℚ)).mpr inferInstance
  haveI : IsFractionRing (integralClosure R₀ E) E :=
    integralClosure.isFractionRing_of_algebraic (fun x hx => hR₀E (hx.trans (map_zero _).symm))
  haveI : SMulCommClass Gal(E/RatFunc ℚ) R₀ E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply R₀ (RatFunc ℚ) E, AlgEquiv.commutes]⟩
  haveI hG : IsGaloisGroup Gal(E/RatFunc ℚ) R₀ (integralClosure R₀ E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/RatFunc ℚ) R₀ (integralClosure R₀ E) (RatFunc ℚ) E
  have hR₀S : Function.Injective (algebraMap R₀ (integralClosure R₀ E)) := by
    intro x y h
    apply hR₀E
    rw [IsScalarTower.algebraMap_apply R₀ (integralClosure R₀ E) E x,
      IsScalarTower.algebraMap_apply R₀ (integralClosure R₀ E) E y, h]
  haveI : FaithfulSMul R₀ (integralClosure R₀ E) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hR₀S
  haveI : Module.IsTorsionFree R₀ (integralClosure R₀ E) := inferInstance
  haveI : IsDedekindDomain R₀ := inferInstance
  haveI : Module.Flat R₀ (integralClosure R₀ E) := by
    refine (IsDedekindDomain.flat_iff_torsion_eq_bot (R := R₀) (M := integralClosure R₀ E)).mpr ?_
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_torsion_iff] at hx
    obtain ⟨a, ha⟩ := hx
    rw [Submodule.mem_bot]
    have ha' : ((a • x : integralClosure R₀ E) : E) = 0 := by rw [ha]; rfl
    rw [Submonoid.smul_def, Algebra.smul_def, Subalgebra.coe_mul] at ha'
    rcases mul_eq_zero.mp ha' with h0 | h0
    · exfalso
      have : ((algebraMap R₀ (integralClosure R₀ E) (a : R₀) : integralClosure R₀ E) : E) =
          algebraMap R₀ E (a : R₀) := rfl
      rw [this, map_eq_zero_iff _ hR₀E] at h0
      exact nonZeroDivisors.coe_ne_zero a h0
    · exact Subtype.ext h0
  haveI : IsDedekindDomain (integralClosure R₀ E) :=
    integralClosure.isDedekindDomain (A := R₀) (K := RatFunc ℚ) (L := E)
  -- a prime of `S₀` over the maximal ideal
  set m₀ := IsLocalRing.maximalIdeal R₀ with hm₀
  obtain ⟨q₂, hq₂, hq₂u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := integralClosure R₀ E) m₀ (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      rw [hR₀S (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  haveI := hq₂
  haveI : q₂.LiesOver m₀ := ⟨hq₂u.symm⟩
  haveI : Fintype (m₀.primesOver (integralClosure R₀ E)) :=
    Set.Finite.fintype (IsDedekindDomain.primesOver_finite m₀ (integralClosure R₀ E))
  -- the residue extensions over `m₀` are separable (degree `< p`)
  have hcardG : Nat.card Gal(E/RatFunc ℚ) = Module.finrank (RatFunc ℚ) E :=
    IsGalois.card_aut_eq_finrank (RatFunc ℚ) E
  haveI : Algebra.HasSeparableResidueFieldsAt R₀ (integralClosure R₀ E) m₀ := by
    constructor
    intro q _ _
    letI := Localization.AtPrime.algebraOfLiesOver m₀ q
    have hf : q.inertiaDeg R₀ = Module.finrank m₀.ResidueField q.ResidueField :=
      Ideal.inertiaDeg_eq m₀ q
    have hfpos : 0 < q.inertiaDeg R₀ := Ideal.inertiaDeg_pos q R₀
    haveI : Module.Free m₀.ResidueField q.ResidueField := Module.Free.of_divisionRing _ _
    haveI : Module.Finite m₀.ResidueField q.ResidueField :=
      Module.finite_of_finrank_pos (hf ▸ hfpos)
    have hsum := Ideal.sum_ramification_inertia_eq_card m₀ (integralClosure R₀ E)
      (G := Gal(E/RatFunc ℚ))
    have hle : q.inertiaDeg R₀ ≤ Nat.card Gal(E/RatFunc ℚ) := by
      rw [← hsum]
      have hmem : (⟨q, ⟨‹_›, ‹_›⟩⟩ : m₀.primesOver (integralClosure R₀ E)) ∈ Finset.univ :=
        Finset.mem_univ _
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)
      exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos (R := R₀) (q := q))
    refine isSeparable_of_finrank_lt p hp ?_ ?_
    · have : algebraMap R₀ m₀.ResidueField (algebraMap ℤ[X] R₀ (C (p : ℤ))) = 0 :=
        Ideal.algebraMap_residueField_eq_zero.mpr hpm
      rw [← map_natCast (algebraMap R₀ m₀.ResidueField), ← this]
      congr 1
      rw [← map_natCast (algebraMap ℤ[X] R₀)]
      congr 1
    · omega
  -- `|I(q₂)| = e(q₂)`
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/RatFunc ℚ)) m₀ q₂
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx m₀ q₂ Gal(E/RatFunc ℚ)] at hcard
  -- the inclusion `B_ℤ → S₀` and the vertical prime `q₀ = q₂ ∩ B_ℤ`
  let ι : integralClosure ℤ[X] E →+* integralClosure R₀ E :=
    { toFun := fun x => ⟨(x : E), IsIntegral.tower_top (A := R₀) x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hιE : ∀ x, ((ι x : integralClosure R₀ E) : E) = (x : E) := fun _ => rfl
  set q₀ := q₂.comap ι with hq₀def
  haveI hq₀ : q₀.IsPrime := Ideal.comap_isPrime _ _
  have hcomp : ι.comp (algebraMap ℤ[X] (integralClosure ℤ[X] E)) =
      (algebraMap R₀ (integralClosure R₀ E)).comp (algebraMap ℤ[X] R₀) := by
    refine RingHom.ext fun x => Subtype.ext ?_
    show algebraMap ℤ[X] E x = algebraMap R₀ E (algebraMap ℤ[X] R₀ x)
    rw [← IsScalarTower.algebraMap_apply]
  have hq₀u : q₀.under ℤ[X] = vertPrime p := by
    rw [Ideal.under_def, hq₀def, Ideal.comap_comap, hcomp, ← Ideal.comap_comap]
    show Ideal.comap (algebraMap ℤ[X] R₀) (q₂.under R₀) = vertPrime p
    rw [hq₂u, hm₀]
    exact Localization.AtPrime.under_maximalIdeal
  -- the inertia of `q₂` is trivial
  have hItriv : Ideal.inertia Gal(E/RatFunc ℚ) q₂ = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    apply hI q₀ hq₀ hq₀u σ
    intro b
    refine ⟨⟨σ (b : E), ?_⟩, rfl, ?_⟩
    · exact (b.2).map ((σ : E ≃ₐ[RatFunc ℚ] E).toAlgHom.restrictScalars ℤ[X])
    · show ι (_ - b) ∈ q₂
      have h := hσ (ι b)
      convert h using 1
  have he1 : q₂.ramificationIdx R₀ = 1 := by
    rw [← hcard, hItriv, Subgroup.card_bot]
  -- `p` generates the maximal ideal of the local ring `S₀_{q₂}`
  letI : CommRing (Localization.AtPrime q₂) := inferInstance
  have hm : (q₂.under R₀).map (algebraMap R₀ (Localization.AtPrime q₂)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q₂) := by
    have h := he1
    rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
      Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
      IsLocalRing.isMaximal_iff] at h
    exact h
  set x : Localization.AtPrime q₂ :=
    algebraMap R₀ (Localization.AtPrime q₂) (algebraMap ℤ[X] R₀ (C (p : ℤ))) with hxdef
  have hm₀span : m₀ = Ideal.span {algebraMap ℤ[X] R₀ (C (p : ℤ))} := by
    have hv : vertPrime p = Ideal.span {C (p : ℤ)} := by
      unfold vertPrime
      rw [Ideal.map_span, Set.image_singleton]
    have hmap : Ideal.map (algebraMap ℤ[X] R₀) (vertPrime p) =
        Ideal.map (algebraMap ℤ[X] R₀) (Ideal.span {C (p : ℤ)}) := congrArg _ hv
    rw [hm₀, ← Localization.AtPrime.map_eq_maximalIdeal, hmap, Ideal.map_span, Set.image_singleton]
  have hmx : IsLocalRing.maximalIdeal (Localization.AtPrime q₂) = Ideal.span {x} := by
    rw [← hm, hq₂u, hm₀span, Ideal.map_span, Set.image_singleton]
  have hinjL : Function.Injective (algebraMap (integralClosure R₀ E) (Localization.AtPrime q₂)) :=
    haveI := IsLocalization.AtPrime.faithfulSMul (Localization.AtPrime q₂) (integralClosure R₀ E) q₂
    FaithfulSMul.algebraMap_injective _ _
  have hx0 : x ≠ 0 := by
    rw [hxdef, IsScalarTower.algebraMap_apply R₀ (integralClosure R₀ E) (Localization.AtPrime q₂)]
    intro h
    apply hp0
    apply hR₀S
    apply hinjL
    rw [h, map_zero, map_zero]
  have hxm2 : x ∉ (IsLocalRing.maximalIdeal (Localization.AtPrime q₂)) ^ 2 := by
    rw [hmx, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨r, hr⟩
    have h1 : x * ((1 : Localization.AtPrime q₂) - x * r) = 0 := by
      linear_combination hr
    rcases mul_eq_zero.mp h1 with h | h
    · exact hx0 h
    · have hu : IsUnit x := IsUnit.of_mul_eq_one (b := r) (by linear_combination -h)
      have hxm : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q₂) := by
        rw [hmx]; exact Ideal.mem_span_singleton_self x
      exact (IsLocalRing.mem_maximalIdeal x).mp hxm hu
  -- the local-ring witness
  refine vertUnramWitness_of_local E p hp ⟨q₀, Localization.AtPrime q₂, inferInstance, inferInstance,
    (algebraMap (integralClosure R₀ E) (Localization.AtPrime q₂)).comp ι, ?_, hq₀u, ?_⟩
  · rw [hq₀def, ← Ideal.comap_comap]
    congr 1
    exact (Localization.AtPrime.under_maximalIdeal).symm
  · have hψ : ((algebraMap (integralClosure R₀ E) (Localization.AtPrime q₂)).comp ι)
        (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C (p : ℤ))) = x := by
      rw [RingHom.comp_apply, ← RingHom.comp_apply ι, hcomp, RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply]
    rw [hψ]
    exact hxm2


/-- **`HeckeVertWitness` by route NV, with the two Hilbert-theory Props proved** (compiled): the bundle fields
`r1r2`, `t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints` and three named Props: `NVLocalInertia` (local algebra
of tame covers), `HeckeBranchFibreUnram` (from `shimuraMainThmIDeligneY3AbU`) and `HeckeSqrtBranch` (from
`elkiesX6StarPrinted`). -/
theorem heckeVertWitness_of_nvLocal (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : NVLocalInertia) (hF : HeckeBranchFibreUnram) (hQ : HeckeSqrtBranch) : HeckeVertWitness :=
  heckeVertWitness_of_nv hRR hT hA hS hW hL ramifiedSqrtInertia vertInertiaTrivial hF hQ

/-! ## `HeckeBranchFibreUnram` is proved (from `R1R2fp` and T5) -/

/-- **`HeckeBranchFibreUnram` is a theorem** from `R1R2fp` (its reciprocity clause at the CM points,
`residue_unramified_over_branch`) and T5 (through `MobiusGlue`, which transfers residue fields of points
between triples). -/
theorem heckeBranchFibreUnram (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure) :
    HeckeBranchFibreUnram := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324 𝔓 h𝔓 h𝔓u φ
  obtain ⟨Y₀, Φ₀, π₀, h1₀, h2₀, hbr⟩ := residue_unramified_over_branch hRR
  obtain ⟨g, hΦ, hπ⟩ := Pin.sameTripleMor_of_mobius (CurveGlue.mobiusGlue_of_T5 hT)
    (Pin.cm_objects_of_R1R2fp hRR) h1₀ h2₀ h1 h2
  obtain ⟨h, hO, -, hval⟩ := hN
  set ψ : integralClosure ℚ[X] E →+* Qbar := φ.comp (Ideal.Quotient.mk 𝔓) with hψdef
  let y : fieldPt Qbar ⟶ Y :=
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (PropTSRed.spec_to_specQ_eq _ _)
  have hC : ∀ c : ℚ, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) (C c)) = algebraMap ℚ Qbar c := by
    intro c
    have hsub : ((ψ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp C : ℚ →+* Qbar) =
        algebraMap ℚ Qbar := Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* Qbar => f c) hsub
  have hX : ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = (-16 / 27 : Qbar) := by
    have hmem : X - C (-16 / 27 : ℚ) ∈ 𝔓.under ℚ[X] := by
      rw [h𝔓u]; exact Ideal.mem_span_singleton_self _
    have h0 : ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) (X - C (-16 / 27 : ℚ))) = 0 := by
      rw [hψdef, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr (show _ ∈ 𝔓 from hmem),
        map_zero]
    rw [map_sub, map_sub, hC, sub_eq_zero] at h0
    rw [h0]
    simp
  have hyv : π.val (K := Qbar) y.left = OnePoint.some (-16 / 27 : Qbar) := by
    have := hval ψ
    rw [hX] at this
    exact this
  have hres : residueImage (X := Y.left) y.left = IntermediateField.adjoin ℚ (Set.range φ) := by
    show residueImage (X := Y.left) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = _
    rw [residueImage_comp_openImmersion h, residueImage_specMap]
    congr 1
    ext z
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨Ideal.Quotient.mk _ b, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact ⟨b, rfl⟩
  have h0 := hbr (y ≫ g) (Or.inr (Or.inr (by rw [← hπ y]; exact hyv)))
  rw [PropTSRed.residueImage_comp_eq_of_pt g hΦ y, hres] at h0
  obtain ⟨hfin, hdisc⟩ := h0
  letI : NumberField (IntermediateField.adjoin ℚ (Set.range φ)) := @NumberField.mk _ _ _ hfin
  exact GlueB3Unram.unramifiedAt_of_not_dvd_discr _ p hp (hdisc p hp (by omega))


/-- **`HeckeVertWitness` by route NV with three of the five Props proved** (compiled): the bundle fields `r1r2`,
`t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints` and two named Props, `NVLocalInertia` (local algebra of tame
covers) and `HeckeSqrtBranch` (from `elkiesX6StarPrinted`). No integral model of the Shimura curve is used. -/
theorem heckeVertWitness_of_nvSqrt (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : NVLocalInertia) (hQ : HeckeSqrtBranch) : HeckeVertWitness :=
  heckeVertWitness_of_nvLocal hRR hT hA hS hW hL (heckeBranchFibreUnram hRR hT) hQ

/-! ## The constant of the square root is controlled (`HeckeSqrtBranchAny`) -/

/-- A nonzero rational of `p`-adic valuation `0` has numerator and denominator prime to `p`. -/
theorem not_dvd_num_den_of_padicValRat_eq_zero (p : ℕ) [hp : Fact p.Prime] {u : ℚ} (hu : u ≠ 0)
    (h : padicValRat p u = 0) : ¬ (p : ℤ) ∣ u.num ∧ ¬ p ∣ u.den := by
  have hnum : u.num ≠ 0 := Rat.num_ne_zero.mpr hu
  have hcop : u.num.natAbs.Coprime u.den := u.reduced
  rw [padicValRat_def] at h
  constructor
  · intro hn
    have h1 : p ∣ u.num.natAbs := Int.natCast_dvd.mp hn
    have hd : ¬ p ∣ u.den := fun hd =>
      (Nat.Prime.coprime_iff_not_dvd hp.out).mp (Nat.Coprime.coprime_dvd_left h1 hcop) hd
    have hv1 : padicValNat p u.den = 0 := padicValNat.eq_zero_of_not_dvd hd
    have hv2 : 1 ≤ padicValNat p u.num.natAbs :=
      one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hnum) h1
    rw [padicValInt, hv1] at h
    omega
  · intro hd
    have hn : ¬ p ∣ u.num.natAbs := fun h1 =>
      (Nat.Prime.coprime_iff_not_dvd hp.out).mp (Nat.Coprime.coprime_dvd_left h1 hcop) hd
    have hv1 : padicValNat p u.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hn
    have hv2 : 1 ≤ padicValNat p u.den := one_le_padicValNat_of_dvd u.den_nz hd
    rw [padicValInt, hv1] at h
    omega

/-- **A square root of `q ∈ ℚ` in a number field unramified at `p` forces `v_p(q)` even.** -/
theorem even_padicValRat_of_sq_mem (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L] (p : ℕ)
    (hp : p.Prime) (hL : UnramifiedAt L p) (q : ℚ) (hq : q ≠ 0) (β : Qbar) (hβ : β ∈ L)
    (hsq : β ^ 2 = algebraMap ℚ Qbar q) : Even (padicValRat p q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  obtain ⟨k, hk⟩ := hodd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp0' : (p : Qbar) ≠ 0 := by exact_mod_cast hp.ne_zero
  set u : ℚ := q * (p : ℚ) ^ (-(2 * k + 1)) with hu
  have hu0 : u ≠ 0 := mul_ne_zero hq (zpow_ne_zero _ hp0)
  have hvu : padicValRat p u = 0 := by
    rw [hu, padicValRat.mul hq (zpow_ne_zero _ hp0), padicValRat.zpow _ (k := -(2 * k + 1)),
      padicValRat.self hp.one_lt, hk]
    ring
  obtain ⟨hnum, hden⟩ := not_dvd_num_den_of_padicValRat_eq_zero p hu0 hvu
  set γ : Qbar := (u.den : Qbar) * β * (p : Qbar) ^ (-k) with hγdef
  have hγL : γ ∈ L :=
    L.mul_mem (L.mul_mem (L.algebraMap_mem (u.den : ℚ)) hβ) (zpow_mem (L.algebraMap_mem (p : ℚ)) _)
  have hqu : algebraMap ℚ Qbar q = algebraMap ℚ Qbar u * (p : Qbar) ^ (2 * k + 1) := by
    rw [hu, map_mul, map_zpow₀, map_natCast, mul_assoc, ← zpow_add₀ hp0']
    simp
  have hud : (u.den : Qbar) * algebraMap ℚ Qbar u = (u.num : Qbar) := by
    have h := Rat.mul_den_eq_num u
    have := congrArg (algebraMap ℚ Qbar) h
    rw [map_mul, map_natCast, map_intCast] at this
    rw [mul_comm]; exact this
  have hγsq : γ ^ 2 = ((u.den * u.num * p : ℤ) : Qbar) := by
    rw [hγdef, mul_pow, mul_pow, hsq, hqu]
    push_cast
    rw [← zpow_natCast ((p : Qbar) ^ (-k)) 2, ← zpow_mul]
    have e : (u.den : Qbar) ^ 2 * (algebraMap ℚ Qbar u * (p : Qbar) ^ (2 * k + 1)) *
        (p : Qbar) ^ (-k * ((2 : ℕ) : ℤ)) =
        ((u.den : Qbar) * algebraMap ℚ Qbar u) * u.den * ((p : Qbar) ^ (2 * k + 1) *
          (p : Qbar) ^ (-k * ((2 : ℕ) : ℤ))) := by ring
    rw [e, hud, ← zpow_add₀ hp0']
    have e2 : 2 * k + 1 + -k * ((2 : ℕ) : ℤ) = 1 := by push_cast; ring
    rw [e2, zpow_one]
    ring
  -- the integral element `γ` and a prime of `𝓞 L` over `p`
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  set N : ℤ := u.den * u.num * p with hN
  have hγsqL : (⟨γ, hγL⟩ : L) ^ 2 = (N : L) := Subtype.ext (by
    rw [IntermediateField.coe_pow]
    rw [hγsq]
    rfl)
  have hintγ : IsIntegral ℤ (⟨γ, hγL⟩ : L) := by
    refine ⟨X ^ 2 - Polynomial.C N, monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hγsqL, sub_eq_zero]
    simp
  set γL : 𝓞 L := ⟨⟨γ, hγL⟩, hintγ⟩ with hγLdef
  have hγLsq : γL ^ 2 = (N : 𝓞 L) := by
    apply RingOfIntegers.coe_injective
    push_cast
    show (⟨γ, hγL⟩ : L) ^ 2 = _
    rw [hγsqL, map_intCast]
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P, hP, hPu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L)
    (Ideal.span {(p : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have : (x : 𝓞 L) = 0 := by simpa using hx
      have hx0 : x = 0 := by exact_mod_cast this
      rw [hx0]; exact Ideal.zero_mem _)
  have hpP : ((p : ℤ) : 𝓞 L) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [hPu]; exact Ideal.mem_span_singleton_self _
    simpa using h1
  have he := hL P hP hpP
  have hγP : γL ∈ P := by
    apply hP.mem_of_pow_mem 2
    rw [hγLsq, hN]
    push_cast
    exact P.mul_mem_left _ hpP
  have hsqP : ((p : ℤ) : 𝓞 L) * ((u.den * u.num : ℤ) : 𝓞 L) ∈ P ^ 2 := by
    have h2 : γL ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hγP 2
    rw [hγLsq, hN] at h2
    push_cast at h2 ⊢
    convert h2 using 1
    ring
  have hP0 : P ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpP
    have : ((p : ℤ) : 𝓞 L) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact this hpP
  have hPmax : P.IsMaximal := hP.isMaximal hP0
  have hrad : (P ^ 2).radical = P := by rw [Ideal.radical_pow P two_ne_zero, hP.radical]
  have hprim : (P ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hPmax)
  rcases (Ideal.isPrimary_iff.mp hprim).2 hsqP with h | h
  · -- `p ∈ P²` contradicts `e(P | p) = 1`
    have hle : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ P ^ 2 := by
      rw [Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
      simpa using h
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPu.symm⟩
    have hsp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
    have he' := Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hsp0
    rw [he] at he'
    have h2mem : 2 ∈ {n | Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ P ^ n} := hle
    by_cases hbdd : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ P ^ n}
    · have := le_csSup hbdd h2mem
      rw [Ideal.ramificationIdx'] at he'
      omega
    · rw [Ideal.ramificationIdx', Nat.sSup_of_not_bddAbove hbdd] at he'
      exact zero_ne_one he'
  · rw [hrad] at h
    have h1 : (u.den * u.num : ℤ) ∈ P.under ℤ := by simpa using h
    rw [hPu, Ideal.mem_span_singleton] at h1
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h1 with h2 | h2
    · exact hden (by exact_mod_cast h2)
    · exact hnum h2

open CategoryTheory AlgebraicGeometry in
/-- **A point over `0` with unramified residue field**, on every triple (from `R1R2fp` and T5). -/
theorem exists_point_zero_unram (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) :
    ∃ y : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = OnePoint.some 0 ∧
      UnramifiedAbove5 (residueImage (X := Y.left) y.left) := by
  have hM := CurveGlue.mobiusGlue_of_T5 hT
  have hCM := Pin.cm_objects_of_R1R2fp hRR
  obtain ⟨Y₁, Φ₁, π₁, h11, h21, hfib⟩ := exists_fibre_object hRR
  obtain ⟨y₁, P₁, -, hy₁⟩ := hfib (OnePoint.some 0)
  obtain ⟨g₁, hΦ₁, hπ₁⟩ := Pin.sameTripleMor_of_mobius hM hCM h11 h21 h1 h2
  set y := (Φ Qbar).symm (Φ₁ Qbar y₁) with hydef
  have hyg : y ≫ g₁ = y₁ := (Φ₁ Qbar).injective (by rw [← hΦ₁, hydef, Equiv.apply_symm_apply])
  have hπy : π.val (K := Qbar) y.left = OnePoint.some 0 := by rw [hπ₁ y, hyg, hy₁]
  obtain ⟨Y₀, Φ₀, π₀, h10, h20, hbr⟩ := residue_unramified_over_branch hRR
  obtain ⟨g₀, hΦ₀, hπ₀⟩ := Pin.sameTripleMor_of_mobius hM hCM h10 h20 h1 h2
  have h0 := hbr (y ≫ g₀) (Or.inl (by rw [← hπ₀ y]; exact hπy))
  rw [PropTSRed.residueImage_comp_eq_of_pt g₀ hΦ₀ y] at h0
  exact ⟨y, hπy, h0⟩

open CategoryTheory AlgebraicGeometry in
/-- **From any square root of `c (27X + 16)` in `E` to one with constant prime to `p`** (`p ≥ 5`): the residue
fields over `0` are unramified at `p` (`exists_point_zero_unram`) and contain `√c`, so `v_p(c)` is even. -/
theorem exists_good_sqrt (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π)
    (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] (hN : NormalizationModel Y π E)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (c : ℚ) (hc : c ≠ 0) (s : E)
    (hs : s ^ 2 = algebraMap ℚ[X] E (C c * (C 27 * X + C 16))) :
    ∃ (a : ℤ) (s' : E), ¬ (p : ℤ) ∣ a ∧
      s' ^ 2 = algebraMap ℚ[X] E (C (a : ℚ) * (C 27 * X + C 16)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hπy, hun⟩ := exists_point_zero_unram hRR hT h1 h2
  obtain ⟨h, hO, himg, hval⟩ := hN
  obtain ⟨y', hy'⟩ := himg y.left (by rw [hπy]; exact OnePoint.coe_ne_infty _)
  set ψ := (Spec.preimage y').hom with hψ
  have hy'' : y' = Spec.map (CommRingCat.ofHom ψ) := by
    rw [hψ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hψX : ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = 0 := by
    have := hval ψ
    rw [← hy'', ← hy', hπy] at this
    exact (OnePoint.coe_injective this).symm
  have hψC : ∀ r : ℚ, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) (C r)) = algebraMap ℚ Qbar r := by
    intro r
    have hsub : ((ψ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp C : ℚ →+* Qbar) =
        algebraMap ℚ Qbar := Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* Qbar => f r) hsub
  have hres : residueImage (X := Y.left) y.left = IntermediateField.adjoin ℚ (Set.range ψ) := by
    rw [hy', PropTSRed.residueImage_comp_openImmersion h y', hy'', PropTSRed.residueImage_specMap]
  -- `s` is integral over `ℚ[X]`
  have hintE : IsIntegral ℚ[X] s := by
    refine ⟨X ^ 2 - Polynomial.C (C c * (C 27 * X + C 16)), monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hs, sub_self]
  set sB : integralClosure ℚ[X] E := ⟨s, hintE⟩ with hsB
  have hsBsq : sB ^ 2 = algebraMap ℚ[X] (integralClosure ℚ[X] E) (C c * (C 27 * X + C 16)) :=
    Subtype.ext (by
      show s ^ 2 = algebraMap ℚ[X] E _
      exact hs)
  have hψs : ψ sB ^ 2 = algebraMap ℚ Qbar (16 * c) := by
    rw [← map_pow, hsBsq]
    simp only [map_mul, map_add, hψX, hψC, mul_zero, zero_add]
    rw [mul_comm]
  set β : Qbar := ψ sB / 4 with hβdef
  have hβL : β ∈ IntermediateField.adjoin ℚ (Set.range ψ) :=
    IntermediateField.div_mem _ (IntermediateField.subset_adjoin ℚ _ ⟨sB, rfl⟩)
      (IntermediateField.algebraMap_mem _ (4 : ℚ))
  have hβsq : β ^ 2 = algebraMap ℚ Qbar c := by
    rw [hβdef, div_pow, hψs, map_mul]
    norm_num
  rw [hres] at hun
  obtain ⟨hfin, hdisc⟩ := hun
  letI : NumberField (IntermediateField.adjoin ℚ (Set.range ψ)) := @NumberField.mk _ _ _ hfin
  have hU := GlueB3Unram.unramifiedAt_of_not_dvd_discr _ p hp (hdisc p hp hp5)
  obtain ⟨k, hk⟩ := even_padicValRat_of_sq_mem _ p hp hU c hc β hβL hβsq
  -- `c = p^{2k} u` with `u` a `p`-adic unit
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set u : ℚ := c * (p : ℚ) ^ (-(k + k)) with hu
  have hu0 : u ≠ 0 := mul_ne_zero hc (zpow_ne_zero _ hp0)
  have hvu : padicValRat p u = 0 := by
    rw [hu, padicValRat.mul hc (zpow_ne_zero _ hp0), padicValRat.zpow _ (k := -(k + k)),
      padicValRat.self hp.one_lt, hk]
    ring
  obtain ⟨hnum, hden⟩ := not_dvd_num_den_of_padicValRat_eq_zero p hu0 hvu
  set ι : ℚ →+* E := (algebraMap ℚ[X] E).comp C with hι
  refine ⟨u.den * u.num, ι u.den * s * ι ((p : ℚ) ^ (-k)), ?_, ?_⟩
  · intro hdvd
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h2 | h2
    · exact hden (by exact_mod_cast h2)
    · exact hnum h2
  · have hq : (u.den : ℚ) ^ 2 * c * ((p : ℚ) ^ (-k)) ^ 2 = ((u.den * u.num : ℤ) : ℚ) := by
      have hud : u * u.den = u.num := Rat.mul_den_eq_num u
      have hc' : c = u * (p : ℚ) ^ (k + k) := by
        rw [hu, mul_assoc, ← zpow_add₀ hp0]; simp
      rw [hc', ← zpow_natCast ((p : ℚ) ^ (-k)) 2, ← zpow_mul]
      push_cast
      have e : (u.den : ℚ) ^ 2 * (u * (p : ℚ) ^ (k + k)) * (p : ℚ) ^ (-k * 2) =
          (u * u.den) * u.den * ((p : ℚ) ^ (k + k) * (p : ℚ) ^ (-k * 2)) := by ring
      rw [e, hud, ← zpow_add₀ hp0]
      have e2 : k + k + -k * 2 = 0 := by ring
      rw [e2, zpow_zero]
      ring
    rw [mul_pow, mul_pow, hs, map_mul, map_mul]
    have : algebraMap ℚ[X] E (C (((u.den * u.num : ℤ) : ℚ))) = ι (((u.den * u.num : ℤ) : ℚ)) := rfl
    rw [this, ← hq, map_mul, map_mul, map_pow, map_pow]
    have : algebraMap ℚ[X] E (C c) = ι c := rfl
    rw [this]
    ring


/-- **GLUE (the `W`-quadratic subfield; from Elkies' model of `X₆`, the field `elkiesX6StarPrinted`), constant-free
form.** For a triple with R1fp, R1hecke, R2fp and any `E` carrying the normalization chart, `E` contains a square
root of `c (27X + 16)` for some nonzero rational `c`: the quadratic subextension of `ℚ(X₆)/ℚ(X)` ramified at
`−16/27` and `∞` (Elkies: `ℚ(X₆) = ℚ(X)(√X, √(−(27X + 16)))`, so `c = −1`; any `c` will do). Weaker than
`HeckeSqrtBranch` (`heckeSqrtBranchAny_of_heckeSqrtBranch`); the constant is controlled by `exists_good_sqrt`. -/
def HeckeSqrtBranchAny : Prop :=
  ∀ (Y : CategoryTheory.Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∃ (c : ℚ) (s : E), c ≠ 0 ∧ s ^ 2 = algebraMap ℚ[X] E (C c * (C 27 * X + C 16))

/-- `HeckeSqrtBranch` implies `HeckeSqrtBranchAny` (compiled). -/
theorem heckeSqrtBranchAny_of_heckeSqrtBranch (h : HeckeSqrtBranch) : HeckeSqrtBranchAny := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN
  obtain ⟨a, s, ha, hs⟩ := h Y Φ π h1 hh h2 E hN
  refine ⟨a, s, ?_, hs⟩
  intro h0
  have h0' : a = 0 := by exact_mod_cast h0
  exact ha 331 (by norm_num) (by norm_num) (by rw [h0']; exact dvd_zero _)

/-- **`HeckeVertWitness` by route NV from the bundle fields, `NVLocalInertia` and the constant-free
`HeckeSqrtBranchAny`** (compiled). -/
theorem heckeVertWitness_of_nvSqrtAny (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : NVLocalInertia) (hQ : HeckeSqrtBranchAny) : HeckeVertWitness := by
  have hB : HeckeBranch :=
    heckeBranch_of' hRR HeckeRestCurve.curveChartInf (HeckeRest.heckeFibreSizes_of hT hA hS hW) hT
  have hD : HeckeDegree := heckeDegree_of_torsion hT
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324
  obtain ⟨c, s, hc, hs⟩ := hQ Y Φ π h1 hh h2 E hN
  obtain ⟨a, s', ha, hs'⟩ := exists_good_sqrt hRR hT h1 h2 E hN p hp (by omega) c hc s hs
  exact vertUnramWitness_of_nv hL ramifiedSqrtInertia vertInertiaTrivial E p hp hp324
    (hB Y Φ π h1 hh h2 E hN) (hD Y Φ π h1 hh h2 E hN)
    (heckeBranchFibreUnram hRR hT Y Φ π h1 hh h2 E hN p hp hp324) a s' ha hs'

end SGRDirect

