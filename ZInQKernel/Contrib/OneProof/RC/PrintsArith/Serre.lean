import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Basic

/-!
# Serre's open image theorem (non-CM), stated over the genuine `ℓ`-adic representations

Lane RC9. The proof of Theorem 5.3 cites "the non-CM open-image theorem \cite{serre}"
(`diophantine_zq.tex`, bibliography: J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini
des courbes elliptiques*, Invent. Math. 15 (1972), 259–331) at:

* tex 2882–2887 (`ex:arith-finite-heegner`, step 1): choose `n ≥ 2` with
  `1 + 2^n M₂(ℤ₂) ⊆ ρ_T(G_ℚ)` and `g ∈ G_ℚ` with `ρ_T(g) = uI`, `u = 1 + 2^n`;
* tex 3597–3605 (`ex:arith-moving-character`): `J = ρ_T(G_{ℚ(μ_{2^∞})})` is the determinant-one part
  of the image and contains `Γ_d = ker(SL₂(ℤ₂) → SL₂(ℤ/2^d))` for a fixed `d ≥ 2`;
* tex 1887–1889, 2479–2480, 7228–7231 (Kato's hypothesis (v), the fixed-witness argument): the
  image over `ℚ(μ_{2^∞})` contains an open subgroup of `SL₂(ℤ₂)`, hence a nonidentity unipotent,
  also after restriction to the index-at-most-two kernel of a quadratic character.

**The print, read for this lane** (scan of the published article, Göttingen digitization of
Invent. Math. 15): §4.4 "Image de `φ_∞`", p. 299, **Théorème 3**: *Si `E` n'a pas de
multiplication complexe, `ρ(G)` est un sous-groupe ouvert de `∏_{ℓ∈P} GL(T_ℓ)`*, where
`ρ = (ρ_ℓ)_ℓ : G = Gal(K̄/K) → ∏_ℓ GL(T_ℓ)` (§4.1, p. 293). Here `K = ℚ`. Its single-prime
consequence is assertion (4) of the Introduction (p. 260; proved in Serre's McGill notes, p. IV-11).
p. 300, **Corollaire 2**: the image of `Gal(K̄/K^cycl)` is an open subgroup of `∏_ℓ SL(T_ℓ)`; its
proof uses that `det ∘ ρ_ℓ` is the `ℓ`-adic cyclotomic character (McGill notes, pp. I-3, I-4).

**Form of the statement (DEPARTURE of form, equivalent).** "Open subgroup of `∏_ℓ GL(T_ℓ)`" is
stated as "contains a basic neighbourhood of `1`": a finite set `S` of primes and exponents `n_ℓ`
such that every family `(α_ℓ)_ℓ` of automorphisms with `α_ℓ ≡ 1 (mod ℓ^{n_ℓ})` for `ℓ ∈ S` (and
`α_ℓ` arbitrary for `ℓ ∉ S`) is `(ρ_ℓ(σ))_ℓ` for one `σ ∈ G_ℚ`. A subgroup of a topological group is
open iff it contains a neighbourhood of `1`; the sets `∏_{ℓ∈S}(1 + ℓ^{n_ℓ}End T_ℓ)^× × ∏_{ℓ∉S}GL(T_ℓ)`
form a neighbourhood basis of `1` in the product of the `ℓ`-adic groups `GL(T_ℓ) ≅ GL₂(ℤ_ℓ)`.

Contents:
* `SerreThm3` (PRINT);
* `serre_two_adic`, `serre_scalar` (PROVED from `SerreThm3`): the forms used at tex 2882–2887;
* `DetTateTwoCyclotomic` (GLUE here: `det ρ₂ = χ₂`, Weil pairing; proved for elliptic `E` as
  `ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic`) and `serre_SL2_part` (PROVED from
  `SerreThm3` and the GLUE): the form used at tex 3597–3605;
* `CMjInteger` (GLUE: CM `j`-invariants are algebraic integers) and `curve_hasNoCM` (PROVED from
  the GLUE): `E_ℓ` has no CM because `j(E_ℓ) = 35152/9` (tex 1765–1767, 1012–1013).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsArith

open scoped WeierstrassCurve

/-! ### The print -/

/-- **Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*, Invent.
Math. 15 (1972), 259–331, §4.4, Théorème 3, p. 299** (PRINT; read from the published scan), over
`K = ℚ`: if `E/ℚ` has no complex multiplication, `ρ(G_ℚ)` is open in `∏_ℓ GL(T_ℓ E)`, in the
neighbourhood-basis form (see the module docstring): there are a finite set `S` of primes and
exponents `n_ℓ` such that every family `(α_ℓ)_ℓ` of `ℤ_ℓ`-linear automorphisms of the Tate modules
with `α_ℓ ≡ 1 (mod ℓ^{n_ℓ})` for `ℓ ∈ S` is `(ρ_ℓ(σ))_ℓ` for a single `σ ∈ G_ℚ`.

Used at tex 2882 and 3600 (`\cite{serre}`), through `serre_two_adic`, `serre_scalar` and
`serre_SL2_part`. Hypotheses match: `E_ℓ` is non-CM (`curve_hasNoCM`).
Links: Serre 1972 https://doi.org/10.1007/BF01405086. -/
def SerreThm3 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], HasNoCM E →
    ∃ (S : Finset Nat.Primes) (n : Nat.Primes → ℕ),
      ∀ α : (ℓ : Nat.Primes) → (TateMod E ℓ ≃ₗ[ℤ_[(ℓ : ℕ)]] TateMod E ℓ),
        (∀ ℓ ∈ S, ∀ x : TateMod E ℓ, ∃ y : TateMod E ℓ,
          α ℓ x = x + ((ℓ : ℕ) : ℤ_[(ℓ : ℕ)]) ^ n ℓ • y) →
        ∃ σ : GalQ, ∀ ℓ : Nat.Primes, tateRep E ℓ σ = (α ℓ).toLinearMap

/-- The prime `2`. -/
abbrev two : Nat.Primes := ⟨2, Nat.prime_two⟩

/-! ### The two-adic forms used in Section 8 -/

/-- **The form used at tex 2882–2883** (PROVED from `SerreThm3`): for non-CM `E/ℚ` there is
`n ≥ 2` with `1 + 2^n End(T₂E) ⊆ ρ₂(G_ℚ)`: every automorphism of `T₂E` congruent to the identity
modulo `2^n` is `ρ₂(σ)` for some `σ ∈ G_ℚ`. -/
theorem serre_two_adic (hS : SerreThm3) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : HasNoCM E) :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ α : TateMod E 2 ≃ₗ[ℤ_[2]] TateMod E 2,
      (∀ x : TateMod E 2, ∃ y : TateMod E 2, α x = x + (2 : ℤ_[2]) ^ n • y) →
      ∃ σ : GalQ, tateRep E 2 σ = α.toLinearMap := by
  obtain ⟨S, n, h⟩ := hS E hE
  refine ⟨max 2 (n two), le_max_left _ _, fun α hα => ?_⟩
  -- The family equal to `α` at `2` and to the identity elsewhere.
  let β : (ℓ : Nat.Primes) → (TateMod E ℓ ≃ₗ[ℤ_[(ℓ : ℕ)]] TateMod E ℓ) :=
    Function.update (β := fun ℓ : Nat.Primes => TateMod E ℓ ≃ₗ[ℤ_[(ℓ : ℕ)]] TateMod E ℓ)
      (fun ℓ => LinearEquiv.refl _ _) two α
  have hβ2 : β two = α :=
    Function.update_self (β := fun ℓ : Nat.Primes => TateMod E ℓ ≃ₗ[ℤ_[(ℓ : ℕ)]] TateMod E ℓ)
      two α _
  have hβne : ∀ ℓ, ℓ ≠ two → β ℓ = LinearEquiv.refl _ _ := fun ℓ hℓ =>
    Function.update_of_ne (β := fun ℓ : Nat.Primes => TateMod E ℓ ≃ₗ[ℤ_[(ℓ : ℕ)]] TateMod E ℓ)
      hℓ α _
  obtain ⟨σ, hσ⟩ := h β fun ℓ _ x => by
    by_cases hℓ : ℓ = two
    · subst hℓ
      obtain ⟨y, hy⟩ := hα x
      refine ⟨(2 : ℤ_[2]) ^ (max 2 (n two) - n two) • y, ?_⟩
      rw [hβ2]
      change α x = x + (2 : ℤ_[2]) ^ n two • ((2 : ℤ_[2]) ^ (max 2 (n two) - n two) • y)
      rw [hy, smul_smul, ← pow_add, Nat.add_sub_cancel' (le_max_right _ _)]
    · exact ⟨0, by rw [hβne ℓ hℓ]; simp⟩
  have key : tateRep E 2 σ = (β two).toLinearMap := hσ two
  exact ⟨σ, by rw [key, hβ2]⟩

/-- `1 + 2^n` is a unit of `ℤ₂` for `n ≥ 1`. -/
theorem isUnit_one_add_two_pow {n : ℕ} (hn : 1 ≤ n) : IsUnit (1 + (2 : ℤ_[2]) ^ n) := by
  rw [PadicInt.isUnit_iff]
  have h2 : ‖(2 : ℤ_[2])‖ < 1 := by
    have h := PadicInt.norm_p (p := 2)
    simp only [Nat.cast_ofNat] at h
    rw [h]; norm_num
  have h2n : ‖(2 : ℤ_[2]) ^ n‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h2 (by omega)
  have h1 : ‖(1 : ℤ_[2])‖ = 1 := norm_one
  rw [PadicInt.norm_add_eq_max_of_ne (by rw [h1]; exact h2n.ne'), h1]
  exact max_eq_left h2n.le

/-- **The scalar element of tex 2883–2887** (PROVED from `SerreThm3`): for non-CM `E/ℚ` there are
`n ≥ 2` and `g ∈ G_ℚ` with `ρ₂(g) = u · id`, `u = 1 + 2^n` (then `e = v₂(u⁴ - 1) = n + 2`,
tex (H1)). -/
theorem serre_scalar (hS : SerreThm3) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : HasNoCM E) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ g : GalQ,
      ∀ x : TateMod E 2, tateRep E 2 g x = (1 + (2 : ℤ_[2]) ^ n) • x := by
  obtain ⟨n, hn, h⟩ := serre_two_adic hS E hE
  let u : ℤ_[2]ˣ := (isUnit_one_add_two_pow (n := n) (by omega)).unit
  obtain ⟨g, hg⟩ := h (LinearEquiv.smulOfUnit u) fun x => ⟨x, by
    show (u : ℤ_[2]) • x = x + (2 : ℤ_[2]) ^ n • x
    rw [IsUnit.unit_spec, add_smul, one_smul]⟩
  exact ⟨n, hn, g, fun x => by rw [hg]; rfl⟩

/-! ### The determinant-one part (tex 3597–3605) -/

/-- **GLUE (not proved here): `det ρ₂ = χ₂`.** The determinant of `ρ₂(σ)` is the `2`-adic
cyclotomic character of `σ` (Weil pairing; Serre 1972, p. 300, citing his McGill notes,
pp. I-3, I-4), in the direction used: if `det ρ₂(σ) = 1`, then `σ` fixes every `2`-power root of
unity. Proved for every elliptic `E/ℚ` from the Weil pairing:
`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic`. -/
def DetTateTwoCyclotomic (E : WeierstrassCurve ℚ) : Prop :=
  ∀ σ : GalQ, LinearMap.det (tateRep E 2 σ) = 1 →
    ∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ

/-- **The form used at tex 3597–3605** (PROVED from `SerreThm3` and the GLUE
`DetTateTwoCyclotomic`): for non-CM `E/ℚ` there is `d ≥ 2` such that every automorphism of `T₂E`
of determinant one and congruent to the identity modulo `2^d` (an element of `Γ_d` in a basis) is
`ρ₂(σ)` for some `σ ∈ G_{ℚ(μ_{2^∞})}`, i.e. `Γ_d ⊆ J = ρ₂(G_{ℚ(μ_{2^∞})})`. -/
theorem serre_SL2_part (hS : SerreThm3) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : HasNoCM E) (hdet : DetTateTwoCyclotomic E) :
    ∃ d : ℕ, 2 ≤ d ∧ ∀ α : TateMod E 2 ≃ₗ[ℤ_[2]] TateMod E 2,
      LinearMap.det α.toLinearMap = 1 →
      (∀ x : TateMod E 2, ∃ y : TateMod E 2, α x = x + (2 : ℤ_[2]) ^ d • y) →
      ∃ σ : GalQ, (∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ) ∧
        tateRep E 2 σ = α.toLinearMap := by
  obtain ⟨d, hd, h⟩ := serre_two_adic hS E hE
  refine ⟨d, hd, fun α hα1 hα => ?_⟩
  obtain ⟨σ, hσ⟩ := h α hα
  exact ⟨σ, hdet σ (by rw [hσ]; exact hα1), hσ⟩

/-! ### `E_ℓ` has no complex multiplication -/

/-- **PRINT + GLUE (not proved here): rational CM `j`-invariants are integers.** If `E/ℚ` has
complex multiplication over `ℚ̄`, then `j(E)` is an algebraic integer, hence an integer since it is
rational. The manuscript uses exactly this (tex 1766–1767: "a rational CM `j`-invariant is an
integer"). Printed (page-checked; bibitem `milnemf`): Milne, *Modular Functions and Modular Forms*,
v1.31 (2017), Corollary 12.15, p. 125: "If E is an elliptic curve over a number field k with
complex multiplication, then j(E) ∈ O_K." (the ring of integers of `k` is meant, as the proof
shows), with complex multiplication as defined on p. 124. GLUE: the complex multiplication of
`E_ℚ̄` is defined over a number field `k`, and `O_k ∩ ℚ = ℤ`. Earlier locator: Silverman, *Advanced
Topics in the Arithmetic of Elliptic Curves*, Theorem II.6.1 (page not checked).
Kind: definition (PRINT + GLUE input).
Links: Milne, Modular Functions and Modular Forms https://www.jmilne.org/math/CourseNotes/MF.pdf;
Silverman, Advanced Topics https://doi.org/10.1007/978-1-4612-0851-8. -/
def CMjInteger : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ¬ HasNoCM E → ∃ z : ℤ, E.j = z

/-- `j(E_ℓ) = 35152/9` for `ℓ ≠ 0` (tex 1765, 1012). -/
theorem curve_j {ℓ : ℚ} (hℓ : ℓ ≠ 0) :
    @WeierstrassCurve.j ℚ _ (curve ℓ) (ZInQ.Manuscript.PoleRC.curve_isElliptic hℓ) =
      35152 / 9 := by
  let _ := ZInQ.Manuscript.PoleRC.curve_isElliptic hℓ
  rw [WeierstrassCurve.j_eq, curve_c₄, curve_Δ]
  field_simp
  ring

/-- **`E_ℓ` has no complex multiplication** (PROVED from the GLUE `CMjInteger`): its
`j`-invariant `35152/9` is not an integer (tex 1766–1767). -/
theorem curve_hasNoCM (hcm : CMjInteger) {ℓ : ℚ} (hℓ : ℓ ≠ 0) :
    @HasNoCM (curve ℓ) (ZInQ.Manuscript.PoleRC.curve_isElliptic hℓ) := by
  let _ := ZInQ.Manuscript.PoleRC.curve_isElliptic hℓ
  by_contra hno
  obtain ⟨z, hz⟩ := hcm (curve ℓ) hno
  rw [curve_j hℓ] at hz
  have h9 : (35152 : ℚ) = 9 * z := by
    rw [← hz]; ring
  have h9' : (35152 : ℤ) = 9 * z := by exact_mod_cast h9
  omega

end ZInQ.Manuscript.RC.PrintsArith
