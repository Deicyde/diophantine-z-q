import ZInQKernel.Contrib.GZDecomp.Decomp
import ZInQKernel.Contrib.GZStatements.Compat
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# `GZDecomp.FHNonvanishing` from Friedberg–Hoffstein and the twisted root number

`ZInQ.GZDecomp.FHNonvanishing` (hypothesis `hL2` of `ZInQ.OneProof.frozenTarget`) was a composite:
Friedberg–Hoffstein's nonvanishing theorem for central values of quadratic twists, with the root
number of the twist folded in. This file states the two published inputs separately, over the
same genuine objects (Tau Ceti's `Newform`, the root number `GZDecomp.rootNumber` pinned by Tau
Ceti's proved functional equation, `GZDecomp.coeff`, `GZDecomp.twistCoeff`, Mathlib's `jacobiSym`,
`ℚ_[p]`), and proves `FHNonvanishing` from them:

* `FriedbergHoffsteinB` (LEAF): Friedberg–Hoffstein, Ann. of Math. 142 (1995), Theorem B, for
  `F = ℚ`, `π = π_f` with `f` a weight-2 newform of trivial nebentypus, and local data `χ₀,v`
  unramified at the finite places of `S`;
* `TwistNewformRootNumber` (LEAF): Atkin–Li 1978 / Iwaniec–Kowalski Prop. 14.20: the twist of a
  newform by a quadratic character of conductor prime to the level is a newform of level `N r²`
  with root number `χ(−N) ε(f)` (Gauss sum `τ(χ_D)² = χ_D(−1)|D|` evaluated);
* the glue (proved here): Dirichlet's theorem (Mathlib) gives a prime `q ≡ −1 (mod 8N)`;
  `D₀ = −q` has `χ_{D₀}(−N) = −1`, so the twist by `χ_{D₀}` has root number `+1`; Friedberg–Hoffstein
  then gives `D` with `D / D₀` a square in `ℚ_p` for every `p ∣ 2N` and `D < 0`; reduction of
  `ℤ_p` modulo `p` (resp. `8`) turns this into the Heegner hypothesis.

Task gz-fh; report `docs/research/gz-fh.md`. This file gives the variant reduction
`ZInQ.GZFH.fhNonvanishing_of_printed` (two printed leaves) and the arithmetic glue shared with the
recommended one, `ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE`
(`Contrib/OneProof/FHNonvanishing.lean`: one printed leaf, the twisted root number proved in
`FHNonvanishing/TwistFE.lean`).
-/

open HeckeRing.GL2

namespace ZInQ.GZFH

open ZInQ.GZDecomp

/-! ## Definitions -/

/-- `D` is an odd fundamental discriminant other than `1`: `D ≡ 1 (mod 4)`, squarefree, `D ≠ 1`.
These are exactly the discriminants of the quadratic fields in which `2` is unramified; for them
`chiD D = (· / |D|)` is the Kronecker character `χ_D` of `ℚ(√D)` (`GZStatements.chiD_prime`,
`chiD_two` for `D < 0`; quadratic reciprocity in general). -/
def IsOddFundDisc (D : ℤ) : Prop := D ≠ 1 ∧ D % 4 = 1 ∧ Squarefree D

/-! ## The two printed leaves -/

/-- **Friedberg–Hoffstein, Theorem B (central values of quadratic twists), for weight-2 newforms
of trivial nebentypus over `ℚ` and local data unramified at the finite places of `S`.**

Let `f` be a newform of weight 2, level `N` and trivial nebentypus, and `π = π_f`. Let `S` be a
finite set of primes containing every prime dividing `2N` (with `∞`, the places of `S` in the
theorem). Let `χ₀ = χ_{D₀}` be the quadratic character of an odd fundamental discriminant `D₀ ≠ 1`
unramified at every `p ∈ S`. Suppose `ε(½, π ⊗ χ₀) = 1`, stated as: the twist `f ⊗ χ_{D₀}` is
the newform `g` of level `N D₀²` and trivial nebentypus with root number `rootNumber g = 1`. Then
there are infinitely many quadratic characters `χ = χ_D` with `χ_v = χ₀,v` at every `v ∈ S ∪ {∞}`
and `L(½, π ⊗ χ) ≠ 0`.

Dictionary used to state the conclusion over `ℤ` (all STANDARD):
* quadratic idele class characters of `ℚ` ↔ fundamental discriminants `D` (`χ_D` the character of
  `ℚ(√D)`); `χ_2 = χ₀,2` unramified forces `D` odd, so `IsOddFundDisc D`; "infinitely many" is
  rendered as "`|D| > B` for every `B`";
* `χ_{D,v} = χ_{D₀,v}` on `ℚ_v^×` iff `D / D₀ ∈ (ℚ_v^×)²` (the local character of `ℚ(√D)` is the
  Hilbert symbol `(D, ·)_v`, a nondegenerate pairing: Serre, *A course in arithmetic*, Ch. III,
  Thm. 2); at `v = ∞` this is `D D₀ > 0`;
* for `(D, N) = 1` (forced by the local condition at `p ∣ N`) the Dirichlet series
  `∑ aₙ(f) χ_D(n) n^{−s}` is the finite `L(s − ½, π_f ⊗ χ_D)`, and `s = 1` is the centre; it has an
  entire continuation (gz-decomp glue G6, `exists_isEntireCont_twist`), unique by
  `IsEntireCont.eq`, so the `∀ G` clause is not vacuous;
* `rootNumber g = ε(½, π_g)`: it is the sign of Tau Ceti's proved functional equation of the
  completed `L(g, s)` (gz-statements §2.3); a newform `g` whose coefficients are those of
  `f ⊗ χ_{D₀}` has `π_g ≅ π_f ⊗ χ₀` (strong multiplicity one).

Source: S. Friedberg, J. Hoffstein, *Nonvanishing theorems for automorphic L-functions on GL(2)*,
Ann. of Math. (2) 142 (1995), no. 2, 385–423, Theorem B (UNVERIFIED: label, page, whether `2 ∈ S`
is required, and whether `π` may be dihedral; statement recalled from memory, see
docs/research/gz-fh.md §2 and gz-statements.md §6 H1). The specialization (trivial central
character, `χ₀` unramified at the finite places of `S`, `S ∋ 2`) only narrows the theorem. -/
def FriedbergHoffsteinB : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ S : Finset ℕ, (∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S) →
  ∀ D₀ : ℤ, IsOddFundDisc D₀ → (∀ p ∈ S, ¬ (p : ℤ) ∣ D₀) →
    (∃ (M : ℕ) (_ : NeZero M) (g : Newform M 2) (hg : g.χ = 1), M = N * D₀.natAbs ^ 2 ∧
        (∀ n : ℕ, n ≠ 0 → coeff g n = twistCoeff f D₀ n) ∧ rootNumber g hg = 1) →
    ∀ B : ℕ, ∃ D : ℤ, B < D.natAbs ∧ IsOddFundDisc D ∧ 0 < D * D₀ ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → IsSquare ((D : ℚ_[p]) / (D₀ : ℚ_[p]))) ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0

/-- **Twist of a newform by a quadratic character of conductor prime to the level: newform of
level `N D²` with root number `χ_D(−N) ε(f)`.**

Let `f` be a newform of weight 2, level `N`, trivial nebentypus, and `D` an odd fundamental
discriminant `≠ 1` with `(D, N) = 1`. Then `f ⊗ χ_D`, with coefficients `aₙ(f) χ_D(n)`, is a
newform of level `N D²` and trivial nebentypus (`χ_D²` is principal), and its root number is
`ε(f ⊗ χ_D) = χ_D(−N) ε(f)`, where `χ_D(−N) = (−N / |D|)` (Jacobi symbol; the Kronecker symbol of
`D ≡ 1 mod 4`).

Printed form (Iwaniec–Kowalski, *Analytic number theory*, AMS Colloq. Publ. 53 (2004),
Prop. 14.20; Atkin–Li, Invent. Math. 48 (1978) 221–243, Thm. 3.1 / Cor.; Shimura 1971 Prop. 3.64
for the functional equation; all UNVERIFIED numbers): for `f` primitive in `S_k(N, ψ)` and `χ`
primitive mod `r`, `(r, N) = 1`, `f ⊗ χ` is primitive in `S_k(N r², ψ χ²)` with Fricke
pseudo-eigenvalue `η(f ⊗ χ) = ψ(r) χ(N) τ(χ)² r⁻¹ η(f)`. This leaf is its specialization to
`k = 2`, `ψ = 1`, `χ = χ_D`, with `τ(χ_D)² = χ_D(−1) |D|` (Gauss) and `rootNumber = i^k η`; for real
`χ` the readings `χ(N)`, `χ̄(N)`, `χ(−N)` of the print coincide once `τ(χ)²` is evaluated. -/
def TwistNewformRootNumber : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1),
  ∀ D : ℤ, IsOddFundDisc D → Nat.Coprime D.natAbs N →
    ∃ (M : ℕ) (_ : NeZero M) (g : Newform M 2) (hg : g.χ = 1), M = N * D.natAbs ^ 2 ∧
      (∀ n : ℕ, n ≠ 0 → coeff g n = twistCoeff f D n) ∧
      rootNumber g hg = (jacobiSym (-(N : ℤ)) D.natAbs : ℂ) * rootNumber f hχ

/-! ## Glue: local squares to Legendre symbols -/

/-- If `a / b` is a square in `ℚ_p` and `p ∤ b`, then `a = b y²` with `y ∈ ℤ_p`. -/
theorem exists_padicInt_of_isSquare_div {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) (h : IsSquare ((a : ℚ_[p]) / (b : ℚ_[p]))) :
    ∃ y : ℤ_[p], (a : ℤ_[p]) = b * y ^ 2 := by
  obtain ⟨x, hx⟩ := h
  have hb1 : ‖(b : ℚ_[p])‖ = 1 := by
    have h1 := Padic.norm_int_le_one (p := p) b
    have h2 : ¬ ‖(b : ℚ_[p])‖ < 1 := fun h => hb (Padic.norm_intCast_lt_one_iff.mp h)
    linarith [not_lt.mp h2]
  have hb0 : (b : ℚ_[p]) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hb1; exact zero_ne_one hb1
  have hax : (a : ℚ_[p]) = b * (x * x) := by
    rw [← hx]; field_simp
  have hxle : ‖x‖ ≤ 1 := by
    have ha := Padic.norm_int_le_one (p := p) a
    rw [hax, norm_mul, hb1, one_mul, norm_mul] at ha
    nlinarith [norm_nonneg x]
  refine ⟨⟨x, hxle⟩, PadicInt.ext ?_⟩
  rw [PadicInt.coe_intCast, PadicInt.coe_mul, PadicInt.coe_intCast, hax]
  congr 1
  show x * x = x ^ 2; ring

/-- If `a / b` is a square in `ℚ_p`, `p` odd, `b ≡ 1 (mod p)` and `a` squarefree, then `a` is a
nonzero square modulo `p`. -/
theorem zmod_of_isSquare_div {p : ℕ} [hp : Fact p.Prime] {a b : ℤ} (ha : Squarefree a)
    (hb : (p : ℤ) ∣ b - 1) (h : IsSquare ((a : ℚ_[p]) / (b : ℚ_[p]))) :
    (a : ZMod p) ≠ 0 ∧ IsSquare (a : ZMod p) := by
  have hpb : ¬ (p : ℤ) ∣ b := by
    intro hd
    have : (p : ℤ) ∣ 1 := by simpa using dvd_sub hd hb
    exact hp.out.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  obtain ⟨y, hy⟩ := exists_padicInt_of_isSquare_div hpb h
  have hb1 : (b : ZMod p) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (b - 1) p).mpr hb
    push_cast at this; linear_combination this
  have hmod : (a : ZMod p) = (PadicInt.toZMod y) ^ 2 := by
    have := congrArg PadicInt.toZMod hy
    rw [map_mul, map_pow, map_intCast, map_intCast, hb1, one_mul] at this
    exact this
  refine ⟨fun h0 => ?_, ⟨PadicInt.toZMod y, by rw [hmod]; ring⟩⟩
  -- `p ∣ y`, so `p² ∣ a`
  have hy0 : PadicInt.toZMod y = 0 := by
    rw [h0] at hmod; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hmod.symm
  have hymem : y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]; exact hy0
  have hylt : ‖y‖ < 1 := PadicInt.mem_nonunits.mp hymem
  have hyle : ‖y‖ ≤ (p : ℝ)⁻¹ := by
    obtain ⟨z, hz⟩ := (PadicInt.norm_lt_one_iff_dvd y).mp hylt
    rw [hz, norm_mul, PadicInt.norm_p]
    have := PadicInt.norm_le_one z
    have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith
  have hale : ‖(a : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(2 : ℕ) : ℤ) := by
    rw [hy, norm_mul, norm_pow]
    have hb' : ‖(b : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
    have h0y := norm_nonneg y
    have : ‖y‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ h0y hyle 2
    have e : (p : ℝ) ^ (-(2 : ℕ) : ℤ) = ((p : ℝ)⁻¹) ^ 2 := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [e]
    nlinarith [norm_nonneg (b : ℤ_[p]), pow_nonneg h0y 2]
  have hdvd : ((p : ℤ) ^ 2) ∣ a := by exact_mod_cast PadicInt.norm_int_le_pow_iff_dvd.mp hale
  have hu := ha (p : ℤ) (by simpa [sq] using hdvd)
  have h1 := Int.isUnit_iff_natAbs_eq.mp hu
  simp only [Int.natAbs_natCast] at h1
  exact hp.out.one_lt.ne' h1

/-- If `a / b` is a square in `ℚ_2`, `b ≡ 1 (mod 8)` and `a ≡ 1 (mod 4)`, then `a ≡ 1 (mod 8)`. -/
theorem mod_eight_of_isSquare_div {a b : ℤ} (ha : a % 4 = 1) (hb : (8 : ℤ) ∣ b - 1)
    (h : IsSquare ((a : ℚ_[2]) / (b : ℚ_[2]))) : a % 8 = 1 := by
  have hpb : ¬ ((2 : ℕ) : ℤ) ∣ b := by omega
  obtain ⟨y, hy⟩ := exists_padicInt_of_isSquare_div hpb h
  have h8 : ((2 : ℕ) ^ 3 : ℕ) = 8 := by norm_num
  have hb1 : (b : ZMod (2 ^ 3)) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (b - 1) (2 ^ 3)).mpr (by simpa using hb)
    push_cast at this; linear_combination this
  have hmod : (a : ZMod (2 ^ 3)) = (PadicInt.toZModPow 3 y) ^ 2 := by
    have := congrArg (PadicInt.toZModPow (p := 2) 3) hy
    rw [map_mul, map_pow, map_intCast, map_intCast, hb1, one_mul] at this
    exact this
  have hsq : ∀ z : ZMod (2 ^ 3), z ^ 2 ≠ 5 := by decide
  have h5 : a % 8 = 1 ∨ a % 8 = 5 := by omega
  rcases h5 with h1 | h5
  · exact h1
  · exfalso
    have : (a : ZMod (2 ^ 3)) = 5 := by
      have e : a = 8 * (a / 8) + 5 := by omega
      rw [e]; push_cast
      have : (8 : ZMod (2 ^ 3)) = 0 := by decide
      rw [this]; ring
    exact hsq _ (hmod ▸ this)

/-! ## The auxiliary discriminant `D₀ = −q` -/

/-- For a prime `q ≡ −1 (mod 8N)`, `D₀ = −q` is an odd imaginary fundamental discriminant with
the Heegner hypothesis for `N`. -/
theorem heegner_neg_prime {N q : ℕ} (hq : q.Prime) (hqN : (8 * N : ℤ) ∣ -(q : ℤ) - 1) :
    IsOddImagFundDisc (-(q : ℤ)) ∧ HeegnerHyp N (-(q : ℤ)) := by
  have h8 : (8 : ℤ) ∣ -(q : ℤ) - 1 := dvd_trans (Dvd.intro (N : ℤ) rfl) hqN
  have hD : IsOddImagFundDisc (-(q : ℤ)) := by
    refine ⟨by have := hq.pos; omega, by omega, ?_⟩
    have : Squarefree (q : ℤ) := Int.squarefree_natCast.mpr hq.squarefree
    exact fun x hx => this x (dvd_neg.mp hx)
  refine ⟨hD, (ZInQ.GZStatements.heegnerHyp_iff_split hD).mpr ⟨fun h2 => ?_, fun p hp hp2 hpN => ?_⟩⟩
  · omega
  · have hpd : (p : ℤ) ∣ -(q : ℤ) - 1 :=
      dvd_trans (by exact_mod_cast Dvd.dvd.mul_left hpN 8) hqN
    have : Fact p.Prime := ⟨hp⟩
    have h1 : ((-(q : ℤ) : ℤ) : ZMod p) = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (-(q : ℤ) - 1) p).mpr hpd
      push_cast at this ⊢; linear_combination this
    rw [h1]
    exact ⟨one_ne_zero, ⟨1, by ring⟩⟩

/-- **The auxiliary discriminant.** For `N ≠ 0` there is an odd imaginary fundamental
discriminant `D₀ ≡ 1 (mod 8N)` with the Heegner hypothesis for `N`: `D₀ = −q` for a prime
`q ≡ −1 (mod 8N)` (Dirichlet's theorem, Mathlib). -/
theorem exists_aux_disc {N : ℕ} (hN0 : N ≠ 0) :
    ∃ D₀ : ℤ, IsOddImagFundDisc D₀ ∧ HeegnerHyp N D₀ ∧ (8 * N : ℤ) ∣ D₀ - 1 := by
  have : NeZero (8 * N) := ⟨by omega⟩
  obtain ⟨q, -, hq, hqmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 8 * N) (a := -1) isUnit_one.neg 0
  have hqN : (8 * N : ℤ) ∣ -(q : ℤ) - 1 := by
    have : ((q : ℤ) : ZMod (8 * N)) = ((-1 : ℤ) : ZMod (8 * N)) := by push_cast; exact hqmod
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this
    have e : (-(q : ℤ) - 1) = -1 - q := by ring
    rw [e]; exact_mod_cast this
  obtain ⟨hD₀, hH₀⟩ := heegner_neg_prime hq hqN
  exact ⟨-(q : ℤ), hD₀, hH₀, hqN⟩

theorem mem_primeFactors_two_mul {N : ℕ} (hN0 : N ≠ 0) {p : ℕ} (hp : p.Prime) (hpd : p ∣ 2 * N) :
    p ∈ (2 * N).primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩

/-- `D₀ ≡ 1 (mod 8N)` is prime to every `p ∣ 2N`. -/
theorem not_dvd_of_mem_primeFactors {N : ℕ} {D₀ : ℤ} (h8 : (8 * N : ℤ) ∣ D₀ - 1) :
    ∀ p ∈ (2 * N).primeFactors, ¬ (p : ℤ) ∣ D₀ := by
  intro p hpS hpD
  obtain ⟨hp, hpd, -⟩ := Nat.mem_primeFactors.mp hpS
  have hp2N : (p : ℤ) ∣ (2 * N : ℤ) := by exact_mod_cast hpd
  have h1 : (p : ℤ) ∣ D₀ - 1 :=
    dvd_trans hp2N (dvd_trans (Dvd.intro (4 : ℤ) (by ring)) h8)
  have : (p : ℤ) ∣ 1 := by
    have := dvd_sub hpD h1
    simpa using this
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

/-- **Local conditions to the Heegner hypothesis.** If `D₀ < 0`, `D₀ ≡ 1 (mod 8N)`, and `D` is an
odd fundamental discriminant with `D D₀ > 0` and `D / D₀` a square in `ℚ_p` for every `p ∣ 2N`,
then `D` is an odd imaginary fundamental discriminant with the Heegner hypothesis for `N`. -/
theorem heegner_of_local {N : ℕ} (hN0 : N ≠ 0) {D₀ D : ℤ} (hD₀ : D₀ < 0)
    (h8N : (8 * N : ℤ) ∣ D₀ - 1) (hDf : IsOddFundDisc D) (hsign : 0 < D * D₀)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], p ∈ (2 * N).primeFactors →
      IsSquare ((D : ℚ_[p]) / (D₀ : ℚ_[p]))) :
    IsOddImagFundDisc D ∧ HeegnerHyp N D := by
  have hDneg : D < 0 := by nlinarith
  have hDisc : IsOddImagFundDisc D := ⟨hDneg, hDf.2.1, hDf.2.2⟩
  refine ⟨hDisc, (ZInQ.GZStatements.heegnerHyp_iff_split hDisc).mpr
    ⟨fun h2 => ?_, fun p hp hp2 hpN => ?_⟩⟩
  · have h8 : (8 : ℤ) ∣ D₀ - 1 := dvd_trans (Dvd.intro (N : ℤ) rfl) h8N
    have := hloc 2 (mem_primeFactors_two_mul hN0 Nat.prime_two (dvd_mul_right 2 N))
    exact mod_eight_of_isSquare_div hDf.2.1 h8 this
  · have : Fact p.Prime := ⟨hp⟩
    have hpd : (p : ℤ) ∣ D₀ - 1 := by
      have hpN' : (p : ℤ) ∣ (N : ℤ) := by exact_mod_cast hpN
      exact dvd_trans (dvd_trans hpN' (Dvd.intro_left (8 : ℤ) rfl)) h8N
    exact zmod_of_isSquare_div hDf.2.2 hpd
      (hloc p (mem_primeFactors_two_mul hN0 hp (dvd_mul_of_dvd_right hpN 2)))

/-! ## The reduction -/

/-- **`FHNonvanishing` from Friedberg–Hoffstein Theorem B and the twisted root number.** -/
theorem fhNonvanishing_of_printed (hFH : FriedbergHoffsteinB) (hTw : TwistNewformRootNumber) :
    FHNonvanishing := by
  intro N _ f hχ hw B
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨D₀, hD₀, hH₀, h8N⟩ := exists_aux_disc hN0
  have hD₀f : IsOddFundDisc D₀ := ⟨by have := hD₀.1; omega, hD₀.2.1, hD₀.2.2⟩
  -- the twist by `χ_{D₀}` has root number `χ_{D₀}(−N) ε(f) = (−1)(−1) = +1`
  obtain ⟨M, _, g, hg, hM, hcoef, hroot⟩ :=
    hTw N f hχ D₀ hD₀f (ZInQ.GZStatements.coprime_of_heegnerHyp (ne_of_lt hD₀.1) hH₀)
  have hJ := ZInQ.GZStatements.jacobiSym_neg_level hN0 hD₀ hH₀
  have hroot1 : rootNumber g hg = 1 := by
    rw [hroot, hJ, hw]; push_cast; ring
  -- Friedberg–Hoffstein with `S = {p ∣ 2N}`
  obtain ⟨D, hDB, hDf, hsign, hloc, hG⟩ :=
    hFH N f hχ (2 * N).primeFactors (fun p hp hpd => mem_primeFactors_two_mul hN0 hp hpd) D₀
      hD₀f (not_dvd_of_mem_primeFactors h8N) ⟨M, inferInstance, g, hg, hM, hcoef, hroot1⟩ B
  obtain ⟨hDisc, hH⟩ := heegner_of_local hN0 hD₀.1 h8N hDf hsign hloc
  exact ⟨D, by have := hDisc.1; omega, hDisc, hH, hG⟩

end ZInQ.GZFH


#print axioms ZInQ.GZFH.fhNonvanishing_of_printed
