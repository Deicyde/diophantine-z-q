import ZInQKernel.Contrib.OneProof.BFHNonvanishing
import ZInQKernel.Contrib.OneProof.BFHPrinted.Kronecker

/-!
# Bump–Friedberg–Hoffstein 1990, clause (ii), over the Kronecker symbol `χ_D(n) = (D / n)`

Task bfh-kronecker (report `docs/research/bfh-kronecker.md`). bfh-leaf's leaf
`ZInQ.BFHPrinted.BFHClauseII` states clause (ii) of the opening theorem of Bump–Friedberg–Hoffstein
(Invent. Math. 102 (1990) 543–618) with `χ_d` the character `FHPrinted.idelicChar d` built from the
local norm-residue characters of `ℚ_p(√d)`. BFH's `χ_D` is the Kronecker symbol `n ↦ (D / n)`.
This file restates the leaf over the Kronecker symbol (`BFHPrinted.kroneckerSym`, defined in
`BFHPrinted/Kronecker.lean` by the textbook formula over Mathlib's `jacobiSym` and `ZMod.χ₈`), with
the splitting set `S` containing the primes dividing `N` as printed (`BFHClauseIIKronecker`), and
proves:

* the bridge: `(D / n) = idelicChar D n` for every fundamental discriminant and `n ≠ 0`
  (`idelicChar_eq_kroneckerSym`), and `chiD D n = (D / n)` for odd `D` (`chiD_eq_kroneckerSym`),
  with the Compat facts for the Kronecker symbol (`kroneckerSym_prime`, `kroneckerSym_two_of_one_mod_four`,
  `kroneckerSym_mul`);
* `bfhClauseIIKronecker_iff : BFHClauseIIKronecker ↔ BFHClauseII` (so the restated leaf is
  equivalent to bfh-leaf's, and no stronger);
* the use at `B = 4` only: `exists_heegnerDisc_of_bfhClauseIIKronecker` applies the leaf once, with
  `S` the primes dividing `2N`, and returns an odd imaginary fundamental discriminant `D < −4` with
  the Heegner hypothesis and `L(1, f, χ_D) ≠ 0` (`D ≡ 1 (mod 8)` and `D < 0` give `D ≤ −7`, so no
  prime beyond `2N` has to be split);
* `grossZagierCd_of_bfhClauseIIKronecker` and
  `frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker`: the assembly of
  `GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` with `FHNonvanishing`
  (used there at `B = 4` only) replaced by the leaf;
* `fhNonvanishing_of_bfhClauseIIKronecker : BFHClauseIIKronecker → FHNonvanishing` (all `B`; the
  drop-in alternative for `Main`).
-/

open HeckeRing.GL2 NumberField WeierstrassCurve

namespace ZInQ.BFHPrinted

open ZInQ.GZDecomp ZInQ.GZFH ZInQ.FHPrinted

/-! ## The leaf over the Kronecker symbol -/

/-- The coefficients of `L(s, f, χ_D) = ∑ aₙ(f) χ_D(n) n^{−s}` with `χ_D(n) = (D / n)` the
Kronecker symbol. -/
noncomputable def kroneckerTwistCoeff {N : ℕ} [NeZero N] (f : Newform N 2) (D : ℤ) (n : ℕ) : ℂ :=
  coeff f n * (kroneckerSym D n : ℂ)

/-- **`L(1, f, χ_D) ≠ 0`**: the entire continuation of `∑ aₙ(f) (D / n) n^{−s}` (from
`Re s > 2`) does not vanish at the centre `s = 1`. -/
def KroneckerCentralValueNeZero {N : ℕ} [NeZero N] (f : Newform N 2) (D : ℤ) : Prop :=
  ∀ G : ℂ → ℂ, IsEntireCont (kroneckerTwistCoeff f D) 2 G → G 1 ≠ 0

/-- **Bump–Friedberg–Hoffstein 1990, opening theorem, clause (ii), at weight `k = 2` and
trivial character, with `χ_D(n) = (D / n)` the Kronecker symbol.**

Printed statement (the statement-check read of D. Bump, S. Friedberg, J. Hoffstein, Invent. Math.
102 (1990), opening theorem, pp. 543–544; paraphrase): let `f` be a newform of even weight `k` and
trivial character on `Γ₀(N)`, `ε` the sign of the functional equation of `L(s, f)`, and `S` a
finite set of primes containing the primes dividing `N`. Then there is a fundamental
discriminant `D` of a quadratic field with `ε D > 0`, every `p ∈ S` split in `ℚ(√D)`, and
`L(k/2, f, χ_D) ≠ 0`, where `χ_D(n) = (D / n)` and `L(s, f, χ_D) = ∑ aₙ χ_D(n) n^{−s}` (centre
`s = k/2`). No CM exclusion, no level condition.

Here, the instance at `k = 2` (centre `s = 1`), stated over Tau Ceti's newform on `Γ₁(N)` with
trivial nebentypus: `f : Newform N 2` with `f.χ = 1`; `IsFESign f ε` (the functional equation of
the completed `L(s, f)` at level `N` with sign `ε`); `S : Finset ℕ` of primes containing every
prime dividing `N`; `Int.IsFundamentalDiscr D` (Mathlib) with `D ≠ 1`; `0 < ε * D`;
`SplitsInQuadratic D S` (two distinct primes of `𝓞 K` above each `p ∈ S`, `K` a quadratic number
field containing `√D`); `KroneckerCentralValueNeZero f D` (`kroneckerSym`, the Kronecker symbol).
The statement over the classical newform on `Γ₀(N)`, as printed, is `BFHClauseIIGamma0`
(`BFHGamma0.lean`), which implies this one (`bfhClauseIIKronecker_of_bfhClauseIIGamma0`).

Source: D. Bump, S. Friedberg, J. Hoffstein, *Nonvanishing theorems for L-functions of modular
forms and their derivatives*, Invent. Math. 102 (1990), 543–618, opening theorem (pp. 543–544),
clause (ii). -/
def BFHClauseIIKronecker : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ ε : ℤ, IsFESign f ε →
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S) →
    ∃ D : ℤ, Int.IsFundamentalDiscr D ∧ D ≠ 1 ∧ 0 < ε * D ∧ SplitsInQuadratic D S ∧
      KroneckerCentralValueNeZero f D

/-! ## The bridge to the characters of the consumers -/

/-- **`chiD D = (D / ·)`** for an odd fundamental discriminant `D` (`n ≠ 0`): gz-decomp's
`chiD D n = J(n | |D|)` is the Kronecker symbol. -/
theorem chiD_eq_kroneckerSym {D : ℤ} (hD4 : D % 4 = 1) (hD : Squarefree D) {n : ℕ} (hn : n ≠ 0) :
    chiD D n = (kroneckerSym D n : ℂ) := by
  rw [chiD, kroneckerSym_eq_jacobiSym hD4 hD hn]

/-- The Kronecker twist is fh-printed's twist (`χ_D` from local components) for every fundamental
discriminant. -/
theorem kroneckerTwistCoeff_eq_printedTwistCoeff {N : ℕ} [NeZero N] (f : Newform N 2) {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) {n : ℕ} (hn : n ≠ 0) :
    kroneckerTwistCoeff f D n = printedTwistCoeff f D n := by
  rw [kroneckerTwistCoeff, printedTwistCoeff, idelicChar_eq_kroneckerSym hD hn]

/-- The Kronecker twist is gz-decomp's twist `twistCoeff f D` for odd `D` (squarefree,
`D ≡ 1 mod 4`). -/
theorem kroneckerTwistCoeff_eq_twistCoeff {N : ℕ} [NeZero N] (f : Newform N 2) {D : ℤ}
    (hD4 : D % 4 = 1) (hD : Squarefree D) {n : ℕ} (hn : n ≠ 0) :
    kroneckerTwistCoeff f D n = twistCoeff f D n := by
  rw [kroneckerTwistCoeff, twistCoeff, chiD_eq_kroneckerSym hD4 hD hn]

/-- The central-value clauses agree for every fundamental discriminant. -/
theorem kroneckerCentralValueNeZero_iff {N : ℕ} [NeZero N] (f : Newform N 2) {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) :
    KroneckerCentralValueNeZero f D ↔ CentralValueNeZero f D := by
  constructor
  · intro h G hG
    exact h G (isEntireCont_congr
      (fun n hn => (kroneckerTwistCoeff_eq_printedTwistCoeff f hD hn).symm) hG)
  · intro h G hG
    exact h G (isEntireCont_congr (fun n hn => kroneckerTwistCoeff_eq_printedTwistCoeff f hD hn) hG)

/-- Splitting restricts to subsets. -/
theorem SplitsInQuadratic.mono {d : ℤ} {S T : Finset ℕ} (h : SplitsInQuadratic d T) (hST : S ⊆ T) :
    SplitsInQuadratic d S := by
  obtain ⟨K, hF, hN, hK, hδ, hs⟩ := h
  exact ⟨K, hF, hN, hK, hδ, fun p hp => hs p (hST hp)⟩

/-- **The restated leaf is equivalent to bfh-leaf's** (`χ_D` the Kronecker symbol vs. the
character from local components; `S ⊇` primes dividing `N` vs. `2N`). -/
theorem bfhClauseIIKronecker_iff : BFHClauseIIKronecker ↔ BFHClauseII := by
  constructor
  · intro h N _ f hχ ε hε S hSp hS
    obtain ⟨D, hfd, hD1, hsign, hsplit, hL⟩ :=
      h N f hχ ε hε S hSp (fun p hp hpN => hS p hp (dvd_mul_of_dvd_right hpN 2))
    exact ⟨D, hfd, hD1, hsign, hsplit, (kroneckerCentralValueNeZero_iff f hfd).mp hL⟩
  · intro h N _ f hχ ε hε S hSp hS
    have hSp' : ∀ p ∈ insert 2 S, p.Prime := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Nat.prime_two
      · exact hSp p hp
    have hS' : ∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ insert 2 S := by
      intro p hp hpd
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h2 | hN
      · exact Finset.mem_insert.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2))
      · exact Finset.mem_insert_of_mem (hS p hp hN)
    obtain ⟨D, hfd, hD1, hsign, hsplit, hL⟩ := h N f hχ ε hε (insert 2 S) hSp' hS'
    exact ⟨D, hfd, hD1, hsign, hsplit.mono (Finset.subset_insert 2 S),
      (kroneckerCentralValueNeZero_iff f hfd).mpr hL⟩

/-! ## The use, at `B = 4` -/

/-- **The one application of the leaf.** For `f` with root number `−1`, BFH (ii) with `S` the
primes dividing `2N` gives an odd imaginary fundamental discriminant `D < −4` with the Heegner
hypothesis for `N` and `L(1, f ⊗ χ_D) ≠ 0`: `ε = −1` gives `D < 0`, `2` split gives
`D ≡ 1 (mod 8)` (so `D ≤ −7`), odd `p ∣ N` split gives `(D / p) = 1`. This is
`GZDecomp.FHNonvanishing` at `B = 4`, the only bound its consumer
(`GZDecomp.grossZagierCd_of_leaves`) uses. -/
theorem exists_heegnerDisc_of_bfhClauseIIKronecker (h : BFHClauseIIKronecker) {N : ℕ} [NeZero N]
    (f : Newform N 2) (hχ : f.χ = 1) (hw : rootNumber f hχ = -1) :
    ∃ D : ℤ, D < -4 ∧ IsOddImagFundDisc D ∧ HeegnerHyp N D ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0 := by
  have hN0 : N ≠ 0 := NeZero.ne N
  set S : Finset ℕ := (2 * N).primeFactors with hSdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S := fun p hp hpd =>
    mem_primeFactors_two_mul hN0 hp hpd
  obtain ⟨D, hfd, hD1, hsign, ⟨K, _, _, hK, ⟨δ, hδ⟩, hsplit⟩, hL⟩ :=
    h N f hχ (-1) (isFESign_of_rootNumber f hχ (by rw [hw]; push_cast; ring)) S hSp
      (fun p hp hpN => hS2N p hp (dvd_mul_of_dvd_right hpN 2))
  have h2S : 2 ∈ S := hS2N 2 Nat.prime_two (dvd_mul_right 2 N)
  have hd8 : D % 8 = 1 := mod_eight_of_splitsIn_two hK (hsplit 2 h2S) hδ hfd
  have hdsq : Squarefree D := by
    rcases Int.isFundamentalDiscr_iff_squarefree.mp hfd with ⟨-, h⟩ | ⟨h0, -⟩
    · exact h
    · omega
  have hdneg : D < 0 := by linarith
  have hDisc : IsOddImagFundDisc D := ⟨hdneg, by omega, hdsq⟩
  have hH : HeegnerHyp N D := (ZInQ.GZStatements.heegnerHyp_iff_split hDisc).mpr
    ⟨fun _ => hd8, fun p hp _ hpN => by
      have : Fact p.Prime := ⟨hp⟩
      have hpS := hS2N p hp (dvd_mul_of_dvd_right hpN 2)
      exact zmod_isSquare_of_splitsIn hK (hsplit p hpS) hδ (not_sq_dvd_of_squarefree hdsq hp)⟩
  refine ⟨D, by omega, hDisc, hH, fun G hG => hL G ?_⟩
  exact isEntireCont_congr
    (fun n hn => (kroneckerTwistCoeff_eq_twistCoeff f (by omega) hdsq hn).symm) hG

/-- **`GrossZagierCd` from the theta-newform leaf, BFH (ii) over the Kronecker symbol and
Gross–Zagier–Heegner.** `GZDecomp.grossZagierCd_of_leaves` with `signOfSimpleZero` (proved),
copied with the application `hL2 N f hχ hw 4` of `FHNonvanishing` replaced by
`exists_heegnerDisc_of_bfhClauseIIKronecker`. -/
theorem grossZagierCd_of_bfhClauseIIKronecker (hL1 : HeckeThetaNewform) (hBFH : BFHClauseIIKronecker)
    (hL3 : GrossZagierHeegner) : GrossZagierCd := by
  intro d hd hsq F hF h1
  have hd0 : d ≠ 0 := by omega
  have hEll : (shortCurve (-(d : ℚ) ^ 2)).IsElliptic := by
    have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    exact shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 hd0'))
  obtain ⟨N, hN, f, hχ, hf⟩ := modular_cd hL1 (by omega) hsq
  have hFf : IsEntireCont (coeff f) 2 F := isEntireCont_of_isLContinuation hf hF
  have hw : rootNumber f hχ = -1 := signOfSimpleZero N f hχ F hFf h1
  obtain ⟨D, hD4, hDisc, hHeeg, hGne⟩ := exists_heegnerDisc_of_bfhClauseIIKronecker hBFH f hχ hw
  obtain ⟨G, hG⟩ := exists_isEntireCont_twist f (ne_of_lt hDisc.1)
  have hG1 := hGne G hG
  have hD0 : (D : ℚ) < 0 := by exact_mod_cast hDisc.1
  obtain ⟨K, hKf, hKa, hK2, δ, hδ⟩ := exists_quadratic_field hD0
  classical
  obtain ⟨y, hy, hyσ⟩ := hL3 _ N f hχ hf D hDisc hD4 hHeeg F G hFf hG h1 hG1
    K hK2 ⟨δ, by simpa using hδ⟩
  exact exists_rat_point_of_heegner hK2 y hy hyσ

/-- **Theorem 1.1 from `SixContactMin`, TYZ Theorem 3.5(2) in reading A, the theta-newform leaf,
BFH (ii) over the Kronecker symbol, and Gross–Zagier–Heegner**:
`GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` with `hL2 : FHNonvanishing`
replaced by `hBFH : BFHClauseIIKronecker`. -/
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker (hH : SixContactMin)
    (hA : ZInQ.Literature.TYZThm35ReadingA) (hL1 : HeckeThetaNewform)
    (hBFH : BFHClauseIIKronecker) (hL3 : GrossZagierHeegner) : FrozenTarget :=
  frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd hH hA
    (grossZagierCd_of_bfhClauseIIKronecker hL1 hBFH hL3)

/-- **`FHNonvanishing` (every bound `B`) from the restated leaf** (through
`bfhClauseIIKronecker_iff` and bfh-leaf's glue): the drop-in replacement of
`GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH`. -/
theorem fhNonvanishing_of_bfhClauseIIKronecker (h : BFHClauseIIKronecker) : FHNonvanishing :=
  fhNonvanishing_of_bfhClauseII (bfhClauseIIKronecker_iff.mp h)

end ZInQ.BFHPrinted
