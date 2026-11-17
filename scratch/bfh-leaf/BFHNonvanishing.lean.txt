import ZInQKernel.Contrib.OneProof.FriedbergHoffsteinBFE
import ZInQKernel.Contrib.OneProof.BFHPrinted.Split
import ZInQKernel.Contrib.OneProof.BFHPrinted.Witness

/-!
# `ZInQ.GZDecomp.FHNonvanishing` from Bump–Friedberg–Hoffstein 1990, clause (ii)

Task bfh-leaf (report `docs/research/bfh-leaf.md`). The top hypothesis
`hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE` of `ZInQ.OneProof.frozenTarget` is used only through
`ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH : ZInQ.GZDecomp.FHNonvanishing`. This file
states clause (ii) of the opening theorem of Bump–Friedberg–Hoffstein, *Nonvanishing theorems for
L-functions of modular forms and their derivatives*, Invent. Math. 102 (1990) 543–618, at weight 2
and trivial character over genuine objects (`BFHClauseII`), and proves `FHNonvanishing` from it
alone, with all glue proved (`fhNonvanishing_of_bfhClauseII`). No twisted root number is needed.

Objects of the leaf:
* `Newform N 2`, `f.χ` (Tau Ceti); `GZDecomp.coeff`, `GZDecomp.IsEntireCont` (gz-decomp);
* the sign `ε` of the functional equation of `L(s, f)`: `IsFESign f ε`, the functional equation
  `Λ_N(2 − s) = ε Λ_N(s)` of the completed L-function `Λ_N(s) = N^{s/2} (2π)^{−s} Γ(s) L(s, f)`
  (`ZInQ.Literature.completedL`, the kernel's), on the strip `0 < Re s < 2`;
* fundamental discriminants: Mathlib's `Int.IsFundamentalDiscr`, with `d ≠ 1` (the discriminant of
  a quadratic field);
* "`p` splits in `ℚ(√d)`": `SplitsInQuadratic d S`, a quadratic number field `K` (Mathlib's
  `NumberField`, `Module.finrank ℚ K = 2`) containing a square root of `d`, in whose ring of
  integers `𝓞 K` every `p ∈ S` has two distinct prime ideals above it (`BFHPrinted.SplitsIn`, over
  Mathlib's `Ideal.primesOver`);
* `L(k, f, χ_d) ≠ 0`: fh-printed's `FHPrinted.CentralValueNeZero f d`, the entire continuation of
  `∑ aₙ(f) χ_d(n) n^{−s}` (`χ_d` from its local components, `FHPrinted.idelicChar`) does not
  vanish at the centre `s = 1 = k`.
-/

open HeckeRing.GL2 NumberField

namespace ZInQ.BFHPrinted

open ZInQ.GZDecomp ZInQ.GZFH ZInQ.FHPrinted

/-! ## The printed leaf -/

/-- **`ε` is the sign of the functional equation of `L(s, f)`**: the entire continuation `G` of
`L(s, f) = ∑ aₙ(f) n^{−s}` satisfies `Λ_N(2 − s) = ε Λ_N(s)` on `0 < Re s < 2`, where
`Λ_N(s) = N^{s/2} (2π)^{−s} Γ(s) G(s)` (`ZInQ.Literature.completedL`) is the completed L-function
of `f` at its level `N`. (`G` is unique, `IsEntireCont.eq`, and not identically zero since
`a₁ = 1`, so `ε` is determined by `f`; it is `GZDecomp.rootNumber f hχ`, see
`isFESign_iff`.) -/
def IsFESign {N : ℕ} [NeZero N] (f : Newform N 2) (ε : ℤ) : Prop :=
  ∃ G : ℂ → ℂ, IsEntireCont (coeff f) 2 G ∧ ∀ s : ℂ, 0 < s.re → s.re < 2 →
    ZInQ.Literature.completedL N G (2 - s) = (ε : ℂ) * ZInQ.Literature.completedL N G s

/-- **Every prime of `S` splits in `ℚ(√d)`**: there is a quadratic number field `K` containing a
square root of `d` (so `K ≅ ℚ(√d)` when `d` is not a square) such that every `p ∈ S` has two
distinct prime ideals of `𝓞 K` above it. -/
def SplitsInQuadratic (d : ℤ) (S : Finset ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K), Module.finrank ℚ K = 2 ∧
    (∃ δ : K, δ ^ 2 = (d : K)) ∧ ∀ p ∈ S, SplitsIn K p

/-- **Bump–Friedberg–Hoffstein 1990, opening theorem, clause (ii), at weight 2 and trivial
character.**

Printed statement (as read from page images of pp. 543–544 by the theorem-application audit,
docs/theorem-application-audit/evidence/theta-upstream.md §1 and §7, INVENTORY.md A025; no copy
on this host): let `f` be a cuspidal newform of even weight `2k` and trivial character on
`Γ₀(N)`, `ε` the sign of the functional equation of `L(s, f)`, and `S` a finite set of primes
containing the primes dividing `N`. Then there is a fundamental discriminant `d` of a quadratic
field with `ε d > 0`, every `p ∈ S` split in `ℚ(√d)`, and `L(k, f, χ_d) ≠ 0`, where
`L(s, f, χ_d) = ∑ aₙ χ_d(n) n^{−s}` with centre `s = k`.

This is its direct instance at `k = 1`, for `S` containing the primes dividing `2N`:
* `f : Newform N 2` with `f.χ = 1` (Tau Ceti's newform on `Γ₁(N)` with trivial nebentypus is a
  newform on `Γ₀(N)`);
* `IsFESign f ε`: `ε` is the sign of the functional equation of the completed `L(s, f)` at level
  `N`;
* `S : Finset ℕ` a finite set of primes containing every prime dividing `2N`;
* `d` a fundamental discriminant (`Int.IsFundamentalDiscr`, Mathlib) of a quadratic field
  (`d ≠ 1`), `0 < ε d`, every `p ∈ S` splits in `ℚ(√d)` (`SplitsInQuadratic`), and
  `L(1, f, χ_d) ≠ 0` (`CentralValueNeZero f d`, fh-printed: the entire continuation of
  `∑ aₙ(f) χ_d(n) n^{−s}`, `χ_d` the quadratic character of `ℚ(√d)` built from its local
  components, does not vanish at `s = 1`).

Source: D. Bump, S. Friedberg, J. Hoffstein, *Nonvanishing theorems for L-functions of modular
forms and their derivatives*, Invent. Math. 102 (1990), 543–618, opening theorem (pp. 543–544),
clause (ii). Unread by this task (no copy on this host, no network); the audit's reading leaves
three checks: (1) no CM exclusion (the use applies it to the CM newform of `C_d`); (2) no
condition on the level (the use has `N = 32 d²`, even and not squarefree); (3) the wording of
clause (ii) (fundamental discriminant or squarefree `d`; "split" or a congruence class modulo
`4N`). -/
def BFHClauseII : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ ε : ℤ, IsFESign f ε →
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S) →
    ∃ d : ℤ, Int.IsFundamentalDiscr d ∧ d ≠ 1 ∧ 0 < ε * d ∧ SplitsInQuadratic d S ∧
      CentralValueNeZero f d

/-- **The splitting clause is satisfiable**: `d = −3` is a fundamental discriminant of a quadratic
field and `7` splits in `ℚ(√−3)` (`cyclotomicThree_witness`). -/
theorem splitsInQuadratic_witness :
    Int.IsFundamentalDiscr (-3) ∧ (-3 : ℤ) ≠ 1 ∧ SplitsInQuadratic (-3) {7} := by
  refine ⟨?_, by norm_num, ?_⟩
  · have h := (Int.isFundamentalDiscr_four_mul_add_one (m := -1)).mpr (by
      rw [show (4 : ℤ) * -1 + 1 = -3 by norm_num]
      exact Int.squarefree_natAbs.mp (by simpa using Nat.prime_three.squarefree))
    simpa using h
  · obtain ⟨K, hF, hN, hK, hδ, hs⟩ := cyclotomicThree_witness
    exact ⟨K, hF, hN, hK, hδ, fun p hp => by rw [Finset.mem_singleton.mp hp]; exact hs⟩

/-! ## Glue -/

/-- `L(s, f)` has an entire continuation (the twist by the trivial character `χ_1`). -/
theorem exists_isEntireCont_coeff {N : ℕ} [NeZero N] (f : Newform N 2) :
    ∃ G : ℂ → ℂ, IsEntireCont (coeff f) 2 G := by
  obtain ⟨G, hG⟩ := exists_isEntireCont_twist f (one_ne_zero : (1 : ℤ) ≠ 0)
  refine ⟨G, isEntireCont_congr (fun n _ => ?_) hG⟩
  simp [twistCoeff, chiD]

/-- The sign of the functional equation of `L(s, f)` at level `N` is `rootNumber f hχ` (Tau
Ceti's `Newform.frickeCompletedL_sub_eq`, through `GZFH.completedL_newform_sub`). -/
theorem isFESign_of_rootNumber {N : ℕ} [NeZero N] (f : Newform N 2) (hχ : f.χ = 1) {ε : ℤ}
    (hε : rootNumber f hχ = ε) : IsFESign f ε := by
  obtain ⟨G, hG⟩ := exists_isEntireCont_coeff f
  exact ⟨G, hG, fun s h1 h2 => by rw [completedL_newform_sub f hχ hG h1 h2, hε]⟩

/-- **`IsFESign` pins `ε`**: the sign of the functional equation of `L(s, f)` at level `N` is
exactly `rootNumber f hχ` (so the leaf's `ε` is a function of `f`, and `IsFESign f ε` holds for
exactly one `ε`). -/
theorem isFESign_iff {N : ℕ} [NeZero N] (f : Newform N 2) (hχ : f.χ = 1) (ε : ℤ) :
    IsFESign f ε ↔ (ε : ℂ) = rootNumber f hχ := by
  constructor
  · rintro ⟨G, hG, hFE⟩
    have hG1 : IsEntireCont (twistCoeff f 1) 2 G :=
      isEntireCont_congr (fun n _ => by simp [twistCoeff, chiD]) hG
    obtain ⟨s, hs1, hs2, hGs⟩ :=
      exists_ne_zero_on_strip hG.1 (twist_cont_ne_zero f one_ne_zero hG1)
    have e1 := hFE s hs1 hs2
    have e2 := completedL_newform_sub f hχ hG hs1 hs2
    have h2π : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hΛ : ZInQ.Literature.completedL N G s ≠ 0 := by
      rw [completedL_eq]
      refine mul_ne_zero ?_ (mul_ne_zero (mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hs1)) hGs)
      · rw [Ne, Complex.cpow_eq_zero_iff]
        exact fun h => (NeZero.ne N) (by exact_mod_cast h.1)
      · rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => h2π h.1
    exact mul_right_cancel₀ hΛ (e1.symm.trans e2)
  · intro h; exact isFESign_of_rootNumber f hχ h.symm

/-- A prime `p` with `p² ∣ d` is excluded for `d` squarefree. -/
theorem not_sq_dvd_of_squarefree {d : ℤ} (hd : Squarefree d) {p : ℕ} (hp : p.Prime) :
    ¬ (p : ℤ) ^ 2 ∣ d := by
  intro h
  have hu := hd (p : ℤ) (by simpa [sq] using h)
  have h1 := Int.isUnit_iff_natAbs_eq.mp hu
  simp only [Int.natAbs_natCast] at h1
  exact hp.one_lt.ne' h1

/-- **`FHNonvanishing` from Bump–Friedberg–Hoffstein clause (ii).** Take `S` the primes dividing
`2N` together with the primes up to `B`; `ε = rootNumber f = −1` gives `d < 0`; `2` split gives
`d ≡ 1 (mod 8)`; `p ∣ N` split gives the Heegner hypothesis; every prime `≤ B` splits, so does not
divide `d`, whence `|d| > B`; the central value transfers by `printedTwistCoeff_eq`. -/
theorem fhNonvanishing_of_bfhClauseII (h : BFHClauseII) : FHNonvanishing := by
  intro N _ f hχ hw B
  have hN0 : N ≠ 0 := NeZero.ne N
  set S : Finset ℕ := (2 * N).primeFactors ∪ (Finset.range (B + 1)).filter Nat.Prime with hSdef
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h1
    · exact Nat.prime_of_mem_primeFactors h1
    · exact (Finset.mem_filter.mp h1).2
  have hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S := fun p hp hpd =>
    Finset.mem_union_left _ (mem_primeFactors_two_mul hN0 hp hpd)
  have hSB : ∀ p : ℕ, p.Prime → p ≤ B → p ∈ S := fun p hp hpB =>
    Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
  obtain ⟨d, hfd, hd1, hsign, ⟨K, _, _, hK, ⟨δ, hδ⟩, hsplit⟩, hL⟩ :=
    h N f hχ (-1) (isFESign_of_rootNumber f hχ (by rw [hw]; push_cast; ring)) S hSp hS2N
  have h2S : 2 ∈ S := hS2N 2 Nat.prime_two (dvd_mul_right 2 N)
  have hd8 : d % 8 = 1 := mod_eight_of_splitsIn_two hK (hsplit 2 h2S) hδ hfd
  have hdsq : Squarefree d := by
    rcases Int.isFundamentalDiscr_iff_squarefree.mp hfd with ⟨-, h⟩ | ⟨h0, -⟩
    · exact h
    · omega
  have hdneg : d < 0 := by linarith
  have hodd : ∀ p ∈ S, p ≠ 2 → (d : ZMod p) ≠ 0 ∧ IsSquare (d : ZMod p) := by
    intro p hpS _
    have : Fact p.Prime := ⟨hSp p hpS⟩
    exact zmod_isSquare_of_splitsIn hK (hsplit p hpS) hδ
      (not_sq_dvd_of_squarefree hdsq (hSp p hpS))
  have hDisc : IsOddImagFundDisc d := ⟨hdneg, by omega, hdsq⟩
  have hH : HeegnerHyp N d := (ZInQ.GZStatements.heegnerHyp_iff_split hDisc).mpr
    ⟨fun _ => hd8, fun p hp hp2 hpN => hodd p (hS2N p hp (dvd_mul_of_dvd_right hpN 2)) hp2⟩
  -- every prime factor of `d` exceeds `B`
  have hB : d < -(B : ℤ) := by
    have hna : 2 ≤ d.natAbs := by omega
    set q := d.natAbs.minFac with hq
    have hqp : q.Prime := Nat.minFac_prime (by omega)
    have hqd : (q : ℤ) ∣ d := Int.natCast_dvd.mpr (Nat.minFac_dvd _)
    have hqB : B < q := by
      by_contra hle
      have hqS := hSB q hqp (by omega)
      by_cases hq2 : q = 2
      · rw [hq2] at hqd; omega
      · exact (hodd q hqS hq2).1 ((ZMod.intCast_zmod_eq_zero_iff_dvd d q).mpr hqd)
    have hqle : q ≤ d.natAbs := Nat.minFac_le (by omega)
    omega
  refine ⟨d, hB, hDisc, hH, fun G hG => hL G ?_⟩
  exact isEntireCont_congr
    (fun n hn => (printedTwistCoeff_eq f ⟨hd1, by omega, hdsq⟩ hn).symm) hG

end ZInQ.BFHPrinted
