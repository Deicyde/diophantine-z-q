# tyz-lcal: the three L-leaves of the TYZ decomposition

**Main result.** `TYZLcalOne` (𝓛(1) = 1, i.e. L(C₁,1) = ¼∫₁^∞dx/√(x³−x)) is **no longer a leaf**. It is proved from
the other two L-leaves:
`tyzLcalOne_of_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) : TYZLcalOne`.
So TYZThm35ReadingA now rests on three TYZ leaves (`tyzThm35ReadingA_of_three_leaves`):
`TYZThm11Integral`, `TYZLemma29Mod2` and `TYZGenusPackage`. Given the first two,
`TYZGenusPackage ↔ TYZThm35ReadingA` (`genusPackage_iff_readingA_of_two`).

**How the proof goes.**
- Integrality at m = 1 gives lcalSq 1 = a², with a ∈ ℤ.
- Lemma 2.9 mod 2 at m = 3 gives 𝓛(3)𝓛(1) ≡ g(3) = 1. The value g(3) = 1 is proved in Lean: ℚ(√−3) = ℚ(ζ₃), and
  Mathlib's `three_pid` makes its ring of integers a PID. So a is odd, and either a² = 1 or a² ≥ 9.
- An explicit analytic bound excludes a² ≥ 9: ‖L(C₁,1)‖ ≤ 3.35 (true value 0.6555) and ∫ ≥ 2. The bound is proved
  in Lean from the fork's Hecke theta continuation (Contrib/HeckeFE). Λ(1) is split at 1 into integrals over (1,∞),
  and Mathlib's Hurwitz kernels are bounded there by explicit geometric majorants.

**What compiles.** `scratch/tyz-lcal/TYZLcal.lean` (~930 lines) passes `lake env lean` with no errors, no warnings,
no sorry and no axiom. `#print axioms` gives only [propext, Classical.choice, Quot.sound]. Also proved:
`lemma29Mod2_iff`, which shows the ∀-sign-choice in `TYZLemma29Mod2` is immaterial, and `tyzLcalOne_of_leaves'`,
the same result with the Theorem 1.1 congruence in place of Lemma 2.9. The file can be copied verbatim into a
new module, e.g. `ZInQKernel/Contrib/TYZLcal/Basic.lean`.

**Audit of the remaining two leaves.** Both are faithful TYZ consequences and not stronger:
- `TYZThm11Integral` is TYZ Theorem 1.1 (integrality, odd n ≡ 1, 3, n = 1 included).
- `TYZLemma29Mod2` is Lemma 2.9 with Proposition 2.3, read mod 2. The w_K = 3 misprint at m = 3 is harmless mod 2.

Both are genuinely TYZ-specific: Waldspurger-formula content, not derivable from the definitions or from PSide's
a_p results. A pure-Python check on 30 inputs (no PARI on this host) found:
- lcalSq is an integer square in every case;
- LemmaTwoEight holds mod 2 in all 29 applicable cases;
- |𝓛| = |a_T|/2^k with Tunnell's coefficients a_T, which pins TYZ's normalisation.

**What remains.** Human checks against the TYZ source, which was not on this host:
- L338–353: the normalisation 2^{2k−2−a}, Ω_{n,∞};
- L371–380: n = 1 in Theorem 1.1;
- the m = 3 case of Lemma 2.9;
- whether the proof of Lemma 2.9 uses L1082.

The Tunnell alternative (integrality ⇔ 2^k | a_T(m)) is only remarked, not pursued.
Report: docs/research/tyz-lcal.md. Log: scratch/tyz-lcal/log.md.
