# rv-h-cm: report

**Verdict: correct after minor repairs.** Theorem NoCM of `docs/research/h-cm.md` holds. For every
`u ∈ ℚ \ 𝒞`, no point of `X⁶` over `t(u)` is a CM point. So the "CM fibers" paragraph (lines 581-631)
of the proof of Theorem 4.1 can be replaced by a short lemma. A003 (Fowler) and A004 (CM height
formula) then leave the trust base, along with the A005 application and the CM use of A065.
`H₆(S;R)` is unchanged, and `SixContactEstimate`/`SixContactMin` need no change. The full review is
`docs/research/rv-h-cm.md`; the computations are in `scratch/rv-h-cm/check.py` and `check.output.txt`.

## What was checked independently
- **Coordinate identities.** These were recomputed from lines 380-382 and 510-514: `t = 1 + 27j/16`,
  `t(u) = H²/G⁶`, `t(u) - 1 = -3(180F/G³)²`. `FGH(u) ≠ 0` was checked for rational `u`.
- **The j-labelling.** The manuscript gives `j = 0, ∞, -16/27` at `D = -4, -3, -24` (lines 421-422 and
  908-909). Lin–Yang's TeX states this explicitly, quoting Baba–Granath. Lin–Yang's independent value
  `j₆(P₋₁₉) = 81/64` matches Elkies' `t(-19) = 3211/1024`. The labelling is essential: swapping `0`
  and `∞` makes the fibre field `ℚ(√3, i)`, and the argument fails. It is already a premise of the
  manuscript (A001, A017), so NoCM adds no new dependence.
- **Elkies' model.** It was read in Elkies' TeX (arXiv math/0005160), whose algebra and order are the
  manuscript's. The shape `ℚ(t)(√(c₀t), √(c₁(t-1)))` is forced by `W` acting over `ℚ`. The constants
  `c₀ = -1`, `c₁ = 3` were rederived here from Shimura reciprocity at the three elliptic points
  alone, without Elkies' table. Complex conjugation acts as `w₃` on the four `ℚ(i)`-points over
  `t(u)`.
- **CM inputs.** These were read in González–Rotger (arXiv math/0612732), §5. Prop. 5.6 gives the
  count `2^b h` and the simply transitive action of `W' × Pic`, Thm. 5.8 the reciprocity law
  `K·ℚ(x) = K(f)`, and Lemma 5.9 the rule `σ_𝔭 = w_p`. Thm. 5.12 gives the field of moduli.
- **Case split.** It is exhaustive: 3 split, 2 split and `(f, 6) > 1` are excluded by the local
  embedding condition. Each of Cases A, B and C was checked.
- **Elkies' tables.** The h-cm scripts rerun byte-identically. Elkies' covers for `l = 5, 7, 13`
  recover 16 table values, including `-52`, which h-cm missed. The `|D| = 40` misprint (`B = 125`)
  is confirmed by Table 2 and by Elkies' text. No row has a rational preimage under `J`. All 24 rows
  match the sharp field prediction of González–Rotger Thm. 5.12 and the ramified Frobenius rule.

## Gaps (all minor; none affects validity)
1. **Source misstatements the audit must not copy.**
   - González–Rotger Prop. 5.6's printed non-emptiness criterion accepts `p | (f, D)` (for example
     `ℤ[3i]`). Saia's count also omits the hypothesis `(f, D) = 1`.
   - Saia's restatement of the Jordan/González–Rotger field-of-moduli theorem has its two cases
     swapped.
   - The note relies on neither, but the audit records for these inputs should state `(f, 6) = 1`
     and cite González–Rotger, not Saia.
2. **Wrong theorem number for the reciprocity law.** González–Rotger attribute it to Shimura 1967
   Main Theorem II; the note says Main Theorem I. Shimura's paper was not available to check.
3. **Wrong section for Elkies' constants.** In the arXiv text they are determined in §3.2, not §3.3.
4. **Missing nonvanishing hypothesis.** The replacement lemma must state `H(u) ≠ 0`. The
   discriminants `10800, 43200, 43200` are not squares, but this fact is not at line 541 as the note
   says. Also, the "keep lines 564-580" range should be "564-577".
5. **Script slip.** h-cm's `isogeny_check.py` misses `|D| = 52`, so its count is 16 values, not 15.

## Suggestions
- **Shorter proof.** Adopt the two-case proof from González–Rotger Thm. 5.12 (`docs/research/rv-h-cm.md`
  §7.2):
  - If `D(R) ≠ 1`, then `ℚ(x) = H_R` forces `R = ℤ[i]`, i.e. `t = 1`, which is excluded.
  - If `D(R) = 1`, then `h(R) = 2`, so `#CM(R) = 2 < 4`.
- **Smaller trust base.** Replace the input (E), Elkies' twist constants, with the reciprocity
  derivation at the elliptic points. Elkies' paper then becomes a cross-check only.
- **Constants.** Keep `B_cm`, `C_cm` in the definition of `H₆` so the Lean numerals stay aligned. The
  value is `2·10¹³·Q_R¹⁷` either way.
- **Not consulted.** Jordan's thesis and Shimura 1967 were not consulted directly.
