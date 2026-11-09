# h-cm report: the CM branch of the six-contact estimate H

Deliverable: `docs/research/h-cm.md`. Scripts and saved outputs: `scratch/h-cm/`
(`cm_table.py`, `isogeny_check.py`, `md_table.py`, `*.output.txt`).

## Result

**The CM branch of the proof of H is empty for rational u.** This is proved, not conjectured.
For every u ∈ ℚ \ 𝒞, the fibre surface A in the proof of Theorem 4.1 has
End⁰(A_ℚ̄) = B (Theorem NoCM, §4.1.4 of the note). The proof uses no class-number
classification and no list of CM points.

Proof in four lines:

1. In Elkies' coordinate t on X*(6) = X⁶/W (t = 0, 1, ∞ at Δ = -24, -4, -3), the manuscript's
   j satisfies t = 1 + 27j/16. Then t(u) = H²/G⁶ and t(u) - 1 = -3(180F/G³)²
   (VERIFIED symbolically).
2. Elkies' model of X⁶ → X* has function field ℚ(t)(√(-t), √(3(t-1))). So the four points over
   t(u) are (±iH/G³, ±540iF/G³). They are defined over ℚ(i), and complex conjugation acts on
   them as w₃.
3. If such a point x had CM by an order 𝔬 of conductor f in K, then (f, 6) = 1, 2 and 3 do not
   split in K, and Shimura's reciprocity law gives K(f) = K·ℚ(x) = K(i), so h(𝔬) ≤ 2.
4. Case split:
   - 2 inert in K: K(f) is unramified at 2 but contains ℚ(i). Contradiction.
   - 2 and 3 ramified: |CM(𝔬)| = h(𝔬) ≤ 2, but the free W-orbit of x already has 4 points.
     Contradiction.
   - 2 ramified, 3 inert: Galois over K acts on x through {1, w₃} = W' and through Pic(𝔬).
     Simple transitivity of W' × Pic(𝔬) (Jordan; González–Rotger, Prop. 5.6) forces
     Pic(𝔬) = 1, so |CM(𝔬)| = 2 < 4. Contradiction.

## Task items

1. **Elkies' list converted** to the manuscript coordinate j = 16(t-1)/27. The table of all 27
   points is in §4.2. One misprint was found and fixed: |D| = 40 has B = 125, not 25; Table 2
   and A - B = 3⁷ confirm this.
   - The degree-12 polynomial B·H(X)² - A·G(X)⁶ was factored over ℚ for each of the 24
     non-elliptic values. The patterns are 2⁶, 4³ or 12, and no row has a linear factor.
     **There are no rational roots, hence no heights to report.**
   - A rational root needs t ∈ ℚ^{×2} and t - 1 ∈ -3ℚ^{×2}. No row passes. The nearest misses
     are |D| = 132 and 708, where t is a square but t - 1 ∈ -ℚ^{×2}.
2. **Completeness of the list** is not needed for the result.
   - For the record: a CM point of X* is rational iff 2^b·h(𝔬) = 4. Completeness would need
     class number 1 (Heegner–Baker–Stark), class number 2 (Baker–Stark) and class number 4
     with 6 | Δ (Arno 1992 or Watkins 2004, both using Goldfeld–Gross–Zagier). For the h = 4
     part, no Baker-type input suffices.
   - Also, 10 of the 27 values are only numerical in Elkies' paper.
3. **Rewritten proof** (§4.1.5): replace the "CM fibers" paragraph (lines 578-631) by the
   NoCM lemma.
   - The constant is unchanged numerically, because C_cm < Q_R^17 for every admissible R
     (log C_cm < 30000D² ≪ 170G₀²D³ log D). So Lean (`SixContactEstimate`, the `eB`/`eC`
     numerals in `CappedTest.lean`) and the size chapter need no change.
   - **Removed from the proof of H:**
     - A003 (Fowler at k = D) and A004 (CM Faltings height formula): `fowler` and `cmheight`
       are used nowhere else, so they leave the trust base entirely.
     - A005: only the CM application of Gaudron–Rémond goes; the theorem stays via A015.
     - A065: the use at lines 580-595 goes; A065 stays for lines 1009-1012 and 1759-1765.
   - **Added (all STANDARD):**
     - Shimura 1967, Main Theorem I.
     - Jordan's thesis 1981, §3, and González–Rotger, J. Math. Soc. Japan 2006, Prop. 5.6:
       the count 2^b·h(𝔬) and simple transitivity.
     - Elkies 1998, §3.1 and §3.3: the twist constants c₀ = -1, c₁ = 3.
     - Vignéras for local optimal embeddings; Cox §9 for ramification of ring class fields.

## Checks on the imported inputs (VERIFIED by script)

- **Elkies' twist constants rederived.** Shimura reciprocity at the class-number-one
  discriminants -19, -43, -67 and -163 forces (c₀, c₁) = (-1, 3).
- **CM values recomputed algebraically.** Elkies' covers X₀*(l) → X*(6) for l = 5, 7, 13 and
  their involutions w_l were rechecked: cycle structure and w_l² = 1. They reproduce 15 table
  values, including t(-19) and t(-43).
- **Fibre fields and reciprocity conventions.** For all 24 non-elliptic entries:
  - the fibre field ℚ(√(-t), √(3(t-1))) lies in the genus field;
  - complex conjugation acts nontrivially;
  - the Frobenius at the prime above each p ∈ {2,3} ramified in K acts as w_p, which is
    Jordan's rule;
  - 2^b·h = 4.

## Ranking

| Route | Status / chance |
| --- | --- |
| C1 (fibre over ℚ(i) + Shimura + Jordan–González–Rotger) | done; high chance it survives audit |
| C4 (same step via Jordan's rule σ_𝔭 = w_p) | done, as a backup proof |
| C2 (Elkies' list) | done as a check; strictly heavier than C1 |
| C3 (ℚ(i)-models of all fibres via Jordan's descent theorem) | speculative; low-medium; smaller constants, but no deep leaf removed |
| C5 (redesign) | not needed |

**Recommendation:** adopt NoCM in the manuscript. Next step: audit records for Shimura 1967 MT I,
González–Rotger Prop. 5.6 (with Jordan §3) and Elkies §3.3. Success means three accepted records
with no convention issue. Chance: high.

## Open questions and follow-up tasks

1. **Audit task.** Write theorem-application-audit records for the three new inputs. The
   points to check:
   - the Pic(𝔬)-action convention, so that Galois acts through Pic as stated;
   - that González–Rotger's "𝔬-CM point" agrees with ours at level N = 1, which it should,
     since both use the maximal order;
   - Elkies' determination of c₀ and c₁, or simply accept the rederivation from the
     class-number-one values.
2. **Manuscript edit task**, for whoever owns the manuscript: replace lines 578-631 per
   §4.1.5, optionally delete B_cm and C_cm from H₆ and line 401, and drop the `fowler` and
   `cmheight` bibliography entries.
3. **Research task (C3).** Use Jordan's descent theorem: since ℚ(x) = ℚ(i) splits B, every
   fibre (A, ι) has a model over ℚ(i). Test whether this lets the non-CM branch avoid the
   degree-D Hom field and the Brauer descent. The first test needs a CAS with genus-2
   conductor routines: compare bad primes of Mestre curves over ℚ(i) with supp M_{{2,3}}(u)
   for about 10 small u.
4. The same Q(i) observation may simplify the Bost/Javanpeykar bookkeeping only cosmetically.
   It does not touch Pan (A011), which remains the core leaf of H (see rs-height).
