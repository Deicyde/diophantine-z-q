# h29-fix (2026-11-15)

**Result.** The h29 fold is now net negative: strict GLUE −1, strictest −1 (h29-split's was 0). `h29 = TYZLemma29Mod2`
is proved from five published leaves, none flagged "pending reading" (VERIFIED: compiled; `#discharges`; axioms
`[propext, Classical.choice, Quot.sound]`; Theorem 1.1 with h29 replaced compiles, `h29fix_frozenTarget`):
`LegendreThreeSquares`, `JonesPallX2Y2Z16`, `TYZTestVectorExists`, `TYZLemma29Printed`, `TYZProp23Printed`.

**TYZ misprint settled (VERIFIED).** On TYZ's 8-point double coset space O_B^x\(O_B/4)^x, built exactly, Q(3) = ±3 for
all 8 admissible τ, and 𝓛(3)² = 1 (PARI). So the printed Lemma 2.9 (±𝓛(3) = Q(3)) is false, and Theorem 2.1
(Q(3) = ±w_K𝓛(3), w_K = 3) is right. The leaf now carries `wK n` (3 at n = 3, 1 otherwise), which is what
TYZ's proof gives. Cross-check on 19 values of n in both classes (class groups up to order 12): the w_K form of
Lemma 2.9 and Prop 2.3's oddness on 2Cl_n hold in all 38 runs.

**The other fixes.**
- `TYZTestVectorExists` gains a nonzero clause and `1 < n`. π^U is now defined by TYZ's printed description
  π^U = 𝒜₀^U: orthogonality to 1 and χ₀∘nrd on the 8 representatives 1+2x of Lemma 2.5. The leaf has no
  unprinted ingredient left. The Hecke bridge T_p = a_p(E) on 𝒜₀^U is checked for odd p < 40 and is not used.
- `TYZProp23Printed`'s docstring states why it is not vacuous.
- Mathlib has no three-square theorem, so `LegendreJonesPall` is split into Legendre and Jones–Pall
  (x²+y²+16z² represents n ≡ 1 mod 8; checked exhaustively to 10⁶) and the composite is proved from them.
- New lemmas `tv_eq_of_toClassGroup_eq` (f∘τ̂ is constant on ideal classes), `genusPeriodTV_eq_of_section` and
  `exists_isPlaceTwo`.
- A fresh model read found no errors and rated all five leaves LEAF.

**Deliverables.**
- `scratch/h29-fix/TYZLemma29Mod2.lean`: drop-in replacement for the ZInQKernel contribution; compiles.
- `DischargesH29Fix*`: the discharge check and its output.
- `autofold.json` and `kinds-rows.tsv`: autofold spec and proposed kinds rows. h29 is a plain argument of
  `frozenTarget`, so this is a by-hand fold (steps in report §4).
- `brandt.py`, `brandt2.py`, `lcal_small.py`, `regular_form.py`: the computations.
- `docs/research/h29-fix.md`: the report.

**Remains.**
- The n = 3 instance is not proved in Lean: it needs lcalSq 3 = 1, an analytic L-value, and Lemma 2.5's adelic
  bijection.
- Jones–Pall's Theorem 5 was not read; locator UNVERIFIED.
- No human review.
