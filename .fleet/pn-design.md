# pn-design (fleet report)

**Encoding.** `ZInQ.PropN.TYZInputs` (`scratch/pn-design/PropN.lean`) states that there is
`L : ℕ → ℤ` (TYZ's 𝓛, one sign choice) with:
- `L 1 = 1` (L1082);
- `LemmaTwoEight L`: Lemma 2.8 with Proposition 2.3 modulo 2. For `m ≡ 1` the pairs are
  unordered, taken as `d ≡ 1`, `d² < m`; for `m ≡ 3` the sum runs over `d ≡ 1`;
- I7: `L n ≠ 0 → ∃ F, IsLContinuation (shortCurve (−n²)) F ∧ analyticOrderAt F 1 ≤ 1`;
- for each squarefree `n ≡ 5 (mod 8)`, `Nonempty (GenusData L n)`.

`GenusData L n` contains:
- an abstract ℤ[i]-module `M` (the role of A(ℍ'_n)), with points `Z, P : ℕ → M`;
- `ε` with Theorem 3.3's classes (`±i` on (5,3), `±1` otherwise);
- the recursion I1;
- I3: `L n = 0 →` `P n` is torsion;
- `τ : ℤ[i] →+ M` for `y ↦ τ(y/2)`, with kernel `(2+2i)` and range containing all torsion (I4);
- `β : M →+ M` fixing `range τ`;
- I5, Lemma 3.21(1), (4), using the fork's `gCl`.

Every field is a consequence of a printed TYZ statement (table in `docs/research/pn-design.md` §2).
The one exception is the typing of `β`, which needs F5.

**Compile status (VERIFIED).** `lake build ZInQKernel` is up to date. `lake env lean
scratch/pn-design/PropN.lean` compiles with exactly four `sorry`s: `lemmaN1_core`, `lemmaN2`,
`finalStep`, `matching`. The following are proved:
- `lemmaN1`, the uniqueness induction from the core;
- `tyzRow5b_of_tyzInputs : TYZInputs → Literature.TYZRow5b`;
- `tyzThm35ReadingA_of_tyzInputs`;
- `Witness.genusData_nonempty`: for any `L` with `L n ≠ 0`, `GenusData L n` is inhabited, so its
  fields are not jointly contradictory. Axioms: propext, Classical.choice, Quot.sound.

**Finding (VERIFIED).** Lemma N2 in the form `c_n(e) ≡ 𝓛(n/e) (mod 2)` holds for any integer `𝓛`.
Its proof is a divisor-pairing induction that needs no Lemma 2.8 and no N1. It does need ε's
(5,3) class to be uniform: `n2_check.py` finds 0 mismatches in 190 trials with uniform classes
and 154 mismatches with mixed classes. So rv-prop-n's "value at (5,3) irrelevant" is too strong.

**Plan** (pn-design.md §6). Estimated sizes; A and B can start now.
- A `finalStep` (~150–250 lines): pure ℤ[i]/τ algebra.
- B `lemmaN2` (~300–450): inductive identity worked in `ℤ[i]/(2)`, with `Finset.sum_involution`
  on `q ↦ m/q`. Not the chain expansion.
- C `matching` (~350–600): first transport `Lam`/`T5aCl`/`T5bCl` to `Finpartition`s of
  `n.primeFactors : Finset ℕ` (shared with D), then split at the class-5/7 block with `avoid` and
  `extend`.
- D `lemmaN1_core` (~400–700): product lemma for partition sums, then counts of `2^{|C|}` and
  `2^{b−1}` unions of blocks, with the `p₀`-representative trick for `m ≡ 1`.

**Most serious risk to faithfulness.** `β : M →+ M` presumes that `ℍ'_n/ℚ` is Galois (F5). TYZ
use this only implicitly (L2593–2595). It follows from their Proposition 3.2(1) and the dihedral
structure of ring class fields (Cox, Lemma 9.3; STANDARD), but it is the one field that is not a
TYZ sentence. A fallback through F4 is sketched in pn-design.md §5. Next in line: the ε-uniformity
at (5,3) (printed, L1309–1310), on which N2 depends.
