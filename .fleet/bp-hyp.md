# bp-hyp: the hypothesis forms of the main theorem in the blueprint

No Lean file was edited. `lake build ZInQKernel` succeeds;
`autoform check blueprint --lean-root .` gives OK (398 articles, 1275 dependencies, no
warnings) and `autoform audit blueprint` gives OK (no warnings).

## Articles added

| Article | Lean names | Status |
| --- | --- | --- |
| `main/six-contact-min.md` (the minimal height hypothesis, def) | `ZInQ.SixContactMin` | statement formalized (hypothesis) |
| `main/six-contact-min-of-estimate.md` (H implies its minimal form, theorem) | `ZInQ.sixContactMin_of_sixContactEstimate`, `ZInQ.Mult.le_heightD_of_mem_S_mul` | proved |
| `main/two-slope-pattern.md` (22P₂, def; not proved here, needs Green–Tao–Ziegler as 22P does) | `ZInQ.TwoSlopePattern`, `ZInQ.GoodSlopePrime` | statement formalized (hypothesis) |
| `multiplication/completeness/slope-representation.md` (SR, def) | `ZInQ.Mult.SlopeRepresentation`, `ZInQ.Mult.GoodSlope` | statement formalized |
| `multiplication/completeness/slope-representation-from-pattern.md` (22P ⇒ SR) | `ZInQ.Mult.slopeRepresentation_of_fixedPrimePattern` | proved |
| `multiplication/completeness/slope-representation-from-two-slope.md` (22P₂ ⇒ SR) | `ZInQ.Mult.slopeRepresentation_of_twoSlopePattern` | proved |

The ids were generated with `autoform migrate article-ids` and inserted by hand into these six
files only. `--write` would also have stamped ids on about twenty container READMEs that have
none.

## Articles changed

| Article | Lean names | Change |
| --- | --- | --- |
| `main/main-theorem.md` | `..._of` (now first, so it takes the credit), `..._of_sixContactEstimate`, `..._of_addMulBound`, `..._of_twoSlopePattern` (added) | Assumes the minimal height hypothesis, PC, 22P. Depends on: target, minimal H, PC, 22P. Proof depends on: assembly, 22P ⇒ SR, catalogue instance. One sentence on the 22P₂ variant and one on the H-form corollary, linked in the prose only. |
| `assembly/assembly-lemma.md` | `ZInQ.Assembly.Pstar_spec`, `ZInQ.Assembly.assembly` | Hypotheses are now minimal H, PC, SR, as in Lean. |
| `assembly/ordinary-value-relation.md`, `assembly/main-branch-exactness.md` | unchanged | Hypotheses are now minimal H, PC, SR, as in Lean. The main-branch proof sketch now uses `M_{S_mul} ∣ M_{S_ht}`. |
| `multiplication/multiplication-template.md` | unchanged | Hypotheses are now minimal H, PC, SR. |
| `multiplication/completeness/completeness.md` | `ZInQ.Mult.multiply_complete` | Assumes PC and SR. The proof no longer depends on pattern-slopes. |
| `multiplication/soundness/{soundness,finite-box,contact-support}.md` | unchanged | Assume the minimal height hypothesis, with `H₆(D) ≤ H₆(S_mul;R) = A_ht`. |
| `multiplication/certificate/constants-properties.md` | unchanged | Item 2 now states the `sixContact_at_Smul` consequence under minimal H. Depends on minimal H. |
| `multiplication/completeness/{slope-completeness,pole-input-valuations}.md` | unchanged | "Conditions 1-4" now refer to the slope-representation article, not to pattern-slopes, so they no longer pull in 22P. |
| `multiplication/completeness/pattern-slopes.md` | `ZInQ.Mult.pattern_slopes` (`GoodSlope` moved to the SR article) | Statement correction, see below. |
| `main/README.md`, `multiplication/completeness/README.md` | none | Place the new articles. |

## Statement corrections

- **pattern-slopes, condition 3.** The article required the odd contact primes to be good
  primes of 22P, including `p ∤ d₁d₂`. The Lean `GoodSlope` asks only for `GoodSlopePrime`:
  `r² = 2` mod p, `75 ∓ 53r ≢ 0`, and `gcd(d₁, d₂) = 4`, without `p ≠ 2` or `p ∤ d₁d₂`. The
  article now says "good slope prime" and notes that 22P's primes also satisfy `p ∤ d₁d₂`. The
  slope-completeness sketch says "good slope prime" accordingly.
- **The ten consumer articles listed above.** They said "assume the six-contact estimate / the
  twenty-two-prime pattern". Their Lean statements take `SixContactMin` and/or
  `SlopeRepresentation`, so the text and the `Depends on` links now name those.
- **22P₂ article.** `GoodSlopePrime` is stated literally, as the existence of `r`, with
  point counts that include the point at infinity. The article adds that for odd `p` this means
  splitting plus good reduction at both places. It also notes that `v`, `u - v` and
  `u - (A+9)v` are nonzero by the primality condition, so their valuation bounds are not
  vacuous.

## Problems

- `autoform audit blueprint --lean-root .` (not required by the task) fails on two errors that
  were already there, in files this task did not touch: `lean-target-kind-mismatch` in
  `compiler/natural/programs/ir-integer-routines.md` and
  `compiler/translation/natural-circuit-well-formed.md`. It also gives `node-too-large`
  warnings.
- The assembly articles that take `MultiplicationExact` (close-*, signed-encoding-semantics,
  value-test-semantics) still list H and 22P under `Depends on`. Their Lean statements assume
  `MultiplicationExact`, not H or 22P. I left them alone because that is a different
  abstraction from this task.

## Suggestions

- If the lead wants `..._of_sixContactEstimate` and `..._of_twoSlopePattern` to appear with
  their own dependency edges, give each its own corollary article. In this task they share
  main-theorem's `lean:` list, so they draw no edges to H or 22P₂ and the main theorem's
  dependency closure stays the one the Lean `..._of` uses.
- The Lean lemma `Compiler.Precision.sixContact_at_heightPrimes` (minimal H at `S_ht`) has no
  article. main-branch-exactness describes it in its proof sketch.
