# bp-assembly report

Chapter: `blueprint/roadmap/assembly/` (Section 1, lines 52-140; Section 11, lines
6094-6271). Locators: `blueprint/sources/assembly-locators.md`. `autoform check`: OK.
`autoform audit`: no finding in the owned paths. The remaining errors belong to other people's
paths: `declared-coverage-gap` rows in `coverage/README.md`, and `missing-source-link` on the
stubs in `compiler/`, `multiplication/` and `size/`.

## Articles written (29 leaves, 4 containers)

Containers: `assembly/README.md`, `assembly/value-templates/README.md`,
`assembly/approximation/README.md`, `assembly/local-tests/README.md`.

| Path | Decl. | Origin | Hypotheses in statement |
| --- | --- | --- | --- |
| assembly/assembly-lemma.md (interface) | theorem | cited (Lemma 1.2) | H, PC, MW, 22P, CAT |
| assembly/ordinary-value-relation.md (interface) | theorem | cited (Sec. 11.3) | H, PC, MW, 22P |
| assembly/main-branch-exactness.md | theorem | bridged | H, PC, MW, 22P |
| value-templates/nonzero-multiples.md | lemma | bridged | none (torsion only) |
| value-templates/natural-codes.md | theorem | cited (Sec. 3.1) | H, PC, MW, 22P |
| value-templates/signed-encoding-semantics.md | theorem | cited | H, PC, MW, 22P |
| value-templates/close-coordinates-semantics.md | theorem | cited | MW |
| value-templates/double-and-add-chains.md | lemma | bridged | none |
| value-templates/exceptions-semantics.md | theorem | cited | MW |
| value-templates/six-local-tests.md | def | cited (Test) | none |
| value-templates/value-test-semantics.md | theorem | cited | H, PC, MW, 22P |
| value-templates/outer-recipe-relations.md | theorem | bridged | none |
| approximation/precision-predicate.md | def | cited (Sec. 10 opening) | none |
| approximation/close-relation.md | theorem | cited | H, PC, MW, 22P |
| approximation/close-soundness.md | theorem | cited (eq:close-sound) | H, PC, MW, 22P |
| approximation/real-subtraction.md | lemma | background | none |
| approximation/real-accumulation.md | theorem | background | none |
| approximation/real-derivative.md | lemma | background | none |
| approximation/close-completeness.md | theorem | cited (eq:close-complete) | H, PC, MW, 22P |
| local-tests/k0-valuations.md | lemma | background | none |
| local-tests/formal-group.md | lemma | background | none |
| local-tests/formal-multiplication.md | lemma | background | none |
| local-tests/good-reduction-multiples.md | lemma | background | none |
| local-tests/bad-place-check.md | lemma | bridged (FINITE) | none |
| local-tests/deep-multiples.md | lemma | bridged | none |
| local-tests/test-divisibility.md | lemma | cited (Lemma 11.1) | none |
| local-tests/pole-input-local.md | lemma | bridged | none |
| local-tests/pole-input-real.md | lemma | bridged | none |
| local-tests/test-completeness.md | lemma | cited (Lemma 11.2) | PC |

Every leaf has an implementation note under `blueprint/.implementation-notes/` (namespace
`ZInQ.Assembly`). The assembly lemma's draft ends with
`assembly hH hPC hMW h22 hCAT : FrozenTarget`, so `ZInQKernel/Main.lean` becomes a single
line.

## Finite computations

1. `local-tests/bad-place-check.md`, part 1: `v_s(x(P₀)) = -6`, so `P₀ ∈ E_3(s)`. A small
   rational computation (`norm_num` with the model's `v_s(a+bs) = min(2v₂a, 2v₂b+1)`).
2. `local-tests/bad-place-check.md`, part 2: `[7]P₀` is affine and `v_d(x([7]P₀)) = -2`.
   Method: kernel certificate. Four group-law steps (`[2]P₀, [3]P₀, [6]P₀, [7]P₀`) on
   literals below `10^170` are checked by `norm_num`; then, writing
   `x([7]P₀) = (α+βs)/γ` with `gcd = 1`, check `49 ∣ γ`, `343 ∤ γ` and `(α+3β) mod 7 ≠ 0`.
   I confirmed these values with an exact Python computation in ℚ(√2) (`v₇(γ)=2`,
   `α+3β ≡ 2 mod 7`). No `native_decide`.
3. Trivial `decide` facts used inline: `0 < |c-c'| ≤ 60` for distinct contact values; `S_ht`
   (primes ≤ 324) has maximum 317; `v_p(2730⁶) = 6` for `p ∈ {2,3,5,7,13}`; the chain lengths
   `0,7,6,6,8,9` (36 raw additions).

`A₀ = H₆(S_ht)`, `B(n,κ)`, `D` and `4^B` are always symbolic. The notes require
`@[irreducible]`, and nothing is evaluated.

## Extra hypotheses

None. No input beyond the five hypotheses was needed. The manuscript's cited analytic facts
(the compactness of `E(ℝ)×E(ℝ)`, the formal logarithm as an isometry from Silverman IV.5.5/IV.6.4,
finite index of formal neighbourhoods from VII.6.3, the derivative of `[n]` from IV.2.3) are
replaced by elementary background lemmas with complete proof sketches, all formalizable without
new theory. Mathlib has none of them, and each gap is recorded in its note: there is no
topology on points, no formal groups, and no reduction of points.

## Reformulations and manuscript issues

1. **Lemma 1.2's form.** The manuscript assumes G, M, H, PC, C, B. Here the assembly lemma assumes
   the five Lean hypotheses (H, PC, MW, 22P, CAT): G follows from MW, M from H, PC, MW and 22P,
   C is unconditional, and B's size bounds use CAT. G, M and C are listed under
   "Informally uses". With this form the main theorem follows directly.
2. **Lemma 11.2, "adjusting by one if equality occurs".** This step is never needed. The
   reduced denominator of `q` is coprime to `R₀ > 1`, so `R₀q² ≠ 1`
   (`local-tests/pole-input-real.md`).
3. **Lemma 11.1, `log(U)/log(H) = s₀/h`.** When `p | h` the argument needs care. It is
   expanded through `Q = [gcd(h,s₀)]P₀ ∈ E_1(π)` and `z([m]Q) = m z(Q)·u`, `u ≡ 1`, so `s₀/h`
   is shown to be p-integral and `≡ t` (`local-tests/test-divisibility.md`). The formal
   logarithm is not used.
4. **Lemma 11.2 at the bad primes.** At `s` (ramified, bad) and `d` (additive reduction), the
   manuscript's single citation of VII.6.3 is replaced by explicit facts: `P₀ ∈ E_3(s)` and
   `[7]P₀ ∈ E_1(d)` (the finite computation). At good primes a pigeonhole argument on
   reductions is used.
5. **Section 11.1.** "`E(ℝ)×E(ℝ)`" means the two different real curves `E^{σ±}`, with
   `e± = 75 ∓ 53√2`. The remark "if the resulting positive differences were bounded …" is not
   needed for existence: pigeonhole gives a positive multiple in every neighbourhood, and it is
   nonzero by infinite order.
6. **`A₀ = H₆(S_ht)`.** This uses `R = max(D, 317, 10¹²)` (317 is the largest prime ≤ 324). It
   is the same number as upstream `HeightConstantAlgorithm.heightConstant`, and the
   precision-predicate note gives a bridge to the real-valued `heightH6` of
   `Hypotheses/Height.lean`.
7. **Infinite order of `P₀`.** All uses of infinite order go through
   `value-templates/nonzero-multiples.md`, which needs only the (unconditional) torsion
   theorem. Lemma 11.1 and Lemma 11.2 therefore do not need MW.

## Interface expectations (please check against the other chapters)

- **compiler** (`rational-translation`, `natural-polynomial-semantics`): `close-relation.md`
  uses input C in the form `Rel_precision(E₀..E₄) ⟺ ∃c∈ℕ⁵, Eᵢ = ι(cᵢ) ∧
  Prec(dec c₀,…,dec c₄)`, with `Prec`, `enc`, `dec`, `z`, `ε_l`, `r(a,j)`, `A₀`, `B(n,κ)`
  defined in `assembly/approximation/precision-predicate.md`. The compiler chapter should link
  that def, or provide a bridge from its own predicate.
- **multiplication**: `multiplication-template.md` is used all-input, as
  `Rel_mul(P,Q,R) ⟺ ∃a,b, P=ι(a), Q=ι(b), R=ι(ab)`, under H, PC, MW, 22P (not CAT). If M needs
  more hypotheses, the statements marked "H, PC, MW, 22P" above must be revised.
  `pole-obstruction.md` is used as "B ≠ 0, Φ(B), p ∉ {2,3,5,7,13} ⟹ v_p(B) not negative odd".
- **size**: `syntax-bounds.md` should give `totalDegree < 2↑↑7` and `|coeff| < 2↑↑8` for the same
  `Syntax.Pstar` (it uses CAT).
- **Possible duplicates**: `natural-codes.md` (the compiler-translation or multiplication
  chapters may need it too); `formal-group.md` and `formal-multiplication.md` (Section 6 also
  uses formal groups and the logarithm). Keep one copy and relink.

## Open questions

- Should `z`, `ε_l`, `r(a,j)`, `A₀` and `Prec` live in the compiler chapter instead? I defined
  them here because `close-coordinates-semantics` and `close-relation` need them and the
  compiler articles are still stubs.
- The valuation infrastructure on `ℤ[√2]` (`k0-valuations.md`) should be shared with the model
  chapter's `v_s`, `v_d` (model-field worktree).

## Push status

Both commits (`Blueprint: assembly chapter`, `Fleet report: bp-assembly`) are on the local
branch `wip/bp-assembly` only. `git push origin HEAD:wip/bp-assembly` failed three times:
twice directly (`Recv failure: Connection reset by peer`) and once through `fwdproxy:8080`
(`CONNECT tunnel failed, response 403`). Push from a host with GitHub access.
