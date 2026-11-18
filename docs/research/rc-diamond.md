# Diamond congruences for the constituent model

**Manuscript verdict.** Appendix F does not state the whole-module
coefficientwise diamond congruence hypothesis `hdiam` of
`buildConstituentModel`. Its integrality claim for diamond translates
(tex 9655–9662) is weaker by itself. The hypothesis does follow from the
manuscript's good Hecke formula, the constituent trace comparison and
its index-by-index fresh Frobenius approximation. The deduction is
on-the-spot, provenance (c). No change to the reduced-expansion model is
needed.

Let `v ∈ Λ` have all positive coefficients in `𝔪`. For any fixed
positive index `n`, use the dense Frobenius tests at good primes `r`
outside the support and the prime divisors of `n`. For every such
Frobenius lift the coefficient of the scalar trace on `v` is
`(Tᵣ v)[n] = v[rn]`, since `r ∤ n`. This lies in `𝔪`.
Continuity and closedness give `(t(g)v)[n] ∈ 𝔪` for arbitrary `g`.
The avoidance set may vary with `n`.

Now fix the desired good prime `q` and evaluate at the positive index
`qn`. Applying the previous result to the chosen Frobenius at `q` gives
`(T_q v)[qn] ∈ 𝔪`. The full Hecke formula gives
`(T_q v)[qn] − v[q²n] = q (⟨q⟩v)[n]`. The left-hand side is in `𝔪`,
and `q` has residue one because it is odd and `2 ∈ 𝔪`. Hence
`(⟨q⟩v)[n] ∈ 𝔪`. The prime used for the operator here is `q`; the
primes used to approximate its trace in the first step avoid `qn`.

## Lean statements and handoff

Both theorems are in namespace `ZInQ.Manuscript.RC.Diamond` in
`ZInQKernel/Contrib/OneProof/RC/Diamond/Congruence.lean`.

- `trace_congruence_of_fresh_hecke`: for `v : Λ` with
  `hv : ∀ n, n ≠ 0 → coeff n v ∈ m` and every `g : GalQ`, proves
  `∀ n, n ≠ 0 → coeff n ⟨tV ρ g v, hst g _ v.2⟩ ∈ m`.
- `hdiam_of_hecke`: proves exactly the argument
  `∀ q, T.Good q → q ∉ avoid → ∀ v : Λ, (∀ n, n ≠ 0 → coeff n v ∈ m) → ∀ n, n ≠ 0 → coeff n (ops.diamond q v) ∈ m`
  of `buildConstituentModel`.

The named inputs use the same coefficient ring `O`, field `K`, ideal
`m : Ideal O`, conductor/type data `T`, finite exclusion set `avoid`
and chosen Frobenius family `frob : ℕ → GalQ` as the constructor:

| Input and Lean type | Expected supplier |
| --- | --- |
| `hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q` | Existing `AddressGenuine.frobeniusExists`; select the lifts used by the constituent data. |
| `ρ : I → GalQ →* GL (Fin 2) K`, `Λ : Submodule O (I → K)` | `rc-theta-coeff`: characteristic-zero constituent coordinates, with old multiplicities, and the integral translate module. |
| `hcont : ContinuousOperators ρ Λ`, `hunr : UnramifiedConstituents T avoid ρ` | `rc-theta-coeff`: continuity and good-prime unramifiedness of those representations. `continuousOperators_of_matrix` gives `hcont` from continuous matrix entries. |
| `ops : GoodOperators T avoid frob ρ Λ` | `rc-theta-coeff`: integral Hecke and diamond maps on the translate module; the existing fields compare them with scalar traces and determinants at the chosen lifts. |
| `coeff : ℕ → Λ →ₗ[O] O`, `hcoeff : ∀ n, Continuous (coeff n)` | `rc-theta-coeff`: the single family of integral Fourier coordinates and continuity. |
| `hhecke : ∀ q, T.Good q → q ∉ avoid → HeckeFourier coeff (ops.hecke q) (ops.diamond q) q` | `rc-theta-coeff`: the formula on all of `Λ`, including indices divisible by `q`. The constructor already obtains it from `D ∅` and `hD ∅`. |
| `hm2 : (2 : O) ∈ m`, `hm : IsClosed (m : Set O)` | The coefficient DVR data from `rc-theta-coeff`. `hm2` is needed only for `hdiam_of_hecke`. |
| `hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ` | Already proved by `stable_operators` from `ops`, `hfrob`, `hcont`, `hunr` and closedness of `Λ`. The constructor uses `lattice_closed Λ hΛ`, for `hΛ : Λ.FG`. |

The translate generators of `Λ` and the scalar character action of
diamonds are the mathematical data behind `Λ`, `hΛ`, and `ops`.
In particular the constituent determinant comparison `ops.det_eq`
is the weight-two identity `d(Fr_q) = q⟨q⟩`. The displayed
correction coefficients and the unary support belong in the existing
`D : ∀ U, DeterminantFourierData ops m (F U)`, with
`hD : ∀ U, (D U).coeff = coeff`, and `F : Finset ℕ → Λ`, from
`rc-theta-coeff`. They remain needed by the constructor's determinant
orbit proof. Their explicit values, the orders of the characters, and
the presentation by generators need no additional hypotheses in the
diamond congruence proof.

At the constructor call, take
`hst := (stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1`
and `hhecke := fun q hq hqa => hD ∅ ▸ (D ∅).hecke_eq q hq hqa`.
Then pass `hdiam_of_hecke hfrob hcont hunr ops hst coeff hhecke hm2 hm hcoeff`
as `hdiam`. The existing `congruence_of_hecke` fills `cong_t` and
`cong_d`, which `GaloisConstituentModel.tE` and `.dE` use to descend
to `Mexp`. No consumer changes or new printed leaves are required.

## Verification

`Congruence.lean` passed `lake env lean --threads=1`. Both
`#print axioms trace_congruence_of_fresh_hecke` and
`#print axioms hdiam_of_hecke` returned
`[propext, Classical.choice, Quot.sound]`. The file has no `sorry` or
new axioms.

## Known issues

- Integrality of the translates does not by itself show that their
  operators preserve the kernel of coefficientwise reduction. Nor does
  reduction of the constituent character values show that diamond acts
  as the identity on reduced expansions: the integral translate module
  need not split along those constituents. The Hecke argument handles
  congruence preservation without integral projectors or saturation.
- The level is divisible by four and the coefficient residue
  characteristic is two. A (q)-expansion principle over
  `ℤ[1/N]` at that level gives no comparison modulo `m`. The proof uses
  only positive coefficients and makes no assertion at index zero.
- The model is conditional on the named genuine-form data. This run
  does not construct them or verify the external source cited for the
  constituent comparison. The other constructor inputs, including the
  coefficient readings and `two_fresh`, are unchanged.
- A mixed build cache failed to supply executable code for an imported
  specialization of `poleMultiplier`. Rebuilding the vendored
  `lean/ZInQ/PoleValuation.lean` from unchanged source resolved the
  failure; no project dependency source was changed.

## Manuscript check

- Tex 2016–2025, 9471–9472 — OK: two is in the fixed support and the fresh primes avoid it; in Lean `T.Good.ne_two` follows from `T.two_dvd`.
- Tex 9638–9646 — OK: coefficientwise reduction requires no comparison with the abstract quotient `Λ/𝔪Λ`.
- Tex 9647–9662 — unverified: the identification of the genuine theta products, the diamond correction formula, and the good Hecke formula for their translates are supplied by the named theta data.
- Tex 9663–9668 — OK: closedness and operator continuity permit passage from the dense good Frobenius tests to the integral scalar operators.
- Tex 9712–9717 — gap filled: for one trace on any vector of `Λ`, avoid the divisors of the current positive coefficient index. This proves trace congruence; using the full Hecke formula at a multiple of a fixed good prime then proves `hdiam` (c).
- Tex 9719–9739 — OK: the determinant identity is evaluated on the reduced trace orbit using the unary corrections; this is distinct from the new whole-module congruence result.
- Tex 9762–9797 — unverified: the constituent comparison is a named input, with the manuscript's Frobenius convention. No external locator has been checked.
- Tex 9891–9902 — OK: evaluate the characteristic-zero identity on the integral form and then reduce; this does not require an integral constituent decomposition.
