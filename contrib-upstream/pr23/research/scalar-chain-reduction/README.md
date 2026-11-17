# Scalar order 31 and a smaller anchor above PR #9

This conditional research proposal rearranges the scalar norm tree at the
same variable cost. Its proposed local argument raises scalar order from
28 to 31, permitting the anchor to decrease from `3^2364` to `3^2130`.

| | PR #9 | This layer |
| --- | ---: | ---: |
| Variables, including the input | 385 | **385** |
| Quadratic residuals | 353 | 353 |
| Quartic monomials | 26,235 | **26,200** |
| Maximum coefficient digits | 757 | **682** |
| Maximum coefficient bits | 2,513 | **2,266** |

The exact new coefficient maximum is `28902 * 3^1420`. Every variable
occurs; the polynomial has degree four and integer content one, and its
input fourth-power coefficient is one. Its decimal table SHA-256 is
`c9e3e65c64c360c1cbf22c44704776c000294a1a7028e6f3f80bbe500243bdfb`.

The construction retains general scalar preparation (`W=1+N`), all point
guards, and the four factored conics from #9. Read [PROOF.md](PROOF.md) for
the actual chain, both-place proxy application, finite preparation and all
three height consumers. [APPLICATION_CONTRACT.json](APPLICATION_CONTRACT.json)
is an unaccepted author contract; independent review and manuscript
incorporation remain pending. The inherited global arithmetic is conditional.

Run from the repository root using Python and Node:

```sh
python3 -B research/scalar-chain-reduction/reproduce.py --output build/scalar-chain
```

The output must be absent or empty and outside the source packets. The
runner verifies the frozen source manifest, compares all raw rows, checks
the scalar identities and exact integer margins with five negative controls,
then replays the compiler, conic transport and every decimal coefficient.
The output must match [EXPECTED.json](EXPECTED.json), including the exact
compiled IR and table hashes. It also checks source bindings before and
after execution.

The existing research CI job runs this replay after the parent's complete
23-stage reproduction and the four-conic check, and uploads the receipts
and decimal table. Finite checks do not accept the uniform arithmetic proof.
