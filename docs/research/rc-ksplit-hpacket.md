**Scoped result.** The singleton trace identity (tex 10329) holds on the
full characteristic-zero sum at the level in the manuscript, including
the old and Eisenstein blocks. The proof on the old space needs the good
Hecke polynomial on the two degeneracy copies. The vanishing argument
for old blocks in (O.12) alone does not provide that calculation.
The Lean packet passes the resulting trace and determinant equations to
the existing App G seed. The old multiplicity realization, the extra
Fourier shifts, and the comparison with the three blocks of the selected
source are still inputs on the actual constituent model.

All declarations are in `ZInQ.Manuscript.RC.KsplitHpacket`. Write
`t = tV(φ)`, `d = dV(φ)`, `U = U_p`, and `F = X.F {p}`.
The same φ and the same operators are used in the trace identity,
in the determinant action, and in the finite-field match.

## Sizing

| Step | Existing data | Smallest missing comparison on the realized model |
| --- | --- | --- |
| Ramified trace and determinant | `O12Local.Stage` and `combine` give the support of `F` and the conjugate Frobenius eigenvalues λ, μ with `Up = λ` on ramified coordinates, in either sector. | None given that stage. The proof uses λ²(λ+μ) = λ³+λμλ. |
| Old action | `CuspidalData.oldUp` is arbitrary, `Sector.old` records only the chosen inertia element, and the abstract Eisenstein sector also has no old action formula. `GoodRec` and `O12Formwise.AtLevel.good_values` model the good recurrence and trace/determinant values at the lower level; `ThetaCoeff.eisenstein_rec` proves the recurrence for the character pairs. | Identify and span the actual old space by lower-level pairs `g, V_p g` with the coefficient and representation identifications. Per pair there are two Fourier images and two scalar values, independent of other primes' multiplicities. `OldBlockCubic` is the operator-level interface. This is local linear algebra once the degeneracy realization is available; the existing Stage cannot supply the realization. |
| Coefficient reading | `FourierData.UpAtOne`, via `WhittakerComparison.coeff_shift` and the Eisenstein shift at one. The Whittaker fields only give the action and the translation equality at one. `O12Eisenstein.eisensteinUp_shift` already proves the positive shift for its explicit ramified operator. | `UpShift` requires only the two additional readings at `p` and `p²` on the active space. It is not an all-index assumption. The proof of the old pair action can use all positive indices just on its two generators if the two operator images are not already supplied. |
| Determinants | `dV` is the coordinate determinant and `weightTwist_frob` gives the factor `p` at an odd prime. `sqrtChar` and its good-Frobenius reading distinguish the character of positive `p` from the one of `p*`. | `DeterminantAt` identifies the common character on the realized B and Θₚ supports with the twist of the character on Θ₁. It concerns one lift; a good-place comparison can instead be extended with `det_eq_of_frobenius` if continuity is supplied in the coefficient field topology. The underlying model gives no topology or determinant character attachment. |
| Assembly | `thetaMul_linear`, `DphiBlocks`, `exists_fresh_trace_match`, and `kSplitSeed_of_singleton_trace` consume exactly these equations. | A new `Packet` extends the existing Stage with these comparisons, the three Fourier realizations and a zero-index slot. `MatchedPacket` adds the two existing matching hypotheses. The realized blocks and their exact subtraction refer to the same transported source and full `D.m₂`. |

For the old pairs the formula is `Ug = a_p g − d V_p g`, `U(V_p g) = g`, where
`d = p χ(p)` on that factor. Thus `U² − tU + d = 0` on each such pair;
both `t` and `d` are scalars on the pair, and the cubic follows.
In the Eisenstein case the good trace and determinant are the sum and
product of the two character values, and the divisor-sum recurrence
gives the same matrix. A pair here is for level exponent one. At higher
exponent the quadratic can fail on the enlarged old space; no such
generalization is asserted. The old proof and the determinant
bookkeeping are on-the-spot (c); no print or LEAF is added.

## Lean results

| Declaration | Statement and use |
| --- | --- |
| `scalarOp_supported`, `scalarOp_eq_smul_of_support` | Coordinatewise multiplication preserves support, and a multiplier constant on that support scales the whole vector. Supplies support in the trace proof and the block action of `dV`. |
| `combine_active_stable`, `old_stable` | The masked combined operator has active output. It sends old vectors to old vectors because the ramified output coordinates are diagonal. Supplies iteration in the trace and cubic proofs. |
| `trace_det_of_diagonal` | A Frobenius matrix conjugate to diag(λ,μ) has trace λ+μ and determinant λμ. |
| `ramified_law`, `up_trace_identity` | On ramified support the operator satisfies `U²(t v) = U³ v + d(Uv)` and `U(dv) = d(Uv)`. With `OldBlockCubic` the same holds on the entire active sum. |
| `trace_coeff_p_sq` | `UpAtOne` and `UpShift` read `(tF)[p²] = F[p³] + (dF)[p]` in `X.K`. Supplies the trace equation. |
| `old_frob_values`, `old_scalars_of_frob` | Trivial inertia at the prime of the local pair transports the good trace and determinant to its chosen lift. Constant values on a support give the corresponding trace and determinant eigenvector equations on both old copies. |
| `old_pair_up_of_goodRec` | The two positive Fourier shifts and expansions on `g, V_p g`, with the good recurrence and faithful active expansion, give `Ug = a_p g − p χ(p) V_p g`, `U(V_p g) = g`. |
| `OldPair.map_up_g`, `oldBlockCubic_of_pairs` | A common scalar operator on an old pair still acts by that scalar on `Ug`. Spanning by such pairs gives the trace and determinant commutations and the cubic in `OldBlockCubic`. |
| `positivePrimeSign_eq_one_or_neg_one`, `positivePrimeSign_at_frob` | The character of √p takes values ±1, with Legendre value `(p/q)` at odd good Frobenius away from p. |
| `det_of_eisenstein_pair` | On a coordinate attached to the normalized Eisenstein pair, its determinant is the product of the two Dirichlet characters and one weight-two cyclotomic factor. |
| `det_eq_of_frobenius` | Two continuous determinant readings in a Hausdorff coefficient field agreeing on arithmetic Frobenius outside a finite set agree on `GalQ`. |
| `coeffIndex_pos`, `fourier_F_of_blocks` | The all-index coefficient convention reproduces `FourierData.index` at positive indices, and the realized block sum is `θ H_p` at every index after embedding. Supplies the middle term of the trace equation. |
| `det_actions_of_characters` | On the three supported vectors the actual determinant acts by the cyclotomic and nebentypus scalars, with the same scalar on B and Θₚ. |
| `dphiBlocks_of_characters` | Supplies `δ_B = δ_p`, `δ_p ∈ O`, `δ_p − δ_1 ∈ 2O`, and `DphiBlocks` for the actual determinant translate. |
| `hpacketTrace_of_packet` | Supplies the previous four determinant conjuncts and the singleton trace equation for the same embedded `tV` and `dV` readings. |
| `hpacket_of_packets` | Supplies the exact `hpacket` argument of `kSplitSeed_of_singleton_trace`, including the prime and trace match from `exists_fresh_trace_match`. |
| `kSplitSeed_of_packets` | With the existing ring and lower-bound hypotheses and the same-source divisions and matched packets, gives `KSplitSeed W D (RevGen S G.r)`. |

## Remaining hypotheses and owners

- **Weight-two realization:** supply `X`, `FourierData`, the actual
  singleton `O12Local.Stage`, the old spanning pairs with their actual
  Fourier action, and `UpShift`. The good attachment and the Hecke
  recurrence are already separate in the tree; the remaining local
  comparison identifies their data with this same Stage. Supply the
  three entries of `BlockRealization` (including `b₁` and `bₚ` in the
  chosen coefficient field), the common Dirichlet nebentypus and
  `DeterminantAt` on those supports. `det_eq_of_frobenius` leaves
  continuity and the good determinant formula as inputs when using
  the density route. This is the realization lane's characteristic-zero work.
- **Even source and place above two:** the place and budget lanes supply
  the selected coefficient ring, its exact unit and phase conditions,
  `χ_mem` for the actual character value, and the `Hp` integrality
  conjunct on this same source. Appendix E and the source binding are unchanged.
- **Trace match:** the trace realization supplies `htr` on a finite
  extension and `hhecke` at the specified good Frobenius elements,
  both on the actual `p²` coefficient at the same packet. The prime
  itself and the congruence are derived.
- **Old unit and companion:** the existing `hlow` and subsequent
  companion inputs stay with their owners. They are independent of the
  old weight-two degeneracy calculation.

## Known issues

- Tex 10329 is right on all the stated blocks, but the preceding
  proof of (O.12) does not treat the old action needed for this identity.
  The missing argument is the two-copy calculation above. Arbitrary
  operators satisfying `Sector.old` need not satisfy tex 10329.
- The previous support slip (tex 10393–10404) is unchanged: the zero
  branch requires the full stationary transported support before
  adjoining p. The existing seed proof uses the determinant formula
  at tex 10375–10386 instead.
- `FourierData.index` is positive only. The explicit zero slot and
  the three all-index realizations in this packet ensure the conclusion
  has the all-index type required by `DphiBlocks`.
- The twist ratio at a chosen lift is the sign for positive `p`.
  It need not be (+1), and for `p ≡ 3 mod 4` the primitive
  conductor-`p` sign of √(p*) may differ by the character at 4.
  The proof does not set δₚ equal to δ₁.

## Manuscript check

Tex references were VERIFIED in the manuscript. No external locator was
rechecked and no new print is cited.

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 9541–9553, 9620–9626 | unverified | These transformations give the level exponent and the two half-integral characters used here. Their modular realization on the selected source is an input. |
| 9638–9654 | unverified | The coefficient place and weight-two constituent realization, including the Eisenstein pairs, are inputs. |
| 9754–9771 | gap filled | The old space is treated with both degeneracy copies per lower-level factor; no diagonalization of the old operator is required. Identifying these vectors in the actual sum remains a realization comparison. |
| 9773–9797 | OK | With arithmetic Frobenius the good trace and determinant are `a_p` and `p χ(p)`; trivial inertia gives the same values at the lift in the packet. The attached polynomial on actual cuspidal forms is an existing input. |
| 9799–9840, 9855–9864 | unverified | Reuse the provided ramified eigenline comparison and Eisenstein sector of the existing Stage; the external conductor and newvector assertions were not re-audited. |
| 9844–9854 | unverified | The seed reading needs two further shifts beyond the proved shift at one; `UpShift` names those two comparisons on the actual operator. |
| 9866–9889 | OK | The ramified diagonal calculation and the zero old inertia differences prove (O.12). The latter argument has no old cubic content. |
| 10326–10331 | gap filled | The identity holds on ramified and old blocks including Eisenstein. The old pair polynomial is the missing calculation for 10329; determinant commutation and the three shifts give 10330. |
| 10332–10333 | OK | Follow the seed in using the ideal generated by integer two, keeping the finite-field match separate. |
| 10338–10344 | unverified | The three-block subtraction is read literally; same-source division and integrality are a budget input. |
| 10355–10360 | gap filled | Coordinate determinant gives scalar action on each support, including old multiplicities. The comparison with the cyclotomic and character values on the realized blocks is explicit. Only membership in `O` is needed here. |
| 10361–10369 | OK | The shared twisted character gives equal determinants on B and Θₚ at φ, including its ramified character. |
| 10370–10379 | OK | The quotient character is the sign of √p, so the difference is zero or `−2δ₁`. Linearity gives `DphiBlocks` and the existing exact identity uses that expansion. |
| 10393–10404 | error | The prior support slip if “old support” is read as pre-transport support; the formula used here avoids that split. |
| 10437–10441 | OK | The existing fresh trace match gives the required prime and integer-two congruence from descent and the good formula. |

## Verification

VERIFIED: Lake built the base imports offline. All five new modules
passed `lake env lean -j1`, with one Lean invocation at a time.
`scratch/rc-ksplit-hpacket/Axioms.lean` printed the axioms of all 24
new theorems; only `propext`, `Classical.choice`, and `Quot.sound`
occurred. The result type of `hpacket_of_packets` also matches the
seed's `hpacket` binder verbatim.
