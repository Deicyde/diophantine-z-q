**Result and scoped stop.** The residue test for the fixed pool is exactly the
stage-phase formula in (O.5), after cancelling the common quadratic sign.
For the actual local factors, the extraction-prime factors also cancel the
genus twist, leaving only the root factors at the elliptic conductor and
the detecting-prime factor in the phase comparison. Lean constructs the
phase from the local residue characters and the genus character, and proves
the exact `hchar` for the pool using that phase. On the
pinned base, an independently supplied `Lift` does not identify its
characteristic-zero phase with this construction. The remaining work is to
make that identification in the stage constructor. The manuscript defines
the phase this way (tex 8422–8424, 8903–8923, 8982–8985) and uses the *same*
phase throughout the pool (tex 9706–9710). There is no additional manuscript
character identity to assume or print.

## The actual pool and residue test

Write $N_0=D_\ell.\mathrm{old}$, $N=N_0\prod_{p\in P.\mathrm{pool}}p$ (the
computational level), and $m=S.m=|h_*|$. The exponent of stage precision in
`Lift S` is separate from these levels. For $u\in(\mathbb Z/N)^\times$ set
$d=(u:\mathbb Z/N).\mathrm{val}$ and $\iota=\kappa\circ\mathrm{algebraMap}(O,K)$.
In [`BlocksPerU/Assemble.lean`](../../ZInQKernel/Contrib/OneProof/RC/BlocksPerU/Assemble.lean),
`realize_of_stage` calls `realize` with
`C = diamondCharacters Dₗ.common_four η η_eval η_order` from the same
`Lift E`. Its representative is $d$, and `η_eval` means $(\eta(u):O)=E.\eta(d)$.
The empty moving set has no level or character twist from any of the pool
primes. In the manuscript, $B_\varnothing$ is the scalar multiple of the fixed
$g$ in tex 9491–9496; only the moving primes contribute $(p/\cdot)$ in tex
9497–9546. Multiplying by ordinary $\theta$ for weight two keeps the scalar
character: the four theta multipliers give the weight-two factor
(`BlocksPerU.theta_product_slash`, tex 9647–9658).

At $U=\varnothing$, the definition of `bCharacter` retains only
`C.η * C.symbol (-1)` after the two integer and coefficient inclusions.
Here $4\mid N$, so the prescribed value of `C.symbol (-1)` applies on every
unit. With complex values understood, the actual test from
`oldCharacter_comp_eq_iff` is therefore
$$
    \iota(E.\eta(d))\operatorname{Jacobi}(-1,d)
    =
    \left(\prod_p\alpha_p(u\bmod c_p)\right)\operatorname{Jacobi}(m,d).
$$
The $\alpha_p$ are the local *scaling* characters of the fixed weight. This
includes the chosen root characters at primes of the elliptic curve level,
the Legendre factors at $p\mid m$, and the one at $\ell_0$ (tex 8499–8515,
8517–8534, 8536–8556, 8571–8576). At the other primes the factor is trivial.
An extra fixed norm sieve contributes no scaling character: multiplying by a
local unit multiplies the norm by a unit square, preserving coprimality and
unit squareclasses (tex 8563–8566, 9094–9098, 9471–9479).
The inverse finite operator gives $d$, with no inversion of these factors
(tex 8903–8906, 8932–8936, 9012–9015).

The established `Odd.psi_div_eta` gives
$\operatorname{Jacobi}(m,d)=\operatorname{Jacobi}(-m,d)\operatorname{Jacobi}(-1,d)$.
The last factor squares to one. Thus the exact condition for a preexisting
lift and independently supplied complex local characters is
$$
  \forall u\in(\mathbb Z/N)^\times,\qquad
  \iota(E.\eta(d))
  =
  \left(\prod_p\alpha_p(u\bmod c_p)\right)\operatorname{Jacobi}(-m,d).
$$
For the actual stage, let $A$ be the primes of the elliptic conductor
together with $\ell_0$, with trivial factors allowed. The scaling support is
$A\sqcup\{p:p\mid m\}$, since $h_*$ is prime to the elliptic conductor
(tex 8228–8230, 8585–8591) and $\ell_0$ avoids $m$ (tex 8437–8438).
By `LocalWeights.negativeDiscriminant_unit_character`, the product of
the prescribed Legendre factors at $p\mid m$ is already
$\operatorname{Jacobi}(-m,d)$, because $m$ is squarefree and $d$ is odd.
It is a sign on these units, so multiplying by the genus twist removes
it. Consequently the **smallest comparison for the actual data** is
$$
  \forall u\in(\mathbb Z/N)^\times,\qquad
  \iota(E.\eta(d))=\prod_{p\in A}\alpha_p(u\bmod c_p).
$$
This cancellation is on-the-spot (c) using the existing local weights
calculation. In particular the quadratic detecting-prime factor
$(d/\ell_0)$ is still present. The formula concerns only the phase, not
the extracted form's determinant character.

This is on the common unit group, where all factors are defined. If a
manuscript evaluation is phrased on integers avoiding additional named
primes, use a representative prime to those primes: reduction from the units
of a common multiple of $N$ and the additional primes is surjective
(`ZMod.unitsMap_surjective`). Compare the values as characters via pullback;
do not assume a least representative avoids primes outside $N$.

## Lean statements and the old-stage input

The statements are in [`Identification.lean`](../../ZInQKernel/Contrib/OneProof/RC/PoolCharacter/Identification.lean)
and [`Extraction.lean`](../../ZInQKernel/Contrib/OneProof/RC/PoolCharacter/Extraction.lean),
with the same `Dₗ`, `S.m` and common-level pool constructor as the consumer.

| Theorem | Statement and use |
| --- | --- |
| `embedded_bCharacter_empty` | For any existing `DiamondCharacters C`, the complex value of the empty moving-set character at $u$ is the embedded source phase at `C.representative u` times $\operatorname{Jacobi}(-1,\mathrm{rep}(u))$. Evaluates the right side of `hchar`. |
| `phaseCharacter_value` | If $4m\mid N$, the value of `phaseCharacter` in $O$ at $u$ is $\prod_p\alpha^O_p(u\bmod c_p)\,\operatorname{Jacobi}(-m,d)$. Evaluates the phase independently of `hchar`, via the existing common-level quadratic character construction. |
| `oldCharacter_comp_eq_bCharacter_iff` | For `ξ = oldCharacter Dₗ.four_dvd hm s c hc α` and the fixed constructor for `C`, `ξ.comp (ZMod.unitsMap Dₗ.old_dvd) = (Units.map κ).comp (bCharacter C ∅)` iff the genus-twisted phase formula displayed above holds. Reduces precisely `hchar` to the general phase formula. |
| `oldCharacter_comp_eq_bCharacter_of_phase` | Take the common-level phase to be `phaseCharacter` of the supplied $O$-valued local homomorphisms and take the complex local homomorphisms to be their images under $\iota$. With the existing stage-evaluation and order arguments of `diamondCharacters`, proves the same homomorphism equality. Supplies `hchar` to `oldStageLaw_of_finiteAction`. |
| `phase_without_extraction` | For squarefree $m\equiv3\pmod4$, $m\mid N$, $4\mid N$, and disjoint factor sets $A$ and $\{p:p\mid m\}$, if the factors at $p\mid m$ are the prescribed Legendre symbols, the full scaling product times the genus sign equals the product over $A$. Simplifies the remaining phase comparison. |
| `oldCharacter_comp_eq_bCharacter_iff_of_extraction` | With that partition and the prescribed scaling values at extraction primes, `hchar` for the full old character is equivalent to the comparison with the product over $A$ alone. Reduces `hchar` for the actual local factors. |

`phaseCharacter` is a homomorphism defined by multiplying the pullbacks of
the local homomorphisms and the integral genus character; it is not defined
via the empty moving-set character or its equality to the Weil character.
No new structure, hypothesis predicate, or print is introduced. The
`η_eval` premise for `oldCharacter_comp_eq_bCharacter_of_phase` is the existing pool constructor's
evaluation of the chosen stage lift, and `η_order` is its existing
pointwise order requirement. Neither asserts a theta transformation,
an old-level character equality, or modularity. The extraction premise
`hextract` independently identifies the local residue values at $p\mid m$
(tex 8536–8549); it says nothing about the pool phase, embedding on the
other factors, or the old character equality. The embedded phase comparison for an independent lift is explicitly an **equivalence** with
`hchar`; it is not asserted as an independent premise of a new structure.
Cancellation, transport to common residues, and using a single ring map on
the products are on-the-spot formal glue (c).

## Remaining hypotheses

| Data or requirement | Manuscript lines and owner |
| --- | --- |
| The fixed odd stage and its `Lift E`, the same pool `P` and `LevelSetup Dₗ`, and the already chosen coefficient comparison $\kappa:K\to\mathbb C$. In particular the existing `Dₗ.common`, `Dₗ.four_dvd`, `Dₗ.old_dvd` supply the level relations; the current theorem is parametrized by these objects. | Tex 8409–8428, 9447–9496, 9647–9662, 9706–9710, 9762–9765. **Existing stage and pool inputs; ELLIOT coefficient and embedding choice.** No comparison of independently chosen complex embeddings is needed if the complex characters are defined by the same $\iota$. |
| $m=S.m$, $m\equiv3\pmod4$, and $m\mid N_0$; for the extraction specialization, $m$ squarefree, the prime sets disjoint, and the factors at $p\mid m$ equal to the prescribed Legendre values; each $c_p\mid N_0$ for the local homomorphisms of the specified weight. `NeZero S.m` and `NeZero N` are interface instances ($m\equiv3\pmod4$ implies the former; positive computational level supplies the latter). `oldCharacter_comp_eq_bCharacter_of_phase` derives $4m\mid N$ from these bounds. | Tex 8207–8212, 8226–8229, 8437–8438, 8536–8549, 8585–8591, 8891–8901, 8925–8936, 8978–8985. **ELLIOT arithmetic stage and old-level realization input.** Values of the actual scaling characters, their support and old-level depth belong to the **stage and local weight lanes**, held here as named data. |
| For the preexisting `Lift E`, identify its chosen phase with the same characteristic-zero local product times the genus character, on representatives of the common units, equivalently with only the factors at the elliptic conductor and $\ell_0$. For the constructed phase, the exact input is `(phaseCharacter … α u : O) = E.η (representative u)` for every unit, with the usual `η_order` (pointwise order a power of two). If building the lift, choose the manuscript phase as its `η` and check the existing `Lift.phase` reduction against the actual `S.η`. The order condition comes from the finite 2-power orders of the local characters and the quadratic genus character. | Tex 8499–8534, 8536–8576, 8593–8596, 8903–8936, 8982–8985, 9083–9089, 9696–9698, 9706–9710. **Stage join, small missing interface identification.** The phase formula is the manuscript's own definition and the text justifies using it in the pool. The missing comparison of two separate Lean fields is interface glue, not an extra ELLIOT mathematical input. |
| The existing `StageGrid` and `RelativeFiniteAction ξ` evaluated on that grid with the same $\xi$ and weights; classwise depth and unit scaling at the actual old level. | Tex 8623–8685, 8726–8890, 8938–8951, 8989–9015, 9030–9036, 9471–9479. **Existing grid and metaplectic sibling lanes**, outside this calculation. Once supplied, the proved `hchar` gives the character input needed to invoke `oldStageLaw_of_finiteAction`. |

## Known issues

- `Lift.phase` only reduces `E.η` to `S.η` modulo the stage precision.
  `S.η_good` is a relation to `S.s` at good primes in the finite stage
  ring. Neither identifies those values with independently supplied
  characteristic-zero local homomorphisms. Likewise, `η_eval` in
  `realize_of_stage` only lifts the phase already in `E`. Defining or
  identifying the phase at the stage join preserves the same local weights,
  coefficient lift and test level.
- Reading $\prod_p\alpha_p$ as only the root weights at the elliptic
  conductor omits the quadratic scaling factors in tex 8536–8556; reading
  $η$ as $η_B$ omits the genus twist in (O.5). Neither substitution is
  justified. No error was found in the scoped manuscript character formulas.
- No cited print is used or added here. The equality
  `oldCharacter_comp_eq_iff` and the Jacobi identity are existing Lean results.

## Manuscript check

- Tex 8207–8212, 8226–8229, 8891–8901 — **OK**: the specified $m$ is the positive absolute value of the negative odd fundamental discriminant, and the determinant has the dyadic sign; the old-level divisibility is still supplied.
- Tex 8499–8515, 8517–8534, 8536–8576 — **unverified**: the actual local scaling data are read from the listed weights and remain named inputs; the character proof does not construct those weights.
- Tex 8536–8549, 8571–8577, 8983–8985 — **gap filled**: the extraction-prime scaling factors multiply to the genus twist and cancel it from the phase; the detecting-prime factor remains.
- Tex 8593–8596, 8903–8906, 8932–8936, 9012–9015 — **OK**: the inverse-idele convention is direct on $d$; the product ranges over all prescribed scaling characters.
- Tex 8907–8923, 8978–8986, 9083–9089 — **OK**: the genus-twisted phase is explicitly defined; its order-two sign quotient is the existing Jacobi identity. Cancellation on the common unit group is now in Lean.
- Tex 8563–8566, 9094–9098, 9471–9479 — **OK**: the specified sieves preserve the scaling factors. The actual depth is a separate input.
- Tex 9447–9454, 9491–9496, 9497–9546 — **OK**: the empty moving set leaves $g$ with only a scalar normalization and no moving twists. The individual moving-prime transformations are outside this proof.
- Tex 9618–9625, 9647–9662 — **gap filled**: the empty ternary block's scalar at the common level is evaluated via the fixed constructor, retaining the same character after multiplication by ordinary theta. No unary transformation is used.
- Tex 9696–9698, 9706–9710 — **OK**: the 2-power order and the reuse of the same stage and phase specify the inputs for the same pool. The characteristic-zero phase field still has to be selected or compared at the stage join.

## Verification

Both new files passed serial `lake env lean -j1`. All six theorem
`#print axioms` checks list only `propext`, `Classical.choice`, and
`Quot.sound`. The proofs use no new axioms or printed-form leaves.
