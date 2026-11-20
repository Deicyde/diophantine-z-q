**Result.** The actual Appendix F lift uses the product of the root
characters at the elliptic conductor and the quadratic character at the
detecting prime. This is equal in the coefficient ring to the full scaling
product times the (O.5) genus character. It therefore reduces to the
existing finite-stage phase at every input. On the common units, the same
phase defines the pool diamonds, and `actual_hchar` supplies the exact
character equality in `oldStageLaw_of_finiteAction` using one embedding.
There is no residual phase comparison to assume.

Write $N$ for the elliptic conductor, $m=|h_*|$, $\ell_0$ for the
detecting prime, $D_0$ for the old level, and $D$ for the common level.
Let $O$ be the valuation ring from the actual local construction and
$F$ the pool coefficient field. The complex comparison uses the same
map $O\to F\to\mathbb C$ on both sides. The actual character field
with `coefficientEmbedding` supplies the canonical choice; the result
also works over a pool coefficient extension with a chosen embedding
`κ`. The local residue characters are
evaluated on the positive residue $d$ of each unit; their moduli are
$q$ at odd $q$ and four at two. At two outside $N$ the factor is trivial.

The lift's phase on the exceptional unit domain is
$\prod_{q\mid N}\alpha_q(d)\,(d/\ell_0)$. Off this domain it has the
existing stage's zero extension. In particular the extension still
vanishes at nonunits of the extraction primes: cancellation on units
does not remove a prime from that domain. For an odd $d$ prime to the
exceptional primes the extraction product is
$\prod_{q\mid m}(d/q)=\operatorname{Jacobi}(-m,d)$. The genus twist
therefore cancels it, since that symbol squares to one. This
cancellation, the transport to the common unit group, and the reuse of
the coefficient lift are on-the-spot arguments (provenance (c)).

## Lean statements

Here `A = schwartzPhase C m hn`, `C = levelRoots hN H w` in the
actual specialization, and `E = actualLift …`.
`actualDiamonds` is the existing `diamondCharacters` constructor
and `actualOldCharacter` is the existing `oldCharacter` on the
same residue scalars. Ellipses below stand for the stage and numerical
level arguments detailed in the next section.

| Theorem | Statement and use |
| --- | --- |
| `prime_dvd_rootModulus` | `q.val ∣ rootModulus q` for each prime index. Relates the residue moduli to the exceptional set. |
| `reduce_natUnit` (private) | If a residue unit equals the cast of an integer unit $n$, its value as a unit is the image of `PhaseData.natUnit` under reduction modulo the root modulus. Transports the conductor factor to the pool. |
| `residueQuadratic_nat` (private) | For a unit represented by $n$, the finite quadratic character at $q$ is $\operatorname{Jacobi}(n,q)$ in $O$. Evaluates the detecting and extraction factors. |
| `legendreUnit_nat` (private) | On `PhaseData.natUnit q n h`, the local weight's `legendreUnit` has value $\operatorname{Jacobi}(n,q)$ in $O$. Identifies that value with the finite residue factor. |
| `residueAlpha_nat` | On a residue unit represented by $n$, `residueAlpha` equals `localAlpha` on `PhaseData.natUnit q n h`. This identifies the characters used by the actual local weights with the old character's residue factors. |
| `dvd_product_of_extraction` (private) | $q\mid m$ implies $q\mid 2mN\ell_0$. Identifies the extraction indices within the exceptional set. |
| `extraction_prod` (private) | For odd $n$, squarefree $m\equiv3\pmod4$, the product of the extraction Jacobi factors is $\operatorname{Jacobi}(-m,n)$ in $O$. |
| `genus_sq` (private) | If `A.Away n`, the genus factor $\operatorname{Jacobi}(-m,n)$ squares to one in $O$. Supplies cancellation and the order bound. |
| `etaSource_eq` | For squarefree $m\equiv3\pmod4$ with the specified disjoint prime sets, `etaSource C hn n = A.eta m n` for every $n$. This is the characteristic-zero comparison used for `Lift.phase`. |
| `eta_order_of_away` | If `A.Away n`, then `A.eta m n ^ (2 ^ (A.exponent + 1)) = 1`. Supplies the stage and pool order bounds. |
| `residueModuli_dvd` | If $4,m,\ell_0$ and every prime dividing $N$ divide a level, all the specified residue moduli divide it. Supplies `hc` to the old character and its pullback. |
| `representative_away` (private) | If those residue moduli divide $D$, the canonical representative of each unit belongs to `A.Away`. |
| `poolPhase_eval` | `(poolPhase C hn … u : O) = A.eta m (representative u)`. Together with `etaSource_eq` this supplies `η_eval` for the actual lift. |
| `poolPhase_order` | For each common unit $u$ there is $e$ with `(poolPhase C hn … u : O) ^ (2 ^ e) = 1`. Supplies `η_order` to the diamonds. |
| `actualEta_reduce` | `stageReduction O M (etaSource C hn n) = (actualLevelStage …).η n`. Supplies the actual lift's `phase` field. |
| `actualLift_order` | For `(actualLevelStage …).Good p`, there is $e$ with `E.η p ^ (2 ^ e) = 1`. On a typed good domain use the existing inclusion into the stage goods, as in `O12Theta.thetaData`. |
| `extractionNonzero` (private) | `DiscriminantData m N ℓ₀` gives `NeZero m` from $m\equiv3\pmod4$. Supplies the instance for the determinant character. |
| `actual_hchar` | `actualOldCharacter ….comp (ZMod.unitsMap Dₗ.old_dvd) = (Units.map κ).comp (bCharacter actualDiamonds ∅)`. This is precisely `hchar`; the proof calls `oldCharacter_comp_eq_bCharacter_of_phase`. |
| `actualOldStageLaw` | The original `StageGrid E a step` and `RelativeFiniteAction` for the specified weight and old character imply `OldStageLaw κ Dₗ actualDiamonds`; `hchar` is supplied by `actual_hchar`. |

## Remaining inputs and owners

| Boundary | Exact input and manuscript location | Owner |
| --- | --- | --- |
| Actual local weights | `0 < N`, `Fact ℓ₀.Prime`, `ℓ₀ % 4 = 3`, `N.Coprime ℓ₀`, and `DiscriminantData m N ℓ₀`: squarefree $m$, $m\equiv3\pmod4$, $-m\equiv1\pmod8$, $(-m/q)=1$ at odd $q\mid N$, and $(-m/\ell_0)=-1$. The function `w : ℕ → ℤˣ` supplies the signs $w_{q^{v_q(N)}}$ at the level primes. Tex 8207–8230, 8431–8438, 8499–8534, 8579–8591. | ELLIOT input: the fixed curve, discriminant and detector. |
| Same stage | `G : PM.Geometry K (levelRing h hN) N Ebar ap`, `d : PM.Evaluation K Ebar M`, and `L : ℕ`; the usual field, algebra, decidable equality, separable closure and ellipticity instances of the existing constructor. The proof works at every $M$; the manuscript takes $M\ge2$. Tex 8410–8415, 8431–8450, 8476–8494, 8600–8621. | Existing PM geometry and evaluation handoff and ELLIOT detector input. |
| Coefficient comparison | An existing `Field F`, `Algebra O F` and `κ : F →+* ℂ` if using a pool coefficient extension. The canonical character field and its inclusion are available from the chosen local data. Tex 8567–8570, 9649–9652. | ELLIOT choice of the common coefficient field. |
| Old and common levels | Existing `P : Window T.Good S W` and `Dₗ : LevelSetup P avoid D`, with `NeZero D`: the pool is of size at most $W$, its primes are type good and stage good, $4\mid D_0$, $D=D_0\prod_{p\in P.\mathrm{pool}}p$, typed good primes are coprime to $D_0$, and the pool is in `avoid`. The extra numerical coverage used here is $m\mid D_0$, $\ell_0\mid D_0$, and $q\mid D_0$ for each prime $q\mid N$. Tex 8891–8901, 8925–8926, 8938–8951, 9497–9555, 9706–9710. | ELLIOT choice of testing domain; the old-level realization supplies the depth bounds. |
| Old classical law only | `a : Fin 3 → ℕ`, `∀ i, NeZero (2 * a i)`, `step : ℚ`, and `StageGrid E a step` (nonzero step, positive diagonal, extraction parameter nonzero, the specified diagonal entries of $Q_B/m$, constancy on cosets, weight support on that grid, and integral extracted exponents). Also `RelativeFiniteAction actualOldCharacter (stageGridWeight E (κ.comp (algebraMap O F)) a step)`, the existing word action statement with the same scalar for the reference and the old weight. Tex 8891–8936, 8948–8962, 8970–8985, 8989–9015. | The remaining grid realization is a separate construction for the finitely many class weights: choose a shared rectangular lattice, verify coset constancy and support, and supply the classwise depth. The metaplectic action belongs to the sibling action work. Neither is needed by `actual_hchar`. |

No new hypothesis structure or named proposition is used. The arithmetic
disjointness and divisibilities express which primes can contribute and
where their local characters can be evaluated; they say nothing about
comparisons of characters, the choice of lift or the finite action. The
private helpers' unit and oddness assumptions are proved from the
existing exceptional unit domain before use. There is no new print.

## Known-issues

- The stage's integer phase is an imprimitive zero extension. A definition
  using just the conductor of the simplified product would have a different
  value at some exceptional nonunits and would not prove `Lift.phase` for
  every natural argument. The construction retains the original domain.
- This identifies the phase for the actual `actualPmLocal` data. It does
  not construct a separate fixed-sieved stage or assert that a different
  weight has the same classical transformation law. The inherited
  filtered support issues in `docs/research/rc-theta-close.md` are outside
  the phase comparison. No new manuscript or cited-source error was found
  in this proof.

## Manuscript check

- Tex 8499–8534 — **OK**: the chosen conductor root characters appear with the same scaling and dyadic modulus as in the actual Schwartz weights.
- Tex 8536–8556, 8571–8577 — **OK**: the extraction and detecting factors are the quadratic unit characters at their respective primes.
- Tex 8567–8570, 9649–9652 — **OK**: both sides use the same coefficient place and the same embedding of the chosen pool field.
- Tex 8593–8596, 8903–8906, 8932–8936, 9012–9015 — **OK**: the positive integer argument is the lower-right entry, so the local factors enter without inversion. The action giving this convention is a separate input of the classical law.
- Tex 8891–8901, 8907–8923, 8978–8985 — **OK**: the extracted character uses the determinant symbol, including its dyadic term; the quotient by the stage phase is the sign $(-1/d)$. The proof reuses the existing character calculation.
- Tex 8536–8549, 8571–8577, 8982–8985 — **gap filled**: the extraction product equals the genus sign on odd units and cancels it; the detecting sign remains in the lift.
- Tex 8925–8926, 8938–8951 — **unverified**: only the numerical containment of the needed residue moduli is used; the actual analytic depth bounds remain with the old-level realization.
- Tex 9083–9089 — **gap filled**: equality in the coefficient ring proves the required reduction at the full finite precision on the same stage.
- Tex 9491–9496, 9497–9555, 9647–9662 — **OK**: the fixed block has no moving-prime twist and has the old character in the weight-two realization.
- Tex 9696–9698, 9706–9710 — **gap filled**: the full phase has two-power order and is carried unchanged through the common pool.

## Verification

The three files compiled individually with serial `lake env lean -j1`.
All 19 `#print axioms` audits, including the private helpers, report only
subsets of `propext`, `Classical.choice`, and `Quot.sound`. No axioms or
placeholders were added.
