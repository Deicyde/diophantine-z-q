# rc-appF-theta: Appendix F's weighted ternary theta form at one stage, as the source for Theorem 5.3's odd side

## Main result (a scoped stop)

**Proved, with no sorry and no new axiom:** take any record `ThetaStage R` of the objects in (O.1)–(O.4) at one actual stage. Its
phase-removed coefficients `aθ n = H_M(m n)` satisfy the tree's `Odd.SourceHyp T δ η Good a_p aθ`. For `R = ZMod (2^M)` this is
the tree's `Odd.OddStageSource M δ η Good a_p aθ`, which `Odd.O9_odd_stage` and `Odd.O11_odd_stage` consume. Two inputs are
taken as hypotheses:

- `a_q ≡ q + 1 (mod 4)`. This is already proved for the actual curve as `GlueSweep.Odd.ap_mod_four_curve`.
- App G's depth inequality. It is taken in the tree's own shape, the field `SourceHyp.depth`.

The recurrence (O.6) is proved at every good prime by Elliot's Brandt-matrix computation (tex 8961–9100). It is built from:

- the local line counts, proved from scratch over `𝔽_p` and `ℤ`;
- the double count over the `p + 1` neighbours of one class;
- self-adjointness with the integer masses `c₀/|R_z^×|`.

Working with integer masses removes the field division that the tree's `brandt_adjoint` needs, so the proof runs modulo `2^M`.

**What is missing (the scoped stop).** Nobody has yet constructed a `ThetaStage` from `(E, ℓ₀, M, L, λ_M)`. That needs:

- the definite quaternion algebra together with its Eichler order of level `N`;
- the finite adelic class set `B^×\B̂^×/R̂^×`, with the local identification `R_p ≅ M₂(ℤ_p)` at split `p`;
- the ternary theta lattices with the local weights (O.3);
- supersingular reduction `π_{ℓ₀}` on `X₀(N)` over `𝔽_{ℓ₀²}`, with its Hecke compatibility.

None of this is in Mathlib. Size and the smallest faithful statement are below. The record's fields are jointly satisfiable:
`trivialStage` builds one, relative to the Voight leaf, but it is a consistency check only and its `aθ` is `0`.

**Item 4 of the brief (transformation law and holomorphy, tex 8623–9037).** I did not formalize this part, because no consumer
needs it:

- `OddStageSource` (= `SourceHyp`) has the fields `prime`, `odd`, `ap_mod`, `recur`, `zero`, `depth`, `mul`, `one`. All of
  them concern coefficients.
- `ThetaComparison` is a congruence between coefficients.

The only consequence of the Weil calculus that a consumer reads is `ψ/η = χ_{−1}`. That is already proved as
`Odd.psi_div_eta`, and it enters here as `ε = (−1/p)` in `ThetaStage.recAt`.

## New files

All new files are under `ZInQKernel/Contrib/OneProof/RC/AppF/`. Each compiles with `lake env lean`. Axiom output is in
`scratch/rc-appF-theta/axioms.out`: every theorem uses only `propext`, `Classical.choice` and `Quot.sound`, or a subset of
them.

| file | content |
|---|---|
| `Lines.lean` | local counts at a good prime (tex 9039–9058) |
| `Brandt.lean` | `PFrame` (one class at `p`), neighbour identity, Brandt transfer, Brandt identity (tex 9059–9082) |
| `Prints.lean` | printed-form leaf `VoightMainThm1461` (tex 8462) |
| `Stage.lean` | `ThetaStage`, `H` (O.4), `aθ`, (O.6), `SourceHyp`, `OddStageSource` |
| `NonVacuity.lean` | `trivialStage`: the fields are consistent |

## New theorems and what they supply

Coordinates: `y = (a b; c −a) ∈ 𝔰𝔩₂`, so `Q_B(y) = −a² − bc`. Lines of `𝔽_p²` are written `Option (ZMod p)`.
`MemNbr p k (a,b,c) L` means `y/p^k ∈ End(Λ_L)`, and `count p k (a,b,c)` is the number of such `L`.

- `count0_primitive` (tex 9041–9043): for `p` odd and `ȳ ≠ 0`, `count p 0 (a,b,c) = 1 + (−Q_B(y)/p)`. This includes the
  nilpotent case.
- `count0_pdiv` (tex 9043–9044): for `y ∈ pR_p`, `count p 0 = p + 1`.
- `count1_primitive` (tex 9045–9054): for primitive `y` with `p² ∣ Q_B(y)`, `count p 1 = 1`.
- `memNbr_two_pdiv` (tex 9045): `y/p² ∈ End(Λ_L)` forces `y ∈ pR_p`. So a neighbour's vectors lie in `p⁻¹R_p⁰`.
- `memNbr_one_scale`, `memNbr_congr`: `(py)/p = y`, and membership depends only on `y mod p²`.
- `memNbr_zero_iff_some`, `memNbr_zero_iff_none`, `card_roots_quadratic`: these are the supporting lemmas.
- `PFrame.neighbor_identity` (tex 9059–9066): for one class with `F(px) = s F(x)` and `s s⁻¹ = 1`,
  `∑_L s⁻¹ ∑_{y ∈ vecs(p²n), y/p ∈ R_L} F y = s⁻¹θ(p²n) + (−n/p)θ(n) + p s θ(n/p²)`.
- `mass_adjoint` (tex 9069–9071): `N_ij w_j = N_ji w_i` together with `w ∣ c₀` gives `(c₀/w_i)N_ij = (c₀/w_j)N_ji`.
- `brandt_transfer` (tex 9067–9075; step-map gap F-a): if `c_iN_ij = c_jN_ji` and `∑_L P(nb j L) = a_p P(j)`, then
  `∑_i c_iP_i ∑_L Θ(nb i L) = a_p ∑_j c_jP_jΘ_j`. It holds over any commutative ring.
- `brandt_identity`: `H(p²n) + s(−n/p)H(n) + ps²H(n/p²) = sχ_p a_p H(n)` for `H = ∑ c_zP_zΘ_z`.
- `ThetaStage.brandt` (tex 9076–9082): the same identity for the stage's `H_M`.
- `ThetaStage.recAt` ((O.6), tex 9083–9093): `RecAt p (η p) (−1/p) a_p aθ`. This supplies `SourceHyp.recur`.
- `ThetaStage.aθ_zero` (tex 9092): `aθ 0 = 0`. This supplies `SourceHyp.zero`.
- `ThetaStage.sourceHyp`: `SourceHyp T δ S.η S.Good S.ap S.aθ`.
  - `mul` and `one` come from `η = η_Bχ_{h_*}` (fields).
  - `prime` and `odd` come from `Good`.
  - `ap_mod` and `depth` are taken as hypotheses.
- `ThetaStage.oddStageSource`: `Odd.OddStageSource M δ S.η S.Good S.ap S.aθ` over `ZMod (2^M)`. This is the input to
  `Odd.O9_odd_stage` and `Odd.O11_odd_stage`.
- `trivialStage`: a `ThetaStage` exists, relative to `VoightMainThm1461` (consistency only).

**Definitions.**

- `ThetaStage.H k = ∑_z (c₀/w_z) P(z) χ_{h_*}(Nrd z) θ_z(k)`. This is (O.4) as a finite sum, with integer masses.
- `ThetaStage.aθ n = H (m n)`.
- `VoightMainThm1461 : Prop` is a PRINT and is not proved.

### What the `ThetaStage` fields encode

The record's fields fall into three kinds.

**1. Definitions of the construction.** These are the class set `X`, `w z = |R_z^×|`, `P`, `χN`, `θ`, the neighbour map `nb`,
the `p`-frames (`PFrame`) and `frame_theta`.

`w_dvd : w z ∣ c₀` is a field because `R_z` is not constructed. The tree proves it for `R_z^× ⊂ GL₄(ℤ)` as
`Odd.card_dvd_c0_of_basis`.

**2. Facts that Elliot uses without a print.**

- `hecke`: `∑_L P(nb z L) = a_p P(z)` modulo `2^M` (tex 8476–8494). This is the standard Eichler–Shimura/Brandt compatibility,
  K2 of the step map.
- `adjoint`: `N_ij w_j = N_ji w_i` (tex 9069–9071, "counting actual isogenies and dualizing").
- `frame_nbr`: a neighbour's theta coefficients are the `y/p`-sum with weight `s⁻¹F(y)`, and a neighbour changes the norm
  character by `χ_{h_*}(p)` (tex 9045–9076).
- `frame_scale`: scaling by `p` at the other places multiplies the weight by `s` (tex 9059).
- `theta_zero`: the local support at `p ∣ m` kills `x = 0` (tex 9092).

**3. The ramification of `B`.** This is the field `ram`, and its existence is the Voight leaf.

### Smallest faithful statement of what is missing, and its size

`∃ S : ThetaStage (𝒪/2^M𝒪)` such that:

- `S.ℓ₀ = ℓ₀`, `S.m = |h_*|`, `S.ap = a_·(E)`, and `S.Good` is the complement of the full support;
- `S.P z = λ_M(Lπ_{ℓ₀}(z))`, for the stage of `ex:app-detector`.

The second condition is what ties `aθ` to (O.7) and makes it non-trivial. `OddStageSource` alone is satisfied by `a = 0`.

Realizing this needs quaternion orders and Eichler orders over `ℤ`, and finiteness of the adelic class set. It also needs the
local splitting and the neighbour lattices. All of that is classical but large; I estimate several thousand lines. The
supersingular reduction of `X₀(N)` with its Hecke action is much larger. Mathlib has no modular curves over `𝔽_ℓ`.

Once a stage exists, `ThetaStage.oddStageSource` gives `OddStageSource` at once, and `O9_odd_stage` / `O11_odd_stage` follow.
The same `H` feeds `ThetaComparison`, which stays with the cloud agent's RC/Visibility lane. The interface there is:
`ThetaComparison`'s `aθ θ D` is an integer lift of `S_θ.aθ D`.

## Known issues

- **K1 (`ZMod (2^M)` against `𝒪/2^M𝒪`).** `RC/Odd/Statements.lean` fixes `OddStageSource` over `ZMod (2^M)`. Elliot's
  coefficients live in `𝒪/2^M𝒪`, where `𝒪` is generated by the root-character values `α_p` at `p ∣ N` (tex 8565–8569).
  - When some `p^e ‖ N` has `p ≡ 1 (mod 4)` and (O.3) requires `α_p(−1) = −1`, `α_p` has order at least 4 and takes non-real
    values, so `𝒪 ⊋ ℤ₂`. Then `s = η_B(p)` and `η` do not lie in `ℤ/2^M`.
  - `ThetaStage.sourceHyp` is generic over `R`, so it applies with `R = 𝒪/2^M𝒪`. The specialization `oddStageSource` applies
    only when every character value is `±1`.
  - `SourceHyp`, `O9` and `O11_theta` are already generic over `R`. Recommendation: generalize `OddStageSource` to a
    coefficient ring `R`. This is a modelling restriction in the tree, not a manuscript error.
- **K2 (the depth input).** The depth inequality is taken in `SourceHyp.depth`'s shape:
  `∀ n, 2^{min T (δ + ω(n))} ∣ aθ n`. This is the tree's packaging of App G's stage choice (tex 10210–10232).
  - App G's proved node `AppGEndpoints.OddMinimumF6` gives (F.6) only at squarefree admissible visible `D` with `ω(D) ≤ W`, on
    an ultrafilter-large set of stages. Together with (F.5) and `M > T + δ_o`, this is the stage-choice paragraph.
  - The glue from `OddMinimumF6` (and (F.5)) to `SourceHyp.depth` at one stage is not in the tree. It needs two more steps:
    - extension from squarefree to all indices, by the shell formulas `Odd.rec_even` and `Odd.rec_odd` at good primes;
    - treatment of indices at support primes, which vanish by the sieve.

    I estimate it as small.
- **K3 (`OddStageSource` is satisfiable by `0`).** The recurrence, zero and depth fields hold for `a = 0`. Non-vacuity of the odd
  source comes from (O.7) at the witness `D_w` (`Odd.witness_vZ`), which is outside this brief.
- **K4 (prints).**
  - Voight Main Thm 14.6.1 is stated as Elliot uses it, at `Σ = {ℓ₀, ∞}`. Ramification is expressed as anisotropy of the
    reduced norm form, since Mathlib has no Hilbert symbol. Locators are UNVERIFIED (no network).
  - Jetchev–Kane §§1.1–1.2 and 2.5 and Weil (Acta 111) are not used by any consumer here, so I added no leaf for them.
- **K5 (`frame_nbr` merges two facts).** The neighbour's theta lattice and the norm-character change `χ_{h_*}(p)` are one field.
  This is because only the product `χ_{h_*}(Nrd z) θ_z` is independent of the representative of the class (tex 8612–8616).

## Manuscript check

Verdicts: OK (right as written, and formalized or relied on), gap filled, error, unverified.

| tex | step | verdict |
|---|---|---|
| 8462–8463 | `B` ramified exactly at `ℓ₀, ∞` (Voight 14.6.1) | unverified: printed-form leaf, locator UNVERIFIED |
| 8463–8474 | Eichler order of level `N`; class set `X`; `R_z^×` as automorphism groups (Jetchev–Kane) | unverified: the missing theory; abstract finite type |
| 8476–8494 | `P_M` has `T_p`-eigenvalue `a_p` modulo `2^M` | unverified: no print; field `hecke` (step-map K2) |
| 8495–8597 | local weights (O.3); only the scaling multiplier is used here | unverified: field `frame_scale`; local pieces proved in the tree (`ThetaLocal`) |
| 8598–8611 | `c₀ = |GL₄(𝔽₃)|`; `|R_z^×| ∣ c₀` | OK: `Odd.card_GL4_ZMod3`, `Odd.card_dvd_c0_of_basis` (tree); field `w_dvd` here |
| 8600–8604 | (O.4) as a finite sum | OK: `ThetaStage.H`, with integer masses `c₀/w_z` |
| 8612–8621 | coefficients in `𝒪`; no precision loss from automorphism denominators | OK: `H` is an integer combination, defined in `R` without division |
| 9039–9043 | `1 + (−n/p)` preserved lines, nilpotent case included | OK: `count0_primitive` |
| 9043–9044 | `x ∈ pR_p⁰`: all `p + 1` lines, excess `p` | OK: `count0_pdiv` |
| 9045 | a nonintegral vector of a neighbour lies in `p⁻¹R_p⁰` | OK: `memNbr_two_pdiv` |
| 9046–9054 | `y/p` lies in exactly one neighbour, the kernel line | OK: `count1_primitive`. The tex leaves implicit that `ȳ` is nilpotent (trace 0 and `det ȳ = 0` give `ȳ² = 0`); the proof covers it |
| 9055–9058 | integral and nonintegral parts exhaust the sum with no genericity assumption | OK: `PFrame.sum_nbrSum` plus the split in `neighbor_identity` |
| 9059–9066 | primitive part `s⁻¹H(p²n) − H(n)`; integral part `(1 + (−n/p))H(n) + psH(n/p²)` | OK: `PFrame.neighbor_identity` (per class) |
| 9067–9071 | self-adjointness `N_ij w_j = N_ji w_i` | unverified: Elliot's one-line argument; field `adjoint` |
| 9071–9075 | moving the neighbour operator onto `P_M`; norm character changes by `χ_{h_*}(p)` | gap filled: written out (F-a) as `brandt_transfer` with integer masses; the character change is field `frame_nbr` |
| 9076–9082 | `H(p²n) + s(−n/p)H(n) + ps²H(n/p²) = sχ_{h_*}(p)a_pH(n)` | OK: `ThetaStage.brandt` |
| 9083–9091 | (O.6) with `η = sχ_{h_*}`, `ψ = s(m/p)`, `ψ/η = (−1/p)` | OK: `ThetaStage.recAt` (via `Odd.O6_of_brandt`) |
| 9092–9093 | zero index vanishes by the local support; negative indices vanish | OK: field `theta_zero` (the argument is right: `v_p Q(0) ≠ 1` at `p ∣ m`); `ThetaStage.aθ_zero` |
| 9094–9099 | sieves preserve (O.6) | unverified: not formalized; no consumer here |
| 8408–8429, 8623–9037 | `g_M ∈ M_{3/2}(Γ₀(K), ψ)`, Weil-representation calculus | unverified: not formalized; no consumer of `OddStageSource` or `ThetaComparison` needs it (`psi_div_eta` is in the tree) |
| 10151–10256 | App G depth minimum, used as the `depth` input | unverified here: taken as a hypothesis in `SourceHyp.depth`'s shape; glue from `OddMinimumF6` is missing (K2) |

Counts: OK 12, gap filled 1, error 0, unverified 8.

No error was found, so `.fleet/rc-appF-theta-verdict.md` was not written.
