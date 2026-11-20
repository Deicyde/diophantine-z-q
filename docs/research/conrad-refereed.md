# C8: reduce the Conrad row to Serre

**Manuscript normalization issue (tex 765–767).** The comparison gives cyclotomic
power zero only after putting the modular representation in the arithmetic
Frobenius (Tate-module) normalization. Using the geometric normalization of
Pan's output directly gives one extra power of the cyclotomic character at
weight two. This is the ambiguity identified in
[`rv-h-c8.md`](rv-h-c8.md); the proposed local replacement has no dependence on
the choice of normalization for the modular representation.

**Result.** `HDec.G0Galois.C8Conrad.conradAppB_of_refereed : SerreA6Prop6 →
C8Conrad.ConradAppB` reduces both halves of the exact open row to one printed
equivalence. This removes the reliance on Conrad's unrefereed Appendix B from
this route. The row and its consumers use their original types.

Lake built all nine new modules. The focused scanner finds one discharge of
`conradAppB`, with only `SerreA6Prop6` still assumed. The
[results log](../../scratch/conrad-refereed/log.md) contains its output and
the standard-axiom check for all 42 new theorems.

## The one printed input

Serre, *Abelian ℓ-adic representations and elliptic curves*, Addison–Wesley
(1989), Ch. III Appendix A6, Proposition 6, equivalence of (iv) and condition
(ii) of A5, Theorem 2 (III-49–50 and III-44; all locators **UNVERIFIED**).
The theorem reference identifies condition (ii) of the proposition; it is not
a second input. The formulation and the comparison proofs were adapted
from local proof history (`b789c8906`). This contribution takes the input
for an arbitrary character on `G_K` with the printed unit-valued condition,
then proves the specialization to the restricted character. The printed
pages were not independently inspected for this reduction.

[`LocalArtin.SerreA6Prop6`](../../ZInQKernel/Contrib/OneProof/ConradRefereed/LocalArtin.lean)
takes the case where the ground and coefficient fields are the same finite
Galois extension `K` of `ℚ_p`. Let `ρ : G_K → Kˣ` be continuous with values
in the integer units `U_K`. For integers `n_σ` indexed by embeddings
`σ : K ≃ₐ[ℚ_p] K`, the statement is:

- (ii) For each `σ`, `σ ∘ ρ ∼ χ^{n_σ}`. The comparison means there is
  a nonzero `b ∈ ℂ_p` such that
  `g(b) = (σ(ρ(g)))⁻¹ χ(g)^{n_σ} b` for every `g ∈ G_K`.
- (iv) There is an open subgroup `U' ≤ U_K` on which
  `ρ(i_K(u)) · ∏_σ σ⁻¹(u)^{n_σ} = 1`, where evaluation uses the
  descended character on `G_K^{ab}`.

The product is Serre's algebraic factor in this specialization: each norm
`N_{K/σK}` is the identity. The checked Lean statement uses Tau Ceti's actual
arithmetic `artinMap K`, unit filtration at depth zero, and the action on the
tree's `ℂ_p`. In particular, the printed input does not contain the norm down
to `ℚ_p`, the row's multiplicity formula, or a conclusion about `G_{ℚ_p}`.
Those passages are theorems.

For arithmetic reciprocity the tree proves `χ(i_{ℚ_p}(u)) = u⁻¹` on units
(`cyc_of_isArtinLift`), and at the ground field `K` its Artin map
sends a uniformizer to arithmetic Frobenius by
`isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer`. With `wt(χ)=+1`,
weight `n` thus means the near-one formula with exponent `−n` on the unit, precisely
`IsLocallyAlgebraicConrad p ψ n`. The manuscript and `PkgI4.htMult` instead
give `χ` weight `−1`. In that convention the same character has weight
`−n`, and `IsLocallyAlgebraic p ψ (-n)` writes the same formula.
The existing `isLocallyAlgebraic_iff_conrad` and
`htMult_eq_conradHTMult_neg` implement these signs.

## What the base already proves

- Tau Ceti identifies the image of the unit filtration at zero with
  abelianized inertia (`map_artinMap_unitFiltration_zero`); `C8LocAlg`
  supplies `exists_unit_isArtinLift`, `cyc_of_isArtinLift`, and the congruence
  check on `χ` for elements fixing a primitive `p^k`-th root.
- Once the local formula holds, `ψχ^{-n}` is trivial on Artin symbols of
  `1+p^kℤ_p`. The finite quotient
  `(ℤ/p^kℤ)ˣ` bounds the order of its values on inertia by
  `φ(p^k)`. The tree has this calculation for `ψ ∘ decomp` in
  `C8LocAlg.pow_card_eq_one_of_mem_inertia`; the argument is local and is
  the same after removing the indicated cyclotomic power. Finite inertia
  permits an unramified part; it does not imply finite global image of
  a local Galois character. The global ray-class step is already proved
  by `C8CFT.finiteOfLocAlgTrivialQNoRam_of_dicts` and `C8Dicts`.
- `CloudB3W11.axSenTate_proof` and
  `CloudB3W11.tateTwistInvariants_proof` cover the whole `G_K` for
  finite `K/ℚ_p` (Tate, *p-divisible groups*, 1967, §3.3, Theorems 1
  and 2; locators **UNVERIFIED**). The first identifies fixed scalars,
  the second excludes nonzero cyclotomic twist invariants.
  `C8LocAlg.TateTwistInvariantsInertia` is a separate assumption for
  the completion of the maximal unramified extension. Its consumer
  `locAlgExponentEqWeight_of_tateInertia` already assumes both local
  algebraicity and Hodge–Tate; it cannot supply either half of the row.
- For an outright proof, what this route would still need is the
  character period criterion: after twisting by `χ^{-n}), an identity
  period over a finite coefficient extension exists precisely when the
  restricted twist is trivial on an open subgroup of inertia (equivalently
  it has finite inertia image). The forward direction must rule out
  ramified periods for *arbitrary continuous* characters, rather than
  only nonzero powers of `χ`. The reverse direction must construct
  periods for unramified unit-valued characters with possibly infinite
  Frobenius image. The two proved whole-group invariant theorems alone
  do not supply these steps. Developing the ramified period theory and
  constructing the unramified periods is a larger route than using the
  single Serre statement.

## New theorems and what they supply

All comparison proofs below are on the spot, provenance (c), except for
the cited mathematical inputs they invoke. Names are grouped by Lean
module in `ZInQKernel/Contrib/OneProof/ConradRefereed/`.

| Module / theorem | Statement and use |
| --- | --- |
| `Bridges.cp_fixed` | A `G_{ℚ_p}`-fixed `x ∈ ℂ_p` comes from `ℚ_p`; apply Ax–Sen–Tate at the bottom intermediate field. |
| `Bridges.ht_independent` | A finite `ℚ_p`-independent family in a single `htSpace` is `ℂ_p`-independent in the ambient linear map space. Normalize a minimal relation and use fixed scalars. |
| `Bridges.pureHT_of_hasHTWeights` | `HasHTWeights p (charRep ψ) {w} → PureHT p ψ (-w)`. Singleton multiplicity gives enough independent equivariant maps, which give the splitting after tensoring. |
| `Bridges.range_restrictGalois` | The image of `G_K → G_{ℚ_p}` is the fixing subgroup of `K`. |
| `Bridges.exists_artinLift` | Every arithmetic Artin symbol of `x ∈ ℚ_pˣ` has a lift in `G_{ℚ_p}`. |
| `Bridges.artinNearOne_iff` | The formula on a neighbourhood of 1 is equivalent to `IsLocallyAlgebraicConrad p ψ n`, by the congruence neighbourhood basis. |
| `Bridges.charRep_extend` | Extending a character's coefficients from `E` to `K` extends `charRep` by the matrix scalar map. |
| `Bridges.extend_conradLA` | `IsLocallyAlgebraicConrad` at a given exponent is equivalent before and after that coefficient extension. |
| `Bridges.identityLine_mem_Ysp` | A period at the identity embedding of `K` gives the vector with that coordinate in `Ysp`. |
| `Bridges.finiteDimensional_Ysp_charRep` | The space `Ysp` for a character over finite `K` is finite dimensional over `K`. |
| `Bridges.finrank_Ysp_charRep_pos` | A nonzero period vector in `Ysp` implies positive `K`-dimension. |
| `Bridges.conradHTMult_of_identityLine` | An identity period at `n` implies `conradHTMult p (charRep ψ) n = [K:ℚ_p]` for finite Galois coefficients. `Ysp` has dimension one by the existing upper bound, then use the proved invariants and descent comparison. |
| `Bridges.conradAppBQp_of_nearOne` | `ConradNearOne → ConradAppBQp`; enlarge coefficients to the normal closure, then descend the near-one equality. |
| `Bridges.conradPropB3Qp_of_identityWeight` | `ConradIdentityWeight → ConradPropB3Qp`; cancel the positive degree of the coefficient enlargement in the exact multiplicity equality. |
| `AbelianChar.conradAbelianChar_artinLift` | Evaluation of the descended continuous character on an Artin symbol equals evaluation on any lift. |
| `AbelianChar.artinNearOneOnAbelianization_iff` | Near-one equality on the abelianized Artin map is equivalent to equality on all lifts. |
| `LocalArtin.norm_eq` | The local field norm on an embedded finite `K` equals the inherited norm. |
| `LocalArtin.topology_eq` | The finite local field topology on `K` equals the inherited topology. |
| `LocalArtin.range_eq_fixing` | Tau Ceti's absolute Galois extension map has image `K.fixingSubgroup` in the common closure. |
| `LocalArtin.character_norm` | Evaluation of a restricted continuous character on `i_K(u)` equals its downstairs evaluation on `i_{ℚ_p}(N u)`. |
| `LocalArtin.forall_fixing_iff_forall_extend` | A predicate on the restricted action holds for all elements of the fixing subgroup iff it holds after extending each absolute automorphism of `K`. |
| `LocalArtin.normOne_isOpen` | The norm-one units are open in `Kˣ`. |
| `LocalArtin.character_norm_one` | Every value of the continuous local character has norm one, by compactness and the powers of each group element. |
| `LocalArtin.openSubgroup_normOne_iff` | An identity on an open subgroup of the norm-one units is equivalent to an identity on an open subgroup of `Kˣ` all of whose members have norm one. |
| `LocalArtin.normOneUnits_eq_unitFiltration`, `serreUnits_eq_normOne` | Norm-one units agree with depth zero of Tau Ceti's unit filtration; `serreUnits` is that subgroup. |
| `LocalArtin.serreA6NormEquivalence_of_prop6` | `SerreA6Prop6 → SerreA6NormEquivalence`; proves the group, topology, compactness and Artin norm translations. |
| `UnitBall.norm_eq_one_of_norm_sub_one_lt` | `‖x−1‖<1 → ‖x‖=1`. |
| `UnitBall.norm_mul_sub_one_le`, `norm_prod_sub_one_le` | A radius `r≤1` bounds distance to one for a product if it bounds the factors, for two and finitely many factors respectively. |
| `UnitBall.norm_algEquiv_apply` | Coefficient automorphisms preserve the inherited norm. |
| `UnitBall.mem_unitBall`, `isOpen_unitBall` | The subgroup `unitBall` is the strict ball about 1 in `Kˣ`, and is open. |
| `UnitBall.norm_normUnits_sub_one_le` | Near 1 the distance of the norm to 1 is at most the distance of the original unit to 1. |
| `IdentityWeight.identityLine_of_serreTwistAdmissible` | Inverting Serre's identity-embedding period gives the period in `IdentityLine`. |
| `IdentityWeight.conradIdentityWeight_of_serre` | `SerreA6NormEquivalence → ConradIdentityWeight`. Take all `n_σ=n`; the norm turns the near-one formula into (iv), and (ii) gives the identity period. |
| `NearOne.serreTwistAdmissible_of_pureHT` | `PureHT p ψ n` gives (ii) for every coefficient automorphism by tensor evaluation at that embedding. |
| `NearOne.norm_sum_le_of_forall_le'` | A nonnegative bound on the norms of all terms bounds the norm of a finite sum. |
| `NearOne.eq_one_of_pow_eq_one_of_norm_sub_lt` | A `d`-th root of unity at distance less than `‖d‖` from 1 is 1. |
| `NearOne.conradNearOne_of_serre` | `SerreA6NormEquivalence → ConradNearOne`. Restrict (iv) along `ℚ_pˣ → Kˣ`; the error character has `[K:ℚ_p]`-th power 1 near 1, so continuity and the root bound kill it on a smaller neighbourhood. |
| `Reduction.conradAppB_of_refereed` | `SerreA6Prop6 → C8Conrad.ConradAppB`; assemble both directions. |
| `DischargesFocused.frozenTarget` | Focused scanner fixture: `(conradAppB : C8Conrad.ConradAppB) → True`. |

## Remaining inputs

- **Refereed print:** only `LocalArtin.SerreA6Prop6`, subject to review
  of the printed locator and its source classification before folding.
- **GLUE:** none left as hypotheses of the reduction. The original
  preprint-based `conradAppB` remains an open GLUE field in the base
  bundle until the lead folds the new theorem.
- **ELLIOT:** none needed for this local row. In the existing C8 consumer
  `g12DetPZ_of_printed`, the independent R13, R14, G9 and de Rham comparison
  inputs retain their existing classifications. `TwistCharHTWt0` and the
  global inertia dictionaries are already theorems.

## Known issues

- **Tex 765–767:** the modular normalization must be fixed before claiming
  power zero. In the manuscript's weight convention a `χ^m` twist subtracts
  `m` from both weights; from geometric modular weights `{0,k−1}` to
  `{0,−1}` at `k=2` this gives `m=1`. This is separate from the local
  arithmetic Artin sign and does not call for a change to the row.
- **Tex 759:** the manuscript says de Rham for the twist; the existing
  `C8Twist` route supplies Hodge–Tate, which suffices here. The source of
  modular Hodge–Tate weights has to cover the possible level at 5, and
  weight one if that weight is admitted. Those issues belong to the
  existing modular inputs, not the local character reduction.
- The Conrad citation is an author preprint and stays GLUE. No new
  mathematical error in Conrad, Serre, or Tate was established here;
  printed locators are unverified on this checkout.

## Manuscript check

| Tex lines | Verdict | Step |
| --- | --- | --- |
| 755–756 | OK | The manuscript gives the cyclotomic character weight `−1`; the row's Conrad normalization instead gives it `+1`. Both the exponent and the weight change sign. |
| 758–760 | OK | The local input only uses the Hodge–Tate consequence for the twist, already supplied by `C8Twist` from its stated modular inputs. |
| 760–762 | gap filled | Hodge–Tate implies local algebraicity via Serre's forward implication and the proved norm and coefficient bridges. The manuscript's preprint is not a leaf. |
| 762–764 | gap filled | The reverse implication supplies the weight of the indicated cyclotomic power; the arithmetic Artin formula then makes the residual inertia image finite at 5. |
| 764–765 | OK | The global finite character follows in the existing class field theory consumer; outside 5 the other inertia calculation is unchanged. |
| 765–767 | error | The power-zero inference needs the arithmetic modular normalization, which is left implicit. See the qualification above. |

Li's formula and the Fricke-stability step (768–770) are downstream and
are not used in this reduction.
