# Residual bounds for the finite Selmer stages

The source compiles as one file. All 70 new theorems and 11 key definitions have been checked separately; their complete elaborated types and axiom dependencies are in `TheoremStatements.txt`. Every theorem uses only standard axioms: `propext`, `Classical.choice`, and `Quot.sound`. No existing source is changed.

## Objects and hypotheses

The coefficient ring is `Acoef i = (ℤ/2^i)[t]/t^i`, definitionally the same ring as `StageA i`. The statements concern the actual `selCx` complexes of the strict, relaxed, Kummer, and standard old-support data.

The arithmetic hypotheses are explicit:

- `IsTotallyComplex K`;
- finite Selmer support containing every finite place above two;
- `FullTorsion K S W (2^i)` at every coefficient level, or the analogous condition over the smaller coefficient support for inflated coefficients;
- open kernels for the coefficient characters;
- fixed local elliptic curves and equivariant local torsion maps for the Kummer conditions.

No residual-rank bound, bounded Selmer cohomology hypothesis, or constancy of residual local conditions is assumed.

The printed inputs are propositions, not additional axioms: the existing global dimension and local/global finiteness leaves, together with the precisely located local cohomological-dimension specialization.

## The fixed residual representation

`TwoTorsionResidual K S W` is `E(K_S)[2]` with its genuine Galois action, its canonical binary vector-space structure, and its discrete topology. For every positive stage, `stageCoefResidualEquiv` identifies the residue-field tensor of the actual coefficient module with this representation. The scalar character disappears because a unit reduces to one in the field with two elements. The equivalence is equivariant; the corresponding cochain comparisons commute with localization. Inflation from a smaller support preserves this description.

Full two-torsion makes this representation two-dimensional. Rational two-torsion makes its action trivial, but triviality is not needed by the bounds.

## Cohomological range

The Selmer differential acts on `Gⁿ × Uⁿ × Lⁿ⁻¹`. Global and local continuous cohomology vanish below zero and above two. Standard zero and Kummer conditions have terms only in degrees zero and one; the full condition has local cohomological range zero through two; the actual unramified condition is the two-term Frobenius complex.

The two exact sequences of the Selmer cone therefore give residual Selmer cohomology only in degrees zero through three. Thus the producer parameters are exactly `lo = 0`, `hi = 3`.

## Uniform natural-number bounds

For the fixed binary representation, put

- `g(n) = dim Hⁿ(G_{K,S}, M̄)`;
- `l(n) = dim Hⁿ(⊕_{v∈S} C_cont(G_v, M̄))`;
- `Gmax = max_{0≤n≤2} g(n)` and `Lmax = max_{0≤n≤2} l(n)`;
- `P_v = dim (𝔽₂ ⊗_ℤ B_v(K_v))`;
- `L_vmax = max_{0≤n≤2} dim Hⁿ(G_v, M̄)`.

The definitions use finite-set suprema, which are maxima on these nonempty degree intervals. Every reference module is finite, from the printed finiteness statements and Kummer injection.

The supplied bounds are:

- strict and relaxed: `Gmax + 2 * Lmax`;
- Kummer: `Gmax + Lmax + ∑ v, (dim M̄ + P_v)`;
- standard old conditions and unramified new conditions: `Gmax + Lmax + ∑ v, (L_vmax + dim M̄ + P_v)`, with the fixed residual representation inflated from the coefficient support.

These are conservative bounds, not asserted to be the least possible bounds.

The Kummer argument does not assert that arbitrary residual Kummer complexes are identical. The scalar-extended point module surjects onto the first Kummer cohomology quotient. Right exactness identifies residual first cohomology with the residue-field tensor of that quotient. Hence its rank is bounded by the one fixed binary point module. Zeroth residual cohomology is bounded by the residual coefficient rank. This works even when torsion levels, equivariant coefficient maps, or standard condition labels vary with the stage.

## Principal statements

- `strictRelaxed_producerBounds`: one `B : ℕ` supplies both `hbdd` and `hB` for the strict and relaxed actual stage families.
- `kummer_producerBounds`: one `B : ℕ` supplies both hypotheses for the actual Kummer family with fixed local curves and stage-varying torsion levels and coefficient maps.
- `standardOld_producerBounds`: one `B : ℕ` supplies both hypotheses for the actual inflated family, choosing zero, full, or Kummer conditions at the old places and the actual unramified conditions at the new places.

Their complete elaborated statements and axiom dependencies are recorded separately by the verification check.

## Supplying the retained producer

Use `lo = 0` and `hi = 3`. Destructure `strictRelaxed_producerBounds` into its common `B`, strict range proof, relaxed range proof, strict rank proof, and relaxed rank proof; select the pair for the chosen family. Destructure `kummer_producerBounds` or `standardOld_producerBounds` into `B`, the range proof, and the rank proof.

These are the literal `hbdd` and `hB` propositions of `exists_retained_of_stageInputs`, because `StageA i` and `Acoef i` are definitionally equal. The witness `B` is respectively `strictRelaxedRankBound`, `kummerSelmerRankBound`, or `oldSelmerRankBound`, as given above. The independent residual-finiteness input comes from the corresponding existing theorem in `StageResidual`; the other producer inputs are unchanged.

## Printed locators

The source is J. S. Milne, *Arithmetic Duality Theorems*, second edition, 2006, https://www.jmilne.org/math/Books/ADTnot.pdf.

- I, Theorem 4.10(c), printed pages 56–57, PDF pages 64–65: for `r ≥ 3`, global cohomology maps bijectively to the product of real-place cohomology. The product is zero for a totally imaginary field.
- I, Remark 1.12, printed page 24, PDF page 32, with the local class formation of I.1.6(b): “Consequently scdₚ(G) = 2 in examples (1.6a,b,c,d) except when p = 2 and K is a number field having a real prime.” `MilneLocalDimensionTwo` states the finite-discrete-module vanishing specialization for the characteristic-zero completions.

The same remark cautions that a general *strict* cohomological-dimension claim for `G_S` is unproved. No such global claim is used here: global vanishing comes from Theorem 4.10(c).
- I, Theorem 2.1 and Corollary 2.3, printed pages 26–28, PDF pages 34–36: local duality and finiteness for finite coefficients of order prime to the field characteristic. In these characteristic-zero completions the restriction is automatic.
- I, Corollary 4.15, printed page 62, PDF page 70: global cohomology is finite in every degree for finite support and finite coefficients whose order is a unit in the ring of support integers. This is the correct precise locator for the existing global finiteness leaf; Theorem 4.10(a) alone only states finiteness of the relevant kernel groups.

The checked PDF has 2,136,045 bytes and SHA-256 `2c6195ec76a974f3f336c77cb71cc3845b018aad2d43136716b3477a3bc5fb31`.

## Scope and remaining inputs

The printed arithmetic propositions and the usual full-torsion support hypothesis remain explicit caller inputs. The other retained-producer data, including pairing, duality, flatness, and the local split-model comparison, are not constructed here.

The unrestricted `CondAt` interface allows arbitrary complexes. Finiteness of their residual cohomology alone cannot imply either a prescribed cohomological range or a uniform stage-independent rank bound. The old-support theorem consequently constructs the standard zero/full/Kummer conditions explicitly; it does not claim a bound for every arbitrary old condition accepted by the broad finiteness interface.

No existing source is changed, and no integration is performed.
