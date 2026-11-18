# C8: Conrad's Proposition B.3 with the full local Galois action

`conradAppB_of_print` reduces the unchanged C8 input `OpenAddedLeaves28.conradAppB` to one row, `ConradAppBPrint`. Its two conjuncts are the near-one display and the pure Hodge–Tate splitting of Proposition B.3, both for local base `ℚ_p`. The older `ConradIdentityWeight` is proved glue. This is a reduction to the cited print, not a proof of Conrad's results.

## Printed statements and ratings

**VERIFIED (supplied page read):** Brian Conrad, *Lifting global representations with local properties*, author preprint December 11, 2011, App. B pp. 32–33, Proposition B.3 p. 33 (proof pp. 33–34). This is the version at `diophantine_zq.tex`, `conrad-local-characters`, L11046–11049. The p. 32 implication is also recorded in [A011](../theorem-application-audit/evidence/parallel-galois-height-report.md#L102). There was no new PDF read or download.

| Statement | Form and role |
| --- | --- |
| `ConradNearOnePrint` | Direct instance of p. 32 (Hodge–Tate implies locally algebraic) in the form of p. 33's display. The `PureHT` premise is its one-weight case on the underlying `ℚ_p` representation. The product over the **base** embeddings has one factor, so the descended character composed with the arithmetic Artin map is `x ↦ x^(-n)` near 1. |
| `ConradB3Print` | Direct instance of B.3, with its preceding parenthetical that the line labels are the Hodge–Tate weights of the underlying representation. Here `ℚ_p ⊗[ℚ_p] K = K` has one factor, so the rule `w_σ = n_i` gives `w_σ = n` for all coefficient embeddings. The conclusion is the `ℂ_p`-linear, full-group equivariant splitting into `[K:ℚ_p]` copies of `ℂ_p(n)`, in Conrad's sign. |
| `ConradAppBPrint` | The one new row, pairing the preceding direct instances for this one citation. Its printed form is independent of whether the cited author preprint counts as an eligible LEAF. |
| `ConradIdentityWeight`, `ConradAppBConcrete` | GLUE. The former uses just the identity line over its stabilizer; the latter packages it with the near-one result. Both keep their original types. |

**On-the-spot (reading the isotypic lines):** Write `T = ℂ_p ⊗[ℚ_p] V`. The group acts by `g(a ⊗ v) = g(a) ⊗ ψ(g)v`, semilinearly over `ℂ_p` and commuting with the coefficient `K)-action on the second factor. For `kv = σ(k)v` in `T`, semilinearity gives `k·g(v) = (g ∘ σ)(k)g(v)`. Thus the full group permutes the canonical lines of the split coefficient algebra `ℂ_p ⊗ K`; the identity embedding has stabilizer exactly the group fixing `K`. On the other hand the Hodge–Tate splitting is by weight, and the `K)-action preserves each weight summand because it commutes with Galois and with the `ℂ_p)-action. The notation `V_σ = ℂ_p(w_σ)` puts the line in the degree-`w_σ` summand. It does not select a generator or say that every coefficient line is itself a full-group subrepresentation. When every weight is `n`, the whole tensor representation is a sum of identical twists; the existential equivalence in `PureHT` simply expresses this and records no chosen identification of the copies with embeddings.

**On-the-spot (restriction to the identity line):** Evaluate on the identity coefficient factor by the `ℂ_p)-linear map `ev(a ⊗ v) = a·ι(v(0))`. It is nonzero and on `G_K` it satisfies `ev(gx) = ι(ψ(g))·g(ev(x))`. Any basis obtained from the full-group splitting has vectors with action `gx = χ(g)^n x`, so one of them has `d = ev(x) ≠ 0`. The relation `ι(ψ(g))g(d) = χ(g)^n d` gives the old isomorphism of semilinear lines in exactly its scalar form with `c = d⁻¹`. Lean extends the pure-tensor action identities by tensor induction. This uses the same fixing subgroup as the existing descent adapter and avoids a dimension argument in this direction. The unchanged `conradAppB_of_concrete` still handles the numerical multiplicity and coefficient enlargement.

**On-the-spot (arithmetic Artin quotient):** The old `exists_artinLift` is surjectivity of the quotient map at the Artin symbol; the old `artinNearOne_iff` compares neighborhoods with congruences. Neither states the descent of this character. The new `conradAbelianChar_artinLift` applies Tau Ceti's `TopologicalAbelianization.lift_mk` to the continuous character into the Hausdorff abelian group `Kˣ`. The map kills the closure of commutators, so its value at the Artin symbol equals the character on every lift. Conversely use `exists_artinLift` at each point. This is the equivalence `artinNearOnePrint_iff`, with no section of the quotient and with the same near-one filter on both sides; thus the old conclusion expresses exactly the p. 33 display at `L = ℚ_p`.

The Lean row is specialized to finite Galois coefficient fields; this is a restriction of the printed domain. The existing adapter enlarges coefficients to a normal closure in the same algebraic closure while keeping the local base `ℚ_p`. No extra continuity or Hodge–Tate requirement is imposed by the B.3 conjunct beyond continuity of the character and the near-one formula. The latter gives local algebraicity in Definition B.1 via the algebraic power map and the scalar inclusion into the Weil restriction.

## Manuscript check

**VERIFIED (source),** `sec:height`, L755–767: L758–762 uses a de Rham twisting character at five, hence a Hodge–Tate character for this local algebraicity argument. L763–765 needs the exponent matched to its local weight so that removing the corresponding cyclotomic power leaves finite inertia at five. The manuscript needs the common weight at local base `ℚ₅`; it does not need a separate choice of identity coefficient line over `G_K`. The identity-line reading is sufficient after the existing descent but is a Lean intermediate, rather than the statement the manuscript applies. At L755 the cyclotomic weight is −1; Conrad's is +1. In arithmetic normalization on a unit, Tau Ceti's `abelianizedLocalCyclotomicCharacter_artinMap_padic` gives `χ(Art(u)) = u⁻¹`, so the Conrad exponent `n` in `u^(-n)` matches the cyclotomic power `χ^n` and the manuscript weight `-n`. The rest of the finite ray-class argument and weight comparison are unchanged.

## Known issues

There is no recorded source gap or failed application condition at C8 in the supplied read and A011. The coefficient-line notation cannot be read as a separate full-group equivariant isomorphism on each isotypic line for nontrivial `K/ℚ_p`; the full-group splitting and the proved stabilizer restriction resolve that point of interpretation. The exact citation is an unrefereed author preprint; there is no claim of a refereed version and no substitute source.

## Checks and count

**VERIFIED (autofold dry run):** The [spec](../../scratch/conrad-b3-verbatim/autofold.json) removes just `OpenAddedLeaves28.conradAppB`, adds `conradAppBPrint`, and generates `sixContactMin_of_open84`. Main and the kinds table were not edited. Baseline: merged main `c3624d0e3` into `b092da9cc`, merge `bf5bfc05c`.

- H strict LEAF/GLUE on N (cited preprint eligible): **5/27 on 32 → 6/26 on 32**.
- H strict LEAF/GLUE on N (refereeing required): **5/27 on 32 → 5/27 on 32**.

**VERIFIED (Lean contribution):** [ConradB3Verbatim.lean](../../ZInQKernel/Contrib/OneProof/ConradB3Verbatim.lean) compiles without warnings. The [verbatim copies](../../scratch/conrad-b3-verbatim/Original.lean) compile and match the original definitions by `Iff.rfl`. The [axiom output](../../scratch/conrad-b3-verbatim/axioms-out.txt) gives only `propext`, `Classical.choice`, and `Quot.sound`.
