# ht-bypass: the field `eigenformHTNew`, its one use, and why abelian-variety fields cannot replace it

Task ht-bypass, 2026-11-15. Base 9a100aa7 (leaf-fold22, `frozenTarget` over `OpenResearchLeaves21`). Lean:
`scratch/ht-bypass/HTBypass.lean` and the contribution file `ZInQKernel/Contrib/OneProof/EigenformHTWeak.lean`
(same content). Log: `scratch/ht-bypass/log.md`. Nothing else under `ZInQKernel/` was edited. This is model work
with no human review.

Marks: **VERIFIED** = compiled, or read in a file on this host. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (there is no
network on this host).

## 1. Verdict

**The field cannot be removed with the abelian-variety fields; the route uses it at one very special instance, and
the weakest form it needs is stated and checked in Lean.** No statement was changed. The field is not false, vacuous
or inert (§4).

- **One use (VERIFIED).** `eigenformHTNew` feeds the old field `r13 : HDec.PkgI4.EigenformHT` (TailX.lean l.205), and
  `r13` has one consumer: `G0Galois.g8_g12_of_leaves3` → `g8_g12` → `g12` → the glue `G12Weight`, proved by
  `g12Weight_of_senTwist` (= `g12Weight_of`, TailB.lean l.4998). There it is applied once, **at `ℓ = 5`**, to the
  semisimple `ρ_g` of the eigenform `g` that Pan∘Berger (`r11r12`) attaches, up to a twist `ψ`, to G8's
  `r₅ ⊂ ℚ̄₅ ⊗ V₅(A)` (`A` the QM abelian surface over `L'`). It is used only in the branch `k ≥ 2`, to show `k = 2`.
- **Only weight `k ≥ 3` is used (VERIFIED, compiled).** At `k = 2` the conclusion of `G12Weight`,
  `∃ n, {n, n + 1 − k} = {0, −1}`, holds with `n = 0`, so nothing is needed. The field serves only to **exclude
  eigenforms of weight `≥ 3`**: if `g` had weight `k ≥ 3`, the Hodge–Tate weights of `ψ ⊗ ρ_g` would be
  `{s, s + 1 − k}`, which cannot equal `r₅`'s `{0, −1}`.
- **Weakest needed form.** `EigenformHTNew5Ge3` (§2): the field at `ℓ = 5` and `k ≥ 3` (all levels, including
  `5 ∣ N`). The consumers `G12Weight`, `g12`, `g8_g12` are re-proved in Lean with it (`G12WeightWeak`,
  `g12WeightWeak_of_senTwist`, `g12Weak`, `g8_g12Weak`), and the field implies it (`eigenformHTNew5Ge3_of_field`).
- **Bypass via the abelian-variety fields fails (SPECULATIVE judgement with the argument in §3).** The abelian-variety
  fields (Faltings `r9a`/`r9b`, the de Rham comparison `hodgeTateDecompAbVar` + `deRhamH1AbVarT` (ex-`r10`), Néron–Ogg–
  Shafarevich `r7a`, Raynaud `r6`, Eichler–Shimura `r16`) can at most give the Hodge–Tate weights of `ρ_f` for
  **weight-2** newforms (`ρ_f` sits in `V_ℓ(A_f)`, `A_f` a quotient of `J₁(N)`). The route never uses weight 2. For
  `k ≥ 3`, `ρ_g` occurs in no Tate module of an abelian variety, and the data the AV side does control
  (determinants, Weil/Ramanujan absolute values, Newton polygons at `p ≠ 5`) are consistent with every `k`.
- **Counts.** Unchanged (GLUE stays GLUE). `EigenformHTNew5Ge3` is not a printed-form leaf, for the same reason as the
  field: Kato's `V_{F_λ}(f)` (or Saito's/Scholl's realization) is not definable in Mathlib. A fold to the weak form
  cannot be done by `autofold.py` (it needs a proof of the field's exact type); it needs a bypass fold through
  `g8_g12_of_leaves3` (§5). `scratch/ht-bypass/autofold.json` records that no autofold applies.

## 2. The weakest form and the Lean

`ZInQ.Contrib.HodgeSplit.HTBypass` (pkg-I4's `G9` constants, as the field):

```lean
def EigenformHTNew5Ge3 : Prop :=
  ∀ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl 5) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : CF N k) (ρ : GaloisRep 5 2),
    0 < N → 3 ≤ k → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → ρ.HasHTWeightsAtSelf 5 {0, 1 - k}
```

| theorem | statement | status |
|---|---|---|
| `eigenformHTNewCopy_eq` | the verbatim copy is the chain's `EigenformHTNew` (`rfl`) | VERIFIED |
| `eigenformHTNew5Ge3_of_field` | `EigenformHTNew → EigenformHTNew5Ge3` | VERIFIED |
| `eigenformHT5Ge3_of_new` | newform case → all normalized eigenforms (`ℓ = 5`, `k ≥ 3`), from I4-L5, R14, `AttachedConj`, `HTConj` | VERIFIED |
| `eigenformHT5Ge3_of_ds` | the same from `EigenformHTNew5Ge3`, `DSThm965`, `DSThm966` only (the inputs TailX uses for `r13`) | VERIFIED |
| `G0Galois.eigenformHT5Ge3Chain_of` | transport to the chain's constants | VERIFIED |
| `G0Galois.g12Weight_of_weak` | `G12WeightWeak → G12Weight` | VERIFIED |
| `G0Galois.g12WeightWeak_of_senTwist` | `G12WeightWeak` from `SenTwist`, `FiniteImageHT` (`k = 1`: Deligne–Serre; `k = 2`: `n = 0`; `k ≥ 3`: the weak form) | VERIFIED |
| `G0Galois.g12Weak`, `G0Galois.g8_g12Weak` | `g12`, `g8_g12` with `EigenformHT5Ge3Chain` and `G12WeightWeak` | VERIFIED |

Compile outcomes are in §6.

**Printed source of the weak form** (from `docs/research/locators.md` row R13, read by the locator audit): Kato,
Astérisque 295 (2004), §§9.2-9.4, (9.2.2), pp. 187-188 (de Rham, every level, newforms; cohomological
normalization, to be dualized); alternatives Saito, Invent. Math. 129 (1997) (UNVERIFIED there), Faltings,
Math. Ann. 278 (1987) (level `ℓ ∣ N` UNVERIFIED), Scholl 1990 with Scholze 2013. The weak form is that theorem at
`p = 5`, `k ≥ 3`, transported to every semisimple `ρ` with the same Frobenius traces (Chebotarev and Brauer–Nesbitt,
proved: `attachedConj_proof`) and dualized (c-to-printed2's `htDual_proof`). **Rating: not printed form**: the
printed object is not definable; c-to-printed2's existential `KatoRealization` / `KatoRealizationCohSS` restricted
to `ℓ = 5`, `k ≥ 3` is the closest printed-form substitute (a consequence, GLUE (c) under the strict reading).

## 3. Why the abelian-variety fields cannot give it

The task's suggestion: "for the elliptic-curve instances, Hodge–Tate weights of `V_ℓ(E)` may follow from the
abelian-variety fields". The instances of the route are not elliptic-curve instances: `g` is whatever eigenform Pan's
theorem returns for `r₅`, of a priori unknown level and weight, and the field is needed exactly to show its weight is
not `≥ 3`.

1. **Weight 2 is unused.** At `k = 2` the consumer's conclusion is trivial (VERIFIED: `g12WeightWeak_of`, branch
   `k = 2`, is `⟨0, by norm_num⟩`). So the part of the field that `r16` + the de Rham comparison could plausibly
   prove (`ρ_f ⊂ ℚ̄_ℓ ⊗ V_ℓ(A_f)`, Hodge–Tate weights `{0, −1}` of `V_ℓ(A_f)`) contributes nothing. (Proving even
   that part would need: base change of `A_f` to `ℚ_ℓ` and of its Tate module, the decomposition of `ℚ̄_ℓ ⊗ V_ℓ(A_f)`
   into `K_f`-eigencomponents, exactness of Hodge–Tate multiplicities on Hodge–Tate representations, and a determinant
   argument to split `{0,−1}` among the components: SPECULATIVE estimate, weeks of glue.)
2. **The AV side does not see `k` (SPECULATIVE judgement, elementary computation).** Suppose `r₅ ≅ ψ ⊗ ρ_g` with `g`
   of weight `k`. For `p` split in `L'`, `p ∤ 5N`: `det r₅(Frob_p) = ±p` (the characteristic polynomial of `r₅(Frob_p)`
   squares to that of `V₅(A)`, which has integer coefficients and constant term `p²`), `det ρ_g(Frob_p) = ε(p)p^{k−1}`
   (R14's determinant clause), hence `ψ(Frob_p)² = ±ε(p)⁻¹p^{2−k}`: `ψ² = (finite) · χ_cyc^{2−k}`. Then
   - complex absolute values: `|eigenvalues of r₅(Frob_p)| = p^{1/2}` (Weil) and `|eigenvalues of ρ_g(Frob_p)| =
     p^{(k−1)/2}` (Deligne) give `|ψ(Frob_p)| = p^{(2−k)/2}`, consistent with the above for every `k`;
   - `p`-adic valuations at `p`: ordinary or supersingular reduction of `A` gives valuations `{0,1}` or
     `{1/2,1/2}` for `r₅`, and `ρ_g`'s are then `{(k−2)/2, k/2}` or `{(k−1)/2, (k−1)/2}`, consistent with
     `v(det ρ_g) = k − 1`;
   - Hodge–Tate/Sen weights: `det` gives the **sum** of `ρ_g`'s Sen weights (`1 − k`, after the shift by `ψ`'s Sen
     weight `(k − 2)/2`), never the **difference**. The difference (`k − 1`, versus `1` for `r₅`) is the only invariant
     here that separates `k = 2` from `k ≥ 3`, and it is the content of Kato's theorem for weight `k`.
   For `k ≥ 3`, `ρ_g` is not a constituent of `V_ℓ` of any abelian variety (its Hodge–Tate weights `{0, 1 − k}` are
   not in `{0, −1}`; STANDARD), so no AV field speaks about it.
3. **A different route avoids it, at a larger cost.** ser-ell's route 1 (Serre's conjecture, strong form: Khare–
   Wintenberger with Kisin 2009; Raynaud's inertia exponents; Serre's weight recipe; `docs/research/ser-ell.md`)
   produces a **weight-2** newform directly and so needs neither Pan∘Berger (`r11r12`) nor `eigenformHTNew`. It
   restructures G8-G12 (large `ℓ`, pigeonhole over newforms) and its three primary statements are UNCHECKED there.
   Not attempted here.

## 4. Not false, vacuous or inert (SPECULATIVE, read from the definitions)

- `HasHTWeightsAtSelf` asks for a model over a finite `E ⊆ ℚ̄_ℓ` with `htMult` equal to the counts; a continuous
  `ρ|_{G_{ℚ_ℓ}}` lands in some `GL₂(E)` (Baire; STANDARD), so the conclusion is the genuine Hodge–Tate statement.
- The hypotheses are satisfiable (every newform of weight `≥ 2` with its `ℓ`-adic representation, Deligne; STANDARD),
  and the convention matches the AV side: `{0, 1 − k}` is `{0, −1}` at `k = 2`, the weights of `V_ℓ` of an elliptic
  curve in the Tate normalization (`DeRhamComparison`).
- It is applied at a non-vacuous instance (`ℓ = 5`, Pan's `g`, any level).

## 5. What a fold would do

`autofold.py` fills a discharged field with a proof of its exact type, so it cannot replace `eigenformHTNew` by the
weaker `EigenformHTNew5Ge3`. The field's consumer is a theorem (`g8_g12_of_leaves3`, inside
`gluePieces_of_open4`'s `afterG7_of3 …` argument, TailK l.322), not a field, so the bypass of
`oneproof-fold-weaker-leaf-bypass` would have to rebuild `GluePieces` from the newest bundles with `g8_g12Weak` in
place of `g8_g12`. Since the weak form is still GLUE and not printed, the GLUE count would not change; the only gain is
a smaller open statement (`ℓ = 5`, `k ≥ 3`). Recommendation: keep the field; record in OPEN.md that the route uses
only `ℓ = 5`, `k ≥ 3`, so a contributor may prove (or cite) just that instance; this file's `g8_g12Weak` is ready if a
later fold wants it.

## 6. Compile log

See `scratch/ht-bypass/log.md`.
