# dl-system: the abstract Selmer system of Route K and its gluing lemmas

Specification: `docs/research/slot-k.md` §2.1–2.3 (with the referee reports `rv-slot-k-proof.md`
and `rv-slot-k-descent.md`). Lean: namespace `ZInQ.RouteK`, directory `ZInQKernel/RouteK/System/`,
root module `ZInQKernel/RouteK/System.lean`, imported from `ZInQKernel.lean`.

Everything below is proved. There is no `sorry`, no axiom and no `native_decide`. The only finite
check is a kernel `decide` over nine bits, in Lemma 3. No finite-computation hypotheses are
introduced.

## Leaves

| Article (slot-k.md) | Lean name | Module | Status |
| --- | --- | --- | --- |
| §2.1 classes, `λ`, `μ` | `oddClasses`, `lam8`, `mu8`, `Config.lam`, `Config.mu` | `System/Config.lean` | proved |
| §2.1 configuration, reciprocity | `Config` (fields `cls`, `cls_mem`, `bit`, `recip`) | `System/Config.lean` | proved |
| §2.1 product class `c(𝒞)` | `Config.prodClass`, `Config.prodClass_mem` | `System/Config.lean` | proved |
| §2.1 unknowns, first coordinate | `Unknowns`, `Unknowns.first` | `System/Selmer.lean` | proved |
| §2.1 Monsky matrix `K` | `Config.monsky`, `Config.monsky_eq_sum` | `System/Selmer.lean` | proved |
| §2.1 rows `E1`, `E2`, `(R)`, `(D)` | `Config.E1`, `Config.E2`, `twoAdicRows`, `Config.D` | `System/Selmer.lean` | proved |
| §2.1 system `Σ(𝒞)`, solution set | `Config.IsSol` (decidable), `Config.sols` | `System/Selmer.lean` | proved |
| §2.2 Lemma 1 (partner) | `Config.Partner`, `Config.Partner.isSol_iff`, `Config.Partner.solsEquiv`, `Config.Partner.bijOn`, `Config.Partner.card_sols`, `Config.Partner.solsEquiv_symm_apply` | `System/Partner.lean` | proved |
| §2.2 Lemma 1, family form | `Config.Partners`, `Config.Partners.isSol_iff`, `Config.Partners.solsEquiv`, `Config.Partners.bijOn`, `Config.Partners.card_sols` | `System/Partner.lean` | proved |
| §2.2 Lemma 2 (gluing) | `Config.glue`, `Config.Gluing`, `Config.glueMap`, `Config.glueLift`, `Config.Gluing.solsEquiv`, `Config.Gluing.bijOn`, `Config.Gluing.card_sols` | `System/Glue.lean` | proved |
| §2.3 Lemma 3 (base) | `Config.base_isSol_iff`, `Config.base_card_sols`, `Config.baseSol₀_mem`, `Config.base_exists_first` | `System/Base.lean` | proved |
| §2.3 Lemma 3 on any two-element index | `Config.base_card_sols'`, `Config.base_mem_sols'`, `Config.base_exists_first'` | `System/Base.lean` | proved |

## The formalization

- **Configurations.** `Config ι` is indexed by an arbitrary type `ι`; `Fintype ι` and
  `DecidableEq ι` are assumed where they are needed. Classes lie in `ZMod 8`, with
  `cls_mem : cls x ∈ {1, 3, 5, 7}`. Bits lie in `ZMod 2`. **Convention:** `bit y x` is `[y/x]`, so the
  first argument is the "numerator". Reciprocity reads `bit x y + bit y x = λ_x λ_y` for `x ≠ y`. The
  diagonal `bit x x` is a free field and never matters. The diagonal term of `K` is
  `[x/x](u_x + u_x) = 0`, so `monsky_eq_sum` writes `(Ku)_x` as a sum over all `y`, and
  `isSol_congr` / `sols_congr` show that `Σ(𝒞)` depends only on the classes and the off-diagonal
  bits.
- **The system.** `IsSol 𝒞 σ := (∀ x, E1 σ x) ∧ (∀ x, E2 σ x) ∧ a₀ = b₀ ∧ D σ`, with the rows
  written exactly as in §2.1. `twoAdicRows c a₁ b₀ b₁ (λ·u) (μ·u) (λ·v)` is the table `(D)`.
  `sols 𝒞 := univ.filter (IsSol 𝒞)` is a `Finset (Unknowns ι)`.
- **Bijections.** Each lemma provides an `Equiv` between the solution finsets (as subtypes)
  together with its `toFun` and `invFun` formulas, the `Set.BijOn` form for the forward map, and
  the cardinality equality. The forward maps keep `a₀, a₁, b₀, b₁`, so the first-coordinate class
  `(a₀, a₁, u)` maps as the note says:
  - Lemma 1: `u ↦ u|_{S∖r}`. The inverse sets `u_r = u_y`, `v_r = v_y`.
  - Lemma 2: `u ↦ (u|_{S'}, u_{g*} := u_g)`. The inverse sets `u_x = u_{g*}` on `X = G ∪ {g}` and
    gives `u_{r_ℓ}`, `v_{r_ℓ}` by (2.1) and (2.2). These are the definitional equations of
    `glueLift` (`solsEquiv_symm_apply`).
- **Transport.** `Config.reindex e` (for `e : κ ≃ ι`), `Config.solsReindexEquiv` and
  `Config.card_sols_reindex` move a configuration and its solutions along an equivalence of index
  types. `Config.solsEquivOfIso` combines this with `sols_congr`: two configurations that match
  through `e` on the classes and the off-diagonal bits have corresponding solution sets.

## Statement corrections and precisions

1. **Lemma 1, "exactly one `y ∈ S`".** The note leaves implicit that `y ≠ r`. Formalized as
   `Partner 𝒞 r y`: `y ≠ r`, `c_r = 1`, `[r/y] = 1`, and `[r/z] = 0` for every `z ∉ {r, y}`. The
   symbols `[z/r]` then follow by reciprocity (`bit_symm_of_cls_one`).
2. **Lemma 1, family form (an addition).** Step 1 of §2.5 removes all `r_ℓ ∈ R_T` at once.
   `Partners` handles a configuration on `ι ⊕ R` in which every `r ∈ R` is a glue prime with a single
   nonzero symbol at `y r ∈ ι`. Its symbols at the other partners are therefore 0, as in §2.5. The
   single-prime Lemma 1 is derived from it by reindexing along `{x // x ≠ r} ⊕ Unit ≃ ι`.
3. **"Isomorphism".** The solution sets are formalized as finsets, and the lemmas state bijections
   (`Equiv`s) given by the note's explicit maps. Linearity is not stated: the system is homogeneous
   linear, the maps are visibly linear, and the consumers (dimension 3, i.e. 8 elements, and the
   membership of the class `β`) need only the bijection and the formulas.
4. **Lemma 2 index type.** As §4.3 of the note suggests, Lemma 2 is proved for the index type
   `S' ⊕ (Option G ⊕ G)`: `.inr (.inl none)` is `g`, `.inr (.inl (some ℓ))` is `ℓ`, and
   `.inr (.inr ℓ)` is `r_ℓ`. The glued configuration lives on `Option S'`, with `none = g*`.
   `glue 𝒞` is defined for every `𝒞`. Its reciprocity is proved from the additivity of `λ` on odd
   classes, as the note remarks, and needs none of the gluing hypotheses.
5. **Lemma 2 hypotheses.** `Gluing 𝒞`: `c_{r_ℓ} = 1`, `[r_ℓ/ℓ] = [r_ℓ/g] = 1`, and `[r_ℓ/z] = 0` for
   every other `z`, including the other glue primes, as in the note. No hypothesis on the symbols
   inside `X = G ∪ {g}` is needed. This agrees with the referee's remark that the condition
   `[q₀/ℓ] = 0` of §2.4 is never used: in step 5 those symbols lie inside `X`.
6. **(2.1) and `a₁`.** The note writes (2.1) with `a₁ = 0`, which `(D)` forces. `glueLift` uses (2.1)
   exactly as printed. Every row of `twoAdicRows` contains `a₁ = 0` (`twoAdicRows_a1`,
   `IsSol.a1_eq_zero`), so `glueLift` inverts `Φ` on solutions.
7. **`(D)` for even `c`.** The table defines `(D)` only for `c ∈ {1, 3, 5, 7}`. `twoAdicRows` is
   `False` for the other classes, which never occur (`prodClass_mem`).
8. **`c(𝒞*) = c(𝒞)`.** This holds because the glue primes have class 1 (`glue_prodClass`). In
   Lemma 1, `c(𝒞 ∖ r) = c(𝒞)` likewise (`Partners.prodClass_eq`).
9. **Lemma 3.** "Dimension 3" is stated as `sols.card = 8`, matching the wording of CR₃ in §4.1.
   The index is `Fin 2` with `p* = 0`, `q₀ = 1` and `x = [q₀/p*] = bit 1 0`. The primed versions
   handle any two-element index type `{p, q}`. Beyond the note's statement, `base_isSol_iff`
   describes all solutions: `a₀, u_{p*}, u_{q₀}` are free, and `v_{p*} = a₀ + xw`,
   `v_{q₀} = a₀ + (x+1)w`, `a₁ = 0`, `b₀ = a₀`, `b₁ = u_{q₀}`, where `w = u_{p*} + u_{q₀}`.
   `base_exists_first` gives, for each `a₀`, a solution with first coordinate `(a₀, 0, 𝟏_{p*})`.
10. **First-coordinate classes.** As integers, the classes `a` before and after gluing agree exactly
    when the lifted `u` vanishes on the removed glue primes. That is `u_y = 0` in Lemma 1, and
    `u_{r_ℓ} = 0`, computed by (2.1), in Lemma 2. Steps 4 and 6 of §2.5 check exactly this. The
    lemmas therefore state the transformation of `(a₀, a₁, u)` and the inverse formulas. They do
    not claim that the integer class is preserved unconditionally.

## Lemmas added beyond the leaves

- `Config.lean`: `oddClasses_mul`, `lam8_mul`, `mu8_mul` (by `decide` over `ZMod 8`),
  `prod_mem_oddClasses`, `lam8_prod`, `mu8_prod`, `Config.bit_symm_of_cls_one`, `Config.reindex`,
  `Config.prodClass_reindex`.
- `Selmer.lean`: `dot`, `twoAdicRows_a1`, `Config.IsSol.a1_eq_zero`, `Config.isSol_congr`,
  `Config.sols_congr`, `Config.isSol_reindex_comp`, `Config.solsReindexEquiv`,
  `Config.card_sols_reindex`, `Config.solsEquivOfIso` (with `_apply`, `_symm_apply`),
  `Config.card_sols_of_iso`, `Unknowns.comp`.
- `Partner.lean`: `bijOn_of_equiv_coe`, `Config.restrictLeft`, `Config.erase`,
  `Config.sumUnitEquiv`, `Config.partnerExtend`, and the row computations `Partners.monsky_inr`,
  `Partners.monsky_inl`.
- `Glue.lean`: `glueVec`, `GlueConst`, and the steps of the proof: `Gluing.monsky_r` (step 1),
  `Gluing.monsky_inl` (step 2), `Gluing.monsky_ell` and `Gluing.sum_monsky_X` (step 3),
  `Gluing.dot_lam`, `Gluing.dot_mu`, `Gluing.D_iff` (step 4), `Gluing.const_of_isSol`,
  `Gluing.glueMap_isSol`, `Gluing.glueLift_isSol`, `Gluing.glueLift_glueMap`.
- `Base.lean`: `twoAdicRows_five`, `baseSol`, `baseSol_injective`, `base_sols_eq`, `baseSol₀`,
  `finTwoEquiv`.

Name check: none of these names clashes with the declarations of the parallel task `dl-slots`
(`ZInQKernel/RouteK/Slots/`, also in the namespace `ZInQ.RouteK`), as of its pushed branch.

## Problems

None blocking. Two technical notes:

- The `Decidable` instance for the nine-variable bit statement of Lemma 3 needs
  `set_option synthInstance.maxSize 4096` (instance search only, no kernel option). The kernel
  `decide` itself takes well under a second.
- `ring` does not know characteristic 2. Identities in `ZMod 2` are closed with
  `ring_nf; reduce_mod_char`, or `linear_combination (norm := (ring_nf; reduce_mod_char)) h`. Large
  `Finset` sums should be generalized to atoms first, because `ring_nf` normalizes inside binders
  inconsistently.

## Suggestions for the next agent (realization, L5, and the proof of DL)

- To apply Lemma 2 to a concrete configuration, for example one indexed by a finset of primes,
  build an equivalence `e : S' ⊕ (Option G ⊕ G) ≃ ι`, apply the lemma to `𝒞.reindex e`, and compose
  with `solsReindexEquiv`. Step 2 of §2.5 uses `S' = Unit` (`{q₀}`), `G = P ∖ {p₀}` and `g = p₀`.
  Step 5 uses `S' = P ∪ R_P`, `G = T` and `g = q₀`.
- Step 5 identifies the glued configuration with `𝒞_Σ`. Use `solsEquivOfIso`, which needs only the
  classes and the off-diagonal symbols. The diagonal of `glue` is set to 0 and never matters.
- To get the base configuration from step 2, use `base_card_sols'` / `base_mem_sols'` on
  `Option Unit` (`p* = none`, `q₀ = some ()`), or reindex to `Fin 2`.
- Lift the class `β` with the explicit inverse formulas (`Partner.solsEquiv_symm_apply`,
  `Gluing.solsEquiv_symm_apply`, and the definition of `glueLift`). Steps 4 and 6 then become
  `ZMod 2` computations with the symbol conditions of §2.4.
