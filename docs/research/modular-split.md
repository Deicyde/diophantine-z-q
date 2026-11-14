# modular-split: the modular-form, Galois-representation and Jacobian GLUE rows of the single proof, split

Task modular-split, 2026-11-14. Base 5da857b0 (wip/w59). Nothing under `ZInQKernel/` or `blueprint/` was edited. The Lean is
in `scratch/modular-split/` (results log `log.md`). Every row statement is **imported** from the kernel, not copied, so the
theorems below are about the bundle's own constants. Model work, no human review.

Marks: **VERIFIED** = compiled or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a judgement.
**UNVERIFIED** = a theorem number recalled without a source (no network on this host). A locator is UNVERIFIED unless
`docs/research/locators.md` read it.

## 1. Main result

There are six rows. Each one was either proved, narrowed, or shown to need a definition Mathlib lacks.

- **r15 `DeligneSerreConseq`: done.** It is now a theorem whose only hypothesis is `DSThm966`, Deligne–Serre 1974 Thm 4.1 in
  Diamond–Shurman's form. `DSThm966` is already a published-form LEAF field of `OpenResearchLeaves8`. So the field `r15` can
  be dropped from the bundle, which takes the strict GLUE count from 27 to 26 (SPECULATIVE until a fold applies it).
- **dimJacobianEqGenus: no literature leaf is left.** The row used to be Milne Prop. 2.1 plus Serre duality. Both are now Lean
  proofs, using the vendored Jacobian-Challenge library that came with cloud-worker 07: `Pic⁰` is smooth of relative
  dimension `dim H¹(X, 𝒪_X)`, and the library proves Serre duality. One project GLUE is left: `H⁰(X, Ω¹) = ` the holomorphic
  differentials of the function field. That step is textbook sheaf theory and is stated over genuine definitions.
  av-split §4.2 had marked this row not splittable. That was true before cloud-worker 07 vendored the library.
- **r17 `CarayolR17'` and eigenformHTNew: narrowed.** Both rows quantify over every semisimple representation attached to
  the form. The transport from the author's own realization to every such representation is now proved:
  - Chebotarev with Brauer–Nesbitt shows the two representations are conjugate;
  - the Serre–Tate conductor exponent is invariant under conjugation (new, proved);
  - Hodge–Tate weights are invariant under conjugation (kernel).

  What is left is one existential leaf per row, `CarayolRealization` and `KatoRealization`. Each is a consequence of the
  printed theorem at the author's realization, not the printed form itself. Carayol's `σ_λ(π)` and Kato's `V_f` are
  étale-cohomology objects that cannot be defined in Mathlib.

  For eigenformHTNew the dualization is also split off. `KatoRealizationCoh` is in Kato's own normalization: geometric
  Frobenius, weights `{0, k−1}`, irreducible. The contragredient is proved to be continuous, irreducible and attached.
  The negation of Hodge–Tate weights is a named GLUE, `HTDual`.
- **r16 and t09: not splittable over the present definitions.** §4 says exactly which definitions are missing.

All the theorems compile with only `propext`, `Classical.choice` and `Quot.sound` (**VERIFIED**: `#print axioms` at the end
of each file, run with `lake env lean scratch/modular-split/<file>.lean`).

## 2. Table

| row | old form (leaf-fold8 §2) | new leaves (published form, source) | new glue | Lean name of the proof |
|---|---|---|---|---|
| r15 `HDec.HSyn.DeligneSerreConseq` | GLUE (comp): Deligne–Serre Thm 4.1, Lemma 3.2, with T25, T18, T19 | `ZInQ.Contrib.HodgeSplit.DSThm966`. Published form: Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1, pp. 513–514 (audit); Diamond–Shurman Thm 9.6.6 (UNVERIFIED number). Already a bundle LEAF (`dsThm966`). | none open. Proved: `artinTransport_finite` (hodge-split's specialization argument, now returning finite image) and `attachedConj_proof` (kernel T18 + T19). | `ModularSplit.deligneSerreConseq_of_ds : DSThm966 → HDec.HSyn.DeligneSerreConseq` (`R15.lean`) **DONE** |
| r16 `LeafModCurves.R16_EichlerShimuraJ1'` | GLUE (comp): Shimura 1973 Thm 1; Shimura 1971 Thm 7.9 | — (not splittable, §4.1) | — | unchanged |
| r17 `LadicCond.CarayolR17'` | GLUE (c): Carayol 1986 Théorème (A) | `ModularSplit.R17.CarayolRealization`: there exists a semisimple attached `ρ` with `condExp(ρ|G_{ℚ_p}) = v_p(N)` for all `p ≠ ℓ`. Consequence: Carayol Thm (A) at `σ_λ(π_f)` (audit), Casselman 1973 `a(π_p) = v_p(N)`, Ribet irreducibility. Still GLUE (c). | proved: `condExp_conj` (with `invariants_conj`, `codimInv_conj`, `isAdapted_conj`, `swan_conj`) and `attachedConj_proof` | `ModularSplit.R17.carayolR17'_of_realization : CarayolRealization → CarayolR17'` (`R17.lean`), narrowed |
| eigenformHTNew `ZInQ.Contrib.HodgeSplit.EigenformHTNew` | GLUE (c): Kato 2004 9.2–9.4, transported and dualized | `ModularSplit.EigenHT.KatoRealizationCoh`: there exists an **irreducible** `ρ` whose **geometric** Frobenius has trace `a_p` and whose HT weights are `{0, k−1}`. This is Kato's normalization: Kato §§9.2–9.4 at `V_f` (UNVERIFIED locators), with Ribet's irreducibility. Still GLUE (c), because the published object is existentially quantified. A weaker alternative leaf, `KatoRealization`, is the Tate normalization. | `HTDual` (named, open): the HT weights of `ρ^∨` are `−S` when `card S = n`. Proved: `dualGR` (the contragredient, continuous), `dualGR_isIrreducible`, `katoRealization_of_coh`, `attachedConj_proof`, `htConj_proof` (kernel). | `ModularSplit.EigenHT.eigenformHTNew_of_coh : KatoRealizationCoh → HTDual → EigenformHTNew`, and `eigenformHTNew_of_realization : KatoRealization → EigenformHTNew` (`EigenHT.lean`), narrowed |
| dimJacobianEqGenus `ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | GLUE (comp): Milne JV Prop. 2.1 with Serre duality | **none** (no literature leaf) | `ModularSplit.DimJac.H0DifferentialsEqHolo` (project glue, open): `dim_ℚ H⁰(X, Ω¹_{X/ℚ}) = CurvesG.fieldGenus F`. Proved: `dim_jacobian_eq_arithmeticGenus` (from the vendored library). | `ModularSplit.DimJac.dimJacobianEqGenus_of_glue : H0DifferentialsEqHolo → DimJacobianEqGenus` (`DimJac.lean`): GLUE (comp) → GLUE (pg) |
| t09 `WeilPairing.T09_SymmIsogenyExists` | GLUE (c): Mumford §§6, 8, 20, 23 | — (not splittable, §4.2) | — | unchanged |

## 3. The proofs

### 3.1 r15 (VERIFIED, `R15.lean`)

Let `ρ` be a semisimple representation attached to a weight-one normalized eigenform `g`.
1. `DSThm966` gives Deligne–Serre's `ρ_g : G_ℚ → GL₂(ℂ)`, which is continuous with finite image.
2. hodge-split's specialization argument (`artinTransport_proof`, copied as `artinTransport_finite`) turns it into a
   semisimple `ρ₀ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to `g`. The original drops the finiteness of `ρ₀`'s image; the copy returns it.
   The argument: Nullstellensatz specialization of the finitely many entries to `ℚ̄`, then `ιL`, then Maschke.
3. `ρ` and `ρ₀` have the same Frobenius traces outside `Nℓ` (`ιC` is injective), and both are semisimple. So they are
   conjugate by `attachedConj_proof` (kernel T18 + T19).
4. Hence `range ρ ⊆ P⁻¹ (range ρ₀) P` is finite.

The locator audit (row R15: "CONSEQUENCE, with Lemma 3.2 … Chebotarev/Brauer–Nesbitt") gives exactly this route. It is
now a Lean proof.

### 3.2 r17 (VERIFIED, `R17.lean`)

`condExp ρ = codim V^{I_p} + swan ρ`, where `swan` is `swanAt` at a level `L` chosen by `Classical.choose` among the
adapted levels. Under `ρ' = PρP⁻¹`:
- the invariants are moved by `P` (`invariants_conj`), so every `codimInv` is unchanged;
- adaptedness of `L` is unchanged, so the two `Exists.choose` terms have equal predicates and pick the same `L`
  (`choose_congr`).

Hence `condExp ρ' = condExp ρ`. With `attachedConj_proof`, the row follows from the existential leaf. The leaf's docstring
records the conventions: the witness is `σ_λ(π_f)`, or its contragredient if Carayol uses geometric Frobenius. The
conductor does not change under duals (audit row R17).

### 3.3 eigenformHTNew (VERIFIED, `EigenHT.lean`)

`KatoRealization` gives a semisimple attached `ρ₀` with weights `{0, 1−k}`. Any other semisimple attached `ρ` is
conjugate to it (`attachedConj_proof`), and `htConj_proof` carries the weights over (`eigenformHTNew_of_realization`).

The dualization is split off too. `KatoRealizationCoh` is the statement in Kato's normalization:
- `ρ` is irreducible (Ribet);
- the trace of geometric Frobenius `σ⁻¹` is `a_p`;
- the HT weights are `{0, k−1}`.

Its contragredient `dualGR ρ = (σ ↦ ρ(σ⁻¹)ᵀ)` is proved to be:
- continuous;
- irreducible (`dualGR_isIrreducible`, a transpose-closed subalgebra argument), hence semisimple (kernel
  `C9Rhof.isSemisimple_of_isIrreducible`);
- unramified where `ρ` is;
- attached in the arithmetic normalization.

The negation of weights is the named GLUE `HTDual`, restricted to the Hodge–Tate case `card S = n`. Without that
restriction the general statement would need Sen theory. `HTDual` needs Tate's `H⁰(G, ℂ_ℓ(i))` computation (the kernel's
leaves `TateTwistInvariants`, `AxSenTate`), applied to `ℂ_ℓ ⊗ V^∨ ≅ ⊕ ℂ_ℓ(w)`. Proved: `eigenformHTNew_of_coh :
KatoRealizationCoh → HTDual → EigenformHTNew`.

Caveat (UNVERIFIED): the translation of Kato's printed weights into the row's convention, in which the cyclotomic
character has weight `−1`, was not checked against the source. The internal consistency check: for `k = 2`, `ρ^∨` is the
Tate module, which has weights `{0, −1}` in this convention (hodge-split, R10). That matches `{0, 1−k}`.

### 3.4 dimJacobianEqGenus (VERIFIED, `DimJac.lean`)

For a Jacobian `(J, aj)` of `(X, P₀)` with `X/ℚ` a smooth proper geometrically connected curve:
1. `exists_abelianVariety_picardDegreeZero` (vendored `Picard/FieldDescent.lean`) gives an abelian variety `V`
   representing `Pic⁰`, **smooth of relative dimension `arithmeticGenus ℚ X = dim H¹(X, 𝒪_X)`**.
2. The Abel–Jacobi map into `V` is Albanese (`Curve.isAlbanese_abelJacobiMap`), so `(V, aj')` is a Jacobian in the sense of
   `LeafModCurves.IsJacobian`. This is cloud-w07's bridge with the dimension kept.
3. `IsJacobian.unique` gives `J.X ≅ V.X`.
4. `ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension` (kernel) gives `J.dim = arithmeticGenus`.
5. The library's Serre duality `Scheme.Modules.finrankH_relativeDifferentials_zero_eq_genus` turns this into
   `dim H⁰(X, Ω¹_{X/ℚ})`.
6. The glue identifies that with `fieldGenus F`.

**The open glue `H0DifferentialsEqHolo`** (statement in `DimJac.lean`; STANDARD content: Hartshorne II.8, II.6.7, II.4.7;
UNVERIFIED numbers). It needs:
- (a) `H⁰ = Γ`: the library's `Scheme.Modules.H.zeroLinearEquiv`, plus the `ℚ`-structure through `globalSectionsRingHom`;
- (b) on affine opens, `Γ(U, Ω¹) ≅ Ω_{Γ(U)/ℚ}` (library `Scheme.Hom.kaehlerSectionsEquiv`), with naturality under
  restriction;
- (c) `Ω_{A/ℚ} ↪ Ω_{F/ℚ}` for `A` smooth: `Ω_A` is projective and `Ω_F` is its localization (Mathlib
  `KaehlerDifferential.isLocalizedModule_map`); the sheaf condition then makes `Γ(X, Ω¹) → Ω_F` injective;
- (d) the image lies in every `regularAt F w`: by the valuative criterion (Mathlib `ValuativeCriterion`, `X` proper), every
  valuation subring `w ⊇ ℚ` contains `Γ(U)` for some affine `U`;
- (e) the image is all of `holoDiff F`: on each affine `U = Spec A` with `A` Dedekind (smooth of dimension one),
  `Ω_A = ⋂_𝔪 Ω_{A_𝔪}` inside `Ω_F` (local–global principle for a projective rank-one module), each `A_𝔪` is a valuation
  subring, and `regularAt F A_𝔪` is the image of `Ω_{A_𝔪}`; then glue the local sections.

No published theorem beyond textbook sheaf theory is involved (SPECULATIVE: estimated at well over 1000 lines, so it was
not attempted).

## 4. Rows that stay as they are: the missing definitions

### 4.1 r16 `R16_EichlerShimuraJ1'`

The row asks for one `(A, π, θ)` that satisfies both:
- Shimura's unconditional clauses: a quotient of `J`, with `K_f ↪ End⁰(A)` and `dim A = [K_f : ℚ]`;
- the Eichler–Shimura trace and determinant clauses on the `ι`-components `eigenFun ℓ A θ ι`.

The trace clause is what ties `θ` to the Hecke action. Separate existential leaves, one per clause, would be about
unrelated `(A, θ)`, so they cannot be combined: the composite cannot be cut into independent existentials. The published
statements (Shimura 1973 Thm 1, audit; Shimura 1971 Thm 7.9/7.11, Diamond–Shurman §6.6, Thm 9.5.4, UNVERIFIED numbers) are
about the specific `A_f = J₁(N)/I_f J₁(N)`.

**Missing definitions:**
1. the Hecke correspondences `T_p`, `⟨d⟩` on `X₁(N)` (or their action on `J₁(N)` through Albanese functoriality, now
   available through the vendored Albanese property);
2. the Hecke algebra `𝕋 ⊆ End(J₁(N))` and the ideal `I_f = ker(𝕋 → K_f, T_p ↦ a_p)`;
3. the quotient `J₁(N)/I_f J₁(N)` of an abelian variety by an abelian subvariety. Mathlib has no quotients of group
   schemes; av-glue's image-as-AbVar recipe gives images, not cokernels.

Given 1–3, Shimura 1973 Thm 1 and the Eichler–Shimura relation become separate published-form leaves about the same
`A_f`. The rank-two clause would then follow from Mumford §19 Thm 4: the characteristic polynomial of `θ(α)` is rational,
hence `μ_α²`.

### 4.2 t09 `T09_SymmIsogenyExists`

The row is stated over `WeilDual`, an abstract structure that stands in for `Pic⁰`. Its own docstring warns that leaves
over it must be existential.

The vendored library now provides:
- invertible module sheaves and `Scheme.Pic` (`Picard/Basic.lean`);
- the relative Picard functor;
- representability of `Pic⁰` **for curves only** (`exists_abelianVariety_picardDegreeZero`).

**Missing definitions:**
1. the dual abelian variety `Â = Pic⁰_{A/K}` for `dim A > 1`, as the representing object of the rigidified
   translation-invariant Picard functor, which needs Mumford §8 representability. The set `Pic⁰(A)(K)` itself is now
   definable from `Scheme.Pic` and translations.
2. `φ_L : A → Â`, `x ↦ t_x^*L ⊗ L⁻¹`, and the theorem of the square;
3. the Weil pairing `e_n : A[n] × Â[n] → μ_n` (Mumford §20; Cartier duality of `[n]`).

With 1–3, T09 becomes "Mumford §§20, 23 for `φ_L`, `L` ample" in published form. Until then `WeilDual` stays abstract and
the row stays GLUE (c).

## 5. Effect on the single proof (SPECULATIVE until a fold applies it)

Nothing in `ZInQKernel/` was changed.
- **r15:** a fold can drop the field and fill it with `deligneSerreConseq_of_ds r.dsThm966`. Strict GLUE goes from 27 to 26.
- **dimJacobianEqGenus:** a fold can replace the field by `H0DifferentialsEqHolo`, which is project glue (pg, not literature).
  Strict GLUE stays 26, but one composite literature row becomes textbook sheaf theory, and Milne Prop. 2.1 and Serre
  duality leave the leaf list.
- **r17, eigenformHTNew:** a fold can replace the fields by `CarayolRealization`, `KatoRealization`. These are strictly
  weaker statements of the same form (c).
- **Build note:** the modules `DimJac.lean` imports must be built: `ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists`,
  `...Curve.CanonicalDegree`, `Contrib.Dim.SmoothStalk`, `Contrib.Dim.Basic`. That is about 700 vendored files; it took
  about 17 minutes here.

## 6. Files

- `scratch/modular-split/R15.lean`: r15 (imports `OneProof.H.TailT`, `OneProof.H.LPrefix`).
- `scratch/modular-split/R17.lean`: r17 (imports `OneProof.H.TailT`, `HDecomp.Conductor.LadicCond`).
- `scratch/modular-split/EigenHT.lean`: eigenformHTNew (imports `OneProof.H.TailT`).
- `scratch/modular-split/DimJac.lean`: dimJacobianEqGenus (imports `Contrib.CurvesG.GenusSplit`, cloud-w07, `Contrib.Dim`).
- `scratch/modular-split/log.md`: results log.
