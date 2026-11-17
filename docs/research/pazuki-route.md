# pazuki-route: taking `pazukiCor13Upper` off the GLUE count

Task pazuki-route, 2026-11-17. Base: origin/wip/pazuki-alg fee21695, with origin/main c0f3d085 (leaf-fold33) and
origin/wip/pazuki-inputs 7f58b014 merged (both clean).

- Lean: `ZInQKernel/Contrib/OneProof/PazukiRoute.lean` (namespace `PazukiRoute`).
- Scratch: `scratch/pazuki-route/` (`Route.lean` is the development copy, `CP.lean` the development file of §4.3,
  `Discharges.lean`, `FoldCheck.lean`, `FieldTaint.lean`, `autofold.json`, `log.md`, and the outputs).

Marks: **VERIFIED** (compiled, or read in a file of this repository), **STANDARD** (published, reference given),
**SPECULATIVE**. Theorem numbers recalled without a source are **UNVERIFIED**: this host has no network and no copy
of the books cited. This is model work; no human has reviewed it.

## 0. Verdict and main result

**Target (GLUE −1 on main): not met.** It is now one composite statement away.

**Main result: the arithmetic half of the analytic-to-algebraic step is proved in Lean.** That half is
pazuki-inputs' `SymmPrincipalDefinedOver`, and through it pazuki-dict's `SymmPrincipalDescends`. It follows from
three existing LEAF fields and one new printed leaf (EGA IV 2.7.2). The fine fold of `pazukiCor13Upper` is now
**GLUE-neutral**:
- strict GLUE 18 → 18, with 2 LEAF rows added;
- it is the first spec of this field that folds without `--allow-rise`;
- its only glue is pazuki-alg's **`RiemannPPAV`**: Riemann's theorem for `Ω ∈ 𝔥₂` in scheme form, the analytic
  half, rated composite.

Statements (VERIFIED, compiled, standard axioms):

```lean
theorem PazukiRoute.symmPrincipalDefinedOver_of_fields (hRep : T09Pic.PicRepresentableAbVar)
    (hK : PicFix.KleimanPicZeroProper) (hT : AvSplit.MumfordTorsionAlgClosed) (hA : AmpleDescendsFieldExt) :
    PazukiInputs.SymmPrincipalDefinedOver
theorem PazukiRoute.pazukiCor13Upper_of_fields (hG : ZInQ.HomLattice.GAGAMorphism)
    (hP : PazukiDict.PazukiCor13UpperPP) (hR : PazukiAlg.RiemannPPAV) (hRep : T09Pic.PicRepresentableAbVar)
    (hK : PicFix.KleimanPicZeroProper) (hT : AvSplit.MumfordTorsionAlgClosed) (hA : AmpleDescendsFieldExt) :
    ZInQ.HeightSplit.PazukiCor13Upper
```

The hypotheses of the field are:
- four existing fields: `gagaMorphism`, `picRepresentableAbVar`, `kleimanPicZeroProper`, `mumfordTorsionAlgClosed`;
- two printed leaves: `PazukiCor13UpperPP` (pazuki-dict; its *reading risk* flag is unchanged) and the new
  **`AmpleDescendsFieldExt`** (ampleness descends along a field extension: EGA IV 2.7.2, restricted to proper `f`);
- one composite: `RiemannPPAV`.

How the three routes came out:

1. **(A) Consumer audit: negative (VERIFIED, §1).**
   - The field has one reader chain on main: `r22_of_upper` → `R22_Pazuki` → `thetaPazuki`, with
     `ThetaPointOfFibre`.
   - There `A` is a number-field model of a fibre of the `Y₃` family. Its objects (`QML3`) carry **no polarization**.
   - `Ω = Ω(τ)` is the period matrix of the *analytic* type-`μ` form `Trd(μ⁻¹xȳ)`, and the theta point comes from the
     analytic `ThetaRatiosAtQM`.
   - No other open field (Bost, Gaudron–Rémond, Javanpeykar, nor their printed-height forms on height-fix) bounds a
     moduli or theta height above by `h_F`.

   So the analytic-to-algebraic step cannot be moved off this chain, and Pazuki's print is needed.
2. **(B) `SymmPrincipalDescends`: proved, not just reduced (VERIFIED, §§3–4).**
   - `h⁰` descends by flat base change (proved).
   - Ampleness descends: the new leaf.
   - The class of `L` is defined over a number field. Proof: the symmetric locus of the Picard scheme is locally of
     finite type. Its complex points are the symmetric classes of `A_ℂ`. These are countable: `λ_L` lies in
     `Hom(A_ℂ, Pic⁰)`, which is free of finite rank, and the fibres lie in `Pic⁰[2]`. Finally, a scheme locally of
     finite type over a number field with countably many complex points has all of them defined over number fields
     (proved from Mathlib's transcendence bases).
   - This replaces the Néron–Severi invariance route the task suggested. No Néron–Severi print is needed.
3. **(C) What is left (§5).**
   - `RiemannPPAV` cannot be proved in the tree: there are no analytic line bundles and no GAGA for sheaves.
   - It becomes LEAF only with a reading of a scheme-form print of Riemann's theorem with the theta line bundle
     (Mumford, *Abelian varieties*, §§2–3 with GAGA; candidates in §5, all UNVERIFIED).
   - Even then, the 11-16 dictionary ruling may keep it GLUE, because the reading passes through GAGA.
   - With that rating the fold is −1. Without it, the fold stays neutral.

No statement was changed. No statement is false or vacuous (§2.3).

## 1. (A) Consumer audit

### 1.1 Readers (VERIFIED, read; taint run §6)

- The field `ZInQ.HeightSplit.PazukiCor13Upper` (`ZInQKernel/OneProof/H/TailY.lean:778`) is read by
  `r22_of_upper` (TailY:810). It proves `ZInQ.LeafPush2.R22_Pazuki`, together with `NeronModelExists`,
  `SemistableReductionThm` and `SemistableNeronBaseChange`.
- `R22_Pazuki` is read by `r22Concrete_of` (LPrefix:12069), then by `thetaPazuki` (LPrefix:12116), together with
  `ThetaPointOfFibre`. Its output `ThetaPazuki` is consumed by the G0 assembly (TailD:205-220 and copies).
- The inequality the chain finally uses is `pazuki_upper_of_upper` at `X = max(1, x + 3)`, with
  `log π ≤ 3`. It is the upper half of Pazuki's display with `min(H_Θ, H_D) ≤ X`, and then
  `h(z') ≤ h(z)` (the even coordinates).

### 1.2 What the consumer has (VERIFIED, read)

- **`A`.** `ThetaPointOfFibre` quantifies over every number-field model `A` of the fibre of `(Y, Φ, π)` over `J(u)`
  (`FibreOver`). The objects of the moduli problem are `QML3 K = (A, surface, q : QMStr A, e : Level3 q)`
  (`ZInQKernel/HDecomp/QM/Structures.lean:222`). The docstring says: no polarization, by Lemma P (type-`μ` principal
  polarizations exist and are unique). The manuscript's moduli problem carries "its canonical principal
  polarization" (`diophantine_zq.tex`, proof of the `Y₃` model). The Lean one dropped it, and y3abu-strict found the
  polarized problem cannot be stated in Lean (no dual abelian scheme over a base). So the consumer has **no
  algebraic principal polarization**.
- **`Ω`.** `thetaPointOfFibre_of_qm_atQM` (TailK:335) takes `Ω = BPAnalytic.QM.Omega τ` from `FibreQMPeriod`, with
  `IsPeriodMatrix Λ Ω` via `isPeriodMatrix_of_comap`. This is the period matrix of the analytic form
  `Trd(μ⁻¹xȳ)` on `ℂ²/Λ_τ` (y3abu-strict's `lemmaP_qmTorus`: it is the unique principal Riemann form of type `μ`).
- **`z`.** It comes from `ThetaRatiosAtQM` (theta-direct proved it with no leaf): the ratios
  `θ_m(0, Ω(τ))/θ_{m₀}(0, Ω(τ))` are algebraic. F1 (`f1_of_theta`) is an analytic identity in `τ`.

### 1.3 Consequences

- **Restating the field over `(A, L)` and moving the analytic step to the consumer does not help.** The consumer
  would have to supply `L` with `IsThetaPeriodMatrix … Ω(τ)`. That is `AnalyticPPAlgebraic` restricted to QM
  fibres: the same analytic-to-algebraic step. In the consumer it is not a theorem, because `FibreQMPeriod`,
  `ThetaRatiosAtQM` and F1 are all analytic in `τ` and never mention a line bundle.
- **No other open field gives the bound.** On main the open hypotheses are the 35 rows of
  `docs/one-proof/kinds.tsv`. The only height inputs are:
  - `bostLowerBound`: a lower bound for `h_F`;
  - `gaudronRemondThm14`: isogeny degree in terms of `h_F`;
  - `javanpeykarBound`: an upper bound for `h_F` of Belyi Jacobians.

  None bounds a moduli, Igusa or theta height above by `h_F`, and that is the direction the chain needs
  (`h(J(u)) ≲ h_F(A)`). The printed-height forms on origin/wip/height-fix (49e6d97d) replace the metric in Bost and
  Gaudron–Rémond, and the direction is unchanged (read: docs/research/height-fix.md on that branch). So Pazuki's
  print, or another theta/Faltings comparison with the same polarization input, is needed. Route (A) closes
  negatively.
- **A different chain** would apply Pazuki to `(Jac C_u, Θ)` for an explicit genus-2 curve and do F1 with algebraic
  Igusa invariants. It would replace FibreQMPeriod, ThetaRatiosAtQM and F1 (the analytic period side of the H
  decomposition). That is out of scope here, and it is not known that the fibres are explicit Jacobians in the tree.

## 2. Statements

### 2.1 Verbatim

`ZInQ.HeightSplit.PazukiCor13Upper`, `PazukiInputs.SymmPrincipalDefinedOver`, `PazukiDict.PazukiCor13UpperPP`,
`PazukiDict.IsSymmPrincipal`, `PazukiAlg.RiemannPPAV` and the existing fields are imported, not copied. The new file
imports `ZInQKernel.Contrib.OneProof.PazukiInputs`, never `ZInQKernel.OneProof.Main`. `#discharges` checks the
conclusion against the field's type (§6).

### 2.2 New statements and ratings

| statement | kind | rating | reason |
| --- | --- | --- | --- |
| `AmpleDescendsFieldExt` | published | **LEAF, printed form (restricted)**; flag: locator UNVERIFIED | EGA IV₂ Cor. 2.7.2: `f`-ampleness descends along a faithfully flat quasi-compact base change, here `Spec k' → Spec k`. EGA II 4.6.6: over an affine base, `f`-ample means ample in the sense of `T09Pic.IsAmple` (Stacks 01PS, EGA II 4.5.3). Both are recalled, not read. Restricted to proper `f` (the print needs only quasi-compact `f`), so it is never stronger than the print. The EGA II identification is a definitional equivalence of two algebraic notions (no analytic dictionary). |
| `SymmClassDefinedOver` | glue | **proved** (`symmClassDefinedOver_of_countable` + §4.2, §4.3) | — |
| `SymmetricClassesCountable` | glue | **proved** (`symmetricClassesCountable_of_fields`) | from existing fields |
| `CountablePointsDefinedOver` | glue | **proved** (`countablePointsDefinedOver_proof`) | Mathlib only |
| `PazukiInputs.SymmPrincipalDefinedOver` | (was composite GLUE) | **proved** from existing fields and `AmpleDescendsFieldExt` | §3, §4 |
| `PazukiAlg.RiemannPPAV` | composite | GLUE (unchanged) | §5 |
| `PazukiDict.PazukiCor13UpperPP` | published | LEAF, printed form; flag *reading risk* (Pazuki Def. 2.6), unchanged | pazuki-dict |

### 2.3 Truth, vacuity, inertness

- `AmpleDescendsFieldExt` is true (EGA IV 2.7.2 with S = Spec k affine, STANDARD). It is not vacuous: `X = Spec k`,
  `L = 𝒪` satisfies the hypothesis. Its proper hypothesis only restricts the print.
- `SymmClassDefinedOver`, `SymmetricClassesCountable` and `CountablePointsDefinedOver` are true by the proofs in
  §§3–4. The first is not vacuous: on the zero abelian variety, `L = 𝒪` satisfies `IsSymmPrincipal`.
- None is inert: the main theorem consumes each.

## 3. The Lean file, part 1: descent of `h⁰` and ampleness (VERIFIED)

| declaration | content |
| --- | --- |
| `finrank_Γ_eq_finrankH` | for `X` proper and geometrically integral over `k`, `dim_{Γ(X,𝒪)} Γ(X, M) = h⁰(X, M)` (constants are bijective) |
| `bcIso` | `A_ℂ ≅ A_{K'} ×_{K',σ'} ℂ` (from pazuki-inputs' `bcMap_isPullback`) |
| `finrank_bcMap` | `h⁰(A_ℂ, bcMap^* M) = h⁰(A_{K'}, M)` (vendored flat base change `finrankH_pullback`, `finrankH_pullback_of_isIso`) |
| `AmpleDescendsFieldExt` | LEAF (§2.2) |
| `isAmple_of_bcMap` | ampleness of `bcMap^* M` gives ampleness of `M` (leaf + `PazukiAlg.isAmple_map` along `bcIso`) |
| `SymmClassDefinedOver` | the class-level core (GLUE, proved in §4) |
| `symmPrincipalDefinedOver_of_class` | **`SymmPrincipalDefinedOver` from `SymmClassDefinedOver` and `AmpleDescendsFieldExt`** |

## 4. The Lean file, part 2: the class-level core (VERIFIED)

### 4.1 `SymmClassDefinedOver` from the symmetric locus of the Picard scheme

`symmClassDefinedOver_of_countable (hRep : PicRepresentableAbVar) (hS : SymmetricClassesCountable)
(hC : CountablePointsDefinedOver) : SymmClassDefinedOver`. Proof:

1. Let `P` represent `Pic_{A/K}` and let `ι = dualP rep [-1] : P → P`. The symmetric locus is
   `Z = P ×_{(1,ι), P×P, Δ} P → P`. It is locally of finite type over `K`: `P` is (`PicLFT.picLocFinType_proof`) and
   `Δ` is, since `Δ ≫ pr₁ = 1`.
2. At a field point `T = Spec F`, every class on `A_F` is normalized (`Pic(Spec F) = 1`). So `toPicardFunctor` is
   bijective there (`toPic_injective` and `toPic_surjective`, from Kleiman 9.2.5 = `PicDict.Θ`).
   `homEquiv_symm_famMap` shows that `ι` acts on points as `[-1]^*`. The `[-1] × id` of `A ×_K F` is the inverse of
   `A_F` (`famMap_inv_eq`).
3. The point of `L` lies on `Z` because `L` is symmetric. The complex points of `Z` over `σ` inject into the
   symmetric classes of `A_ℂ`, so they are countable (`hS`).
4. `hC` gives `y : Spec K' → Z`. Its class `M ∈ Pic(A_{K'})` is symmetric (injectivity at `Spec K'`), and
   `bcMap^* M = L` (`comp_classify`, `bcMap_eq_baseChangeMap`, injectivity at `Spec ℂ`).

### 4.2 `SymmetricClassesCountable` from existing fields

`symmetricClassesCountable_of_fields (h1 : PicRepresentableAbVar) (hK : PicFix.KleimanPicZeroProper)
(hT : AvSplit.MumfordTorsionAlgClosed) : SymmetricClassesCountable`. Proof, for `X = A_ℂ`:

- `Pic⁰ = (B, j)` is an abelian variety. This is `picZeroAbVar0_of_leaves` from `picLocFinType_proof`,
  `identityComponentLFT_proof` and `hK` (with Cartier smoothness).
- Each `L` gives `λ_L ∈ Hom(X, B)` with `λ_L ≫ j = φ_L` (`exists_hom_comp_eq_phiL`). `Hom(X, B)` is free of finite
  rank (`homFreeFiniteC uniformizationLeafAll_proof hT`), hence countable.
- If two symmetric classes `L, L'` have the same `λ`, then `φ_L = φ_{L'}`, so `L'L⁻¹` is translation-invariant
  (`kClass_injective`, `kpt_comp_phiL`).
- A translation-invariant `c` has `[-1]^*c = c⁻¹` (`map_inv_of_isTI`: pull `m^*c = p₁^*c ⊗ p₂^*c` back along
  `(1, [-1])`). If `c` is also symmetric, then `c² = 1`.
- The classes with `IsDT 2` are finitely many (`card_isDT_le0`). So each fibre of `L ↦ λ_L` on the symmetric classes
  is finite.

### 4.3 `CountablePointsDefinedOver`

`countablePointsDefinedOver_proof : CountablePointsDefinedOver` uses Mathlib and nothing from the project. Proof:

1. Take an affine open `U` of `Z` containing the image of `x`. `x` factors through `U ≅ Spec R`
   (`IsOpenImmersion.lift`, `IsAffineOpen.isoSpec`), so `x = Spec ψ ≫ U.isoSpec.inv ≫ U.ι`. Here
   `φ_K : K → R` is defined by `Spec φ_K = U.isoSpec.inv ≫ U.ι ≫ Z.hom` (`Spec.preimage`). It is of finite type
   (`HasRingHomProperty.Spec_iff`), and `ψ ∘ φ_K = σ`.
2. The ring maps `ψ' : R → ℂ` over `σ` give pairwise distinct complex points of `Z` over `σ`, so they are countably
   many.
3. `not_injective_of_countable`: every `ψ(r)` is algebraic over `σ(K)`. Otherwise:
   - for each `c ∈ ℂ` transcendental over `σ(K)`, `exists_ringHom_eval` gives `τ : ℂ → ℂ` fixing `σ(K)` with
     `τ(ψ r) = c`. It is built from transcendence bases of `ℂ` over `K[X]` with the two structures `X ↦ ψ r` and
     `X ↦ c` (`exists_isTranscendenceBasis`, `cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'`,
     `IsAlgClosure.equivOfEquiv`; `ℂ` is renamed `CTwo` for the second structure);
   - the maps `τ ∘ ψ` would then be uncountably many (`not_countable_complex`, and `countable_not_injective`: the
     algebraic numbers over a countable field are countable).
4. So `ψ(R)` is a finitely generated `K`-algebra, integral, hence finite and a field
   (`Algebra.IsIntegral.finite`, `Algebra.IsIntegral.isField_iff_isField`). It is an intermediate field `E` of
   `ℂ/K`, a number field (`NumberField.of_module_finite`), and `x = Spec (E ↪ ℂ) ≫ Spec (R → E) ≫ …`.

## 5. What is left, rated

**One statement: `PazukiAlg.RiemannPPAV`** (composite GLUE, pazuki-alg §2.2). For `Ω ∈ 𝔥₂` there are:
- a complex abelian surface `B₀` with a biholomorphic uniformization `ℂ²/(Ωℤ² + ℤ²) ≅ B₀(ℂ)`;
- a symmetric principal `L₀` (ample, `[-1]^*L₀ ≅ L₀`, `h⁰ = 1`);
- a section of `L₀` whose divisor is the zero set of `θ(· + c, Ω)`.

- **Why it cannot be proved in the tree (VERIFIED by grep, as pazuki-alg and pazuki-inputs found).** There are no
  analytic line bundles and no GAGA for coherent sheaves. `gagaMorphism` algebraizes homomorphisms only. A theta map
  to `ℙ^N` only gives `nΘ` with `n ≥ 2`, never `Θ` with `h⁰ = 1`.
- **Why the consumer cannot avoid it (§1).** The chain's `Ω(τ)` and theta point are analytic, and the fibres carry no
  algebraic polarization.
- **Smallest printed statements that would close it** (all UNVERIFIED, none read on this host):
  1. *Scheme-form Riemann theorem with the theta bundle*: Mumford, *Abelian varieties*, §2 (`θ(·, Ω)` spans
     `H⁰(L(H_Ω, α₀))`, Appell–Humbert) and §3 (the torus is projective, an abelian variety; with Serre's GAGA every
     analytic line bundle and section is algebraic), with Frobenius's `h⁰ = √det E = 1`. If one print states "for
     `Ω ∈ 𝔥_g` there is an abelian variety `B₀/ℂ` with `B₀^an = X_Ω` and a symmetric ample `L₀` with `h⁰ = 1` whose
     section pulls back to `θ(·, Ω)`", then `RiemannPPAV` is that print restricted to `g = 2` (with `c` existential:
     weaker).
  2. Milne, *Abelian varieties* (2008 notes), Part I, Thms 2.8–2.9, cited by the manuscript for "polarizable
     complex tori are abelian varieties and their analytic homomorphisms are algebraic". This covers `B₀` (the
     `CMAbVarExists` precedent of mtcm-polar rates such an existence statement printed form) but not the theta line
     bundle.
  3. Birkenhake–Lange, *Complex abelian varieties*, Thm 4.5.1 (Lefschetz), §8.1 and §8.5 (theta divisor of a
     principal polarization), with GAGA.
- **Rating risk.** Under the 11-16 dictionary ruling, a consequence that passes through GAGA is GLUE. If the
  reviewers keep that ruling for (1), the −1 needs a Lean development of the analytic theory: analytic line bundles on
  `B^an`, GAGA for line bundles, Appell–Humbert for `g = 2`. That is far beyond one task.

Other inputs of the fold, unchanged:
- `PazukiCor13UpperPP`: the Def. 2.6 reading risk, already open.
- `AmpleDescendsFieldExt`: the EGA locators UNVERIFIED.
- `gagaMorphism`: an existing GLUE field (re-rated 11-16), not new.

## 6. Checks

All VERIFIED (outputs in `scratch/pazuki-route/`).

- **Contrib file.** `ZInQKernel/Contrib/OneProof/PazukiRoute.lean`, about 44 KB. It has no `sorry`, `axiom`,
  `instance`, notation, macro, `#eval`, `run_cmd` or `#print`. It imports `PazukiInputs`, `PicLocFinType`,
  `PhiSurjCharZero`, `IdentityComponentLFT` and `HomFreeFiniteAlgClosed` (all under `ZInQKernel/Contrib/OneProof/`),
  never `ZInQKernel.OneProof.Main`. `lake env lean` on the development copy gives no errors and no warnings.
- **Axioms** (`Axioms.lean` → `axioms-output.txt`): `finrank_bcMap`, `symmPrincipalDefinedOver_of_class`,
  `symmClassDefinedOver_of_countable`, `symmetricClassesCountable_of_fields`, `countablePointsDefinedOver_proof`,
  `symmPrincipalDefinedOver_of_fields` and `pazukiCor13Upper_of_fields` depend on `[propext, Classical.choice,
  Quot.sound]`.
- **Build.** `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.PazukiRoute` ends with `Build completed successfully (14231 jobs)`, and
  `frozenTarget` keeps the standard axioms (`build.txt`).
- **`#discharges`** (`Discharges.lean` → `discharges-output.txt`):

  ```
  DISCHARGES [OpenResearchLeaves31.pazukiCor13Upper] by PazukiRoute.pazukiCor13Upper_of_fields
    still assumes: [ZInQ.HomLattice.GAGAMorphism,
   PazukiDict.PazukiCor13UpperPP,
   PazukiAlg.RiemannPPAV,
   T09Pic.PicRepresentableAbVar,
   PicFix.KleimanPicZeroProper,
   AvSplit.MumfordTorsionAlgClosed,
   PazukiRoute.AmpleDescendsFieldExt]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 35 open hypotheses, 9960 theorems checked, 39 discharge one
  ```

  (`pazukiCor13Upper_of_route` and `pazukiCor13Upper_of_route2`, the intermediate forms, also discharge it.)
- **Autofold dry run** (`autofold.json` → `autofold-dryrun.txt`): `strict count: 11/18 on 29 -> 13/18 on 31;
  strictest 11/18 -> 13/18`, with no `--allow-rise`. The module (line 1 stripped: `FoldCheck.lean`) compiles, and
  `HDec.HSyn.sixContactMin_of_open49` depends on `[propext, Classical.choice, Quot.sound]` (`foldcheck-output.txt`).
- **Taint run** (`FieldTaint.lean`, a copy of fold33-pic's with seed `pazukiCor13Upper`): __TAINT__

## 7. Fold count

| spec | leaves (new rows) | strict GLUE | needs `--allow-rise` |
| --- | --- | --- | --- |
| pazuki-dict (coarse) | `pazukiCor13UpperPP` L, `analyticPPAlgebraic` G | 18 → 18 | no |
| pazuki-alg | PP L, `riemannPPAV` G, `symmPrincipalDescends` G | 18 → 19 | yes |
| pazuki-inputs | PP L, `riemannPPAV` G, `symmPrincipalDefinedOver` G | 18 → 19 | yes |
| **pazuki-route** | PP L, `riemannPPAV` G, `ampleDescendsFieldExt` L (+ 4 existing fields) | **18 → 18** | **no** |

Recommendation: fold pazuki-route's spec in place of the earlier ones. It is neutral and isolates the one remaining
GLUE input, Riemann's theorem in scheme form. The arithmetic descent is no longer glue.
