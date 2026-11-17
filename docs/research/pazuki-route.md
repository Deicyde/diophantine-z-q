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

**The target (GLUE −1 on main) is not met.** __CPSTATUS__

What blocks the −1 is now one statement: pazuki-alg's **`RiemannPPAV`** (Riemann's theorem for `Ω ∈ 𝔥₂` in scheme
form, rated composite). It is the analytic-to-algebraic step. Route (A) shows the chain cannot avoid it (§1).
Route (B) was carried out: the arithmetic half of the step is proved in Lean (§3, §4).

1. **(A) Consumer audit (VERIFIED).** The field has one reader on main: `r22_of_upper` → `R22_Pazuki` →
   `thetaPazuki`, through `ThetaPointOfFibre`. There `A` is a number-field model of a fibre of the `Y₃` family. That
   family's objects (`QML3`) carry **no polarization**. `Ω = Ω(τ)` is the period matrix of the *analytic* type-`μ`
   form `Trd(μ⁻¹xȳ)`, and the theta point `z` is analytic (`ThetaRatiosAtQM`). So the consumer never has an algebraic
   principal polarization. No other open field gives an upper bound for a moduli or theta height in terms of `h_F`.
   The analytic-to-algebraic step therefore has to appear somewhere on this chain, and Pazuki's print is the only
   upper bound available.
2. **(B) The arithmetic half is proved (VERIFIED, compiled, standard axioms).** pazuki-inputs left the composite
   core `SymmPrincipalDefinedOver`: a symmetric principal `L` on `A_ℂ` comes from a number field. This task proves it
   from:
   - existing LEAF fields: `picRepresentableAbVar`, `kleimanPicZeroProper`, `mumfordTorsionAlgClosed`;
   - the theorems proved in the tree since 11-16: `PicLocFinType`, `IdentityComponentLFT`, Cartier smoothness,
     Kleiman 9.2.5 (`pushforwardUnitUniversal`), Mumford §19 Thm 3 over `ℂ` (`homFreeFiniteC`), the bound on `Pic⁰[2]`;
   - one new printed leaf: **`AmpleDescendsFieldExt`** (EGA IV 2.7.2; ampleness descends along a field extension);
   - __CPSHORT__

```lean
theorem PazukiRoute.pazukiCor13Upper_of_route2 (hG : ZInQ.HomLattice.GAGAMorphism)
    (hP : PazukiDict.PazukiCor13UpperPP) (hR : PazukiAlg.RiemannPPAV) (hRep : T09Pic.PicRepresentableAbVar)
    (hK : PicFix.KleimanPicZeroProper) (hT : AvSplit.MumfordTorsionAlgClosed) (hA : AmpleDescendsFieldExt)
    (hC : CountablePointsDefinedOver) : ZInQ.HeightSplit.PazukiCor13Upper
```

__CPMAIN__

3. **(C) Count, and what would close it.** __CPCOUNT__
   - The −1 needs `RiemannPPAV` rated printed form, or proved.
   - It cannot be proved in the tree: there are no analytic line bundles and no GAGA for coherent sheaves (pazuki-alg
     §1, pazuki-inputs §3; confirmed).
   - Rating it printed form needs a reading of a scheme-form print. Candidates (UNVERIFIED): Mumford, *Abelian
     varieties*, §3 (algebraization: a polarized complex torus is an abelian variety, and its analytic line bundles
     are algebraic by GAGA) with §2 (theta functions as sections of `L(H, α)`); Milne, *Abelian varieties* (2008
     notes), Part I §2, Thms 2.8–2.9, which the manuscript itself cites (`diophantine_zq.tex`, the line beginning
     "By \cite[Part I, Theorems 2.8--2.9]{milne-av}"); Birkenhake–Lange, *Complex abelian varieties*, §§4.5, 8.1,
     8.5.
   - Under the 11-16 dictionary ruling, a consequence that passes through GAGA is GLUE. So even with a reading, the
     rating may stay GLUE, and the −1 would then need the analytic theory in Lean (§5).

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

__RATINGS__

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

__CPSECTION__

## 5. What is left, rated

__LEFT__

## 6. Checks

__CHECKS__

## 7. Fold count

__FOLD__
