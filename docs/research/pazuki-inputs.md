# pazuki-inputs: the two inputs of `pazukiCor13Upper` that pazuki-alg found missing

Task pazuki-inputs, 2026-11-16/17. Base: origin/main c0f3d085 (leaf-fold33b), with pazuki-alg (fee21695) merged
cleanly.

- Lean: `ZInQKernel/Contrib/OneProof/PazukiInputs.lean` (namespace `PazukiInputs`).
- Scratch: `scratch/pazuki-inputs/` (`Glue.lean` is the development copy; `Discharges.lean`; `autofold.json`;
  `log.md`; build and check outputs).

Marks: **VERIFIED** (compiled, or read in a file of this repository), **STANDARD** (published, reference given),
**SPECULATIVE**. Theorem numbers recalled without a source are **UNVERIFIED**: this host has no network and no copy
of Mumford, *Abelian varieties*, or of any other book cited below. This is model work with no human review.

## 0. Verdict and main result

**The target (−1 GLUE: `pazukiCor13Upper` out, only printed-form leaves in) is not met.**

- **`SymmPrincipalDescends` is not proved.** It is reduced, with every step proved in Lean, to a section-free core
  `SymmPrincipalDefinedOver`:

  > every symmetric principal polarization `L` of `A_ℂ` (A over a number field K) is `bcMap^* M` for a symmetric
  > principal polarization `M` of `A_{K'}`, `K'` a number field in `ℂ` over `σ`.

  The core is still a composite (GLUE). It is exactly "the class of `L` in `Pic(A_ℂ)` is defined over a number
  field". Its known proof uses Néron–Severi invariance, the `Pic⁰[2]`-torsor of symmetric bundles and descent along
  field extensions (§4); several of its inputs are existing fields of the fold, but the Lean proof of the rest is far
  beyond this task.
- **`RiemannPPAV` keeps the rating composite.** The reading that would make it printed form (Mumford, *Abelian
  varieties*, §3, scheme form of the algebraization of `ℂ^g/(Ωℤ^g + ℤ^g)` with its theta line bundle) could not be
  done: no copy of the book on this host, no network (§3). Nothing in the tree gives the theta line bundle (pazuki-alg
  §1 (a); confirmed, §3).
- **No statement was changed. No statement is false or vacuous** for the instance used (a Jacobian over a number
  field; §2.3).

**Main result (VERIFIED, compiled; standard axioms only, §5):**

```lean
def PazukiInputs.SymmPrincipalDefinedOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (L : (bcC A σ).X.left.Pic),
    IsSymmPrincipal (bcC A σ) L →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (σ' : K' →+* ℂ)
      (hσ : σ'.comp (algebraMap K K') = σ) (M : (A.baseChange K').X.left.Pic),
      IsSymmPrincipal (A.baseChange K') M ∧ Scheme.Pic.map (bcMap A σ σ' hσ) M = L

theorem PazukiInputs.symmPrincipalDescends_of_definedOver (h : SymmPrincipalDefinedOver) :
    PazukiDict.SymmPrincipalDescends
theorem PazukiInputs.pazukiCor13Upper_of_definedOver (hG : ZInQ.HomLattice.GAGAMorphism)
    (hP : PazukiDict.PazukiCor13UpperPP) (hR : PazukiAlg.RiemannPPAV) (hD : SymmPrincipalDefinedOver) :
    ZInQ.HeightSplit.PazukiCor13Upper
```

## 1. The Lean file (VERIFIED, compiled)

| declaration | content |
| --- | --- |
| `bcMap'`, `bcMap` | the projection `A ×_{K,σ} ℂ → A ×_K K'` over `σ' : K' → ℂ` (`pullback.lift fst (snd ≫ Spec σ')`) |
| `liftPt_ptE` | `liftPt A σ σ' hσ (ptE A σ p) = p.left ≫ bcMap`: pazuki-dict's lifted point is the image of `p` |
| `bcMap_isPullback` | the square `bcMap`, `Spec σ'` is cartesian (pasting with the cartesian square of `A_{K'}`) |
| `surjective_bcMap` | `bcMap` is surjective (base change of the surjection `Spec ℂ → Spec K'`) |
| `SymmPrincipalDefinedOver` | the core (GLUE, composite) |
| `onZeroLocus_zero` | every point lies on the divisor of the zero section |
| `eq_zero_of_pullbackSec_eq_zero` | a section whose pullback along a surjection onto a reduced scheme vanishes is zero (divisor = preimage; `support = ⊤ ⇒ Z(s) = ⊥` on reduced schemes; `Z(s) = ⊥ ⇔ s = 0`) |
| `isIntegral_abVar`, `isField_Γ_abVar` | an abelian variety is integral; `Γ(A, 𝒪)` is a field (vendored `isField_of_universallyClosed_of_isField`) |
| `zeroLocus_eq_of_factor` | if `s = u ≫ t` and `t = u' ≫ s` (with `u, u'` endomorphisms of `𝒪`) then `Z(s) = Z(t)` (vendored `zeroLocus_comp_le`) |
| `scal`, `scal_comp_app` | multiplication by `c ∈ Γ(X, 𝒪)` as an endomorphism of `𝒪`; `(c·) ≫ t` evaluates to `c • t(1)` |
| `symmPrincipalDescends_of_definedOver` | **`SymmPrincipalDescends` from the core** |
| `pazukiCor13Upper_of_definedOver` | **the field**, from `GAGAMorphism`, `PazukiCor13UpperPP`, `RiemannPPAV`, the core |

**Proof of `symmPrincipalDescends_of_definedOver`.** Given `(L, s)` on `A_ℂ`, the core gives `M` on `A_{K'}` with
`bcMap^* M = L`. If `s = 0`, take `s' = 0`: both divisors are everything. Otherwise:

1. `h⁰(M) = 1` gives a nonzero global section `u` of `M`; `s' := 𝒪 → M` the corresponding morphism (vendored
   `homOfGlobalSection`), nonzero.
2. `t := bcMap^* s'` (pazuki-alg's `pullbackSec`) has divisor `bcMap⁻¹ Z(s')`. If `t = 0`, then `Z(s')` has full
   support (`bcMap` is surjective), so `Z(s') = ⊥` (`A_{K'}` is reduced) and `s' = 0`; hence `t ≠ 0`.
3. `Γ(A_ℂ, 𝒪)` is a field and `H⁰(L)` is one-dimensional over it, so `s(1) = c · t(1)` with `c ≠ 0`. Hence
   `s = (c·) ≫ t` and `t = (c⁻¹·) ≫ s`, and `Z(s) = Z(t)`.
4. `OnZeroLocus s' (liftPt (ptE p)) ⟺ OnZeroLocus s' (p ≫ bcMap) ⟺ p ∈ bcMap⁻¹ Z(s') = Z(t) = Z(s)`.

## 2. Statements and ratings

### 2.1 Verbatim

`PazukiDict.SymmPrincipalDescends`, `RiemannPPAV`, `PazukiCor13UpperPP`, `GAGAMorphism` and the field are used
unchanged (they are imported, not copied: the new file imports `ZInQKernel.Contrib.OneProof.PazukiAlg`, which
imports pazuki-dict's file, and `#discharges` checks the conclusion against the field's type; §5).

### 2.2 The new statement and its rating

| statement | kind | rating | reason |
| --- | --- | --- | --- |
| `SymmPrincipalDefinedOver` | composite | **GLUE; not printed form** | Its content is "the class of a symmetric principal `L` on `A_ℂ` is defined over a number field". The standard proof (§4) combines Néron–Severi invariance under extension of algebraically closed fields (Maulik–Poonen, Duke 161 (2012), Prop. 3.1, UNVERIFIED), the torsor of symmetric bundles under `Pic⁰[2]` (Mumford §8 (iv), §4 App. 2, UNVERIFIED), finite presentation from `ℚ̄` to a number field (EGA IV 8.5.2) and descent of ampleness (EGA IV 2.7.2, UNVERIFIED). No single print states it. |
| `RiemannPPAV` (pazuki-alg) | composite | GLUE; not printed form (unchanged) | §3 |
| `PazukiCor13UpperPP` (pazuki-dict) | published | LEAF, printed form; flag *reading risk* (Def. 2.6) | unchanged |
| `GAGAMorphism` | existing field `{t}.gagaMorphism` | — | not a new leaf |

`SymmPrincipalDefinedOver` is strictly smaller than `SymmPrincipalDescends`: it drops the sections and divisors,
and `SymmPrincipalDescends` is proved from it (§1). It is not stronger than the classical statement: it asks for the
class of `L` only (equality in `Pic`), which is what the classical descent gives.

### 2.3 Check against the instance (falsity, vacuity)

The instance used is a principally polarized abelian surface over a number field that is a Jacobian of a genus-2
curve `C/K` (the six-contact family).

- **Hypotheses satisfiable.** On `J = Jac(C)`, with `W` a Weierstrass point rational over a finite extension `K'`,
  `Θ_W = {[P − W]}` is symmetric (`[-1]` maps `P − W` to `ιP − W`, and `P + ιP ∼ 2W`), ample, with `h⁰(𝒪(Θ_W)) = 1`
  (Riemann's theorem on the theta divisor; STANDARD). So `IsSymmPrincipal` holds for `L = 𝒪(Θ_W)_ℂ`. In Lean, the
  hypotheses are also satisfiable for the zero abelian variety (`L = 𝒪`), so the statement is not vacuous.
- **Conclusion true** (STANDARD, the classical descent, §4): for `L = 𝒪(Θ_W)_ℂ`, `M = 𝒪(Θ_W)` on `J_{K'}` works
  directly; in general `L` is one of the finitely many symmetric principal bundles in its algebraic class, all
  defined over `ℚ̄`.
- **Not inert.** The conclusion is what `SymmPrincipalDescends` needs: the equality `bcMap^* M = L` carries the
  divisor (proved, §1).
- `RiemannPPAV` (pazuki-alg §2.3): true and not vacuous; for the period matrix `Ω` of `J_σ`, `B₀ = J_ℂ` with
  `L₀ = 𝒪(Θ_W)` (Riemann's vanishing theorem, `c` = the Riemann constant). The functional equation of `θ` (proved by
  pazuki-alg) shows the zero-set condition is consistent.

## 3. `RiemannPPAV`: the reading could not be done; the tree does not give the theta bundle

- **Reading.** The scheme form needs a print stating that for `Ω ∈ 𝔥_g` there is a complex abelian variety `B₀`
  with `B₀^an ≅ ℂ^g/(Ωℤ^g + ℤ^g)` and an algebraic ample symmetric line bundle with `h⁰ = 1` whose section is
  `θ(·, Ω)`. Mumford, *Abelian varieties*, §3 ("algebraization": Lefschetz's theorem and the remark that by GAGA
  every analytic line bundle on `X^an` is algebraic) is the candidate (UNVERIFIED: not read). No copy of the book or
  of Birkenhake–Lange is on this host and there is no network, so the rating stays composite. A reader with the book
  should check whether §3 (or the start of §4) states: (i) `X_Ω` is the analytic space of a projective variety
  (Lefschetz, `L³` very ample); (ii) the functor `X ↦ X^an` from abelian varieties over `ℂ` to polarizable complex
  tori is an equivalence and analytic line bundles are algebraic (GAGA). If both are printed, `RiemannPPAV` is a
  consequence of the print of the same kind as the uniformization leaf of the 11-16 dictionary pass.
- **Tree (VERIFIED by grep of `ZInQKernel/`).** No definition of analytic line bundles or of GAGA for coherent
  sheaves exists, so a Lean proof of `RiemannPPAV` from the tree is not possible; `GAGAMorphism` only algebraizes
  homomorphisms (pazuki-alg §1). This confirms pazuki-alg's finding (a).

## 4. `SymmPrincipalDefinedOver`: the proof and what Lean would need

Proof (STANDARD; locators UNVERIFIED). Let `P` represent `Pic_{A/K}` (the existing field `picRepresentableAbVar`,
LEAF) and `P⁰` its identity component, an abelian variety (`PicZeroAbVar`, Mumford §13; `kleimanPicZeroProper`,
LEAF). The point `x ∈ P(ℂ)` of `L` is fixed by the involution `ι = [-1]^*`. For `y ∈ x·P⁰(ℂ)` symmetric, `y = x·n`
with `n ∈ P⁰(ℂ)` and `ι n = n`; since `ι` is inversion on `P⁰` (Mumford §8 (iv)), `n ∈ P⁰[2](ℂ)`, a finite group
equal to `P⁰[2](K̄)` (`mumfordTorsionAlgClosed`, LEAF: both have `2^{2g}` elements and the map is injective). So the
symmetric points of the component of `x` are finitely many, and the component of `x` in `P_ℂ` is one of finitely
many over the point of `P` below `x` (Néron–Severi: `π₀(P)` is an étale `K`-scheme; Maulik–Poonen Prop. 3.1,
SGA 6 XIII). Hence the `Aut(ℂ/K)`-orbit of `x` is finite, and `x` lies over a closed point of `P`, i.e. comes from
`P(K')` for a number field `K' ⊂ ℂ`. The `K'`-point is a line bundle `M` on `A_{K'}` (the identity section rigidifies),
`bcMap^* M = L`, and `M` is symmetric (`Pic(A_{K'}) → Pic(A_ℂ)` is injective), ample (ampleness descends, EGA IV
2.7.2) and `h⁰(M) = 1` (flat base change of `H⁰`, vendored `finrankH_pullback`).

What the Lean proof would need beyond the existing fields: `[-1]^*` is inversion on `Pic⁰` (Mumford §8 (iv), a
printed statement over the tree's `IsPicZero`), the finiteness of `π₀(P)` over each point (or `π₀(P)` étale), the
`Aut(ℂ/K)`-orbit argument (or an equivalent "a `ℂ`-point of a locally finite type `K`-scheme with finite orbit lies
over a closed point"), the injectivity of `Pic` under field extension and the descent of ampleness. Each is a
separate development; together they are far beyond one task. The core is therefore left as one composite row.

## 5. Checks

All VERIFIED (outputs in `scratch/pazuki-inputs/`).

- **Contrib file.** `lake env lean ZInQKernel/Contrib/OneProof/PazukiInputs.lean`: no errors, no warnings. The file
  has no `sorry`, `axiom`, instance, notation, macro, `#eval`, `run_cmd` or `#print`; it imports
  `ZInQKernel.Contrib.OneProof.PazukiAlg`, never `ZInQKernel.OneProof.Main`.
- **Build.** `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.PazukiInputs` ends with `Build completed successfully (14230 jobs)` (`build.txt`).
- **`#discharges`** (`Discharges.lean`; `discharges-output.txt`):

  ```
  DISCHARGES [OpenResearchLeaves31.pazukiCor13Upper] by PazukiInputs.pazukiCor13Upper_of_definedOver
    still assumes: [ZInQ.HomLattice.GAGAMorphism,
   PazukiDict.PazukiCor13UpperPP,
   PazukiAlg.RiemannPPAV,
   PazukiInputs.SymmPrincipalDefinedOver]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 35 open hypotheses, 9866 theorems checked, 36 discharge one
  ```

- **Autofold dry run** (`autofold.json`). Without `--allow-rise` it is refused:
  `strict count: 11/18 on 29 -> 12/19 on 31; strictest 11/18 -> 12/19`. With `--allow-rise` the generated module
  (`autofold-dryrun.txt`, line 1 stripped: `FoldCheck.lean`) compiles, and
  `HDec.HSyn.sixContactMin_of_open49` depends on `[propext, Classical.choice, Quot.sound]` (`foldcheck-output.txt`).

## 6. Fold count

The spec `scratch/pazuki-inputs/autofold.json` discharges `pazukiCor13Upper` (GLUE in kinds.tsv) with three
leaves: `pazukiCor13UpperPP` (published, LEAF), `riemannPPAV` (composite, GLUE), `symmPrincipalDefinedOver`
(composite, GLUE). **Net +1 GLUE** (needs `--allow-rise`), the same count as pazuki-alg's spec; pazuki-dict's
coarser spec (`PazukiCor13UpperPP` plus the single composite `AnalyticPPAlgebraic`) stays count-neutral. The fine
spec now isolates the arithmetic composite as a statement about line bundles alone.

The −1 needs both: a reading that rates `RiemannPPAV` printed form (§3), and a Lean proof of
`SymmPrincipalDefinedOver` (§4) or a print of it.
