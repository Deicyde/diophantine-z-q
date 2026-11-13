# g9-derham: glue step G9 (N5's de Rham descent lemma), the target `G9Glue`

Status: research note, task g9-derham, 2026-11-13. Branch `wip/g9-derham`. Lean files are all new,
under `ZInQKernel/Contrib/G9/`. No existing project file was edited. Log: `scratch/g9-derham/log.md`.
Two runs of this task worked in the same worktree; the second run is "3c" below. The split was
agreed between the runs, and every file names its author run.

Marks: **VERIFIED** = compiled in Lean, or read in a source; **STANDARD** = published, with a
reference; **SPECULATIVE** = an assessment. Locators recalled from memory are marked UNVERIFIED.

## 1. Main result

The target is g0-mod-galois's `G9Glue` (`scratch/g0-mod-galois/ModGalois.lean` L20241 at
`251edd47`), restated verbatim in `Statement.lean` as `ZInQ.Contrib.G9.G0Galois.G9Glue`. Its
dependencies are restated verbatim too: `I3Layer.lean` = Leaves.lean `PkgI3Sec`, `I4Layer.lean` =
Leaves.lean `PkgI4Sec`. Both were checked identical (by `diff`) to the copies in ModGalois.lean.

**`G9Glue` is not proved outright.** Its conclusion needs two facts that are neither among its
hypotheses (R10 = `PkgI4.DeRhamComparison`, T23 = `PkgI4.T23_FontaineClosure`) nor in Mathlib
(§2). Everything else is proved: VERIFIED, standard axioms only.

```lean
-- ZInQKernel/Contrib/G9/LocalModel.lean
theorem ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange
    (hBC : G9Bridge.AbVarBaseChange) (hW : G9Bridge.R10Weights) : G0Galois.G9Glue

def G9Bridge.AbVarBaseChange : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : PkgI3.AbVar K) (L : Type) [Field L] (i : K →+* L)
    (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ (A' : PkgI4.I3.AbVar L) (c : A'.V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ), A'.dim = A.dim ∧
      ∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (Field.absoluteGaloisGroup.map i σ) (c v)

-- ZInQKernel/Contrib/G9/Reduction.lean
def G9Bridge.R10Weights : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (w : ℤ), w ≠ 0 → w ≠ -1 → PkgI4.htMultOver p (A.galRep p) w = 0
```

T23 is a hypothesis of `G9Glue`, but the proof does not use it: a dimension count replaces
Fontaine's closure properties. T10 does not occur at all.

The intermediate theorems, all in namespace `ZInQ.Contrib.G9` and all VERIFIED with the standard
axioms:

| declaration | type (abridged) | file |
|---|---|---|
| `localModel_of_abVarBaseChange` | `AbVarBaseChange → G9Bridge.LocalModel` | LocalModel.lean |
| `g9Glue_of_localModel` | `LocalModel → R10Weights → G9Glue` | Final.lean |
| `fieldEmbBdR` | `G9Bridge.FieldEmbBdR` (`F' ⊆ B_dR` semilinearly), from 3c's `iotaDR` | Final.lean |
| `g9Glue_of_fieldEmb` | `LocalModel → R10Weights → FieldEmbBdR → G9Glue` | Reduction.lean |
| `g9Glue_of_bridges` | `LocalModel → R10Weights → BdRContainsQbar → G9Glue` | Reduction.lean |
| `coef_descent` | `ℚ̄_p`-intertwiner `⇒` finite `E ⊆ ℚ̄_p`, `ρE : G_{ℚ_p} →* GL₂(E)`, `E`-intertwiner | CoefDescent.lean |
| `core_ht` | local data + `htMultOver` = 2, 2, 0 `⇒ HasHTWeights p ρE {0, -1}` | LocalCore.lean |
| `core_dR_F`, `core_dR` | local data + `IsDeRhamOver` + `F' → B_dR` `⇒ IsDeRham p ρE` | LocalCore.lean |
| `overF_count_gen`, `core_count_F` | counting through `E ⊗ V ≅ U × U`, descent `F → ℚ_p` | LocalCore.lean |
| `PkgI4.bdrAct_mul`, `bdrAct_one`, `htAct`, `drAct` | `G_{ℚ_p}` acts on `ℂ_p(i)` and on `B_dR` | BdRAct.lean |
| `descent_finrank`, `speiser_finrank`, `range_gfToGqp` | Galois descent; Speiser; image of `G_F` | Descent/Speiser/Galois.lean |
| (3c) `iotaDR`, `bdrAct_iotaDR` | `F' →ₐ[ℚ_p] B_dR`, `σ(ι x) = ι(σ|_{F'} x)` (Hensel in `B_dR^+`) | G9.lean, BdREmb.lean, HenselEmb.lean, KerTheta.lean |
| (3c) `g9_deRham`, `g9_hasHTWeights`, `g9_local` | the same local statement in 3c's form, `DeRhamComparisonWeights` (= `R10Weights` with a `dim` hypothesis) | G9.lean, G9Weights.lean |

The local data in `core_ht`/`core_dR_F` are: `F/ℚ_p` finite Galois; `ρ` a `ℚ_p`-representation of
`G_F` on `V`; `E ⊆ ℚ̄_p` finite; `ρE : G_{ℚ_p} →* GL₂(E)`; and
`eE : E ⊗ V ≃ₗ[E] E² × E²` with `eE ∘ (ρ σ).baseChange E = (ρE(gf σ) ⊕ ρE(gf σ)) ∘ eE`.

`#print axioms` output: `scratch/g9-derham/Axioms.lean`, saved in
`scratch/g9-derham/axioms-output.txt`. Every one of the 20 theorems listed there prints
`[propext, Classical.choice, Quot.sound]`, for example:

```
'ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.G9.localModel_of_abVarBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.G9.g9Glue_of_localModel' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.G9.core_ht' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.G9.coef_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.G9.iotaDR' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build: `lake build ZInQKernel.Contrib.G9.LocalModel ZInQKernel.Contrib.G9.G9Weights` succeeds
(VERIFIED); together these two modules import all 19 files of `Contrib/G9`. There is no `sorry`
and no `axiom`. One declaration raises the heartbeat limit: `localModel_of_abVarBaseChange` has
`set_option maxHeartbeats 2000000 in`, because its final anonymous constructor times out at the
default limit.

## 2. Findings

**Route check (first step).** G9 is still needed (VERIFIED, read). h-decomposition.md §1 (L467)
says: "Recommendation: route P for the announced decomposition, route K as the fallback". Route K
(L1060: GK1, GK2 replacing G9, G10, G12, G14) applies only on the fallback route.

**F1: R10's Lean form omits the vanishing of the other Hodge–Tate weights** (VERIFIED by reading
the definitions).
- `G9Out` requires `HasHTWeights p ρ {0, -1}`, which is `∀ w, htMult p ρ w = count w {0, -1}`.
  So `htMult` must vanish at every `w ∉ {0, −1}`.
- `PkgI4.DeRhamComparison` gives `htMultOver` only at `0` and `−1`.
- Nothing among `G9Glue`'s hypotheses bounds the other weights. Bounding them needs Tate's theorem
  (`ℂ_p(j)^{G_F} = 0` for `j ≠ 0`) and Sen's independence of the twists. Both rest on Ax–Sen–Tate,
  which is not in Mathlib (bdr-kertheta.md "What remains" (b)).
- The published comparison theorem does contain the vanishing. It is the Hodge–Tate decomposition
  `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g` (Tate 1967 for good reduction, Faltings 1988 in general;
  UNVERIFIED locators). With Tate's theorem, this gives multiplicity 0 at every other weight.
- **Recommendation:** add the clause `R10Weights` to R10. It is part of the same published
  statement, not a new leaf.
- Without `R10Weights`, the proof still gives `IsDeRham` and the multiplicities `1` at `0` and at
  `−1` (3c's `g9_deRham`).

**F2: base change of the abelian variety** (VERIFIED by reading).
- R10 is stated for `PkgI4.I3.AbVar F` over a finite `F/ℚ_ℓ`. `G9Glue`'s `A` is a `PkgI3.AbVar K`
  over a number field.
- Applying R10 needs three things: the base change `A_F`; the identity `dim A_F = dim A`; and
  `V_ℓ(A_F) ≅ V_ℓ(A)|G_F`, which holds because every `ℓⁿ`-torsion point over `F̄` is defined over
  `K̄`, since `A[ℓⁿ]` is finite étale.
- These are STANDARD (Mumford, *Abelian varieties*, §4 and §6; EGA IV 4.1.4 for the dimension;
  locators UNVERIFIED). They are not in Mathlib and not among the hypotheses.
- `G9Bridge.AbVarBaseChange` states exactly this, for an arbitrary field embedding in
  characteristic 0, with the Galois compatibility through Mathlib's
  `Field.absoluteGaloisGroup.map i`.
- The Galois-theoretic half of the old bridge `LocalModel` is proved
  (`localModel_of_abVarBaseChange`):
  - `K` embeds into the finite Galois field `F` = the normal closure in `ℚ̄_ℓ` of the `ℚ_ℓ`-span
    of the image of `K`;
  - the two maps `G_F → G_ℚ`, through `K` (`resQ`) and through `ℚ_ℓ` (`decomp`), are conjugate,
    because two embeddings of `ℚ̄` into `F̄` differ by an automorphism of `ℚ̄`
    (`exists_aut_comp`, via `AlgHom.restrictNormal`).
- I judge `AbVarBaseChange` true as stated (SPECULATIVE, but each ingredient is STANDARD). It is
  needed only for `K` a number field and `L` a finite extension of `ℚ_ℓ`; the general form is
  stated because it is the cleaner textbook statement.

**F3: `ℚ̄_p ⊆ B_dR`. Closed (VERIFIED).**
- Descending `D_dR` from `F` to `ℚ_p` needs an embedding `F' → B_dR` (`F' ⊆ ℚ̄_p` the copy of `F`)
  with `σ(ι x) = ι(σ x)`.
- 3c constructed it: `iotaDR`, by Hensel's lemma in `B_dR^+`. It uses bdr-kertheta's `θ⁺` (copied
  verbatim into `KerTheta.lean`), the equivariance `θ⁺ ∘ σ = σ ∘ θ⁺` and the `ℚ_p`-linearity of
  `θ⁺` (`BdREmb.lean`).
- The bridge `BdRContainsQbar` of `Reduction.lean` is therefore no longer needed.

**Other point.** g0-mod-galois's docstring plans a Baire argument for the finite coefficient field.
It is not needed: `coef_descent` takes `E` generated by finitely many matrix entries, namely those
of `e'`, of `e'⁻¹`, and of `r` at coset representatives of `G_{ℚ_ℓ}/G_F`, which form the finite
group `Gal(F'/ℚ_ℓ)`. VERIFIED.

## 3. The proof (N5 L10939-11000, h-trust C3 "Galois choice")

1. From `LocalModel`: `F`, `A'/F` with `dim A' = 2`, `c : V_ℓ(A') ≅ V_ℓ(A)` intertwining
   `G_F → G_K`, and `g ∈ G_ℚ` with `resQ K (j σ) = g · decomp(σ) · g⁻¹`.
2. The intertwiner `e' := (r(g)⁻¹ ⊕ r(g)⁻¹) ∘ e ∘ (1 ⊗ c) : ℚ̄_ℓ ⊗ V_ℓ(A') ≅ ℚ̄_ℓ² × ℚ̄_ℓ²`
   intertwines `G_F` with `r|_{G_{ℚ_ℓ}} ⊕ r|_{G_{ℚ_ℓ}}` through `gfToGqp`.
3. `coef_descent` gives a finite `E ⊆ ℚ̄_ℓ`, `ρE` with `map ρE = r.restrictLocal ℓ`, and
   `eE : E ⊗ V ≅ E² × E²`.
4. Counting (`overF_count_gen`): for each period ring `B` (`ℂ_p(i)` or `B_dR`),
   `[E:ℚ_ℓ] · dim D_F(V) = 2 · dim D_F(ρE)`.
5. Descent (`descent_finrank`, Speiser): `dim D_F(ρE) = [F:ℚ_ℓ] · dim D_{ℚ_ℓ}(ρE)`, through
   `F' ⊆ ℚ̄_ℓ ⊆ ℂ_p` (`cpEmb`) and `F' ⊆ B_dR` (`iotaDR`).
6. Divisibility (`finrank_dvd_Dsp_core`): `[F:ℚ_ℓ] ∣ dim D_F(V)` (an `F'`-structure), so
   `htMultOver` determines `dim` exactly.
7. With R10 and `R10Weights`: `dim D_{ℚ_ℓ}(ρE) = 2[E:ℚ_ℓ]` (de Rham), and the HT multiplicities
   are `1, 1, 0`.

## 4. What remains

- `G9Bridge.AbVarBaseChange` (F2): algebraic geometry of abelian varieties, namely base change,
  dimension, and finiteness of `A[ℓⁿ]`. Not in Mathlib. This is the main missing piece.
- `G9Bridge.R10Weights` (F1): best handled by amending R10. Proving it needs Tate–Sen
  (Ax–Sen–Tate), which is not in Mathlib.
- For the integrator: `g9Glue_of_abVarBaseChange` closes `G9Glue` as soon as both are available.
  If R10 is amended to `DeRhamComparison ∧ R10Weights`, the only new statement is
  `AbVarBaseChange`.

## 5. Files (all new; `ZInQKernel/Contrib/G9/`)

- Verbatim restatements: `I3Layer.lean`, `I4Layer.lean`, `Statement.lean`; 3c's
  `KerTheta.lean` (bdr-kertheta's scratch file).
- First run: `Speiser.lean`, `Descent.lean`, `Galois.lean`, `OverF.lean` (3c added the equivalences
  `DspPiEquiv`, `DspProdEquiv`), `BdRAct.lean`, `LocalCore.lean`, `CoefDescent.lean`,
  `Reduction.lean`, `Final.lean`, `LocalModel.lean`.
- Second run (3c): `Local.lean`, `HenselEmb.lean`, `BdREmb.lean`, `G9.lean`, `G9Weights.lean`.
- Checks: `scratch/g9-derham/Axioms.lean` and `axioms-output.txt`.
- There are no name clashes across the directory: a file importing all modules compiles
  (VERIFIED).
