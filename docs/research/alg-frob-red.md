# alg-frob-red: reducing `FrobTrace.AlgFrobRed`

Task alg-frob-red, 2026-11-13. Lean: `scratch/alg-frob-red/part_red.lean`.
`scratch/alg-frob-red/build.sh` assembles `scratch/alg-frob-red/AlgFrobRed.lean`. It puts this
task's file after verbatim copies of two sources:

- frob-trace's three parts (`src_part_*.lean`), from `origin/wip/frob-trace:scratch/frob-trace/`
  at commit 87ed8c54.
- `src_Rigidity.lean`, `cmp`-identical to `scratch/mul-rigidity/Rigidity.lean`. It provides
  `G0FibreSimple.rigidityHom`, which mul-rigidity proved from Mathlib.

Checks on the assembled file (VERIFIED with `cmp`):
- After its four import lines, it contains frob-trace's `FrobTrace.lean` (all but that file's
  single import line).
- Then comes the body of `Rigidity.lean` (all but its four import lines).
- Both blocks are byte-identical to their sources.

Log: `scratch/alg-frob-red/log.md`.

## 1. Result

**`FrobTrace.AlgFrobRed`, copied verbatim, is proved from five inputs:**
- two leaf candidates: `GoodRedCofinite` (published) and `SmoothGeomConnIntegral` (textbook);
- the existing kernel leaf I2-Red, `PkgI2.ReductionTorsionBijective` (Serre–Tate 1968 §1);
- two glue Props:
  - `FExtendGen`: `F` extends to the abelian scheme. This is the Néron mapping property, i.e. the
    kernel leaf I2-NMP, applied to the conjugate model. It is stated on the generic fibre, with no
    points.
  - `AbsFrob`: the absolute Frobenius of a scheme in characteristic `p` exists and is natural on
    affine points. This is pure scheme theory and is not in Mathlib.

The file compiles with no `sorry`, and every `#print axioms` line gives
`[propext, Classical.choice, Quot.sound]` (VERIFIED: `lake env lean
scratch/alg-frob-red/AlgFrobRed.lean`, exit 0, about 70 s, 87 axiom prints).

```
theorem AlgFrobRedRed.algFrobRed_of_gen (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed
theorem AlgFrobRedRed.tateBridge35_of_gen (hT : PkgI3.TateModuleFree)
    (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    G14Bridge.TateBridge35
```

Coarser forms are also proved, in case a piece is stated differently:
- `algFrobRed_of_absFrob` takes `FExtendCore` in place of `FExtendGen`. `FExtendCore` states the
  extension through lifts of points. `fExtendCore_of_gen : FExtendGen → FExtendCore`.
- `algFrobRed_of_core` additionally takes `FrobMorph` in place of `AbsFrob`. `FrobMorph` is the
  twisted Frobenius `Fr_Ā ≫ F̄` on the special fibre. `frobMorph_of : AbsFrob → FrobMorph`.
- `algFrobRed_of_leaves` additionally takes `FExtend` in place of `FExtendCore`. `FExtend` lets `t`
  vary and asks for `t(a)^p ≡ a`. `FExtendCore` pins `t` to `σ⁻¹|_{O_w}` (`tSig`), which is the
  only `t` that can work, and the clause `t(a)^p ≡ a` is proved (`tSig_residue`).

**Effect on G14.** frob-trace's `FrobTraceCompose.g12Spec_g14_of_G7Data` takes `AlgFrobRed` as an
input. Substituting this theorem, G14's `G12Spec ∧ G14TraceCompat` rests on these five inputs
instead. Its other inputs are unchanged: I3.M0, T7, `DirichletOfFinite` and G8-G12.

No statement was changed. `AlgFrobRed` is true, not vacuous and not degenerate (frob-trace §4; the
review in §5 agrees).

**What the Lean proof covers.** Everything except the five inputs:
- moving to the place `g(v)` where `gτg⁻¹` is a Frobenius;
- isolating the finite set `S`;
- showing the special fibre is an abelian variety, given `SmoothGeomConnIntegral`;
- the residue characteristic, and `ℓⁿ` being a unit;
- `O_w` being a DVR (`owDVR`);
- the valuative criterion, existence and uniqueness of lifts (from Mathlib);
- `κ(v)` being an algebraic closure of `κ(w)` (`residueAlgClosed`, `residueAlgebraic`);
- the reduction map being a group homomorphism (`redRelMul`, via the adjunction
  `Over.map ⊣ Over.pullback`);
- transporting I2-Red from `L‾` to `ℚ̄` and to the special fibre (`redTorsionQbar_of`);
- `σ` acting on `κ(v)` as `z ↦ z^p`, and `σ⁻¹|_{O_w}` inducing `Frob⁻¹` on `κ(w)`;
- the twisted Frobenius `β = Fr_Ā ≫ F̄` on the special fibre (`frobMorph_of`): the base change
  `F̄ = F̃ ×_{Spec t} Spec t̄`, `β` lying over the identity, `β` fixing `0` (`sf_eta_fst`), and
  the point formula;
- rigidity (mul-rigidity's proof).

## 2. The chain of proved implications

All of these are in namespace `AlgFrobRedRed`.

| step | theorem | content |
|---|---|---|
| 1 | `algFrobRed_of_at : AlgFrobRedAt → AlgFrobRed` | Moves to the place `g(v)` and the Frobenius `gτg⁻¹` there (`liesOver_smul`, `isArithFrob_conj`). |
| 2 | `algFrobRedAt_of_good : GoodRedCofinite → AlgFrobRedGood → AlgFrobRedAt` | `S` is the set of bad primes. What remains is local, at one place of good reduction. |
| 3 | `algFrobRedGood_of : SmoothGeomConnIntegral → ReductionMapGood → RedTorsionQbar → ReductionFrobGood → AlgFrobRedGood` | Sets `k = κ(w)`, `Ā = sf 𝒜` (abelian by `sf_isAbelianVariety`) and `N = 1`. The intertwining comes from uniqueness of reductions. The torsion clauses are `RedTorsionQbar` at `m = ℓⁿ` (`charP_kw`, `isUnit_cast_of_ne`). |
| 4 | `reductionMapGood_of : ResidueAlgClosure → RedRelMul → ReductionMapGood` | Valuative criterion from Mathlib: `exists_lift` (`UniversallyClosed.eq_valuativeCriterion`), `lift_unique` (`IsSeparated.valuativeCriterion`), `exists_redRel`, `redRel_unique`. |
| 5 | `reductionFrobGood_of : SmoothGeomConnIntegral → FExtend → FrobMorph → ReductionFrobGood` | `ᾱ = β` is a homomorphism by `rigidityHom`. `residue_sigV` shows `σ` acts as `z ↦ z^p` on `κ(v)`, and `j` commutes with `z ↦ z^p`. |
| 6 | `residueAlgClosure_of : ResidueAlgClosed → ResidueAlgebraic → ResidueAlgClosure` | `IsAlgClosure.equiv`. |
| 7 | `redTorsionQbar_of : PkgI2.ReductionTorsionBijective → OwDVR → RedTorsionQbar` | Transport along `ψ : L‾ ≃ₐ[L] ℚ̄` (`UnramTate.trPt`), see below. |
| 8 | `residueAlgClosed`, `residueAlgebraic`, `redRelMul`, `owDVR` | Proved outright from Mathlib. `owDVR` adapts neron-lg's `dvrAt_center`. |
| 9 | `fExtend_of_core : FExtendCore → FExtend` | `t = tSig σ = σ⁻¹|_{O_w}` (via `AlgEquiv.restrictNormal`). `tSig_residue` gives `t(a)^p ≡ a`. |
| 10 | `frobMorph_of : AbsFrob → FrobMorph` | `β = Fr ≫ F̄`, with `F̄ = pullback.map F̃ (Spec t̄) (Spec t)` and `t̄ = ResidueField.map t` (local by `isLocalHom_of_resPow`). `β` lies over `Spec(Frob ∘ t̄) = id`. It fixes `0`: by `sf_eta_fst`, the unit of `sf 𝒜` is `Spec κ → Spec O` followed by the unit of `𝒜`. The point formula is point-naturality of `Fr`. |
| 11 | `fExtendCore_of_gen : FExtendGen → FExtendCore` | The lift of `f x` is `Spec(σ|_{O_v}) ≫ x' ≫ F̃`. It lies over `Spec(toW)` because `σ ∘ t = id` on `O_w`. It restricts to `f x` by `hf`, the generic compatibility, and `Spec σ ≫ Spec(O_v ⊂ ℚ̄) = Spec(O_v ⊂ ℚ̄) ≫ Spec σ_v`. |

How step 7 works:
- `Θ` (`thetaW`, `thetaHom`) is a bijective monoid homomorphism. It sends I2's `κ(w')`-points of
  `𝒜` to the `κ(w)‾`-points of `sf 𝒜`, where `w' = ψ⁻¹(v)`.
- I2's `IsReductionOf` becomes `RedRel` (`redRel_of_isReductionOf`).
- Injectivity on torsion uses the group law (`redRelMul`). With it, both of I2-Red's clauses are
  needed only in their existence form.

Intermediate forms are also theorems: `algFrobRed_of_split`, `_fine`, `_finest`, `_final`,
`_main`, `_five`, `_I2`, `_leaves`, `_core` and `_absFrob`. Each has a `tateBridge35_of_*` companion.

## 3. The objects (definitions in `part_red.lean`)

- `Ow L v` is `v.comap (algebraMap L ℚ̄)`. This is `O_w`, the valuation ring of `L` below the place
  `v` of `ℚ̄`. `kw L v` is its residue field `κ(w)`.
- `sf 𝒜` is `(Over.pullback (Spec κ(O) → Spec O)).mapGrp.obj 𝒜`: the special fibre, as a group
  object over `Spec κ(O)`.
- `RedRel v 𝒜 e j x y` is the reduction relation. It holds when some `O_w`-morphism
  `x' : Spec O_v → 𝒜` does two things:
  - it restricts to `x ∈ A(ℚ̄)` on `Spec ℚ̄`, through `e : 𝒜_L ≅ A` (the generic clause of I2's
    `IsReductionOf`, copied);
  - it satisfies `y ≫ pr₁ = Spec j ≫ Spec(res) ≫ x'`. Here `y` is a `κ(w)‾`-point of `sf 𝒜` and
    `j : κ(v) → κ(w)‾` is a ring map.
- Auxiliary definitions:
  - `genPt`, `genMap`: the generic point map of `x`;
  - `vsq`: Mathlib's `ValuativeCommSq`;
  - `sigV`: `σ` restricted to `O_v`, for `σ ∈ D(v)`;
  - `wOf`, `psiW`, `iotaW`, `thetaW`: the transport;
  - `dvrAt'`, `toO'`: as in neron-lg;
  - `tSig`: `σ⁻¹|_{O_w}`.

  The base change `F̄` in `frobMorph_of` is a local `pullback.map`.

## 4. The remaining named Props: leaf or glue

| Prop | kind | statement (informal) | why true / source |
|---|---|---|---|
| `GoodRedCofinite` | **leaf candidate** (published) | For `A/L`, with `L ⊆ ℚ̄` a number field, there is a finite `S` such that `PkgI2.HasGoodReduction A (v ∩ L)` holds for every place `v ∣ p` with `p ∉ S`. | Spreading out to an abelian scheme over `O_L[1/N]`: EGA IV₃ §8 (8.8.2, 8.10.5), EGA IV₄ 17.7.8, and openness of geometric connectedness of fibres. Serre–Tate 1968 §1 and Milne (Cornell–Silverman 1986) §20 also state it. All locators are UNVERIFIED. Related: neron-lg's glue N1-g1 `AbVarSpreadsOut` is the global form over `𝓞_L[1/f]`, without geometric connectedness of fibres. |
| `SmoothGeomConnIntegral` | **leaf candidate** (textbook) | A smooth, quasi-compact, geometrically connected scheme over a field is geometrically integral. | After every field base change the scheme is smooth, hence regular, hence normal. A connected normal scheme with finitely many irreducible components is integral (a Stacks 033M-type lemma; EGA IV₂ 6.7-6.8). Locators UNVERIFIED. |
| I2-Red, `PkgI2.ReductionTorsionBijective` | **leaf** (existing kernel leaf, `Objects.lean` L975) | Reduction is a bijection on `m`-torsion, for `m` invertible in the DVR `O`. | Serre–Tate 1968 §1 (locator UNVERIFIED, as in the kernel). |
| `FExtendGen` | glue, from the kernel leaf I2-NMP | There is a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)`, with `t = σ⁻¹|_{O_w}` (`tSig`). It fixes the unit section and restricts to `F` on the generic fibre: `e⁻¹ ≫ pr₁ ≫ F̃ = F ≫ e⁻¹ ≫ pr₁` as maps `A → 𝒜`. There are no points in the statement. The earlier forms `FExtendCore` (lifts of points) and `FExtend` (`t` free, plus `t(a)^p ≡ a`) are proved from it. | `F` lies over `Spec(σ⁻¹|_L)`, because `f(x)` is an `L`-point for every `x`. So `F` is an `L`-morphism `A → A^{(t)}`. I2-NMP (`PkgI2.NeronMappingAbelianScheme`, BLR §1.2) applied to `𝒜` and its base change `𝒜^{(t)}` along `Spec t` extends it. The unit section is fixed by separatedness and `f(0) = 0`. |
| `AbsFrob` | glue (standard construction; not in Mathlib 4.35) | For a scheme `X` over a field `k` of characteristic `p`, there is `Fr_X : X → X` over `Spec(z ↦ z^p)` such that `Spec(r ↦ r^p) ≫ g = g ≫ Fr_X` for every ring `R` of characteristic `p` and every `g : Spec R → X`. | `Fr_X` is the absolute Frobenius: the identity on the underlying space and `f ↦ f^p` on sections. It commutes with every morphism of `𝔽_p`-schemes (SGA 5 XV, Stacks 0CC6; locators UNVERIFIED). It replaces the earlier glue `FrobMorph`, which is now proved from it. |

Rigidity (Mumford §4 Cor. 1) is no longer an input: mul-rigidity proved it, and its copy is
compiled here. `OwDVR`, `ResidueAlgClosed`, `ResidueAlgebraic`, `RedRelMul`, `RedTorsionQbar`
(from I2-Red), `FrobMorph` (from `AbsFrob`), `FExtend` and `FExtendCore` (from `FExtendGen`) were named Props in
earlier steps. Each is now a theorem, possibly from the listed inputs.

## 5. Checks on the statements

- **Review.** One read-only model review (no human review) covered the twelve Props of the first
  split: `GoodRedCofinite`, `SmoothGeomConnIntegral`, `RedRel`, `ResidueAlgClosure`, `RedRelMul`,
  `RedTorsionQbar`, `FExtend`, `FrobMorph`, `AlgFrobRedAt`, `AlgFrobRedGood`, `ReductionMapGood`
  and `ReductionFrobGood`. Verdict: all TRUE as stated, none vacuous. Points it checked in
  particular:
  - In `FExtend`, the direction `residue(t a)^p = residue a` is correct, since
    `t = σ⁻¹|_{O_w}`. The other direction would be false.
  - `FrobMorph`'s point formula is consistent with `β` lying over the identity.
  - The quantifier `∀ j` in `ReductionFrobGood` and `RedRelMul` is harmless: for `j` incompatible
    with `O_w`, `RedRel` is empty.
  - `RedTorsionQbar` holds for every compatible `j`.
  - The two leaf candidates are standard; their locators are uncertain.

  It also noted three things that do not affect truth: `IsFinite`/`Surjective F` are unused,
  `Bijective j` is redundant given compatibility, and `FrobMorph` does not need `𝒜` abelian. Since
  then, `ResidueAlgClosure`, `RedRelMul` and `RedTorsionQbar` (the last from I2-Red) have been
  proved in Lean. That settles their truth.
- **Second review.** A second read-only model review (no human review) checked the two glue Props
  added later, `FExtendGen` and `AbsFrob`. Verdict: both TRUE and correctly oriented.
  - In `FExtendGen`, `t = σ⁻¹|_{O_w}` is forced by `σ ∘ ι ∘ s = ι`.
  - Clause (3), `e⁻¹ ≫ pr₁ ≫ F̃ = F ≫ e⁻¹ ≫ pr₁`, has the right direction and is consistent with
    clause (1).
  - `F̃` exists by the Néron mapping property for `𝒜 → 𝒜^{(t)}`.
  - The unit section is fixed, by three facts: separatedness, `f(0) = 0`, and
    `Spec ℚ̄ → Spec L` being an epimorphism.
  - `AbsFrob` is naturality of the absolute Frobenius.
- **Not degenerate.** `RedRel` uses the genuine special fibre (`Over.pullback` along
  `Spec κ(O) → Spec O`) and the genuine generic clause of I2's `IsReductionOf`. The glue Props
  are stated over genuine notions: the kernel's `HasGoodReduction` and `IsAbelianScheme`,
  Mathlib's valuative-criterion machinery, and `IsArithFrob`. None is stated over an abstract
  structure invented for the purpose.
- `AlgFrobRedAt` is equivalent to `AlgFrobRed`: it is the case `g = 1`, and step 1 proves the
  converse. `AlgFrobRedGood` is strictly local.

## 6. What compiles, what remains

- `scratch/alg-frob-red/AlgFrobRed.lean`: exit 0, no `sorry` (the word appears only in comments),
  87 standard axiom prints (VERIFIED, log runs 23-40).
- **Remains:**
  - `FExtendGen`, to be proved from I2-NMP. This needs:
    - the conjugate model `𝒜^{(t)}`;
    - that `F` lies over `Spec(σ⁻¹|_L)` (morphisms to `Spec L` that agree on all `ℚ̄`-points are
      equal);
    - that `Spec ℚ̄ → Spec L` is an epimorphism.
  - `AbsFrob`. Construct the absolute Frobenius as a morphism of locally ringed spaces: the
    identity on spaces, `f ↦ f^p` on sections, local on stalks. Then prove its naturality.
  - The two leaf candidates.
- **Integration notes:**
  - `RedRel` and the Props mentioning `e` need `set_option synthInstance.maxHeartbeats 400000`.
    The `Monoidal` instance of `Over.pullback` along `Spec(O_w → L)` times out at 20000.
  - The assembled file adds Rigidity's Mathlib imports: `Group.Abelian`, `AlgClosed.Basic` and
    `ZariskisMainTheorem`.
  - Under `open scoped CategoryTheory.Obj`, `IsMonHom e.inv.hom.hom` is not found. The `MonObj`
    instance on `(Over.pullback g).obj 𝒜.X` is then `Functor.monObjObj`, not the `mapGrp` one.
    The proofs therefore work at the `mapGrp` type (`pb_symm_mul'`, `pb_mul'`).
  - Mathlib builds `Over.mapPullbackAdj` with `mkOfHomEquiv`, so its `homEquiv` is not
    definitionally the given formula, but `homEquiv.symm` is. That is why `thetaW` is defined
    with `pullback.lift` directly.
