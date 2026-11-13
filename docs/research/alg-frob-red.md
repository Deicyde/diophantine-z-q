# alg-frob-red: reducing `FrobTrace.AlgFrobRed`

Task alg-frob-red, 2026-11-13. Lean: `scratch/alg-frob-red/part_red.lean`.
`scratch/alg-frob-red/build.sh` assembles `scratch/alg-frob-red/AlgFrobRed.lean`. It puts this
task's file after verbatim copies of two sources:

- frob-trace's three parts (`src_part_*.lean`), from `origin/wip/frob-trace:scratch/frob-trace/`
  at commit 87ed8c54. Before the Rigidity imports were added, the first 2780 lines of the
  assembled file were `cmp`-identical to frob-trace's `FrobTrace.lean` (VERIFIED).
- `src_Rigidity.lean`, `cmp`-identical to `scratch/mul-rigidity/Rigidity.lean`. It provides
  `G0FibreSimple.rigidityHom`, which mul-rigidity proved from Mathlib.

Log: `scratch/alg-frob-red/log.md`.

## 1. Result

**`FrobTrace.AlgFrobRed`, copied verbatim, is proved from five inputs:**
- two leaf candidates: `GoodRedCofinite` (published) and `SmoothGeomConnIntegral` (textbook);
- the existing kernel leaf I2-Red, `PkgI2.ReductionTorsionBijective` (Serre–Tate 1968 §1);
- two glue Props: `FExtend` and `FrobMorph`.

The file compiles with no `sorry`, and every `#print axioms` line gives
`[propext, Classical.choice, Quot.sound]`. This was VERIFIED with `lake env lean
scratch/alg-frob-red/AlgFrobRed.lean`: exit 0, about 70 s, 74 axiom prints.

```
theorem AlgFrobRedRed.algFrobRed_of_leaves (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed
theorem AlgFrobRedRed.tateBridge35_of_leaves (hT : PkgI3.TateModuleFree)
    (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtend) (hFr : FrobMorph) :
    G14Bridge.TateBridge35
```

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
- `σ` acting on `κ(v)` as `z ↦ z^p`;
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

How step 7 works:
- `Θ` (`thetaW`, `thetaHom`) is a bijective monoid homomorphism. It sends I2's `κ(w')`-points of
  `𝒜` to the `κ(w)‾`-points of `sf 𝒜`, where `w' = ψ⁻¹(v)`.
- I2's `IsReductionOf` becomes `RedRel` (`redRel_of_isReductionOf`).
- Injectivity on torsion uses the group law (`redRelMul`). With it, both of I2-Red's clauses are
  needed only in their existence form.

Intermediate forms are also theorems: `algFrobRed_of_split`, `_fine`, `_finest`, `_final`,
`_main`, `_five` and `_I2`. Each has a `tateBridge35_of_*` companion.

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
  - `dvrAt'`, `toO'`: as in neron-lg.

## 4. The remaining named Props: leaf or glue

| Prop | kind | statement (informal) | why true / source |
|---|---|---|---|
| `GoodRedCofinite` | **leaf candidate** (published) | For `A/L`, with `L ⊆ ℚ̄` a number field, there is a finite `S` such that `PkgI2.HasGoodReduction A (v ∩ L)` holds for every place `v ∣ p` with `p ∉ S`. | Spreading out to an abelian scheme over `O_L[1/N]`: EGA IV₃ §8 (8.8.2, 8.10.5), EGA IV₄ 17.7.8, and openness of geometric connectedness of fibres. Serre–Tate 1968 §1 and Milne (Cornell–Silverman 1986) §20 also state it. All locators are UNVERIFIED. Related: neron-lg's glue N1-g1 `AbVarSpreadsOut` is the global form over `𝓞_L[1/f]`, without geometric connectedness of fibres. |
| `SmoothGeomConnIntegral` | **leaf candidate** (textbook) | A smooth, quasi-compact, geometrically connected scheme over a field is geometrically integral. | After every field base change the scheme is smooth, hence regular, hence normal. A connected normal scheme with finitely many irreducible components is integral (a Stacks 033M-type lemma; EGA IV₂ 6.7-6.8). Locators UNVERIFIED. |
| I2-Red, `PkgI2.ReductionTorsionBijective` | **leaf** (existing kernel leaf, `Objects.lean` L975) | Reduction is a bijection on `m`-torsion, for `m` invertible in the DVR `O`. | Serre–Tate 1968 §1 (locator UNVERIFIED, as in the kernel). |
| `FExtend` | glue, from the kernel leaf I2-NMP | There are a ring map `t : O_w → O_w` (it is `σ⁻¹|_{O_w}`) and `F̃ : 𝒜 → 𝒜` over `Spec t` such that `t(a)^p ≡ a` mod `𝔪_w`, `F̃` fixes the unit section, and for every lift `x'` of `x`, `Spec(σ|_{O_v}) ≫ x' ≫ F̃` lifts `f x`. | `F` lies over `Spec(σ⁻¹|_L)`, because `f(x)` is an `L`-point. I2-NMP (`PkgI2.NeronMappingAbelianScheme`, BLR §1.2) extends the `L`-morphism `A → A^{(t)}` to `𝒜 → 𝒜^{(t)}`. The unit section is fixed by separatedness. The lift identity holds on the generic point. |
| `FrobMorph` | glue (absolute Frobenius; not in Mathlib) | Take `O` local with `char κ(O) = p`, `𝒜/O` abelian, `t` with `t(a)^p ≡ a`, and `F̃` over `Spec t` fixing `0`. Then there is a `κ(O)`-morphism `β` of `sf 𝒜` fixing `0` with `β ∘ y = F̃ ∘ y ∘ Spec(z ↦ z^p)` on `κ(O)‾`-points. | `β = Fr_Ā ≫ F̄`, where `F̄` is the base change of `F̃` along `Spec t̄` and `t̄ = Frob⁻¹`. It lies over `Spec(Frob ∘ t̄) = id`. The point formula is naturality of the absolute Frobenius. |

Rigidity (Mumford §4 Cor. 1) is no longer an input: mul-rigidity proved it, and its copy is
compiled here. `OwDVR`, `ResidueAlgClosed`, `ResidueAlgebraic` and `RedRelMul` were named Props in
earlier steps; all four are now theorems.

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
- **Not degenerate.** `RedRel` uses the genuine special fibre (`Over.pullback` along
  `Spec κ(O) → Spec O`) and the genuine generic clause of I2's `IsReductionOf`. The glue Props
  are stated over genuine notions: the kernel's `HasGoodReduction` and `IsAbelianScheme`,
  Mathlib's valuative-criterion machinery, and `IsArithFrob`. None is stated over an abstract
  structure invented for the purpose.
- `AlgFrobRedAt` is equivalent to `AlgFrobRed`: it is the case `g = 1`, and step 1 proves the
  converse. `AlgFrobRedGood` is strictly local.

## 6. What compiles, what remains

- `scratch/alg-frob-red/AlgFrobRed.lean`: exit 0, no `sorry` (the word appears only in comments),
  74 standard axiom prints (VERIFIED, log runs 23-31).
- **Remains:**
  - `FExtend`, to be proved from I2-NMP. This needs:
    - the conjugate model `𝒜^{(t)}`;
    - that `F` lies over `Spec(σ⁻¹|_L)` (morphisms to `Spec L` that agree on all `ℚ̄`-points are
      equal);
    - that `Spec ℚ̄ → Spec L` is an epimorphism.
  - `FrobMorph`. Mathlib 4.35 has no absolute Frobenius of an `𝔽_p`-scheme.
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
