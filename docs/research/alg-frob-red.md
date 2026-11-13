# alg-frob-red: reducing `FrobTrace.AlgFrobRed`

Task alg-frob-red, 2026-11-13. Lean: `scratch/alg-frob-red/part_red.lean`.
`scratch/alg-frob-red/build.sh` assembles `scratch/alg-frob-red/AlgFrobRed.lean` from four
verbatim copies plus this task's file:

- frob-trace's three parts, copied as `src_part_*.lean` from
  `origin/wip/frob-trace:scratch/frob-trace/` (commit 87ed8c54). The first 2780 lines of the
  assembled file, before the Rigidity imports were added, were `cmp`-identical to frob-trace's
  `FrobTrace.lean` (VERIFIED).
- `src_Rigidity.lean`, `cmp`-identical to `scratch/mul-rigidity/Rigidity.lean`. It supplies
  `G0FibreSimple.rigidityHom`, proved from Mathlib.

Log: `scratch/alg-frob-red/log.md`.

## 1. Result

**`FrobTrace.AlgFrobRed`, copied verbatim, is proved from five named Props.** Two are leaf
candidates: `GoodRedCofinite` (published) and `SmoothGeomConnIntegral` (a textbook result). Three
are glue: `RedTorsionQbar`, `FExtend` and `FrobMorph`. The file compiles with no `sorry`. Every
`#print axioms` line gives `[propext, Classical.choice, Quot.sound]` (VERIFIED: `lake env lean
scratch/alg-frob-red/AlgFrobRed.lean`, exit 0, about 60 s, 64 axiom prints).

```
theorem AlgFrobRedRed.algFrobRed_of_five (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : FrobTrace.AlgFrobRed
theorem AlgFrobRedRed.tateBridge35_of_five (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) :
    G14Bridge.TateBridge35
```

With frob-trace's `FrobTraceCompose.g12Spec_g14_of_G7Data`, G14's `G12Spec ∧ G14TraceCompat`
then rests on these five Props in place of `AlgFrobRed`. The other inputs are unchanged: I3.M0,
T7, `DirichletOfFinite` and G8-G12.

No statement was changed. `AlgFrobRed` is true, not vacuous and not degenerate (frob-trace §4;
confirmed by the review in §5).

The Lean proof covers everything except those five inputs:

- conjugating the place;
- isolating the finite set `S`;
- the special fibre as an abelian variety;
- the residue characteristic, and the fact that `ℓⁿ` is a unit;
- both halves of the valuative criterion (Mathlib);
- `κ(v)` as an algebraic closure of `κ(w)` (`ResidueAlgClosed` and `ResidueAlgebraic`, both proved
  from Mathlib);
- the reduction map as a group homomorphism (`RedRelMul`, proved through the adjunction
  `Over.map ⊣ Over.pullback`);
- `σ` acting on `κ(v)` as `z ↦ z^p`;
- rigidity (mul-rigidity's proof).

## 2. The chain of proved implications

All of these are in `part_red.lean`, namespace `AlgFrobRedRed`.

| step | theorem | content |
|---|---|---|
| 1 | `algFrobRed_of_at : AlgFrobRedAt → AlgFrobRed` | Moves to the place `g(v)` and the Frobenius `gτg⁻¹` there (`liesOver_smul`, `isArithFrob_conj`). |
| 2 | `algFrobRedAt_of_good : GoodRedCofinite → AlgFrobRedGood → AlgFrobRedAt` | `S` is the set of bad primes. What remains is local, at one place of good reduction. |
| 3 | `algFrobRedGood_of : SmoothGeomConnIntegral → ReductionMapGood → RedTorsionQbar → ReductionFrobGood → AlgFrobRedGood` | Sets `k = κ(w)`, `Ā = sf 𝒜` (abelian by `sf_isAbelianVariety`), `N = 1`. The intertwining follows from uniqueness of reductions. The torsion clauses are `RedTorsionQbar` at `m = ℓⁿ` (`charP_kw`, `isUnit_cast_of_ne`). |
| 4 | `reductionMapGood_of : ResidueAlgClosure → RedRelMul → ReductionMapGood` | Uses the valuative criterion from Mathlib: `exists_lift` (from `UniversallyClosed.eq_valuativeCriterion`), `lift_unique` (from `IsSeparated.valuativeCriterion`), `exists_redRel` and `redRel_unique`. |
| 5 | `reductionFrobGood_of : SmoothGeomConnIntegral → FExtend → FrobMorph → ReductionFrobGood` | `ᾱ = β` is a homomorphism by `rigidityHom`. `residue_sigV` gives `σ = (z ↦ z^p)` on `κ(v)`, and `j` commutes with `z ↦ z^p`. |
| 6 | `residueAlgClosure_of : ResidueAlgClosed → ResidueAlgebraic → ResidueAlgClosure` | Uses `IsAlgClosure.equiv`. |
| 7 | `residueAlgClosed`, `residueAlgebraic`, `redRelMul` | Proved outright, from Mathlib. |

The intermediate forms are also theorems, for use if a later piece changes:

- `algFrobRed_of_split` (with `ResidueAlgClosure`, `RedRelMul`, `ReductionFrobGood`);
- `algFrobRed_of_fine`;
- `algFrobRed_of_finest`;
- `algFrobRed_of_final`;
- `algFrobRed_of_main` (with `RedRelMul`).

Each has a `tateBridge35_of_*` companion.

## 3. The objects (definitions in `part_red.lean`)

- `Ow L v = v.comap (algebraMap L ℚ̄)`. This is `O_w`, the valuation ring of `L` below the place
  `v` of `ℚ̄`. `kw L v` is its residue field `κ(w)`.
- `sf 𝒜 = (Over.pullback (Spec κ(O) → Spec O)).mapGrp.obj 𝒜`. This is the special fibre, as a
  group object over `Spec κ(O)`.
- `RedRel v 𝒜 e j x y` is the reduction relation. It holds when some `O_w`-morphism
  `x' : Spec O_v → 𝒜` satisfies two conditions:
  - `x'` restricts to `x ∈ A(ℚ̄)` on `Spec ℚ̄`, through `e : 𝒜_L ≅ A`. This is the generic clause
    of I2's `IsReductionOf`, copied.
  - `y ≫ pr₁ = Spec j ≫ Spec(res) ≫ x'`, for the `κ(w)‾`-point `y` of `sf 𝒜` and a ring map
    `j : κ(v) → κ(w)‾`.
- `genPt`, `genMap` (the generic point map of `x`), `vsq` (Mathlib's `ValuativeCommSq`) and
  `sigV` (`σ` restricted to `O_v`, for `σ ∈ D(v)`).

## 4. The remaining named Props: leaf or glue

| Prop | kind | statement (informal) | why true / source |
|---|---|---|---|
| `GoodRedCofinite` | **leaf candidate** (published) | For `A/L`, `L ⊆ ℚ̄` a number field, there is a finite `S` with `PkgI2.HasGoodReduction A (v ∩ L)` for every place `v ∣ p`, `p ∉ S`. | Spreading out to an abelian scheme over `O_L[1/N]`: EGA IV₃ §8 (8.8.2, 8.10.5), EGA IV₄ 17.7.8, openness of geometric connectedness of fibres. Also stated in Serre–Tate 1968 §1 and Milne (Cornell–Silverman 1986) §20. All locators UNVERIFIED. |
| `SmoothGeomConnIntegral` | **leaf candidate** (textbook) | A smooth, quasi-compact, geometrically connected scheme over a field is geometrically integral. | Smooth ⇒ regular ⇒ normal after every field base change. A connected normal scheme with finitely many irreducible components is integral (Stacks 033M-type lemma; EGA IV₂ 6.7-6.8). Locators UNVERIFIED. |
| `RedTorsionQbar` | glue (transport of the leaf I2-Red) | For `m ≥ 1` invertible in `O_w` and any ring isomorphism `j : κ(v) ≅ κ(w)‾` compatible with `O_w`, `RedRel` is a bijection `A(ℚ̄)[m] → Ā(κ(w)‾)[m]` (`∃!` both ways). | This is `PkgI2.ReductionTorsionBijective` (Serre–Tate 1968 §1), moved along `ℚ̄ ≅ L‾` (as `L`-algebras), the universal property of `sf 𝒜`, and `j`. It also needs `O_w` to be a DVR, which holds: a nontrivial valuation ring of a number field. |
| `FExtend` | glue (from the leaf I2-NMP) | There are a ring map `t : O_w → O_w` (it is `σ⁻¹|_{O_w}`) and `F̃ : 𝒜 → 𝒜` over `Spec t`. They satisfy: `t(a)^p ≡ a` mod `𝔪_w`; `F̃` fixes the unit section; and for every lift `x'` of `x`, `Spec(σ|_{O_v}) ≫ x' ≫ F̃` lifts `f x`. | `F` lies over `Spec(σ⁻¹|_L)`, which is forced by `f(x)` being an `L`-point. I2-NMP (`PkgI2.NeronMappingAbelianScheme`, BLR §1.2) extends the `L`-morphism `A → A^{(t)}` to `𝒜 → 𝒜^{(t)}`. The unit section is fixed by separatedness, and the lift identity holds on the generic point. |
| `FrobMorph` | glue (absolute Frobenius; not in Mathlib) | Let `O` be local with `char κ(O) = p`, `𝒜/O` abelian, `t` with `t(a)^p ≡ a`, and `F̃` over `Spec t` fixing `0`. Then there is a `κ(O)`-morphism `β` of `sf 𝒜` fixing `0`, with `β ∘ y = F̃ ∘ y ∘ Spec(z ↦ z^p)` on `κ(O)‾`-points. | Take `β = Fr_Ā ≫ F̄`, where `F̄` is the base change of `F̃` along `Spec t̄` and `t̄ = Frob⁻¹`. Then `β` lies over `Spec(Frob ∘ t̄) = id`. The point formula follows from naturality of the absolute Frobenius. |

The existing kernel leaves behind this glue are I2-Red (L1467 of `Objects.lean`) and I2-NMP
(L1454). Rigidity (Mumford §4 Cor. 1) is no longer an input: mul-rigidity proved it, and the
copy is compiled here.

## 5. Checks on the statements

- **Review.** One read-only model review (no human review) covered all twelve new Props. Its
  verdict: all TRUE as stated, none vacuous. It checked five points specifically:
  - `FExtend`: the direction `residue(t a)^p = residue a` is correct, since `t = σ⁻¹|_{O_w}`.
    The opposite direction would be false.
  - `FrobMorph`: the point formula is consistent with `β` lying over the identity.
  - The quantifier `∀ j` in `ReductionFrobGood` and in `RedRelMul` is harmless. When `j` is not
    compatible with `O_w`, `RedRel` is empty: the structure maps to `Spec O_w` cannot match.
  - `RedTorsionQbar` holds for every compatible `j`, because `O_v` is strictly henselian and
    `𝒜[m]` is finite étale.
  - `GoodRedCofinite` and `SmoothGeomConnIntegral` are standard. Their locators are uncertain.

  The review also made three remarks, none affecting truth: `IsFinite F` and `Surjective F` are
  unused; `Bijective j` is redundant given compatibility; and `FrobMorph` does not need `𝒜` to be
  abelian.
- **Not degenerate.** `RedRel` uses the genuine special fibre (`Over.pullback` along
  `Spec κ(O) → Spec O`) and the genuine generic clause of I2's `IsReductionOf`. The glue Props are
  stated over the kernel's `HasGoodReduction`, `IsAbelianScheme`, Mathlib's `ValuativeCommSq`
  machinery and `IsArithFrob`. None is over an abstract structure invented for the purpose.
- `AlgFrobRedAt` is equivalent to `AlgFrobRed`. It is the special case `g = 1`, and step 1 proves
  the converse.
- `AlgFrobRedGood` is strictly local: one place, no finite set.

## 6. What compiles, what remains

- `scratch/alg-frob-red/AlgFrobRed.lean`: exit 0, no `sorry` (the word appears only in
  comments), 64 standard axiom prints (VERIFIED, log run 23). New declarations: 37 theorems,
  definitions and one instance in namespace `AlgFrobRedRed` (§2, §3).
- **Remains:**
  - `RedTorsionQbar`. To prove it from I2-Red, transport along an `L`-isomorphism
    `L‾ ≅ ℚ̄` (unram-tate's `trPt` recipe), identify I2's `κ(w)`-points of `𝒜` with `sf 𝒜`-points
    (the adjunction, as in `redRelMul`), and prove that `O_w` is a DVR. None of this was attempted.
  - `FExtend`, from I2-NMP. This needs the conjugate model `𝒜^{(t)}` and the fact that
    `Spec ℚ̄ → Spec L` is an epimorphism.
  - `FrobMorph`. Mathlib 4.35 has no absolute Frobenius of an `𝔽_p`-scheme.
  - The two leaf candidates.
- Integration notes:
  - `RedRel` and the Props mentioning `e` need `set_option synthInstance.maxHeartbeats 400000`:
    the `Monoidal` instance of `Over.pullback` along `Spec(O_w → L)` times out at 20000.
  - The assembled file adds Rigidity's Mathlib imports (`Group.Abelian`, `AlgClosed.Basic`,
    `ZariskisMainTheorem`).
  - Inside `open scoped CategoryTheory.Obj`, `IsMonHom e.inv.hom.hom` is not found. The reason is
    that the `MonObj` instance on `(Over.pullback g).obj 𝒜.X` is then `Functor.monObjObj`, not
    the `mapGrp` one. `redRelMul` therefore works at the `mapGrp` type through `pb_symm_mul'`.
