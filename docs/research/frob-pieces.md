# frob-pieces: the open inputs of `FrobTrace.AlgFrobRed`

Task frob-pieces, 2026-11-13. Lean files:
- `ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean`;
- ten Tau Ceti modules vendored unmodified under `ZInQKernel/Contrib/TauCeti/` (see §4);
- `scratch/frob-pieces/`: the parts `part_good.lean`, `part_neron.lean`, `part_final.lean` and
  `part_full.lean`, the scripts `build.sh` and `build_full.sh`, and the assembled files
  `FrobPieces.lean` and `FrobPiecesFull.lean`.

Log: `scratch/frob-pieces/log.md`.

## 1. Result

**`SmoothGeomConnIntegral` is proved outright, and `GoodRedCofinite` is reduced to smaller named
Props.** Both are alg-frob-red's leaf candidates; both statements are copied verbatim.

Combined with task afr-absfrob, which proved `AbsFrob` and derived `FExtendGen` from the kernel
leaf I2-NMP, this gives:

```
theorem FrobPiecesGood.algFrobRed_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed
```

So `FrobTrace.AlgFrobRed` now rests on four inputs:
- neron-lg's existing glue N1-g1 `AbVarSpreadsOut` (spreading out);
- the new leaf candidate `ProperSmoothGenConnected` (Zariski's connectedness theorem);
- the kernel leaf I2-Red;
- the kernel leaf I2-NMP.

The other declarations proved by this task:

```
theorem FrobPieces.smoothGeomConnIntegral : FrobPieces.SmoothGeomConnIntegral
theorem FrobPiecesGood.smoothGeomConnIntegral : AlgFrobRedRed.SmoothGeomConnIntegral
theorem FrobPiecesGood.goodRedCofinite_of (h : AbSchemeSpreadsOut) : GoodRedCofinite
theorem FrobPiecesNeron.goodRedCofinite_of_neron (hsp : AbVarSpreadsOut)
    (hc : ProperSmoothGenConnected) : AlgFrobRedRed.GoodRedCofinite
theorem FrobPiecesGood.algFrobRed_of_spread_nmp (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed
theorem FrobPiecesGood.algFrobRed_of_goodRed_nmp (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed
theorem FrobPiecesGood.tateBridge35_of_neron_nmp (hT : PkgI3.TateModuleFree)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35
theorem FrobPiecesGood.tateBridge35_of_spread_nmp (hT : PkgI3.TateModuleFree)
    (hG : AbSchemeSpreadsOut) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) : G14Bridge.TateBridge35
```

Forms without afr-absfrob's results, which keep `FExtendGen` and `AbsFrob` as inputs, are also
proved: `algFrobRed_of_spread`, `algFrobRed_of_neron`, `algFrobRed_of_four`,
`tateBridge35_of_spread` and `tateBridge35_of_neron`. These are in `FrobPieces.lean`. Helper
lemmas, all proved: `isUnit_intCast_of_coprime`, `pullbackGrp_congr`,
`geometricallyConnected_of_geometricallyIntegral` and `hasGoodReduction_of_base`.

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every one of them (VERIFIED).
See §3.

## 2. The pieces

### 2.1 `SmoothGeomConnIntegral`: proved

```
def SmoothGeomConnIntegral : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (.of k)),
    Smooth f → GeometricallyConnected f → QuasiCompact f → GeometricallyIntegral f
```

The proof is the vendored Tau Ceti instance
`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`:
`{X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [GeometricallyConnected f] : GeometricallyIntegral f`.
It comes from Tau Ceti commit 5a01f5fe, module
`TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral`. Its argument:
- after a field base change, a smooth scheme is locally noetherian with regular local rings;
- regular local rings are domains (`TauCeti.IsRegularLocalRing.isDomain`);
- a connected, locally noetherian scheme whose stalks are domains is integral
  (`TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk`).

Quasi-compactness is not needed.

The import closure has 11 modules, one of which was already vendored. The other ten were copied
unmodified with `tcport.py` (§4). The Contrib file holds a verbatim copy of the `def` and proves
it. In the assembled scratch file, alg-frob-red's own `AlgFrobRedRed.SmoothGeomConnIntegral` is
proved by the same term, since the two `def`s have the same body.

### 2.2 `GoodRedCofinite`: two reductions

`GoodRedCofinite` (alg-frob-red, verbatim) says the following. For an abelian variety `A` over a
number field `L ⊆ ℚ̄`, there is a finite set `S` of primes such that `PkgI2.HasGoodReduction A
(v ∩ L)` holds for every place `v` of `ℚ̄` above a prime `p ∉ S`.

**(a) From `AbSchemeSpreadsOut`** (`goodRedCofinite_of`). `AbSchemeSpreadsOut` is a new leaf
candidate, the published spreading-out statement:

```
def AbSchemeSpreadsOut : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L),
    ∃ (s : Finset L) (𝒜 : Grp (Over (Spec (.of (Subring.closure (s : Set L)))))),
      PkgI2.IsAbelianScheme 𝒜 ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (Subring.closure (s : Set L)) L)))).mapGrp.obj 𝒜 ≅ ObjBridge.toGrp A)
```

Sources (locators UNVERIFIED): EGA IV₃ 8.8.2, 8.10.5 (xii); EGA IV₄ 17.7.8; EGA IV₃ 9.7.7 or
EGA III 4.3 for the geometric connectedness of the fibres.

The proof:
1. Mathlib's `exists_integral_multiples ℤ ℚ s` gives `y ≠ 0` with every `y·a` integral, for
   `a ∈ s`. Take `S` to be the prime factors of `y`.
2. For `p ∉ S` and `w ∣ p`, `y` is a unit of `O_w` (`isUnit_intCast_of_coprime`), and integral
   elements lie in `O_w`. So `ℤ[s] ⊆ O_w`.
3. The base change of `𝒜` along `Spec O_w → Spec ℤ[s]` is an abelian scheme, since proper,
   smooth and geometrically connected are stable under base change.
4. Its generic fibre is that of `𝒜`. This uses `Functor.mapGrpCompIso` and
   `Functor.mapGrpNatIso (Over.pullbackComp _ _).symm`. Monoidality of the natural iso is
   automatic, by `NatTrans.IsMonoidal.of_cartesianMonoidalCategory`.

**(b) From neron-lg's N1-g1 and Zariski connectedness** (`goodRedCofinite_of_neron`). The inputs:
- `AbVarSpreadsOut` and `HasAbelianSchemeAway`, verbatim copies of neron-lg's glue N1-g1
  (`scratch/neron-lg/NeronLG.lean` L449-469, same `open`s; mechanically checked);
- the new leaf candidate below.

```
def ProperSmoothGenConnected : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (f : 𝓞 L) (R : Type) [CommRing R] [Algebra (𝓞 L) R]
    [IsLocalization.Away f R] [Algebra R L] [IsScalarTower (𝓞 L) R L]
    (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProper X.hom →
    GeometricallyConnected
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj X).hom →
    GeometricallyConnected X.hom
```

Why `ProperSmoothGenConnected` is true (STANDARD; EGA III₁ 4.3.1-4.3.4, Hartshorne III 11.3,
locators UNVERIFIED):
- `R` is normal.
- `X_L` is proper, smooth (so geometrically reduced) and geometrically connected, so
  `H⁰(X_L, 𝒪) = L`.
- `f_*𝒪_X` is a finite, torsion-free `R`-algebra inside `L`. It is integral over `R`, so
  `f_*𝒪_X = 𝒪_R`.
- Zariski's connectedness theorem then makes every fibre geometrically connected.
- The fibres are nonempty: the image of `X` is open (flat, finite presentation), closed (proper)
  and contains the generic point.

Mathlib v4.35 has no Stein factorization and no finiteness of `f_*`, so this stays a leaf
candidate.

The proof of `goodRedCofinite_of_neron`:
1. Present `𝓞_L[1/f]` as `Localization.Away f` and get `G`, `gen` and `IsMonHom gen.hom` from
   N1-g1.
2. `G` is geometrically connected by `ProperSmoothGenConnected`, because its generic fibre is
   `≅ A`, which is geometrically integral.
3. Take `S` to be the prime factors of `N = absNorm (span {f})`. Since `N ∈ (f)`
   (`Ideal.absNorm_mem`) and `N` is a unit of `O_w`, `f` is a unit of `O_w`. So
   `IsLocalization.Away.lift` maps `𝓞_L[1/f]` to `O_w`, compatibly with the maps to `L`.
4. Conclude with `hasGoodReduction_of_base`, applied to the group object `Grp.mk G` and the
   group iso `Grp.mkIso' gen`.

### 2.3 `AbsFrob` and `FExtendGen`: done by afr-absfrob

Task afr-absfrob (branch `wip/afr-absfrob`, merged here) proved these two:
- `AlgFrobRedRed.absFrob : AbsFrob`, from Mathlib;
- `AlgFrobRedRed.fExtendGen_of_nmp : PkgI2.NeronMappingAbelianScheme.{0} → FExtendGen`.

This task did not redo them. It only assembles them with its own results (`build_full.sh`).

## 3. What compiles

Every check below exits 0. `sorry` occurs only in comments, and every `#print axioms` line is
`[propext, Classical.choice, Quot.sound]` (VERIFIED).

| file | command | result |
|---|---|---|
| `ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean` | `lake build ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral` | success, 29 s; axioms standard |
| the ten vendored Tau Ceti modules | `lake build ...Morphisms.Smooth.GeometricallyIntegral` | success, 17 s |
| `scratch/frob-pieces/FrobPieces.lean` (`build.sh`) | `lake env lean` | exit 0, about 2 min 15 s, 99 axiom prints (run3.txt) |
| `scratch/frob-pieces/FrobPiecesFull.lean` (`build_full.sh`) | `lake env lean` | exit 0, about 3 min, 114 axiom prints (run_full1.txt) |

Layout checks (VERIFIED):
- `FrobPieces.lean` is a `cmp`-identical copy of `scratch/alg-frob-red/AlgFrobRed.lean`, with
  this task's Contrib import added after its 20 import lines, followed by the parts.
- `FrobPiecesFull.lean` has the same layout, built on a `cmp`-identical copy of
  `scratch/afr-absfrob/AfrAbsFrob.lean`. That file in turn begins with a `cmp`-identical
  `AlgFrobRed.lean`.
- `scratch/frob-pieces/py/verbatim_check.py` confirms these docstrings and `def`s are verbatim in
  this task's copies: `SmoothGeomConnIntegral` (Contrib file and assembled file),
  `GoodRedCofinite`, `HasAbelianSchemeAway` and `AbVarSpreadsOut`.

## 4. Vendored Tau Ceti modules (licence)

Ten modules from Tau Ceti commit 5a01f5fe were copied unmodified by `tcport.py`. The list is in
`scratch/frob-pieces/vendor-new.txt`:
- `AlgebraicGeometry/IrreducibleOfConnectedDomainStalk`;
- `AlgebraicGeometry/Morphisms/Smooth/GeometricallyIntegral`;
- `AlgebraicGeometry/Morphisms/Smooth/Regular`;
- `AlgebraicGeometry/Scheme/RegularLocalRing`;
- `LinearAlgebra/Span/Basic`;
- `RingTheory/KrullDimension/Regular`;
- `RingTheory/LocalRing/MaximalIdeal/Square`;
- `RingTheory/RegularLocalRing/Basic`;
- `RingTheory/RegularLocalRing/Flat`;
- `RingTheory/Smooth/Regular`.

`ThirdParty/TauCeti/NOTICE` has a new entry for them. `diffcheck2.py`: NOTE-ONLY 0,
MOD-UNNOTED 0 (VERIFIED).

## 5. What remains

| Prop | kind | status |
|---|---|---|
| `AbVarSpreadsOut` (neron-lg N1-g1) | glue / candidate textbook leaf (EGA IV₃ 8.8.2, 8.10.5, IV₄ 17.7.8) | open. Mathlib has descent of morphisms (Stacks 01ZC), but not of schemes, properness or smoothness |
| `ProperSmoothGenConnected` | leaf candidate (Zariski's connectedness theorem) | open. Needs Stein factorization |
| `AbSchemeSpreadsOut` | leaf candidate (the two above combined, over `ℤ[s]`) | open. An alternative single input for `GoodRedCofinite` |
| I2-Red, I2-NMP | existing kernel leaves | unchanged |

No statement was changed.

## 6. Checks on the new statements

There was one read-only model review and no human review (2026-11-13, about 10:40). Its
verdicts:

- **`AbSchemeSpreadsOut`: TRUE, non-vacuous.**
  - `L` is the direct limit of the rings `𝓞_L[1/N]`, and each of these is `Subring.closure s`
    for a finite `s` (an integral basis and `1/N`).
  - Spreading out (EGA IV 8.8.2, 8.10.5, 17.7.8) gives a model over some `𝓞_L[1/N]`.
    `ProperSmoothGenConnected` makes it geometrically connected.
  - `Subring.closure s` is never the zero ring.
  - The trivial abelian variety shows the statement is not vacuous.
- **`ProperSmoothGenConnected`: TRUE, non-vacuous.**
  - `f = 0` is vacuous: there is no ring map from the zero ring to `L`.
  - For `f ≠ 0`, `R` is canonically `𝓞_L[1/f]`.
  - An empty `X` fails the hypothesis.
  - The proof goes through `f_*𝒪_X = 𝒪_{Spec R}` and EGA III 4.3. The fibres are nonempty
    because `X → Spec R` is surjective (open, closed, `Spec R` connected).
  - `X = Spec R` shows it is not vacuous.
- **`goodRedCofinite_of_neron`: the argument is sound** (`N = |N(f)| ∈ (f)`, then base change).
- **Docstring wording.** The review flagged four points, all now fixed:
  - `ℤ[s]` need not be normal, so the docstring now names the shrinking to `𝓞_L[1/N]`;
  - `𝒪_{Spec R}`;
  - where torsion-freeness and nonemptiness come from;
  - Hartshorne III 11.3 is for projective morphisms, so it was dropped.

  After the fixes, both assembled files were recompiled (§3).

Neither `goodRedCofinite_of` nor `goodRedCofinite_of_neron` uses the group structure beyond
transporting it. Neither uses `IsDiscreteValuationRing` of `O_w`: `HasGoodReduction` asks only
for a valuation subring.
