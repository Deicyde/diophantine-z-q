# zariski-conn: `ProperSmoothGenConnected` reduced to Zariski's connectedness theorem

Task zariski-conn, branch `wip/zariski-conn`, based on fork main 83651ea9 (w45).

## 1. Main result

frob-pieces' leaf candidate `FrobPiecesNeron.ProperSmoothGenConnected` is now reduced to a single
published theorem: Zariski's connectedness theorem (EGA III₁ 4.3.1 with 4.3.4), stated in its
published form as `ZariskiConn.ZariskiConnectedness`. Everything else is proved from Mathlib v4.35
and vendored Tau Ceti. That includes the whole special-case argument: `R → Γ(X, 𝒪_X)` is
bijective, and therefore `𝒪_{Spec R} ≅ f_*𝒪_X`.

The finiteness of `f_*𝒪_X` (EGA III₁ 3.2.1) is **not** needed. Over a normal base, integrality of
global sections suffices, and Mathlib has it for universally closed morphisms.

### Declarations proved

File `ZInQKernel/Contrib/ZariskiConn/Basic.lean`, module `ZInQKernel.Contrib.ZariskiConn.Basic`,
namespace `ZariskiConn`:

```lean
theorem properSmoothGenConnected_of_zariskiConnectedness (hZ : ZariskiConnectedness.{0}) :
    ProperSmoothGenConnected

theorem appTop_bijective_of_generic {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{0}} (p : X ⟶ Spec (.of R))
    [Flat p] [UniversallyClosed p]
    [GeometricallyIntegral (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop)

theorem app_bijective_of_appTop_bijective {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y]
    [QuasiCompact f] [QuasiSeparated f] (hf : Function.Bijective f.appTop) (U : Y.Opens) :
    Function.Bijective (f.app U)

theorem dedekind_fractionRing_of_away (L : Type) [Field L] [NumberField L] (f : 𝓞 L)
    (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
    [IsScalarTower (𝓞 L) R L] :
    ∃ (_ : IsDomain R), IsDedekindDomain R ∧ IsFractionRing R L
```

The file also proves three helpers: `isSchemeTheoreticallyDominant_Spec_map`,
`bijective_of_isLocalization_away` and `isLocalization_of_eq_basicOpen`.

`ZariskiConn.ProperSmoothGenConnected` is a verbatim copy (docstring, `def`, and the `set_option`
line above it) of `FrobPiecesNeron.ProperSmoothGenConnected` from
`scratch/frob-pieces/part_neron.lean`. `scratch/zariski-conn/py/verbatim_check.py` checks this for
the Contrib file and for the assembled file.

In the assembled single-file check `scratch/zariski-conn/ZariskiConnFull.lean`, namespace
`ZariskiConnGlue`:

```lean
theorem properSmoothGenConnected (hZ : ZariskiConn.ZariskiConnectedness.{0}) :
    FrobPiecesNeron.ProperSmoothGenConnected
theorem goodRedCofinite_of_neron_zariski (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hZ : ZariskiConn.ZariskiConnectedness.{0}) : AlgFrobRedRed.GoodRedCofinite
theorem algFrobRed_of_neron_zariski_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hZ : ZariskiConn.ZariskiConnectedness.{0})
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed
theorem tateBridge35_of_neron_zariski_nmp (hT : PkgI3.TateModuleFree)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hZ : ZariskiConn.ZariskiConnectedness.{0})
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35
```

### `#print axioms`

From `scratch/zariski-conn/run1.txt` (`lake env lean scratch/zariski-conn/ZariskiConnFull.lean`, exit 0),
with line wraps joined:

```
'ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZariskiConn.appTop_bijective_of_generic' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZariskiConn.app_bijective_of_appTop_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZariskiConn.dedekind_fractionRing_of_away' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZariskiConnGlue.properSmoothGenConnected' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZariskiConnGlue.goodRedCofinite_of_neron_zariski' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZariskiConnGlue.algFrobRed_of_neron_zariski_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZariskiConnGlue.tateBridge35_of_neron_zariski_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 122 `#print axioms` lines of the assembled file (frob-pieces' 114 and these 8) are
`[propext, Classical.choice, Quot.sound]`. There are 0 `sorryAx`, and `sorry` occurs only in
comments (VERIFIED).

## 2. The leaf

```lean
/-- **Zariski's connectedness theorem (LEAF; published: EGA III₁ 4.3.1 with 4.3.4; locators
UNVERIFIED).** ... -/
def ZariskiConnectedness : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), IsProper f → IsLocallyNoetherian Y →
    (∀ U : Y.Opens, Function.Bijective (f.app U)) → GeometricallyConnected f
```

This is the published statement (STANDARD; locators UNVERIFIED, since there is no network):
- **Hypotheses.** `Y` is locally noetherian, `f` is proper, and `f_*𝒪_X = 𝒪_Y`. The last
  condition says the canonical map `𝒪_Y(U) → 𝒪_X(f⁻¹U)` is bijective for every open `U`, i.e.
  `𝒪_Y → f_*𝒪_X` is an isomorphism of sheaves.
- **Conclusion.** The fibres are non-empty and geometrically connected.
  - EGA III₁ 4.3.1: `f⁻¹(y)` is connected and non-empty.
  - EGA III₁ 4.3.4: the fibres are geometrically connected.
  - Hartshorne III 11.3 covers the projective case.
- **Non-emptiness is part of the theorem.** If `y ∉ f(X)`, then some open `U ∋ y` misses the
  closed set `f(X)`. Then `𝒪_Y(U) ≅ 𝒪_X(∅) = 0`, so `U = ∅`, a contradiction. This matters
  because Mathlib's `GeometricallyConnected` uses `ConnectedSpace`, which includes non-emptiness.
- **Non-vacuous.** It applies to every proper `f` with `f_*𝒪_X = 𝒪_Y`, for example the identity,
  or the structure map of a smooth proper scheme over `𝓞_L[1/f]` with geometrically connected
  generic fibre (this report).

**Why it stays a leaf.** In EGA its proof uses two inputs: the theorem on formal functions
(EGA III₁ 4.1.5), to rule out a disconnected fibre via idempotents of `lim H⁰(X_n, 𝒪)`, and
étale-local flat base change, to pass from connected to geometrically connected. Mathlib v4.35 has
neither, and has no coherent sheaf cohomology or higher direct images; formal schemes are missing
too. Tau Ceti's current main has sheaf cohomology, higher direct images, cohomology and base
change, and semicontinuity. It has no theorem on formal functions, no Stein factorization and no
Zariski connectedness; grep found none of these (VERIFIED).

**Possible further split, not done.** Write `Z431` for 4.3.1, with conclusion "every fibre
`f⁻¹(y)` is connected and non-empty". Deriving the geometric version from `Z431` needs two inputs:
- étale neighbourhoods realising a given finite separable extension of `k(y)`, together with flat
  base change of `f_*𝒪_X` (Mathlib's `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`);
- "connected over a separable closure ⇒ geometrically connected" (EGA IV₂ 4.5; UNVERIFIED). This
  is missing in Mathlib v4.35 (memory note, grep).

That is a larger development than this task's window allowed.

## 3. Proof of `ProperSmoothGenConnected` from the leaf (all compiled)

Let `R` be a presentation of `𝓞_L[1/f]` with compatible `R → L`, and let `X/R` be smooth and
proper with geometrically connected generic fibre `X_L`.

1. **The base** (`dedekind_fractionRing_of_away`). If `f = 0`, then `R` is the zero ring
   (`IsLocalization.subsingleton`), which has no ring map to `L`; so `f ≠ 0`. Then `R` is a domain
   (`IsLocalization.isDomain_of_le_nonZeroDivisors`) and a Dedekind domain
   (`IsLocalization.isDedekindDomain`), with fraction field `L`
   (`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`).
2. **The generic fibre.** `X_L → Spec L` is smooth (base change) and geometrically connected, so it
   is geometrically integral (Tau Ceti `Smooth.geometricallyIntegral`, vendored by frob-pieces).
3. **Global sections** (`appTop_bijective_of_generic`; this works for any integrally closed domain
   `R` with fraction field `K`, `p` flat and universally closed, and geometrically integral generic
   fibre).
   - `ψ : K → Γ(X_K, 𝒪)` is bijective, by Tau Ceti
     `Scheme.baseRingToGlobalSections_bijective_of_geometricallyIntegral` (vendored here).
   - `j : Γ(X, 𝒪) → Γ(X_K, 𝒪)` is injective. `Spec K → Spec R` is scheme-theoretically dominant
     (dense image over a reduced base, `IsSchemeTheoreticallyDominant.of_isDominant`). Flat base
     change preserves this (`IsSchemeTheoreticallyDominant.pullbackFst`), and then
     `Scheme.Hom.app_injective` applies.
   - `φ : R → Γ(X, 𝒪)` is integral (`isIntegral_appTop_of_universallyClosed`), and
     `j ∘ φ = ψ ∘ (R → K)` by `pullback.condition` and `ΓSpecIso_inv_naturality`.
   - Take `b ∈ Γ(X)` and write `j b = ψ c`. Then `c` is integral over `R`, so `c ∈ R`
     (`IsIntegrallyClosed.algebraMap_eq_of_integral`), and `b = φ c` because `j` is injective.
     Injectivity of `φ` follows from that of `ψ ∘ (R → K)`.
4. **`f_*𝒪_X = 𝒪`** (`app_bijective_of_appTop_bijective`; any affine `Y` and qcqs `f`).
   - On a basic open `D(r)`, `Γ(Y, D(r)) = Γ(Y)_r`. Also `Γ(X, f⁻¹D(r)) = Γ(X)_{f^*r}`, by the qcqs
     lemma `isLocalization_basicOpen_of_qcqs` and `f⁻¹D(r) = D(f^*r)`. So `f.app D(r)` is the
     localization of a bijection, hence bijective (`bijective_of_isLocalization_away`, via
     `IsLocalization.ringEquivOfRingEquiv`).
   - The sheaf map `⟨f.c⟩ : 𝒪_Y ⟶ f_*𝒪_X` is then an isomorphism, by
     `TopCat.Sheaf.isIso_iff_isIso_basis` with the basic-open basis `isBasis_basicOpen`. So it is
     bijective on every open.
5. **Conclusion.** Apply `ZariskiConnectedness` to `X.hom`, which is proper, over the noetherian
   `Spec R`.

frob-pieces' docstring sketch used finiteness of `f_*𝒪_X` (EGA III₁ 3.2.1). Step 3 replaces it
with integrality (Mathlib) and Tau Ceti's computation of `H⁰` of the generic fibre.

## 4. What compiles

| check | command | result |
|---|---|---|
| vendored Tau Ceti closure of `Geometrically.GlobalSections` (11 new modules) | `lake build ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Geometrically.GlobalSections` | success, 26 s |
| `ZInQKernel/Contrib/ZariskiConn/Basic.lean` | `lake build ZInQKernel.Contrib.ZariskiConn.Basic` | success; axioms standard (`scratch/zariski-conn/axioms.lean`) |
| `scratch/zariski-conn/ZariskiConnFull.lean` (`build.sh`) | `lake env lean` | exit 0, 2 min 49 s, 122 axiom prints, all standard (`run1.txt`) |

Layout checks:
- `ZariskiConnFull.lean` is laid out as follows:
  - `src_FrobPiecesFull.lean`, a `cmp`-identical copy of frob-pieces' assembled
    `scratch/frob-pieces/FrobPiecesFull.lean` (which is up to date with frob-pieces'
    `build_full.sh` inputs, `cmp`, VERIFIED);
  - the import `ZInQKernel.Contrib.ZariskiConn.Basic`, inserted after its 21 import lines;
  - then `part_zc.lean`.
- `py/verbatim_check.py` prints `ALL VERBATIM`.
- `diffcheck2.py`: NOTE-ONLY 0, MOD-UNNOTED 0.

## 5. Vendored Tau Ceti modules (licence)

Eleven modules were copied unmodified by `tcport.py` from Tau Ceti commit 5a01f5fe. They are the
closure of `AlgebraicGeometry.Geometrically.GlobalSections` minus what was already vendored; the
list is in `scratch/zariski-conn/vendor-new.txt`. Each has an entry in `ThirdParty/TauCeti/NOTICE`.

## 6. Statement remarks

`ProperSmoothGenConnected` is correct as stated, and nothing in it needs to change. Its docstring
(owned by frob-pieces) mentions finiteness of `f_*𝒪_X`, which the proof here shows to be
unnecessary. A possible wording, not applied, is: "`Γ(X, 𝒪_X)` is integral over `R`
(universally closed) and embeds in `H⁰(X_L, 𝒪) = L` (flat base change), hence equals `R`".
