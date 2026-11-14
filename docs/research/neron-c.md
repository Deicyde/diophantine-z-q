# neron-c: leaf-fold3 fields `t3` and `t41` (Néron models)

Task neron-c, 2026-11-13. Base: fork main 8ec80711 with origin/wip/leaf-fold3 (f7951690) merged.
Fork main had not moved by the end of the task. Model work, no human review. No existing file was
edited; every Lean deliverable is a new file under `ZInQKernel/Contrib/NeronC/` or `scratch/neron-c/`.
Results log: `scratch/neron-c/log.md`.

Marks: **VERIFIED** means compiled, or read in a file. **STANDARD** means published, with a reference.
**UNVERIFIED** means a theorem number recalled without a source (there is no network here).

## 1. Main result

Neither field is proved outright. Each is reduced, by proved Lean glue, to a published statement
that asks for strictly less than the field. Both reductions are equivalences: the converse
theorems are proved too.

| field | was | now | proved glue |
|---|---|---|---|
| `t3 : PkgI2.NeronMappingAbelianScheme.{0}` (T3 = I2-NMP) | bijectivity of restriction to the generic fibre | `NeronMappingAbelianSchemeSurj` (the surjective half; BLR §1.2 Prop. 8) | the injective half, proved outright from Mathlib |
| `t41 : ZInQ.H5Neron.NeronModelExists` (T41 = N1) | a Néron model that is a `GroupModel` (group scheme, `gen` a group isomorphism) | `NeronSchemeExtensionExists` (a smooth, separated, quasi-compact scheme `N` with `N_L ≅ A_L` such that maps extend; BLR §1.4 Thm. 3) | the group law of `N`, `gen` being a homomorphism, and uniqueness of extensions |

The declarations, exact types (VERIFIED, `lake env lean`, no `sorry`):

```lean
-- ZInQKernel/Contrib/NeronC/NMPInjective.lean  (namespace ZInQ.Contrib.NeronC, universe u)
theorem neronMappingAbelianScheme_injective (K : Type u) [Field K] (O : ValuationSubring K)
    [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme 𝒜] [PkgI2.IsAbelianScheme ℬ] :
    Function.Injective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)
theorem neronMappingAbelianScheme_of_surj (h : NeronMappingAbelianSchemeSurj.{u}) :
    PkgI2.NeronMappingAbelianScheme.{u}
theorem neronMappingAbelianSchemeSurj_of_nmp (h : PkgI2.NeronMappingAbelianScheme.{u}) :
    NeronMappingAbelianSchemeSurj.{u}

-- ZInQKernel/Contrib/NeronC/NeronGroup.lean  (namespace ZInQ.Contrib.NeronC)
theorem neronModelExists_of_extension (h : NeronSchemeExtensionExists) :
    ZInQ.H5Neron.NeronModelExists
theorem neronModelExists_of_scheme (h : NeronSchemeModelExists) : ZInQ.H5Neron.NeronModelExists
theorem neronSchemeExtensionExists_of_neronModelExists (h : ZInQ.H5Neron.NeronModelExists) :
    NeronSchemeExtensionExists
theorem neronSchemeModelExists_of_neronModelExists (h : ZInQ.H5Neron.NeronModelExists) :
    NeronSchemeModelExists
```

The new leaves (exact text):

```lean
def NeronMappingAbelianSchemeSurj : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme 𝒜] [PkgI2.IsAbelianScheme ℬ],
    Function.Surjective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)

def NeronSchemeExtensionExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ (N : Over (Spec (CommRingCat.of (𝓞 L)))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (e : genericFibre L N ≅ (A.baseChange L).X),
      ∀ (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [Smooth Y.hom],
        Function.Surjective fun f : Y ⟶ N =>
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f ≫ e.hom
```

`NeronSchemeModelExists` is the same as `NeronSchemeExtensionExists` with `Function.Bijective`; it
is the intermediate step.

`#print axioms` (VERIFIED; `scratch/neron-c/check_out.txt` and the module builds). Every theorem
below gives `[propext, Classical.choice, Quot.sound]`:
- the T3 theorems: `neronMappingAbelianScheme_injective`, `neronMappingAbelianScheme_of_surj`,
  `neronMappingAbelianSchemeSurj_of_nmp`;
- the general lemmas: `ext_of_isSchemeTheoreticallyDominant_of_isSeparated`,
  `pullback_map_injective`, `grpObjOfNeron`, `isMonHom_of_neron`;
- the T41 theorems: `neronModelExists_of_scheme`, `neronModelExists_of_extension`,
  `neron_extension_injective` and the two converses;
- the non-vacuity lemma `neronSchemeExtension_zero`;
- the check-file theorems `NeronCCheck.t3_of_surj`, `t3_iff`, `t41_of_scheme`, `t41_of_extension`,
  `t41_iff`.

## 2. T3: the injective half is proved

**Mathlib-level lemmas** (`NMPInjective.lean`, VERIFIED):
- `ext_of_isSchemeTheoreticallyDominant_of_isSeparated`. This is Mathlib's
  `ext_of_isDominant_of_isSeparated` with the hypothesis "`ι` scheme-theoretically dominant" in
  place of "`X` reduced and `ι` dominant". Proof: the equalizer of `f, g` over a separated base is
  a closed immersion. Its kernel lies in `ker ι = ⊥`, so it is an isomorphism (Mathlib:
  `IsClosedImmersion.isIso_iff_ker_eq_bot`, `Scheme.Hom.le_ker_comp`).
- `pullback_map_injective`. Base change along a quasi-compact, scheme-theoretically dominant
  `j : T ⟶ S` is injective on maps from a flat `S`-scheme to a separated one. Flatness makes
  `X_T → X` scheme-theoretically dominant (Mathlib: `IsSchemeTheoreticallyDominant.pullbackFst`).
- `isSchemeTheoreticallyDominant_spec_map`. If `φ` is an injective ring map out of a reduced ring,
  then `Spec φ` is scheme-theoretically dominant (via `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`).

**Application** (`neronMappingAbelianScheme_injective`). `𝒜` is smooth, hence flat, over `O`;
`ℬ` is proper, hence separated; `O → K` is injective and `O` is a domain. No reducedness of `𝒜`
is needed. This matters because the special fibre of a smooth scheme being reduced is not in
Mathlib.

**What remains**, `NeronMappingAbelianSchemeSurj`: every `K`-morphism `𝒜_K → ℬ_K` extends.
- **STANDARD.** Bosch–Lütkebohmert–Raynaud, *Néron Models* (Springer, Ergebnisse 21, 1990), §1.2
  Prop. 8: an abelian scheme over a Dedekind scheme (in particular a DVR) is the Néron model of its
  generic fibre. Apply it with the smooth test scheme `Y = 𝒜` (§1.2 Def. 1). Locator UNVERIFIED.
- **Proof in the source.** The valuative criterion at the codimension-one points of `𝒜`, then
  Weil's extension theorem (BLR §4.4 Thm. 1, UNVERIFIED). Neither piece is in Mathlib v4.35:
  rational maps exist (`Scheme.RationalMap`), but not codimension, nor Weil's theorem.
- **Never stronger than the source.**
  - `K` is the fraction field of `O`: a valuation subring that is a DVR is not `K`.
  - `IsAbelianScheme` (proper, smooth, geometrically connected fibres, a `Grp` object) is BLR's
    abelian scheme.
  - The statement concerns all `O`-morphisms of schemes, not only homomorphisms. BLR's mapping
    property is exactly for morphisms of schemes from smooth `Y`.
- **Its use** (VERIFIED, `scratch/leaf-fold3/olean/TailH.lean`, `fExtendGen_of_nmp`): only
  `(hN L (Ow L v) 𝒜 ℬ).2` is used, i.e. this surjective half, at a DVR of a number field.

## 3. T41: the group law and uniqueness are proved

**Abstract construction** (`NeronGroupAbstract.lean`, Mathlib only, VERIFIED). Setting:
- `C`, `D` are cartesian monoidal categories, and `F : C ⥤ D` is any functor;
- `P` is a class of objects of `C` containing `𝟙_` and closed under `⊗`;
- `N` is in `P`, `A` is a group object of `D`, and `e : F N ≅ A`;
- `f ↦ F f ≫ e` is bijective `Hom(Y, N) → Hom(F Y, A)` for every `Y` in `P`.

Results:
- `grpObjOfNeron` puts a `GrpObj` on `N`. It copies the proof of Mathlib's
  `GrpObj.ofRepresentableBy`, restricted to test objects in `P`.
- `isMonHom_of_neron`: if `F` is monoidal, then `e.hom` is a homomorphism for
  `Functor.grpObjObj`.

This is the remark after BLR §1.2 Def. 1 ("the Néron model of a group scheme is a group scheme"),
now a theorem rather than an input.

**Application** (`NeronGroup.lean`, VERIFIED):
- **Setting.** `F = Over.pullback (Spec 𝓞_L ← Spec L)` and `P = smooth over 𝓞_L`. `P` contains
  `𝟙_` (`smooth_tensorUnit`) and is closed under `⊗` (`smooth_tensor`, from base change and
  composition).
- **Uniqueness** (`neron_extension_injective`) is `pullback_map_injective` again: `Y` is smooth,
  hence flat; `Spec L → Spec 𝓞_L` is scheme-theoretically dominant; `N` is separated.
- **Non-vacuity** (`neronSchemeExtension_zero`): the conclusion of the new leaf holds for
  `AbVar.zero K`, from h5-neron's `neronModelExists_zero`.

**What remains**, `NeronSchemeExtensionExists`:
- **STANDARD.** BLR §1.4 Thm. 3: an abelian variety over the field of fractions of a Dedekind
  scheme has a Néron model. Here the Dedekind scheme is `Spec 𝓞_L` and the abelian variety is `A_L`.
  Definition: BLR §1.2 Def. 1, a smooth, separated `S`-scheme of finite type with the mapping
  property for all smooth `S`-schemes `Y`. Locators UNVERIFIED.
- **Never stronger than the source.**
  - Mathlib's `Smooth` includes "locally of finite presentation". With `QuasiCompact` this gives
    finite type, which BLR's definition requires and its theorem provides.
  - The test schemes are all smooth `𝓞_L`-schemes, not only those of finite type, as in BLR Def. 1.
  - The new leaf asks for no group law and no uniqueness. `A : AbVar K` with `K ⊆ L` only enters
    through `A_L`, an abelian variety over `L`.
- **Why it is not reduced further.** neron-lg (`docs/research/neron-lg.md`) reduces N1 to:
  - the local leaves N1-loc and N1-ab and the leaf NL (BLR §1.2 Prop. 4);
  - `AbVarSpreadsOut`, now proved on fork main from three EGA IV leaves;
  - two glue Props, `NeronNearBadPoint` and `NeronGlueAway`. Both are unproved: gluing schemes and
    group schemes along a Zariski cover of `Spec 𝓞_L` is not in Mathlib v4.35.

  Folding that reduction would replace one published leaf by three leaves and two open glue
  Props, so it is not done here.

## 4. Proposed statement change (not applied)

In leaf-fold3's `OpenTextbookLeaves3`, replace two fields:
- `t3 : PkgI2.NeronMappingAbelianScheme.{0}` by
  `t3 : ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{0}`. The old field is recovered by
  `ZInQ.Contrib.NeronC.neronMappingAbelianScheme_of_surj t.t3`.
- `t41 : ZInQ.H5Neron.NeronModelExists` by `t41 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists`.
  The old field is recovered by `ZInQ.Contrib.NeronC.neronModelExists_of_extension t.t41`.

Both new Props are over Mathlib and kernel definitions only, so the Contrib theorems apply to
leaf-fold3's verbatim copies. `scratch/neron-c/Check.lean` checks this on verbatim copies
(`t3_of_surj`, `t41_of_extension`).

## 5. Checks

- **Module builds.** `lake build ZInQKernel.Contrib.NeronC.NMPInjective ZInQKernel.Contrib.NeronC.NeronGroup`
  succeeds; `NeronGroupAbstract` builds as their import. The only warnings are linter warnings
  about `letI`.
- **Single-file check.** `scratch/neron-c/assemble.py` writes `scratch/neron-c/Check.lean`. It
  slices the kernel text of T3 and T41 verbatim into the fresh namespaces `NeronCCheck.PkgI2` and
  `NeronCCheck.H5Neron`, then applies the reductions to the copies. `lake env lean scratch/neron-c/Check.lean`
  exits 0, no `sorry`, and all 9 `#print axioms` lines are the standard three (VERIFIED, about 5 s
  over the built modules).
- **Verbatim check.** `python3 scratch/neron-c/py/verbatim_check.py` prints `ALL OK`
  (`scratch/neron-c/py/verbatim_check_out.txt`). The kernel text of T3 and T41 and of the
  declarations they use (`IsAbelianScheme`, `GroupModel`, `genericFibre`,
  `GroupModel.IsNeronModel`, `AbVar`) occurs verbatim in leaf-fold3's `Leaves3.lean`. T3 and T41
  occur verbatim in `Check.lean`.
