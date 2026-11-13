# tau-n1n2: the Néron leaves N1 and N2

Status: research note (task tau-n1n2, 2026-11-13).
- **Lean:** `scratch/tau-n1n2/N1N2.lean` (about 480 lines). It imports only
  `ZInQKernel.HDecomp.Faltings.H5BaseChange` and was compiled with `lake env lean`. There is no
  `sorry` and no `axiom`, and all 13 `#print axioms` list only `propext`, `Classical.choice`,
  `Quot.sound`.
- **Results log:** `scratch/tau-n1n2/log.md`.
- **Statements under study:** N1 `NeronModelExists` and N2 `SemistableNeronIdentityComponent` of
  `scratch/h5-neron/Reduction.lean`, which are now in the build at
  `ZInQKernel/HDecomp/Faltings/H5Neron.lean:205` and `:603`. §1 of the Lean file copies them
  verbatim and checks `Iff.rfl` against the build's declarations (`neronModelExists_iff`,
  `semistableNeronIdentityComponent_iff`).
- No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or scratch
  files were edited.

Marks: **VERIFIED** = compiled, or read in Mathlib or the repository. **STANDARD** = published
mathematics with a reference. **SPECULATIVE** = an estimate. **UNVERIFIED** = a locator from
memory (there is no network).

## 0. Main result

**Verdict.**
1. N1 and N2 are true as stated. Both follow from the published theorems cited in their
   docstrings, and neither is vacuous. N2 is not trivially satisfiable (§4.1).
2. Neither N1 nor N2 can be proved in Lean today, not even for elliptic curves or for good
   reduction outside a finite set. Mathlib v4.35 has no Néron models, no abelian schemes and no
   way to construct a nonzero `AbVar` (§2).
3. Both are now **reduced in Lean** to three smaller leaves, each closer to the literal published
   statement, and two glue statements. The reduction is proved and compiles (VERIFIED):

```lean
theorem ZInQ.TauN1N2.n1_n2_of_leaves
    (hloc1 : LocalNeronModelExists)          -- leaf N1-loc: BLR §1.4 Thm 3 over a DVR O ⊂ L
    (hab   : AbelianSchemeIsNeron)           -- leaf N1-ab:  BLR §1.2 Prop 8
    (hloc2 : LocalSemistableIdentityComponent) -- leaf N2-loc: SGA 7 IX 3.6 + 3.3, local form
    (hg1   : NeronLocalToGlobal)             -- glue: spreading out + gluing (BLR §1.4 proof)
    (hg2   : SemistableLocalToGlobal) :      -- glue: finitely many bad places, compositum, gluing
    NeronModelExists ∧ SemistableNeronIdentityComponent
```

Intermediate results, all proved (VERIFIED):

| Lean theorem | statement |
|---|---|
| `neronModelExists_of_self` | N1 ⇐ `NeronModelExistsSelf` (BLR §1.4 Thm 3 literally: `B` over `L`, model over `𝓞_L`) |
| `neronModelExistsSelf_of_local` | `NeronModelExistsSelf` ⇐ N1-loc + N1-ab + `NeronLocalToGlobal` |
| `neronModelExists_of_local` | N1 ⇐ N1-loc + N1-ab + `NeronLocalToGlobal` |
| `isMonHom_of_reflect` | general lemma: after a monoidal functor `F`, if `F φ` is compatible with monoid morphisms `g_M`, `g_N` and maps `𝟙 → N` and `M ⊗ M → N` are determined by `F(-) ≫ g_N`, then `φ` is a monoid morphism |
| `isMonHom_of_neron` | an isomorphism of Néron group models that is compatible with `gen` is a group isomorphism |
| `semistableNeronIdentityComponent_of_some` | N2 ⇐ N2 with "some Néron model `𝒩'`" in place of "every Néron model `𝒩'`" (the converse holds given N1: `some_of_semistableNeronIdentityComponent`) |
| `semistableNeronIdentityComponent_of_local` | N2 ⇐ N1 + N1-ab + N2-loc + `SemistableLocalToGlobal` |
| `localNeronModelExists_zero`, `neronLocalToGlobal_zero` | the local leaf's conclusion and the glue's conclusion hold for the zero abelian variety |

## 1. What exists (VERIFIED by search on this host)

- **Mathlib v4.35** (`.lake/packages/mathlib`). No file mentions Néron models (`grep -ri neron`
  finds nothing). For abelian varieties there is only
  `AlgebraicGeometry/Group/Abelian.lean`: a proper, geometrically integral group scheme over a
  field is commutative. There are no abelian schemes, no spreading out of group schemes, and no
  identity component of a group scheme over a base.
- **The project.** `ZInQKernel/HDecomp/Objects.lean:393` says no nonzero `AbVar` can be built in
  Mathlib v4.35. Weierstrass curves exist only as sets of points, not as `GrpObj`s in
  `Over (Spec K)`. Already proved in the build (`H5Neron.lean`, from h5-neron) are the
  consequences of the mapping property: `NeronProp.lift`, `NeronProp.uniqueIso`, products
  (`NeronProp.tensor`), and N1 and N2 for the zero abelian variety. `TextbookLeaves.t3`
  (`NeronMappingAbelianScheme`) states the mapping property only when the test scheme is itself
  an abelian scheme over a DVR.
- **Anthropic FLT project.** There is no copy on this host, and fetching one would need the
  network. prereq-survey lists two files there:
  `Def_AlgebraicGeometry_NeronModelUniquenessUpToIsomorphism.lean` and
  `…NeronModelEndomorphismExtension.lean`. By their names (the files were not read; SPECULATIVE)
  these are uniqueness up to isomorphism and the extension of endomorphisms. Both are formal
  consequences of the mapping property, which the project has already proved (`uniqueIso`,
  `lift`). Neither name suggests existence.
- **ATLAS / Tau Ceti indexes** (`~/atlas/index`). For elliptic curves they contain the easy
  direction of Néron–Ogg–Shafarevich (`MathlibExt…NeronOggShafarevich`) and Néron–Tate heights.
  There are no Néron models.

## 2. Why no case of N1 can be proved now

- **Elliptic curves first.** To prove N1 for an elliptic curve, one must first have the curve as
  an `AbVar`: a proper smooth geometrically integral `GrpObj` over `Spec K`. That needs the
  projective closure of a Weierstrass equation as a scheme and the group law as a morphism of
  schemes, neither of which is in Mathlib (VERIFIED, Objects.lean:393). One must then build its
  Néron model. That is the smooth locus of the minimal regular proper model (BLR §1.5 Prop 1,
  UNVERIFIED), which needs regular models of arithmetic surfaces, or an explicit gluing driven by
  Tate's algorithm. None of this exists.
- **Good reduction outside `T`.** N1 is consumed once, by `TextbookLeaves.t41` in
  `heightAdditivity_of_h5neron` (scratch/h-decomposition/Leaves.lean:33766, VERIFIED). There it
  is applied to arbitrary factors `A`, `Z` of `J₁(N)` over every finite extension `E.L`. These
  have bad reduction at the primes dividing `N`, so the decomposition cannot avoid local Néron
  models at bad primes. With good reduction outside `T`, the primes outside `T` are covered by an
  abelian scheme (N1-ab) and the primes in `T` need N1-loc. This is exactly the split of §3.
- **Good reduction everywhere** (an abelian-scheme model over `𝓞_L`). This case is the leaf N1-ab
  (BLR §1.2 Prop 8). Its proof needs Weil's extension theorem for rational maps into smooth group
  schemes (BLR §4.4 Thm 1, UNVERIFIED), which is also absent from Mathlib.

## 3. N1: the reduction (proved)

`NeronModelOver R L B` (VERIFIED, §2 of the Lean file) is a Néron model of `B : AbVar L` over any
ring `R → L`, following BLR §1.2 Def. 1. It is a smooth, separated, quasi-compact `GrpObj` over
`Spec R`, together with a group isomorphism `gen` from its generic fibre to `B.X` and the Néron
mapping property for every smooth `R`-scheme. For `R = 𝓞_L` and `B = A_L`, its fields are
literally those of `GroupModel A L` and `IsNeronModel` (`NeronModelOver.toGroupModel`, which
needs no isomorphism transport).

| name | kind | statement | source |
|---|---|---|---|
| `NeronModelExistsSelf` | leaf (equivalent to N1) | every `B : AbVar L`, `L` a number field, has a `NeronModelOver (𝓞 L) L B` | BLR §1.4 Thm 3 (UNVERIFIED locator), literally, with `R = 𝓞_L` |
| `LocalNeronModelExists` (N1-loc) | leaf | the same over every discrete valuation ring `O ⊂ L` (a `ValuationSubring L` with `IsDiscreteValuationRing`; these are the `𝓞_{L,𝔭}`) | BLR §1.4 Thm 3 for `R = O`. In BLR the local case is §1.3 Cor. 2 (strictly henselian) followed by étale descent (§6.2) (UNVERIFIED) |
| `AbelianSchemeIsNeron` (N1-ab) | leaf | a smooth proper `GrpObj` over a Dedekind domain `R` with fraction field `L`, with generic fibre identified with `B`, has the Néron mapping property | BLR §1.2 Prop 8 (UNVERIFIED) |
| `NeronLocalToGlobal` | glue (assumes N1-ab) | Néron models over every DVR `O ⊂ L` give one over `𝓞_L` | the proof of BLR §1.4 Thm 3: spread `B` out to an abelian scheme over `𝓞_L[1/f]` (EGA IV §8), which is Néron by N1-ab; spread out the finitely many local models and glue; the Néron property is local on the base (BLR §1.2) |

Notes.
- An earlier attempt reduced N1 to `NeronModelExistsSelf` stated with `GroupModel B L`. It had to
  transport along `(B_L)_L ≅ B_L` (the pullback along `Spec.map id`). The kernel timed out
  ("deterministic timeout"), the known pattern for iso chains whose declared types are only
  definitionally equal. Stating the leaf with `NeronModelOver` avoids the transport entirely.
- The glue `NeronLocalToGlobal` takes N1-ab as a hypothesis. Without it, the glue's proof would
  silently use a literature theorem (BLR 1.2/8) at the infinitely many primes of good reduction.
  The glue's proof also uses textbook facts that are not in Mathlib: spreading out (EGA IV §8)
  and the locality of the Néron property (BLR §1.2). The project may promote these to textbook
  leaves.

## 4. N2: audit and reduction

### 4.1 N2 is true and not trivially satisfiable

N2 asks for a group model `𝒰` with open-immersion homomorphisms into `𝒩'` and into the base
change `𝒱` of `𝒩₀`. It does **not** ask that these be compatible with the identifications `gen`
of the generic fibres. One might worry that this makes N2 trivially true, with `𝒰` the
restriction of `𝒩'` to a dense open `V ⊂ Spec 𝓞_{L'}` over which `𝒩' ≅ 𝒱`. That fails. A `GrpObj`
in `Over (Spec 𝓞_{L'})` has a unit section `Spec 𝓞_{L'} → 𝒰`, so `𝒰` meets every fibre. Hence
`𝒰_s` is an open subgroup of both `𝒩'_s` and `𝒱_s` and contains both identity components
(STANDARD). So N2 forces `(𝒩'_s)⁰ ≅ (𝒱_s)⁰` at every place `s` of every `L' ⊇ L₀`. That is a
genuine semistability condition: for additive reduction, the unipotent rank of the special fibre
drops after a further extension (SGA 7 IX 3.3 and 3.6, UNVERIFIED). The same argument shows that
the local leaf below (whose `U` is a `GrpObj` over `Spec O'`) is not trivial: the generic fibre,
open in `Spec O'`, has no section over `O'`.

N2 holds by SGA 7 IX Thm 3.6 (one `L₀` for the finitely many bad places, by composita) and SGA 7
IX Prop./Cor. 3.3. Take `𝒰 = 𝒩'⁰ ≅ (𝒩₀⁰)_{𝓞_{L'}}`, open by SGA 3 VI_B 3.10. All locators are
UNVERIFIED. This agrees with h5-neron's independent review.

### 4.2 One Néron model per `L'` suffices (proved)

`semistableNeronIdentityComponent_of_some`. Given another Néron model `𝒩''`, `uniqueIso` gives
`φ : 𝒩' ≅ 𝒩''` compatible with `gen`, and `isMonHom_of_neron` makes `φ` a group isomorphism (it
uses Néron injectivity on the smooth test schemes `𝟙` and `𝒩' ⊗ 𝒩'`). So open subgroups transfer
(`isOpenSubgroupModel_of_neron`).

### 4.3 Local leaf and glue (proved reduction)

| name | kind | statement | source |
|---|---|---|---|
| `LocalSemistableAt A O` | definition | there is a finite `L₀/K` such that for every DVR `O₀ ⊂ L₀` over `O`, every Néron model `𝒩₀` over `O₀`, every finite `L'/L₀`, every DVR `O' ⊂ L'` over `O₀` and every Néron model `𝒩'` over `O'`, there is a `GrpObj` `U` over `O'` with open-immersion homomorphisms `i : U → 𝒩'` and `j : U → 𝒩₀ ×_{O₀} O'` that agree on the generic fibre after the natural maps to `𝒩₀`: `ιU ≫ j ≫ p = i_{L'} ≫ gen' ≫ π ≫ gen₀⁻¹ ≫ ι₀`, with `π = bcProj : A_{L'} → A_{L₀}` | — |
| `LocalSemistableIdentityComponent` (N2-loc) | leaf | `LocalSemistableAt A O` for every number field `K`, every `A`, and every DVR `O ⊂ K` | SGA 7 IX Thm 3.6 (or Prop 4.7 with `L₀ = K(A[m])`, `m ≥ 3` prime to the residue characteristic) and Prop./Cor. 3.3; SGA 3 VI_B 3.10 (UNVERIFIED) |
| `SemistableLocalToGlobal` | glue (assumes N1, N1-ab) | `LocalSemistableAt A O` at every DVR `O ⊂ K` ⇒ N2's conclusion for `A` | finitely many bad places (spreading out); at good places N1-ab gives an abelian scheme, which commutes with base change; `L₀` = compositum (`H5Neron.compositum`, proved); the compatible local embeddings are restrictions of the canonical map `𝒱 → 𝒩'` and glue to `𝒩'⁰` |

The generic-fibre compatibility in `LocalSemistableAt` is necessary. Without it, local data at
different places are only abstract isomorphisms of identity components and cannot be glued.
Recovering the canonical isomorphism from them would need more of SGA 7 IX, which would make the
glue no longer glue. With the compatibility, the local embeddings are determined by their generic
fibres: `U` is flat, so its generic fibre is schematically dense, and the targets are separated.

## 5. What remains

- **Leaves** (literature; to be formalized or kept as hypotheses): N1-loc, N1-ab, N2-loc. These
  replace N1 (`TextbookLeaves.t41`) and N2. N2 is not consumed by
  `HSyn.sixContactMin_of_leaves` today, since H5 is the leaf `r.h5`. It enters through h5-glue's
  `stableFaltingsHeight_eq_neron_all'` if H5 is later discharged.
- **Glue** (to be proved by the project; needs algebraic geometry missing from Mathlib):
  `NeronLocalToGlobal` and `SemistableLocalToGlobal`. They use spreading out (EGA IV §8), gluing
  of schemes along opens, the identity component of a smooth group scheme over a Dedekind base
  and its compatibility with base change (SGA 3 VI_B), and the locality of the Néron property
  (BLR §1.2).
- **Integration suggestion.** In `TextbookLeaves`, replace `t41 : NeronModelExists` by the three
  leaf fields and add the two glue Props to `GluePieces`. Then
  `neronModelExists_of_local hloc1 hab hg1` supplies `t41`. All declarations are in the single
  file `scratch/tau-n1n2/N1N2.lean`, which imports only `ZInQKernel.HDecomp.Faltings.H5BaseChange`.
