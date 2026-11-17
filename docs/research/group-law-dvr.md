# group-law-dvr: *GIT* Thm 6.14 over a DVR reduced to Néron models over a DVR plus one comparison step; `mumfordGroupLawConn` narrowed, not removed

Task group-law-dvr, 2026-11-16. Base wip/group-law 680165b2, merged with origin/main c1e4ed1b (TailZ45, leaf-fold32
dictionary fold). Results log: scratch/group-law-dvr/log.md. Model work, no human review.

Marks: **VERIFIED** means compiled, or read in a named file on this host. **STANDARD** means published mathematics
with a reference. **SPECULATIVE** means judgement. **UNVERIFIED** marks a theorem number recalled without a source
(no network).

## 1. Verdict

**Target missed: `mumfordGroupLawConn` is not removed with no new leaf (no −1).** `MumfordGroupLawDVR` (*GIT*
Thm 6.14 over a discrete valuation ring) is **not** proved outright. The suggested input does not apply:
`neronSchemeExtensionExists` gives Néron models only over rings of integers `𝓞_L` of number fields, never over the
DVRs the chain needs, which are local rings of curves over `ℚ` (§3). No other open field gives Néron models over a
general DVR or group laws on families.

**Main result (VERIFIED, no `sorry`, standard axioms).** `MumfordGroupLawDVR` follows from:
* the Néron existence theorem over a DVR, a printed leaf;
* one comparison step, a named glue Prop.

```lean
theorem ZInQ.Contrib.GroupLawNeron.mumfordGroupLawDVR_of_neron
    (hN : NeronSchemeExtensionDVR) (hI : NeronGoodModelIso) : ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
```

File: `ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean` (new; 207 lines).
* `NeronSchemeExtensionDVR` (LEAF, printed form) is Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.4 Thm 3 at
  `S = Spec R` (numbers UNVERIFIED). It is the DVR case of `NeronSchemeExtensionDedekind`, the same theorem over any
  affine Dedekind scheme.
* `NeronSchemeExtensionDedekind` also implies the existing textbook field
  (`neronSchemeExtensionExists_of_dedekind : NeronSchemeExtensionDedekind → NeronC.NeronSchemeExtensionExists`, the
  case `D = 𝓞_L`). So one form of BLR 1.4 Thm 3 serves both uses.
* `NeronGoodModelIso` (GLUE, not a print): if `F` is as in the leaf (proper smooth over a DVR `R`, every field fibre
  an abelian variety) and `N` is smooth and separated over `R`, then a morphism `ψ : F → N` that is an isomorphism on
  generic fibres is an isomorphism. Its proof needs van der Waerden's purity theorem or fibre-dimension theory; none
  is in Mathlib 4.35 or the tree (§4).

With group-law's `qmFamilyGroupLaw_of_dvr`, the chain's use of the field follows: `qmFamilyGroupLaw_of_neron`,
`qmFamilyGroupLaw_of_neronDedekind`.

**Folds** (§5; both compiled in an olean overlay outside the repository; no file under `ZInQKernel/` other than the
new contribution was edited):

| fold | ORL28 fields replacing `mumfordGroupLawConn` | count | status |
|---|---|---|---|
| F1 narrowing | `mumfordGroupLawDVR : MumfordGroupLawDVR` (LEAF, printed form, implied by the old field: `dvr_of_conn`) | 0 | VERIFIED (overlay) |
| F2 Néron | `neronSchemeExtensionDedekind` (LEAF, printed form) + `neronGoodModelIso` (GLUE) | +1 field; GIT 6.14 gone | VERIFIED (overlay) |

F1 is group-law's narrowing, updated to TailZ45. F2 removes *GIT* 6.14 from the literature list. Its leaf is the
printed generality of BLR 1.4 Thm 3, which also proves the textbook field `neronSchemeExtensionExists`. So a
follow-up cross-bundle fold can delete that field (net: one LEAF fewer, one GLUE more). Neither fold is the −1 the
task asked for.

## 2. The field on the merged tree (VERIFIED)

* `HDec.HSyn.OpenResearchLeaves28.mumfordGroupLawConn : DictModels.MumfordConn.MumfordGroupLawConn`
  (`OneProof/H/TailZ45.lean:58`). Its only reader is TailZ45:85,
  `mumfordGroupLaw := mumfordGroupLaw_of_conn n.mumfordGroupLawConn`. That line fills
  `OpenResearchLeaves27.mumfordGroupLaw : MumfordRigidity.MumfordGroupLaw`, the field type of generations 14 to 27.
* scratch/group-law-dvr/ClosureCheck.lean (closure_check.txt) lists the users in `frozenTarget`'s closure of
  `MumfordGroupLaw` and `qmFamilyGroupLaw_of_groupLaw`, outside the bundle structures:
  * `exists_qmAbScheme_gl`;
  * `x6Rows_of_open14` and `researchLeaves9_of_open14` (TailZ23);
  * `DCY3Used.y3Connected_of_leaves` (TailZ34).

  The only user of `mumfordGroupLaw_of_conn` is `openResearchLeaves27_of_OpenResearchLeaves28`. So, as on
  group-law's base, the chain needs only `QMFamilyGroupLaw`. `MumfordGroupLawDVR` is not in the closure.

## 3. Why `neronSchemeExtensionExists` does not give the extension (VERIFIED, read)

`ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (`Contrib/NeronC/NeronGroup.lean:82`) quantifies over an abelian
variety `A/K` and a **number field** `L ⊇ K`. It gives a Néron model of `A_L` over `𝓞_L`. The chain's group law is
needed (group-law's `mumfordGroupLawCurve_of_dvr`) at the local rings `Γ(S,V)_𝔭` of a proper smooth curve `S/ℚ` at
closed points. These rings are DVRs that contain `ℚ`, with residue fields finite over `ℚ`. `𝓞_L` is not local, and no
base change turns a Néron model over `𝓞_L` into one over a DVR containing `ℚ`. Over such a DVR, the generic fibre of
`F` is an abelian variety over the function field of `S`, not over a number field. The field is therefore unusable
here. No other open field of the bundles gives Néron models over a general DVR or group laws on families (OPEN.md,
VERIFIED by reading):
* `blr_7_2_1` presupposes the Néron models;
* `raynaudSemistableSHOr` and `sga7_IX_3_3_SHpre` work over strictly henselian traits, with a given model.

## 4. The reduction (VERIFIED)

### Statements

* **`NeronSchemeExtensionDedekind`** (LEAF). For every Dedekind domain `D`, fraction field `L` and `A : AbVar L`, there
  is `N → Spec D` that is smooth, separated and quasi-compact, with `ε : N_L ≅ A`. For every smooth `Y → Spec D`, the
  map `f ↦ f_L ≫ ε` from `Hom_D(Y, N)` to `Hom_L(Y_L, A)` is surjective.
* **`NeronSchemeExtensionDVR`** (LEAF): the same for `D = R` a DVR (`dvr_of_dedekind`).
* **`NeronGoodModelIso`** (GLUE): stated in §1.

### Proof of `mumfordGroupLawDVR_of_neron`

Let `R` be a DVR, `K = Frac R`, `s₀ : Spec K → Spec R`, and `F, e` as in the leaf.
1. The fibre hypothesis at `s₀` gives `A : AbVar K` with `g : A → F` a pullback square. Hence an isomorphism
   `φ : F_K ≅ A` of `K`-schemes (`fibreIso`).
2. The leaf gives `N` and `ε : N_K ≅ A`. Extensions into `N` are unique (`NeronC.pullback_map_injective`, since
   `Spec K → Spec R` is scheme-theoretically dominant and `N` is separated). So `N` has the full mapping property for
   smooth test schemes, and `NeronC.grpObjOfNeron` (neron-c) puts a group law on `N`.
3. `F` is smooth, so `φ` extends to `ψ : F → N` with `ψ_K ≫ ε = φ`. Then `ψ_K` is an isomorphism, and the glue
   makes `ψ` an isomorphism.
4. The group law on `F` is `GrpObj.ofIso (asIso ψ).symm`. Its identity is `η_N ≫ ψ⁻¹`. And `η_N = e ≫ ψ`: both are
   `R`-points of the separated `N`, and they agree on `Spec K`. There, `η_N` restricts to the identity of `A` (by the
   construction of the Néron group law), and `e` restricts to the origin of `A` (the fibre hypothesis's
   `(1 : A(K)) ≫ g = s₀ ≫ e`).

### The glue, and why it is not proved here (SPECULATIVE judgement; references UNVERIFIED)

`NeronGoodModelIso` is true. Proof:
1. `N` is flat over `R`, so `N_K ≅ F_K` is dense and `N` is irreducible.
2. `ψ` is proper (`F` proper, `N` separated). So it is surjective, and `ψ_k : F_k → N_k` is a surjection of
   `g`-dimensional varieties. `N` has constant relative dimension `g`, since it is smooth and connected.
3. Hence `ψ` maps the generic point `ξ` of the integral `F_k` to the generic point of `N_k`. There both local rings
   are DVRs of the same function field, so they are equal, and `ψ` is a local isomorphism at `ξ`.
4. By van der Waerden's purity theorem (EGA IV₄ 21.12.12, `N` regular), the locus where the birational `ψ` is not a
   local isomorphism is empty or of pure codimension 1. It lies in `F_k`, so it is empty or equal to `F_k`. It misses
   `ξ`, so it is empty.
5. A proper birational local isomorphism is an isomorphism.

An alternative uses the Néron group law: rigidity makes `ψ_k` a homomorphism, its kernel is trivial, and the
fibrewise criterion makes `ψ` a closed immersion.

Mathlib 4.35 has some of the pieces:
* `IsFinite.of_isProper_of_locallyQuasiFinite`;
* `IsClosedImmersion.iff_isProper_and_mono`;
* `Flat.isIso_of_surjective_of_mono`;
* the quasi-finite locus (`AlgebraicGeometry/ZariskisMainTheorem.lean`).

It has none of the following:
* purity;
* fibre-dimension theory for morphisms of finite type;
* the fibrewise criterion for closed immersions;
* rigidity with group-scheme targets over non-closed fields.

The tree's `infra-smooth-dim` covers smooth schemes over a field only. Each missing piece is days of work, so the glue
stays a named Prop.

## 5. The folds (manual; compiled in an olean overlay, VERIFIED)

Autofold cannot express either fold. No theorem proves the old field type `MumfordGroupLawConn` (connected, possibly
non-reduced bases) from the new fields. As in group-law's narrowing, the field type of the older generations is
narrowed in place. Script: scratch/group-law-dvr/fold/make_patch.py (`F1` or `F2`). Patches: fold/F1-narrowing.patch,
fold/F2-neron.patch. Specs: fold/autofold-F1.json, fold/autofold-F2.json (marked manual).

Edits common to F1 and F2 (15 modules):
1. In OpenResearchLeaves14 to 27 (structures in TailZ23, 25 to 29, 33 to 38, 41 and 44), change the field type
   `_root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` to `_root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR`. Keep
   the name `mumfordGroupLaw`, so every `mumfordGroupLaw := n.mumfordGroupLaw` stays as it is.
2. In TailZ23, add `import ZInQKernel.Contrib.OneProof.MumfordGroupLawRed`. At the three sites in `x6Rows_of_open14`
   and `researchLeaves9_of_open14`, replace `qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw` with
   `qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw`.
3. In TailZ34 (`sixContactMin_of_open28`), replace `y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU`
   with `y3Connected_of_ab_gl (qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw) (y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU)`.

Edits specific to each fold (TailZ45):
* **F1**: field `mumfordGroupLawConn : MumfordGroupLawConn` → `mumfordGroupLawDVR : MumfordGroupLawDVR` (new
  docstring), and `mumfordGroupLaw := n.mumfordGroupLawDVR`.
* **F2**: add `import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron`. Replace the field `mumfordGroupLawConn` with
  `neronGoodModelIso : NeronGoodModelIso` and `neronSchemeExtensionDedekind : NeronSchemeExtensionDedekind`. Set
  `mumfordGroupLaw := mumfordGroupLawDVR_of_neron (dvr_of_dedekind n.neronSchemeExtensionDedekind) n.neronGoodModelIso`.

## 6. Fold check (VERIFIED, 11-16 ~16:05–16:25)

No file under `ZInQKernel/` was edited for the check. Script: scratch/group-law-dvr/fold/compile_overlay.sh.
* It builds a symlink tree of the worktree's build at /tmp/gldfold/<V>/lib, first on `LEAN_PATH`.
* It recompiles the 42 modules of `Main`'s import closure downstream of TailZ23 (fold/downstream-modules.txt) in
  topological order with `lean -R <root> -o`.

* **F1**: 42/42 modules, no errors (fold/compile-F1.txt).
  * `Main`: `frozenTarget` depends on `[propext, Classical.choice, Quot.sound]`.
  * fold/FoldCheck.lean (output in foldcheck-F1.txt): `OpenResearchLeaves28` has `mumfordGroupLawDVR : MumfordGroupLawDVR` and no
    `mumfordGroupLawConn`.
  * In `frozenTarget`'s closure: `MumfordGroupLawDVR`, `qmFamilyGroupLaw_of_dvr`.
  * Not in it: `MumfordGroupLawConn`, `mumfordGroupLaw_of_conn`, `MumfordGroupLaw`, `qmFamilyGroupLaw_of_groupLaw`.
* **F2**: F1's overlay, with modules 39–42 (TailZ45 to `Main`) recompiled, no errors (fold/compile-F2.txt).
  * `frozenTarget` has standard axioms.
  * `OpenResearchLeaves28` has `neronGoodModelIso` and `neronSchemeExtensionDedekind`.
  * In the closure: `NeronGoodModelIso`, `NeronSchemeExtensionDedekind`, `mumfordGroupLawDVR_of_neron`,
    `MumfordGroupLawDVR`.
  * Not in it: `MumfordGroupLawConn`, `MumfordGroupLaw`.

The integrator should also update the docstrings of the narrowed fields (unchanged in the patch), and the kinds.tsv and
OPEN.md rows.

### `#discharges` (VERIFIED, scratch/group-law-dvr/discharges.txt)

`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron`
built 14,108 jobs. `#discharges` reports 45 open hypotheses, 6,825 theorems checked, and 14 discharges. One of them
is new:

```
DISCHARGES [OpenTextbookLeaves13.neronSchemeExtensionExists] by ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind
```

That is the widening, from `NeronSchemeExtensionDedekind`. No discharge of `mumfordGroupLawConn` comes from the new
file (expected). All new theorems have axioms `[propext, Classical.choice, Quot.sound]`.

## 7. The new statements, rated

* **`NeronSchemeExtensionDedekind`: printed form.** BLR §1.4 Thm 3 (as recalled: `S` a Dedekind scheme with field of
  rational functions `K`, `A_K` an abelian variety; then `A_K` has a Néron model over `S`). It is stated for affine `S`,
  with "finite type" as smooth plus quasi-compact, and only the existence half of the mapping property (uniqueness is
  automatic and proved). It is over genuine definitions: Mathlib's `IsDedekindDomain`, `IsFractionRing`, `Smooth`,
  `IsSeparated`, `QuasiCompact` and `Over.pullback`, and the kernel's `AbVar`. Reading risk: the theorem number
  (UNVERIFIED), and whether BLR's "Dedekind scheme" allows dimension 0. The field case is trivial (`N = A`), so either
  reading gives this statement.
* **`NeronSchemeExtensionDVR`: printed form**, the DVR case of the above.
* **`NeronGoodModelIso`: GLUE**, not a printed statement. It is true (§4), and to be proved by the project. Its proof
  needs van der Waerden purity (EGA IV₄ 21.12.12, a printed theorem, UNVERIFIED number) or fibre-dimension theory.
* **`MumfordGroupLawDVR`** (unchanged from group-law): printed form, the field's narrowing used by F1.

## 8. What remains

* `NeronGoodModelIso` in Lean (§4), which would make F2 a removal of *GIT* 6.14 with no glue left.
* The cross-bundle follow-up of F2: replace OpenTextbookLeaves13's `neronSchemeExtensionExists` by
  `neronSchemeExtensionExists_of_dedekind` of the research field. Not compiled. Note that neron-ext is working on that
  field.
* Neither fold has had an integration build or an OPEN.md/kinds.tsv regeneration.
