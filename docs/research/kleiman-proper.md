# kleiman-proper: `kleimanPicZeroProper` cannot be removed without a new leaf; phisurj's surjectivity argument already uses properness of `Pic⁰`

Task kleiman-proper, 2026-11-16. Base: wip/leaf-fold33b `0595e253c`. `git merge origin/main` reported "already up to
date". Build: a reflink copy of leaf-fold33b's `.lake/build`, at the same commit. The results log is
`scratch/kleiman-proper/log.md`. This is model work with no human review.

**VERIFIED** means read in a named file on this host, or compiled. **STANDARD** means a published result.
**SPECULATIVE** is marked where used. Theorem numbers given from memory are marked UNVERIFIED.

## 1. Verdict

1. **The target (−1, no new leaf) is not reached, and phisurj's route cannot reach it.** The brief proposed proving
   that `Pic⁰` is proper as the image of `A` under `λ_L` (Stacks 03GN). That needs `dim Pic⁰ ≤ dim A`. phisurj proves
   this bound only for a `Pic⁰` already known to be an abelian variety, so it does not help here. VERIFIED by reading:
   * `PhiSurj.dim_le_of_open0` (`ZInQKernel/Contrib/OneProof/PhiSurjCharZero.lean:304`; general form
     `PhiAmpleIsogenyOpen.lean:369`) bounds `dim B` through `#B[ℓ] = ℓ^{2 dim B}`.
   * That count is the torsion leaf `mumfordTorsionAlgClosed`, applied to `B` as an abelian variety:
     `exists_torsAddEquiv hT B b ℓ`, line 317.
   * `B` is the abelian variety that `PicZeroAbVar0` supplies, with `IsPicZero rep B j`. An `AbVar` carries
     `[IsProper X.hom]` (`ZInQKernel/Contrib/G9/I3Layer.lean:626`). So `B` is proper only because
     `kleimanPicZeroProper` makes it so.
2. **No torsion count can do this without properness.** STANDARD; the examples are textbook.
   * A smooth connected commutative group that is not proper can have the torsion of a smaller abelian variety. In
     characteristic 0, `𝔾_a` has no torsion at all.
   * The universal vector extension of `Â` has dimension `2g` and exactly the torsion of `Â`.
   * So the inputs phisurj uses cannot bound `dim Pic⁰` unless the unipotent part is excluded first: the counts
     `B[n] ↪ {translation-invariant c, cⁿ = 1}` with at most `n^{2g}` elements, and Cartier's theorem.
   * Excluding the unipotent part is the cohomological content: `h¹(A, 𝒪_A) = g`, Mumford §13 (UNVERIFIED numbering).
     Equivalently, it is phisurj's missing piece (a), every translation-invariant class lies in the image of `φ_L`,
     for classes in `Pic⁰`.
3. **No other hypothesis in the chain implies it.** VERIFIED by a scan of `docs/one-proof/open-statements.json`.
   No open hypothesis besides the four Picard leaves mentions the Picard functor, the identity component or
   `IsProper`.
4. **The isolated missing input** is the dimension bound `PicZeroDimLeAbVar0` (§3, rated in §5). It is weaker than
   the field: Lean derives it from the field (narrowed) and the chain's leaves. The converse is the brief's argument.
   Its last step is compiled. Two of its steps are not (§3).
5. **Recommendation: keep `kleimanPicZeroProper` as it is.**
   * Replacing it by `PicZeroDimLeAbVar0` trades a printed LEAF for a consequence, and kinds.tsv counts
     `consequence` rows as strict GLUE.
   * Narrowing it to what the chain reads, `KleimanPicZeroProperAbVar0` (abelian varieties, characteristic 0), makes
     the same trade.
   * No fold is proposed.

## 2. Where the chain reads the field (VERIFIED, read)

There is exactly one reader: `TailZ53.lean`'s `openAddedLeaves22PZ_of_OpenAddedLeaves23`, through
`PicZeroChar0.picZeroAbVar0_of_leaves h1 h2 h3`. That theorem uses `h3` only through
`picZeroProperAt_of_kleiman h3 K` at fields `K` of characteristic 0 (`PicZeroAbVarCharZero.lean:142-205`). So the
chain needs only

```lean
def KleimanPicZeroProperAbVar0 : Prop := ∀ (K : Type) [Field K] [CharZero K], PicZeroChar0.PicZeroProperAt K
```

This is `Pic⁰` proper for abelian varieties in characteristic 0. `picZeroAbVar0_of_narrowed` (compiled) proves
`PicZeroAbVar0` from it, together with `picLocFinType`, `identityComponentLFT` and Cartier's theorem.

The `B` of `IsPicZero` is used in every lemma of phisurj's proof of `PhiAmpleIsogeny0`, not only in step 4. All of
the following are typed over `B : AbVar K` with `IsPicZero`:

* `exists_hom_comp_eq_phiL` (TailZ24.lean:136, rigidity into `B`);
* `finite_ker_pts` (MumfordKLFinite.lean:278);
* `finiteOfFiniteKerPts` (PicDictionary.lean:1317, which uses `IsProper B`);
* `picZeroPtsTranslInv_of_leaves` (PicDictionary.lean:1952);
* `phi_mul0`, `mumfordBundle_eq_one_of_isTI0` and `mumfordMulNPicZeroAC0_of_open`, and through them `card_isDT_le0`
  (PhiSurjCharZero.lean:117-300).

Steps 1–3 could in principle be redone with the open subgroup `V` in place of `B`: they need only a separated group
receiving `φ_c` as a homomorphism. That is SPECULATIVE; the rigidity lemma would have to be re-proved for a target
that is not proper. Step 4 is the essential use, as explained in §1.

## 3. Lean (`scratch/kleiman-proper/KleimanProper.lean`; VERIFIED: compiled, standard axioms, `compile_out.txt`)

| declaration | statement |
|---|---|
| `KleimanProper.KleimanPicZeroProper` | verbatim copy (with `IsNormalScheme`); `kleimanPicZeroProper_eq : _ = PicFix.KleimanPicZeroProper := rfl` |
| `KleimanPicZeroProperAbVar0`, `kleimanPicZeroProperAbVar0_of` | the narrowed form the chain reads; a consequence of the field |
| `picZeroAbVar0_of_narrowed (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3 : KleimanPicZeroProperAbVar0) : PicZeroAbVar0` | the chain's only use, from the narrowed form |
| `PicZeroDimLeAbVar0` | for `A : AbVar K`, `CharZero K`, every representing `P` and every open `V` whose underlying set is the identity component: `topologicalKrullDim V ≤ topologicalKrullDim A.X.left` |
| `dim_eq_of_isPicZero` | `IsPicZero rep B j → topologicalKrullDim V = topologicalKrullDim B.X.left` (homeomorphism through `j`) |
| `picZeroDimLeAbVar0_of_narrowed (h1 : PicRepresentableAbVar) (hL hI) (hT : MumfordTorsionAlgClosed) (h3 : KleimanPicZeroProperAbVar0) : PicZeroDimLeAbVar0` | the core is weaker than the field, given the chain's leaves (phisurj's `dim_le_of_open0`) |
| `isProper_of_surjective` | Stacks 03GN shape: `IsProper (f ≫ g)`, `f` surjective, `g` separated and locally of finite type, imply `IsProper g` |
| `picZeroProper_of_surjective (hL : PicLocFinType) … (f : A.X.left ⟶ V) (hf : f ≫ V.ι ≫ P.hom = A.X.hom) [Surjective f] : IsProper (V.ι ≫ P.hom)` | the brief's last step. `P` is separated by the vendored `GrpObj.isSeparated_hom` (CloudW07 `Group/Separated.lean`) |

**What the converse (core ⇒ narrowed field) still needs. None of it is compiled.** It is the brief's argument, with
the dimension bound supplied by the core:

1. **An ample class on `A` over `K`.** The tree has one only for algebraically closed `K`
   (`exists_isAmple_of_isAlgClosed`, TailZ24.lean:434). The alternative is to prove properness over `K̄` and descend
   it. That needs two pieces: the base change of `P` represents `Pic_{A_K̄/K̄}`, with identity components matching;
   and fpqc descent of `IsProper`.
2. **`λ_L : A → V`.** It is `φ_L` lifted into `V` (`A` is connected and `φ_L(0) = e`). It must be shown locally
   quasi-finite, which means `finite_ker_pts` and `finiteOfFiniteKerPts` re-proved for the target `V` instead of `B`.
3. **Surjectivity.** phisurj's `surjective_of_dim_le` with the core's bound, then `picZeroProper_of_surjective`.

## 4. Other routes checked

* **Homotopy invariance (vendored).** CloudW07's `nonempty_iso_pullback_lift_of_isAlgClosed`
  (`Picard/AffineSpaceRigidity.lean:349`, Stacks 0BEH; proved, not a leaf) shows that line bundles on `X ×_k D(f)`
  have isomorphic pullbacks at any two `k`-points, for `X` integral with UFD stalks. It forbids nonconstant maps from
  opens of `𝔸¹` into `Pic`, so `Pic⁰` contains no `𝔾_a` and no `𝔾_m`. Two inputs are missing before it gives
  properness:
  * that the stalks of `A` are UFDs, i.e. regular local implies UFD (Auslander–Buchsbaum; Mathlib 4.35 has only
    `RingTheory/RegularLocalRing/Defs` and `Polynomial`);
  * "a smooth connected commutative group over `k̄` with no rational curves is proper", which is Chevalley's
    structure theorem plus Borel's lemma that a nontrivial connected linear group contains `𝔾_a` or `𝔾_m`.

  None of these is in the tree, so this route costs at least two new printed leaves plus glue. Not recommended.
* **Valuative criterion.** Extending line bundles from `A_K` to `A_R` needs divisor theory on `A_R`, and Mathlib's
  criterion quantifies over all valuation rings, not only DVRs. Not pursued.
* **Replacing `Pic⁰` in the readers by the image `λ_L(A)`.** This would avoid properness. But
  `exists_hom_comp_eq_phiL` factors `φ_{L'}` through `B` for every `L'`, and `WeilDual.dualEnd` needs `f^*` to
  preserve the image. Both need `λ_L(A) = Pic⁰`, which is the same gap. Not pursued.

## 5. The missing input, rated

* **`PicZeroDimLeAbVar0`: printed form, no.**
  * It is a consequence of Mumford, *Abelian varieties*, §13: `Pic⁰ = Â` is an abelian variety of dimension `g`, and
    `T_0 Â ≅ H¹(A, 𝒪_A)` (numbering UNVERIFIED).
  * It is also a consequence of Kleiman 9.5.4 together with the chain's leaves (compiled,
    `picZeroDimLeAbVar0_of_narrowed`).
  * It is never stronger than the field.
  * It would count as GLUE (kind `consequence`).
* **`KleimanPicZeroProperAbVar0`: printed form, no.** It is Kleiman 9.5.4 restricted to abelian varieties in
  characteristic 0, a consequence of the field.
* **The field itself is fine as stated.** It is not false and not vacuous: an identity component `V` exists by
  `identityComponentLFT`, and the statement is Kleiman 9.5.4 for every representing scheme. It stays a printed LEAF.

## 6. Deliverables

* `scratch/kleiman-proper/KleimanProper.lean` (compiled), `compile_out.txt` and `log.md`.
* No file under `ZInQKernel/Contrib/OneProof/`. Nothing here proves an open hypothesis or reduces one to printed
  leaves, so `#discharges` would match nothing.
* No fold spec. No fold is recommended: the only possible changes trade the LEAF for a GLUE (§1.5).
