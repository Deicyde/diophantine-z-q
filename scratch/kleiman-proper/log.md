# kleiman-proper results log

Base wip/leaf-fold33b 0595e253c; `git merge origin/main`: already up to date. Build: reflink copy of
~/dzq-wt/leaf-fold33b/.lake/build and lean/.lake/build (same commit).

## Step 1: does phisurj's surjectivity argument use properness of Pic⁰? (VERIFIED, read)

YES. Every lemma of phisurj's proof of `PhiAmpleIsogeny`/`PhiAmpleIsogeny0` takes the abelian variety `B` with
`IsPicZero rep B j` supplied by `PicZeroAbVar`/`PicZeroAbVar0` (an `AbVar` carries `[IsProper X.hom]`, I3Layer.lean:626):
- step 4 `dim_le_of_open0` (PhiSurjCharZero.lean:304; general form PhiAmpleIsogenyOpen.lean:369) bounds `dim B` by
  `#B[ℓ] = ℓ^{2 dim B}`: `exists_torsAddEquiv hT B b ℓ` (PhiSurjCharZero.lean:317) applies the torsion leaf
  `mumfordTorsionAlgClosed` to `B` as an abelian variety. This is the essential use: for a smooth connected
  commutative group that is not proper the count fails (G_a: no ℓ-torsion in char 0; the universal vector extension
  of Â has the torsion of Â and dimension 2g), so no torsion count bounds dim Pic⁰ without properness.
- also typed over `B : AbVar K` with `IsPicZero`: `exists_hom_comp_eq_phiL` (TailZ24.lean:136, rigidity into B),
  `finite_ker_pts` (MumfordKLFinite.lean:278), `finiteOfFiniteKerPts` (PicDictionary.lean:1317, uses IsProper B),
  `picZeroPtsTranslInv_of_leaves` (PicDictionary.lean:1952), `card_isDT_le0` (through `mumfordMulNPicZeroAC0_of_open`,
  which gets B from h2: PhiSurjCharZero.lean:141-185), `phi_mul0`.
- The brief's premise "phisurj proved dim Pic⁰ ≤ dim A" holds only for Pic⁰ already known to be an abelian variety.

## Step 2: Lean (scratch/kleiman-proper/KleimanProper.lean) — VERIFIED compiled, standard axioms
- `KleimanProper.KleimanPicZeroProper` verbatim copy; `kleimanPicZeroProper_eq : _ = PicFix.KleimanPicZeroProper := rfl`.
- `KleimanPicZeroProperAbVar0 := ∀ K [Field K] [CharZero K], PicZeroChar0.PicZeroProperAt K` (narrowed: what the chain
  reads); `kleimanPicZeroProperAbVar0_of`; `picZeroAbVar0_of_narrowed (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
  (h3 : KleimanPicZeroProperAbVar0) : PicZeroAbVar0`.
- Core `PicZeroDimLeAbVar0` (dim V ≤ dim A, V the identity component, char 0); `dim_eq_of_isPicZero`;
  `picZeroDimLeAbVar0_of_narrowed (h1 hL hI hT h3) : PicZeroDimLeAbVar0`.
- `lake env lean`: no errors; `#print axioms` both: [propext, Classical.choice, Quot.sound]. (first run: one name
  error `ZInQ.Contrib.AbVarBC.dim_finite` -> `PkgI3.AbVar.dim_finite`, fixed.)
- §4 added: `isProper_of_surjective` (Stacks 03GN shape: `UniversallyClosed.of_comp_surjective`) and
  `picZeroProper_of_surjective (hL : PicLocFinType) … (f : A.X.left ⟶ V) (hf : f ≫ V.ι ≫ P.hom = A.X.hom)
  [Surjective f] : IsProper (V.ι ≫ P.hom)` (separatedness from vendored `GrpObj.isSeparated_hom`, CloudW07).
  Compiled, all three `#print axioms`: [propext, Classical.choice, Quot.sound] (output in compile_out.txt).

## Step 3: other routes checked (VERIFIED by reading unless marked)
- open-statements.json: no open hypothesis other than the four Pic leaves mentions Picard / identity component /
  IsProper (python scan) — no existing leaf implies properness of Pic⁰.
- Vendored CloudW07 `nonempty_iso_pullback_lift_of_isAlgClosed` (Picard/AffineSpaceRigidity.lean:349, Stacks 0BEH):
  line bundles on X ×_k D(f) have isomorphic pullbacks at two k-points, X integral with UFD stalks. This rules out
  nonconstant maps from opens of 𝔸¹ into Pic (no G_a, G_m inside Pic⁰) but (a) needs UFD stalks of A (regular local
  ⇒ UFD, Auslander–Buchsbaum: Mathlib 4.35 has only RegularLocalRing/Defs, Polynomial; not proved) and (b) going
  from "no rational curves" to "proper" needs Chevalley's structure theorem and Borel's G_a/G_m lemma (not in the tree).
- kinds.tsv: `consequence` rows count strict GLUE, so narrowing the field to `KleimanPicZeroProperAbVar0` (a
  consequence) would trade a LEAF for a GLUE: not recommended, no fold written.
