# fold33-review log

Base: wip/leaf-fold33b 667e0aed (origin/main already included, VERIFIED by git merge-base).

## 1. Closure and hypothesis list (scratch/fold33-review/Closure.lean -> Closure-output.txt, open-statements.json)

Build tree: copied (cp -a) from the leaf-fold33b worktree at the same commit 667e0aed (.lake/build and lean/.lake).
`lake env lean scratch/fold33-review/Closure.lean`: 2 min 16 s, no errors (VERIFIED).

- `#print axioms ZInQ.OneProof.frozenTarget`: [propext, Classical.choice, Quot.sound] (VERIFIED).
- 37 open hypotheses (31 H bundle fields + 6 others), identical (field name and full type string) to the lead's
  committed docs/one-proof/open-statements.json at 667e0aed (VERIFIED, python compare).
- Against the list at 3e66542b6 (step 7, before the homfree reroute; 44 hypotheses): removed hP23, hQ, hW, hfx,
  homFreeFiniteAlgClosed, mumfordGroupLawConn, neronSchemeExtensionExists, sga3_VIB_3_10_Nbhd; added only
  neronSchemeExtensionDedekind; type changed only hCM (ShimuraMainCM -> HCMDict.ShimuraThm54). Every other field has
  the same full type string (VERIFIED).
- Constant closure of frozenTarget (through definitions and theorem proofs): 271096 constants. Names matching
  SGA3_VIB_3_10 / MumfordGroupLawConn / GZDecomp.GrossZagierHeegner: none (VERIFIED). Matches present, all derived
  or proved: T5Glue.ShimuraMainCM (derived by shimuraMainCM_of_printed), NeronC.NeronSchemeExtensionExists (derived
  by neronSchemeExtensionExists_of_dedekind), GZOptimal.GrossZagierModuliOptAt/Cd and
  GZStatements.GrossZagierHeegnerCd (derived from hGZ), HomFreeC.HomFreeFiniteC / homFreeFiniteC (proved), the
  projections OpenTextbookLeaves{6..13}HF.homFreeFiniteAlgClosed (field type HomFreeC.HomFreeFiniteC, the proved
  C-form, HomFreeFiniteAlgClosedReroute.lean:729, :2018), and AVB1.HomFreeFiniteAlgClosed._proof_4 (an auxiliary
  proof term, see below).
- Statement closure (types through definitions only) of each open hypothesis: no removed Prop reached; the only hit
  is AVB1.HomFreeFiniteAlgClosed._proof_4 under charPolyIndepOfEllAlgClosed (auxiliary proof shared by the
  elaborator, checked in step 2).

## 2. Vacuity and use checks (scratch/fold33-review/Vacuity.lean -> Vacuity-output.txt)

`lake env lean scratch/fold33-review/Vacuity.lean`: 3 min 20 s, no errors, two linter warnings (VERIFIED).
- `Fold33Review.shimuraThm54_hyps_satisfiable`: every hypothesis of HCMDict.ShimuraThm54 holds at m = 1, e from
  `exists_normalized_embed_any 1`, σ = id, s = 1 (ArtinCond by map_one, as RingClassLattice.lean:1154 does), 𝔞 = κ⁻¹⟨1,i⟩
  with L = pp I, E = L.weierstrassCurve (short, elliptic), ξ = L.toPoint (IsAnalyticUnif by toPoint_isAnalyticUnif).
  Axioms: standard (VERIFIED).
- NeronSchemeExtensionDedekind: hypotheses inhabited at (ℤ, ℚ, PkgI3.AbVar.zero ℚ), ℤ not a field; DVR instances
  ℤ_[p] / ℚ_[p] exist; the leaf gives NeronSchemeExtensionDVR and NeronC.NeronSchemeExtensionExists by instantiation
  (dvr_of_dedekind, neronSchemeExtensionExists_of_dedekind) (VERIFIED).
- GrossZagierAlgOptCd → GZOptimal.GrossZagierModuliOptCd with the proved q-expansion principle
  (grossZagierModuliOptCd_of_alg gamma0QExpansion_proof) (VERIFIED): every instance of gz-optimal's hypotheses gives
  one of the algebraic leaf's (φ^* := phiOf x' y').
- Use sites in the constant closure of frozenTarget (all true, VERIFIED): shimuraMainCM_of_printed,
  eq_scaled_of_isAnalyticUnif, grossZagierFormulaCd_of_alg, grossZagierModuliOptAt_of_alg, GZOptimal.core_selfOptimal,
  PeriodOdd.core_isog, grossZagierFormulaCd_of_etaW32, mumfordGroupLawDVR_of_neron, dvr_of_dedekind,
  neronSchemeExtensionExists_of_dedekind, NeronGoodModelIso (supplied by GoodModelIso.neronGoodModelIso_of_dedekind,
  NeronGoodModelIso.lean:606, from the leaf alone).

## 3. Grep of the copies (reroutes)

NoSGA3Copy.lean, GoodModelIsoCopy.lean, TailZ48-50, HomFreeFiniteAlgClosedReroute.lean: the old names occur only in
docstrings/comments ("field `sga3_VIB_3_10` not copied"), in the superseded bundles OpenResearchLeaves30 (TailZ49,
field mumfordGroupLawConn, not an argument of frozenTarget) and as the HF bundles' field `homFreeFiniteAlgClosed` whose
type is the proved HomFreeC.HomFreeFiniteC. Decisive check is step 1: the 37 hypothesis types equal the pre-fold
ones except neronSchemeExtensionDedekind (new) and hCM (retyped).

## 4. chiD = Kronecker character (py/chiD_check.py -> py/chiD_check-output.txt)

GZDecomp.chiD D n = jacobiSym n |D| equals the Kronecker symbol (D/n) on 30 random (D, n), D odd negative squarefree
≡ 1 mod 4: 0 mismatches (VERIFIED, computed); by hand: Jacobi reciprocity with |D| ≡ 3 mod 4, and (2/|D|) = (D/2).
PARI/cypari2 is not installed on this host (~/pyenv absent), so no PARI check was run.
