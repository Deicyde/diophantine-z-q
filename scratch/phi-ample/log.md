# phi-ample results log

Base c1e4ed1b8 (wip/phi-ample). Build tree reflink-copied from ~/dzq-wt/sga3-nbhd (no ZInQKernel diff vs base).

## Route chosen: (a), K(L) finite, proved over any field K inside PhiAmpleIsogeny's context

PhiAmpleIsogeny quantifies over rep, B, j (IsPicZero), L ample, lam with lam ≫ j = phiL rep L, so the
representation of Pic is available without a new hypothesis. Plan (Mumford's argument, irreducible-subset form,
no translation by non-rational points needed):
1. Ker := pullback lam.left η_B.left (closed subscheme of A).
2. Z ⊆ Ker closed irreducible, Zs := reduced induced subscheme (integral; vendored isIntegral_subscheme_vanishingIdeal).
3. i : Zs → A, i ≫ lam = const η_B ⇒ i ≫ phiL = const η_P ⇒ (comp_classify, homEquiv_symm_one, Θ_inj with
   pushforwardUnitUniversal) (1×i)^*Λ(L) = 1 in Pic(A ×_K Zs).
4. Pull back along z ↦ (−z, z): i^*(L ⊗ (−1)^*L) = 1 in Pic(Zs).
5. i^*L and i^*(−1)^*L ample (isAmple_pullback); sections s, t nonvanishing at x; s^m ⊗ t^n ↦ global function f
   with x ∈ D(f); Γ(Zs,O) is a field (Mathlib isField_of_universallyClosed) ⇒ f unit ⇒ Z(s) = ∅ ⇒ Zs affine ⇒
   Zs ≅ Spec(field) ⇒ Z is one point.
6. Ker noetherian, irreducible components points ⇒ Ker finite ⇒ finitely many K̄-points in ker lam ⇒
   finiteOfFiniteKerPts.
Target theorem: PhiAmpleIsogeny from MumfordPhiSurjectiveAC alone (removes mumfordKLFiniteSectionAC).

## Compile log
- KL1.lean (zero-locus lemmas; isAffine_of_ample_mul_eq_one; subsingleton_of_isAffine_of_isField): COMPILED, no errors (11 s warm; first cold run 3.5 min).
- KL2.lean: core lemma subsingleton_of_lam_const (integral closed Z ⊆ A with λ_L|Z = 0 is a point) COMPILED, no errors, no sorry.
- KL3.lean: finite_ker_pts (ker λ_L has finitely many K̄-points, any field, any ample L) and
  phiAmpleIsogeny_of_phiSurjective (h8 : MumfordPhiSurjectiveAC) : PhiAmpleIsogeny COMPILED, no sorry.
  #print axioms: [propext, Classical.choice, Quot.sound] for both (axioms.txt). VERIFIED.
- ZInQKernel/Contrib/OneProof/MumfordKLFinite.lean (copy scratch/phi-ample/MumfordKLFinite.lean): adds
  mumfordKLFiniteAC_of_open, mumfordKLFiniteSectionAC_of_open (L1, L2 ⇒ pic-fix's printed leaf).
  `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.MumfordKLFinite`:
  Build completed successfully (14102 jobs). VERIFIED.
- #discharges (Discharges.lean → discharges.txt): DISCHARGES [OpenAddedLeaves19.mumfordKLFiniteSectionAC] by
  PhiAmple.mumfordKLFiniteSectionAC_of_open, still assumes [T09Pic.PicRepresentableAbVar, T09Pic.PicZeroAbVar]
  (both fields of OpenAddedLeaves19), axioms standard. VERIFIED.
- autofold.json dry run: `strict count: 16/21 on 37 -> 15/21 on 36; strictest 16/21 -> 15/21` (−1, no new leaf).
  FoldDryRun.lean (line 1 stripped) compiles; sixContactMin_of_open39 axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- Same spec on origin/wip/leaf-fold33b (3091ccc77; temporary worktree /tmp/pa-lf33, build tree from ~/dzq-wt/leaf-fold33b,
  removed afterwards): dry run `strict count: 15/20 on 35 -> 14/20 on 34; strictest 15/20 -> 14/20`; the printed module
  (FoldDryRunLF33.lean.txt, .txt so it is not a Lean target) compiles after lake build of MumfordKLFinite there (14158 jobs);
  sixContactMin_of_open40 axioms standard. VERIFIED.
