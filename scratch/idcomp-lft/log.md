# idcomp-lft results log

Base wip/leaf-fold33b 0595e253c; `git merge origin/main`: already up to date. Build tree: reflink copy of
the leaf-fold33b worktree's .lake/build and lean/.lake/build (same commit, Main.lean byte-identical).

## Target
`PicDict.IdentityComponentLFT` (ZInQKernel/Contrib/OneProof/PicDictionary.lean:2208), field
`identityComponentLFT` of the staged bundle (ZInQKernel/OneProof/H/TailZ53.lean:37).

## Step 1: full proof (scratch/idcomp-lft/IdCompLFT.lean)
- `IdCompLFT.identityComponentLFT_proof : PicDict.IdentityComponentLFT` — VERIFIED (compiled, `lake env lean`,
  21:05 PST 11-16; axioms [propext, Classical.choice, Quot.sound]; `example : PicDict.IdentityComponentLFT :=
  IdCompLFT.identityComponentLFT_proof` checks the exact type).
- No new leaf. Inputs: Mathlib (pointOfClosedPoint, JacobsonSpace, NoetherianSpace, Scheme.Pullback.range_map,
  Functor.grpObjObj for Over.pullback), vendored CloudB3W16 `geometricallyConnected_of_connectedSpace_of_section`
  (Stacks 04KV, rational-section form, proved), vendored CloudW07 `GrpObj.mulLeft`/`isIso_mulLeft_left`.
- Proof outline: (open) loc. noetherian ⇒ connected components open; (mul) V geom. connected (04KV) ⇒ V×_K V
  connected ⇒ μ(V×V) connected ∋ e; (inv) ι(V) connected ∋ e; (geom. irreducible) reduce to K̄-algebraically
  closed L (surjective base change); over L every point of G_L has an open irreducible nbhd: the set S of such
  points is open, nonempty (noetherian affine open has an open subset of a component), contains a closed point
  (Jacobson), translations by rational points (= closed points, Nullstellensatz) act transitively on closed
  points, so S contains every closed point, so Sᶜ (closed, Jacobson) is empty; V_L ⊆ G_L open (base change of
  an open immersion), connected (04KV) ⇒ irreducible.

## Step 2: contributor-kit deliverable
- `ZInQKernel/Contrib/OneProof/IdentityComponentLFT.lean` (18.9 KB; imports PicDictionary, the vendored
  CloudB3W16 ConnectedPoint, CloudW07 Group/Translations and Geometrically/Irreducible; no build-time code):
  `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.IdentityComponentLFT`
  succeeded (14224 jobs, module 5.7 s, no warnings) — VERIFIED.
- `#discharges` (scratch/idcomp-lft/Discharges.lean, output scratch/idcomp-lft/discharges-output.txt):
  `DISCHARGES [OpenAddedLeaves23.identityComponentLFT] by IdCompLFT.identityComponentLFT_proof`,
  `still assumes: []`, axioms [propext, Classical.choice, Quot.sound] — VERIFIED.
- `scratch/idcomp-lft/autofold.json`; `autofold.py --dry-run`: "strict count: 13/18 on 31 -> 12/18 on 30;
  strictest 13/18 -> 12/18"; generated `OpenAddedLeaves24` (= 23 without the field, no new leaf) and
  `sixContactMin_of_open47`; scratch/idcomp-lft/FoldDryRun.lean (line 1 stripped) compiles, axioms standard —
  VERIFIED.
