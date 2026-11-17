# idcomp-lft: `PicDict.IdentityComponentLFT` proved outright

**Result.** The added field `identityComponentLFT : PicDict.IdentityComponentLFT` (the identity component of a
group scheme locally of finite type over a field is open, a subgroup, and geometrically irreducible; SGA 3 VI_A 2.4,
Stacks 0B7R) is proved in Lean, in every characteristic, with **no new leaf**:

* `IdCompLFT.identityComponentLFT_proof : PicDict.IdentityComponentLFT`, in
  `ZInQKernel/Contrib/OneProof/IdentityComponentLFT.lean` (18.9 KB, no build-time code). Axioms: `propext`,
  `Classical.choice`, `Quot.sound` (VERIFIED, compiled).
* `#discharges`: `DISCHARGES [OpenAddedLeaves23.identityComponentLFT] by IdCompLFT.identityComponentLFT_proof`,
  `still assumes: []`, standard axioms (VERIFIED; full output `scratch/idcomp-lft/discharges-output.txt`).
* Fold: `scratch/idcomp-lft/autofold.json` (the field's exact type, proof `_root_.IdCompLFT.identityComponentLFT_proof`).
  `autofold.py --dry-run` reports `strict count: 13/18 on 31 -> 12/18 on 30; strictest 13/18 -> 12/18` and generates
  `OpenAddedLeaves24` (= `OpenAddedLeaves23` without the field) and `HDec.HSyn.sixContactMin_of_open47`. The generated
  module (`scratch/idcomp-lft/FoldDryRun.lean`, line 1 stripped) compiles against `TailZ53`, standard axioms (VERIFIED).
  So the count goes down by 1 and no leaf is added.

After the fold, piczero-char0's `PicZeroChar0.picZeroAbVar0_of_leaves` rests on `picLocFinType` (Kleiman 9.4.8)
and `kleimanPicZeroProper` (Kleiman 9.5.4) only, plus Cartier's theorem (already proved, `cartierSmooth_proof`).

The statement was checked as stated (not changed, no narrower form needed): the proof gives all four clauses for
every field `K`, so no reroute of the characteristic-`0` chain is needed.

## Inputs (all already proved or in Mathlib)

| input | where | status |
| --- | --- | --- |
| connected components of a locally noetherian scheme are open | copied from gt-rigidity (`MumfordRigidity.lean`) | proved |
| a connected scheme with a rational section is geometrically connected (Stacks 04KV, rational-section form) | vendored `AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section` (`Contrib/CloudB3W16Connected/.../ConnectedPoint.lean`) | proved; no finiteness hypotheses |
| `X` geometrically connected, `Y` connected over a field ⇒ `X ×_K Y` connected | Mathlib instance (`Geometrically/Connected.lean`, needs `UniversallyOpen`, automatic over a field; as in gt-sga3's `mul_mem`) | Mathlib |
| closed points of a scheme locally of finite type over an algebraically closed field are rational | Mathlib `pointOfClosedPoint` | Mathlib |
| schemes locally of finite type over a field are Jacobson | Mathlib `LocallyOfFiniteType.jacobsonSpace`, `nonempty_inter_closedPoints` | Mathlib |
| a noetherian space has an open nonempty subset of each irreducible component | Mathlib `NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent` | Mathlib |
| left translation by a rational point is an automorphism | vendored CloudW07 `GrpObj.mulLeft`, `GrpObj.isIso_mulLeft_left` | proved |
| group structure on a base change | Mathlib `Functor.grpObjObj` for `Over.pullback` | Mathlib |

## Proof (as formalized)

Let `G` be a group scheme over `K`, locally of finite type, `e` its unit, `V` the connected component of `e`
(this is `T09Pic.identityComponent G`, since `Spec K` has one point).

1. **Open.** `G` is locally noetherian, so `V` is open.
2. **Geometrically connected.** `V` is connected and the unit section factors through `V`, so `V → Spec K` is
   geometrically connected (Stacks 04KV, rational-section form).
3. **Subgroup.** `V ×_K V` is connected (2.); its image in `G ×_K G` is the set of points whose two coordinates lie in
   `V` (`Scheme.Pullback.range_map`), and its image under `μ` is connected and contains `μ(e, e) = e`, so it lies in
   `V`. The image `ι(V)` of the inverse is connected and contains `ι(e) = e`.
4. **Geometrically irreducible.** For a field `Ω` over `K`, base change along `Ω → Ω̄` is surjective, so it suffices
   that `V_L` is irreducible for `L` algebraically closed. Over `L`:
   * every point of `G_L` has an open irreducible neighbourhood. The set `S` of such points is open; it is nonempty
     (an affine open of `G_L` is a noetherian space, so it contains an open subset of one of its irreducible
     components); `G_L` is Jacobson, so `S` contains a closed point `x₀`; closed points are `L`-rational and the left
     translation by `y·x₀⁻¹` is an automorphism of `G_L` sending `x₀` to `y`, so every closed point lies in `S`; `Sᶜ`
     is closed, and a nonempty closed set contains a closed point, so `Sᶜ = ∅`;
   * `V_L` is an open subscheme of `G_L` (base change of the open immersion `V → G`, by pasting pullback squares), and
     connected (2.); in a connected space where every point has an open irreducible neighbourhood, any two points lie
     in a common open irreducible set, so the space is irreducible.

The argument needs neither smoothness of `G_red` nor Cartier's theorem, so it holds in every characteristic.

## Files

* `ZInQKernel/Contrib/OneProof/IdentityComponentLFT.lean`: the deliverable (namespace `IdCompLFT`).
* `scratch/idcomp-lft/IdCompLFT.lean`: the same proof as a scratch file, with an `example` checking the exact type.
* `scratch/idcomp-lft/Discharges.lean`, `discharges-output.txt`: the `#discharges` run.
* `scratch/idcomp-lft/autofold.json`, `FoldDryRun.lean`: the fold spec and the dry-run module (compiles).
* `scratch/idcomp-lft/log.md`: results log.

New leaves: none.
