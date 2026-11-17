# piclft: `PicDict.PicLocFinType` proved outright

**Result.** The added field `picLocFinType : PicDict.PicLocFinType` (for an abelian variety `A` over a field `K`,
every scheme `P` representing the fppf Picard functor `Pic_{A/K}` is locally of finite type over `K`; cited as
Kleiman 9.4.8 / BLR 8.2 Thm 3 / Murre–Oort) is proved in Lean, as stated, in every characteristic, with **no new
leaf**. The Picard scheme is never constructed.

* `PicLFT.picLocFinType_proof : PicDict.PicLocFinType`, in `ZInQKernel/Contrib/OneProof/PicLocFinType.lean`
  (32 KB, 544 lines, no build-time code). It imports `ZInQKernel.Contrib.OneProof.PicDictionary`, where the
  statement is defined, and four vendored modules that are already in the tree. Axioms: `propext`,
  `Classical.choice`, `Quot.sound` (VERIFIED, compiled; `lake build +ZInQKernel.Contrib.OneProof.PicLocFinType`
  37 s on the copied build tree).
* `#discharges` (`scratch/piclft/Discharges.lean`, full output in `scratch/piclft/discharges-output.txt`):
  `DISCHARGES [OpenAddedLeaves24.picLocFinType] by PicLFT.picLocFinType_proof`, `still assumes: []`, standard
  axioms (VERIFIED). The intermediate `PicLFT.picLocFinType_of_spreadOut` is also listed, with
  `still assumes: [PicLFT.PicSpreadOut]`; `PicSpreadOut` is proved in the same file (`PicLFT.picSpreadOut`).
* Fold: `scratch/piclft/autofold.json` (field `picLocFinType`, proof `_root_.PicLFT.picLocFinType_proof`).
  `autofold.py --dry-run` reports `strict count: 12/18 on 30 -> 11/18 on 29; strictest 12/18 -> 11/18` and generates
  `OpenAddedLeaves25` (`OpenAddedLeaves24` without the field: `picRepresentableAbVar`, `kleimanPicZeroProper`)
  and `HDec.HSyn.sixContactMin_of_open48`. The generated module (`scratch/piclft/FoldDryRun.lean.txt`, with line 1
  stripped) compiles against `TailZ54` with standard axioms (VERIFIED, 6 s). So the count goes down by 1 and no
  leaf is added.

After the fold, piczero-char0's `PicZeroChar0.picZeroAbVar0_of_leaves` (via `picLocFinType`, `identityComponentLFT`
and `kleimanPicZeroProper`) rests on **`kleimanPicZeroProper` (Kleiman 9.5.4) only**, plus Cartier's theorem
(already proved, `cartierSmooth_proof`). `identityComponentLFT` was removed by idcomp-lft. The host task
kleiman-proper works on `kleimanPicZeroProper`; this task did not touch it.

The statement was used exactly as stated. No narrower characteristic-0 form was needed. The proof uses about
`A` only that it is proper (stages are quasi-compact and separated) and that `𝒪_T = f_{T*}𝒪_{A_T}` holds
universally (`PicDict.pushforwardUnitUniversal`, already a theorem; it makes the vendored Kleiman 9.2.5
applicable).

## Proof (as formalized)

Write `F = (picardFunctor A.X.hom).obj`, the fppf sheafification of `T ↦ Pic(A ×_K T)` on all `K`-schemes
(CloudW07 `Picard/Sheaf.lean`). Let `rep : F.RepresentableBy P`.

**1. Criterion** (`PicLFT.locallyOfFiniteType_of_fgFactor`; the surjectivity half of EGA IV 8.14.2, restricted to
local finite type). The hypothesis is `FGFactor K X`: every `K`-morphism `g : Spec B → X` equals
`Spec(S ↪ B) ≫ g'` for some finitely generated `K`-subalgebra `S ≤ B` and some `g' : Spec S → X`. From it,
`X → Spec K` is locally of finite type. By `HasRingHomProperty.of_iSup_eq_top` it suffices to treat each affine open
`V ⊆ X`. Give `Γ(V)` the `K`-algebra structure induced by `X.hom`, and apply the hypothesis to
`fromSpec : Spec Γ(V) → X`. This gives `S` and `g'`. Let `J ⊆ S` be the ideal of the closed set
`Spec S ∖ g'⁻¹V`. The image of `Spec Γ(V)` lies in `g'⁻¹V`, so `JΓ(V) = Γ(V)`, that is
`1 = Σ cₜ·t` with `t ∈ J`. Adjoining the finitely many `cₜ` gives a finitely generated `S' ⊇ S` with `JS' = S'`.
So `Spec S' → Spec S → X` lands in `V` and lifts through `fromSpec`. The lift is `Spec ρ` for a ring map
`ρ : Γ(V) → S'`, and `ρ` followed by `S' ↪ Γ(V)` is the identity, because `fromSpec` is a monomorphism. Hence
`S' = Γ(V)`, and `Γ(V)` is finitely generated. (`fg_top_of_factor`; uses only Mathlib.)

**2. Transfer through `rep`** (`PicLFT.picLocFinType_of_spreadOut`). Take a `K`-morphism `g : Spec B → P`, and let
`ξ = rep.homEquiv g ∈ F(Spec B)`. Since `pushforwardUnitUniversal` is proved, `PicDict.Θ` (normalized classes
`≅ F`, the vendored Kleiman 9.2.5) is an isomorphism, so `toPicardFunctor` is surjective and `ξ` is the image of
some `c ∈ Pic(A ×_K Spec B)`. `PicSpreadOut` gives `c = Pic.map (A ×_K Spec(S ↪ B)) c'` with `S` finitely generated.
The naturality of `toPicardFunctor` and of `rep.homEquiv` then give `g = Spec(S ↪ B) ≫ rep.homEquiv.symm(c')`.

**3. Spreading out of Picard classes** (`PicLFT.picSpreadOut : PicSpreadOut`).
* *Limit.* Index by `Finset B`, with stage `K[s]`. CloudW06 `AdjoinFinset.specOverCone` and `isLimitSpecCone`
  present `Spec B` as the limit of the `Spec K[s]`. Base change `T ↦ A ×_K T` (the functor `bcF`, whose maps are
  `JacobianChallenge.baseChangeMap`, exactly the maps of `picardPresheaf`) preserves this connected limit
  (`isLimitBcF`, via Mathlib `isLimitOfIsPullbackOfIsConnected` and CloudW07 `isPullback_baseChangeMap`). The
  transition maps are affine (base changes of `Spec` maps), and the stages are compact (`A` is quasi-compact) and
  separated.
* *Module.* Let `L` be the representative of `c`. It is invertible, hence finite locally free, hence finitely
  presented. By CloudW07 `exists_isFinitePresentation_pullback_iso_of_isLimit` (EGA IV 8.5.2 for finitely
  presented module sheaves, already proved in the tree), `L ≅ π₀^*M₀` for a finitely presented `M₀` at some stage.
* *Invertibility at a finite stage* (`invAtStage`). The sheaf `L` is trivial near each point `x` of the limit. By
  Mathlib `isBasis_preimage_isAffineOpen`, it is trivial on some `π_k⁻¹W` with `W` affine in a stage `k`.
  `triv_stage` restricts the system to the preimages of `W` (CloudW07 `preimageDiagram`, `isLimit_preimageCone`,
  an affine limit). There the isomorphism `π^*(M_k|W) ≅ 𝒪` descends to some stage. The generic core is
  `exists_iso_stage`: CloudW07 `exists_hom_of_affine_limit` is applied twice (to the map and to its inverse), and
  `exists_hom_eq_of_affine_limit` twice (to the two composites). By compactness of the limit
  (`Scheme.compactSpace_of_isLimit`), finitely many such opens cover it. At a common stage they cover the stage
  (Mathlib `exists_map_eq_top`), and `M` is trivial on each of them, so it is invertible
  (`isInvertible_iff_forall_exists_pullback_unit`).
* *Class.* `c' := Pic.mk M_j` satisfies `Pic.map π_j c' = c` (`Scheme.Pic.eq_iff_nonempty_iso`).

## Inputs (all already proved or in Mathlib)

| input | where | status |
| --- | --- | --- |
| normalized classes `≅` fppf Picard sheaf (Kleiman 9.2.5) | vendored `picardFunctorNormalizedIso`, `PicDict.Θ`, with `PicDict.pushforwardUnitUniversal` | proved |
| fp module sheaves descend along directed limits of qc separated schemes with affine transitions (EGA IV 8.5.2) | CloudW07 `Modules/Limits/Objects.lean` `exists_isFinitePresentation_pullback_iso_of_isLimit` | proved |
| morphisms / equalities of fp modules descend on affine limits | CloudW07 `Modules/Limits/Hom.lean` | proved |
| preimage diagrams of an open, and their limit | CloudW07 `Modules/Limits/OpenCover.lean` | proved |
| `B = colim K[s]`, `Spec B = lim Spec K[s]` in `Over (Spec K)` | CloudW06 `PoincareRigidity/AdjoinFinset.lean` | proved |
| invertible ⇒ finite locally free ⇒ finitely presented; local criterion for invertibility | CloudW07 `Sheaf/LocallyFree.lean`, `Modules/Invertible.lean` | proved |
| basis of the limit topology, covering at a finite stage, compactness of the limit | Mathlib `AffineTransitionLimit.lean` (Stacks 01Z4, 01Z2 area) | Mathlib |

New leaves: **none**.

## Lean notes (pitfalls met)

* In one monolithic proof of `triv_stage`, kernel type checking took 207 s (`set_option profiler true`:
  "type checking took 207s"). Moving the descent algebra into a lemma `exists_iso_stage` over abstract variables
  (any directed affine system `P`) brought the whole file to about 30 s.
* `Functor.map_id` under `open CategoryTheory` resolved to the monad law `id <$> x`. Write
  `CategoryTheory.Functor.map_id`.
* `SheafOfModules.IsInvertible` and `IsFinitePresentation` carry a universe parameter for their local data. When
  instance search fails across universes or across `let`-bound modules, pass the instance with `@`, or re-derive
  invertibility through `isInvertible_iff_forall_exists_pullback_unit` (`.1` then `.2`).
* `pullback` is ambiguous between `Limits.pullback` and `Scheme.Modules.pullback` under `open Scheme.Modules`.

## Files

* `ZInQKernel/Contrib/OneProof/PicLocFinType.lean`: the deliverable.
* `scratch/piclft/Main.lean`: the same proof as a scratch file. `Criterion.lean` (part 1, Mathlib only),
  `Reduce.lean` (parts 1–2) and `Spread.lean` (`invAtStage`) are the steps, each compiling on its own.
* `scratch/piclft/Discharges.lean`, `discharges-output.txt`, `autofold.json`, `FoldDryRun.lean.txt`, `log.md`.
