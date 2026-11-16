# st-qbar: `STQM` proved; the leaf `shimuraTaniyamaQbar` can leave the bundles

Task st-qbar, 2026-11-15, base `9a100aa7` (leaf-fold22b). Contributor file
`ZInQKernel/Contrib/OneProof/STQM.lean` (namespace `GapST`, imports only `ZInQKernel.OneProof.H.TailO`, 47 KB).
No new leaf, no new glue statement: every hypothesis is a field already in the bundles or a theorem of the base.

## 1. Result (all VERIFIED: compiled with `lake build ZInQKernel.Contrib.OneProof.STQM`)

```lean
theorem GapST.stQM_of (hRep : HDec.LeafAdopt.R1R2fpRep) (hconn : HDec.TSHecke.Y3Connected)
    (hAL : HDec.HeckeRest.ALFixedPoints) (hT : _root_.PkgI2.TorsionStructure.{0})
    (hU : _root_.ZInQ.LeafPush2.UniformizationExists) (hC : _root_.ZInQ.HomUnify.HomLatticeCorr) :
    HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
```
`'GapST.stQM_of' depends on axioms: [propext, Classical.choice, Quot.sound]`

The conclusion is the full `STQM` (every `A : PkgI3.AbVar ℂ` with `q : QMStr A`, `A.dim = 2` and CM by `ℤ[i]`,
`ℤ[ζ₃]` or `ℤ[√−6]`), not only its restriction to `QML3 ℂ`; a level-3 structure is constructed
(`GapST.exists_level3`).

Hypotheses (where each comes from):

| hypothesis | type | supplied on the base by |
| --- | --- | --- |
| `hRep` | `LeafAdopt.R1R2fpRep` | research field `r1r2` (gen 7: `r.r1r2`) |
| `hconn` | `TSHecke.Y3Connected` | added field `y3Connected` (gen 7: `l.y3Connected`) |
| `hAL` | `HeckeRest.ALFixedPoints` | chain theorem `(qmRows_of7 t l).2.1` (TailX L240; the same term fills `alFixedPoints` at TailX L259) |
| `hT` | `PkgI2.TorsionStructure` (T5) | `_root_.AvSplit.Final.h25 t.mumfordTorsionAlgClosed` (TailX L221) |
| `hU` | `ZInQ.LeafPush2.UniformizationExists` (T35) | `_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed` (TailX L231) |
| `hC` | `ZInQ.HomUnify.HomLatticeCorr` | `_root_.AvSplit.Final.h69 t.uniformizationLeafAll t.gagaMorphism` (TailX L226) |

Also exported (same axioms, VERIFIED):

```lean
theorem GapST.cmDescends_of (hRep : HDec.LeafAdopt.R1R2fpRep) (hconn : HDec.TSHecke.Y3Connected)
    (hAL : HDec.HeckeRest.ALFixedPoints) (hT : _root_.PkgI2.TorsionStructure.{0})
    (hU : _root_.ZInQ.LeafPush2.UniformizationExists) (hC : _root_.ZInQ.HomUnify.HomLatticeCorr)
    (hR : ZInQ.LeafPush2.T11b_Rigidity) : HDec.HSyn.G0Split.FibreQM.PeriodMapH.CMDescends

theorem GapST.cm_point (hRep : HDec.LeafAdopt.R1R2fpRep) (hconn : HDec.TSHecke.Y3Connected)
    (hAL : HDec.HeckeRest.ALFixedPoints) (hT : PkgI2.TorsionStructure.{0})
    (hU : ZInQ.LeafPush2.UniformizationExists) (hC : HDec.HomUnify.HomLatticeCorr)
    (Q : QML3 ℂ) (hcm : HasCM4 Q.q ∨ HasCM3 Q.q ∨ HasCM24 Q.q) :
    ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ Nonempty (Q.Iso Q')

theorem GapST.exists_qbar_factor (Y : Over (Spec (CommRingCat.of ℚ))) [IsProper Y.hom]
    [SmoothOfRelativeDimension 1 Y.hom] [IrreducibleSpace Y.left]
    (y : fieldPt ℂ ⟶ Y) (h : Y ⟶ Y) (hy : y ≫ h = y) (s : fieldPt Qbar ⟶ Y) (hs : s ≫ h ≠ s) :
    ∃ (ιe : Qbar →+* ℂ) (y₀ : fieldPt Qbar ⟶ Y), fieldMap ιe.toRatAlgHom ≫ y₀ = y

theorem GapST.twist_of_cm (hT : PkgI2.TorsionStructure.{0}) (hU : ZInQ.LeafPush2.UniformizationExists)
    (hC : HDec.HomUnify.HomLatticeCorr) (hA : A.dim = 2) (q : QMStr A)      -- A : PkgI3.AbVar ℂ
    (hcm : HasCM4 q ∨ HasCM3 q ∨ HasCM24 q) :
    (HasCM4 q ∧ Nonempty (QMIso q (q.twist (HDec.LeafQM.AV.Pin.Exact.rep 1)))) ∨
    (HasCM3 q ∧ Nonempty (QMIso q (q.twist (HDec.LeafQM.AV.Pin.Exact.rep 2)))) ∨
    (HasCM24 q ∧ Nonempty (QMIso q (q.twist (HDec.LeafQM.AV.Pin.Exact.rep 3))))

theorem GapST.exists_level3 {A : PkgI3.AbVar ℂ} (hT : PkgI2.TorsionStructure.{0}) (hA : A.dim = 2)
    (q : QMStr A) : Nonempty (Level3 q)
```
`#print axioms` for each: `[propext, Classical.choice, Quot.sound]` (`scratch/st-qbar/axioms.txt`).
`twist_of_cm` is the converse of `ALFixedPoints` over `ℂ` (the missing piece named by triage row L08); with
`gen2`/`gen3` (generators of `A[2]`, `A[3]` as `𝒪`-modules) it may serve task cm-stab (same three CM orders).

## 2. `#discharges`

`scratch/st-qbar/Discharges.lean` (imports `Main`, `Discharges`, `Contrib.OneProof.STQM`), output in
`scratch/st-qbar/discharges.txt`:

```
#discharges: 63 open hypotheses, 1700 theorems checked, 5 discharge one
```
The five are other tasks' contributions already in the tree (GRCountX6, GapSHPair, ElkiesX6Star,
SGA7PersistsNF, UnipotentForward). None is ours, as expected: `STQM` is not a bundle field (the field is
`shimuraTaniyamaQbar : ShimuraTaniyamaQbar`, which is strictly more general: any CM abelian surface over
`ℂ`, not only QM ones). So no autofold spec: the leaf leaves by rerouting its only consumer (§3).

## 3. Manual fold

**Consumers of `shimuraTaniyamaQbar` at `9a100aa7`.** One real consumer:

* `ZInQKernel/OneProof/H/TailX.lean` L261, in `addedLeaves6_of_open7` (gen 7 → gen 6):
  `stQM := stQM_lf7 l.shimuraTaniyamaQbar`.

  **Replacement term** (compiled in that context: `scratch/st-qbar/FoldCheck.lean`, which also restates the whole
  of `addedLeaves6_of_open7` with it as `addedLeaves6_of_open7_st`, axioms standard):
  ```lean
  stQM := _root_.GapST.stQM_of r.r1r2 l.y3Connected (qmRows_of7 t l).2.1
    (_root_.AvSplit.Final.h25 t.mumfordTorsionAlgClosed)
    (_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)
    (_root_.AvSplit.Final.h69 t.uniformizationLeafAll t.gagaMorphism)
  ```
  (`addedLeaves6_of_open7` already takes `r t l`; TailX imports TailO, so importing
  `ZInQKernel.Contrib.OneProof.STQM` creates no cycle.)

Every other occurrence only forwards the field to the previous generation. On the live path of
`frozenTarget` (`sixContactMin_of_open28` → … → `open17` → `open11` → … → `open7`): TailZ34 L159
(`openAddedLeaves16_of_OpenAddedLeaves17`), TailZ31 L56 (`15_of_16`), TailZ30 L60 (`14_of_15`), TailZ26 L178
(`13_of_14`), TailZ24 L823 (`addedLeaves12_of_open13`), TailZ23 L750 (`addedLeaves9_of_open14`, the leaf-fold14
bypass), TailZ13 L57 (`addedLeaves8_of_open9`), TailZ4 L245 (`addedLeaves7_of_open8`). Off the live path
(maps no longer used by `frozenTarget`): TailZ22 L324, TailZ18 L1239, TailZ17 L263. Field declarations:
TailZ34 L121 (`OpenAddedLeaves17`), TailZ31 L19, TailZ30 L19, TailZ26 L137, TailZ24 L775, TailZ22 L239,
TailZ18 L1216, TailZ17 L195, TailZ13 L27, TailZ4 L137, TailX L170 (`OpenAddedLeaves7`).

**Consumers of `STQM`.** Field `stQM` of `OpenAddedLeaves6` (TailO L2830); its one consumer is TailO L2872,
`cmDescends_of6` (`LeafQCheck.cmDescends_of l.stQM …`), reached from `addedLeaves4_of_open6` (TailO L2883, `cmDescends := cmDescends_of6 r t l` at L2899) on the live path.
It needs no change (it receives the new `stQM`). The `stQM` fields at TailO L2650, L2674, L2698, L2722 belong to
older generations that are not on the live path. (Alternative, if preferred: `GapST.cmDescends_of` gives
`CMDescends` directly, with `hR := t11b_of_exists5 t.t11bExists`.)

**How the fold goes (VERIFIED end to end by a compiled demonstration).** Since the field is threaded through
every added-bundle generation 7 … 17, the new generation (17 without `shimuraTaniyamaQbar`) cannot map to 17; as
in leaf-fold14 the maps on the live path that take an added bundle must be re-instantiated without the field.
`scratch/st-qbar/BypassFold.lean` (generated by `scratch/st-qbar/gen_bypass.py`, which copies verbatim and only
renames) does exactly that:

* `OpenAddedLeaves17S` (the proposed new bundle: `OpenAddedLeaves17` minus `shimuraTaniyamaQbar`, checked by
  diffing the field lists) and copies `OpenAddedLeaves{7,8,9,12,…,16}S` of the intermediate generations without
  the field;
* the 33 declarations on `frozenTarget`'s path that take one of these bundles, copied with suffix `_S` and the
  forwarding line deleted: `sixContactMin_of_open{28,…,17,11,10,9,8,7}`, `openAddedLeaves{16,15,14,13}_of_…`,
  `addedLeaves12_of_open13`, `addedLeaves9_of_open14`, `researchLeaves9_of_open14`, `x6Rows_of_open14`,
  `ss1_ss3_of14`, `semistableAlmostAll_of10`, `addedLeaves8_of_open9`, `addedLeaves7_of_open8`, `qmRows_of7`,
  `researchLeaves5_of_open7`, `textbookLeaves6_of_open7`, `addedLeaves6_of_open7` (with the replacement term
  above for `stQM`);
* `ZInQ.Contrib.TYZChain.frozenTarget_S`: `frozenTarget`'s statement and proof (Main.lean L60) with
  `l : OpenAddedLeaves17S`.

```
'HDec.HSyn.sixContactMin_of_open28_S' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZChain.frozenTarget_S' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(`scratch/st-qbar/bypass-axioms.txt`; the file compiles in 8 s against the base's build.) So `ZInQ.FrozenTarget`
follows from the current open hypotheses minus `shimuraTaniyamaQbar`. A real fold would put this in a new
`TailZ35` with the usual generation names (the lead's call; `autofold.py` cannot express it since the field is
not discharged by a proof of its own statement).

**Counts** (kinds.tsv, H fields only, as `autofold.py`'s `counts`; the row `added shimuraTaniyamaQbar` is
published, LEAF/LEAF):

| | H fields | strict LEAF / GLUE | strictest LEAF / GLUE |
| --- | --- | --- | --- |
| before (`9a100aa7`) | 56 | 46 / 10 | 45 / 11 |
| after | 55 | 45 / 10 | 44 / 11 |

No glue count rises; no field is added (`r1r2`, `y3Connected`, `mumfordTorsionAlgClosed`,
`uniformizationLeafAll`, `gagaMorphism` are already used elsewhere in the chain). Open hypotheses overall:
63 → 62.

## 4. Method

Notation: `Y = Y₃` with `Φ : Y(K) ≃ M3 K` from `r1r2`; `α_k = rep k` (conjugation by `w_k = 1, i, j, ij`).

1. **The Atkin–Lehner automorphism of a CM point** (`twist_of_cm`, VERIFIED). For CM `φ ∈ End_𝒪(A)`, take
   `(k, w, c, n) = (1, i, 1+φ, 2)`, `(2, j, 2φ−1, 3)`, `(3, ij, φ, 6)` for CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`;
   `f = ι(w)c` satisfies `f ι(a) = ι(α_k a) f` and `f² = n²r` with `r = φ, 1, −1` a unit.
   * `f` kills `A[n]`: `A[p]` (`p = 2, 3`) is free of rank one over `𝒪/p𝒪` (`gen2`, `gen3`): some `v ∈ A[p]` is
     not killed by `ι(w₀)` (`w₀ = i, j`; else `ι(w₀)² = ±p` kills `A[p²]`, against `p⁸ > p⁴` from T5), its
     annihilator is `p𝒪` (finite check `d1`: every `a ∉ p𝒪` has a left multiple `≡ 1` or `≡ w₀` mod `p`) and
     `a ↦ ι(a)v` is onto by counting. `c` acts on `A[p]` by right multiplication by some `u` with `u² ∈ p𝒪`, and
     the finite check `d2` (`x² ∈ p𝒪 ⇒ w a x ∈ p𝒪` for `(p, w) = (2, i), (2, ij), (3, j), (3, ij)`) gives
     `f(A[p]) = 0`. The checks are `decide +kernel` over `ZMod p` coordinates (6561 cases, seconds).
   * division: an endomorphism killing `A[n]` is `n·g` (`dvd_of_kills`: lift to `M` on `ℂ²` by
     `HomLatticeCorr`(1), `M/n` preserves `Λ`, realize by `HomLatticeCorr`(2)); `End(A)` is torsion-free
     (`eq_zero_of_natCast_mul`, from the surjective uniformization T35).
   * so `ψ = f/n` is an automorphism (`ψ² = r`) with `ψ ι(a) = ι(α_k a) ψ`: `QMIso q (q.twist α_k)`.
2. **The fixed point** (`fixed_class`, `cm_point`). Transporting the level structure along `ψ` and
   `Level3.torsor` + `exists_unit_congr` give `u ∈ 𝒪^×` with `[Q] = rightMul u (twist α_k [Q])`; with R1hecke's
   automorphisms `g_α`, `g_u` of `Y`, the `ℂ`-point `y` of `Q` satisfies `y ≫ (g_α ≫ g_u) = y`. A `ℚ̄`-point
   `s₀` with `π₆ = 1` (X6Surj) has no CM (R2X6PropsIff), so by `ALFixedPoints` it is not fixed:
   `s₀ ≫ (g_α ≫ g_u) ≠ s₀`.
3. **Algebraicity** (`exists_qbar_factor`, `closure_eq_univ_of_not_closed`). `Y` is irreducible
   (`Y3Connected`, `irreducibleSpace_of_connected`) and reduced (`isReduced_of_smooth_domain`). If the point `p`
   of `y` were not closed, it would be the generic point (the stalk at a closed point in its closure is a
   1-dimensional local domain, `stalk_dim_of_smoothOfRelativeDimension`, `isDomain_of_dim_one`, so a
   non-maximal prime is `⊥`), `y` would be dominant and `g_α ≫ g_u = 𝟙` (`ext_of_isDominant_of_isSeparated`),
   contradicting step 2. So `p` is closed, `κ(p)` is finite over `ℚ` (Jacobson), and `κ(p) → ℂ` factors through
   some `ℚ̄ → ℂ`: `y = fieldMap ιe ≫ y₀`.
4. **The model** (`stQM_of`, `bc_iso`). R1fp naturality gives `Q' = (Φ y₀)_ℂ` with `IsBaseChangeOf ιe P Q'` and
   `Q ≅ Q'`; `descend_main`'s comparison gives `Q'.A ≅ P.A ×_{ℚ̄,ιe} ℂ`; for a bare `(A, q)` a level structure is
   built from a generator of `A[3]` (`exists_level3`).

Files: `ZInQKernel/Contrib/OneProof/STQM.lean`; `scratch/st-qbar/` (`Discharges.lean`, `discharges.txt`,
`FoldCheck.lean`, `BypassFold.lean`, `gen_bypass.py`, `bypass-axioms.txt`, `Axioms.lean`, `axioms.txt`, development parts, `log.md`). Note for others: the worktree
lacked `lean/.lake/build`; it was copied from `~/dzq` (same commit).
