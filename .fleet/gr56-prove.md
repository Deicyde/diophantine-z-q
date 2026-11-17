# gr56-prove (fleet summary)

**Result.** I did not prove the research field `gonzalezRotgerProp56X6` (`GRCountX6.GonzalezRotgerProp56X6`)
outright. I discharged it with one new leaf, Eichler's optimal-embedding count `GRCountX6.EichlerOptEmbCount6`
(pure quaternion-order algebra, printed form). Every other hypothesis is a field already in the bundles.
Contributor file: `ZInQKernel/Contrib/OneProof/GR56Lattice.lean` (85 KB, no `sorry`).

```lean
theorem GR56.gonzalezRotgerProp56X6_of_main (hE : GRCountX6.EichlerOptEmbCount6)
    (hS : RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (hST : HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : GRCountX6.GonzalezRotgerProp56X6
```

Axioms: `[propext, Classical.choice, Quot.sound]`. The same holds for every theorem listed in
`scratch/gr56-prove/axioms.txt`.

**Content.** The CM-point correspondence `CM(R) ≃ Emb(R, 𝒪)/𝒪^×` (gt-grcount's `CMPointsOptEmb6`) is proved from
the lattice model (`GR56.cmPointsOptEmb6_of_main`):
- It is injective from the three textbook fields alone (`cmMap_injective`).
- It is surjective from two existence statements. "QM tori are abelian surfaces" is the moduli clause of
  `shimuraMainThmIDeligneY3AbU`. "CM points are algebraic" is proved from `shimuraTaniyamaQbar`, using base change
  in stages and descent by T11(b).

The upper bound `R5fpCountLe`, the only half the chain uses, follows from Eichler's count and the textbook fields
alone (`r5fpCountLe_of_eichler`). The chain's single consumer (`nocm_on_witness`) is rerouted to it.

**#discharges** (`scratch/gr56-prove/discharges.txt`): `DISCHARGES [OpenResearchLeaves22.gonzalezRotgerProp56X6] by
GR56.gonzalezRotgerProp56X6_of_main still assumes [EichlerOptEmbCount6, ShimuraMainThmIDeligneY3AbU,
ShimuraTaniyamaQbar, UniformizationLeafAll, GAGAMorphism, MumfordTorsionAlgClosed]`. Two more forms of the field
theorem also discharge it: `_of_st` and `_of_leaves`. Totals: 63 open, 1976 checked, 10 discharge one.

**Fold.** Spec: `scratch/gr56-prove/autofold.json`. The new leaf is `eichlerOptEmbCount6`, and the proof uses
`{n}`, `{l}` and `{t}`. `--dry-run` gives 46/10 on 56 -> 46/10 on 56 (strictest 45/11 -> 45/11). The generated
module compiles with standard axioms. An alternative spec without the composite field
(`autofold-alt-torus.json`, adding the leaf `qmTorusAbelian`) gives 46/10 -> 47/10.

**What remains.** `EichlerOptEmbCount6` is still a leaf. Proving it needs local quaternion orders over `ℚ₂` and
`ℚ₃` and local-global theory for lattices, which Mathlib does not have, so I did not attempt it. Its statement
review against the print is still pending; the `𝒪^×` normalization is consistent with the field via the proved
bijection. Report: `docs/research/gr56-prove.md`.
