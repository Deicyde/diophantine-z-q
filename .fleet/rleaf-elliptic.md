# rleaf-elliptic (fleet summary)

**Main result.** Two textbook leaves about elliptic curves are proved outright, each with the
leaf's exact type and no hypotheses. As a result, the glue target `BelyiX1` is now
hypothesis-free; T39 is derived from T40; and T40 is reduced to Igusa's theorem plus the Tate
curve.
- `ZInQ.RLeaf.t36_torsionStructure : X1Belyi.TorsionStructure` (T36, `E[N] ≅ (ℤ/N)²`), via Tau Ceti
  `WeierstrassCurve.torsion_addEquiv_prod`. File `ZInQKernel/Contrib/RLeaf/T36Torsion.lean`.
- `ZInQ.RLeaf.T37.t37_goodReductionUnramified : X1Belyi.GoodReductionUnramified` (T37,
  Néron–Ogg–Shafarevich over `k(T)`, residue characteristic 0). File
  `ZInQKernel/Contrib/RLeaf/T37GoodReduction.lean`. The proof: the division field is finite
  Galois; Tau Ceti's inertia lemma (`Affine/Point/Inertia.lean`) makes the inertia group trivial;
  a valuation-to-ideal inertia bridge and Mathlib's `card_inertia_eq_ramificationIdxIn` give
  `e = 1`.
- `ZInQ.RLeaf.belyiX1 : LeafModCurves.BelyiX1` (`BelyiX1.lean`).
- `ZInQ.RLeaf.x1ConstantField_of_x1RationalCusp : X1RationalCusp → X1ConstantField` (T39 ⇐ T40: a
  degree-one place forces constant field ℚ), plus `x1Leaves_of_t38_t40` and
  `x1ModelExists_of_t38_t40` (`X1ConstantField.lean`).
- `ZInQ.RLeaf.x1RationalCusp_of_igusa_tate : IgusaTransitive → TateCuspLaurent → X1RationalCusp`,
  plus `x1Leaves_of_t38_igusa_tate` (`X1RationalCusp.lean`). The two new Props are consequences of
  Igusa 1959 and of the Tate curve (Silverman ATAEC V).

**What compiles.** `lake build` of the five `ZInQKernel.Contrib.RLeaf.*` modules succeeds. Every
`#print axioms` line (18 declarations) reads `[propext, Classical.choice, Quot.sound]`. 230 oct16
Tau Ceti modules were vendored (192 + 38). One lemma was renamed in a vendored file, with a note
there and in NOTICE; diffcheck2 reports MOD-UNNOTED 0 and NOTE-ONLY 0.

**Survey (docs/research/rleaf-elliptic.md §1).** No research-level leaf (R1-R22, H5) is about
elliptic curves, and none reduces to one: each is used at `g = 2` or on `J₁(N)`. Tau Ceti's
`g = 1` results (NOS and potential good reduction over local fields, Weil pairing, Tate module)
cannot discharge them. Using them at all would need an `AbVar`(dim 1) ↔ `WeierstrassCurve` bridge
(AV7) and DVR-generality. The elliptic leaves are textbook: T36-T40.

**Remains.** The two suppliers of T40, `IgusaTransitive` (research-level) and `TateCuspLaurent`
(needs a backport of Tau Ceti main's Tate uniformization and a normed-field structure on `ℚ((t))`);
T38 (not elliptic); all research leaves. Leaf-list effect: T36 and T37 are proved and T39 follows
from T40, so the textbook list goes from 35 to 32.
