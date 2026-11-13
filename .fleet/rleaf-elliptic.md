# rleaf-elliptic (fleet summary)

**Main result.** Two textbook leaves about elliptic curves are proved outright, each with the
leaf's exact type and no hypotheses. As a result, the glue target `LeafModCurves.BelyiX1` is now
proved with no hypotheses:
- `ZInQ.RLeaf.t36_torsionStructure : X1Belyi.TorsionStructure` (T36, `E[N] ≅ (ℤ/N)²`), in
  `ZInQKernel/Contrib/RLeaf/T36Torsion.lean`, via Tau Ceti's `WeierstrassCurve.torsion_addEquiv_prod`.
- `ZInQ.RLeaf.T37.t37_goodReductionUnramified : X1Belyi.GoodReductionUnramified` (T37,
  Néron–Ogg–Shafarevich over `k(T)` with residue characteristic 0), in
  `ZInQKernel/Contrib/RLeaf/T37GoodReduction.lean`. The proof: the division field is finite
  Galois; Tau Ceti's inertia lemma (`Affine/Point/Inertia.lean`) makes the inertia group trivial;
  a valuation-to-ideal inertia bridge and Mathlib's `card_inertia_eq_ramificationIdxIn` give
  `e = 1`.
- `ZInQ.RLeaf.belyiX1 : LeafModCurves.BelyiX1`, `x1Leaves_of`, `x1ModelExists_of` (only T38-T40
  remain for `X1Leaves` / `X1ModelExists`), in `ZInQKernel/Contrib/RLeaf/BelyiX1.lean`.

**What compiles.** `lake build ZInQKernel.Contrib.RLeaf.BelyiX1` succeeds. Every `#print axioms` line
reads `[propext, Classical.choice, Quot.sound]`. 230 oct16 Tau Ceti modules were vendored (192 +
38). One of them was renamed-lemma-patched and noted; NOTICE is updated; diffcheck2 reports
MOD-UNNOTED 0 and NOTE-ONLY 0.

**Survey (docs/research/rleaf-elliptic.md §1).** No research-level leaf (R1-R22, H5) is a
statement about elliptic curves, and none reduces to one. Each is used at `g = 2` or on `J₁(N)`.
Tau Ceti's `g = 1` results (NOS, potential good reduction, Weil pairing, Tate module) cannot
discharge them. Using them at all would need an `AbVar`-dimension-1 ↔ `WeierstrassCurve` bridge
(AV7) and DVR-generality. The elliptic leaves are textbook: T36 and T37 (proved here), and T39
(Igusa) and T40 (rational cusp), which remain open and both need Igusa's theorem.

**Remains.** T38, T39, T40; all research leaves.
