**Remaining work after leaf-fold (2026-11-13).** Hypotheses of `HSyn.sixContactMin_of_open`:
1. **Open textbook leaves** (27 of the 35; 26 fields of `HSyn.OpenTextbookLeaves`): T1 (purity),
   T3-T8 (Néron mapping property, reduction of torsion, torsion structure, `Hom` finite free,
   characteristic polynomials, Poincaré), T9 (Weil pairing), T10 (étale `H¹` duality), T11(a), T11(b)
   (Riemann, rigidity), T14(a′), T14(b′) (Brauer–Hasse–Noether, reciprocity; both follow from
   t1415-tc's `KummerIndexBound`, `HSyn.t14_of_kummerIndexBound`), T16(b) (local reciprocity,
   upper numbering), T23 (Fontaine's closure), T24 (twists), T26 (`T_ℓ` free), T27 (QM dichotomy),
   T28 (Igusa separation; reduced by t28-igusa to `M3Identities` and `SeparationSpecial`), T29(a),
   T29(b) (local normalizers), T33 (Jacobians), T34 (`dim J₁(N)`), T35 (uniformization), T36-T40
   (`x1`), T41 (Néron models).
2. **Open research-level leaves** (all 23; 26 fields of `HSyn.OpenResearchLeaves`), with R10 and
   R14 in their corrected forms (`PkgI4.DeRhamComparisonHT`, `G0Galois.R14Det`) and R1(b), R17
   still `opaque` placeholders.
3. **The ten glue pieces** of `HSyn.GluePieces` (unchanged; §3, table "Glue pieces"). G10, inside
   `modularConstituent`, now has g10-odd's concrete statement `G0Galois.G10GlueConcrete` and core
   `G0Galois.ConjTwistNontrivial` recorded in `Leaves.lean`.
4. Items 2-5 of the list after leaf-adopt3 below (premises, glue targets outside G0, unification),
   less "the local-to-global transport for T20, T21", which diff-bridge did.
