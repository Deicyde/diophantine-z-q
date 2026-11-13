# tc-survey (2026-11-13): open H leaves vs Tau Ceti

**Main result.** None of the 23 research-level leaves (R1-R22, H5) is in Tau Ceti. A grep of
tc-main 4d91513e finds no p-adic Hodge theory, Faltings height, Néron models of abelian varieties,
Shimura curves, Igusa invariants, or Galois representations of eigenforms. Among the open textbook
leaves, the cheap Tau Ceti closures are the ones other tasks already own: T17 (kw-new), T18
(cheb-bridge), T20/T21 (diff-bridge), and T14/T15 on the other host. T14's unconditional Hasse
principle exists only at main. The best candidates nobody owns:
- **T25** `NewformOfEigenform`: Tau Ceti `HeckeRing.GL2.EigenformAwayFromLevel.exists_newform_eigenvalue_eq`
  (oct16) states the same theorem. The bridge is medium: about 204 unvendored modules, plus a
  dictionary between coefficient eigenforms and Hecke eigenforms, whose lemmas Tau Ceti has.
- **T31** `LeafUnramified`: Tau Ceti `mk_eq_zero_of_forall_mem_unitFiltration_zero` plus
  `h2MuToBr_injective` (oct16). The bridge is medium (7 unvendored modules).
- **Two open glue transports, already vendored by tc-port**:
  - the degree-2 cochain comparison, which links the cochain leaves T14′/T15′ to
    `continuousCohomology` (compiled, below);
  - G15's `D_P ≅ Gal(L_P/ℚ_p)` with lower ramification filtrations: `decompositionEquiv`,
    `map_ramificationGroup_decompositionHom`.

Weaker than their leaves:
- T24: the twist exists only as a newform of level dividing `N m²`.
- T16b: only the kernel-level upper-numbering case is there.
- T1: purity in dimension 2 only, at main only.
- T5, T9, T26, R7a, R7b, T11a, T35: elliptic curves (`g = 1`) only.

Tau Ceti main also builds a nonzero abelian variety (`WeierstrassCurve.toAbelianVariety`, of
dimension 1, and a product of dimension 2), but it is not at oct16.

**What compiles** (VERIFIED). After merging origin/wip/tc-port, `lake env lean
scratch/tc-survey/Compare.lean` exits 0. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for each of:
- `TCSurvey.h2Equiv (K) [Field K] [CharZero K] : H2 (Field.absoluteGaloisGroup K) (PkgI6.Z2 K).V ≃+ continuousCohomology 2 (PkgI6.Z2 K)`
- `TCSurvey.mem_Z2_iff ε : (fun q => ε q.1 q.2) ∈ TauCeti.ContCohomology.Z2 G_K (PkgI6.Z2 K).V ↔ PkgI6.IsCocycle2 ε`
- `TCSurvey.mem_B2_iff ε : (fun q => ε q.1 q.2) ∈ TauCeti.ContCohomology.B2 G_K (PkgI6.Z2 K).V ↔ PkgI6.IsCoboundary2 ε`

This is a statement comparison, not a leaf proof. No leaf was proved and nothing was vendored.

**What remains.** Port T25 (medium) and bridge it, then T24, after restating it or adding
`p`-stabilization. Bridge T31 and T15(ℚ_p) through the cochain comparison. Krasner's lemma,
SemisimpleBaseChange and every research-level leaf have no Tau Ceti source.

Report: docs/research/tc-survey.md (table of 20 rows sorted by value, with closures). Log:
scratch/tc-survey/log.md.
