# fold33-review (fleet summary)

**Verdict:** the staged fold wip/leaf-fold33b (667e0aed) can land. All three new leaves are LEAF. None is false,
vacuous or inert, and no statement change is needed. One flag remains on hGZ.

- **hCM** (`HCMDict.ShimuraThm54`, Shimura 1971 Thm 5.4): **LEAF**, pending a reading of the locator. Every
  difference from the print is a direct instance, or a dictionary step that Lean proves (`isAnalyticUnif_iff`). The
  Artin and lattice conventions are `ShimuraMainCM`'s, unchanged. Lean proves only `ShimuraThm54 → ShimuraMainCM`.
  The new leaf also asserts that `s⁻¹𝔞` is a lattice, which is true and a consequence of the print.
- **neronSchemeExtensionDedekind** (BLR 1.4 Thm 3 over an affine Dedekind base): **LEAF**, pending a reading of the
  locator. Every difference is a direct instance: special case, finite type weakened to quasi-compact, uniqueness and
  group law dropped.
- **hGZ** (`GZAlg.GrossZagierAlgOptCd`, Gross–Zagier 1986, strong Weil parametrization): **LEAF in printed form
  through a dictionary, needs-reading.** Three standard translation steps are not proved in Lean:
  - D1: field embeddings are morphisms;
  - D2: φ at Heegner points through `q`-expansions, provable from what the tree already contains;
  - D3: `IsOptimalParam` is the strong Weil parametrization, which matters only if GZ V §2 is restricted to it.

  Under the strictest rule these would count as glue. Keep the flag "unread" until someone reads GZ V §2 for its
  hypotheses on φ.
- **Reroutes (homFreeFiniteAlgClosed, sga3_VIB_3_10_Nbhd, mumfordGroupLawConn): clean.**
  - `frozenTarget` has 37 hypotheses, identical to the lead's list.
  - Against the pre-fold list, the only additions are `neronSchemeExtensionDedekind` (new) and `hCM` (retyped). Every
    other type is unchanged.
  - The constant closure (271,096 constants) contains no `SGA3_VIB_3_10*`, `MumfordGroupLawConn` or
    `GZDecomp.GrossZagierHeegner`. The homfree names that appear are the proved `HomFreeFiniteC`.
  - Axioms: standard.

**What compiles** (VERIFIED, `lake env lean` on the leaf-fold33b build tree):
- `scratch/fold33-review/Closure.lean`: the hypothesis list, the closure search and the axioms.
- `scratch/fold33-review/Vacuity.lean`:
  - `shimuraThm54_hyps_satisfiable` (m = 1, σ = id, s = 1, `⟨1,i⟩`);
  - instances for the Néron leaf;
  - the GZ bridge `GrossZagierAlgOptCd → GrossZagierModuliOptCd` with the proved q-expansion principle;
  - every use site of the three leaves is in the closure of `frozenTarget`.
- `py/chiD_check.py`: `chiD` equals the Kronecker character on 30 samples, with no mismatch.

**What remains:**
- None of the prints was read (no network): Shimura 5.4, Lang Ch. 10 Thm 3, BLR 1.4 Thm 3, and the hypotheses of GZ
  V §2 on φ.
- The direction of the Artin map was not re-checked numerically: PARI is not on this host.
- The whole hypothesis list of hGZ at a concrete `d` was not shown in Lean.
- The D2 lemma is proposed in the report (§3.3) but not proved.

Report: `docs/research/fold33-review.md`. Log: `scratch/fold33-review/log.md`.
