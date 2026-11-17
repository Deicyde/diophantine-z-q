# newform-dict (2026-11-15)

**Result: the dictionary is proved in Lean, in both directions, for the definitions as they stand.** For
`N ≥ 1`, the kernel's `IsNewform f χ` (normalized eigenform of every `T_n` given by its coefficients, and not in
the span of level raises) holds iff `f` is a Tau Ceti `HeckeRing.GL2.Newform N k` with `g.χ = toUnitHom χ`. Tau
Ceti's newform is the printed one: Atkin–Lehner / Li / Diamond–Shurman Def. 5.8.1, a normalized eigenform in the
Petersson orthogonal complement of the old space. The hard direction (strong multiplicity one) uses only Tau
Ceti theorems already vendored in the kernel: DS 5.8.3 spanning (eigenvalue-refined), DS 5.8.2 on the whole
χ-space, diamond stability of the old space, and independence of the χ-spaces. No new leaf.

**File:** `ZInQKernel/Contrib/OneProof/NewformDict.lean`. It builds with no warnings; every theorem uses only
`[propext, Classical.choice, Quot.sound]`.
- `NewformDict.isNewform_iff (hN : 0 < N) : PkgI4.IsNewform f χ ↔ ∃ (_ : NeZero N) (g : Newform N k), g.toCuspForm = f ∧ g.χ = MulChar.toUnitHom χ`.
  The hard half is `exists_newform_of_isNewform`. The same statement for the other two copies of `IsNewform`
  (G9/I4Layer and LPrefix) is `g9_isNewform_iff` and `leafModCurves_isNewform_iff`.
- `forall_isNewform_iff`: any statement about every `IsNewform` is the same statement about every printed newform.
- The three fields stated over `IsNewform` are each proved equivalent to their restatement over `Newform`:
  - `carayolR17'_iff_newform` (`r17`);
  - `r16CoreY_iff_newform` (`r16CoreY`);
  - `eigenformHTNew_iff_newform` (`eigenformHTNew`).

**`#discharges`:** r17, eigenformHTNew and r16CoreY are each discharged by `NewformDict.*_of_newform`, still
assuming the restated leaf (`CarayolR17Newform`, `EigenformHTNewNewform`, `R16CoreYNewform`); standard axioms.

**Autofold:** `scratch/newform-dict/autofold.json`. The dry run is count-neutral (46/10 → 46/10). The generated
`sixContactMin_of_open30` compiles. The new leaves keep their fields' kinds (consequence, composite, consequence)
and stay GLUE for their other reasons (transport to every attached ρ, A_f not definable, Kato's V_f not
definable). The newform notion is no longer one of those reasons.

**Leaves freed of the dictionary step.** On this base: r17, r16CoreY and eigenformHTNew. The GZ/TYZ hypotheses
(hFH, hL3, h33) were already over Tau Ceti's `Newform` and never needed it. Off base: the proposed new leaves
`NewformRepConductor` (r17-bypass), `KatoHTExists` (ht-exists) and `AfTateCharPoly` (r16-used). Their Newform
forms are proved equivalent in `scratch/newform-dict/OffBase.lean` (compiles). I recommend folding those leaves
in their Newform form.

**Remains:** the folds (integrator) and the readings those leaves' own tasks list.
Report: `docs/research/newform-dict.md`.
