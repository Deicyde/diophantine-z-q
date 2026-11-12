p='docs/research/h-decomposition.md'; L=open(p).read()
def r(a,b):
    global L
    assert L.count(a)==1,(a[:70],L.count(a)); L=L.replace(a,b)
r("unramified case is stated, `PkgI4.CarayolUnramified`, but D5 needs `p | N`. Step D5.",
  "unramified case is stated, `PkgI4.CarayolUnramified`, but D5 needs `p | N`. Step D5. Update\n(hsyn-fold): def-ladic-cond defines the conductor exponent over `G_{ℚ_p}` and states R17 as\n`CarayolR17` in `scratch/def-ladic-cond/LadicCond.lean` (compiles; not yet in `Leaves.lean`, where\nR17 is still a placeholder).")
old_start = L.index("### §2.3 Counts")
old_end = L.index("---", old_start)
L = L[:old_start] + """### §2.3 Counts (VERIFIED from the lists and the compiled file; updated by hsyn-fold, 2026-11-12)

- Research-level: 22 leaves (R1-R22), 24 statements (R7 and R9 have parts a, b). Textbook: 32
  leaves (T1-T32), 35 statements (T14, T16, T22 have two parts). In all 54 leaves. R8 is no longer
  used by any step (A6 is proved without it), so 21 research-level leaves suffice; it stays listed.
- Stated in Lean over genuine definitions (in `Leaves.lean`): research R4, R6, R7, R8, R9, R10,
  R13, R14, R15, and R11 + R12 jointly (`PkgI4.PanBerger`): 11 leaves, 12 Props; textbook T1-T9,
  T13-T32: 29 leaves, 34 Props (T29 and T32 have two Props each). Total **40 of 54 leaves, 46
  Props**. The other **14** leaves (R1-R3, R5, R16-R22; T10-T12) are `opaque` placeholders.
  Outside `Leaves.lean`: R17 has a concrete statement in `scratch/def-ladic-cond/` (would make 41).
- New definitions needed: medium for R17 (done in def-ladic-cond, not folded in); large for T10,
  T11, T12; very large for R1-R3, R5 (QM moduli), R16, R18 (`J₁(N)`), R18-R22 (Faltings height).
- Route K (§1): 20 research leaves.
- Not leaves: one named glue Prop that proved theorems take as hypothesis,
  `GlueI3.SemisimpleBaseChange` (C2, E1), elementary algebra (WP3); `PkgI2.QuatUnipotentTrivial` is
  now the theorem `PkgI2.quatUnipotentTrivial`. In the merged reports outside `Leaves.lean`:
  `SwanIndependent` and `AdaptedExists` (def-ladic-cond) and a new leaf `LeafConj`
  (glue-b3-unram). `GlueAssembly.GlueOutputs` is the numerical contract (§3).
- Glue proved in `Leaves.lean` since the first version: A6 without `QuatUnipotentTrivial`
  (`PkgI2.goodReduction_of_QM_rational3`, `goodReduction_of_QM_rational3'`), C10's Galois side
  (`GlueC10.c10`, `frobLift`, `frobDense`, `iso_three_of_five`, …; `PkgI3.trace_indep_of_ell`), D1
  local (`GlueD1Local.D1_local'`, `D1_krasner'`, …).
- `sorry` list: one, `HSyn.glueOutputs_of_leaves` (G1-G17, G19). No other `sorry` in the file.
- Lean check (hsyn-fold, VERIFIED 2026-11-12 00:16 PST): `lake env lean
  scratch/h-decomposition/Leaves.lean` exits 0 (about 1.5 min); one `sorry` warning
  (`HSyn.glueOutputs_of_leaves`); 14 `opaque`, no `axiom`; 69 `#print axioms`, all `propext`,
  `Classical.choice`, `Quot.sound` except `HSyn.sixContactMin_of_leaves` (adds `sorryAx`).

""" + L[old_end:]
r("""**proved** on the Raynaud route: `PkgI2.goodReduction_of_QM_rational3` from the leaves `RaynaudCriterion`, `NeronOggShafarevich`, `TorsionStructure` and the pure-algebra glue Prop `PkgI2.QuatUnipotentTrivial` (hypotheses; rv-a6-route); `QuatUnipotentTrivial` unproved in Lean (paper proof rv-a6-route §3; its valuation step is proved in `scratch/rv-a6-route/QuatVal.lean`, not copied here);""",
  """**proved** on the Raynaud route from the three leaves `RaynaudCriterion`, `NeronOggShafarevich`, `TorsionStructure` alone: `PkgI2.goodReduction_of_QM_rational3` (and `…'` without the auxiliary `w`); `QuatUnipotentTrivial` **proved** (`PkgI2.quatUnipotentTrivial`, glue-a6-alg); the instantiation on the actual `A` (R1) is open;""")
r("| N5 L776-795 | needs Galois representations of abelian varieties with Frobenius | medium |",
  "| N5 L776-795 | Galois side **proved**: `GlueC10.c10` (`r₃ ≅ ρ_{f,3}` from C9's `r₅ ≅ ρ_{f,5}`, the trace identities and semisimplicity, from `ChebotarevExists`, `BrauerNesbittChar0`; Frobenius lift to `G_ℚ` proved), `PkgI3.trace_indep_of_ell` (from T7), glue-c10; continuity of `ρ_ℓ` **proved** (glue-rho-cont, not in `Leaves.lean`); the trace identities (Néron mapping, Serre–Tate specialization, Eichler–Shimura) open | medium |")
r("""(glue-I6-rest, `PkgI6.ramificationIdx_le_factorial`, not copied here; caveat: Glazer's D1 bounds only the local degree, so the passage to a global field, by Krasner or by `D_P ≅ Gal(L_P/ℚ_p)`, is open);""",
  """(glue-I6-rest, `PkgI6.ramificationIdx_le_factorial`, not copied here) and in local form through the decomposition group (`GlueD1Local.D1_local'`, `D1_krasner'`, glue-d1-local); the transports from Glazer's local field (Krasner's choice of `K`, `D_P ≅ Gal(L_P/ℚ_p)` with filtrations) are STANDARD and not in Lean;""")
r("unproved: unramifiedness of `L'` (needs T32), instantiation on the actual `A`",
  "unramifiedness of `L'` (B3(v)) **proved** in glue-b3-unram from `LeafB3a`, `LeafB3b`, `LeafConj` (not in `Leaves.lean`); both Galois halves of the local square-root criterion proved in glue-sqrt-local (disjointness open); unproved: instantiation on the actual `A`")
r("CM elements of `𝒪` (`PkgI1.cm4`, `cm3`, `cm24`);", "CM elements of `𝒪` (`PkgI1.cm4`, `cm3`, `cm24`); normalizer index `[N_B(𝒪):ℚ^×𝒪^×] = 4` and the local normalizers **proved** (glue-vigneras, not in `Leaves.lean`; adelic bookkeeping open);")
r("| G8; R10, T23, T10 | N5 L10939-11000 | needs `B_dR` |", "| G8; R10, T23, T10 | N5 L10939-11000 | `B_dR` is Mathlib's, now shown classical (bdr-kertheta: `ker θ = (ξ)`, `B_dR^+` a complete DVR); T23 stated; the lemma itself open |")
# §5
r("""| WP1 | Review the cheap definitions of `Leaves.lean`; build the shared object layer recommended by rv-leaves-b §2 (I2's `Grp (Over (Spec K))` with `IsAbelianVariety` as the object, I3's `Hom`, `End`, `T_ℓ`, `V_ℓ` through the compiled bridge `RvLeavesB.ofGrp`, one universe, one `galAct`), replacing the three copies;""",
  """| WP1 | Review the cheap definitions of `Leaves.lean`; adopt obj-bridge's shared object layer (built and compiled in `scratch/obj-bridge/Objects.lean`: I2's `Grp (Over (Spec K))` with `IsAbelianVariety` as the object, I3's `Hom`, `End`, `T_ℓ`, `V_ℓ` through `ObjBridge.ofGrp`, a bijection, every leaf restated with a proved equivalence), replacing the copies in `Leaves.lean`;""")
r("| trust in all 39 stated Props (35 leaves) |", "| trust in all 46 stated Props (40 leaves) |")
r("and self-contained T19, T21, T29 | WP1 | 12 textbook leaves |", "and self-contained T19, T21 (T29 for N5's order is proved by glue-vigneras: integrate it) | WP1 | 12 textbook leaves |")
r("""`LeafLocalTwo`; `QuatUnipotentTrivial` (A6; paper proof rv-a6-route §3, a few hundred lines); `SemisimpleBaseChange` (C2, E1; standard algebra); the local-field parts of the square-root criterion and of cyclic inflation (glue-I6-rest §3); D1's local `e ≤ a!`; glue-assembly's "finite-image character is Dirichlet"; T29 (elementary); Prop. TS""",
  """`LeafLocalTwo`; `SemisimpleBaseChange` (C2, E1; standard algebra); the disjointness step of the square-root criterion (glue-sqrt-local) and the local part of cyclic inflation (glue-I6-rest §3); def-ladic-cond's `SwanIndependent`, `AdaptedExists`; integrating glue-a6-alg, glue-c10, glue-d1-local (done in `Leaves.lean`), glue-b3-unram, glue-vigneras, glue-rho-cont into the kernel; glue-assembly's "finite-image character is Dirichlet"; Prop. TS""")
r("| WP5 | ℓ-adic conductors at infinite level (on `PkgI6` and Tau Ceti) |", "| WP5 | ℓ-adic conductors at infinite level (defined by def-ladic-cond, R17 stated there; fold into `Leaves.lean`, prove its glue Props) |")
r("| WP7 | Fontaine's closure (T23) and N5's appendix lemma (G9) as statements over pkg-I4's de Rham layer; principality of `ker θ` |",
  "| WP7 | N5's appendix lemma (G9) over pkg-I4's de Rham layer (T23 now stated, leaf-push; `ker θ` principal and `B_dR` classical, bdr-kertheta); `B_dR`'s Galois action compatibility |")
open(p,'w').write(L); print('ok')
