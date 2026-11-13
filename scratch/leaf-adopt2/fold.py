#!/usr/bin/env python3
"""leaf-adopt2: fold scratch/leaf-push2/LeafPush2.lean into scratch/h-decomposition/Leaves.lean.

One-shot, deterministic. Every replacement asserts that its target occurs exactly once.
Statement-bearing lines of LeafPush2.lean are copied verbatim; only docstrings change
(listed in docs/research/leaf-adopt2.md §1). Run from the repository root.
"""
import sys

LEAVES = "scratch/h-decomposition/Leaves.lean"
SRC = "scratch/leaf-push2/LeafPush2.lean"

src = open(SRC).read().split("\n")
# body: from the module docstring (line 4) through `end ZInQ.LeafPush2`; drop imports and
# the trailing `#print axioms` block.
start = 3
end = src.index("end ZInQ.LeafPush2")
body = "\n".join(src[start:end + 1])


def rep1(text, old, new, label):
    n = text.count(old)
    if n != 1:
        sys.exit(f"[{label}] expected 1 occurrence, found {n}")
    return text.replace(old, new)


# ---------------------------------------------------------------- docstring edits in the copy
LP = ("Lemma P (rv-qm-polar §0): for the fixed `μ` (N5's `2j+ij`) the type-`μ` principal "
      "polarization of `(A, ι)` exists and is unique in characteristic 0, also at CM points "
      "(conditions: type fixed, characteristic 0, `𝒪` maximal; all three hold here); VERIFIED as "
      "an argument, lattice cores compiled (`eq_pm_E0_of_principal`, `type_eq_mu_mul`), published "
      "locators (Buzzard 1997 p. 592; Rotger 2003, 2004) UNVERIFIED")

body = rep1(body,
    "  value `j ∈ ℙ¹` of the Hauptmodul of `X₆/W` (bp-qmmoduli §2.2, existence of the polarization:\n"
    "  SPECULATIVE in the repository, under review in rv-qm-polar; Baba–Granath Thm 2.1 for `X₆/W`).",
    "  value `j ∈ ℙ¹` of the Hauptmodul of `X₆/W` (leaf-adopt2: Lemma P, rv-qm-polar §0: for the\n"
    "  fixed `μ` (N5's `2j+ij`) the type-`μ` principal polarization of `(A, ι)` exists and is unique\n"
    "  in characteristic 0, also at CM points; its conditions (type fixed, characteristic 0, `𝒪`\n"
    "  maximal) all hold here; VERIFIED as an argument, lattice cores compiled\n"
    "  (`eq_pm_E0_of_principal`, `type_eq_mu_mul`), published locators (Buzzard 1997 p. 592; Rotger\n"
    "  2003, 2004) UNVERIFIED; Baba–Granath Thm 2.1 for `X₆/W`).",
    "R3 premise")

body = rep1(body,
    "**Polarization (rv-qm-polar).** The statement is existential in `C` and does not mention a\n"
    "polarization, so it stays a consequence if a QM surface carries several principal polarizations\n"
    "(each gives a curve; Lin–Yang's is one of them). What would change: a form \"for **every** genus-2",
    "**Polarization (rv-qm-polar).** The statement is existential in `C` and does not mention a\n"
    "polarization, so it stays a consequence although a QM surface carries several principal\n"
    "polarizations (rv-qm-polar §1.3: one of each type `c ∈ 𝒪`, `c² = −6`, up to sign; only the\n"
    "type-`μ` one of Lemma P is used, and it gives Lin–Yang's curve).\n"
    "What would change: a form \"for **every** genus-2",
    "R3 polarization")

body = rep1(body,
    "/-!\n# leaf-push2: concrete statements of R18, R22, R3 over the new definitions\n",
    "/-!\n# leaf-push2: concrete statements of R18, R22, R3 over the new definitions\n\n"
    "(leaf-adopt2, 2026-11-12: this section is `scratch/leaf-push2/LeafPush2.lean` copied verbatim,\n"
    "without its imports and `#print axioms`; only the R3 docstring now cites Lemma P of\n"
    "rv-qm-polar. `PkgI3.AbVar` and `PkgI4.IsComplexConj` resolve to this file's copies of the\n"
    "kernel's `ZInQKernel/HDecomp/Objects.lean` definitions. Part I duplicates `DefFaltingsSec` with\n"
    "`PkgI3.AbVar` in place of the local `ZInQ.DefFaltings.AbVar`, see `LeafAdopt.abVarEquiv`.)\n",
    "header")

# The two `_root_` declarations `PeriodPair.lattice1` and `PeriodPair.covolume_lattice1` are
# already in `DefFaltingsSec`, with identical text (checked: diff of the two 17-line blocks is
# empty). They cannot be declared twice, so their second copies are replaced by a comment; every
# reference resolves to the first copy, which is the same definition.
body = rep1(body,
    "/-- The period lattice of a `PeriodPair` as a lattice in `ℂ¹ = Fin 1 → ℂ`. -/\n"
    "noncomputable def _root_.PeriodPair.lattice1 (L : PeriodPair) : Submodule ℤ (Fin 1 → ℂ) :=\n"
    "  ZLattice.comap ℝ L.lattice (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ).toLinearMap\n",
    "/-! leaf-adopt2: `_root_.PeriodPair.lattice1` (the period lattice of a `PeriodPair` in\n"
    "`ℂ¹ = Fin 1 → ℂ`) is declared in `DefFaltingsSec` with this exact text; not re-declared. -/\n",
    "dup lattice1")
body = rep1(body,
    "theorem _root_.PeriodPair.covolume_lattice1 (L : PeriodPair) :\n"
    "    ZLattice.covolume L.lattice1 = ZLattice.covolume L.lattice :=\n"
    "  ZLattice.covolume_comap L.lattice volume volume\n"
    "    (e := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ) (volume_preserving_funUnique (Fin 1) ℂ)\n",
    "/-! leaf-adopt2: `_root_.PeriodPair.covolume_lattice1` is proved in `DefFaltingsSec` with this\n"
    "exact text; not re-declared. -/\n",
    "dup covolume_lattice1")

section = ("section LeafPush2Sec\n\n" + body + "\n\nend LeafPush2Sec\n")

t = open(LEAVES).read()

t = rep1(t, "end LeafAdoptSec\n", "end LeafAdoptSec\n\n" + section, "insert")

# ---------------------------------------------------------------- file header
t = rep1(t,
    "`R1pi0Props`, `R2X6PropsIff`, `R5fpStrong`, `H5`, and the bridge `abVarEquiv`). The placeholders\n"
    "are now R1(b), R3, R17, R18, R22, T10-T12 (8 `opaque`). The Shimura-curve leaves rest on the\n"
    "SPECULATIVE premise bp-qmmoduli §2.2, and the height leaves are not yet known to be non-vacuous\n"
    "(AN3 open); see the docstrings and `docs/research/leaf-adopt.md`.\n\n"
    "No `axiom` declarations. Leaf numbering (R1-R22 and H5 research-level, T1-T34 textbook, T32 now\n"
    "glue) is that of the note's §2.",
    "`R1pi0Props`, `R2X6PropsIff`, `R5fpStrong`, `H5`, and the bridge `abVarEquiv`).\n\n"
    "leaf-adopt2 (2026-11-12) added `LeafPush2Sec` after `LeafAdoptSec`: scratch/leaf-push2 copied\n"
    "verbatim, with R3 (`ZInQ.LeafPush2.R03_LinYang`), R18 (`R18_Javanpeykar`), R22 (`R22_Pazuki`),\n"
    "T11 (`T11a_RiemannEnd`, `T11b_Rigidity`), the new textbook leaf T35 (`UniformizationExists`,\n"
    "AN3 for abelian varieties) and the glue target `T12_ComplexConjEigen` (T12 is now glue). The\n"
    "placeholders are now R1(b), R17, T10 (3 `opaque`). The Shimura-curve leaves (R1, R2, R5) and\n"
    "R3 rest on Lemma P of rv-qm-polar (type `μ` fixed, characteristic 0, `𝒪` maximal), a published\n"
    "input folded into each leaf because polarizations cannot be stated in Lean yet; the height\n"
    "leaves (R18-R22, H5) are not yet known to be non-vacuous (AN3 open); see the docstrings,\n"
    "`docs/research/leaf-adopt.md` and `docs/research/leaf-adopt2.md`.\n\n"
    "No `axiom` declarations. Leaf numbering (R1-R22 and H5 research-level, T1-T35 textbook, T12 and\n"
    "T32 now glue) is that of the note's §2.",
    "file header")

# ---------------------------------------------------------------- leaf-qm-fp docstrings (Lemma P)
t = rep1(t,
    "/-- **An abelian surface over `K` with QM by `𝒪` and a level-3 structure.** (No polarization:\n"
    "for this datum a principal polarization with Rosati involution `x ↦ μ⁻¹x̄μ` on `ι(𝒪)` exists and\n"
    "is unique, bp-qmmoduli §2.2, whose lattice core is `BPQM.eq_pm_E0_of_principal`.) -/",
    "/-- **An abelian surface over `K` with QM by `𝒪` and a level-3 structure.** (No polarization:\n"
    "for this datum and a fixed `μ` (N5's `2j+ij`) a principal polarization with Rosati involution\n"
    "`x ↦ μ⁻¹x̄μ` on `ι(𝒪)` exists and is unique in characteristic 0, also at CM points: Lemma P of\n"
    "rv-qm-polar §0 (= bp-qmmoduli §2.2 with the type fixed), VERIFIED as an argument, lattice cores\n"
    "compiled (`BPQM.eq_pm_E0_of_principal`, rv-qm-polar `type_eq_mu_mul`), published locators\n"
    "UNVERIFIED. Without fixing `μ` it is not unique.) -/",
    "QML3")

t = rep1(t,
    "`Spec K` for fields `K`; projective implies proper. `M3 K` drops `λ` (bp-qmmoduli §2.2: for this\n"
    "datum `λ` exists and is unique in characteristic 0; SPECULATIVE until reviewed, lattice core\n"
    "proved as `BPQM.eq_pm_E0_of_principal`; not needed on Buzzard's route), and puts `η` on",
    "`Spec K` for fields `K`; projective implies proper. `M3 K` drops `λ` (Lemma P, rv-qm-polar §0:\n"
    "for a fixed `μ` (N5's `2j+ij`) the type-`μ` principal polarization of `(A, ι)` exists and is\n"
    "unique in characteristic 0, also at CM points; VERIFIED as an argument, lattice cores compiled\n"
    "(`BPQM.eq_pm_E0_of_principal`, `type_eq_mu_mul`), published locators UNVERIFIED; not needed on\n"
    "Buzzard's route), and puts `η` on",
    "R1fp a")

t = rep1(t,
    "`E(G,h) = ℚ`) still needs a human check. (ii) On the Shimura–Deligne route the leaf is \"published\n"
    "theorem + bp-qmmoduli §2.2\" (existence and uniqueness of `λ` for `(A, ι)`), and §2.2 is\n"
    "SPECULATIVE (unreviewed; uniqueness checked by the leaf-qm-fp review, existence over `ℂ` by class\n"
    "number one and the sign argument, unformalized). On Buzzard's route",
    "`E(G,h) = ℚ`) still needs a human check. (ii) On the Shimura–Deligne route the leaf is \"published\n"
    "theorem for the type-`μ` PEL problem + Lemma P\" (rv-qm-polar §2: a consequence, independent of\n"
    "the choice of `μ`; Lemma P is folded into the leaf because polarizations cannot be stated in Lean\n"
    "yet; if the sources print only uniqueness, its existence half is glue, argued in rv-qm-polar\n"
    "§1.2 with the lattice core and sign step compiled, class number one and the descent from `ℂ`\n"
    "not in Lean). On Buzzard's route",
    "R1fp b")

t = rep1(t,
    "space `X₆` (STANDARD); the points of `X₆` are QM pairs `(A, ι)`, which uses bp-qmmoduli §2.2\n"
    "(the polarization exists and is unique; SPECULATIVE, see `R1fp`);",
    "space `X₆` (STANDARD); the points of `X₆` are QM pairs `(A, ι)`, which uses Lemma P\n"
    "(the type-`μ` polarization exists and is unique; rv-qm-polar, see `R1fp`);",
    "R5fp")

t = rep1(t,
    "2^{#{p | D(R)N(R)}} h(R)` with `N = 1`; points of `X₆(ℚ̄)` are classes of QM pairs (bp-qmmoduli\n"
    "§2.2, SPECULATIVE). **Not** the",
    "2^{#{p | D(R)N(R)}} h(R)` with `N = 1`; points of `X₆(ℚ̄)` are classes of QM pairs (Lemma P,\n"
    "rv-qm-polar; see `R1fp`). **Not** the",
    "R5fpCount")

t = rep1(t,
    "bp-qmmoduli §2.2 (the polarization of a QM pair `(A, ι)` exists and is unique; SPECULATIVE until\n"
    "reviewed), because `QML3`/`QMPair` omit `λ`. Polarizations cannot be stated in Lean today\n"
    "(no dual abelian variety), so §2.2 cannot be carried as a separate Lean hypothesis. -/",
    "Lemma P (rv-qm-polar §0: for a fixed `μ` the type-`μ` principal polarization of a QM pair\n"
    "`(A, ι)` exists and is unique in characteristic 0; VERIFIED as an argument, published locators\n"
    "UNVERIFIED), because `QML3`/`QMPair` omit `λ`. Polarizations cannot be stated in Lean today\n"
    "(no dual abelian variety), so Lemma P cannot be carried as a separate Lean hypothesis. -/",
    "QMLeaves")

# ---------------------------------------------------------------- LeafAdoptSec docstrings
t = rep1(t,
    "**SPECULATIVE premise (bp-qmmoduli §2.2).** `QML3` and `QMPair` omit the polarization `λ`. Every\n"
    "clause is the published statement (Shimura 1967 Main Thms I-II; Deligne 1971 Thm 4.21, Cor. 5.7,\n"
    "Ex. 5.8, §§2, 4.8-4.17; Baba–Granath 2008 Thm 2.1, Lemma 3.1, §3.1; González–Rotger 2006\n"
    "Prop. 5.6, Thm 5.12) or a consequence of it **only together with** bp-qmmoduli §2.2: for a QM pair\n"
    "`(A, ι)` in characteristic 0 a principal polarization with Rosati involution `x ↦ μ⁻¹x̄μ` exists\n"
    "and is unique. §2.2 is SPECULATIVE: its uniqueness half and lattice core were checked by\n"
    "model reviews (leaf-qm-fp, rv-blueprints, which also verified the sign claim numerically), its\n"
    "existence half (class number one and the sign argument; Lefschetz principle) is unformalized and\n"
    "has no human review. Polarizations cannot be stated in Lean today, so §2.2 cannot be a separate\n"
    "hypothesis. Buzzard's polarization-free moduli problem would remove it (UNVERIFIED for full level\n"
    "3).",
    "**Premise: Lemma P (rv-qm-polar §0; leaf-adopt2).** `QML3` and `QMPair` omit the polarization\n"
    "`λ`. Every clause is the published statement for the type-`μ` PEL problem (Shimura 1967 Main\n"
    "Thms I-II; Deligne 1971 Thm 4.21, Cor. 5.7, Ex. 5.8, §§2, 4.8-4.17; Baba–Granath 2008 Thm 2.1,\n"
    "Lemma 3.1, §3.1; González–Rotger 2006 Prop. 5.6, Thm 5.12) or a consequence of it **together\n"
    "with** Lemma P: for a fixed `μ` (N5's `2j+ij`), a QM pair `(A, ι)` over a field of characteristic\n"
    "0 (`𝒪` maximal) has exactly one principal polarization with Rosati involution `x ↦ μ⁻¹x̄μ` on\n"
    "`ι(𝒪)`, also at CM points (rv-qm-polar §2: no statement needs correcting, and the λ-free\n"
    "clauses do not depend on the choice of `μ`). Lemma P is VERIFIED as an argument (rv-qm-polar\n"
    "§1.2; lattice core and sign step compiled: `eq_pm_E0_of_principal`, `type_eq_mu_mul`,\n"
    "`lemmaP_lattice`; class number one and the descent from `ℂ` not in Lean); its published locators\n"
    "(Buzzard 1997 p. 592; Rotger 2003, 2004) are UNVERIFIED, and if they print only uniqueness its\n"
    "existence half becomes glue. Without fixing `μ` the polarization is not unique (one per type\n"
    "`c`, `c² = −6`, up to sign; `two_principal_types`). Polarizations cannot be stated in Lean today,\n"
    "so Lemma P is folded into the leaf rather than a separate hypothesis. Buzzard's\n"
    "polarization-free moduli problem would remove it (UNVERIFIED for full level 3).",
    "R1R2fpRep")

t = rep1(t,
    "for `b = 0`, `[ℚ(x):ℚ] = #Pic R`. SPECULATIVE premise bp-qmmoduli §2.2 as for `R1R2fpRep`. -/",
    "for `b = 0`, `[ℚ(x):ℚ] = #Pic R`. Premise Lemma P (rv-qm-polar) as for `R1R2fpRep`. -/",
    "R5fpStrong")

# ---------------------------------------------------------------- HSyn §2: R1(b) and the placeholders
t = rep1(t,
    "`LeafAdopt.R5fp_iff_R5fpStrong`) and `LeafQM.AV.R5fpCount`. All of them rest on the SPECULATIVE\n"
    "premise bp-qmmoduli §2.2 (see `LeafAdopt.R1R2fpRep`). Part (b) of R1 stays a placeholder: -/",
    "`LeafAdopt.R5fp_iff_R5fpStrong`) and `LeafQM.AV.R5fpCount`. All of them rest on Lemma P of\n"
    "rv-qm-polar (type `μ` fixed, characteristic 0, `𝒪` maximal; see `LeafAdopt.R1R2fpRep`;\n"
    "leaf-adopt2). Part (b) of R1 stays a placeholder: -/",
    "R1 comment")

t = rep1(t,
    "and of abelian varieties (large; bp-qmmoduli N14). Rests on bp-qmmoduli §2.2 as R1R2fpRep. -/",
    "and of abelian varieties (large; bp-qmmoduli N14). Rests on Lemma P (rv-qm-polar) as R1R2fpRep.\n"
    "Part (a) at a single point is `ZInQ.LeafPush2.UniformizationExists` (T35) for `QML3 ℂ` plus the\n"
    "QM lattice computation (bp-analytic Q1); (b) and (c) are the family statements still missing. -/",
    "R1b")

old_r3 = t[t.index("/-- **R3. Lin–Yang.** On the finite nonzero"):t.index("opaque R03_LinYang : Prop\n") + len("opaque R03_LinYang : Prop\n")]
t = rep1(t, old_r3,
    "/-! leaf-adopt2 (2026-11-12): the placeholder `R03_LinYang` is replaced by leaf-push2's\n"
    "`ZInQ.LeafPush2.R03_LinYang` (section `LeafPush2Sec`): over `ℂ`, every abelian surface with\n"
    "`𝒪 ↪ End A` is `≅ Jac C` for a curve `C` with a sextic model on the Lin–Yang family at some\n"
    "`j ≠ 0`, or a product of elliptic curves. A consequence of Lin–Yang Example 29 with Weil's\n"
    "dichotomy and Lemma P (rv-qm-polar). The `J`/Igusa–Clebsch convention is tied to hdec-elementary's\n"
    "`OnQMLocus` (`ZInQ.LeafPush2.linYangTuple_onQMLocus`, proved). The `ℚ̄`-form\n"
    "`R03_LinYang_algClosed` is a glue target (Lefschetz principle). -/\n",
    "R3 opaque")

old_r18 = t[t.index("/-- **R18. Javanpeykar.** A smooth projective"):t.index("opaque R18_Javanpeykar : Prop\n") + len("opaque R18_Javanpeykar : Prop\n")]
t = rep1(t, old_r18,
    "/-! leaf-adopt2 (2026-11-12): the placeholder `R18_Javanpeykar` is replaced by leaf-push2's\n"
    "`ZInQ.LeafPush2.R18_Javanpeykar` (section `LeafPush2Sec`): over a number field `K`, for a pointed\n"
    "curve `X` with Jacobian `J` (`IsJacobian`), `g = dim J ≥ 1` and a Belyi function `t ∈ K(X)` of\n"
    "degree `d > 0`, `stableFaltingsHeight J ≤ 13·10⁶ · g · d⁵` (in `EReal`). A consequence of ANT 8\n"
    "(2014) Thm 1.1.1 with H5. Its height is leaf-push2's copy of def-faltings' height over\n"
    "`PkgI3.AbVar`. -/\n",
    "R18 opaque")

old_r22 = t[t.index("/-- **R22. Pazuki** (repaired after the locator audit"):t.index("opaque R22_Pazuki : Prop\n") + len("opaque R22_Pazuki : Prop\n")]
t = rep1(t, old_r22,
    "/-! leaf-adopt2 (2026-11-12): the placeholder `R22_Pazuki` is replaced by leaf-push2's\n"
    "`ZInQ.LeafPush2.R22_Pazuki` (section `LeafPush2Sec`): the audit's upper half\n"
    "`h([θ_m(0, Ω)]) ≤ X/2 + C₂ log(X + 2)` for `X ≥ max(1, h_F + log π)`, for every abelian surface\n"
    "over a number field, every analytic uniformization at every complex place and every `Ω ∈ 𝔥₂`\n"
    "that is a period matrix of its lattice (all principal polarizations, no polarization object).\n"
    "Consequence of Bull. SMF 140 (2012) Cor. 1.3(2) with H5; the identification of Pazuki's level-2\n"
    "coordinates (Def. 2.6) with `θ[a;b](0, Ω)` is UNVERIFIED (the main risk). The glue form with\n"
    "`X = max(1, h_F + 3)` is `ZInQ.LeafPush2.R22_plus3` (proved). -/\n",
    "R22 opaque")

old_t11 = t[t.index("/-- **T11. Riemann's theorem, GAGA, rigidity.**"):t.index("opaque T12_ArtinComparison : Prop\n") + len("opaque T12_ArtinComparison : Prop\n")]
t = rep1(t, old_t11,
    "/-! leaf-adopt2 (2026-11-12): the placeholders `T11_RiemannGAGA` and `T12_ArtinComparison` are\n"
    "removed. T11 is now the two concrete textbook leaves `ZInQ.LeafPush2.T11a_RiemannEnd`\n"
    "(endomorphisms of `A/ℂ` = `ℂ`-linear maps preserving the lattice of a uniformization) and\n"
    "`ZInQ.LeafPush2.T11b_Rigidity` (`Hom(A_L, B_L) = Hom(A, B)` over `k = k̄` of characteristic 0).\n"
    "T12 is glue: its used form `ZInQ.LeafPush2.T12_ComplexConjEigen` (the `±1`-eigenspaces of complex\n"
    "conjugation on `V_ℓ(A)` have dimension `dim A`) is a glue target from T35, T5, T26 and the\n"
    "antiholomorphy of complex conjugation. The new textbook leaf T35 is\n"
    "`ZInQ.LeafPush2.UniformizationExists` (AN3 for abelian varieties: Mumford §1 with GAGA); it is\n"
    "kept instead of bp-analytic's `UniformizationLeaf` (docs/research/leaf-adopt2.md §2): its\n"
    "predicate is the one R22 and T11a quantify over, it ties `g` to `dim A`, and it covers every\n"
    "`K` with `σ : K → ℂ`. -/\n",
    "T11 T12 opaque")

t = rep1(t,
    "`LeafPush.T32a_TameQuadratic` and `LeafPush.T32b_QuadraticRamification` (consequences).\n"
    "leaf-adopt (2026-11-12): T32 is now glue, proved (`HSyn.t32a_glue`, `HSyn.t32b_glue`, §3). -/",
    "`LeafPush.T32a_TameQuadratic` and `LeafPush.T32b_QuadraticRamification` (consequences).\n"
    "leaf-adopt (2026-11-12): T32 is now glue, proved (`HSyn.t32a_glue`, `HSyn.t32b_glue`, §3).\n"
    "leaf-adopt2 (2026-11-12): T12 is now glue (target `ZInQ.LeafPush2.T12_ComplexConjEigen`,\n"
    "unproved). -/",
    "glue comment")

# ---------------------------------------------------------------- glue: one identification, proved
t = rep1(t,
    "/-- **B3(v) with no leaf** (glue-t32a): `LeafB3a` of glue-b3-unram is proved. -/",
    "/-- **The two complex-conjugation predicates agree** (leaf-adopt2): leaf-push2's\n"
    "`ZInQ.LeafPush2.IsComplexConj` (used by `T12_ComplexConjEigen`) is pkg-I4's\n"
    "`PkgI4.IsComplexConj` (used by the oddness of `GaloisRep`s, G10), by definition. -/\n"
    "theorem isComplexConj_leafPush2_iff (c : Field.absoluteGaloisGroup ℚ) :\n"
    "    ZInQ.LeafPush2.IsComplexConj c ↔ PkgI4.IsComplexConj c :=\n"
    "  Iff.rfl\n\n"
    "/-- **B3(v) with no leaf** (glue-t32a): `LeafB3a` of glue-b3-unram is proved. -/",
    "isComplexConj glue")

# ---------------------------------------------------------------- bundles
t = rep1(t,
    "R2, R5 (leaf-qm-fp, repaired), R16 (leaf-modcurves), R19-R21 and H5 (def-faltings). Remaining\n"
    "placeholders: R1(b), R3, R17, R18, R22. -/",
    "R2, R5 (leaf-qm-fp, repaired), R16 (leaf-modcurves), R19-R21 and H5 (def-faltings);\n"
    "leaf-adopt2 (2026-11-12): R3, R18, R22 (leaf-push2). Remaining placeholders: R1(b), R17. -/",
    "RL doc")

t = rep1(t,
    "  SPECULATIVE premise bp-qmmoduli §2.2 (polarization exists and is unique), see the definition. -/",
    "  Premise Lemma P of rv-qm-polar (type-`μ` polarization exists and is unique), see the definition. -/",
    "RL r1r2")
t = rep1(t,
    "  /-- R1(d), Shimura reciprocity, object form (leaf-qm-fp; premise bp-qmmoduli §2.2). -/",
    "  /-- R1(d), Shimura reciprocity, object form (leaf-qm-fp; premise Lemma P, rv-qm-polar). -/",
    "RL r1rec")
t = rep1(t,
    "  r3 : R03_LinYang\n",
    "  /-- R3, Lin–Yang over `ℂ`, existential and polarization-free (leaf-push2; premise Lemma P). -/\n"
    "  r3 : ZInQ.LeafPush2.R03_LinYang\n",
    "RL r3")
t = rep1(t,
    "  premise bp-qmmoduli §2.2). -/\n  r5 : LeafQM.AV.R5fp",
    "  premise Lemma P, rv-qm-polar). -/\n  r5 : LeafQM.AV.R5fp",
    "RL r5")
t = rep1(t,
    "  /-- R5(i), González–Rotger Prop. 5.6, `#CM(R) = 2^b h(R)` (premise bp-qmmoduli §2.2). -/",
    "  /-- R5(i), González–Rotger Prop. 5.6, `#CM(R) = 2^b h(R)` (premise Lemma P, rv-qm-polar). -/",
    "RL r5count")
t = rep1(t,
    "  r18 : R18_Javanpeykar\n",
    "  /-- R18, Javanpeykar, over leaf-push2's stable Faltings height on `PkgI3.AbVar` (with H5). -/\n"
    "  r18 : ZInQ.LeafPush2.R18_Javanpeykar\n",
    "RL r18")
t = rep1(t,
    "  r22 : R22_Pazuki\n",
    "  /-- R22, Pazuki's upper half, over all uniformizations and period matrices (leaf-push2). -/\n"
    "  r22 : ZInQ.LeafPush2.R22_Pazuki\n",
    "RL r22")

t = rep1(t,
    "  t11 : T11_RiemannGAGA\n  t12 : T12_ArtinComparison\n",
    "  /-- T11(a), Riemann/GAGA for endomorphisms (leaf-push2). -/\n"
    "  t11a : ZInQ.LeafPush2.T11a_RiemannEnd\n"
    "  /-- T11(b), rigidity of homomorphisms under extension of an algebraically closed field\n"
    "  (leaf-push2). -/\n"
    "  t11b : ZInQ.LeafPush2.T11b_Rigidity\n"
    "  -- leaf-adopt2: T12 is glue (`ZInQ.LeafPush2.T12_ComplexConjEigen`, a target), no longer a field.\n",
    "TL t11")
t = rep1(t,
    "  t34 : LeafModCurves.DimJ1Genus\n",
    "  t34 : LeafModCurves.DimJ1Genus\n"
    "  /-- T35 (new, leaf-push2): analytic uniformization of `A(ℂ)_σ` by `ℂ^{dim A}` with a full\n"
    "  lattice (Mumford §1 with GAGA; AN3 for abelian varieties). -/\n"
    "  t35 : ZInQ.LeafPush2.UniformizationExists\n",
    "TL t35")

# ---------------------------------------------------------------- #print axioms for the new section
pa = "\n".join(l for l in src[end + 1:] if l.startswith("#print axioms"))
pa += "\n#print axioms HSyn.isComplexConj_leafPush2_iff\n"
t = t.rstrip("\n") + "\n" + pa

open(LEAVES, "w").write(t)
print("ok", len(t.split("\n")), "lines")
