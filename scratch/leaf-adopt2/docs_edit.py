#!/usr/bin/env python3
"""leaf-adopt2: update docs/research/h-decomposition.md (leaf table, counts, glue, remaining work).
One-shot; every replacement asserts its target count. Run from the repository root."""
import sys

P = "docs/research/h-decomposition.md"
t = open(P).read()


def rep(old, new, label, count=1):
    global t
    n = t.count(old)
    if n != count:
        sys.exit(f"[{label}] expected {count}, found {n}")
    t = t.replace(old, new)


# §0 claim
rep("**33 textbook theorems** in six groups (T32 is now proved glue; T33, T34 added by leaf-adopt)",
    "**33 textbook theorems** in six groups (T32 is now proved glue and T12 glue; T33, T34 added by\n"
    "leaf-adopt, T35 by leaf-adopt2)", "claim")

# §0 what is in Lean today
rep("`axiom`, one `sorry`). *Counts after leaf-adopt (2026-11-12)*: **48 of 56 leaves** are stated",
    "`axiom`, one `sorry`). *Counts after leaf-adopt2 (2026-11-12)*: **53 of 56 leaves** are stated\n"
    "concretely (21 of 23 research-level: R2-R16, R18-R22, H5, with R11 and R12 through their joint\n"
    "consequence; 32 of 33 textbook: T1-T11, T13-T31, T33-T35), parts (a), (c), (d) of R1 and\n"
    "`π₀(X₆) = 1` are concrete while R1(b) is a placeholder, and **2 leaves are placeholders** (R17,\n"
    "T10). The bundles have 64 fields: 61 concrete Props and 3 placeholders (R1(b), R17, T10). The\n"
    "Shimura-curve leaves and R3 rest on Lemma P of rv-qm-polar (type `μ` fixed, characteristic 0,\n"
    "`𝒪` maximal; folded into each leaf, published locators UNVERIFIED), and the leaves over the\n"
    "Faltings height (R18-R22, H5) are not yet known to be non-vacuous (§2.1 R1, R19, H5;\n"
    "docs/research/leaf-adopt2.md). *Superseded counts after leaf-adopt*: **48 of 56 leaves** were stated",
    "lean today")

rep("(def-faltings, the stable Faltings height as an infimum over smooth group models) are now\n"
    "stated concretely; still missing:",
    "(def-faltings, the stable Faltings height as an infimum over smooth group models) are now\n"
    "stated concretely. *Update (leaf-adopt2, 2026-11-12):* 3 (over `ℂ`, existential, via sextic\n"
    "models and Igusa's `J`'s), 18 (with `g := dim J`), 22 (via period matrices, no polarization\n"
    "object) and T11 are stated too (leaf-push2), T12 is glue, and the new textbook leaf T35\n"
    "(`UniformizationExists`) states the analytic uniformization without analytification; still\n"
    "missing after leaf-adopt2: R1(b) in family form, T10 in Galois-equivariant form (Mathlib\n"
    "v4.35's `Scheme.EllAdicCohomology` is only an abelian group), the fold of def-ladic-cond (17).\n"
    "*As leaf-adopt left it:* still missing:",
    "cannot be stated")

rep("theorems and 33 textbook results listed, plus 20 glue steps; in Lean, 48 of these 56 leaves (and\n"
    "three of the four parts of a 49th, R1) are stated concretely, and the last part of the glue is\n"
    "proved.\" (Counts as of leaf-adopt, 2026-11-12; with the caveats that the Shimura-curve leaves\n"
    "rest on the SPECULATIVE premise bp-qmmoduli §2.2 and that the height leaves R19-R21, H5 are not\n"
    "yet known to be non-vacuous.)",
    "theorems and 33 textbook results listed, plus 20 glue steps; in Lean, 53 of these 56 leaves (and\n"
    "three of the four parts of a 54th, R1) are stated concretely, and the last part of the glue is\n"
    "proved.\" (Counts as of leaf-adopt2, 2026-11-12; with the caveats that the Shimura-curve leaves\n"
    "and R3 rest on Lemma P of rv-qm-polar, a published input folded into each leaf whose locators are\n"
    "UNVERIFIED, and that the height leaves R18-R22, H5 are not yet known to be non-vacuous.)",
    "exact claim")

# §0 change log
rep("- **Counts**: 54 → 56 leaves (22 → 23 research with H5; 32 → 33 textbook: −T32, +T33, +T34);\n"
    "  concrete 40 → 48 (plus R1 in part); placeholders 14 → 7 (plus R1(b)).\n",
    "- **Counts**: 54 → 56 leaves (22 → 23 research with H5; 32 → 33 textbook: −T32, +T33, +T34);\n"
    "  concrete 40 → 48 (plus R1 in part); placeholders 14 → 7 (plus R1(b)).\n\n"
    "**Changes since leaf-adopt (leaf-adopt2, 2026-11-12).** Report: docs/research/leaf-adopt2.md.\n"
    "VERIFIED: `lake env lean scratch/h-decomposition/Leaves.lean` exits 0 (about 4 min), one `sorry`\n"
    "(`HSyn.glueOutputs_of_leaves`), 3 `opaque`, no `axiom`; every new `#print axioms` is `propext`,\n"
    "`Classical.choice`, `Quot.sound`.\n"
    "- **leaf-push2** copied verbatim as section `LeafPush2Sec` (namespace `ZInQ.LeafPush2`; only\n"
    "  docstrings changed, and two `_root_` declarations already present with identical text in\n"
    "  `DefFaltingsSec` are not re-declared). New bundle fields: `r3 : ZInQ.LeafPush2.R03_LinYang`,\n"
    "  `r18 : R18_Javanpeykar`, `r22 : R22_Pazuki`, `t11a : T11a_RiemannEnd`, `t11b : T11b_Rigidity`,\n"
    "  `t35 : UniformizationExists`. The placeholders `R03_LinYang`, `R18_Javanpeykar`, `R22_Pazuki`,\n"
    "  `T11_RiemannGAGA`, `T12_ArtinComparison` are removed. T12 is glue: its used form\n"
    "  `T12_ComplexConjEigen` is a glue target (from T35, T5, T26), not a field.\n"
    "- **T35 = `UniformizationExists`** (Mumford §1 with GAGA) is kept rather than bp-analytic's\n"
    "  `UniformizationLeaf`: its predicate is the one R22 and T11a quantify over, it ties `g` to\n"
    "  `dim A` (bp-analytic's `g` is existential), and it covers every `K` with `σ : K → ℂ`\n"
    "  (bp-analytic: `K = ℂ`). bp-analytic's stronger predicate (local coordinates, continuity of\n"
    "  `φ⁻¹`) and its proved glue (uniqueness, analytic representation, torsion) remain the blueprint\n"
    "  for proving T35 and for the T12 glue (leaf-adopt2 §2).\n"
    "- **rv-qm-polar applied**: the docstrings of `QML3`, `R1fp`, `R5fp`, `R5fpCount`, `QMLeaves`,\n"
    "  `R1R2fpRep`, `R5fpStrong`, R1(b), the bundle fields and R3 cite Lemma P with its conditions\n"
    "  (type `μ` fixed, characteristic 0, `𝒪` maximal) instead of the SPECULATIVE bp-qmmoduli §2.2;\n"
    "  no statement changed (rv-qm-polar §2: none needs correcting).\n"
    "- **Glue**: `HSyn.isComplexConj_leafPush2_iff` (proved, `Iff.rfl`) identifies leaf-push2's\n"
    "  complex-conjugation predicate with pkg-I4's. Proved glue now in the file: `R22_plus3`,\n"
    "  `R18_real`, `linYangTuple_onQMLocus`, `onQMLocus_of_linYangTuple`, `linYang_j_eq`,\n"
    "  `R03_of_algClosed`, `exists_isComplexConj`, `isSiegel_I`, `javanpeykarBound_pos`, `_mono`. New\n"
    "  glue targets (unproved): `T12_ComplexConjEigen`, `R03_LinYang_algClosed` (Lefschetz).\n"
    "- **Counts**: concrete 48 → **53 of 56** (plus R1 in part); placeholders 7 → **2** (R17, T10)\n"
    "  plus R1(b); bundle fields 63 → 64 (61 concrete, 3 `opaque`).\n",
    "changelog")

# §2.1 premise text, three occurrences
OLD_PREM = ("**SPECULATIVE premise**: like every leaf over leaf-qm-fp's objects, it is the published "
            "statement or a consequence of it only together with bp-qmmoduli §2.2 (a QM pair `(A, ι)` "
            "in characteristic 0 has a unique principal polarization with Rosati involution "
            "`x ↦ μ⁻¹x̄μ`; `QML3`, `QMPair` omit `λ`); §2.2's uniqueness half was checked by model "
            "reviews, its existence half is unformalized, and no human has reviewed it.")
NEW_PREM = ("**Premise: Lemma P** (rv-qm-polar §0; leaf-adopt2): like every leaf over leaf-qm-fp's "
            "objects, it is the published statement for the type-`μ` PEL problem, or a consequence "
            "of it, together with Lemma P: for a fixed `μ` (N5's `2j+ij`), a QM pair `(A, ι)` over a "
            "field of characteristic 0, `𝒪` maximal, has exactly one principal polarization whose "
            "Rosati involution is `x ↦ μ⁻¹x̄μ` on `ι(𝒪)`, also at CM points (`QML3`, `QMPair` omit "
            "`λ`; rv-qm-polar §2: no statement needs correcting, and the λ-free statements do not "
            "depend on the choice of `μ`). Lemma P is VERIFIED as an argument (rv-qm-polar §1.2; "
            "lattice core and sign step compiled, class number one and the descent from `ℂ` not in "
            "Lean); its published locators (Buzzard 1997 p. 592; Rotger 2003, 2004) are UNVERIFIED, "
            "and if they print only uniqueness, existence is glue. Without fixing `μ` the "
            "polarization is not unique (rv-qm-polar §1.3). Lemma P is folded into the leaf because "
            "polarizations cannot be stated in Lean yet.")
rep(OLD_PREM, NEW_PREM, "premise", count=3)

# R3
rep("Lean: **no** (QM locus). Steps A7, F1. (The Igusa-invariant side is cheap; hdec-elementary\n"
    "proves in Lean the algebraic identity `j = 3779136·I₁₀²/I₄⁵` on its Igusa–Clebsch form of the\n"
    "locus, `HDec.j_eq_of_onQMLocus`.)",
    "Lean: **yes** since leaf-adopt2 (below). Steps A7, F1. (The Igusa-invariant side is cheap;\n"
    "hdec-elementary proves in Lean the algebraic identity `j = 3779136·I₁₀²/I₄⁵` on its\n"
    "Igusa–Clebsch form of the locus, `HDec.j_eq_of_onQMLocus`.)\n"
    "*Lean (leaf-adopt2, 2026-11-12).* **Concrete** (leaf-push2): `ZInQ.LeafPush2.R03_LinYang`. Every\n"
    "abelian surface `A/ℂ` (`A.dim = 2`) with an injective unital `ι : 𝒪 → End A` (`QMStr`) is either\n"
    "`≅ Jac C` as group schemes, for a smooth proper geometrically connected integral curve `C` whose\n"
    "function field is `ℂ(x)[y]/(y² − a∏(x−rᵢ))` (six distinct roots) with `LinYangTuple a r j` at\n"
    "some `j ≠ 0`, or `≅ E₁ × E₂` with `dim Eᵢ = 1`. Consequence of Example 29 at `j ≠ 0, ∞`, with\n"
    "Weil's dichotomy at `j ∈ {0, ∞}` (where the tuple has `J₁₀ = 0`; Weil 1957, UNVERIFIED) and\n"
    "Lemma P (premise above; its conditions hold over `ℂ`). Existential in `C` and polarization-free,\n"
    "so it is unaffected by the several principal polarizations of `(A, ι)` (rv-qm-polar §1.3). The\n"
    "`J`/Igusa–Clebsch convention is tied to hdec-elementary's `OnQMLocus`\n"
    "(`linYangTuple_onQMLocus`, proved); F1's `j = 3779136·I₁₀²/I₄⁵` on the first branch is\n"
    "`linYang_j_eq` (proved). Not stated: the link `j = π₆(x)` to the moduli point (needs leaf-qm-fp's\n"
    "`X₆` package). The `ℚ̄`-form `R03_LinYang_algClosed` is a glue target (Lefschetz principle).\n"
    "Open check: the tuple is compared with hdec-elementary's transcription, not with the printed\n"
    "(13)-(14) or Baba–Granath Prop. 3.6.",
    "R3")

# R18
rep("bounds the minimal Belyi degree. CONSEQUENCE (audit) of the printed bound; the inequality itself\n"
    "is as printed. Lean: **no**\n(Faltings height). Step E2.",
    "bounds the minimal Belyi degree. CONSEQUENCE (audit) of the printed bound; the inequality itself\n"
    "is as printed. Lean: **yes** since leaf-adopt2. Step E2.\n"
    "*Lean (leaf-adopt2, 2026-11-12).* **Concrete** (leaf-push2): `ZInQ.LeafPush2.R18_Javanpeykar`.\n"
    "Over a number field `K`: a smooth proper geometrically connected integral curve `X/K` with a\n"
    "`K`-point `P₀`, its Jacobian `J` (`IsJacobian X P₀ J aj`, over `PkgI3.AbVar`), `g = dim J ≥ 1`,\n"
    "a Belyi function `t ∈ K(X)` (`IsBelyiFunction`) of degree `d = [K(X) : K(t)] > 0`:\n"
    "`stableFaltingsHeight J ≤ 13·10⁶ · g · d⁵` in `EReal`. Consequence of Thm 1.1.1 with H5 (base\n"
    "change to `ℚ̄`; `deg_B ≤ d`; either Faltings' or Deligne's normalization). The `EReal` form asserts\n"
    "`h < ⊤`, so the leaf is also \"correctness of the definition\" (H5's finiteness half), and it is\n"
    "over leaf-push2's copy of the height on `PkgI3.AbVar`, while the bundle's H5 is over\n"
    "def-faltings' copy (same text, `AbVar` replaced; identifying the two heights through\n"
    "`LeafAdopt.abVarEquiv` is unproved glue, WP1). `R18_real` (the real-valued form) is proved.",
    "R18")

# R22
rep("SMF 140 (2012), Cor. 1.3(2) (read by a model). C (hardened). Lean:\n"
    "**no** (Faltings height, theta constants). Step F3.",
    "SMF 140 (2012), Cor. 1.3(2) (read by a model). C (hardened). Lean:\n"
    "**yes** since leaf-adopt2 (below). Step F3.",
    "R22 a")
rep("`pazukiGoodGenus2'_of_literal` in scratch/rv-loc-leaves/PazukiR22.lean); the `R22_Pazuki`\n"
    "placeholder docstring in Leaves.lean states the literal corollary and this consequence.",
    "`pazukiGoodGenus2'_of_literal` in scratch/rv-loc-leaves/PazukiR22.lean); the `R22_Pazuki`\n"
    "placeholder docstring in Leaves.lean states the literal corollary and this consequence.\n"
    "*Lean (leaf-adopt2, 2026-11-12).* **Concrete** (leaf-push2): `ZInQ.LeafPush2.R22_Pazuki`, the\n"
    "audit's upper half. For an abelian surface `A` over a number field `K` with\n"
    "`stableFaltingsHeight A = x` (a real `x`) and `X ≥ max(1, x + log π)`; every `σ : K → ℂ`, every\n"
    "analytic uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ` (`IsUniformization`), every `Ω ∈ 𝔥₂`\n"
    "with `IsPeriodMatrix Λ Ω` (all principal polarizations with a symplectic basis; no polarization\n"
    "object), and every representative `z ∈ L¹⁶` of `[θ[a;b](0, Ω)]` over a number field `L`:\n"
    "`absLogHeight z ≤ X/2 + C₂ log(X + 2)` (sup norms, `≤` Pazuki's Euclidean `h_Θ`). The hardened\n"
    "form `R22_plus3` (`X = max(1, x + 3)`) is proved. Inputs disclosed: H5 (same remark on the two\n"
    "height copies as for R18), algebraicity of analytic principal polarizations (T11-type), and the\n"
    "identification of Pazuki's level-2 coordinates (Def. 2.6) with `θ[a;b](0, Ω)`, UNVERIFIED (the\n"
    "main risk of this leaf; open check: read Def. 2.6).",
    "R22 b")

# §2.2 table
rep("| T10 | `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨` | Milne 1986, Thm 15.1(a) | E | new defs (étale cohomology; large) | none |",
    "| T10 | `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨` | Milne 1986, Thm 15.1(a) | E | placeholder; Galois-equivariant form needs `ℤ_ℓ`-linear functorial ℓ-adic cohomology (Mathlib v4.35 has `Scheme.EllAdicCohomology` as a group only); leaf-push2's non-equivariant `ZInQ.LeafPush2.T10_groupIso` is in `Leaves.lean` but is not the form used | none |",
    "T10 row")
rep("| T11 | Riemann/GAGA/rigidity: `End⁰(A_ℂ)` = Hodge endomorphisms, `Hom_ℚ̄ = Hom_ℂ` | Mumford §§1-3; Serre 1956; Conrad 2006 | E | new defs (analytification; large) | Tau Ceti: Riemann forms |\n"
    "| T12 | Artin comparison with complex conjugation | SGA 4 XI 4.4 | E | new defs (as T11) | none |",
    "| T11 | Riemann/GAGA/rigidity: `End(A_ℂ)` = `ℂ`-linear maps preserving the lattice of a uniformization; `Hom_k = Hom_L` for `k = k̄` of characteristic 0 | Mumford §§1-3; Birkenhake–Lange Prop. 1.2.1; Serre 1956; Conrad 2006 §3; Milne 1986 §20 | E | **yes** (leaf-adopt2, from leaf-push2): `ZInQ.LeafPush2.T11a_RiemannEnd`, `T11b_Rigidity` | Tau Ceti: Riemann forms; bp-analytic proves the `∀ f, ∃ M` half of T11a as glue over its own predicate |\n"
    "| ~~T12~~ | Artin comparison with complex conjugation, used form: the `±1`-eigenspaces of complex conjugation on `V_ℓ(A)`, `A/ℚ`, have dimension `dim A` | SGA 4 XI 4.4; elementary through `ℂ^g/Λ` | — | **glue** (leaf-adopt2): target `ZInQ.LeafPush2.T12_ComplexConjEigen` from T35, T5, T26 and antiholomorphy of conjugation (unproved); removed from `TextbookLeaves` | — |\n"
    "| T35 | Analytic uniformization: `A(ℂ)_σ` for `A/K`, `σ : K → ℂ`, is uniformized by `ℂ^{dim A}` with kernel a full lattice (new, leaf-adopt2, from leaf-push2) | Mumford §1 with GAGA (Serre 1956) (UNVERIFIED numbers) | E | yes, `ZInQ.LeafPush2.UniformizationExists` (coordinate form, no analytification; kept over bp-analytic's `UniformizationLeaf`, leaf-adopt2 §2) | bp-analytic: complex tori, exponential, period lattices, uniqueness glue (Mathlib only) |",
    "T11 T12 rows")

# §2.3
rep("### §2.3 Counts (VERIFIED from the lists and the compiled file; updated by leaf-adopt, 2026-11-12)\n\n",
    "### §2.3 Counts (VERIFIED from the lists and the compiled file; updated by leaf-adopt2, 2026-11-12)\n\n"
    "- **leaf-adopt2 counts.** Research-level: **23** leaves (R1-R22 and H5). Textbook: **33** leaves\n"
    "  (T1-T11, T13-T31, T33-T35; T12 is glue, T32 proved glue). In all **56**. Stated concretely in\n"
    "  `Leaves.lean`: research R2-R16 (R11 + R12 jointly), R18-R22, H5 (**21**), and R1 in part ((a),\n"
    "  (c), (d) and `π₀(X₆) = 1`; (b) is a placeholder); textbook T1-T11, T13-T31, T33-T35 (**32**).\n"
    "  Total **53 of 56 leaves**, plus R1 in part. Placeholders: R17, T10 (**2**) and R1(b). Bundle\n"
    "  fields (VERIFIED by counting the structures): `ResearchLeaves` 26 (24 concrete, 2 `opaque`:\n"
    "  `r1an`, `r17`), `TextbookLeaves` 38 (37 concrete, 1 `opaque`: `t10`): **61 concrete Props, 3\n"
    "  placeholders**. R17 has a concrete statement outside `Leaves.lean` (`LadicCond.CarayolR17'`,\n"
    "  def-ladic-cond, confirmed by leaf-push2 §4); folding it would make 54 of 56.\n"
    "- Premises (docstrings): R1, R2, R5 and R3 rest on Lemma P (rv-qm-polar; type `μ` fixed,\n"
    "  characteristic 0, `𝒪` maximal); R18-R22 and H5 are not yet known to be non-vacuous; R18, R22\n"
    "  also rest on H5 for leaf-push2's copy of the height.\n"
    "- *The bullets below are leaf-adopt's (counts then: 48 of 56, 7 placeholders).*\n\n",
    "counts")

# §3 glue
rep("| G10 | `r_ℓ` odd | G8; T11, T12 | N5 L742-751 | needs T11-T12 | medium |",
    "| G10 | `r_ℓ` odd | G8; T11, T35 (T12 now glue) | N5 L742-751 | T11 stated (leaf-adopt2: `ZInQ.LeafPush2.T11a_RiemannEnd`, `T11b_Rigidity`); T12's used form `ZInQ.LeafPush2.T12_ComplexConjEigen` is a glue target from T35, T5, T26 (unproved); its conjugation predicate is pkg-I4's (`HSyn.isComplexConj_leafPush2_iff`, proved) | medium |",
    "G10")
rep("unproved: that the theta point of the actual `A` satisfies F1 (from R1-R4) | medium |",
    "unproved: that the theta point of the actual `A` satisfies F1 (from R1-R4); leaf-adopt2: R3 and R22 concrete, `ZInQ.LeafPush2.R22_plus3` (the hardened form) and `linYang_j_eq` (F1's `j`-formula on R3's first branch) proved | medium |",
    "G19")

# §4 definitions
rep("| analytification, complex tori, Hodge structures | T11, T12, G10 | Tau Ceti (Riemann forms); GAGA missing | large |",
    "| analytification, complex tori, Hodge structures | T11, T12, T35, R22, G10 | leaf-adopt2: uniformization in coordinate form `ZInQ.LeafPush2.IsUniformization` (no analytification), `IsSiegel`, `IsPeriodMatrix`, `thetaConst`, complex points `CPts` (leaf-push2, in `Leaves.lean`); complex tori as Lie groups built in bp-analytic (not in `Leaves.lean`); Tau Ceti (Riemann forms); GAGA missing | large (statements done) |",
    "defs analytic")
rep("`fieldOfModuli*`, `ToP1` (morphisms to `P¹` by charts), `fieldPt`; no polarization (premise bp-qmmoduli §2.2, SPECULATIVE); schemes over a base, analytification (R1(b)), the QM locus with Igusa invariants (R3) missing |",
    "`fieldOfModuli*`, `ToP1` (morphisms to `P¹` by charts), `fieldPt`; no polarization (premise Lemma P, rv-qm-polar); R3's sextic models and Igusa `J`'s done (leaf-push2: `HasSexticModel`, `IgJ*`, `LinYangTuple`); schemes over a base, analytification (R1(b)) missing |",
    "defs QM")
rep("are glue targets; genus of curves over `ℚ̄` missing (R18) |",
    "are glue targets; R18 stated with `g := dim J` (leaf-push2), so the genus is not needed |",
    "defs X1")
rep("(until proved, the height may be `⊤`), polarizations and theta heights (R22) |",
    "(until proved, the height may be `⊤`); R18, R22 stated over leaf-push2's copy on `PkgI3.AbVar` (R22 through period matrices and theta constants, no polarization object) |",
    "defs height")

# §5
rep("H5, acceptance tests AT1-AT5 (rv-blueprints F3); state R18, R22 |",
    "H5, acceptance tests AT1-AT5 (rv-blueprints F3); R18, R22 stated (leaf-adopt2); prove T35 `UniformizationExists` (bp-analytic's blueprint); identify leaf-push2's and def-faltings' copies of the height |",
    "WP10")
rep("remove or prove the premise bp-qmmoduli §2.2 (polarizations, or Buzzard's polarization-free problem); R1(b) in family form (analytification); R3;",
    "state Lemma P (rv-qm-polar) as a separate hypothesis once polarizations exist, or use Buzzard's polarization-free problem; R1(b) in family form (analytification); R3 stated (leaf-adopt2), its Lefschetz glue `R03_LinYang_algClosed` and the link `j = π₆(x)`;",
    "WP12")
rep("| trust in all 55 stated Props (48 leaves and R1 in part; leaf-adopt) |",
    "| trust in all 61 stated Props (53 leaves and R1 in part; leaf-adopt2) |",
    "WP1")

rep("**Remaining work after leaf-adopt (2026-11-12).**\n",
    "**Remaining work after leaf-adopt2 (2026-11-12).**\n"
    "1. Placeholders: R1(b) (analytification, family form), R17 (fold def-ladic-cond's\n"
    "   `CarayolR17'` and its glue Props `SwanIndependent`, `AdaptedExists`), T10 (Galois-equivariant\n"
    "   ℓ-adic cohomology).\n"
    "2. Premises: Lemma P (rv-qm-polar; human check of Buzzard 1997 p. 592 and Rotger 2003/2004; it\n"
    "   becomes a separate hypothesis once polarizations exist, WP4); AN3's three Props and\n"
    "   `HodgeLatticeTheorem` (non-vacuity of R18-R22, H5); Pazuki's Def. 2.6 coordinates (R22);\n"
    "   Lin–Yang's printed (13)-(14) against `LinYangTuple` (R3).\n"
    "3. Glue targets: `T12_ComplexConjEigen`, `R03_LinYang_algClosed` (leaf-push2); `X1ModelExists`,\n"
    "   `BelyiX1`, `VSurjOfSurjective` (leaf-modcurves); the four glue pieces of leaf-qm-fp §4.\n"
    "4. Unification (WP1): leaf-push2's Part I is a second copy of def-faltings' height over\n"
    "   `PkgI3.AbVar` (R18, R22) beside `ZInQ.DefFaltings` (R19-R21, H5); identify them through\n"
    "   `LeafAdopt.abVarEquiv`. Curves (`IsCurve`, `IsJacobian`, `IsBelyiFunction`), `𝒪`, `QMStr` and\n"
    "   the Igusa–Clebsch invariants also have second copies in `ZInQ.LeafPush2`.\n"
    "5. The glue `HSyn.glueOutputs_of_leaves` (`sorry`) as before.\n\n"
    "**Remaining work after leaf-adopt (2026-11-12; superseded by the list above).**\n",
    "remaining")

# §6
rep("- **R5. Placeholders and the numerical interface.** 7 of the 56 leaves, and part (b) of R1, are\n"
    "  `opaque` placeholders (leaf-adopt, 2026-11-12; 19 of 54 in the first version, 14 after\n"
    "  hsyn-fold);",
    "- **R5. Placeholders and the numerical interface.** 2 of the 56 leaves (R17, T10), and part (b)\n"
    "  of R1, are `opaque` placeholders (leaf-adopt2, 2026-11-12; 19 of 54 in the first version, 14\n"
    "  after hsyn-fold, 7 after leaf-adopt);",
    "risk R5")
rep("- **R7. Premises of the adopted leaves (leaf-adopt, 2026-11-12).** (i) Every Shimura-curve leaf\n"
    "  (R1, R2, R5) is the published statement or a consequence of it only together with bp-qmmoduli\n"
    "  §2.2 (SPECULATIVE; polarizations cannot yet be stated, so it is not a Lean hypothesis).",
    "- **R7. Premises of the adopted leaves (leaf-adopt, 2026-11-12; leaf-adopt2).** (i) Every\n"
    "  Shimura-curve leaf (R1, R2, R5) and R3 is the published statement or a consequence of it only\n"
    "  together with Lemma P of rv-qm-polar (type `μ` fixed, characteristic 0, `𝒪` maximal; VERIFIED\n"
    "  as an argument, published locators UNVERIFIED; polarizations cannot yet be stated, so it is not\n"
    "  a Lean hypothesis).",
    "risk R7")

open(P, "w").write(t)
print("ok")
