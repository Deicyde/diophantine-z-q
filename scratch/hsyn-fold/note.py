p='docs/research/h-decomposition.md'; L=open(p).read()
def r(a,b):
    global L
    assert L.count(a)==1,(a[:70],L.count(a)); L=L.replace(a,b)
r("""(G1-G20, composed in G0): the manuscript's new arguments, the repository's replacement arguments, and
bookkeeping. The glue is **not** formalized. It has been reviewed only by AI models; in Lean,
its last steps (from the level bound, the theta point and the height inequalities to H) and
Glazer's Brauer and cochain steps are proved, as are A6, C2 and E1 (each modulo one named
algebra statement) and D3, D4, together with elementary pieces of most other steps.""",
"""(G1-G20, composed in G0): the manuscript's new arguments, the repository's replacement arguments, and
bookkeeping. The glue is **not** formalized. It has been reviewed only by AI models; in Lean,
its last steps (from the level bound, the theta point and the height inequalities to H) and
Glazer's Brauer and cochain steps are proved, as are A6 (from its three leaves R6, R7(a), T5
alone), C2 and E1 (modulo the named algebra statement `SemisimpleBaseChange`), the Galois side of
C10 (from Chebotarev and Brauer–Nesbitt), D1's degree bound in local form (modulo two standard
transports not in Lean), and D3, D4, together with elementary pieces of most other steps.""")
r("""**What is in Lean today** (VERIFIED: `scratch/h-decomposition/Leaves.lean` compiles, no
`axiom`). 10 research-level leaves (items 4, 6, 7, 9, 10, 13, 14, 15, and 11 + 12 through their
joint consequence) and 25 textbook leaves, 35 of 54 (33 stated individually, R11 and R12 only through their joint
consequence), are stated concretely over Mathlib,""",
"""**What is in Lean today** (VERIFIED: `scratch/h-decomposition/Leaves.lean` compiles, no
`axiom`; counts updated by hsyn-fold, 2026-11-12). 11 research-level leaves (items 4, 6, 7, 8, 9,
10, 13, 14, 15, and 11 + 12 through their joint consequence) and 29 textbook leaves, 40 of 54 (38
stated individually, R11 and R12 only through their joint consequence; 46 Props), are stated
concretely over Mathlib,""")
r("""genus-2 theta constants as lattice sums, continuous Galois cohomology. The other 12
research-level and 7 textbook leaves are `opaque` placeholders with no content. Each needs new
definitions (cheap for T29 and T32, up to very large for R1-R3, R5, R16, R18-R22) before it can
be stated.""",
"""genus-2 theta constants as lattice sums, continuous Galois cohomology. The other 11
research-level and 3 textbook leaves (R1-R3, R5, R16-R22; T10-T12) are `opaque` placeholders with
no content. Each needs new definitions (medium for R17, large for T10-T12, very large for R1-R3,
R5, R16, R18-R22) before it can be stated; R17 now has a statement over a new definition of the
conductor in `scratch/def-ladic-cond/` (not yet folded into `Leaves.lean`).""")
r("""level bound, the theta point and the transfer inequalities to H (F2 on Mathlib's Weil heights,
E2-E4 and F3 arithmetic, the final constant, the return from `J(u)` to `u`); step A6 (Lemma PR(ii), good reduction away from 3) by Raynaud's route, from the leaves
R6, R7(a) and T5 and the algebra statement `QuatUnipotentTrivial` (rv-a6-route; paper proof
complete, not yet in Lean); the I3 glue""",
"""level bound, the theta point and the transfer inequalities to H (F2 on Mathlib's Weil heights,
E2-E4 and F3 arithmetic, the final constant, the return from `J(u)` to `u`); step A6 (Lemma PR(ii), good reduction away from 3) by Raynaud's route, from the leaves
R6, R7(a) and T5 alone (`PkgI2.goodReduction_of_QM_rational3`; the algebra statement
`QuatUnipotentTrivial` is now a theorem, glue-a6-alg); the Galois side of C10 (`GlueC10.c10`:
`r₃ ≅ ρ_{f,3}` from the 5-adic identification and trace data, from T18 and T19 in the forms
`ChebotarevExists`, `BrauerNesbittChar0`, with the lift of Frobenius to `G_ℚ` proved) and the
ℓ-independence of traces from T7 (`PkgI3.trace_indep_of_ell`), glue-c10; D1's `e ≤ a!` through the
decomposition group (`GlueD1Local.D1_krasner'`, glue-d1-local); the I3 glue""")
r("""stated in Lean, with conclusion the repository's `ZInQ.SixContactMin`. Its proof has one `sorry`:
the glue from the leaves to the numerical interface of the Arakelov end
(`HSyn.glueOutputs_of_leaves`). It is the only `sorry` in the file: the three report statements
that had one (A6 `PkgI2.goodReduction_of_QM_rational3`, D4 `PkgI6.artinConductor_le_of_upper`,
D3 `PkgI6.sq_principalUnits`) are now proved. What those proofs still assume is an explicit
hypothesis, never a hidden `sorry`: `QuatUnipotentTrivial` (A6) and `SemisimpleBaseChange` (C2, E1)
are named glue Props, and A6, C2, E1 also take their leaves as hypotheses.""",
"""stated in Lean, with conclusion the repository's `ZInQ.SixContactMin`. Its proof has one `sorry`:
the glue from the leaves to the numerical interface of the Arakelov end
(`HSyn.glueOutputs_of_leaves`). It is the only `sorry` in the file: the three report statements
that had one (A6 `PkgI2.goodReduction_of_QM_rational3`, D4 `PkgI6.artinConductor_le_of_upper`,
D3 `PkgI6.sq_principalUnits`) are now proved. What those proofs still assume is an explicit
hypothesis, never a hidden `sorry`: `SemisimpleBaseChange` (C2, E1) is the one named glue Prop left
in the file; A6, C2, E1, C10 and D1 take their leaves as hypotheses; C10 also takes the trace
identities and semisimplicity that other steps (Néron mapping property, Serre–Tate specialization,
Eichler–Shimura, C2) must supply, none statable over Mathlib today.""")
r("""caveats above on Tian–Yuan–Zhang. Hypothesis H is reduced on paper to the 22 research-level
theorems and 32 textbook results listed, plus 20 glue steps; in Lean, 35 of these 54 leaves can
already be stated, and the last part of the glue is proved.\"""",
"""caveats above on Tian–Yuan–Zhang. Hypothesis H is reduced on paper to the 22 research-level
theorems and 32 textbook results listed, plus 20 glue steps; in Lean, 40 of these 54 leaves can
already be stated, and the last part of the glue is proved.\"""")
r("""has to be formalized, and it has only model reviews.

---
""", """has to be formalized, and it has only model reviews.

**Changes since the first version (hsyn-fold, 2026-11-12).** Folded in the provers that finished
after hsyn-fix:
- **glue-a6-alg**: `QuatUnipotentTrivial` is proved (`PkgI2.quatUnipotentTrivial`), so A6 follows
  from R6, R7(a), T5 alone; the valuation ring `w` of `K̄` over `O` is proved to exist, so
  `PkgI2.goodReduction_of_QM_rational3'` drops it. R8 is now needed by no proved step (only by
  h-b1's second route for A6); the counts still list it (22), so 21 research-level theorems suffice.
- **glue-c10**: C10's Galois side proved from Chebotarev and Brauer–Nesbitt, with the Frobenius
  lift to `G_ℚ`; ℓ-independence of traces from Mumford §19 Thm 4 (`GlueC10.*`,
  `PkgI3.trace_indep_of_ell`, now in `Leaves.lean`).
- **glue-d1-local**: D1's `e ≤ a!` through the decomposition group (`GlueD1Local.*`, now in
  `Leaves.lean`); the passage from Glazer's local field to the global statement (Krasner, and
  `D_P ≅ Gal(L_P/ℚ_p)` with filtrations) is STANDARD but not in Lean.
- **leaf-push**: R8, T9, T23, T29, T32 stated concretely (now in `Leaves.lean`; the five `opaque`
  placeholders are removed): 35 → **40 of 54** leaves, 19 → **14** placeholders, 39 → 46 Props.
- **obj-bridge**: the shared object layer for I2 and I3 is built and compiled in
  `scratch/obj-bridge/Objects.lean` (bijection on objects and morphisms, every I2/I3 leaf restated
  with a proved equivalence), and I2-Rank (`PkgI2.HomRankBound`) follows from T6
  (`PkgI3.HomFreeFinite`). **Not** adopted in `Leaves.lean` (time); the duplicated I2/I3
  definitions remain there (WP1).
- **bdr-kertheta**: `ker θ` is principal for `𝓞_ℂ_p` and Mathlib's `BDeRham` is a complete
  discretely valued field with valuation ring `BDeRhamPlus`, so pkg-I4's `IsDeRham` (R10-R13, T23)
  is over the classical `B_dR`. Not copied into `Leaves.lean` (no leaf statement changes).
- Five further reports merged, not folded into `Leaves.lean` (each compiles in its own
  `scratch/<task>/`, axioms `propext`, `Classical.choice`, `Quot.sound` per its report):
  **def-ladic-cond** (conductor exponent of an ℓ-adic representation of `G_{ℚ_p}`; R17 stated as
  `CarayolR17` over it; glue Props `SwanIndependent`, `AdaptedExists` open); **glue-rho-cont**
  (pkg-I3's `ρ_ℓ` is continuous, from T26; closes rv-leaves-b's continuity gap for C10);
  **glue-b3-unram** (B3(v), `L'` unramified outside `T`, proved from `LeafB3a`, `LeafB3b` (T32's two
  parts) and a new leaf `LeafConj`, places over `p` are conjugate; it also corrects
  glue-descent's `twist_kills_inertia`, whose hypothesis was undischargeable); **glue-sqrt-local**
  (both Galois halves of B2's local square-root criterion; the disjointness
  `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)ˣ × ⟨p⟩` still open); **glue-vigneras** (every normalizer fact of
  A3(a) for N5's order proved, `[N_B(𝒪) : ℚ^×𝒪^×] = 4`, so T29 is no longer needed as a leaf once
  integrated; the adelic bookkeeping of A3 is open).
- **Still not formalized**: the glue G1-G17, G19 as a whole (`HSyn.glueOutputs_of_leaves` is
  `sorry`); every step that needs the actual abelian surface `A` or `J₁(N)` (Mathlib cannot build
  a nonzero abelian variety); the 14 placeholder leaves; and every leaf itself (all are hypotheses).

---
""")
open(p,'w').write(L); print('ok')
