# lt-local results log

## Step 0 (2026-11-13 09:35-09:50 PST): environment
- Merged origin/wip/lg-kerwild (745af133). origin/wip/g8-tate read, not merged (its `part_tools.lean`
  lemmas `padic_card_le`, `padicAlgCl_card` copied verbatim into part 1, renamed namespace).
- `lake build` of the 25 `ZInQKernel` modules imported by `scratch/lg-kerwild/KerWild.lean`: success (2m25s).
- `Base.lean` = `scratch/lg-kerwild/KerWild.lean` minus `#print axioms` lines (generated, not committed).
  `ctail.sh Base.lean Base`: exit 0, 69 s, olean in `olean/` (dev only).

## Step 1 (09:50-10:00): part_tools.lean (namespace `LTLocal`)
- New: `qbar_card_le` (`#ℚ̄ ≤ ℵ₀`), `exists_equiv_extending_aux` (two alg. closed fields of card `𝔠`
  with embeddings of `ℚ̄` are isomorphic compatibly: transcendence bases over `ℚ̄`,
  `MvPolynomial.renameEquiv`, `IsAlgClosure.equivOfEquiv_algebraMap`), **`exists_equiv_extending`**:
  `ιC : ℚ̄ →ₐ[ℚ] ℂ`, `j : ℚ̄ →ₐ[ℚ] ℚ̄_ℓ` ⟹ `∃ Φ : ℂ ≃+* ℚ̄_ℓ, ∀ x, Φ (ιC x) = j x`.
- Compile (VERIFIED): `ctail.sh T1.lean` (import Base + part_tools): exit 0, 6 s;
  `#print axioms LTLocal.exists_equiv_extending`: `[propext, Classical.choice, Quot.sound]`.

## Step 2 (10:00-10:10): part_g7.lean
- New: `T_prime` (copied from g8-tate), **`g7Clauses_of_transport`**: `G7Data` + `[L:ℚ] ≤ D` +
  `ιC ∘ βQ = β` + `∂(j ∘ βQ) = ε'` ⟹ `G15Ram.G7Clauses (j ∘ βQ) ε' L`;
  **`dim_bc_of_g7Data`**: `G7Data` ⟹ `dim A_{L'} = 2` (IsModelOver + P.surface + g0-dim).
- Compile (VERIFIED): `ctail.sh T2.lean` (import Base + parts 1-2): exit 0, 8 s; both axiom
  reports `[propext, Classical.choice, Quot.sound]`.

## Step 3 (10:10-10:45): part_copy.lean, part_main.lean
- part_copy.lean: verbatim copies from G0Assemble2.lean: `G0ModNewform.Vb` (l.41358-41360),
  `G14Trace` header + `FrobTraceLink` (l.62238-62242, 62356-62373), `HSyn.G0AssembleMod` header +
  `LinkedTateLocal` (l.63903-63947). Containment checked by a python substring test (VERIFIED).
  Name resolution: G0Assemble2 resolves `Qbar`, `GQ` in `LinkedTateLocal` in its own context; here
  the section-level opens of its `section G0A2_a85_linked` (`open GlueDescent GlueC10 PkgI3`) are
  used. All candidates are reducible abbrevs of `AlgebraicClosure ℚ` / `Qbar ≃ₐ[ℚ] Qbar`.
  Without them: "unknown identifier"; with them also over `G14Trace`: "ambiguous" (PkgI4 vs
  GlueC10), so `G14Trace` is copied outside them (as in G0Assemble2, where Link.lean's `end`
  closes that section first).
- part_main.lean (namespace `LTLocal`): defs `ModelEndRank4` (GLUE), `G7DegreeBound` (GLUE,
  expected false as stated), `LinkedTateLocalD` (LinkedTateLocal + premise
  `Module.finrank ℚ L ≤ ZInQ.heightD`); theorems `localGlue_at`,
  **`linkedTateLocalD_of_tateBridge35`** (R6, I2-Tors, `UnramRoots 2 5`, `UnramRoots 2 3`,
  `G14Bridge.TateBridge35`, `ModelEndRank4` ⟹ `LinkedTateLocalD`), `linkedTateLocal_of_D`,
  `linkedTateLocalD_of_local`, `modelEndRank4_of_localD`.
- Compile (VERIFIED): `mk_test.sh; ctail.sh T3.lean` (import Base + parts 1-4): exit 0, 10 s;
  8 `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`, no sorry.

## Step 4 (10:45-11:10): part_rank.lean — `ModelEndRank4` reduced to existing Props
- Verbatim copies (sed line ranges, see part header) from scratch/linked-tate/LinkedTate.lean:
  `ZInQ.DefFaltings.AbVar`/`baseChange`, `LeafAdopt.abVarEquiv`, `HSyn.G0Split.FibreOver`,
  `HSyn.G0Split.FibreSimple` (existing GluePieces piece; FS5 in GluePieces3),
  `HSyn.LinkedTate.QMEndRank` (linked-tate's literature-backed glue).
- New: `endDivision_of_fibreSimple` (linked-tate's proof; `Qbar` → `PkgI4.Qbar` because the bare
  name became an auto-bound implicit here), **`modelEndRank4_of_qmEndRank`**:
  `FibreSimple` + `QMEndRank` ⟹ `ModelEndRank4`; **`linkedTateLocalD_of_tateBridge35'`**:
  R6 + I2-Tors + UnramRoots 2 5 + UnramRoots 2 3 + TateBridge35 + FibreSimple + QMEndRank ⟹
  `LinkedTateLocalD`.
- Compile (VERIFIED): `ctail.sh T3.lean` (import Base + parts 1-5): exit 0, 14 s; 11 axiom
  reports, all `[propext, Classical.choice, Quot.sound]`, no sorry.
