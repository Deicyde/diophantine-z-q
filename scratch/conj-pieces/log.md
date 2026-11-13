# conj-pieces results log

Task: ArtinTorsionSurj, HomLinearLift, ConjUniformization (scratch/conj-twist/ConjTwist.lean).
Build: `lake build ZInQKernel.HDecomp.LeafPush2.T` (2 min, cached), then `lake env lean <file>`.

- 2026-11-13 06:47 `scratch/conj-pieces/Artin.lean`: **`artinTorsionSurj_of_mulIsogeny :
  G0FibreSimple.MulIsogeny → ArtinTorsionSurj`** (N1-surj from the leaf `MulIsogeny`, field 1 of
  g0-assemble's GluePieces2, status LEAF). Helper lemmas proved: `intCast_end_hom`
  (`((n:ℤ):End A).hom = 𝟙^n`), `comp_mulN` (`Q ≫ [n] = Qⁿ`), `isClosed_one_apply` (unit section
  image closed), `isClosed_singleton_of_mem` (point of a closed discrete set is closed),
  `mem_range_emb` (integral over σ(K) ⇒ in ι(K̄)). Copies verbatim (VERIFIED by diff):
  `ArtinTorsionSurj`, `toC`, `embHom` (conj-twist), `MulIsogeny` (g0-assemble parts/40).
  0 errors, 0 sorry; `#print axioms` = [propext, Classical.choice, Quot.sound]. VERIFIED (compiled).
- 2026-11-13 06:49 `scratch/conj-pieces/Holo.lean`: new textbook leaf `HoloHomLift` (N2′: a
  homomorphism `Ψ : ℂ^g → B(ℂ)_σ` holomorphic in the `IsUniformization` sense factors as
  `Φ_B ∘ M`, `M` ℂ-linear; Mumford §1 + Birkenhake–Lange Prop. 1.2.1, UNVERIFIED numbers).
  Proved `cDom_comp` (rfl), `cEvalAt_comp` (pullback of regular functions), and
  **`homLinearLift_of_holoHomLift : HoloHomLift → HomLinearLift`**. `HomLinearLift` copied
  verbatim (VERIFIED by diff). 0 errors, 0 sorry, axioms standard. VERIFIED (compiled).
- 2026-11-13 06:56 `scratch/conj-pieces/Conj.lean`: copies verbatim from conj-twist (20 blocks,
  VERIFIED by substring check): specS, conjVar, homEquiv_mul_conj, conjHom, conjCs, mapPtIso,
  twistC, twistC_one, conjL(+lemmas), ConjUniformization, conjHomInv, mapPtIsoInv,
  twistC_inj_aux, twistC_injective, ringHom_bijective_of_numberField. Proved: `twistC_mul`,
  `twistC_surj_aux`, `twistC_surjective`, `isUniformization_twist` (group clauses), new glue def
  `ConjHolo` (the two analytic clauses for any holomorphic Ψ), **`conjUniformization_of_conjHolo :
  ConjHolo → ConjUniformization`**; analytic lemmas `top_le_preimage_spec`, `top_le_of_comp_eq`,
  `eval_of_comp_eq_conj` (ΓSpecIso naturality: value at r = conj(value at q)), `homEquiv_left_fst`,
  `cfst`, `cconj`, `twistC_left_fst` (twistC Q ≫ pr₁ = Spec(conj) ≫ Q), `cEvalAt_twistC`,
  `differentiableOn_conj_conj` (z ↦ conj F(z̄) holomorphic, via restrictScalars),
  **`conjHolo_of_bijective`** (ConjHolo's conclusion for bijective s, no hypotheses beyond),
  new def `ConjUniformizationNF` (ConjUniformization with [NumberField K]) and
  **`conjUniformizationNF : ConjUniformizationNF`** (proved outright). 0 errors, 0 sorry,
  axioms standard (2 #print axioms). VERIFIED (compiled).
- 2026-11-13 07:05 `scratch/conj-pieces/ConjPieces.lean` (2164 lines): conj-twist's ConjTwist.lean
  verbatim as prefix (VERIFIED with cmp), then §A/§B/§C from the three files and §D:
  `conjAntiLiftLat_of_homLinearLift : HomLinearLift → ConjAntiLiftLat` (N3a eliminated via
  `conjUniformizationNF`), `conjTwistNontrivial_of_surj_N2 : TateModuleFree →
  UniformizationExists → ArtinTorsionSurj → HomLinearLift → ConjTwistNontrivial`,
  **`conjTwistNontrivial_leaves : TateModuleFree → UniformizationExists → MulIsogeny →
  HoloHomLift → ConjTwistNontrivial`**, **`conjTwistFromLeaves_leaves : MulIsogeny →
  HoloHomLift → ConjTwistFromLeaves`**, `conjTwistFromLeaves_of_pieces : MulIsogeny → HoloHomLift
  → ConjHolo → ConjTwistFromLeaves`. 0 errors, 0 sorry, 35 `#print axioms` all
  [propext, Classical.choice, Quot.sound]; 35 s. VERIFIED (compiled).
- 2026-11-13 07:15 `scratch/conj-pieces/G10.lean` (needs also `lake build
  ZInQKernel.HDecomp.I3Linalg.C2`): g10-odd's G10Odd.lean verbatim up to its `end G0Galois`
  (VERIFIED with cmp), then ConjPieces.lean from conj-twist's §2 on (conj-twist's §1 is a
  verbatim copy of G10Odd declarations), then **`g10GlueConcrete_of_leaves : MulIsogeny →
  HoloHomLift → G10GlueConcrete`** and **`g10Glue_of_leaves : TateModuleFree →
  UniformizationExists → MulIsogeny → HoloHomLift → G10Glue`**. 0 errors, 0 sorry, 45
  `#print axioms` all standard; 38 s. VERIFIED (compiled).
