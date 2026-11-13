# conj-pieces results log

Task: ArtinTorsionSurj, HomLinearLift, ConjUniformization (scratch/conj-twist/ConjTwist.lean).
Build: `lake build ZInQKernel.HDecomp.LeafPush2.T` (2 min, cached), then `lake env lean <file>`.

- 2026-11-13 07:20 `scratch/conj-pieces/Artin.lean`: **`artinTorsionSurj_of_mulIsogeny :
  G0FibreSimple.MulIsogeny → ArtinTorsionSurj`** (N1-surj from the leaf `MulIsogeny`, field 1 of
  g0-assemble's GluePieces2, status LEAF). Helper lemmas proved: `intCast_end_hom`
  (`((n:ℤ):End A).hom = 𝟙^n`), `comp_mulN` (`Q ≫ [n] = Qⁿ`), `isClosed_one_apply` (unit section
  image closed), `isClosed_singleton_of_mem` (point of a closed discrete set is closed),
  `mem_range_emb` (integral over σ(K) ⇒ in ι(K̄)). Copies verbatim (VERIFIED by diff):
  `ArtinTorsionSurj`, `toC`, `embHom` (conj-twist), `MulIsogeny` (g0-assemble parts/40).
  0 errors, 0 sorry; `#print axioms` = [propext, Classical.choice, Quot.sound]. VERIFIED (compiled).
- 2026-11-13 07:35 `scratch/conj-pieces/Holo.lean`: new textbook leaf `HoloHomLift` (N2′: a
  homomorphism `Ψ : ℂ^g → B(ℂ)_σ` holomorphic in the `IsUniformization` sense factors as
  `Φ_B ∘ M`, `M` ℂ-linear; Mumford §1 + Birkenhake–Lange Prop. 1.2.1, UNVERIFIED numbers).
  Proved `cDom_comp` (rfl), `cEvalAt_comp` (pullback of regular functions), and
  **`homLinearLift_of_holoHomLift : HoloHomLift → HomLinearLift`**. `HomLinearLift` copied
  verbatim (VERIFIED by diff). 0 errors, 0 sorry, axioms standard. VERIFIED (compiled).
