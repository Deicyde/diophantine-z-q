# t5-torsion results log

## Statement (VERIFIED, read in ZInQKernel/HDecomp/Objects.lean:993 and :1486)
- `PkgI2.TorsionStructure.{u}`: ∀ K field (any characteristic), A : Grp (Over (Spec K)) with
  `[IsAbelianVariety A]` (proper, smooth, geometrically integral), g n : ℕ,
  topologicalKrullDim A.X.left = g → 0 < n → (n : K) ≠ 0 →
  ∃ e : torsion A K̄ n ≃ (Fin (2g) → ZMod n), additive.
  `torsion A K̄ n = {x : specOver K K̄ ⟶ A.X | x ^ n = 1}` (K-morphisms Spec K̄ → A).
- `ObjBridge.TorsionStructure` is the same in Type 0 (`torsionStructure_iff : … ↔ PkgI2.TorsionStructure.{0}`, Iff.rfl).
- Demands: all characteristics (p ∤ n), all fields K (no cardinality bound). Consumers
  (Mobius/Glue.lean level3_finite, QM/Structures.lean, A6) apply it with [CharZero K].

## Build
- 12:10 lake build of TauCeti group modules, AbVarBC.Main, LeafPush2.T started.
- 12:04 build done (3 min).

## Compile outcomes
- GroupGlue.lean: `T5Torsion.nonempty_torsionBy_addEquiv_pi` (A abelian group, N ≠ 0, ∀ m ∣ N, #A[m] = m^r ⇒ A[N] ≃+ (Fin r → ZMod N)) and rank-r prime-power lemma. COMPILES, axioms propext/Classical.choice/Quot.sound. (VERIFIED)
- Torus.lean: `T5Torsion.natCard_pow_eq_one` (Φ : E → P additive-to-multiplicative, surjective, kernel a full ℤ-lattice Λ of a fin-dim real normed space E ⇒ #{x : P | xⁿ = 1} = n^(dim_ℝ E)), `finrank_real_fin_complex` (dim_ℝ ℂ^g = 2g). COMPILES, standard axioms. (VERIFIED)
- Descent.lean: `T5Torsion.exists_extPt_eq` (lift of N-torsion along κ : Ω →ₐ[K] Ω₂, Ω alg. closed, [N] finite), `natCard_torsion_eq_of_ext` (char 0: #A(Ω)[n] = #A(Ω₂)[n], via proved `mulIsogeny`). COMPILES, standard axioms. (VERIFIED)
- T5Torsion.lean (single file = GroupGlue + Torus + Descent + assembly): COMPILES, standard axioms (VERIFIED):
  - `torsionStructure_of_torsionCard : TorsionCard.{u} → PkgI2.TorsionStructure.{u}`
  - `torsionStructureC_of_uniformization : ZInQ.LeafPush2.UniformizationExists → TorsionStructureC`
    (T5 for every field K with a ring hom K →+* ℂ, from T35 alone)
  - `torsionCard_of_uniformization` (#A(K̄)[n] = n^{2g} for K →+* ℂ, from T35)
- T5Mobius.lean (T5Torsion + copies of Level3.onto/range_le/torsor, level3_finite, twistClassFinite_of with hT replaced by TorsionStructureC + σ): COMPILES, standard axioms (VERIFIED):
  - `LeafQM.AV.Pin.mobiusGlue_of_T35 : ZInQ.LeafPush2.UniformizationExists → MobiusGlue`
  (GluePiecesPin.mobius from TextbookLeaves.t35 alone; T5's only use in MobiusGlue is at K = ℚ̄, g = 2, n = 3.)
- T5Torsion.lean part 4b (VERIFIED, compiles, standard axioms):
  - `TorsionCardNonC` (TorsionCard on fields with IsEmpty (K →+* ℂ)),
  - `torsionStructure_of_uniformization_of_nonC : UniformizationExists → TorsionCardNonC → PkgI2.TorsionStructure.{0}`,
  - `torsionStructureAt` (T5 at one K with σ : K →+* ℂ, same shape as `hT K A g n hdim hn hnK`).
- T5Full.lean = T5Mobius.lean + part 6 (copies of A6's goodReduction_of_QM_rational3_of_alg / ' and
  QM/Structures' hrat, QML3.goodReduction with T35 + τ : K →+* ℂ for T5): COMPILES, standard axioms (VERIFIED):
  - `GlueA6Alg.goodReduction_of_QM_rational3_C`, `..._C'`, `LeafQM.AV.hratC`, `LeafQM.AV.QML3.goodReductionC`.

## Consumers of T5 (VERIFIED by reading)
- ZInQKernel/Contrib/Mobius/Glue.lean level3_finite ← twistClassFinite_of: K = Qbar (TwistClassFinite is over QML3 Qbar). Now `mobiusGlue_of_T35`.
- ZInQKernel/HDecomp/QM/Structures.lean Level3.onto (n = 3, g = 2): K of the QML3 object.
- ZInQKernel/HDecomp/A6/A6.lean goodReduction_of_QM_rational3* (n = 3^(2k), g = 2): K the field of the DVR; in the assembly
  (G0Assemble2 good_of_QML3, line 59730) K : IntermediateField ℚ Qbar, finite over ℚ (a number field).
- scratch/g0-assemble2 torsionBound3_of (line 56625): K = Qbar.
- scratch/g0-assemble2 torsionCountPts_of_leaf (line 59756): L : IntermediateField ℚ Qbar.
- All uses are at fields with a ring embedding into ℂ (Qbar → ℂ by IsAlgClosed.lift).
- part 7 (in T5Full.lean): `AssemblyCopies.torsionBound3_of_T35`, `AssemblyCopies.torsionCountPts_of_T35` (verbatim copies of the
  assembly Props TorsionBound3, TorsionCountPts with tors/TorsCount/IF/PtQ), and `natCard_torsion_algClosed`. COMPILES (VERIFIED).
- Tate.lean (= part 8 of T5Full.lean): `TateFree.tate_linearEquiv` (#M[ℓⁿ] = ℓ^{nr} ∀n ⇒ T_ℓ M ≃ₗ[ℤ_ℓ] ℤ_ℓ^r for the
  kernel's PkgI3.Tate.T), `TateFree.tateModuleFree_at`, `TateFree.tateModuleFree_of_torsionStructure : PkgI2.TorsionStructure.{0} → PkgI3.TateModuleFree`.
  COMPILES, standard axioms (VERIFIED). So T26 is glue given T5.
- part 9: `tateModuleFreeC_of_uniformization` (T26 for k with k →+* ℂ, from T35 alone), `tateModuleFree_of_torsionCard`,
  `tateModuleFree_of_uniformization_of_nonC`. COMPILES (VERIFIED).
- Pitfalls: Module (ZMod ℓ) given by `letI := AddCommGroup.zmodModule h` makes Module.finBasisOfFinrankEq / natCard_eq_pow_finrank
  instance search "stuck"; state the lemma with `[Module (ZMod ℓ) V]` as a binder and pass the instance with `@`.
  A file-level `open … MonObj` makes `one_mul` resolve to `MonObj.one_mul`; use `_root_.one_mul`.
- part 10 (T5Full.lean): `numberFieldToC`, `subfieldQbarToC`, `torsionStructure_numberField`, `torsionStructure_subfieldQbar`
  (T5 at number fields / subfields of ℚ̄ from T35). COMPILES (VERIFIED).
- Consumers found later (VERIFIED by reading): g0-assemble3 `qmModelG3_of` (G0Assemble3.lean:74743, K : IF, via QML3.goodReduction);
  lt-local `torsGL_of_leaf` (scratch/lt-local/LtLocal4.lean:3055, K a number field).
- part 11 (T5Full.lean): `TateFree.exists_tate_lift_level`, `TateFree.tate_surj_at`, `tate_surj_of_torsionStructure`,
  `tate_surj_numberField` (T_ℓ A → A[ℓ^k] onto, from T5 / from T35 for number fields). COMPILES (VERIFIED).
  Consumer (VERIFIED by reading): G0Assemble3 `tatePairingZl_of_leaves` (:49582), the only main-chain use of the
  GluePieces4 leaf `divisiblePoints` (#40), at K a number field (TatePairingZl, :49484).

## Files
- T5Full.lean: the complete artifact (parts 1-11). Built as T5Mobius.lean (= T5Torsion.lean + import Mobius + mobius.part)
  + a6.part + count.part + tate.part (= Tate.lean body + part 9) + nf.part + surj.part + surj2.part, imports merged.
- Standalone compiling pieces: GroupGlue.lean, Torus.lean, Descent.lean, T5Torsion.lean (parts 1-4b), Tate.lean (part 8), T5Mobius.lean.
