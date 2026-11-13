# leaf-qm-fp results log

Compile command: `lake env lean scratch/leaf-qm-fp/QMLeaves.lean` (one Lean process at a time). Since the A6 section the file imports `ZInQKernel.HDecomp.A6.A6` (prebuilt olean present in this worktree; otherwise `lake build ZInQKernel.HDecomp.A6.A6` first).

## 2026-11-12

- 16:41 QMLeaves.lean §0-§3 (order copied from bp-qmmoduli, QMStr, K-rational Level3, QML3,
  Iso refl/symm/trans, isoSetoid, M3, twist/rightMul on objects and classes): COMPILES, 17 s.
  Change from bp-qmmoduli: `Level3.eta : 𝒪 →+ A(K)` (K-rational points), kernel exactly 3𝒪,
  no ontoness clause (equivalent in char 0 for surfaces, docstring), so base change needs no
  counting leaf.
- (16:4x) §4-§6 added: QMPair/QMIso/pairSetoid/forget, com + HasCM4/3/24, `com_twist` (proved),
  `IsBaseChangeOf` / `IsBaseChangeOfPair` (pullback-square relation; no `A_L` object, no
  dimension lemma needed), `stab3`, `fieldOfModuli3`, `stabPair`, `fieldOfModuliPair`,
  `UnramifiedAbove5` (`p ∤ NumberField.discr`), `ToP1` (morphism to P¹ by two charts) and
  `ToP1.val` (via Mathlib `Scheme.SpecToEquivOfField`, `Scheme.evaluation`): COMPILES, 17 s.
- (16:4x) §8 leaves compile: `R1fpProps`, `R1heckeProps`, `R2fpProps`, `R1fp`, `R1R2fp`, `R1rec`,
  `R5fp` (case split on b(k)), `R5fpWeak`, `R5fpCount` (2^b h), bundle `QMLeaves`. Proved:
  `R1fp_of_R1R2fp`, `R5fpWeak_of_R5fp`. All `#print axioms`: propext, Classical.choice,
  Quot.sound.
- (16:4x) glue proved: `specToEquivOfField_comp`, `ToP1.val_comp` (π(y∘Spec f) = f(π y)),
  `conj_twist_of_rational` (A7 core: for a ℚ̄-point with rational π-value, every Galois
  conjugate's QM pair is an Aut(𝒪)-twist of the original, so σA ≅ A), `QMIso.nonempty_abVarIso`.
  COMPILES, 18 s.
- Finding: NoCM (rv-h-cm §7.2, case D(R) ≠ 1) needs `k ⊆ ℚ(x)`, not only the degree: with the
  degree form alone, disc −19 (h = 1, b = 2, degree 2h = 2) is not excluded by a fibre field
  ℚ(i) of degree 2. R5fp must carry the containment.
- (16:5x) R5fp now carries `inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] ℚ(x))` (from ℚ(x) = H_R ⊇ k).
- (16:5x) X₆ added to the bundle: `QMPair.twist`, `X6Props` (proper smooth curve, Ψ : X(ℚ̄) ≃
  pairs/≅ Galois-equivariant, W-twists by automorphisms, forgetful fY : Y → X, π = π₆ ∘ fY
  pointwise), `R2X6Props` (Baba–Granath on X₆: fibres = twist classes, CM values), `CMExists`
  (the three CM points exist). `R1R2fp` := ∃ Y Φ π X Ψ fY π₆, R1fpProps ∧ R1heckeProps ∧
  X6Props ∧ R2X6Props ∧ CMExists. Proved: `R2fpProps_of_X6`, `R1R2fp_Y` (the Y₃ form).
  COMPILES, 19 s, axioms standard.
- 16:55 proved `conj_iso_of_rational` (A7 in the manuscript's form: for a K-point with rational
  π-value and embeddings e₁ e₂ : K → ℚ̄, the base changes exist and their QM pairs are twists, so
  the abelian surfaces are isomorphic over ℚ̄), from R1fpProps + R2fpProps only. COMPILES.
- 16:56 proved `conjHom` (ring hom End A → End A' from a QM-pair iso), `conjHom_iota`,
  `conjHom_mem_com`, `HasCM4/3/24.of_iso`, `hasCM4/3/24_twist`, and `cm_of_val` (h-b1 M9 on X₆:
  points over 0, ∞, −16/27 are CM by ℤ[i], ℤ[ζ₃], ℤ[√−6], from R2X6Props + CMExists).
  COMPILES, 19 s, standard axioms.
- 17:0x proved `ToP1.comp` (pull back the charts of a morphism to P¹ along a morphism of
  schemes; uses `Scheme.Hom.naturality`, `Scheme.preimage_basicOpen`),
  `specToEquivOfField_comp_right`, `ToP1.val_comp_right` ((π∘h)(y) = π(h∘y)). The leaf no longer
  asserts a separate π on Y₃: `X6Props` lost its π-clause, `R1R2fp` quantifies only π₆ on X₆,
  and `R1R2fp_Y` produces π := π₆.comp fY.left with `R2fpProps` (compiled). COMPILES.
- 17:1x adversarial model review (subagent, read-only): no DEFECT; RISKs: (1) every leaf rests on
  bp-qmmoduli §2.2 (polarization exists and is unique, SPECULATIVE) because QML3/QMPair omit λ;
  (2) no vacuity guard. NOTEs: audit verdict missing in R1fp docstring; R1hecke ignores λ;
  CM clauses of R2 need Baba–Granath's §3.1 table (single W-orbit), not Thm 2.1/Lemma 3.1 alone;
  R5 printed condition is D(R)N*(R) ≠ 1 with N* = 1; Nat.card/finrank are 0 on infinite inputs.
  Applied: `Nonempty (fieldPt Qbar ⟶ Y)` in R1fpProps and `Nonempty (fieldPt Qbar ⟶ X)` in
  X6Props; docstrings of R1fp, R1R2fp (R1hecke, R2), R5fp, R5fpCount, QMLeaves repaired.
  COMPILES, 19 s, all axioms standard.
- 17:1x A3 glue proved: `Level3.ext'`, `Level3.rightMul_rightMul`, `QML3.rightMul_rightMul`,
  `M3.rightMul_rightMul` (the 𝒪^× action on classes is an action), and
  `Level3.exists_mul_of_range_le` (two level structures on one (A, ι) with range η' ⊆ range η
  differ by right multiplication by some u₀ ∈ 𝒪 invertible mod 3𝒪; over K̄ the range condition
  is the 81 = 81 count from TorsionStructure, not proved here). COMPILES.
- 17:2x proved, from the kernel leaf `ObjBridge.TorsionStructure`: `Level3.onto` (in char 0 every
  3-torsion K̄-point of A is the image of a level point: 𝒪/3𝒪 ↪ A(K)[3] ↪ A(K̄)[3], 81 = 81, by
  `ofInt_injective`, `bcPt_injective` (Spec K̄ → Spec K is an epimorphism,
  `Flat.epi_of_flat_of_surjective`) and `Fintype.bijective_iff_injective_and_card`),
  `Level3.range_le`, and `Level3.torsor` (two level structures on one (A, ι) differ by right
  multiplication by an element of 𝒪 invertible mod 3: the count of A3). Consequence: all of A[3]
  is K-rational (A6's hypothesis `hrat`). COMPILES, 20 s, standard axioms.
- 17:3x A6 on the leaves' objects: import switched to `ZInQKernel.HDecomp.A6.A6`; copied
  bp-qmmoduli's `oi`, `oj`, `hI`, `hJ`, `hIJ`; new `galAct_bcPt` (K-points are Galois-fixed) and
  `hrat` (all of A[3] Galois-fixed, from `Level3.onto`); `QML3.goodReduction` [CharZero K] from
  `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` via
  `GlueA6Alg.goodReduction_of_QM_rational3'`. COMPILES, 24 s, standard axioms.
- 17:1x proved `unramified_over_branch` (Lemma NV step 2, h-b1 §3): from R1R2fp ∧ R1rec, a
  ℚ̄-point of Y₃ over 0, ∞ or −16/27 has a field of moduli that is a number field unramified at
  every p ≥ 5 (via `cm_of_val`, the forgetful map and `ToP1.val_comp_right`). COMPILES.
- 17:2x added `residueImage` (κ(x) ⊆ ℚ̄ for a ℚ̄-point, via `SpecToEquivOfField`) and the point
  form of reciprocity `R1recProps` (residue fields of CM points of Y₃ unramified at p ≥ 5) as a
  sixth conjunct of `R1R2fp`; proved `residue_unramified_over_branch` (Lemma NV step 2 in h-b1's
  form, residue fields of points over the branch values) from `R1R2fp` alone. Finding: the object
  form `R1rec` (fields of moduli) cannot be transferred to residue fields in Lean without the
  uniqueness of base change up to isomorphism, which needs rigidity (a morphism of abelian
  varieties preserving 0 is a homomorphism); hence the point form. COMPILES, 24 s.
- 17:2x finding: the bundle did not assert that π₆ is onto P¹(ℚ̄) nor that Y₃ → X₆ is onto
  X₆(ℚ̄); without them no fibre over J(u) can be chosen (A4). Added `X6Surj` as a seventh
  conjunct of `R1R2fp` (consequences of Baba–Granath's X₆/W ≅ P¹ and of R1's finite surjective
  forgetful map). Proved `exists_fibre_object` (A4: over every t ∈ P¹(ℚ̄) there is a point of Y₃
  with an object and π-value t). COMPILES, 24 s.
