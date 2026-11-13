# leaf-qm-fp results log

Compile command: `lake env lean scratch/leaf-qm-fp/QMLeaves.lean` (one Lean process at a time).

## 2026-11-12

- 16:41 QMLeaves.lean §0-§3 (order copied from bp-qmmoduli, QMStr, K-rational Level3, QML3,
  Iso refl/symm/trans, isoSetoid, M3, twist/rightMul on objects and classes): COMPILES, 17 s.
  Change from bp-qmmoduli: `Level3.eta : 𝒪 →+ A(K)` (K-rational points), kernel exactly 3𝒪,
  no ontoness clause (equivalent in char 0 for surfaces, docstring), so base change needs no
  counting leaf.
- 16:47 §4-§6 added: QMPair/QMIso/pairSetoid/forget, com + HasCM4/3/24, `com_twist` (proved),
  `IsBaseChangeOf` / `IsBaseChangeOfPair` (pullback-square relation; no `A_L` object, no
  dimension lemma needed), `stab3`, `fieldOfModuli3`, `stabPair`, `fieldOfModuliPair`,
  `UnramifiedAbove5` (`p ∤ NumberField.discr`), `ToP1` (morphism to P¹ by two charts) and
  `ToP1.val` (via Mathlib `Scheme.SpecToEquivOfField`, `Scheme.evaluation`): COMPILES, 17 s.
- 16:58 §8 leaves compile: `R1fpProps`, `R1heckeProps`, `R2fpProps`, `R1fp`, `R1R2fp`, `R1rec`,
  `R5fp` (case split on b(k)), `R5fpWeak`, `R5fpCount` (2^b h), bundle `QMLeaves`. Proved:
  `R1fp_of_R1R2fp`, `R5fpWeak_of_R5fp`. All `#print axioms`: propext, Classical.choice,
  Quot.sound.
- 17:03 glue proved: `specToEquivOfField_comp`, `ToP1.val_comp` (π(y∘Spec f) = f(π y)),
  `conj_twist_of_rational` (A7 core: for a ℚ̄-point with rational π-value, every Galois
  conjugate's QM pair is an Aut(𝒪)-twist of the original, so σA ≅ A), `QMIso.nonempty_abVarIso`.
  COMPILES, 18 s.
- Finding: NoCM (rv-h-cm §7.2, case D(R) ≠ 1) needs `k ⊆ ℚ(x)`, not only the degree: with the
  degree form alone, disc −19 (h = 1, b = 2, degree 2h = 2) is not excluded by a fibre field
  ℚ(i) of degree 2. R5fp must carry the containment.
- 17:20 R5fp now carries `inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] ℚ(x))` (from ℚ(x) = H_R ⊇ k).
- 17:25 X₆ added to the bundle: `QMPair.twist`, `X6Props` (proper smooth curve, Ψ : X(ℚ̄) ≃
  pairs/≅ Galois-equivariant, W-twists by automorphisms, forgetful fY : Y → X, π = π₆ ∘ fY
  pointwise), `R2X6Props` (Baba–Granath on X₆: fibres = twist classes, CM values), `CMExists`
  (the three CM points exist). `R1R2fp` := ∃ Y Φ π X Ψ fY π₆, R1fpProps ∧ R1heckeProps ∧
  X6Props ∧ R2X6Props ∧ CMExists. Proved: `R2fpProps_of_X6`, `R1R2fp_Y` (the Y₃ form).
  COMPILES, 19 s, axioms standard.
