# bp-qmmoduli results log

Task: blueprint for the Shimura-curve objects of leaves R1-R3, R5 (docs/research/bp-qmmoduli.md).

## 2026-11-12

- `lake build ZInQKernel.HDecomp.Objects`: OK, 57 s (VERIFIED). Scratch files may import it.
- Mathlib v4.35 inventory (VERIFIED, ls/grep of .lake/packages/mathlib): no ample line bundles,
  no Picard scheme or dual abelian variety, no quaternion orders; present: sheaves of modules on
  schemes (`AlgebraicGeometry/Modules/Sheaf.lean`), `RingTheory/PicardGroup.lean` (Pic of a ring),
  `ProjectiveSpectrum`, group schemes (`AlgebraicGeometry/Group/{Abelian,Affine,Smooth}.lean`),
  `QuaternionAlgebra`, `ModularForms/ArithmeticSubgroups.lean`.
- `order_table.py` (sympy, VERIFIED): structure constants of 𝒪 = ℤ⟨1,i,(1+j)/2,(i+k)/2⟩ in
  B = (2,−3) are integral; x ↦ x† = μ⁻¹x̄μ preserves 𝒪; trd(x x†) = 2x0²+4x1²+18x2²−48x2x3+36x3²
  is positive definite; x†x has equal j- and k-coordinates (so x†x ∈ ker(z ↦ trd(μ⁻¹z̄)) =
  {z2 = z3}); w₂ = 1+i+j (nrd 2), w₃ = j (nrd 3), μ (nrd 6) normalize 𝒪; w₂w₃μ⁻¹ ∈ 𝒪, nrd 1;
  w₂² = 2(i+j), i+j ∈ 𝒪¹.
- `QMOrder.lean` (Mathlib only): compiles, no errors, no `sorry` (VERIFIED, `lake env lean`,
  ~15 s). Axioms of `eq_smul_E0`, `eq_pm_E0_of_principal`, `trd_mul_dag_pos`,
  `atkinLehner_relations`, `w2_normalizes`: propext, Classical.choice, Quot.sound. Contents:
  `O : Subring B`; `dag` (anti-involution, `dag_dag`, `dag_mul`, `dag_mem`, `dag_eq'`);
  `trd_mul_dag_pos` (positivity); `E0_alt`, `E0_rosati`, `E0_gram`, `gram_det`, `E0_int`;
  **`eq_smul_E0`**: every alternating ℚ-bilinear `E` on `B` with `E(ax,y) = E(x,a†y)` is `r·E₀`;
  **`eq_pm_E0_of_principal`**: Gram determinant 1 on N5's basis ⇒ `E = ±E₀`;
  `w2_normalizes`, `w3_normalizes`, `mu_normalizes`, `atkinLehner_relations`.
- `QMAbVar.lean` (imports `ZInQKernel.HDecomp.Objects`): compiles, no errors, no `sorry`
  (VERIFIED). Axioms of `not_qmStr_zero`, `Level3.rightMul_eq_self`, `Level3.twist`,
  `QML3.Iso.refl`: propext, Classical.choice, Quot.sound. Contents: `endPt` (ring hom
  `End_K(A) → End(A(L))`), `QMStr` (injective `𝒪 →+* End_K A`), `qmAct`, `qmModule`, `Level3`
  (𝒪-linear, kernel 3𝒪, onto `A(K̄)[3]`, Galois-fixed), `Level3.tors`, `Level3.eq_iff`,
  `Level3.rightMul` (𝒪^× action), `rightMul_eq_self` (units ≡ 1 mod 3𝒪 act trivially),
  `QMStr.twist`/`Level3.twist` (Aut(𝒪) action, `A` unchanged), `QML3`, `QML3.Iso`, `M3 K`
  (isomorphism classes). Pitfall: `ι` and `η` are tokens under the kernel's `open`s (field names
  `iota`, `eta`); `mul_assoc` is ambiguous with `MonObj.mul_assoc` (use `_root_.`); `ring` fails
  on the noncommutative `O` (use `noncomm_ring`).
- `Units72.lean`: `|(𝒪/3𝒪)^×| = 72` (two-sided units of `(Fin 4 → ZMod 3)` with the structure
  constants mod 3) by `decide +kernel`, ~18 s, axioms propext, Classical.choice, Quot.sound
  (VERIFIED). Agrees with h-trust A3 / h-b1 M3 (`form_check.py`, `b1_checks.py` §B).
- Mathlib has `CommRing.Pic` (Picard group of a commutative ring, `RingTheory/PicardGroup.lean`):
  usable for `h(R) = #Pic(R)` of an imaginary quadratic order in R5's statement (VERIFIED, grep).
- Mathlib has `Functor.map.instIsMonHom` (monoidal functors map monoid homs to monoid homs,
  `CategoryTheory/Monoidal/Mon.lean:845`): base change of `End` along `Over.pullback` is
  definable (VERIFIED, grep; not built here).
- `QMAbVar.lean` now imports `ZInQKernel.HDecomp.A6.A6` (built: `lake build
  ZInQKernel.HDecomp.A6.A6`, 68 s). New §5: **`QML3.goodReduction`**: for every `P : QML3 K` and
  every DVR `Ov` of `K` with `3` a unit, `HasGoodReduction (toGrp P.A) Ov`, from
  `NeronOggShafarevich.{0}`, `RaynaudCriterion.{0}`, `TorsionStructure.{0}` through the kernel's
  `GlueA6Alg.goodReduction_of_QM_rational3'` (`I = ι(i)`, `J = ι(j)`, `i² = 2`, `j² = −3`,
  `ji + ij = 0` proved in `𝒪`; `hrat` from `Level3.onto` + `Level3.rational`). Compiles, axioms
  propext, Classical.choice, Quot.sound (VERIFIED).
- docs/research/bp-qmmoduli.md written (first version).
- `QMAbVar.lean` §6 (VERIFIED, compiles, standard axioms): `QML3.Iso.symm`, `QML3.Iso.trans`,
  `isoSetoid` (isomorphism is an equivalence relation), `M3'` (the `Quotient`); `com q`
  (centralizer of `ι(𝒪)` in `End_K A`), `HasCM4`, `HasCM3`, `HasCM24`, `intCast_mem_com`;
  **`endBC`**: base change `End_K(A) →+* End_L(A_L)` along `Over.pullback (Spec L → Spec K)`
  (first half of node N8; needs `open scoped CategoryTheory.Obj` and the explicit instance
  `Functor.map.instIsMonHom`). Not done: injectivity of `endBC` (faithfulness of the pullback),
  base change of `Level3`.
- `QMAbVar.lean` §6 continued (VERIFIED, standard axioms): `specMap_flat`, `specMap_surjective`
  (instances for `Spec L → Spec K`), **`endBC_injective`** (from Mathlib's
  `(Over.pullback f).Faithful` for `f` flat, surjective, quasi-compact,
  `Morphisms/FlatDescent.lean:193`), **`QMStr.baseChange`** (QM structures base-change along any
  field extension). Finding: base change of `Level3` needs that `A(K̄)[3] → A_L(L̄)[3]` is onto,
  which is not definitional: it follows from `TorsionStructure` (both sides have `3^4` elements,
  and the map is injective because `Spec L̄ → Spec K̄` is an epimorphism) — glue with a leaf.
- `QMAbVar.lean` §7 (VERIFIED, compiles, standard axioms): `QMIso` (isomorphism of QM pairs),
  `conjAV`, `conjQM` (conjugation by `σ ∈ Aut(ℚ̄/ℚ)` through `QMStr.baseChange` with the algebra
  `σ.toAlgebra`), **`fieldOfModuli`** (fixed field of the closure of `{σ : (σA, σι) ≅ (A, ι)}`),
  `conductor` (`relIndex` of `R` in `𝒪_k`), and the leaf statement **`R5fp`** (González–Rotger
  2006 Thms 5.8/5.12 in degree form: `[ℚ(x):ℚ] ∈ {#Pic R, 2·#Pic R}` for `com ι ≅ R`, `R` an
  order of conductor prime to 6 in an imaginary quadratic `k`). Statement only (a `def … : Prop`),
  not proved, not used.
- `QMAbVar.lean` (VERIFIED, compiles, standard axioms): `QMIso.symm/trans/refl`, `QMPair`,
  `pairSetoid`, `inertCount6` (`#{p ∈ {2,3} : p𝒪_k prime}`), leaf statement **`R5fpCount`**
  (González–Rotger Prop. 5.6 / Jordan: number of classes of QM pairs over `ℚ̄` with centralizer
  `≅ R` is `2^b·#Pic R`); `QML3.Iso.twist`, `QML3.Iso.rightMul`, `M3'.twist`, `M3'.rightMul`
  (the `Γ'` operations descend to isomorphism classes).
- Attempted and dropped: `innerIso` (inner twists by `Ad(u)`, `u ∈ 𝒪^×`, are isomorphic to the
  original via `ι(u)`): `exact` timed out at `whnf` (200000 heartbeats) on the equivariance field,
  even after isolating the algebra in `iota_conj`; cause not found. Not in the file.
