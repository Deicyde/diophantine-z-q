import ZInQKernel.Syntax.Templates.Core

/-!
# The multiplication certificate templates

Templates `6` (`test_group`, 44 parameters, 162 witnesses), `7` (`slope`, 22 parameters,
1298 witnesses) and `8` (`height_certificate`, 36 parameters, 35106 witnesses): `addTestGroup`,
`addSlope` and `addHeightCertificate` of `construction/multiplication-certificate.js`, with the
same parameter order and the same allocation order of witnesses and blocks. None has rational
constants. For each template we prove the counts, the block list (the witness blocks of the
saved specification), well-formedness and the relation through the private blocks.
-/

namespace ZInQ.Syntax

open MvPolynomial

/-! ### `test_group` -/

/-- One local test of `test_group` at the point `P`: the pairs `ζ`, `λ`, `ρ`, then the calls
`raw_z[P, ζ]`, `log25[ζ, λ]` and `raw_inverse_x[P, ρ]`. -/
noncomputable def testGroupLocal (P : Code) : Build (Pair × Pair × Pair × List Formula) := do
  let z ← Build.freshPair
  let L ← Build.freshPair
  let r ← Build.freshPair
  let c1 ← Build.call rawZTemplate (Fin.append P z.args)
  let c2 ← Build.call log25Template (Fin.append z.args L.args)
  let c3 ← Build.call rawInverseXTemplate (Fin.append P r.args)
  pure (z, L, r, [c1, c2, c3])

/-- The calls `member[F]` and `raw_add[F, neg(C), V]` of `test_group`. -/
noncomputable def testGroupRoot (F C V : Code) : Build (List Formula) := do
  let m ← Build.call memberTemplate F
  let a ← Build.call rawAddTemplate (Fin.append (Fin.append F C.neg) V)
  pure [m, a]

/-- The construction of `test_group` on the points `C₀, …, C₃` and the output pairs
`D₀, …, D₁₁`. -/
noncomputable def testGroupBuild (C : Fin 4 → Code) (D : Fin 12 → Pair) : Build Formula := do
  let F ← Build.freshPoints 4
  let V ← Build.freshPoints 4
  let a0 ← testGroupRoot (F 0) (C 0) (V 0)
  let a1 ← testGroupRoot (F 1) (C 1) (V 1)
  let a2 ← testGroupRoot (F 2) (C 2) (V 2)
  let a3 ← testGroupRoot (F 3) (C 3) (V 3)
  let ⟨_, L0, r0, c0⟩ ← testGroupLocal (F 0)
  let ⟨_, L1, r1, c1⟩ ← testGroupLocal (F 1)
  let ⟨_, L2, r2, c2⟩ ← testGroupLocal (F 2)
  let ⟨_, L3, r3, c3⟩ ← testGroupLocal (F 3)
  let ⟨_, L4, r4, c4⟩ ← testGroupLocal (V 0)
  let ⟨_, L5, r5, c5⟩ ← testGroupLocal (V 1)
  let ⟨_, L6, r6, c6⟩ ← testGroupLocal (V 2)
  let ⟨_, L7, r7, c7⟩ ← testGroupLocal (V 3)
  let n1 ← Build.fnz L0
  let n2 ← Build.fnz L4
  let q ← Build.freshPairs 6
  pure (.and (a0 ++ a1 ++ a2 ++ a3 ++ [fin (F 0), fin (V 0)] ++
    c0 ++ c1 ++ c2 ++ c3 ++ c4 ++ c5 ++ c6 ++ c7 ++ [n1, n2] ++
    [feq (L0.mul (q 0)) L1, feq (L0.mul (q 1)) L2, feq (L0.mul (q 2)) L3,
      feq (L4.mul (q 3)) L5, feq (L4.mul (q 4)) L6, feq (L4.mul (q 5)) L7] ++
    [feq (D 0) r0, feq (D 1) r1, feq (D 2) r2, feq (D 3) r3,
      feq (D 4) r4.conj, feq (D 5) r5.conj, feq (D 6) r6.conj, feq (D 7) r7.conj,
      feq (D 8) ((q 0).sub (q 3).conj), feq (D 9) ((q 1).sub (q 4).conj),
      feq (D 10) ((q 2).sub (q 5).conj), feq (D 11) (((q 0).mul (q 1)).sub (q 2))]))

/-- The parameter points `C_i = (X_{5i}, …, X_{5i+4})` of `test_group`. -/
noncomputable def testGroupC : Fin 4 → Code := fun i => varPoint (5 * i)

/-- The parameter pairs `D_j = (X_{20+2j}, X_{21+2j})` of `test_group`. -/
noncomputable def testGroupD : Fin 12 → Pair := fun j => varPair (20 + 2 * j)

/-- **The test-group template** (template index `6`). -/
noncomputable def testGroupTemplate : ExPoly :=
  Build.template 44 (testGroupBuild testGroupC testGroupD)

/-- The call blocks of `test_group`, in order. -/
def testGroupBlocks : List (ℕ × ℕ) :=
  [(84, 7), (91, 6), (97, 7), (104, 6), (110, 7), (117, 6), (123, 7), (130, 6), (142, 1),
    (143, 0), (143, 0), (149, 1), (150, 0), (150, 0), (156, 1), (157, 0), (157, 0), (163, 1),
    (164, 0), (164, 0), (170, 1), (171, 0), (171, 0), (177, 1), (178, 0), (178, 0), (184, 1),
    (185, 0), (185, 0), (191, 1), (192, 0), (192, 0)]

theorem testGroup_facts :
    Build.Facts 44 (testGroupBuild testGroupC testGroupD) 206 testGroupBlocks [] := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  have := memberTemplate_wf
  have := memberTemplate_witnesses
  have := rawAddTemplate_wf
  have := rawAddTemplate_witnesses
  have := rawZTemplate_wf
  have := rawZTemplate_witnesses
  have := log25Template_wf
  have := log25Template_witnesses
  have := rawInverseXTemplate_wf
  have := rawInverseXTemplate_witnesses
  wp_run (Avail 206 testGroupBlocks) 206
  facts_close

/-- The calls `member[F]` (block at `w`) and `raw_add[F, neg(C), V]` (block at `w + 7`). -/
noncomputable def testGroupRootFormula (F C V : Code) (w : ℕ) : List Formula :=
  [.call memberTemplate F w, .call rawAddTemplate (Fin.append (Fin.append F C.neg) V) (w + 7)]

/-- The local test at the point `P` with pairs `ζ = (X_b, X_{b+1})`, `λ = (X_{b+2}, X_{b+3})`,
`ρ = (X_{b+4}, X_{b+5})`: the calls `raw_z[P, ζ]` (block at `b + 6`), `log25[ζ, λ]` and
`raw_inverse_x[P, ρ]` (empty blocks at `b + 7`). -/
noncomputable def testGroupLocalFormula (P : Code) (b : ℕ) : List Formula :=
  [.call rawZTemplate (Fin.append P (varPair b).args) (b + 6),
    .call log25Template (Fin.append (varPair b).args (varPair (b + 2)).args) (b + 7),
    .call rawInverseXTemplate (Fin.append P (varPair (b + 4)).args) (b + 7)]

/-- The formula of `test_group` with the variables of the article: `F_i` at `X_{44+5i}`, `V_i`
at `X_{64+5i}`, the root blocks at `84 + 13i`, the local tests at bases `136 + 7i`, the inverse
witnesses `X₁₉₂`, `X₁₉₃` and the ratio pairs `q_{σ,i}` at `X₁₉₄, …, X₂₀₅`. -/
noncomputable def testGroupFormula : Formula :=
  let C := testGroupC
  let D := testGroupD
  let lam : ℕ → Pair := fun i => varPair (138 + 7 * i)
  let ρ : ℕ → Pair := fun i => varPair (140 + 7 * i)
  let q : ℕ → Pair := fun k => varPair (194 + 2 * k)
  .and (testGroupRootFormula (varPoint 44) (C 0) (varPoint 64) 84 ++
    testGroupRootFormula (varPoint 49) (C 1) (varPoint 69) 97 ++
    testGroupRootFormula (varPoint 54) (C 2) (varPoint 74) 110 ++
    testGroupRootFormula (varPoint 59) (C 3) (varPoint 79) 123 ++
    [fin (varPoint 44), fin (varPoint 64)] ++
    testGroupLocalFormula (varPoint 44) 136 ++ testGroupLocalFormula (varPoint 49) 143 ++
    testGroupLocalFormula (varPoint 54) 150 ++ testGroupLocalFormula (varPoint 59) 157 ++
    testGroupLocalFormula (varPoint 64) 164 ++ testGroupLocalFormula (varPoint 69) 171 ++
    testGroupLocalFormula (varPoint 74) 178 ++ testGroupLocalFormula (varPoint 79) 185 ++
    [nzFormula (lam 0).norm 192, nzFormula (lam 4).norm 193] ++
    [feq ((lam 0).mul (q 0)) (lam 1), feq ((lam 0).mul (q 1)) (lam 2), feq ((lam 0).mul (q 2)) (lam 3),
      feq ((lam 4).mul (q 3)) (lam 5), feq ((lam 4).mul (q 4)) (lam 6), feq ((lam 4).mul (q 5)) (lam 7)] ++
    [feq (D 0) (ρ 0), feq (D 1) (ρ 1), feq (D 2) (ρ 2), feq (D 3) (ρ 3),
      feq (D 4) (ρ 4).conj, feq (D 5) (ρ 5).conj, feq (D 6) (ρ 6).conj, feq (D 7) (ρ 7).conj,
      feq (D 8) ((q 0).sub (q 3).conj), feq (D 9) ((q 1).sub (q 4).conj),
      feq (D 10) ((q 2).sub (q 5).conj), feq (D 11) (((q 0).mul (q 1)).sub (q 2))])

theorem testGroupBuild_formula :
    (testGroupBuild testGroupC testGroupD ⟨44, []⟩).1 = testGroupFormula := by
  dsimp only [testGroupBuild, testGroupRoot, testGroupLocal, Build.bind_apply, Build.pure_apply,
    Build.call, Build.freshPoints, Build.freshPairs, Build.freshPair, Build.fresh, Build.fnz,
    Build.nz]
  simp only [memberTemplate_witnesses, rawAddTemplate_witnesses, rawZTemplate_witnesses,
    log25Template_witnesses, rawInverseXTemplate_witnesses]
  rfl

theorem testGroupTemplate_params : testGroupTemplate.params = 44 := rfl

theorem testGroupTemplate_witnesses : testGroupTemplate.witnesses = 162 :=
  testGroup_facts.witnesses

theorem testGroupTemplate_wf : testGroupTemplate.WF := testGroup_facts.wf

/-- The relation of `test_group` through its private blocks: some assignment extending the
parameters satisfies the conjunction with every call replaced by the callee relation. -/
theorem testGroupTemplate_rel_iff (a : Fin 44 → ℚ) :
    testGroupTemplate.Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin 44, y i = a i) ∧
      testGroupFormula.Lift y := by
  unfold testGroupTemplate
  rw [← testGroupBuild_formula]
  exact testGroup_facts.rel_iff_nil a

/-! ### `slope` -/

/-- The contact product `F(t) = (t+0)(t+15)(t+20)(t+24)(t+30)(t+60)`. -/
noncomputable def slopeContact (t : Poly) : Poly :=
  (t + 0) * (t + 15) * (t + 20) * (t + 24) * (t + 30) * (t + 60)

/-- `W = ∏_j (1 + R C'_j²)` in pair arithmetic, multiplied from `1 = (1, 0)` in list order. -/
noncomputable def slopeW (R : Poly) (N : List Pair) : Pair :=
  N.foldl (fun W n => W.mul (Pair.one.add (Pair.smul R n.sq))) Pair.one

theorem PairIn.slopeW {G : ℕ → Prop} {R : Poly} {n : ℕ} {N : Fin n → Pair} (hR : VarsIn R G)
    (hN : ∀ j, PairIn (N j) G) : PairIn (ZInQ.Syntax.slopeW R (List.ofFn N)) G :=
  PairIn.list_foldl (P := fun u => PairIn u G) PairIn.one
    (fun _ _ hv ha => hv.mul (PairIn.one.add (PairIn.smul hR ha.sq)))
    (fun a ha => by obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha; exact hN j)

/-- One group of the slope certificate: the pairs `D_{g,0}, …, D_{g,11}`, the call
`test_group[C, D_g]`, the normalized pairs `C'_{g,j}`, and `Div(1, W_g)` with value `ω_g`;
the formulas are the call, `den_j C'_{g,j} ≐ D_{g,j}` and the division. -/
noncomputable def slopeGroup (C : Fin 20 → Poly) (den1 den2 R : Poly) :
    Build (Pair × List Formula) := do
  let D ← Build.freshPairs 12
  let c ← Build.call testGroupTemplate (Fin.append C (pairsArgs D))
  let N ← Build.freshPairs 12
  let ⟨ω, φ⟩ ← Build.fdiv Pair.one (slopeW R (List.ofFn N))
  pure (ω, [c, feq (Pair.smul den1 (N 0)) (D 0), feq (Pair.smul den1 (N 1)) (D 1),
    feq (Pair.smul den1 (N 2)) (D 2), feq (Pair.smul den1 (N 3)) (D 3),
    feq (Pair.smul den1 (N 4)) (D 4), feq (Pair.smul den1 (N 5)) (D 5),
    feq (Pair.smul den1 (N 6)) (D 6), feq (Pair.smul den1 (N 7)) (D 7),
    feq (Pair.smul den2 (N 8)) (D 8), feq (Pair.smul den2 (N 9)) (D 9),
    feq (Pair.smul den2 (N 10)) (D 10), feq (Pair.smul den2 (N 11)) (D 11), φ])

/-- The construction of `slope` on the slope `t`, the integer `ℓ` and the coordinates `C` of
the points `C₀, …, C₃`. -/
noncomputable def slopeBuild (t ell : Poly) (C : Fin 20 → Poly) : Build Formula := do
  let eta ← Build.fresh
  let q ← Build.fresh
  let R0 ← Build.fresh
  let a := 1 - R0 * q ^ 2
  let R := ell ^ 2 * a ^ 2 * R0
  let n1 ← Build.nz (t - 1)
  let n2 ← Build.nz (slopeContact t)
  let n3 ← Build.nz ell
  let n4 ← Build.nz a
  let den1 := R0 * (t - 1) ^ 2
  let den2 := R0 ^ 25 * (t - 1) ^ 26
  let ⟨ω0, f0⟩ ← slopeGroup C den1 den2 R
  let ⟨ω1, f1⟩ ← slopeGroup C den1 den2 R
  let ⟨ω2, f2⟩ ← slopeGroup C den1 den2 R
  let ⟨ω3, f3⟩ ← slopeGroup C den1 den2 R
  let ⟨ω4, f4⟩ ← slopeGroup C den1 den2 R
  let ⟨ω5, f5⟩ ← slopeGroup C den1 den2 R
  let θ := 2 * (ω0.1 + ω1.1 + ω2.1 + ω3.1 + ω4.1 + ω5.1)
  let B ← Build.fresh
  let nθ ← Build.nz θ
  let cp ← Build.call poleTemplate ![B]
  pure (.and ([.eq (eta ^ 2) 1, n1, n2, n3, .eq (R0 * (t - 1) ^ 8) (eta * slopeContact t), n4] ++
    f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ [nθ, .eq (B * θ ^ 2) R, cp]))

/-- **The slope template** (template index `7`): parameters `t = X₀`, `ℓ = X₁` and the points
`C_i = (X_{2+5i}, …, X_{6+5i})`. -/
noncomputable def slopeTemplate : ExPoly := Build.template 22 (slopeBuild (X 0) (X 1) (varArgs 2 20))

/-- The call blocks of `slope`, in order. -/
def slopeBlocks : List (ℕ × ℕ) :=
  [(53, 162), (266, 162), (479, 162), (692, 162), (905, 162), (1118, 162), (1309, 11)]

theorem slope_facts : Build.Facts 22 (slopeBuild (X 0) (X 1) (varArgs 2 20)) 1320 slopeBlocks [] := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  have := testGroupTemplate_wf
  have := testGroupTemplate_witnesses
  have := poleTemplate_wf
  have := poleTemplate_witnesses
  have hW := @PairIn.slopeW (Avail 1320 slopeBlocks)
  wp_run (Avail 1320 slopeBlocks) 1320
  facts_close

/-- The formulas of slope group `g` with base `β = 29 + 213g`: the call
`test_group[C, D_g]` (block at `β + 24`, `D_{g,j} = (X_{β+2j}, X_{β+2j+1})`), the pair
equations `den_j C'_{g,j} ≐ D_{g,j}` (`C'_{g,j} = (X_{β+186+2j}, X_{β+187+2j})`) and
`Div(1, W_g)` with `ω_g = (X_{β+210}, X_{β+211})` and inverse witness `X_{β+212}`. -/
noncomputable def slopeGroupFormula (C : Fin 20 → Poly) (den1 den2 R : Poly) (β : ℕ) :
    List Formula :=
  let D : Fin 12 → Pair := fun j => varPair (β + 2 * j)
  let N : Fin 12 → Pair := fun j => varPair (β + 186 + 2 * j)
  [.call testGroupTemplate (Fin.append C (pairsArgs D)) (β + 24),
    feq (Pair.smul den1 (N 0)) (D 0), feq (Pair.smul den1 (N 1)) (D 1),
    feq (Pair.smul den1 (N 2)) (D 2), feq (Pair.smul den1 (N 3)) (D 3),
    feq (Pair.smul den1 (N 4)) (D 4), feq (Pair.smul den1 (N 5)) (D 5),
    feq (Pair.smul den1 (N 6)) (D 6), feq (Pair.smul den1 (N 7)) (D 7),
    feq (Pair.smul den2 (N 8)) (D 8), feq (Pair.smul den2 (N 9)) (D 9),
    feq (Pair.smul den2 (N 10)) (D 10), feq (Pair.smul den2 (N 11)) (D 11),
    divFormula Pair.one (slopeW R (List.ofFn N)) (varPair (β + 210)) (β + 212)]

/-- The formula of `slope` with the variables of the article: `η = X₂₂`, `q = X₂₃`,
`R₀ = X₂₄`, inverse witnesses `X₂₅, …, X₂₈`, the six groups at bases `29 + 213g`, `B = X₁₃₀₇`,
`u_θ = X₁₃₀₈` and the pole block at `1309`. -/
noncomputable def slopeFormula : Formula :=
  let t := X 0
  let ell := X 1
  let eta := X 22
  let R0 := X 24
  let a := 1 - R0 * X 23 ^ 2
  let R := ell ^ 2 * a ^ 2 * R0
  let den1 := R0 * (t - 1) ^ 2
  let den2 := R0 ^ 25 * (t - 1) ^ 26
  let C := varArgs 2 20
  let θ := 2 * (X 239 + X 452 + X 665 + X 878 + X 1091 + X 1304)
  .and ([.eq (eta ^ 2) 1, nzFormula (t - 1) 25, nzFormula (slopeContact t) 26, nzFormula ell 27,
      .eq (R0 * (t - 1) ^ 8) (eta * slopeContact t), nzFormula a 28] ++
    slopeGroupFormula C den1 den2 R 29 ++ slopeGroupFormula C den1 den2 R 242 ++
    slopeGroupFormula C den1 den2 R 455 ++ slopeGroupFormula C den1 den2 R 668 ++
    slopeGroupFormula C den1 den2 R 881 ++ slopeGroupFormula C den1 den2 R 1094 ++
    [nzFormula θ 1308, .eq (X 1307 * θ ^ 2) R, .call poleTemplate ![X 1307] 1309])

theorem slopeBuild_formula : (slopeBuild (X 0) (X 1) (varArgs 2 20) ⟨22, []⟩).1 = slopeFormula := by
  dsimp only [slopeBuild, slopeGroup, Build.bind_apply, Build.pure_apply, Build.call,
    Build.freshPairs, Build.fresh, Build.nz, Build.fdiv, Build.fnz]
  simp only [testGroupTemplate_witnesses]
  rfl

theorem slopeTemplate_params : slopeTemplate.params = 22 := rfl

theorem slopeTemplate_witnesses : slopeTemplate.witnesses = 1298 := slope_facts.witnesses

theorem slopeTemplate_wf : slopeTemplate.WF := slope_facts.wf

/-- The relation of `slope` through its private blocks. -/
theorem slopeTemplate_rel_iff (a : Fin 22 → ℚ) :
    slopeTemplate.Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin 22, y i = a i) ∧ slopeFormula.Lift y := by
  unfold slopeTemplate
  rw [← slopeBuild_formula]
  exact slope_facts.rel_iff_nil a

/-! ### `height_certificate` -/

/-- One root of the height certificate: the call `member[P]`, the fresh `a₀`, `a₁`, `b`, and
`NZ(b)`, `b P₁ ≐ a₀`, `b P₂ ≐ a₁`. -/
noncomputable def heightRoot (P : Code) : Build (Poly × Poly × Poly × List Formula) := do
  let m ← Build.call memberTemplate P
  let a0 ← Build.fresh
  let a1 ← Build.fresh
  let d ← Build.fresh
  let n ← Build.nz d
  pure (a0, a1, d, [m, n, .eq (d * P 1) a0, .eq (d * P 2) a1])

/-- One quantity `Q` of the height certificate: three fresh slopes `s₀, s₁, s₂`, the atom
`s₀ + s₁ + s₂ ≐ Q` and the calls `slope[s_l, ℓ, C]`. -/
noncomputable def heightQuantity (Q ell : Poly) (C : Fin 20 → Poly) : Build (List Formula) := do
  let s0 ← Build.fresh
  let s1 ← Build.fresh
  let s2 ← Build.fresh
  let c0 ← Build.call slopeTemplate (Fin.append ![s0, ell] C)
  let c1 ← Build.call slopeTemplate (Fin.append ![s1, ell] C)
  let c2 ← Build.call slopeTemplate (Fin.append ![s2, ell] C)
  pure [.eq (s0 + s1 + s2) Q, c0, c1, c2]

/-- The construction of `height_certificate` on the roots `P₀, P₁, P₂`, the integer `ℓ` and the
coordinates `C` of the points `C₀, …, C₃`. -/
noncomputable def heightBuild (P0 P1 P2 : Code) (ell : Poly) (C : Fin 20 → Poly) :
    Build Formula := do
  let ⟨a00, a01, b0, f0⟩ ← heightRoot P0
  let ⟨a10, a11, b1, f1⟩ ← heightRoot P1
  let ⟨a20, a21, b2, f2⟩ ← heightRoot P2
  let g0 ← heightQuantity a00 ell C
  let g1 ← heightQuantity a01 ell C
  let g2 ← heightQuantity b0 ell C
  let g3 ← heightQuantity a10 ell C
  let g4 ← heightQuantity a11 ell C
  let g5 ← heightQuantity b1 ell C
  let g6 ← heightQuantity a20 ell C
  let g7 ← heightQuantity a21 ell C
  let g8 ← heightQuantity b2 ell C
  pure (.and (f0 ++ f1 ++ f2 ++ g0 ++ g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8))

/-- **The height certificate template** (template index `8`): parameters the points
`P_i = (X_{5i}, …, X_{5i+4})`, `ℓ = X₁₅` and the points `C_i = (X_{16+5i}, …, X_{20+5i})`. -/
noncomputable def heightTemplate : ExPoly :=
  Build.template 36 (heightBuild (varPoint 0) (varPoint 5) (varPoint 10) (X 15) (varArgs 16 20))

/-- The call blocks of `height_certificate`, in order. -/
def heightBlocks : List (ℕ × ℕ) :=
  [(36, 7), (47, 7), (58, 7), (72, 1298), (1370, 1298), (2668, 1298), (3969, 1298),
    (5267, 1298), (6565, 1298), (7866, 1298), (9164, 1298), (10462, 1298), (11763, 1298),
    (13061, 1298), (14359, 1298), (15660, 1298), (16958, 1298), (18256, 1298), (19557, 1298),
    (20855, 1298), (22153, 1298), (23454, 1298), (24752, 1298), (26050, 1298), (27351, 1298),
    (28649, 1298), (29947, 1298), (31248, 1298), (32546, 1298), (33844, 1298)]

set_option maxRecDepth 20000 in
theorem height_facts : Build.Facts 36
    (heightBuild (varPoint 0) (varPoint 5) (varPoint 10) (X 15) (varArgs 16 20)) 35142
    heightBlocks [] := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  have := memberTemplate_wf
  have := memberTemplate_witnesses
  have := slopeTemplate_wf
  have := slopeTemplate_witnesses
  wp_run (Avail 35142 heightBlocks) 35142
  facts_close

/-- The formulas of root `i` of the height certificate at base `b = 36 + 11i`: the call
`member[P]` (block at `b`), `NZ(b_i)` with inverse witness `X_{b+10}`, `b_i P₁ ≐ a_{i0}` and
`b_i P₂ ≐ a_{i1}`, where `a_{i0} = X_{b+7}`, `a_{i1} = X_{b+8}`, `b_i = X_{b+9}`. -/
noncomputable def heightRootFormula (P : Code) (b : ℕ) : List Formula :=
  [.call memberTemplate P b, nzFormula (X (b + 9)) (b + 10), .eq (X (b + 9) * P 1) (X (b + 7)),
    .eq (X (b + 9) * P 2) (X (b + 8))]

/-- The formulas of quantity `k` of the height certificate at base `c = 69 + 3897k`:
`s₀ + s₁ + s₂ ≐ Q` with `s_l = X_{c+l}` and the calls `slope[s_l, ℓ, C]` (blocks at
`c + 3 + 1298l`). -/
noncomputable def heightQuantityFormula (Q : Poly) (c : ℕ) : List Formula :=
  [.eq (X c + X (c + 1) + X (c + 2)) Q,
    .call slopeTemplate (Fin.append ![X c, X 15] (varArgs 16 20)) (c + 3),
    .call slopeTemplate (Fin.append ![X (c + 1), X 15] (varArgs 16 20)) (c + 1301),
    .call slopeTemplate (Fin.append ![X (c + 2), X 15] (varArgs 16 20)) (c + 2599)]

/-- The formula of `height_certificate` with the variables of the article. -/
noncomputable def heightFormula : Formula :=
  .and (heightRootFormula (varPoint 0) 36 ++ heightRootFormula (varPoint 5) 47 ++
    heightRootFormula (varPoint 10) 58 ++
    heightQuantityFormula (X 43) 69 ++ heightQuantityFormula (X 44) 3966 ++
    heightQuantityFormula (X 45) 7863 ++ heightQuantityFormula (X 54) 11760 ++
    heightQuantityFormula (X 55) 15657 ++ heightQuantityFormula (X 56) 19554 ++
    heightQuantityFormula (X 65) 23451 ++ heightQuantityFormula (X 66) 27348 ++
    heightQuantityFormula (X 67) 31245)

theorem heightBuild_formula :
    (heightBuild (varPoint 0) (varPoint 5) (varPoint 10) (X 15) (varArgs 16 20) ⟨36, []⟩).1 =
      heightFormula := by
  dsimp only [heightBuild, heightRoot, heightQuantity, Build.bind_apply, Build.pure_apply,
    Build.call, Build.fresh, Build.nz]
  simp only [memberTemplate_witnesses, slopeTemplate_witnesses]
  rfl

theorem heightTemplate_params : heightTemplate.params = 36 := rfl

theorem heightTemplate_witnesses : heightTemplate.witnesses = 35106 := height_facts.witnesses

theorem heightTemplate_wf : heightTemplate.WF := height_facts.wf

/-- The relation of `height_certificate` through its private blocks. -/
theorem heightTemplate_rel_iff (a : Fin 36 → ℚ) :
    heightTemplate.Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin 36, y i = a i) ∧ heightFormula.Lift y := by
  unfold heightTemplate
  rw [← heightBuild_formula]
  exact height_facts.rel_iff_nil a

end ZInQ.Syntax
