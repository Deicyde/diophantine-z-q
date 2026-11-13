/-! ## linked-tate: the linked Tate data are constructed; `LinkedTateCoreDR` reduced to `LinkedFrobRam`

unram-tate proved g0-mod-field's `TateBridge` (copied above, `UnramTate.tateBridge_of_tateModuleFree`)
by applying the Tate functor `opV` to the points-level descent datum `m_σ = μ_σ ∘ σ`:
`Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`, `a = 1`, `β' g = γ(hgh⁻¹)`, separately for each `ℓ`.
Here the same construction is run once for `ℓ = 5` and `ℓ = 3` with **one** scalar function
`γ₀ : G_ℚ → ℚ̄` (`scalarTransferQ`, unram-tate's `scalarTransfer` with target `ℚ̄`), mapped to
`ℚ̄_ℓ` by embeddings `j_ℓ : ℚ̄ → ℚ̄_ℓ`. So the scalar link of g14-trace (finding F1) holds by
construction, and the existence half of `LinkedTateCoreDR` is proved (from the leaf I3.M0
through `TateCont`). What is left is the named glue Prop `LinkedFrobRam`: `FrobTraceLink` and
`RhoRamWild` for these canonical operators (`tmOf`), for every choice of the data that the
construction uses.
-/

section LinkedDataSec

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- **`ScalarTransfer` with target `ℚ̄`, tied to `β/a`** (proved; unram-tate's `scalarTransfer`
with `PadicAlgCl ℓ` replaced by `ℚ̄`): `γ_ℂ = β/a` takes algebraic values (unram-tate's argument),
so for an embedding `κ : ℚ̄ → ℂ` every value has a preimage `γ₀(σ)`; injectivity of `κ` transfers
`∂γ_ℂ = n/d` to `γ₀`. -/
theorem scalarTransferQ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ)
    (hd : ∀ σ τ, d σ τ ≠ 0)
    (hna : ∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ))
    (hβe : ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ))
    (ha0 : ∀ σ, 0 < a σ)
    (hcos : ∀ σ, ∀ k ∈ GQL L', a (σ * k) = a σ ∧ β (σ * k) = β σ)
    (hone : ∀ k ∈ GQL L', a k = 1 ∧ β k = 1) :
    ∃ (gam : GQ → PkgI4.Qbar) (κ : PkgI4.Qbar →ₐ[ℚ] ℂ),
      (∀ σ, κ (gam σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) ∧ (∀ σ, gam σ ≠ 0) ∧
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PkgI4.Qbar) / (d σ τ : PkgI4.Qbar)) * gam (σ * τ)) ∧
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) ∧ (∀ k ∈ GQL L', gam k = 1) := by
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) / ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hgcos : ∀ σ, ∀ k ∈ GQL L', gC (σ * k) = gC σ := by
    intro σ k hk; simp only [gC]; rw [(hcos σ k hk).1, (hcos σ k hk).2]
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  let κ : PkgI4.Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hpre : ∀ σ, ∃ y : PkgI4.Qbar, κ y = gC σ := by
    intro σ
    have hint := halg σ
    set P := minpoly ℚ (gC σ) with hP
    have hP0 : P.map (algebraMap ℚ PkgI4.Qbar) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hroot : ((P.map (algebraMap ℚ PkgI4.Qbar)).map (κ : PkgI4.Qbar →+* ℂ)).IsRoot (gC σ) := by
      rw [Polynomial.map_map, κ.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        minpoly.aeval]
    obtain ⟨y, hy⟩ :=
      (IsAlgClosed.splits (P.map (algebraMap ℚ PkgI4.Qbar))).mem_range_of_isRoot hP0 hroot
    exact ⟨y, hy⟩
  choose gam hgam using hpre
  have hκ : Function.Injective κ := κ.toRingHom.injective
  refine ⟨gam, κ, hgam, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    rw [← hgam, h0, map_zero]
  · intro σ τ
    apply hκ
    rw [map_mul, map_mul, hgam, hgam, map_div₀, map_intCast, map_intCast, hgam, hq]
    simp only [q]
    push_cast
    ring
  · intro σ k hk
    apply hκ
    rw [hgam, hgam, hgcos σ k hk]
  · intro k hk
    apply hκ
    rw [hgam, map_one, hg1 k hk]

/-- **The canonical operators** `Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`
(unram-tate's construction, for the points-level maps `m`, the transport `Θ : A(ℚ̄) ≅ A_{L'}(\bar{L'})`
and `h ∈ G_ℚ`). -/
def tmOf {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (m : GQ → (PtQ L A →+ PtQ L A)) (ℓ : ℕ) [Fact ℓ.Prime] :
    PkgI4.GQ → Module.End (PadicAlgCl ℓ)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
  fun g => ((opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ))
    (m (h * g * h⁻¹))

/-- **Glue: the Frobenius trace link and Glazer's wild ramification for the canonical
operators** (linked-tate; the remaining content of `LinkedTateCoreDR`). For every fibre context
and G7 data, every transport `(Θ, h)` with unram-tate's `TatePoints` property, every
points-level descent datum `(m, a, n, d)` of `A` for `ε` (the clauses of g0-mod-field's
`DescentDatum`, with the rational discrepancy `n/d` as functions), every `γ₀ : G_ℚ → ℚ̄` with
`∂γ₀ = n/d`, constant on `G_{L'}`-cosets and `1` on `G_{L'}`, and all embeddings `j₅`, `j₃`:
* g14-trace's `FrobTraceLink` for `tmOf … 5`, `tmOf … 3` (N5 L777-786: at a Frobenius `τ` above
  `p ∉ S`, `N·Tm_ℓ(τ)` is `V_ℓ` of `N·μ̄ ∘ F` on the reduction, at `ℓ = 3` and `ℓ = 5`);
* `RhoRamWild` for `ρ₅ = (j₅∘β')⁻¹ Tm₅` at `p ≠ 5` and `ρ₃` at `p = 5` (`β' g = γ₀(hgh⁻¹)`,
  `a = 1`; N5 L819-852, D1-D4).
GLUE (AV reduction theory, Néron/Serre–Tate, and the conductor bounds of G15). -/
def LinkedFrobRam : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∀ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      (∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)) →
    ∀ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ) (n d : GQ → GQ → ℤ),
      (∀ σ, 0 < a σ) →
      (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) →
      (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
      (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
      (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) →
      (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) →
      (∀ σ τ, n σ τ ≠ 0 ∧ d σ τ ≠ 0 ∧ d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ) ∧
        (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
      (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
    ∀ (gam : GQ → PkgI4.Qbar),
      (∃ κ : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ σ, κ (gam σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) →
      (∀ σ, gam σ ≠ 0) →
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PkgI4.Qbar) / (d σ τ : PkgI4.Qbar)) * gam (σ * τ)) →
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) → (∀ k ∈ GQL L', gam k = 1) →
    ∀ (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3),
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))
        (tmOf hLL' A Θ h m 5) (tmOf hLL' A Θ h m 3) ∧
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 5) (fun _ => j5 1)
            (fun g => j5 (gam (h * g * h⁻¹))))) ∧
        (p = 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 3) (fun _ => j3 1)
            (fun g => j3 (gam (h * g * h⁻¹)))))

/-- **Glue: the Frobenius trace link for the canonical operators** (linked-tate; N5 L777-786).
For every fibre context and G7 data, every transport `(Θ, h)` with unram-tate's `TatePoints`
property and every points-level descent datum `(m, a, n, d)` of `A` for `ε` (the clauses of
g0-mod-field's `DescentDatum`, the discrepancy `n/d` as functions): g14-trace's `FrobTraceLink`
holds for `tmOf … 5` and `tmOf … 3`: outside a finite set of primes, at every arithmetic Frobenius
`τ` there are an abelian variety `Ā` over a field of characteristic `p`, `α' ∈ End(Ā)` and
`N ≠ 0` with `N·Tm_ℓ(τ)` conjugate to `V_ℓ(α')` at `ℓ = 3` and `ℓ = 5` (Glazer: `Ā` the
reduction of `A_{L'}`, `α' = N·μ̄ ∘ F`; Néron mapping property and Serre–Tate). GLUE. -/
def LinkedFrob : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∀ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      (∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)) →
    ∀ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ) (n d : GQ → GQ → ℤ),
      (∀ σ, 0 < a σ) →
      (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) →
      (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
      (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
      (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) →
      (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) →
      (∀ σ τ, n σ τ ≠ 0 ∧ d σ τ ≠ 0 ∧ d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ) ∧
        (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
      (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))
        (tmOf hLL' A Θ h m 5) (tmOf hLL' A Θ h m 3)

/-- **Glue: Glazer's wild ramification for the canonical descended operators** (linked-tate;
N5 L819-852, D1-D4). Same data as `LinkedFrob`, and every `γ₀ : G_ℚ → ℚ̄` that is `β/a` under some embedding `ℚ̄ → ℂ` (the
scalars of G7, N5 L719-722), with `∂γ₀ = n/d`, constant on `G_{L'}`-cosets and `1` on `G_{L'}`, and
all embeddings `j₅`, `j₃`: `RhoRamWild` for
`ρ₅ = (j₅∘β')⁻¹ Tm₅` at `p ≠ 5` and for `ρ₃` at `p = 5` (`β' g = γ₀(hgh⁻¹)`, `a = 1`). GLUE. -/
def LinkedRam : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∀ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      (∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)) →
    ∀ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ) (n d : GQ → GQ → ℤ),
      (∀ σ, 0 < a σ) →
      (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) →
      (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
      (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
      (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) →
      (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) →
      (∀ σ τ, n σ τ ≠ 0 ∧ d σ τ ≠ 0 ∧ d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ) ∧
        (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
      (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
    ∀ (gam : GQ → PkgI4.Qbar),
      (∃ κ : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ σ, κ (gam σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) →
      (∀ σ, gam σ ≠ 0) →
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PkgI4.Qbar) / (d σ τ : PkgI4.Qbar)) * gam (σ * τ)) →
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) → (∀ k ∈ GQL L', gam k = 1) →
    ∀ (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3),
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 5) (fun _ => j5 1)
            (fun g => j5 (gam (h * g * h⁻¹))))) ∧
        (p = 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 3) (fun _ => j3 1)
            (fun g => j3 (gam (h * g * h⁻¹)))))

/-- `LinkedFrobRam` is the conjunction of `LinkedFrob` and `LinkedRam` (proved). -/
theorem linkedFrobRam_of (hF : LinkedFrob) (hR : LinkedRam) : LinkedFrobRam := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8
    gam g0 g1 g2 g3 g4 j5 j3
  exact ⟨hF Y Φ π u P hctx L A ε N χ β L' hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8,
    hR Y Φ π u P hctx L A ε N χ β L' hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8 gam g0 g1 g2 g3 g4
      j5 j3⟩

set_option maxHeartbeats 1000000 in
/-- **`LinkedTateCoreDR`, proved** from the leaf I3.M0 (`PkgI3.TateModuleFree`, through
unram-tate's `tateCont_of_tateModuleFree`) and the glue `LinkedFrobRam`. The data: unram-tate's
`Θ, h` (`tatePoints`), the descent datum of `G7Data`, `γ₀` from `scalarTransferQ`, `a = 1`,
`β' g = γ₀(hgh⁻¹)`, `j_ℓ = IsAlgClosed.lift : ℚ̄ → ℚ̄_ℓ`; `G7Out` at each `ℓ` by unram-tate's
assembly (`tateBridge_of_pieces`) run with the scalars `j_ℓ ∘ 1`, `j_ℓ ∘ β'`. -/
theorem linkedTateCoreDR_of (hT : PkgI3.TateModuleFree) (hFR : LinkedFrobRam) :
    HSyn.LinkedTate.LinkedTateCoreDR := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrank
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hD' := hD
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, hmsf, hmc, hmF⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(endBaseChange K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := tatePoints L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gam, κ, hκgam, hgam0, hgamc, hgamcos, hgam1⟩ := scalarTransferQ L' a β ε n d hd hna hβe ha0
    (fun σ k hk => ⟨(haL σ k (hLL'G k hk)).2.1, by
      have := hβe σ k
      rw [hβL' k hk, _root_.mul_one, eps_right_one L ε hεc hinf h11 σ k (hLL'G k hk),
        _root_.one_mul] at this
      exact this.symm⟩)
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  have hC := tateCont_of_tateModuleFree hT
  have hR := resQEmbedding
  let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
  have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
    show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
    group
  -- `G_{L'}` is normal
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hres : ∀ σ : Field.absoluteGaloisGroup L',
      cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
    intro σ
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  -- one coefficient prime, with the scalars `j ∘ 1`, `j ∘ γ₀ ∘ cj`
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
          (tmOf hLL' A Θ h m ℓ) c c (fun _ => j 1) (fun g => j (gam (h * g * h⁻¹))) uu := by
    intro ℓ _ j
    let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
    let m' : GQ → AddMonoid.End (PtQ L A) := m
    let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
    let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
      ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
    let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => j 1
    let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (gam (cj g))
    -- matrix units
    let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
    have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, iO_sq, map_add, map_one, two_smul]
    have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
      module
    have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
      rw [← map_mul, iO_jO, map_neg, map_mul]
    obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
    have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
      intro g o
      apply Commute.map _ R
      exact hmEnd (cj g) (iot o)
    -- the relations
    have hT : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
      intro g g₂
      have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
        hnd (cj g) (cj g₂)
      have h1 := congrArg R h0
      rw [map_zsmul, map_zsmul, ← hcj] at h1
      have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
        show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
        rw [← map_mul]; exact h1
      have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
          (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
        (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
          (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
      have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
      show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
      rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
      intro g g₂; simp only [a', map_one, _root_.one_mul, _root_.mul_one]
    have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
      intro g g₂
      show j (gam (cj g)) * j (gam (cj g₂)) =
        ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) *
          j (gam (cj (g * g₂)))
      rw [← map_mul, hgamc, map_mul, map_div₀, map_intCast, map_intCast, hcj]
    have hβ0 : ∀ g, β' g ≠ 0 := fun g => (map_ne_zero j).mpr (hgam0 _)
    have hTres : ∀ σ : Field.absoluteGaloisGroup L',
        Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      have hτ := hres σ
      let σ' : Qbar ≃ₐ[L] Qbar :=
        AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
          (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
      have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
      rw [tate_eq_opV]
      show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
      congr 1
      refine DFunLike.ext _ _ fun x => ?_
      show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
      rw [hm]
      show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
      rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
    have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
        GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      unfold GlueDescent.rho
      rw [hTres σ]
      simp only [β', a', hgam1 _ (hres σ), map_one, inv_one, _root_.mul_one, one_smul]
    refine ⟨c', uu, hdim, hrank, hT, ha, hβ, hβ0,
      fun σ => ⟨hTres σ, map_one j, by
        show j (gam (cj (@GaloisCopy.resQ L' _ hNF σ))) = 1
        rw [hgam1 _ (hres σ), map_one]⟩,
      fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
    -- continuity
    intro f v
    rw [continuous_iff_continuousAt]
    intro g₀
    let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
    have he₀ : Topology.IsOpenEmbedding e₀ :=
      (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
    have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
    have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
        fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
      funext σ
      simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
      rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hT ha hβ hβ0, hrho1, Module.End.mul_apply]
    have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
      rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
    rw [he₀.continuousAt_iff, he₀1] at hc
    exact hc
  let j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5 := IsAlgClosed.lift
  let j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3 := IsAlgClosed.lift
  obtain ⟨c5, u5, h5⟩ := key 5 j5
  obtain ⟨c3, u3, h3⟩ := key 3 j3
  obtain ⟨hF, hRam⟩ := hFR Y Φ π u P hctx L A ε N χ β L' hLL' hD' Θ h hΘ m a n d ha0 haL hmL
    hmLL hmEnd hmsf (fun σ τ => ⟨hn σ τ, hd σ τ, hnd σ τ, hna σ τ⟩) hmF gam ⟨κ, hκgam⟩ hgam0 hgamc hgamcos
    hgam1 j5 j3
  exact ⟨fun _ => 1, fun g => gam (h * g * h⁻¹), j5, j3, tmOf hLL' A Θ h m 5, c5, c5, u5,
    tmOf hLL' A Θ h m 3, c3, c3, u3, h5, h3, hF, hRam⟩

end UnramTate

/-- **`LinkedTateData`, proved** from the leaves T7 (`PkgI3.CharPolyIndepOfEll`) and I3.M0
(`PkgI3.TateModuleFree`) and the glue Props `FibreSimple`, `QMEndRank`, `LinkedFrobRam`. -/
theorem HSyn.LinkedTate.linkedTateData_of_frobRam (hM : PkgI3.CharPolyIndepOfEll)
    (hT : PkgI3.TateModuleFree) (hFS : HSyn.G0Split.FibreSimple)
    (hR : HSyn.LinkedTate.QMEndRank) (hFR : UnramTate.LinkedFrobRam) :
    HSyn.G0AssembleMod.LinkedTateData :=
  HSyn.LinkedTate.linkedTateData_of hM
    (HSyn.LinkedTate.linkedTateCore_of hFS hR (UnramTate.linkedTateCoreDR_of hT hFR))

/-- **`AfterG7` (G8-G16) with both joint Props of g0-assemble reduced** (proved): g0-assemble's
inputs of `afterG7_of` (leaf bundles, `GaloisPieces`, `DirichletOfFinite`, `CarayolR17'`, the
three LadicCond glue Props) with `ModelG3G6` and `LinkedTateData` replaced by the glue Props
`FibreSimple` (already a `GluePieces` field), `GoodRedG3Bridge`, `QMEndRank`, `LinkedFrob`,
`LinkedRam`; the leaves used are the bundles' R6, R7a, T5 (G3), T7 (G14) and T26 = I3.M0. -/
theorem HSyn.LinkedTate.afterG7_of_final (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : G0Galois.GaloisPieces) (hDF : G0ModNewform.DirichletOfFinite)
    (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hFS : HSyn.G0Split.FibreSimple) (hB : HSyn.LinkedTate.GoodRedG3Bridge)
    (hR : HSyn.LinkedTate.QMEndRank) (hF : UnramTate.LinkedFrob) (hRam : UnramTate.LinkedRam) :
    G0ModField.AfterG7 :=
  HSyn.G0AssembleMod.afterG7_of r t m hDF hCar hSw hL8 hAd
    (HSyn.LinkedTate.modelG3G6_of hFS (HSyn.LinkedTate.qmModelG3_of r.r7a r.r6 t.t5 hB))
    (HSyn.LinkedTate.linkedTateData_of_frobRam t.t7 t.t26 hFS hR
      (UnramTate.linkedFrobRam_of hF hRam))

end

end LinkedDataSec

#print axioms UnramTate.tateBridge_of_tateModuleFree
#print axioms UnramTate.scalarTransferQ
#print axioms UnramTate.linkedTateCoreDR_of
#print axioms UnramTate.linkedFrobRam_of
#print axioms HSyn.LinkedTate.linkedTateData_of_frobRam
#print axioms HSyn.LinkedTate.afterG7_of_final
