/-! # g8-tate, part 5: `TateBridgeOnL` from T26, `EndRank4` and linked-tate's `LinkedFrob`

The data of `TateBridgeOnL` are those of unram-tate's construction as run by linked-tate
(`linkedTateCoreDR_of`, copied with changes to the scalars): `Θ, h` from `tatePoints`, the descent
datum `m, a, n/d` of `G7Data`, the canonical operators `Tm_ℓ = tmOf … ℓ`, `γ₀ = gam` from
`scalarTransferQ` (`κ ∘ γ₀ = β/a`), and
* `βQ = κ⁻¹ ∘ β` (the values of `β` are roots of unity: `β² = χ`), so `ιC ∘ βQ = β` with `ιC = κ`;
* `aQ(g) = βQ(g) / γ₀(hgh⁻¹)`, `ε_ℓ = ∂(j_ℓ ∘ βQ)`.
Then `∂aQ · c = ∂βQ` (`c = ∂γ₀ ∘ conj_h`), and `aQ = 1` on `G_L` because `β(hkh⁻¹) = β(k)` for
`k ∈ G_L` (`ε` is `1` when one argument lies in `G_L`) and `a = 1` on `G_L`. The representation
`ρ = β'⁻¹ a' Tm` is linked-tate's (`β'⁻¹ a' = (j γ₀(hgh⁻¹))⁻¹`), so continuity carries over.
`OnL` is part 4's `onL_canon`; `FrobTraceLink` is linked-tate's `LinkedFrob`, applied to the same
choice. `dim A_{L'} = 2` is proved (`PK.surface`, the kernel's `dim_baseChange`); `rank End = 4` is
the named glue `EndRank4`. -/

noncomputable section

namespace G8Tate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open G0ModField UnramTate

/-- **GLUE (G5-G6 + A9; N5 L564-577): the endomorphism ring of the model over `L'` has rank 4.**
For every fibre context and G7 data, `rank_ℤ End(A_{L'}) = 4`. This is the `rank` clause that
`G0Galois.G7Out` asks for and that g14-trace's `TateBridge35` and g0-mod-field's `TateBridge` take
as a hypothesis. linked-tate derives it (`linkedTateCore_of`, over `Leaves.lean`, not re-checked
here) from `FibreSimple` (`EndDivision A_{L'}`) and its `QMEndRank` (Albert's classification;
Mumford §19 Thm 3, §21; numbering UNVERIFIED). -/
def EndRank4 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4

/-- An algebraic complex number lies in the image of any embedding `κ : ℚ̄ → ℂ` (proved; the
argument of linked-tate's `scalarTransferQ`). -/
theorem exists_preimage (κ : PkgI4.Qbar →ₐ[ℚ] ℂ) {z : ℂ} (hint : IsIntegral ℚ z) :
    ∃ y : PkgI4.Qbar, κ y = z := by
  set P := minpoly ℚ z with hP
  have hP0 : P.map (algebraMap ℚ PkgI4.Qbar) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have hroot : ((P.map (algebraMap ℚ PkgI4.Qbar)).map (κ : PkgI4.Qbar →+* ℂ)).IsRoot z := by
    rw [Polynomial.map_map, κ.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
      minpoly.aeval]
  obtain ⟨y, hy⟩ :=
    (IsAlgClosed.splits (P.map (algebraMap ℚ PkgI4.Qbar))).mem_range_of_isRoot hP0 hroot
  exact ⟨y, hy⟩

/-- `β(σ)^{2·ord χ} = 1` from `β² = χ` (proved; the computation in g0-mod-field's
`b3_of_cochain`). -/
theorem beta_pow_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
    (hβs : ∀ x, β x ^ 2 = galChar χ x) (σ : GQ) : β σ ^ (2 * orderOf χ) = 1 := by
  rw [pow_mul, hβs]
  show (MulChar.mulEquivToUnitHom χ (cyc N σ)) ^ orderOf χ = 1
  rw [← MonoidHom.pow_apply, ← map_pow, pow_orderOf_eq_one, map_one, MonoidHom.one_apply]

/-- `β(hkh⁻¹) = β(k)` for `k ∈ H` when `∂β = ε` and `ε` is `1` as soon as one argument lies in
`H` (proved). -/
theorem beta_conj {G U : Type*} [Group G] [CommGroup U] (H : Subgroup G) (β : G → U)
    (ε : G → G → U) (hβe : ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ))
    (hεN : ∀ σ τ, (σ ∈ H ∨ τ ∈ H) → ε σ τ = 1) (h k : G) (hk : k ∈ H) (hck : h * k * h⁻¹ ∈ H) :
    β (h * k * h⁻¹) = β k := by
  have e1 := hβe (h * k * h⁻¹) h
  have e2 := hβe h k
  rw [hεN _ _ (Or.inl hck), _root_.one_mul] at e1
  rw [hεN _ _ (Or.inr hk), _root_.one_mul] at e2
  have e3 : h * k * h⁻¹ * h = h * k := by group
  rw [e3] at e1
  have e4 := e1.trans e2.symm
  rw [_root_.mul_comm (β h)] at e4
  exact mul_right_cancel e4

set_option maxHeartbeats 2000000 in
/-- **`TateBridgeOnL` from the leaf T26 (`PkgI3.TateModuleFree`) and the glue Props `EndRank4`
and linked-tate's `LinkedFrob` (proved).** -/
theorem tateBridgeOnL_of (hT : PkgI3.TateModuleFree) (hRk : EndRank4)
    (hF : UnramTate.LinkedFrob) : TateBridgeOnL := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD _hLD
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hD' := hD
  have hrank := hRk Y Φ π u P hctx L A ε N χ β L' hLL' hD
  obtain ⟨hQM, hDD, -, -, -, -, hβs, hβe, hL', -, -, -⟩ := hD
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := by
    obtain ⟨K, hKL, PK, -, hA⟩ := hQM
    rw [@PkgI3.AbVar.dim_baseChange L _ A L' _ (incAlg hLL'), hA,
      @PkgI3.AbVar.dim_baseChange K _ PK.A L _ (incAlg hKL)]
    exact PK.surface
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
  -- `G_{L'}` and `G_L` are normal
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hnormL : (L.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hresL' : ∀ σ : Field.absoluteGaloisGroup L',
      (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
    intro σ
    show (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup
    rw [← resQRange L']; exact ⟨σ, rfl⟩
  have hres : ∀ σ : Field.absoluteGaloisGroup L',
      cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := fun σ => hnorm.conj_mem _ (hresL' σ) h
  -- `βQ = κ⁻¹ ∘ β` and `aQ = βQ / γ₀(h · h⁻¹)`
  have hκ : Function.Injective κ := κ.toRingHom.injective
  have hord : 0 < 2 * orderOf χ := Nat.mul_pos two_pos (orderOf_pos_dirichlet χ)
  have hβint : ∀ σ, IsIntegral ℚ (β σ : ℂ) := by
    intro σ
    refine ⟨Polynomial.X ^ (2 * orderOf χ) - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 hord.ne', ?_⟩
    have h1 : (β σ : ℂ) ^ (2 * orderOf χ) = 1 := by
      rw [← Units.val_pow_eq_pow_val, beta_pow_eq_one χ β hβs σ, Units.val_one]
    simp [Polynomial.eval₂_sub, h1]
  choose βQ hβQ using fun σ => exists_preimage κ (hβint σ)
  have hβQ0 : ∀ σ, βQ σ ≠ 0 := fun σ h0 => by
    have := hβQ σ
    rw [h0, map_zero] at this
    exact Units.ne_zero _ this.symm
  have hβQ1 : ∀ k ∈ GQL L', βQ k = 1 := fun k hk => by
    apply hκ
    have e5 : κ (βQ k) = β k := hβQ k
    rw [e5, map_one, hβL' k hk, Units.val_one]
  have hεN := GlueDescent.B3Q.inflatedNormalized_of L ε hεc hinf h11
  let aQ : GQ → PkgI4.Qbar := fun g => βQ g / gam (cj g)
  have haQL : ∀ k ∈ GQL L, aQ k = 1 := by
    intro k hk
    have hck : cj k ∈ GQL L := hnormL.conj_mem k hk h
    have hb : β (cj k) = β k := beta_conj (GQL L) β ε hβe hεN h k hk hck
    apply hκ
    show κ (βQ k / gam (cj k)) = κ 1
    have e5 : κ (βQ k) = β k := hβQ k
    have e6 : κ (gam (cj k)) = β (cj k) / a (cj k) := hκgam (cj k)
    rw [map_one, map_div₀, e5, e6, hb, (haL 1 (cj k) hck).1]
    have hb0 : (β k : ℂ) ≠ 0 := Units.ne_zero _
    push_cast
    field_simp
  have hQa : ∀ g g₂ : PkgI4.GQ, aQ g * aQ g₂ *
      ((n (cj g) (cj g₂) : PkgI4.Qbar) / (d (cj g) (cj g₂) : PkgI4.Qbar)) =
      βQ g * βQ g₂ / βQ (g * g₂) * aQ (g * g₂) := by
    intro g g₂
    have e := hgamc (cj g) (cj g₂)
    rw [← hcj] at e
    have h1 := hgam0 (cj g)
    have h2 := hgam0 (cj g₂)
    have h3 := hgam0 (cj (g * g₂))
    have h4 := hβQ0 (g * g₂)
    have hq0 : ((n (cj g) (cj g₂) : PkgI4.Qbar) / (d (cj g) (cj g₂) : PkgI4.Qbar)) ≠ 0 :=
      div_ne_zero (Int.cast_ne_zero.mpr (hn _ _)) (Int.cast_ne_zero.mpr (hd _ _))
    simp only [aQ]
    calc βQ g / gam (cj g) * (βQ g₂ / gam (cj g₂)) *
          ((n (cj g) (cj g₂) : PkgI4.Qbar) / (d (cj g) (cj g₂) : PkgI4.Qbar))
        = βQ g * βQ g₂ * ((n (cj g) (cj g₂) : PkgI4.Qbar) / (d (cj g) (cj g₂) : PkgI4.Qbar)) /
          (gam (cj g) * gam (cj g₂)) := by ring
      _ = βQ g * βQ g₂ * ((n (cj g) (cj g₂) : PkgI4.Qbar) / (d (cj g) (cj g₂) : PkgI4.Qbar)) /
          (((n (cj g) (cj g₂) : PkgI4.Qbar) / (d (cj g) (cj g₂) : PkgI4.Qbar)) *
            gam (cj (g * g₂))) := by rw [e]
      _ = βQ g * βQ g₂ / gam (cj (g * g₂)) := by
          rw [div_eq_div_iff (mul_ne_zero hq0 h3) h3]; ring
      _ = βQ g * βQ g₂ / βQ (g * g₂) * (βQ (g * g₂) / gam (cj (g * g₂))) := by
          rw [div_mul_div_comm, div_eq_div_iff h3 (mul_ne_zero h4 h3)]; ring
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
          (tmOf hLL' A Θ h m ℓ) c ε' (fun g => j (aQ g)) (fun g => j (βQ g)) uu := by
    intro ℓ _ j
    let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
    let m' : GQ → AddMonoid.End (PtQ L A) := m
    let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
    let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
      ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
    let a' : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (aQ g)
    let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (βQ g)
    let ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ => j (βQ g * βQ g₂ / βQ (g * g₂))
    have hc'j : ∀ g g₂, c' g g₂ = j ((n (cj g) (cj g₂) : PkgI4.Qbar) / (d (cj g) (cj g₂) : PkgI4.Qbar)) :=
      fun g g₂ => by rw [map_div₀, map_intCast, map_intCast]
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
    have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = ε' g g₂ * a' (g * g₂) := by
      intro g g₂
      rw [hc'j]
      simp only [a', ε']
      rw [← map_mul, ← map_mul, ← map_mul, hQa g g₂]
    have hβ : ∀ g g₂, β' g * β' g₂ = ε' g g₂ * β' (g * g₂) := by
      intro g g₂
      simp only [β', ε']
      rw [← map_mul, ← map_mul, div_mul_cancel₀ _ (hβQ0 _)]
    have hβ0 : ∀ g, β' g ≠ 0 := fun g => (map_ne_zero j).mpr (hβQ0 _)
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
      simp only [β', a', haQL _ (hLL'G _ (hresL' σ)), hβQ1 _ (hresL' σ), map_one, inv_one,
        _root_.mul_one, one_smul]
    refine ⟨c', ε', uu, hdim, hrank, hT, ha, hβ, hβ0,
      fun σ => ⟨hTres σ, by
        show j (aQ (@GaloisCopy.resQ L' _ hNF σ)) = 1
        rw [haQL _ (hLL'G _ (hresL' σ)), map_one], by
        show j (βQ (@GaloisCopy.resQ L' _ hNF σ)) = 1
        rw [hβQ1 _ (hresL' σ), map_one]⟩,
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
      rw [← GlueDescent.rho_map_mul Tm c' ε' a' β' hT ha hβ hβ0, hrho1, Module.End.mul_apply]
    have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
      rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
    rw [he₀.continuousAt_iff, he₀1] at hc
    exact hc
  let j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5 := IsAlgClosed.lift
  let j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3 := IsAlgClosed.lift
  obtain ⟨c5, ε5, u5, h5⟩ := key 5 j5
  obtain ⟨c3, ε3, u3, h3⟩ := key 3 j3
  have hFr := hF Y Φ π u P hctx L A ε N χ β L' hLL' hD' Θ h hΘ m a n d ha0 haL hmL hmLL hmEnd
    hmsf (fun σ τ => ⟨hn σ τ, hd σ τ, hnd σ τ, hna σ τ⟩) hmF
  obtain ⟨ψ5, hOn5⟩ := onL_canon hLL' A Θ h m n d hmL hmLL hmsf hn hd hnd 5
    (fun g => j5 (aQ g)) (fun k hk => by show j5 (aQ k) = 1; rw [haQL k hk, map_one])
  obtain ⟨ψ3, hOn3⟩ := onL_canon hLL' A Θ h m n d hmL hmLL hmsf hn hd hnd 3
    (fun g => j3 (aQ g)) (fun k hk => by show j3 (aQ k) = 1; rw [haQL k hk, map_one])
  exact ⟨aQ, βQ, j5, j3, tmOf hLL' A Θ h m 5, c5, ε5, u5, tmOf hLL' A Θ h m 3, c3, ε3, u3,
    ψ5, ψ3, h5, h3, hFr, ⟨κ, hβQ⟩, hOn5, hOn3⟩

/-- **g8-object's `LinkedTateObjS` from the leaves R6, I2-Tors, T26, the textbook Prop
`UnramRoots 2 5`, and the glue Props `EndRank4` and `LinkedFrob` (proved).** -/
theorem linkedTateObjS_of_frob (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU : G15Ram.UnramRoots 2 5)
    (hT : PkgI3.TateModuleFree) (hRk : EndRank4) (hF : UnramTate.LinkedFrob) :
    G8Object.LinkedTateObjS :=
  linkedTateObjS_of_onL hR6 hTors hU (tateBridgeOnL_of hT hRk hF)

/-- **g8-object's `LinkedTateDataD` (g0-assemble's `LinkedTateData` for G7 data with `[L:ℚ] ≤ D`)
from the leaves T7, R6, I2-Tors, T26, `UnramRoots 2 5`, `EndRank4` and `LinkedFrob` (proved).** -/
theorem linkedTateDataD_of_frob (hM : PkgI3.CharPolyIndepOfEll)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : G15Ram.UnramRoots 2 5) (hT : PkgI3.TateModuleFree) (hRk : EndRank4)
    (hF : UnramTate.LinkedFrob) : G8Object.LinkedTateDataD :=
  G8Object.linkedTateDataD_of_S hM (linkedTateObjS_of_frob hR6 hTors hU hT hRk hF)

end G8Tate

end

#print axioms G8Tate.exists_preimage
#print axioms G8Tate.tateBridgeOnL_of
#print axioms G8Tate.linkedTateObjS_of_frob
#print axioms G8Tate.linkedTateDataD_of_frob
