/-! ## lg-kerwild §5: `TateBridgeK` proved from the leaf I3.M0 (unram-tate's proof with the
kernel-field clause)

unram-tate proved g0-mod-field's `TateBridge` from I3.M0 (`tateBridge_of_tateModuleFree`) with
`β' g = γ(h g h⁻¹)`, `γ = ψ ∘ (β/a)`, `ψ` a field embedding. Below: `ScalarTransferK` adds to
unram-tate's `ScalarTransfer` the clause `γ(σ) = 1 → β(σ) = a(σ)` (the same proof gives it, `ψ`
being injective), and `tateBridgeK_of_piecesK` is unram-tate's `tateBridge_of_pieces` (proof copied)
with the extra conclusion `KerWild L' β' L`: for `g ∈ G_L` with `β'(g) = 1`, `hgh⁻¹ ∈ G_L`
(normal), `a = 1` on `G_L` (DescentDatum), so `β(hgh⁻¹) = 1`, so `hgh⁻¹ ∈ G_{L'}` (G7Data's
clause), so `g ∈ G_{L'}` (normal) `= resQ_{L'}(G_{L'})`. -/

section LGTateBridgeKSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- **Glue piece TB-iii with the kernel clause (GLUE, proved below: `scalarTransferK`).**
unram-tate's `ScalarTransfer` (statement copied) with the extra output `γ(σ) = 1 ⟹ β(σ) = a(σ)`:
the transfer of the scalars into `ℚ̄_ℓ` is injective on the values of `β/a`. -/
def ScalarTransferK : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (ℓ : ℕ) [Fact ℓ.Prime] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ),
    (∀ σ τ, d σ τ ≠ 0) →
    (∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
    (∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ)) →
    (∀ σ, 0 < a σ) →
    (∀ σ, ∀ k ∈ GQL L', a (σ * k) = a σ ∧ β (σ * k) = β σ) →
    (∀ k ∈ GQL L', a k = 1 ∧ β k = 1) →
    ∃ gam : GQ → PadicAlgCl ℓ, (∀ σ, gam σ ≠ 0) ∧
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ)) ∧
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) ∧ (∀ k ∈ GQL L', gam k = 1) ∧
      (∀ σ, gam σ = 1 → (β σ : ℂ) = ((a σ : ℝ) : ℂ))

/-- **`ScalarTransferK`, proved** (unram-tate's `scalarTransfer`, proof copied, plus the kernel
clause from the injectivity of `ψ`). -/
theorem scalarTransferK : ScalarTransferK := by
  intro L' _ _ ℓ _ a β ε n d hd hna hβe ha0 hcos hone
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
  let F : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range gC)
  haveI : Algebra.IsAlgebraic ℚ F := IntermediateField.isAlgebraic_adjoin (by
    rintro x ⟨σ, rfl⟩; exact halg σ)
  let ψ : F →ₐ[ℚ] PadicAlgCl ℓ := IsAlgClosed.lift
  have hmem : ∀ σ, gC σ ∈ F := fun σ => IntermediateField.subset_adjoin ℚ _ ⟨σ, rfl⟩
  let gam : GQ → PadicAlgCl ℓ := fun σ => ψ ⟨gC σ, hmem σ⟩
  refine ⟨gam, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    have : (⟨gC σ, hmem σ⟩ : F) = 0 := ψ.toRingHom.injective (h0.trans (map_zero ψ).symm)
    exact congrArg Subtype.val this
  · intro σ τ
    have hF : (⟨gC σ, hmem σ⟩ : F) * ⟨gC τ, hmem τ⟩ =
        algebraMap ℚ F (q σ τ) * ⟨gC (σ * τ), hmem (σ * τ)⟩ := Subtype.ext (hq σ τ)
    show ψ _ * ψ _ = _ * ψ _
    rw [← map_mul, hF, map_mul, AlgHom.commutes]
    congr 1
    simp only [q, map_div₀, map_intCast]
  · intro σ k hk
    exact congrArg ψ (Subtype.ext (hgcos σ k hk))
  · intro k hk
    show ψ _ = 1
    rw [← map_one ψ]
    exact congrArg ψ (Subtype.ext (hg1 k hk))
  · intro σ h1
    have hF : (⟨gC σ, hmem σ⟩ : F) = 1 := ψ.toRingHom.injective (h1.trans (map_one ψ).symm)
    have hg : gC σ = 1 := congrArg Subtype.val hF
    have h2 := (div_eq_one_iff_eq (ha0' σ)).mp hg
    exact h2

set_option maxHeartbeats 1000000 in
/-- **`TateBridgeK` from the five glue pieces, with `ScalarTransferK` (proved)**: unram-tate's
`tateBridge_of_pieces` (proof copied verbatim up to the final `refine`), plus the kernel-field
clause. -/
theorem tateBridgeK_of_piecesK (hP : TatePoints) (hE : EndBaseChange) (hS : ScalarTransferK)
    (hC : TateCont) (hR : ResQEmbedding) : LGKerWild.TateBridgeK := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank ℓ _
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, -⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(hE K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := hP L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gam, hgam0, hgamc, hgamcos, hgam1, hgamK⟩ := hS L' ℓ a β ε n d hd hna hβe ha0
    (fun σ k hk => ⟨(haL σ k (hLL'G k hk)).2.1, by
      have := hβe σ k
      rw [hβL' k hk, _root_.mul_one, eps_right_one L ε hεc hinf h11 σ k (hLL'G k hk),
        _root_.one_mul] at this
      exact this.symm⟩)
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  -- notation
  let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
  let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
  have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
    show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
    group
  let m' : GQ → AddMonoid.End (PtQ L A) := m
  let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
  let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
    ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
  let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
  let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
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
    intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
  have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
    intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
  have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
  -- `G_{L'}` is normal
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hres : ∀ σ : Field.absoluteGaloisGroup L',
      cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
    intro σ
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
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
    simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
  refine ⟨Tm, c', c', a', β', uu, ⟨_hdim, _hrank, hT, ha, hβ, hβ0,
    fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
    fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩, ?_⟩
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
  -- the kernel-field clause (lg-kerwild)
  intro g hgL hg1
  have hgL' : g ∈ GQL L := mem_GQL.mpr (fun x hx => hgL x hx)
  have hnormL : (L.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hcjL : cj g ∈ GQL L := hnormL.conj_mem _ hgL' h
  have haone : a (cj g) = 1 := (haL 1 (cj g) hcjL).1
  have hβC : (β (cj g) : ℂ) = 1 := by
    rw [hgamK (cj g) hg1, haone, Complex.ofReal_one]
  have hβ1 : β (cj g) = 1 := Units.ext (by rw [hβC, Units.val_one])
  have hcjL' : cj g ∈ GQL L' := (hL' (cj g)).mpr ⟨hcjL, hβ1⟩
  have hgL'' : g ∈ L'.fixingSubgroup := by
    have h4 : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ ∈ L'.fixingSubgroup := hnorm.conj_mem _ hcjL' h⁻¹
    have e : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g := by group
    rwa [e] at h4
  rw [RQ.resQ_range L']
  exact hgL''

/-- **`TateBridgeK` from the leaf I3.M0 alone (proved)**: g0-mod-field's `TateBridge` with the
kernel-field clause `KerWild L' β' L` in its output (lg-kerwild's correction of local-glue finding
G8), by unram-tate's construction (`tatePoints`, `endBaseChange`, `tateCont_of_tateModuleFree`,
`resQEmbedding`) and `scalarTransferK`. -/
theorem tateBridgeK_of_tateModuleFree (hT : PkgI3.TateModuleFree) : LGKerWild.TateBridgeK :=
  tateBridgeK_of_piecesK tatePoints endBaseChange scalarTransferK
    (tateCont_of_tateModuleFree hT) resQEmbedding

end UnramTate

/-- **`TateBridge35K` from I3.M0 and frob-trace's `AlgFrobRed` (proved)**: frob-trace's
`tateBridge35_of_algFrobRed` composed with `tateBridge35K_of_35`. -/
theorem LGKerWild.tateBridge35K_of_algFrobRed (hT : PkgI3.TateModuleFree)
    (hR : FrobTrace.AlgFrobRed) : LGKerWild.TateBridge35K :=
  LGKerWild.tateBridge35K_of_35 (FrobTrace.tateBridge35_of_algFrobRed hT hR)

end LGTateBridgeKSec

#print axioms UnramTate.scalarTransferK
#print axioms UnramTate.tateBridgeK_of_piecesK
#print axioms UnramTate.tateBridgeK_of_tateModuleFree
#print axioms LGKerWild.tateBridge35K_of_algFrobRed
