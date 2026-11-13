import Prefix2

/-! # g8-tate, part 4: `OnL` for the canonical operators of unram-tate / linked-tate

`tmOf hLL' A Θ h m ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` (linked-tate's `tmOf`, unram-tate's
construction) is, on `G_L` (through `resQ L`), the Tate action of the model `A/L`, transported by an
isomorphism `ψ` (`onL_canon`, proved). `ψ⁻¹ = opV(m_x) ∘ V(Θ ∘ trPt φ₁)`, where `φ₁ : L̄ ≅ ℚ̄` is an
`L`-isomorphism, `g₁ = φ₁ ∘ (Mathlib's embedding ℚ̄ → L̄)` and `x = h g₁⁻¹`: `trPt φ₁` carries `σ_L` to
`g₁ resQ(σ_L) g₁⁻¹`, and `m_x` (an isogeny on points: `m_x m_{x⁻¹} = (n/d)·1`) intertwines that with
`h resQ(σ_L) h⁻¹` (the descent datum's `m(σk) = m σ m k`, `m(kσ) = m k m σ` on `G_L`).
Only the clauses of g0-mod-field's `DescentDatum` are used. -/

noncomputable section

namespace G8Tate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open G0ModField UnramTate

/-! ### The Tate functor across groups -/

section VX

variable {K K' : Type} [Field K] [Field K'] (A : PkgI3.AbVar K) (B : PkgI3.AbVar K')
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(Ξ)` for an additive map `Ξ : A(K̄) → B(K̄')`. -/
def VX (Ξ : PtA A →+ PtA B) : GaloisCopy.Vb A ℓ →ₗ[PadicAlgCl ℓ] GaloisCopy.Vb B ℓ :=
  ((PkgI3.Tate.map (ℓ := ℓ) Ξ).baseChange ℚ_[ℓ]).baseChange (PadicAlgCl ℓ)

theorem tateMapX_comp {M N R : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup R]
    (φ : N →+ R) (ψ : M →+ N) :
    PkgI3.Tate.map (ℓ := ℓ) (φ.comp ψ) = (PkgI3.Tate.map (ℓ := ℓ) φ).comp (PkgI3.Tate.map ψ) := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

theorem tateMapX_id {M : Type*} [AddCommGroup M] :
    PkgI3.Tate.map (ℓ := ℓ) (AddMonoidHom.id M) = LinearMap.id := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

/-- `opV(Ξ f Ξ⁻¹) = V(Ξ) opV(f) V(Ξ)⁻¹` (proved). -/
theorem opV_conjE (Ξ : PtA A ≃+ PtA B) (f : AddMonoid.End (PtA A)) :
    opV B ℓ (conjE Ξ f) =
      VX A B ℓ Ξ.toAddMonoidHom ∘ₗ opV A ℓ f ∘ₗ VX B A ℓ Ξ.symm.toAddMonoidHom := by
  have e : PkgI3.Tate.map (ℓ := ℓ) (conjE Ξ f) = (PkgI3.Tate.map (ℓ := ℓ) Ξ.toAddMonoidHom).comp
      ((PkgI3.Tate.map (ℓ := ℓ) (f : PtA A →+ PtA A)).comp
        (PkgI3.Tate.map (ℓ := ℓ) Ξ.symm.toAddMonoidHom)) := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl
  unfold opV VX
  rw [e, LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.baseChange_comp,
    LinearMap.baseChange_comp]

theorem VX_comp_symm (Ξ : PtA A ≃+ PtA B) :
    VX A B ℓ Ξ.toAddMonoidHom ∘ₗ VX B A ℓ Ξ.symm.toAddMonoidHom = LinearMap.id := by
  unfold VX
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← tateMapX_comp]
  have : Ξ.toAddMonoidHom.comp Ξ.symm.toAddMonoidHom = AddMonoidHom.id _ := by
    ext x; simp
  rw [this, tateMapX_id, LinearMap.baseChange_id, LinearMap.baseChange_id]

/-- `V(Ξ)` as a linear isomorphism. -/
def VXe (Ξ : PtA A ≃+ PtA B) : GaloisCopy.Vb A ℓ ≃ₗ[PadicAlgCl ℓ] GaloisCopy.Vb B ℓ :=
  LinearEquiv.ofLinear (VX A B ℓ Ξ.toAddMonoidHom) (VX B A ℓ Ξ.symm.toAddMonoidHom)
    (VX_comp_symm A B ℓ Ξ) (by simpa using VX_comp_symm B A ℓ Ξ.symm)

end VX

/-- An endomorphism with `f g = λ·1`, `g f = μ·1` (`λ, μ ≠ 0`) is a linear isomorphism (proved). -/
theorem exists_equiv_of_quasiInv {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (f g : Module.End E V) (lam mu : E) (hl : lam ≠ 0) (hm : mu ≠ 0)
    (h1 : f * g = lam • 1) (h2 : g * f = mu • 1) :
    ∃ e : V ≃ₗ[E] V, e.toLinearMap = f ∧ e.symm.toLinearMap = lam⁻¹ • g := by
  have hr : f * (lam⁻¹ • g) = 1 := by rw [mul_smul_comm, h1, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hlf : (mu⁻¹ • g) * f = 1 := by rw [smul_mul_assoc, h2, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have heq : mu⁻¹ • g = lam⁻¹ • g := by
    calc mu⁻¹ • g = (mu⁻¹ • g) * (f * (lam⁻¹ • g)) := by rw [hr, _root_.mul_one]
      _ = ((mu⁻¹ • g) * f) * (lam⁻¹ • g) := by rw [_root_.mul_assoc]
      _ = lam⁻¹ • g := by rw [hlf, _root_.one_mul]
  rw [heq] at hlf
  exact ⟨LinearEquiv.ofLinear f (lam⁻¹ • g) hr hlf, rfl, rfl⟩

/-- `m 1 = id` for a descent datum (proved: `m 1 = m 1 ∘ m 1` and `m 1` is onto). -/
theorem m_one {L : IF} {A : PkgI3.AbVar L} (m : GQ → (PtQ L A →+ PtQ L A))
    (hmLL : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (hmsf : ∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) :
    m 1 = AddMonoidHom.id _ := by
  have h1 := (hmLL 1 1 (one_mem _)).1
  rw [_root_.one_mul] at h1
  refine AddMonoidHom.ext fun y => ?_
  obtain ⟨z, rfl⟩ := (hmsf 1).1 y
  show m 1 (m 1 z) = m 1 z
  exact (DFunLike.congr_fun h1 z).symm

set_option maxHeartbeats 1000000 in
/-- **`OnL` for the canonical operators (proved).** For a descent datum `m` (the clauses of
`DescentDatum` used: `m = Galois action` on `G_L`, `m(σk) = m σ m k`, `m(kσ) = m k m σ`, `m σ` onto,
`d • m σ m τ = n • m(στ)` with `n, d ≠ 0`), any transport `Θ`, `h ∈ G_ℚ`, and scalars `aℓ` equal to
`1` on `G_L`: `OnL L A (tmOf hLL' A Θ h m ℓ) aℓ ψ` for some `ψ`. -/
theorem onL_canon {L L' : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L] [FiniteDimensional ℚ L']
    (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (m : GQ → (PtQ L A →+ PtQ L A)) (n d : GQ → GQ → ℤ)
    (hmL : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hmLL : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (hmsf : ∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite)
    (hn : ∀ σ τ, n σ τ ≠ 0) (hd : ∀ σ τ, d σ τ ≠ 0)
    (hnd : ∀ σ τ, d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ))
    (ℓ : ℕ) [Fact ℓ.Prime] (aℓ : PkgI4.GQ → PadicAlgCl ℓ) (ha : ∀ k ∈ GQL L, aℓ k = 1) :
    ∃ ψ, G8Object.OnL L A (tmOf hLL' A Θ h m ℓ) aℓ ψ := by
  letI hNF : NumberField L := numberField_of_fd L
  haveI : Algebra.IsAlgebraic L Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI : IsAlgClosure L Qbar := ⟨inferInstance, inferInstance⟩
  let φ₁ : AlgebraicClosure L ≃ₐ[L] Qbar := IsAlgClosure.equiv L (AlgebraicClosure L) Qbar
  obtain ⟨g0, hcomm⟩ := resQ_comm' L
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L := g0.toRatAlgHom
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    haveI : Algebra.IsAlgebraic L (AlgebraicClosure L) := AlgebraicClosure.isAlgebraic L
    exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L) := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L) := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ge : Qbar ≃+* AlgebraicClosure L := RingEquiv.ofBijective g0 hgbij
  let hR : Qbar ≃+* Qbar := ge.trans φ₁.toRingEquiv
  let g₁ : PkgI4.GQ := AlgEquiv.ofRingEquiv (f := hR) (fun q => by
    rw [eq_ratCast (algebraMap ℚ Qbar) q, map_ratCast])
  have hg₁ : ∀ y, g₁ y = φ₁ (g0 y) := fun _ => rfl
  have hnorm : (L.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  -- the isogeny `m_x`, `x = h g₁⁻¹`, on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`
  let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
  let m' : GQ → AddMonoid.End (PtQ L A) := m
  let hG : GQ := h
  let g₁G : GQ := g₁
  let x : GQ := hG * g₁G⁻¹
  have hm1 : m' 1 = 1 := m_one m hmLL hmsf
  have hRinv : ∀ y z : GQ, R (m' y) * R (m' z) =
      ((n y z : PadicAlgCl ℓ) / (d y z : PadicAlgCl ℓ)) • R (m' (y * z)) := by
    intro y z
    have h0 : d y z • (m' y * m' z) = n y z • m' (y * z) := hnd y z
    have h1 := congrArg R h0
    rw [map_zsmul, map_zsmul, map_mul] at h1
    have h2 : (d y z : PadicAlgCl ℓ) • (R (m' y) * R (m' z)) =
        (n y z : PadicAlgCl ℓ) • R (m' (y * z)) :=
      (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
        (h1.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
    have hd0 : (d y z : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
    rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hne : ∀ y z : GQ, ((n y z : PadicAlgCl ℓ) / (d y z : PadicAlgCl ℓ)) ≠ 0 := fun y z =>
    div_ne_zero (Int.cast_ne_zero.mpr (hn _ _)) (Int.cast_ne_zero.mpr (hd _ _))
  obtain ⟨Ex, hEx, -⟩ := exists_equiv_of_quasiInv (R (m' x)) (R (m' x⁻¹)) _ _ (hne x x⁻¹)
    (hne x⁻¹ x) (by rw [hRinv, mul_inv_cancel, hm1, map_one])
    (by rw [hRinv, inv_mul_cancel, hm1, map_one])
  -- the points transport `A(L̄) ≅ A(ℚ̄) ≅ A_{L'}(\bar L')`
  let Ξ : PtA A ≃+ PtQ L A := (trPt A φ₁).toAdditive
  let Ξ' : PtA A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) := Ξ.trans Θ
  let E := (VXe A (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ Ξ').trans Ex
  refine ⟨E.symm, fun σL => ?_⟩
  set k₀ : GQ := @G0Galois.resQ L _ (numberField_of_fd L) σL with hk₀
  have hk₀L : k₀ ∈ GQL L := by
    show k₀ ∈ L.fixingSubgroup
    rw [← resQ_range L]; exact ⟨σL, rfl⟩
  refine ⟨ha k₀ hk₀L, ?_⟩
  -- `k = g₁ k₀ g₁⁻¹` acts on `ℚ̄` as `φ₁ σL φ₁⁻¹`
  set k : GQ := g₁G * k₀ * g₁G⁻¹ with hk
  have hkL : k ∈ GQL L := hnorm.conj_mem _ hk₀L g₁G
  let σ₂ : Qbar ≃ₐ[L] Qbar :=
    AlgEquiv.ofRingEquiv (f := (act k).toRingEquiv) (fun y => (mem_GQL.mp hkL) y y.2)
  have hkey : ∀ z, σ₂ (φ₁ z) = φ₁ (actK σL z) := by
    intro z
    have hinv : g₁⁻¹ (φ₁ z) = ge.symm z := by
      apply g₁.injective
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hg₁]
      show φ₁ z = φ₁ (g0 (ge.symm z))
      rw [show g0 (ge.symm z) = z from ge.apply_symm_apply z]
    have hres : (@GaloisCopy.resQ L _ hNF σL) (ge.symm z) = ge.symm (actK σL z) := by
      apply ge.injective
      rw [ge.apply_symm_apply]
      have := hcomm σL (ge.symm z)
      rw [show g0 (ge.symm z) = z from ge.apply_symm_apply z] at this
      exact this
    show g₁ ((@GaloisCopy.resQ L _ hNF σL) (g₁⁻¹ (φ₁ z))) = φ₁ (actK σL z)
    rw [hinv, hres, hg₁]
    show φ₁ (g0 (ge.symm (actK σL z))) = φ₁ (actK σL z)
    rw [show g0 (ge.symm (actK σL z)) = actK σL z from ge.apply_symm_apply (actK σL z)]
  have hmk : m' k = MonoidHom.toAdditive (A.galAct σ₂) := hmL k σ₂ (fun _ => rfl)
  -- `m_x ∘ m_k = m_{h k₀ h⁻¹} ∘ m_x`
  have hc : hG * k₀ * hG⁻¹ ∈ GQL L := hnorm.conj_mem _ hk₀L hG
  have hxk : x * k = (hG * k₀ * hG⁻¹) * x := by
    simp only [x, hk]; group
  have hint : m' x * m' k = m' (hG * k₀ * hG⁻¹) * m' x := by
    have e1 := (hmLL x k hkL).1
    have e2 := (hmLL x (hG * k₀ * hG⁻¹) hc).2
    rw [hxk] at e1
    exact e1.symm.trans e2
  -- `R(m_k) = V(Ξ') tate(σL) V(Ξ')⁻¹`
  have hRk : R (m' k) = VX A (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
      Ξ'.toAddMonoidHom ∘ₗ GaloisCopy.tate A ℓ σL ∘ₗ
      VX (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) A ℓ Ξ'.symm.toAddMonoidHom := by
    rw [tate_eq_opV]
    refine Eq.trans ?_ (opV_conjE A (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ Ξ'
      (MonoidHom.toAdditive (A.galAct (actK σL))))
    show opV _ ℓ (conjE Θ (m' k)) = _
    congr 1
    refine DFunLike.ext _ _ fun y => ?_
    show Θ (m' k (Θ.symm y)) =
      Θ (Ξ (MonoidHom.toAdditive (A.galAct (actK σL)) (Ξ.symm (Θ.symm y))))
    congr 1
    rw [hmk]
    show MonoidHom.toAdditive (A.galAct σ₂) (Θ.symm y) =
      Additive.ofMul (trPt A φ₁ (A.galAct (actK σL)
        ((trPt A φ₁).symm (Additive.toMul (Θ.symm y)))))
    rw [trPt_galAct A φ₁ (actK σL) σ₂ hkey, MulEquiv.apply_symm_apply]
    rfl
  -- assemble: `tmOf(k₀) = E tate(σL) E⁻¹`
  have htm : tmOf hLL' A Θ h m ℓ k₀ = R (m' (hG * k₀ * hG⁻¹)) := rfl
  apply LinearMap.ext
  intro v
  rw [htm]
  show R (m' (hG * k₀ * hG⁻¹)) v = E (GaloisCopy.tate A ℓ σL (E.symm v))
  have hv : v = Ex (Ex.symm v) := (Ex.apply_symm_apply v).symm
  conv_lhs => rw [hv]
  have hExv : ∀ w, Ex w = R (m' x) w := fun w => by rw [← hEx]; rfl
  rw [hExv, ← Module.End.mul_apply, ← map_mul, ← hint, map_mul, Module.End.mul_apply, hRk]
  show R (m' x) (VX _ _ ℓ Ξ'.toAddMonoidHom (GaloisCopy.tate A ℓ σL
      (VX _ A ℓ Ξ'.symm.toAddMonoidHom (Ex.symm v)))) = _
  rw [← hExv]
  rfl

end G8Tate

end

#print axioms G8Tate.opV_conjE
#print axioms G8Tate.exists_equiv_of_quasiInv
#print axioms G8Tate.onL_canon
