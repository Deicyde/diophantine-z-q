/-!
# g8-tate: the Tate functor on G7's descent datum on `G_L` (`OnL`) for frob-trace's operators

Appended (by `build_dev.sh` / `build.sh`) to verbatim copies of alg-frob-red's `AlgFrobRed.lean`
(which contains frob-trace's `FrobTrace.lean`), g0-mod-galois' `G0Galois` definitions and
g8-object's `G8Object.OnL`.

frob-trace's operators are `Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` with scalars
`aQ g = βQ g / γQ(hgh⁻¹)`. On `G_L` (through `resQ L`), they are conjugate to the Tate action of
the model `A/L`:
* `Λ = trPt κ : A(L̄) ≅ A(ℚ̄)` for an `L`-isomorphism `κ : L̄ ≅ ℚ̄`, and `t = κ ∘ g_L ∈ G_ℚ`
  (`g_L : ℚ̄ → L̄` the embedding chosen by `resQ L`), so `Λ ∘ σ_L = m_{tgt⁻¹} ∘ Λ` for
  `g = resQ L σ_L`;
* `X = Θ ∘ m_{ht⁻¹} ∘ Λ : A(L̄) → A_{L'}(L̄')`, an isogeny on points, with quasi-inverse
  `Λ⁻¹ ∘ m_{th⁻¹} ∘ Θ⁻¹` (`d·m_σ m_τ = n·m_{στ}`, `m₁ = 1`);
* `m_{hgh⁻¹} m_{ht⁻¹} = m_{hgt⁻¹} = m_{ht⁻¹} m_{tgt⁻¹}` (DescentDatum's coset clauses, both
  `hgh⁻¹` and `tgt⁻¹` lie in `G_L`, a normal subgroup);
* `ψ⁻¹ = ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(X)` is bijective and intertwines.
The scalar clause: `a = 1` on `G_L` and `β(hgh⁻¹) = β(g)` (`ε` is trivial as soon as one argument
lies in `G_L`), so `aQ = 1` on `G_L`.
No `sorry`, no `axiom`.
-/

noncomputable section

namespace G8Tate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField
open UnramTate

/-! ## The Tate functor on additive maps between point groups -/

section OpW

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(M)`. -/
abbrev Wb (M : Type*) [AddCommGroup M] : Type _ :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ M))

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

/-- `ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(f)` for an additive map `f : M → N` (unram-tate's `opV` for `M ≠ N`). -/
def opW (f : M →+ N) : Wb ℓ M →ₗ[PadicAlgCl ℓ] Wb ℓ N :=
  ((PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]).baseChange (PadicAlgCl ℓ)

theorem opW_comp (f : N →+ P) (g : M →+ N) :
    opW ℓ (f.comp g) = opW ℓ f ∘ₗ opW ℓ g := by
  have h : PkgI3.Tate.map (ℓ := ℓ) (f.comp g) =
      (PkgI3.Tate.map (ℓ := ℓ) f) ∘ₗ (PkgI3.Tate.map (ℓ := ℓ) g) := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl
  unfold opW
  rw [h, LinearMap.baseChange_comp, LinearMap.baseChange_comp]

theorem opW_id : opW ℓ (AddMonoidHom.id M) = LinearMap.id := by
  have h : PkgI3.Tate.map (ℓ := ℓ) (AddMonoidHom.id M) = LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl
  unfold opW
  rw [h, LinearMap.baseChange_id, LinearMap.baseChange_id]

theorem opW_add (f g : M →+ N) : opW ℓ (f + g) = opW ℓ f + opW ℓ g := by
  have h : PkgI3.Tate.map (ℓ := ℓ) (f + g) =
      PkgI3.Tate.map (ℓ := ℓ) f + PkgI3.Tate.map (ℓ := ℓ) g := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl
  unfold opW
  rw [h, LinearMap.baseChange_add, LinearMap.baseChange_add]

/-- `opW` as an additive map. -/
def opWHom : (M →+ N) →+ (Wb ℓ M →ₗ[PadicAlgCl ℓ] Wb ℓ N) :=
  AddMonoidHom.mk' (opW ℓ) (opW_add ℓ)

theorem opW_zsmul (z : ℤ) (f : M →+ N) :
    opW ℓ (z • f) = (z : PadicAlgCl ℓ) • opW ℓ f := by
  have h := map_zsmul (opWHom ℓ (M := M) (N := N)) z f
  rw [show opWHom ℓ (z • f) = opW ℓ (z • f) from rfl, show opWHom ℓ f = opW ℓ f from rfl] at h
  rw [h]
  exact (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) z _).symm

/-- An additive map with a quasi-inverse on both sides (`d • f ∘ g = n • 1`,
`d' • g ∘ f = n' • 1`, `n, d, n', d' ≠ 0`) gives a bijection on `ℚ̄_ℓ ⊗ V_ℓ`. -/
theorem opW_bijective (f : M →+ N) (g : N →+ M) (n d n' d' : ℤ) (hn : n ≠ 0) (hd : d ≠ 0)
    (hn' : n' ≠ 0) (hd' : d' ≠ 0)
    (hfg : d • f.comp g = n • AddMonoidHom.id N) (hgf : d' • g.comp f = n' • AddMonoidHom.id M) :
    Function.Bijective (opW ℓ f) := by
  have h1 : (d : PadicAlgCl ℓ) • (opW ℓ f ∘ₗ opW ℓ g) = (n : PadicAlgCl ℓ) • LinearMap.id := by
    rw [← opW_comp, ← opW_zsmul, hfg, opW_zsmul, opW_id]
  have h2 : (d' : PadicAlgCl ℓ) • (opW ℓ g ∘ₗ opW ℓ f) = (n' : PadicAlgCl ℓ) • LinearMap.id := by
    rw [← opW_comp, ← opW_zsmul, hgf, opW_zsmul, opW_id]
  have hn0 : (n : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hd0 : (d : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hn0' : (n' : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr hn'
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have := congrArg (fun F => F x - F y) h2
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply, hxy, sub_self,
      ← smul_sub] at this
    have h0 := (smul_eq_zero.mp this.symm).resolve_left hn0'
    exact sub_eq_zero.mp h0
  · refine ⟨((d : PadicAlgCl ℓ) / n) • opW ℓ g y, ?_⟩
    have := congrArg (fun F => F y) h1
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [map_smul, div_eq_inv_mul, ← smul_smul, this, smul_smul, inv_mul_cancel₀ hn0, one_smul]

end OpW

/-! ## `OnL` for `opV(Θ ∘ m_{h·h⁻¹} ∘ Θ⁻¹)` -/

/-- **The Tate functor on G7's descent datum on `G_L` (proved).** For an abelian variety `A` over
a finite Galois `L ⊆ ℚ̄`, additive maps `m_σ` of `A(ℚ̄)` with three of `DescentDatum`'s clauses
(the Galois action on `G_L`, the `G_L`-coset clauses, `d·m_σ m_τ = n·m_{στ}`), any additive
bijection `Θ : A(ℚ̄) ≅ A'(K̄)` and any `h ∈ G_ℚ`: there is a `ℚ̄_ℓ`-isomorphism
`ψ : ℚ̄_ℓ ⊗ V_ℓ(A') ≅ ℚ̄_ℓ ⊗ V_ℓ(A)` with `opV(Θ ∘ m_{h·resQ(σ_L)·h⁻¹} ∘ Θ⁻¹) = ψ⁻¹ ∘ ρ_{A,ℓ}(σ_L) ∘ ψ`
for every `σ_L ∈ G_L`. -/
theorem onL_exists {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    {K : Type} [Field K] (A' : PkgI3.AbVar K) (Θ : PtQ L A ≃+ PtA A') (h : PkgI4.GQ)
    (m : GQ → (PtQ L A →+ PtQ L A))
    (hmL : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hmLL : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧
        m (k * σ) = (m k).comp (m σ))
    (hmc : ∀ σ τ, ∃ n d : ℤ, n ≠ 0 ∧ d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ))
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ ψ : GaloisCopy.Vb A' ℓ ≃ₗ[PadicAlgCl ℓ] G0Galois.Vb A ℓ,
      ∀ σL : Field.absoluteGaloisGroup L,
        opV A' ℓ (conjE Θ (m (h * @G0Galois.resQ L _ (numberField_of_fd L) σL * h⁻¹))) =
          ψ.symm.toLinearMap ∘ₗ G0Galois.tate A ℓ σL ∘ₗ ψ.toLinearMap := by
  haveI hNF : NumberField L := numberField_of_fd L
  -- `κ : L̄ ≃ₐ[L] ℚ̄`
  haveI : Algebra.IsAlgebraic L Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI : IsAlgClosure L Qbar := ⟨inferInstance, inferInstance⟩
  let κ : AlgebraicClosure L ≃ₐ[L] Qbar := IsAlgClosure.equiv L (AlgebraicClosure L) Qbar
  -- `t = κ ∘ g_L`
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
  let tR : Qbar ≃+* Qbar := ge.trans κ.toRingEquiv
  let t : PkgI4.GQ := AlgEquiv.ofRingEquiv (f := tR) (fun q => by
    rw [eq_ratCast (algebraMap ℚ Qbar) q, map_ratCast])
  have ht : ∀ y, t y = κ (g0 y) := fun _ => rfl
  have htinv : ∀ z, t⁻¹ (κ z) = ge.symm z := by
    intro z
    apply t.injective
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, ht]
    show κ z = κ (g0 (ge.symm z))
    rw [show g0 (ge.symm z) = z from ge.apply_symm_apply z]
  -- the transport `Λ : A(L̄) ≅ A(ℚ̄)`
  let Λ : PtA A ≃+ PtQ L A := (trPt A κ).toAdditive
  -- `G_L` is normal
  have hnorm : (L.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hresL : ∀ σL : Field.absoluteGaloisGroup L,
      (@G0Galois.resQ L _ hNF σL) ∈ GQL L := by
    intro σL
    have : (@GaloisCopy.resQ L _ hNF σL) ∈ L.fixingSubgroup := by
      rw [← resQRange L]; exact ⟨σL, rfl⟩
    exact this
  -- `m₁ = 1`
  have hm1 : m 1 = AddMonoidHom.id _ := by
    rw [hmL 1 1 (fun x => rfl)]
    refine DFunLike.ext _ _ fun x => ?_
    show Additive.ofMul (PkgI3.AbVar.galHom (1 : Qbar ≃ₐ[L] Qbar) ≫ Additive.toMul x) = x
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
    rfl
  -- the isogeny `X` and its quasi-inverse `Y`
  let w : GQ := h * t⁻¹
  let X : PtA A →+ PtA A' :=
    Θ.toAddMonoidHom.comp ((m w).comp Λ.toAddMonoidHom)
  let Y : PtA A' →+ PtA A :=
    Λ.symm.toAddMonoidHom.comp ((m w⁻¹).comp Θ.symm.toAddMonoidHom)
  obtain ⟨n1, d1, hn1, hd1, h1⟩ := hmc w w⁻¹
  obtain ⟨n2, d2, hn2, hd2, h2⟩ := hmc w⁻¹ w
  rw [mul_inv_cancel, hm1] at h1
  rw [inv_mul_cancel, hm1] at h2
  have hXY : d1 • X.comp Y = n1 • AddMonoidHom.id (PtA A') := by
    refine DFunLike.ext _ _ fun x => ?_
    have := congrArg (fun F : PtQ L A →+ PtQ L A => F (Θ.symm x)) h1
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at this ⊢
    show d1 • Θ (m w (Λ (Λ.symm (m w⁻¹ (Θ.symm x))))) = n1 • x
    rw [AddEquiv.apply_symm_apply, ← map_zsmul, this, map_zsmul, AddEquiv.apply_symm_apply]
  have hYX : d2 • Y.comp X = n2 • AddMonoidHom.id (PtA A) := by
    refine DFunLike.ext _ _ fun x => ?_
    have := congrArg (fun F : PtQ L A →+ PtQ L A => F (Λ x)) h2
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at this ⊢
    show d2 • Λ.symm (m w⁻¹ (Θ.symm (Θ (m w (Λ x))))) = n2 • x
    rw [AddEquiv.symm_apply_apply, ← map_zsmul, this, map_zsmul, AddEquiv.symm_apply_apply]
  have hbij := opW_bijective ℓ X Y n1 d1 n2 d2 hn1 hd1 hn2 hd2 hXY hYX
  let ψs : G0Galois.Vb A ℓ ≃ₗ[PadicAlgCl ℓ] GaloisCopy.Vb A' ℓ :=
    LinearEquiv.ofBijective (opW ℓ X) hbij
  refine ⟨ψs.symm, fun σL => ?_⟩
  -- the point-level identity
  let gL := @G0Galois.resQ L _ hNF σL
  have hgL := hresL σL
  let k1 : GQ := h * gL * h⁻¹
  let k2 : GQ := t * gL * t⁻¹
  have hk1 : k1 ∈ GQL L := hnorm.conj_mem _ hgL h
  have hk2 : k2 ∈ GQL L := hnorm.conj_mem _ hgL t
  let σ' : Qbar ≃ₐ[L] Qbar :=
    AlgEquiv.ofRingEquiv (f := (act k2).toRingEquiv) (fun x => (mem_GQL.mp hk2) x x.2)
  have hkey : ∀ z, σ' (κ z) = κ ((actK σL).restrictScalars L z) := by
    intro z
    show t (gL (t⁻¹ (κ z))) = κ (actK σL z)
    have hres : gL (ge.symm z) = ge.symm (actK σL z) := by
      apply ge.injective
      rw [ge.apply_symm_apply]
      have := hcomm σL (ge.symm z)
      rw [show g0 (ge.symm z) = z from ge.apply_symm_apply z] at this
      exact this
    rw [htinv, hres, ht]
    show κ (g0 (ge.symm (actK σL z))) = κ (actK σL z)
    rw [show g0 (ge.symm (actK σL z)) = actK σL z from ge.apply_symm_apply (actK σL z)]
  have hΛ : ∀ x : PtA A, Λ (MonoidHom.toAdditive (A.galAct σL) x) = m k2 (Λ x) := by
    intro x
    rw [hmL k2 σ' (fun _ => rfl)]
    show Additive.ofMul (trPt A κ (A.galAct ((actK σL).restrictScalars L) (Additive.toMul x))) =
      Additive.ofMul (A.galAct σ' (trPt A κ (Additive.toMul x)))
    rw [trPt_galAct A κ ((actK σL).restrictScalars L) σ' hkey]
  have e1 := (hmLL w k1 hk1).2
  have e2 := (hmLL w k2 hk2).1
  have e3 : k1 * w = w * k2 := by
    show h * gL * h⁻¹ * (h * t⁻¹) = h * t⁻¹ * (t * gL * t⁻¹)
    group
  have hpt : (conjE Θ (m k1)).comp X = X.comp (MonoidHom.toAdditive (A.galAct σL)) := by
    refine DFunLike.ext _ _ fun x => ?_
    show Θ (m k1 (Θ.symm (Θ (m w (Λ x))))) =
      Θ (m w (Λ (MonoidHom.toAdditive (A.galAct σL) x)))
    rw [AddEquiv.symm_apply_apply, hΛ]
    congr 1
    calc m k1 (m w (Λ x)) = ((m k1).comp (m w)) (Λ x) := rfl
      _ = m (k1 * w) (Λ x) := by rw [← e1]
      _ = m (w * k2) (Λ x) := by rw [e3]
      _ = ((m w).comp (m k2)) (Λ x) := by rw [e2]
      _ = m w (m k2 (Λ x)) := rfl
  have hop : opV A' ℓ (conjE Θ (m k1)) ∘ₗ opW ℓ X =
      opW ℓ X ∘ₗ G0Galois.tate A ℓ σL := by
    calc opV A' ℓ (conjE Θ (m k1)) ∘ₗ opW ℓ X = opW ℓ ((conjE Θ (m k1)).comp X) :=
          (opW_comp ℓ _ _).symm
      _ = opW ℓ (X.comp (MonoidHom.toAdditive (A.galAct σL))) := by rw [hpt]
      _ = opW ℓ X ∘ₗ G0Galois.tate A ℓ σL := opW_comp ℓ _ _
  show opV A' ℓ (conjE Θ (m k1)) = _
  apply LinearMap.ext
  intro v
  have := congrArg (fun F => F (ψs.symm v)) hop
  simp only [LinearMap.comp_apply] at this
  show _ = ψs.symm.symm (G0Galois.tate A ℓ σL (ψs.symm v))
  rw [LinearEquiv.symm_symm]
  show _ = opW ℓ X (G0Galois.tate A ℓ σL (ψs.symm v))
  rw [← this]
  show _ = opV A' ℓ (conjE Θ (m k1)) (ψs (ψs.symm v))
  rw [LinearEquiv.apply_symm_apply]

end G8Tate

end

#print axioms G8Tate.opW_bijective
#print axioms G8Tate.onL_exists
