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

/-! ## `TateBridge35` with the `G_L`-clause `OnL` -/

open FrobTrace
open GlueC10Link (FrobCompare)

/-- **The linked Tate bridge at `ℓ = 3, 5` with the `G_L`-clause (GLUE; g8-object §4.1's
"`TateBridge35` + `OnL`").** The text of g14-trace's `G14Bridge.TateBridge35`, with two more
witnesses `ψ₅, ψ₃` (isomorphisms `ℚ̄_ℓ ⊗ V_ℓ(A_{L'}) ≅ ℚ̄_ℓ ⊗ V_ℓ(A)`) and two more conjuncts: g8-object's
`G8Object.OnL` for `(Tm₅, j₅ ∘ aQ, ψ₅)` and `(Tm₃, j₃ ∘ aQ, ψ₃)`, i.e. through `resQ L`, the scalar
`a` is `1` on `G_L` and `Tm_ℓ` is the Tate action of the model `A/L` transported by `ψ_ℓ`.
Proved below from the leaf I3.M0 and frob-trace's glue `AlgFrobLink` (hence from `AlgFrobRed`,
hence from alg-frob-red's five inputs). -/
def TateBridge35OnL : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (ψ5 : GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 ≃ₗ[PadicAlgCl 5]
        G0Galois.Vb A 5)
      (ψ3 : GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 ≃ₗ[PadicAlgCl 3]
        G0Galois.Vb A 3),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3 ∧
      @G14Bridge.FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      G8Object.OnL L A Tm5 (fun g => j5 (aQ g)) ψ5 ∧
      G8Object.OnL L A Tm3 (fun g => j3 (aQ g)) ψ3

/-- `TateBridge35OnL` contains `TateBridge35` (proved). -/
theorem tateBridge35_of_onL (h : TateBridge35OnL) : G14Bridge.TateBridge35 := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, -, -, h5, h3, hF, hι, -, -⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, hι⟩

/-- **frob-trace's `scalarsQbar` with one more conclusion** (proof copied from
scratch/frob-trace/part_frob.lean L375-491, one clause added): `ιC ∘ γQ = β/a`, which links `γQ`
to `βQ` (`ιC ∘ βQ = β`). -/
theorem scalarsQbarC (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ)
    (hd : ∀ σ τ, d σ τ ≠ 0)
    (hna : ∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ))
    (hβe : ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ))
    (hε2 : ∀ σ τ, ε σ τ ^ 2 = 1)
    (ha0 : ∀ σ, 0 < a σ)
    (hone : ∀ k ∈ GQL L', a k = 1 ∧ β k = 1) :
    ∃ (gamQ βQ : GQ → Qbar) (ιC : Qbar →ₐ[ℚ] ℂ), (∀ σ, gamQ σ ≠ 0) ∧
      (∀ σ τ, gamQ σ * gamQ τ = ((n σ τ : Qbar) / (d σ τ : Qbar)) * gamQ (σ * τ)) ∧
      (∀ k ∈ GQL L', gamQ k = 1) ∧ (∀ σ, ιC (βQ σ) = (β σ : ℂ)) ∧
      (∀ σ, ιC (gamQ σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) := by
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) /
        ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
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
  -- `β` is algebraic: `β(σ)^r = ±1`
  have hpowβ : ∀ (σ : GQ) (k : ℕ), ∃ e : ℂ, e ^ 2 = 1 ∧
      (β σ : ℂ) ^ k = e * (β (σ ^ k) : ℂ) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by norm_num, by rw [pow_zero, pow_zero, (hone 1 (one_mem _)).2]; simp⟩
    | succ k ih =>
      obtain ⟨e, he, hk⟩ := ih
      refine ⟨e * (ε (σ ^ k) σ : ℂ), ?_, ?_⟩
      · rw [mul_pow, he, _root_.one_mul, ← Units.val_pow_eq_pow_val, hε2, Units.val_one]
      · rw [pow_succ, hk, _root_.mul_assoc, ← Units.val_mul, hβe, Units.val_mul, pow_succ]
        ring
  have halgβ : ∀ σ, IsIntegral ℚ (β σ : ℂ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨e, he, ht⟩ := hpowβ σ r
    rw [(hone _ hr).2, Units.val_one, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ (r * 2) - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
    simp [Polynomial.eval₂_sub, pow_mul, ht, he]
  let F : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (Set.range gC ∪ Set.range (fun σ => (β σ : ℂ)))
  haveI : Algebra.IsAlgebraic ℚ F := IntermediateField.isAlgebraic_adjoin (by
    rintro x (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
    · exact halg σ
    · exact halgβ σ)
  let ψ : F →ₐ[ℚ] Qbar := IsAlgClosed.lift
  have hmem : ∀ σ, gC σ ∈ F := fun σ =>
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨σ, rfl⟩)
  have hmemβ : ∀ σ, (β σ : ℂ) ∈ F := fun σ =>
    IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨σ, rfl⟩)
  letI : Algebra F Qbar := ψ.toAlgebra
  haveI : IsScalarTower ℚ F Qbar := IsScalarTower.of_algebraMap_eq (fun x => (ψ.commutes x).symm)
  haveI : Algebra.IsAlgebraic F Qbar :=
    Algebra.IsAlgebraic.extendScalars (R := ℚ) (algebraMap ℚ F).injective
  let ιF : Qbar →ₐ[F] ℂ := IsAlgClosed.lift
  let ιC : Qbar →ₐ[ℚ] ℂ := ιF.restrictScalars ℚ
  have hιψ : ∀ x : F, ιC (ψ x) = x := fun x => ιF.commutes x
  refine ⟨fun σ => ψ ⟨gC σ, hmem σ⟩, fun σ => ψ ⟨β σ, hmemβ σ⟩, ιC, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro k hk
    show ψ _ = 1
    rw [← map_one ψ]
    exact congrArg ψ (Subtype.ext (hg1 k hk))
  · intro σ
    exact hιψ ⟨β σ, hmemβ σ⟩
  · intro σ
    exact hιψ ⟨gC σ, hmem σ⟩

set_option maxHeartbeats 4000000 in
/-- **`TateBridge35OnL` from the leaf I3.M0 and frob-trace's glue `AlgFrobLink` (proved).** The
proof of frob-trace's `tateBridge35_of_algFrobLink` (copied from part_frob.lean L503-688, with
`scalarsQbarC`), plus `OnL`: `onL_exists` for `ψ_ℓ`, and `aQ = βQ/γQ(h·h⁻¹) = 1` on `G_L`. -/
theorem tateBridge35OnL_of_algFrobLink (hT : PkgI3.TateModuleFree)
    (hF : FrobTrace.AlgFrobLink) : TateBridge35OnL := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, hFalg⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(endBaseChange K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := tatePoints L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gamQ, βQ, ιC, hg0, hgc, hg1, hιβ, hιg⟩ :=
    scalarsQbarC L' a β ε n d hd hna hβe hεc.2.1 ha0
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  have hβQ0 : ∀ g, βQ g ≠ 0 := by
    intro g h0
    have := hιβ g
    rw [h0, map_zero] at this
    exact Units.ne_zero _ this.symm
  have hβQ1 : ∀ k, k ∈ GQL L' → βQ k = 1 := by
    intro k hk
    apply ιC.toRingHom.injective
    show ιC (βQ k) = ιC 1
    rw [hιβ, hβL' k hk, map_one, Units.val_one]
  have hC := tateCont_of_tateModuleFree hT
  have hR := resQEmbedding
  -- the operators and `G7Out` at one `ℓ`
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        @GaloisCopy.G7Out L' _ (numberField_of_fd L')
          (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _
          (fun g => opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
            (conjE Θ (m (h * g * h⁻¹)))) c ε'
          (fun g => j (βQ g / gamQ (h * g * h⁻¹))) (fun g => j (βQ g)) uu := by
    intro ℓ _ j
    let gam : GQ → PadicAlgCl ℓ := fun σ => j (gamQ σ)
    have hgam0 : ∀ σ, gam σ ≠ 0 := fun σ => (map_ne_zero j).mpr (hg0 σ)
    have hgamc : ∀ σ τ, gam σ * gam τ =
        ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ) := by
      intro σ τ
      show j _ * j _ = _ * j _
      rw [← map_mul, hgc, map_mul, map_div₀, map_intCast, map_intCast]
    have hgam1 : ∀ k ∈ GQL L', gam k = 1 := by
      intro k hk; show j _ = 1; rw [hg1 k hk, map_one]
    -- (from here: unram-tate's `tateBridge_of_pieces`, with this `gam`)
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
    have hTm : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
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
    have hnorm : (L'.fixingSubgroup).Normal :=
      (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
    have hres : ∀ σ : Field.absoluteGaloisGroup L',
        cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact hnorm.conj_mem _ this h
    have hres0 : ∀ σ : Field.absoluteGaloisGroup L',
        (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact this
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
    have hG7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c' c' a' β' uu := by
      refine ⟨_hdim, _hrank, hTm, ha, hβ, hβ0, fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
        fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
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
        rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hTm ha hβ hβ0, hrho1, Module.End.mul_apply]
      have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
        rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
      rw [he₀.continuousAt_iff, he₀1] at hc
      exact hc
    -- rescale by `φ = j(βQ)/γ(h·h⁻¹)`
    let φ : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (βQ g) / gam (cj g)
    have hφ0 : ∀ g, φ g ≠ 0 := fun g =>
      div_ne_zero ((map_ne_zero j).mpr (hβQ0 g)) (hgam0 _)
    have hφ1 : ∀ σ, φ (@GaloisCopy.resQ L' _ hNF σ) = 1 := by
      intro σ
      show j (βQ _) / gam (cj _) = 1
      rw [hβQ1 _ (hres0 σ), hgam1 _ (hres σ), map_one, div_one]
    refine ⟨c', _, uu, g7Out_rescale _ ℓ Tm c' c' a' β' _ _ φ uu hφ0 hφ1 (fun g => ?_)
      (fun g => ?_) hG7⟩
    · show j (βQ g / gamQ (cj g)) = j (βQ g) / j (gamQ (cj g)) * 1
      rw [map_div₀, _root_.mul_one]
    · show j (βQ g) = j (βQ g) / gam (cj g) * gam (cj g)
      rw [div_mul_cancel₀ _ (hgam0 _)]
  let j5 : Qbar →ₐ[ℚ] PadicAlgCl 5 := IsAlgClosed.lift
  let j3 : Qbar →ₐ[ℚ] PadicAlgCl 3 := IsAlgClosed.lift
  obtain ⟨c5, ε5, u5, h5⟩ := key 5 j5
  obtain ⟨c3, ε3, u3, h3⟩ := key 3 j3
  -- `OnL` (this task)
  have hmc' : ∀ σ τ, ∃ n d : ℤ, n ≠ 0 ∧ d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ) :=
    fun σ τ => ⟨n σ τ, d σ τ, hn σ τ, hd σ τ, hnd σ τ⟩
  obtain ⟨ψ5, hψ5⟩ := onL_exists A (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Θ h m hmL
    hmLL hmc' 5
  obtain ⟨ψ3, hψ3⟩ := onL_exists A (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Θ h m hmL
    hmLL hmc' 3
  have hεN := inflatedNormalized_of L ε hεc hinf h11
  have hnormL : (L.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have haQ : ∀ σL : Field.absoluteGaloisGroup L,
      βQ (@G0Galois.resQ L _ (numberField_of_fd L) σL) /
        gamQ (h * @G0Galois.resQ L _ (numberField_of_fd L) σL * h⁻¹) = 1 := by
    intro σL
    let gG : GQ := @G0Galois.resQ L _ (numberField_of_fd L) σL
    let hG : GQ := h
    let k : GQ := h * @G0Galois.resQ L _ (numberField_of_fd L) σL * h⁻¹
    have hgmem : gG ∈ GQL L := by
      have : (@GaloisCopy.resQ L _ (numberField_of_fd L) σL) ∈ L.fixingSubgroup := by
        rw [← resQRange L]; exact ⟨σL, rfl⟩
      exact this
    have hk : k ∈ GQL L := hnormL.conj_mem _ hgmem h
    have hkh : k * hG = hG * gG := by
      show h * @G0Galois.resQ L _ (numberField_of_fd L) σL * h⁻¹ * h =
        h * @G0Galois.resQ L _ (numberField_of_fd L) σL
      group
    have hβk : β k = β gG := by
      have e1 := hβe k hG
      have e2 := hβe hG gG
      rw [hεN k hG (Or.inl hk), _root_.one_mul, hkh] at e1
      rw [hεN hG gG (Or.inr hgmem), _root_.one_mul] at e2
      rw [← e2, _root_.mul_comm (β hG)] at e1
      exact mul_right_cancel e1
    have hak : a k = 1 := (haL 1 k hk).1
    rw [div_eq_one_iff_eq (hg0 k)]
    apply ιC.toRingHom.injective
    show ιC (βQ gG) = ιC (gamQ k)
    rw [hιβ, hιg, hak, hβk]
    simp
  have onL5 : G8Object.OnL L A
      (fun g => opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
        (conjE Θ (m (h * g * h⁻¹))))
      (fun g => j5 (βQ g / gamQ (h * g * h⁻¹))) ψ5 :=
    fun σL => ⟨by show j5 _ = 1; rw [haQ σL, map_one], hψ5 σL⟩
  have onL3 : G8Object.OnL L A
      (fun g => opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
        (conjE Θ (m (h * g * h⁻¹))))
      (fun g => j3 (βQ g / gamQ (h * g * h⁻¹))) ψ3 :=
    fun σL => ⟨by show j3 _ = 1; rw [haQ σL, map_one], hψ3 σL⟩
  refine ⟨fun g => βQ g / gamQ (h * g * h⁻¹), βQ, j5, j3, _, c5, ε5, u5, _, c3, ε3, u3, ψ5, ψ3,
    h5, h3, ?_, ⟨ιC, hιβ⟩, onL5, onL3⟩
  -- `FrobTraceLink` from `AlgFrobLink`
  obtain ⟨S, hS⟩ := hF L A m hmL hmLL hFalg
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS' : p ∉ S := fun h' => hpS (Finset.mem_union_left _ h')
  have hp3 : (3 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  have hp5 : (5 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  obtain ⟨k, _, hk, Ab, α, N', hN', hΨ⟩ := hS p hp hpS' v τ hv hτ h
  obtain ⟨Ψ3, hΨ3⟩ := hΨ 3 hp3
  obtain ⟨Ψ5, hΨ5⟩ := hΨ 5 hp5
  exact ⟨k, _, hk, Ab, α, N', hN',
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 3 Ab α N' Ψ3 hΨ3,
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 5 Ab α N' Ψ5 hΨ5⟩


/-- **`TateBridge35OnL` from the leaf I3.M0 and frob-trace's `AlgFrobRed` (proved).** -/
theorem tateBridge35OnL_of_algFrobRed (hT : PkgI3.TateModuleFree) (hR : FrobTrace.AlgFrobRed) :
    TateBridge35OnL :=
  tateBridge35OnL_of_algFrobLink hT (algFrobLink_of_one (algFrobOne_of_red hR))

/-- **Main result: `TateBridge35OnL` from the leaf I3.M0 and alg-frob-red's five inputs**
(leaf candidates `GoodRedCofinite`, `SmoothGeomConnIntegral`; kernel leaf I2-Red; glue
`FExtendGen`, `AbsFrob`). -/
theorem tateBridge35OnL_of_gen (hT : PkgI3.TateModuleFree) (hG : AlgFrobRedRed.GoodRedCofinite)
    (hS : AlgFrobRedRed.SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : AlgFrobRedRed.FExtendGen) (hA : AlgFrobRedRed.AbsFrob) : TateBridge35OnL :=
  tateBridge35OnL_of_algFrobRed hT (AlgFrobRedRed.algFrobRed_of_gen hG hS hRed hE hA)


end G8Tate

end

#print axioms G8Tate.opW_bijective
#print axioms G8Tate.onL_exists
#print axioms G8Tate.tateBridge35_of_onL
#print axioms G8Tate.scalarsQbarC
#print axioms G8Tate.tateBridge35OnL_of_algFrobLink
#print axioms G8Tate.tateBridge35OnL_of_algFrobRed
#print axioms G8Tate.tateBridge35OnL_of_gen
