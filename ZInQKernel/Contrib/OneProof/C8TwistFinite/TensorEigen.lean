import ZInQKernel.Contrib.OneProof.C8TwistFinite.LocalUnits
import ZInQKernel.Contrib.CloudB3W11TateTrace.TwistWholeGroup
import ZInQKernel.Contrib.CloudB3W11AxCompletion.GaloisAction

/-! # C8 without Conrad, local part 2: Tate's theorem kills a power of the twist

* `exists_eigen_of_pureHT`: a character `ψ : G_{ℚ_p} → E^×` (`E/ℚ_p` finite) which is
  Hodge–Tate of weight `0`, in the form of an equivariant splitting
  `ℂ_p ⊗ E ≅ ℂ_p^{[E:ℚ_p]}` (`PureHT'`, word for word `C8Conrad.Bridges.PureHT` with the
  copies of `cpAct` and `cycPow` in `ZInQ.Contrib.G9.PkgI4`), has a nonzero `t ∈ ℂ_p ⊗ E` with
  `(σ ⊗ 1) t = (1 ⊗ ψ(σ)⁻¹) t`: pull back the vector `(1, …, 1)`.
* `pow_eq_one_of_eigen`: if moreover `ψ^d` is trivial on the kernel of the cyclotomic
  character, then `ψ` has finite order. `ℂ_p ⊗ E` is reduced (`E/ℚ_p` is separable), so `t^d ≠ 0`
  is an eigenvector for `ψ^d`, and the tree's Tate–Sen theorem (`TensorTwist.solution`, with the
  traces of `CyclotomicTrace.solution`, as in `TwistWholeGroup`) gives `ψ^{dn} = 1`. -/

noncomputable section

namespace ZInQ.Contrib.C8TwistFinite

open Module
open scoped TensorProduct

variable {p : ℕ} [Fact p.Prime]

/-- A character as a one-dimensional representation (as `C8Conrad.charRep`). -/
def charRep' {E : Type*} [Field E] (ψ : PkgI4.GQp p →* Eˣ) : PkgI4.GQp p →* GL (Fin 1) E :=
  (Units.map (algebraMap E (Matrix (Fin 1) (Fin 1) E)).toMonoidHom).comp ψ

variable (p)

/-- The constant-weight Hodge–Tate splitting (as `C8Conrad.Bridges.PureHT`). -/
def PureHT' {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ) (i : ℤ) : Prop :=
  ∃ e : (ℂ_[p] ⊗[ℚ_[p]] (Fin 1 → E)) ≃ₗ[ℂ_[p]] (Fin (finrank ℚ_[p] E) → ℂ_[p]),
    ∀ (σ : PkgI4.GQp p) (a : ℂ_[p]) (v : Fin 1 → E) j,
      e ((G9.PkgI4.cpAct p σ a) ⊗ₜ[ℚ_[p]]
          ((charRep' ψ σ : Matrix (Fin 1) (Fin 1) E).mulVec v)) j =
        G9.PkgI4.cycPow p σ i • G9.PkgI4.cpAct p σ (e (a ⊗ₜ[ℚ_[p]] v) j)

theorem charRep'_mulVec {E : Type*} [Field E] (ψ : PkgI4.GQp p →* Eˣ) (σ : PkgI4.GQp p)
    (v : E) :
    (charRep' ψ σ : Matrix (Fin 1) (Fin 1) E).mulVec (fun _ => v) = fun _ => (ψ σ : E) * v := by
  funext i
  fin_cases i
  simp [charRep', Matrix.mulVec, dotProduct, Matrix.algebraMap_matrix_apply]

/-- **Weight `0` gives an eigenvector**: pull back `(1, …, 1)` along the splitting. -/
theorem exists_eigen_of_pureHT {E : Type*} [Field E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] (ψ : PkgI4.GQp p →* Eˣ) (h : PureHT' p ψ (-0)) :
    ∃ t : ℂ_[p] ⊗[ℚ_[p]] E, t ≠ 0 ∧ ∀ σ : PkgI4.GQp p,
      Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] E) t =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (((ψ σ)⁻¹ : Eˣ) : E)) * t := by
  obtain ⟨e, he⟩ := h
  let ι : (ℂ_[p] ⊗[ℚ_[p]] E) ≃ₗ[ℚ_[p]] (ℂ_[p] ⊗[ℚ_[p]] (Fin 1 → E)) :=
    TensorProduct.congr (LinearEquiv.refl _ _) (LinearEquiv.funUnique (Fin 1) ℚ_[p] E).symm
  let F : (ℂ_[p] ⊗[ℚ_[p]] E) ≃+ (Fin (finrank ℚ_[p] E) → ℂ_[p]) :=
    ι.toAddEquiv.trans e.toAddEquiv
  have hF : ∀ (σ : PkgI4.GQp p) (s : ℂ_[p] ⊗[ℚ_[p]] E),
      F (((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Eˣ) : E)) *
        Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] E) s) =
        fun j => G9.PkgI4.cpAct p σ (F s j) := by
    intro σ s
    induction s using TensorProduct.induction_on with
    | zero => funext j; simp
    | tmul a v =>
      funext j
      have h1 := he σ a (fun _ => v) j
      rw [charRep'_mulVec] at h1
      have hc : G9.PkgI4.cycPow p σ (-0) = 1 := by simp [G9.PkgI4.cycPow]
      rw [hc, one_smul] at h1
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [ZInQ.Contrib.CloudB3W11AxCompletion.galois_galAlgHom_apply_eq_cpAct]
      exact h1
    | add x y hx hy =>
      funext j
      rw [map_add, mul_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]
  let t : ℂ_[p] ⊗[ℚ_[p]] E := F.symm (fun _ => 1)
  have hFt : F t = fun _ => 1 := F.apply_symm_apply _
  refine ⟨t, ?_, fun σ => ?_⟩
  · intro h0
    have hd : 0 < finrank ℚ_[p] E := Module.finrank_pos
    have := congrFun hFt ⟨0, hd⟩
    rw [h0, map_zero] at this
    exact zero_ne_one this
  · have h2 : ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Eˣ) : E)) *
        Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] E) t = t := by
      apply F.injective
      rw [hF σ t, hFt]
      funext j
      exact map_one _
    calc Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] E) t
        = ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (((ψ σ)⁻¹ : Eˣ) : E)) *
          (((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Eˣ) : E)) *
          Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] E) t) := by
          rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.inv_mul,
            ← Algebra.TensorProduct.one_def, one_mul]
      _ = _ := by rw [h2]

/-- **Tate's theorem kills a power**: a character with a nonzero eigenvector in `ℂ_p ⊗ E`,
some power of which is trivial on the kernel of the cyclotomic character, has finite order. -/
theorem pow_eq_one_of_eigen {E : Type*} [Field E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] (η : PkgI4.GQp p →* Eˣ) (t : ℂ_[p] ⊗[ℚ_[p]] E) (ht0 : t ≠ 0)
    (ht : ∀ σ : PkgI4.GQp p,
      Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] E) t =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((η σ : Eˣ) : E)) * t)
    {d : ℕ} (hd0 : 0 < d) (hd : ∀ σ, cycL p σ = 1 → η σ ^ d = 1) :
    ∃ n : ℕ, 0 < n ∧ ∀ σ, η σ ^ n = 1 := by
  have : Algebra.IsSeparable ℚ_[p] E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyUnramified ℚ_[p] E := Algebra.FormallyUnramified.of_isSeparable _ _
  have hred : IsReduced (ℂ_[p] ⊗[ℚ_[p]] E) := Algebra.FormallyUnramified.isReduced_of_field ℂ_[p] _
  have htd0 : t ^ d ≠ 0 := fun h => ht0 (IsReduced.eq_zero t ⟨d, h⟩)
  let Kb : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥
  let Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p) := CloudB3W11TateTrace.CyclotomicTrace.TCT.F p
  let ψ' : Kb.fixingSubgroup →* Eˣ := (powMonoidHom d).comp (η.comp (Subgroup.subtype _))
  have hψ' : ∀ σ : Kb.fixingSubgroup,
      (∀ m, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Km m).fixingSubgroup) → ψ' σ = 1 := by
    intro σ hσ
    have hchar : cycL p (σ : PkgI4.GQp p) = 1 := by
      rw [cycL_apply]
      apply (TauCeti.cyclotomicCharacter_eq_one_iff p).mpr
      intro n ζ hζ
      exact (IntermediateField.mem_fixingSubgroup_iff (Km n) (σ : PkgI4.GQp p)).mp (hσ n) ζ
        (PadicAlgCl.cyclotomicTower_mono p (Nat.le_add_right n 2)
          (PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζ))
    exact hd _ hchar
  have hxσ : ∀ σ : Kb.fixingSubgroup,
      Algebra.TensorProduct.map
          (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
          (AlgHom.id ℚ_[p] E) (t ^ d) =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ' σ : Eˣ) : E)) * t ^ d := by
    intro σ
    rw [map_pow, ht, mul_pow, Algebra.TensorProduct.tmul_pow, one_pow]
    simp [ψ', Units.val_pow_eq_pow_val]
  obtain ⟨dd, -, hR⟩ := CloudB3W11TateTrace.CyclotomicTrace.solution p
  obtain ⟨n, hn, hfin⟩ := CloudB3W11TateTrace.TensorTwist.solution p Kb Km
    (CloudB3W11TateTrace.CyclotomicTrace.TCT.F_mono p) (fun _ => bot_le)
    (CloudB3W11TateTrace.CyclotomicTrace.TCT.finiteDimensional_F p)
    dd 0 (fun m _ => hR m) E ψ' hψ' (t ^ d) htd0 hxσ
  refine ⟨d * n, Nat.mul_pos hd0 hn, fun σ => ?_⟩
  have hσ : σ ∈ Kb.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact σ.commutes q
  have h := hfin ⟨σ, hσ⟩
  rw [pow_mul]
  exact h

end ZInQ.Contrib.C8TwistFinite
