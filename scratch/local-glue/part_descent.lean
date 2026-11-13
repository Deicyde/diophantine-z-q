
/-! ## §7d (local-glue). `p ≤ 5`: the torsion field of a model over `L` (proved from a descent Prop)

At `p ∈ {2, 3, 5}` the trick of §7 (`p ∤ |GL₄(𝔽_m)|`) is not available (finding G3), and Glazer
uses the model `A_L` over the Hom field `L` (N5 L813-818): `E = L_v(A_L[m])`, of degree
`≤ |GL₄(𝔽_m)|` over `L_v`. Here:
* `DescentPts A L` (GLUE, new): `L/ℚ` is Galois and `A` has a model `A₀` over `L` with
  `dim A₀ = 2` and a group isomorphism `A₀(L̄) ≅ A(K̄)` intertwining `σ₀ ∈ G_L` with `σ' ∈ G_K`
  whenever both restrict to the same element of `G_ℚ`;
* `index_torsStab_le` (proved): `[G_L : Stab(A₀[q])] ≤ |GL₄(𝔽_q)|` (I2-Tors);
* `torsFix_of_descent` (proved): from R6, I2-Tors and `DescentPts`, for `q ≠ p` prime, `q ≥ 3`, and
  any finite `M ⊇ L_v`, there is `E ⊇ M` with `[E:ℚ_p] ≤ |GL₄(𝔽_q)|·[M:ℚ_p]` on whose wild inertia
  every `ℓⁿ`-torsion point of `A(K̄)` is fixed (`ℓ ≠ p`). `E` is the fixed field of the open
  subgroup `decomp⁻¹(resQ_L(Stab)) ∩ G_M`; its degree is the index (Mathlib's
  `finrank_eq_fixingSubgroup_index`);
* `torsFixWildOdd_of_descent`, `torsFixWildE_two_of_descent`, `tateWildKE_of_descent`,
  `localGlue_of_descent` (proved). -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj

section DescentSec

variable {p : ℕ} [Fact p.Prime]

attribute [local instance] RQ.numberField_of_fd

/-- **Glue (the descent of `A` to the Hom field `L`; N5 L813-818; g0-mod-field: `G7Data` carries
`A : AbVar L` and `TateBridge` takes `A_{L'}` to be its base change to `L'`).** `L/ℚ` is Galois, and
`A/K` has a model `A₀/L` (`dim A₀ = 2`) with a group isomorphism `φ : A₀(L̄) ≅ A(K̄)` such that
`φ ∘ σ₀ = σ' ∘ φ` whenever `σ₀ ∈ G_L` and `σ' ∈ G_K` have the same image in `G_ℚ` (`resQ`). For
`K = L'` and `A = (A₀)_{L'}` this is the base change of points (`bcPt`) along an identification
`L̄ ≅ L̄'` compatible with `qEmb L` and `qEmb L'`; if Mathlib's choices of the embeddings
`L ↪ ℚ̄` (inside `resQ L`, `resQ L'`) differ on `L` by `γ ∈ Gal(L/ℚ)`, the model is the conjugate
`A₀ ×_{L,γ} L`, so the existential is still met. -/
def DescentPts {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] : Prop :=
  IsGalois ℚ L ∧
  ∃ (A₀ : PkgI3.AbVar L) (φ : A₀.Pt (AlgebraicClosure L) ≃* A.Pt (AlgebraicClosure K)),
    A₀.dim = 2 ∧ ∀ (σ₀ : Field.absoluteGaloisGroup L) (σ' : Field.absoluteGaloisGroup K),
      G0Galois.resQ L σ₀ = G0Galois.resQ K σ' →
        ∀ P : A₀.Pt (AlgebraicClosure L), φ (A₀.galAct σ₀ P) = A.galAct σ' (φ P)

variable {K : Type} [Field K] [NumberField K]

/-- **`[G_K : Stab(A[q])] ≤ |GL₄(𝔽_q)|` (proved)** from `A(K̄)[q] ≅ (ℤ/q)⁴` (`TorsGL`): the
action on `A[q]` is a homomorphism `G_K → GL(𝔽_q⁴)` whose kernel is the stabilizer. -/
theorem index_torsStab_le (A : PkgI3.AbVar K) (q : ℕ) [Fact q.Prime] (hT : TorsGL A q) :
    (torsStab A q).index ≠ 0 ∧
      (torsStab A q).index ≤ Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) := by
  set S := {P : A.Pt (AlgebraicClosure K) | P ^ q = 1} with hSdef
  obtain ⟨e, he⟩ := hT
  have hS : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : S), A.galAct σ x.1 ∈ S :=
    fun σ x => by
      have hx : x.1 ^ q = 1 := x.2
      show (A.galAct σ x.1) ^ q = 1
      rw [← map_pow, hx, map_one]
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := fun x hx y hy => by
    simp only [hSdef, Set.mem_setOf_eq] at hx hy ⊢
    rw [mul_pow, hx, hy, _root_.one_mul]
  let f : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) → (Fin 4 → ZMod q) → (Fin 4 → ZMod q) :=
    fun σ v => e ⟨A.galAct σ (e.symm v).1, hS σ _⟩
  have hadd : ∀ σ a b, f σ (a + b) = f σ a + f σ b := by
    intro σ a b
    set x := e.symm a
    set y := e.symm b
    have hxy : e.symm (a + b) = ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he x y, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have h1 : (⟨A.galAct σ (e.symm (a + b)).1, hS σ _⟩ : S) =
        ⟨(A.galAct σ x.1) * (A.galAct σ y.1), hSmul _ (hS σ x) _ (hS σ y)⟩ := by
      apply Subtype.ext
      simp only [hxy, map_mul]
    show e ⟨A.galAct σ (e.symm (a + b)).1, hS σ _⟩ = e ⟨A.galAct σ x.1, hS σ x⟩ +
      e ⟨A.galAct σ y.1, hS σ y⟩
    rw [h1, he ⟨A.galAct σ x.1, hS σ x⟩ ⟨A.galAct σ y.1, hS σ y⟩]
  have hmul : ∀ σ τ v, f (σ * τ) v = f σ (f τ v) := by
    intro σ τ v
    show e ⟨A.galAct (σ * τ) (e.symm v).1, _⟩ =
      e ⟨A.galAct σ (e.symm (e ⟨A.galAct τ (e.symm v).1, _⟩)).1, _⟩
    congr 1
    apply Subtype.ext
    simp only [Equiv.symm_apply_apply]
    rw [galAct_galAct]
  have hone : ∀ v, f 1 v = v := by
    intro v
    show e ⟨A.galAct 1 (e.symm v).1, _⟩ = v
    have h1 : (⟨A.galAct 1 (e.symm v).1, hS 1 _⟩ : S) = e.symm v := by
      apply Subtype.ext
      change PkgI3.AbVar.galHom 1 ≫ (e.symm v).1 = (e.symm v).1
      rw [PkgI3.AbVar.galHom_one, Category.id_comp]
    rw [h1, Equiv.apply_symm_apply]
  let fL : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →
      ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) := fun σ =>
    { ((AddMonoidHom.mk' (f σ) (hadd σ)).toZModLinearMap q) with
      invFun := f σ⁻¹
      left_inv := fun v => by
        change f σ⁻¹ (f σ v) = v
        rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun v => by
        change f σ (f σ⁻¹ v) = v
        rw [← hmul, mul_inv_cancel, hone] }
  let ρ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) :=
    { toFun := fL
      map_one' := LinearEquiv.ext hone
      map_mul' := fun σ τ => LinearEquiv.ext (hmul σ τ) }
  have hker : ρ.ker ≤ torsStab A q := by
    intro σ hσ P hP
    have h1 : f σ (e ⟨P, hP⟩) = e ⟨P, hP⟩ := by
      have := congrArg (fun g : (Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q) => g (e ⟨P, hP⟩))
        (MonoidHom.mem_ker.mp hσ)
      exact this
    have h2 := e.injective h1
    simp only [Equiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  set N := Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) with hN
  have hcard : Nat.card ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) = N :=
    (Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod q)
      (Fin 4 → ZMod q)).toEquiv).symm.trans
      (Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv).symm
  haveI : Finite ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) :=
    Finite.of_equiv _ ((Matrix.GeneralLinearGroup.toLin).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod q) (Fin 4 → ZMod q)).toEquiv)
  have hkerI : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have hr1 : 0 < Nat.card ρ.range := Nat.card_pos
  have hrN : Nat.card ρ.range ≤ N := hcard ▸ Subgroup.card_le_card_group _
  have hdvd : (torsStab A q).index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hker
  have hpos : 0 < (torsStab A q).index := Nat.pos_of_dvd_of_pos hdvd (hkerI ▸ hr1)
  exact ⟨hpos.ne', (Nat.le_of_dvd (hkerI ▸ hr1) hdvd).trans (hkerI ▸ hrN)⟩

end DescentSec

end G15Ram

end
