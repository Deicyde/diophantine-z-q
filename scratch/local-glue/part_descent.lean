
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

/-- `resQ K` is injective (proved): `qEmb K ∘ resQ K τ = τ ∘ qEmb K` and `qEmb K` is onto. -/
theorem resQ_injective' : Function.Injective (G0Galois.resQ K) := by
  intro τ₁ τ₂ h
  let τ₁' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ₁
  let τ₂' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ₂
  show τ₁' = τ₂'
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := qEmbRing_surjective K y
  have h1 := G0Galois.resQ_spec K τ₁' x
  have h2 := G0Galois.resQ_spec K τ₂' x
  change τ₁' (G0Galois.qEmbRing K x) = τ₂' (G0Galois.qEmbRing K x)
  rw [← h1, ← h2]
  exact congrArg (fun g => G0Galois.qEmbRing K (g x)) h

/-- **The torsion field of the model over `L` (proved)** from the leaves R6 (`raynaudPlace_of_R6`)
and I2-Tors and the glue `DescentPts`. For a prime `q ≥ 3`, `q ≠ p`, and a finite `M ⊇ L_v`,
there is a finite `E ⊇ M` with `[E:ℚ_p] ≤ |GL₄(𝔽_q)|·[M:ℚ_p]` such that every wild `σ ∈ G_E` fixes
every `ℓⁿ`-torsion point of `A(K̄)` through `G_K` (`ℓ ≠ p`). `E` is the fixed field of
`H = decomp⁻¹(resQ_L(Stab(A₀[q]))) ∩ G_M`, which is open (it contains `G_{E₀}`, `E₀` generated over
`M` by a basis of `L(A₀[q])`, finite by `ptFinite`), and `[E:ℚ_p] = [G_{ℚ_p} : H]`. For wild
`σ ∈ G_E`, `decomp σ = resQ_L σ₀` with `σ₀` fixing `A₀[q]`; Raynaud (`RaynaudPlace A₀ q`) and the
`p`-power period (`wildIter`) give that `σ₀` fixes `A₀[ℓⁿ]` (D2), and `φ` carries this to `A`. -/
theorem torsFix_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (q : ℕ) [Fact q.Prime] (hq3 : 3 ≤ q) (hpq : q ≠ p)
    (M : Fld p) [FiniteDimensional ℚ_[p] M] (hLvM : Lv (p := p) L ≤ M) :
    ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ M ≤ E ∧
      Module.finrank ℚ_[p] E ≤
        Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) * Module.finrank ℚ_[p] M ∧
      ∀ σ ∈ fixSet E ∩ wildSet, ∀ σ' : Field.absoluteGaloisGroup K,
        G0Galois.resQ K σ' = decomp p σ →
          ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P := by
  obtain ⟨hGal, A₀, φ, hdim₀, hφ⟩ := hD
  have hp : p.Prime := Fact.out
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp Fact.out).mp h).symm
  have hT₀ : TorsGL A₀ q := torsGL_of_leaf hTors A₀ hdim₀ q (by omega)
  obtain ⟨hidx0, hidx⟩ := index_torsStab_le A₀ q hT₀
  obtain ⟨F', hF'fd, hF'⟩ := exists_fin_le_torsStab A₀ q hT₀
  let Stab : Subgroup (Field.absoluteGaloisGroup L) := torsStab A₀ q
  let ρL : Field.absoluteGaloisGroup L →* GQ := G0Galois.resQ L
  have hρinj : Function.Injective ρL := resQ_injective'
  have hrange : ρL.range = L.fixingSubgroup := RQ.resQ_range L
  let Hq : Subgroup GQ := Stab.map ρL
  let GM : Subgroup (GQp p) := M.fixingSubgroup
  let H : Subgroup (GQp p) := Hq.comap (decomp p) ⊓ GM
  -- `decomp` of `G_M` fixes `L`
  have hdecL : ∀ σ : GQp p, σ ∈ fixSet M → decomp p σ ∈ L.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      (decomp_fix_of_le (fun x hx => hLvM (embP_mem_Lv hx)) hσ)
  -- the open subgroup `G_{E₀}` inside `H`
  haveI : FiniteDimensional L F' := hF'fd
  haveI : Module.Free L F' := Module.Free.of_divisionRing L F'
  let b := Module.finBasis L F'
  let eL : AlgebraicClosure ℚ ≃+* AlgebraicClosure L :=
    RingEquiv.ofBijective (G0Galois.qEmbRing L)
      ⟨(G0Galois.qEmbRing L).injective, qEmbRing_surjective L⟩
  let S₀ : Set (Kbar p) := Set.range fun i => embP (eL.symm (b i : AlgebraicClosure L))
  haveI : Finite S₀ := Set.finite_range _ |>.to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] S₀) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E₀ : Fld p := M ⊔ IntermediateField.adjoin ℚ_[p] S₀
  have hE₀H : E₀.fixingSubgroup ≤ H := by
    intro σ hσ
    have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
    have hσM : σ ∈ fixSet M := fun x hx => hσ' x (le_sup_left (a := M) hx)
    have hσS : ∀ i, decomp p σ (eL.symm (b i : AlgebraicClosure L)) =
        eL.symm (b i : AlgebraicClosure L) := by
      intro i
      apply (embP (p := p)).injective
      rw [decomp_spec]
      exact hσ' _ (le_sup_right (a := M)
        (IntermediateField.subset_adjoin ℚ_[p] S₀ ⟨i, rfl⟩))
    obtain ⟨σ₀, hσ₀⟩ : decomp p σ ∈ ρL.range := hrange ▸ hdecL σ hσM
    let σ₀' : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L := σ₀
    have hσ₀b : ∀ i, σ₀' (b i : AlgebraicClosure L) = b i := by
      intro i
      have h1 := G0Galois.resQ_spec L σ₀' (eL.symm (b i : AlgebraicClosure L))
      have h2 : G0Galois.qEmbRing L (eL.symm (b i : AlgebraicClosure L)) = b i :=
        eL.apply_symm_apply _
      change G0Galois.qEmbRing L (ρL σ₀ _) = _ at h1
      rw [hσ₀, hσS i, h2] at h1
      exact h1.symm
    have hσ₀F : σ₀' ∈ F'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      have hsum := b.sum_repr ⟨z, hz⟩
      set c := b.repr ⟨z, hz⟩ with hc
      have hz' : z = ∑ i, c i • (b i : AlgebraicClosure L) := by
        have := congrArg (fun w : F' => (w : AlgebraicClosure L)) hsum
        simp only at this
        rw [← this, IntermediateField.coe_sum]
        rfl
      rw [hz', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hσ₀b i]
    refine ⟨?_, (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσM⟩
    show decomp p σ ∈ Hq
    exact ⟨σ₀', hF' hσ₀F, hσ₀⟩
  have hHopen : IsOpen (H : Set (GQp p)) :=
    Subgroup.isOpen_mono hE₀H (IntermediateField.fixingSubgroup_isOpen E₀)
  have hHclosed : IsClosed (H : Set (GQp p)) := Subgroup.isClosed_of_isOpen H hHopen
  let E : Fld p := IntermediateField.fixedField H
  have hEH : E.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  -- the index
  have hmapLe : GM.map (decomp p) ≤ ρL.range := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [hrange]
    exact hdecL σ ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ)
  have hrel1 : Hq.relIndex ρL.range = Stab.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hρinj,
      Subgroup.relIndex_top_right]
  have hrel2 : Hq.relIndex (GM.map (decomp p)) ≤ Stab.index := by
    rw [← hrel1]
    exact Subgroup.relIndex_le_of_le_right hmapLe (by rw [hrel1]; exact hidx0)
  have hrel3 : Hq.relIndex (GM.map (decomp p)) ≠ 0 := fun h0 =>
    hidx0 (hrel1 ▸ Subgroup.relIndex_eq_zero_of_le_right hmapLe h0)
  have hHidx : H.index = (Hq.comap (decomp p)).relIndex GM * GM.index := Subgroup.index_inf
  rw [Subgroup.relIndex_comap] at hHidx
  have hMfr : Module.finrank ℚ_[p] M = GM.index :=
    IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) M
  have hEfr : Module.finrank ℚ_[p] E = H.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) E, hEH]
  have hMpos : 0 < Module.finrank ℚ_[p] M := Module.finrank_pos
  have hEpos : 0 < Module.finrank ℚ_[p] E := by
    rw [hEfr, hHidx]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hrel3) (hMfr ▸ hMpos)
  refine ⟨E, Module.finite_of_finrank_pos hEpos, ?_, ?_, ?_⟩
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp (Subgroup.mem_inf.mp hτ).2 x hx
  · rw [hEfr, hHidx, hMfr]
    exact Nat.mul_le_mul_right _ (hrel2.trans hidx)
  · intro σ hσ σ' hσ' n P hP
    have hσE : σ ∈ E.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσ.1
    rw [hEH] at hσE
    obtain ⟨σ₀, hσ₀S, hσ₀⟩ := (Subgroup.mem_inf.mp hσE).1
    have hσ₀' : G0Galois.resQ L σ₀ = decomp p σ := hσ₀
    have hR := raynaudPlace_of_R6 (p := p) hR6 hTors A₀ hdim₀ hq3 hpq'
    set Q := φ.symm P with hQdef
    have hQ : Q ^ (ℓ ^ n) = 1 := by rw [hQdef, ← map_pow, hP, map_one]
    have hu := hR σ hσ.2 σ₀ hσ₀' (fun R hR' => hσ₀S R hR') ℓ Fact.out hℓp n Q hQ
    obtain ⟨a, ha⟩ := wildIter (p := p) A₀ σ hσ.2 σ₀ hσ₀' Q
    have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
      Nat.Coprime.pow a n ((Nat.coprime_primes hp Fact.out).mpr (Ne.symm hℓp))
    have hfix := fixed_of_unipSq_of_iterate' A₀ σ₀ Q ℓ n p a hcop hQ hu ha
    have h1 := hφ σ₀ σ' (hσ₀'.trans hσ'.symm) Q
    rw [hfix, hQdef, MulEquiv.apply_symm_apply] at h1
    exact h1.symm

/-- `|GL₄(𝔽₅)| = G₀ = 116064000000` (proved). -/
theorem card_GL4_five :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 5)) = ZInQ.heightG0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  unfold ZInQ.heightG0
  norm_num

/-- **`TorsFixWildOdd` at every `p ≠ ℓ` (proved)** from the leaves R6, I2-Tors and the glue
`DescentPts`: `torsFix_of_descent` with `M = L_v` and `q = 3` (`q = 5` if `p = 3`);
`|GL₄(𝔽₃)| = 24261120 ≤ G₀` and `|GL₄(𝔽₅)| = G₀` (Glazer's `E = L_v(A_L[3])`, resp. `A_L[5]`). -/
theorem torsFixWildOdd_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : TorsFixWildOdd (p := p) A ℓ L := by
  obtain ⟨hLvfd, -⟩ := Lv_fin (p := p) L
  haveI := hLvfd
  have key : ∃ q : ℕ, ∃ _ : Fact q.Prime, 3 ≤ q ∧ q ≠ p ∧
      Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) ≤ ZInQ.heightG0 := by
    by_cases h3 : p = 3
    · exact ⟨5, ⟨by norm_num⟩, by norm_num, by omega, card_GL4_five.le⟩
    · refine ⟨3, ⟨by norm_num⟩, le_refl _, Ne.symm h3, ?_⟩
      rw [card_GL4_three]
      unfold ZInQ.heightG0
      norm_num
  obtain ⟨q, hq, hq3, hqp, hqN⟩ := key
  obtain ⟨E, hEfd, hLvE, hdeg, hfix⟩ :=
    torsFix_of_descent hR6 hTors hD hℓp q hq3 hqp (Lv (p := p) L) le_rfl
  exact ⟨E, hEfd, hLvE, hdeg.trans (Nat.mul_le_mul_right _ hqN), hfix⟩

/-- **`TorsFixWildE` from `BetaTwist2` (proved; used at `p = 2`, valid for `p ≠ 3`)**:
`torsFix_of_descent` with `q = 3` over `BetaTwist2`'s `M`; `4·|GL₄(𝔽₃)| ≤ G₀`. -/
theorem torsFixWildE_of_twist (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hp3 : p ≠ 3) {β : GQ → PadicAlgCl ℓ}
    (hB : BetaTwist2 (p := p) β L) : TorsFixWildE (p := p) A ℓ β L := by
  obtain ⟨M, hMfd, hLvM, hMdeg, hMβ⟩ := hB
  haveI := hMfd
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨E, hEfd, hME, hdeg, hfix⟩ :=
    torsFix_of_descent hR6 hTors hD hℓp 3 le_rfl (Ne.symm hp3) M hLvM
  refine ⟨E, hEfd, hLvM.trans hME, ?_, fun σ hσ =>
    ⟨hMβ σ ⟨fun x hx => hσ.1 x (hME hx), hσ.2⟩, hfix σ hσ⟩⟩
  rw [card_GL4_three] at hdeg
  calc Module.finrank ℚ_[p] E ≤ 24261120 * Module.finrank ℚ_[p] M := hdeg
    _ ≤ 24261120 * (4 * Module.finrank ℚ_[p] (Lv (p := p) L)) := Nat.mul_le_mul_left _ hMdeg
    _ = 97044480 * Module.finrank ℚ_[p] (Lv (p := p) L) := by ring
    _ ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) :=
        Nat.mul_le_mul_right _ (by unfold ZInQ.heightG0; norm_num)

/-- **`TateWildKE` at every `p ≠ ℓ` (proved)** from R6, I2-Tors, `DescentPts`, G7's clauses and,
at `p = 2`, `BetaTwist2`. -/
theorem tateWildKE_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]
    {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hC : G7Clauses β ε L)
    (hD : DescentPts A L) (hℓp : ℓ ≠ p) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    TateWildKE (p := p) A ℓ β L := by
  by_cases h2 : p = 2
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_twist hR6 hTors hD hℓp (by omega) (hB h2))
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_odd h2 hC (torsFixWildOdd_of_descent hR6 hTors hD hℓp))

/-- **`LocalGlue p Tm a β L` on G7's data (proved)** from the leaves R6 and I2-Tors and the glue
`KerWild` (all `p`), `DescentPts` (`p ≤ 5`) and `BetaTwist2` (`p = 2`). -/
theorem localGlue_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L] (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hD : p ≤ 5 → DescentPts A L) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_leaves hR6 hTors hpℓ h7 hC hK
    (fun h5 => tateWildKE_of_descent hR6 hTors hC (hD h5) (Ne.symm hpℓ) hB) hB

end DescentSec

end G15Ram

end

#print axioms G15Ram.index_torsStab_le
#print axioms G15Ram.torsFix_of_descent
#print axioms G15Ram.torsFixWildOdd_of_descent
#print axioms G15Ram.torsFixWildE_of_twist
#print axioms G15Ram.tateWildKE_of_descent
#print axioms G15Ram.localGlue_of_descent
