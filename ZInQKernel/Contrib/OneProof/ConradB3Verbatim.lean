import ZInQKernel.Contrib.OneProof.ConradBridges
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-! Step C8, sec:height, L760–764. The two printed inputs are Conrad's
near-one display and Proposition B.3 for local base `ℚ_p`. -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Bridges

open Module
open scoped TensorProduct Topology Filter

set_option linter.style.longLine false

variable (p : ℕ) [Fact p.Prime]
variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- The continuous character on the topological abelianization appearing in
Conrad, Appendix B pp. 32–33 (C8, L760–762). -/
def conradAbelianChar (ψ : PkgI4.GQp p →* Kˣ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p))) :
    Field.absoluteGaloisGroupAbelianization ℚ_[p] →ₜ* Kˣ :=
  TopologicalAbelianization.lift
    { toMonoidHom := ψ
      continuous_toFun := Units.isEmbedding_val₀.isInducing.continuous_iff.mpr
        (Topology.IsInducing.subtypeVal.continuous_iff.mpr hc) }

/-- C8, Conrad p. 33: the displayed near-one equality on the arithmetic Artin
map itself, for local base `ℚ_p` (one factor in the product). -/
def ArtinNearOnePrint (ψ : PkgI4.GQp p →* Kˣ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p))) (n : ℤ) : Prop :=
  ∀ᶠ x : ℚ_[p]ˣ in 𝓝 1,
    (conradAbelianChar p ψ hc (TauCeti.ClassFieldTheory.artinMap ℚ_[p] x) : K) =
      algebraMap ℚ_[p] K (x : ℚ_[p]) ^ (-n)

/-- Evaluating the descended character on the arithmetic Artin symbol agrees
with evaluating the original character on any lift of that symbol. -/
theorem conradAbelianChar_artinLift (ψ : PkgI4.GQp p →* Kˣ) (hc)
    (x : ℚ_[p]ˣ) (σ : PkgI4.GQp p) (hσ : IsArtinLift p σ x) :
    conradAbelianChar p ψ hc (TauCeti.ClassFieldTheory.artinMap ℚ_[p] x) = ψ σ := by
  rw [← hσ]
  exact TopologicalAbelianization.lift_mk _ _

/-- The old lift formulation is equivalent to Conrad's equality on the
abelianization. Surjectivity is used pointwise, with no choice of section. -/
theorem artinNearOnePrint_iff (ψ : PkgI4.GQp p →* Kˣ) (hc) (n : ℤ) :
    ArtinNearOnePrint p ψ hc n ↔ ArtinNearOne p ψ n := by
  constructor
  · intro h
    filter_upwards [h] with x hx σ hσ
    rwa [← conradAbelianChar_artinLift p ψ hc x σ hσ]
  · intro h
    filter_upwards [h] with x hx
    obtain ⟨σ, hσ⟩ := exists_artinLift p x
    rw [conradAbelianChar_artinLift p ψ hc x σ hσ]
    exact hx σ hσ

/-- C8 (L760–762), Conrad pp. 32–33: the Hodge–Tate implication followed by
the printed display, at local base `ℚ_p`, for the constant weight case. -/
def ConradNearOnePrint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (i : ℤ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p))),
    PureHT p ψ i → ∃ n : ℤ, ArtinNearOnePrint p ψ hc n

/-- C8 (L760–764), Conrad p. 33, Proposition B.3 at local base `ℚ_p`.
There is only one factor of `ℚ_p ⊗ K = K`, so every weight is the
single exponent `n`. The printed multiset of weights is expressed as a
splitting of the underlying `ℚ_p`-representation after tensoring with
`ℂ_p`, equivariant for the full local Galois group. -/
def ConradB3Print : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p))),
    ArtinNearOnePrint p ψ hc n → PureHT p ψ n

/-- Step C8, Conrad Appendix B pp. 32–33: the near-one display and B.3,
both at local base `ℚ_p` and in Conrad's sign and Artin conventions. -/
def ConradAppBPrint : Prop :=
  ConradNearOnePrint ∧ ConradB3Print

open _root_.ZInQ.Contrib.G9 (matRep)

private theorem identityLine_of_pureHT [FiniteDimensional ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ) (h : PureHT p ψ n) :
    IdentityLine p K ψ n := by
  classical
  obtain ⟨e, he⟩ := h
  let V := Fin 1 → K
  let T := ℂ_[p] ⊗[ℚ_[p]] V
  let D := Fin (finrank ℚ_[p] K)
  let ev : T →ₗ[ℂ_[p]] ℂ_[p] :=
    (((IsScalarTower.toAlgHom ℚ_[p] K ℂ_[p]).toLinearMap).comp
      (LinearMap.proj (R := K) (φ := fun _ : Fin 1 => K) 0 |>.restrictScalars ℚ_[p])).liftBaseChange ℂ_[p]
  have ev_tmul (a : ℂ_[p]) (v : V) : ev (a ⊗ₜ[ℚ_[p]] v) = a * algebraMap K ℂ_[p] (v 0) := rfl
  have hev : ev ≠ 0 := by
    intro hzero
    have h1 := LinearMap.congr_fun hzero ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (fun _ : Fin 1 => (1 : K)))
    simp only [ev_tmul, map_one, mul_one, LinearMap.zero_apply, one_ne_zero] at h1
  obtain ⟨j, hj⟩ : ∃ j : D, ev (e.symm (Pi.single j 1)) ≠ 0 := by
    by_contra! hz
    apply hev
    apply ((Pi.basisFun ℂ_[p] D).map e.symm).ext
    intro k
    simpa only [Basis.map_apply, Pi.basisFun_apply, LinearMap.zero_apply] using hz k
  let z := e.symm (Pi.single j 1)
  refine ⟨(ev z)⁻¹, inv_ne_zero hj, fun g => ?_⟩
  let σ := restrictGalois p K g
  change algebraMap K ℂ_[p] (ψ σ : K) * (ev z)⁻¹ =
    PkgI4.cycPow p σ n • PkgI4.cpAct p σ ((ev z)⁻¹)
  have hσ : σ ∈ K.fixingSubgroup := (K.fixingSubgroupEquiv.symm g).2
  have hfix (k : K) :
      PkgI4.cpAct p σ (algebraMap K ℂ_[p] k) = algebraMap K ℂ_[p] k := by
    rw [IsScalarTower.algebraMap_apply K (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
      PkgI4.cpAct_coe]
    exact congrArg (fun x : PadicAlgCl p => (x : ℂ_[p])) (hσ k)
  let A0 : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] :=
    { toFun := PkgI4.cpAct p σ
      map_add' := map_add _
      map_smul' := fun a x => by simp only [RingHom.id_apply, Algebra.smul_def, map_mul,
        PkgI4.cpAct_algebraMap] }
  let A : T →ₗ[ℚ_[p]] T := TensorProduct.map A0 (matRep p (charRep ψ) σ)
  have A_tmul (a : ℂ_[p]) (v : V) : A (a ⊗ₜ[ℚ_[p]] v) =
      (PkgI4.cpAct p σ a) ⊗ₜ[ℚ_[p]]
        ((charRep ψ σ : Matrix (Fin 1) (Fin 1) K).mulVec v) := rfl
  have ev_A (x : T) :
      ev (A x) = algebraMap K ℂ_[p] (ψ σ : K) * PkgI4.cpAct p σ (ev x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a v =>
      rw [A_tmul, ev_tmul, ev_tmul, map_mul, hfix]
      have hm : ((charRep ψ σ : Matrix (Fin 1) (Fin 1) K).mulVec v) 0 = (ψ σ : K) * v 0 := by
        simp [Matrix.mulVec, dotProduct, charRep, Matrix.algebraMap_matrix_apply]
      rw [hm, map_mul]
      ring
    | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  have e_A (x : T) (k : D) :
      e (A x) k = PkgI4.cycPow p σ n • PkgI4.cpAct p σ (e x k) := by
    induction x using TensorProduct.inductionOn with
    | tmul a v => simpa only [A_tmul] using he σ a v k
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, smul_add]
  have hAz : A z = PkgI4.cycPow p σ n • z := by
    apply e.injective
    ext k
    have hz : e z = Pi.single j 1 := e.apply_symm_apply _
    rw [e_A, LinearMapClass.map_smul_of_tower, Pi.smul_apply, hz]
    by_cases hk : k = j
    · subst k
      simp
    · simp [Pi.single_eq_of_ne hk]
  have eqn := ev_A z
  rw [hAz, LinearMapClass.map_smul_of_tower] at eqn
  have hz : ev z ≠ 0 := hj
  have hgz : PkgI4.cpAct p σ (ev z) ≠ 0 := (map_ne_zero _).mpr hz
  rw [Algebra.smul_def, map_inv₀, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hz hgz]
  simpa only [Algebra.smul_def] using eqn.symm

/-- B.3 for the full group implies the original identity-line statement. -/
theorem conradIdentityWeight_of_print (h : ConradB3Print) : ConradIdentityWeight := by
  intro p _ K _ _ ψ n hc hn
  exact identityLine_of_pureHT p ψ n (h p K ψ n hc ((artinNearOnePrint_iff p ψ hc n).mpr hn))

/-- Both conjuncts of the unchanged concrete C8 statement follow from print. -/
theorem conradAppBConcrete_of_print (h : ConradAppBPrint) : ConradAppBConcrete := by
  refine ⟨?_, conradIdentityWeight_of_print h.2⟩
  intro p _ K _ _ ψ i hc hHT
  obtain ⟨n, hn⟩ := h.1 p K ψ i hc hHT
  exact ⟨n, (artinNearOnePrint_iff p ψ hc n).mp hn⟩

/-- Discharges the existing C8 field `OpenAddedLeaves28.conradAppB`. -/
theorem conradAppB_of_print (h : ConradAppBPrint) : ConradAppB :=
  conradAppB_of_concrete (conradAppBConcrete_of_print h)

end HDec.G0Galois.C8Conrad.Bridges
