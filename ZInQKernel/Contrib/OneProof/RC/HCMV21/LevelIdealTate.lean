import ZInQKernel.Contrib.OneProof.RC.HCMV21.HomPlacementBasic
import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricTateChain
import ZInQKernel.Contrib.OneProof.RC.HCMV21.CyclicTateChain
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceGeometricPoints
import ZInQKernel.Contrib.OneProof.RC.Adelic.FullPatch
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.OriginalTateGeometry

/-! Local principality of the placed level-`N` Hom ideal at a prime `p`
dividing the level (tex 9136–9142). The rank-four `ℤ`-basis of `Hom(E, E₀)`
read off a placement and the Tate bases of the geometric Tate modules
(`HDec.CMSerreTate.P1.originalTateModuleFree_proved`) give a `ℤ_p`-basis of the
integral Tate Hom module. The comparison map sends `T_p(α)` to the placed `α`
and intertwines postcomposition with left multiplication. The completed level
lattice is the set of Tate maps preserving the two cyclic chains. An
isomorphism of chains then generates it over the completed enhanced order. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] {a b : ℚ} {E₀ E : PkgI3.AbVar k}
  {S : Order a b} {j : E₀.End ≃+* S.ring}

theorem homT_postcomp (p : ℕ) [Fact p.Prime] (o : E₀.End) (α : Hom E E₀) :
    homT (ℓ := p) (postcomp o α) = (homT (ℓ := p) o).comp (homT (ℓ := p) α) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ (α.hom ≫ o.hom)) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ α.hom) ≫ o.hom)
  rw [Category.assoc]

namespace HomPlacement

/-- The placement identifies `Hom(E, E₀)` with its full image lattice. -/
def latticeEquiv (P : HomPlacement S j E) : Hom E E₀ ≃ₗ[ℤ] P.ideal.val.lattice :=
  LinearEquiv.ofBijective (LinearMap.codRestrict _ P.emb.toIntLinearMap P.mem_ideal)
    ⟨fun α β h => P.injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
      obtain ⟨α, hα⟩ := P.exists_of_mem hx
      exact ⟨α, Subtype.ext hα⟩⟩

theorem emb_latticeEquiv_symm (P : HomPlacement S j E) (y : P.ideal.val.lattice) :
    P.emb (P.latticeEquiv.symm y) = y := by
  have h := congrArg Subtype.val (P.latticeEquiv.apply_symm_apply y)
  exact h

/-- The rank-four `ℤ`-basis of `Hom(E, E₀)` read off a placement. -/
def homBasis (P : HomPlacement S j E) : Module.Basis (Fin 4) ℤ (Hom E E₀) :=
  (P.ideal.val.full.basis (QuaternionAlgebra.basisOneIJK a 0 b)).map P.latticeEquiv.symm

end HomPlacement

section Tate

variable (p : ℕ) [Fact p.Prime]

theorem nonempty_tateBasis (hp : (p : k) ≠ 0) (X : PkgI3.AbVar k) (hX : X.dim = 1) :
    Nonempty (Module.Basis (Fin 2) ℤ_[p] (X.T p)) := by
  obtain ⟨hFree, hFinite, hRank⟩ :=
    HDec.CMSerreTate.P1.originalTateModuleFree_proved k X p hp
  have hRank' : ((Module.finrank ℤ_[p] (X.T p) : ℕ∞) : WithBot ℕ∞) = 2 := by
    simpa only [hX, mul_one] using hRank
  exact ⟨Module.finBasisOfFinrankEq _ _ (WithTop.coe_inj.mp (WithBot.coe_inj.mp hRank'))⟩

variable {p}

/-- The integral Tate Hom module, with the basis of rank four. -/
def tateHomBasisFour (hp : (p : k) ≠ 0) (hE : E.dim = 1) (hE₀ : E₀.dim = 1) :
    Module.Basis (Fin 4) ℤ_[p] (E.T p →ₗ[ℤ_[p]] E₀.T p) :=
  ((nonempty_tateBasis p hp E hE).some.linearMap
    (nonempty_tateBasis p hp E₀ hE₀).some).reindex finProdFinEquiv

theorem span_tateHom_eq_top (P : HomPlacement S j E) (hp : (p : k) ≠ 0)
    (hE : E.dim = 1) (hE₀ : E₀.dim = 1) :
    Submodule.span ℤ_[p] (Set.range (tateHom p E E₀)) = ⊤ :=
  span_homT_eq_top_of_basis p 4 hp P.homBasis (tateHomBasisFour hp hE hE₀)

/-- The linear combination of the Tate maps of the placement basis. -/
def tateCombination (P : HomPlacement S j E) :
    (Fin 4 → ℤ_[p]) →ₗ[ℤ_[p]] (E.T p →ₗ[ℤ_[p]] E₀.T p) :=
  Fintype.linearCombination ℤ_[p] (fun i => tateHom p E E₀ (P.homBasis i))

theorem tateHom_eq_combination (P : HomPlacement S j E) (α : Hom E E₀) :
    tateHom p E E₀ α = tateCombination P (fun i => ((P.homBasis.repr α i : ℤ) : ℤ_[p])) := by
  conv_lhs => rw [← P.homBasis.sum_repr α]
  rw [map_sum, tateCombination, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem tateCombination_bijective (P : HomPlacement S j E) (hp : (p : k) ≠ 0)
    (hE : E.dim = 1) (hE₀ : E₀.dim = 1) : Function.Bijective (tateCombination (p := p) P) := by
  have hsurj : Function.Surjective (tateCombination (p := p) P) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_tateHom_eq_top P hp hE hE₀]
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    exact ⟨_, (tateHom_eq_combination P α).symm⟩
  haveI : Module.Finite ℤ_[p] (E.T p →ₗ[ℤ_[p]] E₀.T p) :=
    Module.Finite.of_basis (tateHomBasisFour hp hE hE₀)
  refine ⟨OrzechProperty.injective_of_surjective_of_injective
    (tateHomBasisFour hp hE hE₀).equivFun.symm.toLinearMap _
    (tateHomBasisFour hp hE hE₀).equivFun.symm.injective hsurj, hsurj⟩

/-- The `ℤ_p`-basis of the integral Tate Hom module given by the Tate maps of
the placement basis. -/
def tatePlacementBasis (P : HomPlacement S j E) (hp : (p : k) ≠ 0)
    (hE : E.dim = 1) (hE₀ : E₀.dim = 1) : Module.Basis (Fin 4) ℤ_[p] (E.T p →ₗ[ℤ_[p]] E₀.T p) :=
  Module.Basis.ofEquivFun
    (LinearEquiv.ofBijective (tateCombination P) (tateCombination_bijective P hp hE hE₀)).symm

theorem tatePlacementBasis_apply (P : HomPlacement S j E) (hp : (p : k) ≠ 0)
    (hE : E.dim = 1) (hE₀ : E₀.dim = 1) (i : Fin 4) :
    tatePlacementBasis P hp hE hE₀ i = tateHom p E E₀ (P.homBasis i) := by
  classical
  rw [tatePlacementBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
  change tateCombination P (Pi.single i 1) = _
  rw [tateCombination, Fintype.linearCombination_apply_single, one_smul]

/-- The completed comparison, sending `T_p(α)` to the placed `α`. -/
def tateToLocal (P : HomPlacement S j E) (hp : (p : k) ≠ 0) (hE : E.dim = 1)
    (hE₀ : E₀.dim = 1) : (E.T p →ₗ[ℤ_[p]] E₀.T p) →ₗ[ℤ_[p]] Bp p a b :=
  (tatePlacementBasis P hp hE hE₀).constr ℤ_[p] (fun i => toLocal p (P.emb (P.homBasis i)))

theorem tateToLocal_tateHom (P : HomPlacement S j E) (hp : (p : k) ≠ 0) (hE : E.dim = 1)
    (hE₀ : E₀.dim = 1) (α : Hom E E₀) :
    tateToLocal P hp hE hE₀ (tateHom p E E₀ α) = toLocal p (P.emb α) := by
  conv_lhs => rw [← P.homBasis.sum_repr α]
  conv_rhs => rw [← P.homBasis.sum_repr α]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← tatePlacementBasis_apply P hp hE hE₀, tateToLocal, Module.Basis.constr_basis]

theorem tateToLocal_comp (P : HomPlacement S j E) (hp : (p : k) ≠ 0) (hE : E.dim = 1)
    (hE₀ : E₀.dim = 1) (o : E₀.End) (φ : E.T p →ₗ[ℤ_[p]] E₀.T p) :
    tateToLocal P hp hE hE₀ ((homT (ℓ := p) o).comp φ) =
      toLocal p (j o : B a b) * tateToLocal P hp hE hE₀ φ := by
  let Cmp : (E.T p →ₗ[ℤ_[p]] E₀.T p) →ₗ[ℤ_[p]] (E.T p →ₗ[ℤ_[p]] E₀.T p) :=
    { toFun := fun φ => (homT (ℓ := p) o).comp φ
      map_add' := fun _ _ => LinearMap.comp_add _ _ _
      map_smul' := fun _ _ => LinearMap.comp_smul _ _ _ }
  let Mul : Bp p a b →ₗ[ℤ_[p]] Bp p a b :=
    { toFun := fun y => toLocal p (j o : B a b) * y
      map_add' := fun _ _ => mul_add _ _ _
      map_smul' := fun _ _ => mul_smul_comm _ _ _ }
  let L₁ := (tateToLocal P hp hE hE₀).comp Cmp
  let L₂ := Mul.comp (tateToLocal P hp hE hE₀)
  have h : L₁ = L₂ := by
    apply (tatePlacementBasis P hp hE hE₀).ext
    intro i
    change tateToLocal P hp hE hE₀ ((homT (ℓ := p) o).comp (tatePlacementBasis P hp hE hE₀ i)) =
      toLocal p (j o : B a b) * tateToLocal P hp hE hE₀ (tatePlacementBasis P hp hE hE₀ i)
    rw [tatePlacementBasis_apply]
    change tateToLocal P hp hE hE₀ ((homT (ℓ := p) o).comp (homT (ℓ := p) (P.homBasis i))) = _
    rw [← homT_postcomp]
    change tateToLocal P hp hE hE₀ (tateHom p E E₀ (postcomp o (P.homBasis i))) =
      _ * tateToLocal P hp hE hE₀ (tateHom p E E₀ (P.homBasis i))
    rw [tateToLocal_tateHom, tateToLocal_tateHom, P.map_postcomp, map_mul]
  exact congrArg (fun L => L φ) h

end Tate

section Closure

variable [IsAlgClosed k]

/-- The level test on `k`-points is the test on geometric points. -/
theorem levelHom_iff_closure {A B : PkgI3.AbVar k} (C : Subgroup (A.Pt k))
    (D : Subgroup (B.Pt k)) (f : Hom A B) :
    f ∈ levelHom (L := k) C D ↔
      f ∈ levelHom (C.map (levelPointsToClosure A)) (D.map (levelPointsToClosure B)) := by
  have he (P : A.Pt k) : levelPointsToClosure B (P ≫ f.hom) =
      levelPointsToClosure A P ≫ f.hom := by
    change (geometricPointSourceIso k).hom ≫ (P ≫ f.hom) =
      ((geometricPointSourceIso k).hom ≫ P) ≫ f.hom
    exact (Category.assoc _ _ _).symm
  constructor
  · intro h P hP
    obtain ⟨Q, hQ, rfl⟩ := hP
    exact ⟨Q ≫ f.hom, h Q hQ, he Q⟩
  · intro h P hP
    obtain ⟨Q, hQ, heQ⟩ := h _ ⟨P, hP, rfl⟩
    exact (levelPointsToClosure_injective B (heQ.trans (he P).symm)) ▸ hQ

/-- Restatement of the primary reduction (`HCMV21/GeometricTateChain.lean`,
private there). -/
theorem span_levelHom_eq_span_primary' {A B : PkgI3.AbVar k} (p n r : ℕ) [Fact p.Prime]
    (hr : IsUnit (r : ℤ_[p]))
    (C : Subgroup (A.Pt (AlgebraicClosure k))) (D : Subgroup (B.Pt (AlgebraicClosure k)))
    (hC : ∀ P ∈ C, P ^ (r * p ^ n) = 1) :
    Submodule.span ℤ_[p] (tateHom p A B '' (levelHom C D : Set (Hom A B))) =
      Submodule.span ℤ_[p] (tateHom p A B '' (levelHom (C ⊓ (powMonoidHom (p ^ n)).ker)
        (D ⊓ (powMonoidHom (p ^ n)).ker) : Set (Hom A B))) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨f, fun P hP => ⟨hf P hP.1, ?_⟩, rfl⟩
    change (P ≫ f.hom) ^ (p ^ n) = 1
    have hh : P ^ (p ^ n) = 1 := hP.2
    rw [← MonObj.pow_comp, hh, MonObj.one_comp]
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    have hf' : r • f ∈ levelHom C D := by
      intro P hP
      have hp : P ^ r ∈ C ⊓ (powMonoidHom (p ^ n)).ker :=
        ⟨C.pow_mem hP r, by change (P ^ r) ^ (p ^ n) = 1; rw [← pow_mul]; exact hC P hP⟩
      change P ≫ f.hom ^ r ∈ D
      rw [MonObj.comp_pow, ← MonObj.pow_comp]
      exact (hf (P ^ r) hp).1
    let L := Submodule.span ℤ_[p] (tateHom p A B '' (levelHom C D : Set (Hom A B)))
    have h : tateHom p A B (r • f) ∈ L := Submodule.subset_span ⟨_, hf', rfl⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p]] at h
    have hinv : (↑hr.unit⁻¹ : ℤ_[p]) * (r : ℤ_[p]) = 1 :=
      (congrArg ((↑hr.unit⁻¹ : ℤ_[p]) * ·) hr.unit_spec.symm).trans (Units.inv_mul hr.unit)
    change tateHom p A B f ∈ L
    simpa only [smul_smul, hinv, one_smul] using L.smul_mem (↑hr.unit⁻¹ : ℤ_[p]) h

/-- Restatement of `cyclic_primary` (`HCMV21/ReferenceTateLevel.lean`, private there). -/
theorem cyclic_primary' {G : Type*} [CommGroup G] (P : G) (r s : ℕ)
    (hr : r ≠ 0) (hs : s ≠ 0) (hP : orderOf P = r * s) :
    Subgroup.zpowers P ⊓ (powMonoidHom s).ker = Subgroup.zpowers (P ^ r) := by
  apply le_antisymm
  · intro x hx
    have ht : IsOfFinOrder P := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨r * s, Nat.mul_pos (Nat.pos_of_ne_zero hr) (Nat.pos_of_ne_zero hs),
        hP ▸ pow_orderOf_eq_one P⟩
    obtain ⟨m, rfl⟩ := ht.mem_powers_iff_mem_zpowers.mpr hx.1
    have hm : r * s ∣ m * s := by
      rw [← hP]
      exact orderOf_dvd_of_pow_eq_one (by
        rw [pow_mul]
        exact hx.2)
    obtain ⟨v, rfl⟩ := (Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hs) hm)
    change P ^ (r * v) ∈ Subgroup.zpowers (P ^ r)
    rw [pow_mul]
    exact (Subgroup.zpowers (P ^ r)).pow_mem (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    refine ⟨(Subgroup.zpowers P).pow_mem (Subgroup.mem_zpowers _) _, ?_⟩
    change (P ^ r) ^ s = 1
    rw [← pow_mul, ← hP, pow_orderOf_eq_one]

/-- The completed level Hom lattice between two cyclic enhancements is the
set of integral Tate maps preserving the `p`-primary level preimages. -/
theorem span_levelHom_cyclic {A B : PkgI3.AbVar k} (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)
    (N : ℕ) (hN : N ≠ 0) (PA : A.Pt k) (hPA : orderOf PA = N) (PB : B.Pt k)
    (hPB : orderOf PB = N)
    (hfull : Submodule.span ℤ_[p] (Set.range (tateHom p A B)) = ⊤) :
    let n := N.factorization p
    let r := N / p ^ n
    (Submodule.span ℤ_[p] (tateHom p A B '' (levelHom (L := k) (Subgroup.zpowers PA)
      (Subgroup.zpowers PB) : Set (Hom A B))) : Set (A.T p →ₗ[ℤ_[p]] B.T p)) =
      {φ : A.T p →ₗ[ℤ_[p]] B.T p | Set.MapsTo (⇑φ)
        (tateLevelPreimage A p n (Subgroup.zpowers (levelPointsToClosure A PA ^ r)))
        (tateLevelPreimage B p n (Subgroup.zpowers (levelPointsToClosure B PB ^ r)))} := by
  intro n r
  let QA := levelPointsToClosure A PA
  let QB := levelPointsToClosure B PB
  have hQA : orderOf QA = N :=
    (orderOf_injective (levelPointsToClosure A) (levelPointsToClosure_injective A) PA).trans hPA
  have hQB : orderOf QB = N :=
    (orderOf_injective (levelPointsToClosure B) (levelPointsToClosure_injective B) PB).trans hPB
  have hn : N = r * p ^ n := by
    rw [mul_comm]
    exact (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  have hnd := Nat.not_dvd_ordCompl (Fact.out : p.Prime) hN
  have hr : IsUnit (r : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnd))
  have hr₀ : r ≠ 0 := fun h => hN (by simp [hn, h])
  have hp₀ : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hL : (levelHom (L := k) (Subgroup.zpowers PA) (Subgroup.zpowers PB) : Set (Hom A B)) =
      (levelHom (Subgroup.zpowers QA) (Subgroup.zpowers QB) : Set (Hom A B)) := by
    ext f
    change f ∈ levelHom (L := k) _ _ ↔ f ∈ levelHom _ _
    rw [levelHom_iff_closure, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have hD : ∀ x ∈ Subgroup.zpowers QA, x ^ (r * p ^ n) = 1 := by
    intro x hx
    have hpow : QA ^ N = 1 := hQA ▸ pow_orderOf_eq_one QA
    obtain ⟨m, rfl⟩ := hx
    change (QA ^ m) ^ (r * p ^ n) = 1
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
  rw [hL, span_levelHom_eq_span_primary' p n r hr _ _ hD,
    cyclic_primary' QA r _ hr₀ hp₀ (hQA.trans hn), cyclic_primary' QB r _ hr₀ hp₀ (hQB.trans hn)]
  apply span_levelHom_eq_tateLevelMaps p n hp _ _ _ hfull
  intro x hx
  have hU : orderOf (QA ^ r) = p ^ n := by
    rw [orderOf_pow_of_dvd hr₀ (by rw [hQA, hn]; exact dvd_mul_right _ _), hQA, hn,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr₀)]
  have hpow : (QA ^ r) ^ (p ^ n) = 1 := hU ▸ pow_orderOf_eq_one _
  obtain ⟨m, rfl⟩ := hx
  change ((QA ^ r) ^ m) ^ (p ^ n) = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]

end Closure

/-- A left-invertible element of the local quaternion algebra is a unit. -/
theorem exists_unit_of_left_inverse (p : ℕ) [Fact p.Prime] {v w : Bp p a b} (h : v * w = 1) :
    ∃ u : (Bp p a b)ˣ, (u : Bp p a b) = w := by
  let f : Bp p a b →ₗ[ℚ_[p]] Bp p a b := LinearMap.mulLeft ℚ_[p] w
  have hinj : Function.Injective f := by
    intro x y hxy
    have h' := congrArg (v * ·) hxy
    simpa [f, ← mul_assoc, h] using h'
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  have hx' : w * x = 1 := hx
  have hvx : v = x := by
    calc v = v * (w * x) := by rw [hx', mul_one]
      _ = x := by rw [← mul_assoc, h, one_mul]
  exact ⟨⟨w, x, hx', by rw [← hvx, h]⟩, rfl⟩

end ZInQ.Manuscript.RC.HCMV21
