import ZInQKernel.Contrib.OneProof.RC.HCMV21.VoightCandidates
import ZInQKernel.Contrib.OneProof.RC.HCMV21.PrimeToRepresentative
import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricRightIdeal

/-! Placements of `Hom(E, E₀)` in the rational quaternion algebra. Any two
placements differ by right multiplication by a rational unit, so the left ideal
class of the image does not depend on the placement; placements transport along
isomorphisms. The level-`N` Hom lattice of maps sending `C` into `C₀` is a full
left ideal of the enhanced reference order, locally equal to the level-one ideal
at every prime not dividing `N`. All proofs are Lean proofs. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] {a b : ℚ} {E₀ E E' : PkgI3.AbVar k}
  {S : Order a b} {j : E₀.End ≃+* S.ring}

namespace HomPlacement

theorem mem_ideal (P : HomPlacement S j E) (α : Hom E E₀) : P.emb α ∈ P.ideal.val.lattice := by
  have h : P.emb α ∈ (P.ideal.val.lattice : Set (B a b)) := by
    rw [P.range_eq]
    exact ⟨α, rfl⟩
  exact h

theorem exists_of_mem (P : HomPlacement S j E) {x : B a b} (hx : x ∈ P.ideal.val.lattice) :
    ∃ α, P.emb α = x := by
  have h : x ∈ (P.ideal.val.lattice : Set (B a b)) := hx
  rw [P.range_eq] at h
  exact h

private theorem zsmul_cancel {x y : B a b} {e : ℤ} (he : e ≠ 0) (h : e • x = e • y) : x = y := by
  rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ] at h
  exact smul_right_injective _ (Int.cast_ne_zero.mpr he) h

/-- Every additive `O₀`-linear map from `Hom(E, E₀)` to `B` is the placement
followed by right multiplication by one element. -/
theorem exists_mul_right (P : HomPlacement S j E) (g : Hom E E₀ →+ B a b)
    (hg : ∀ (o : E₀.End) (α : Hom E E₀), g (postcomp o α) = (j o : B a b) * g α) :
    ∃ x : B a b, ∀ α, g α = P.emb α * x := by
  let b₀ := QuaternionAlgebra.basisOneIJK a 0 b
  obtain ⟨d, hd, hdS⟩ := FullLattice.multiple_mem S.full P.ideal.val.full b₀
  obtain ⟨α₀, hα₀⟩ := P.exists_of_mem (hdS 1 S.ring.one_mem)
  refine ⟨(d : ℚ)⁻¹ • g α₀, fun α => ?_⟩
  obtain ⟨e, he, heS⟩ := FullLattice.multiple_mem P.ideal.val.full S.full b₀
  have hmem : e • P.emb α ∈ S.ring := heS _ (P.mem_ideal α)
  let o := j.symm ⟨e • P.emb α, hmem⟩
  have ho : (j o : B a b) = e • P.emb α := by
    simp only [o, RingEquiv.apply_symm_apply]
  have h1 : postcomp o α₀ = (e * d) • α := by
    apply P.injective
    rw [P.map_postcomp, ho, hα₀, map_zsmul, smul_mul_smul_comm, mul_one, mul_comm]
  have h2 := congrArg g h1
  rw [hg, ho, map_zsmul, mul_comm e d, mul_smul] at h2
  have h3 : d • g α = P.emb α * g α₀ := by
    apply zsmul_cancel he
    rw [smul_comm e d, ← h2, smul_mul_assoc]
  have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  rw [mul_smul_comm, ← h3, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hd', one_smul]

/-- Two placements of the same `Hom(E, E₀)` differ by right multiplication by
a rational unit of the definite algebra. -/
theorem exists_unit (ha : a < 0) (hb : b < 0) (P P' : HomPlacement S j E) :
    ∃ u : (B a b)ˣ, ∀ α, P'.emb α = P.emb α * u := by
  obtain ⟨x, hx⟩ := P.exists_mul_right P'.emb P'.map_postcomp
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨y, hy, hy0⟩ := P'.ideal.val.exists_ne_zero
    obtain ⟨α, rfl⟩ := P'.exists_of_mem hy
    exact hy0 (by rw [hx, mul_zero])
  exact ⟨unitOfNeZero ha hb x hx0, hx⟩

/-- Right translation of a placement by a rational unit. -/
def translate (P : HomPlacement S j E) (u : (B a b)ˣ)
    (hu : (P.ideal.val.translate u).LocallyPrincipal) : HomPlacement S j E where
  emb := (AddMonoidHom.mulRight (u : B a b)).comp P.emb
  injective α β h := P.injective (by
    simpa using congrArg (· * (↑u⁻¹ : B a b)) h)
  map_postcomp o α := by
    change P.emb (postcomp o α) * u = _ * (P.emb α * u)
    rw [P.map_postcomp, mul_assoc]
  ideal := ⟨P.ideal.val.translate u, hu⟩
  range_eq := by
    ext x
    change x ∈ (P.ideal.val.translate u).lattice ↔ _
    rw [LeftIdeal.mem_translate]
    constructor
    · intro h
      obtain ⟨α, hα⟩ := P.exists_of_mem h
      exact ⟨α, by simp [hα, mul_assoc]⟩
    · rintro ⟨α, rfl⟩
      simpa [mul_assoc] using P.mem_ideal α

/-- Transport a placement along an isomorphism `E ≅ E′`. -/
def transport (P : HomPlacement S j E') (f : Hom E E') (g : Hom E' E)
    (hfg : f.hom ≫ g.hom = 𝟙 _) (hgf : g.hom ≫ f.hom = 𝟙 _) : HomPlacement S j E where
  emb := P.emb.comp (homPull g)
  injective α β h := by
    have h' := congrArg Hom.hom (congrArg (homPull f) (P.injective h))
    simp only [homPull_hom] at h'
    rw [← Category.assoc, ← Category.assoc, hfg, Category.id_comp, Category.id_comp] at h'
    exact Hom.ext' h'
  map_postcomp o α := by
    change P.emb (homPull g (postcomp o α)) = _ * P.emb (homPull g α)
    rw [← P.map_postcomp]
    congr 1
  ideal := P.ideal
  range_eq := by
    rw [P.range_eq]
    ext x
    constructor
    · rintro ⟨β, rfl⟩
      refine ⟨homPull f β, ?_⟩
      change P.emb (homPull g (homPull f β)) = P.emb β
      congr 1
      apply Hom.ext'
      simp [homPull, ← Category.assoc, hgf]
    · rintro ⟨α, rfl⟩
      exact ⟨homPull g α, rfl⟩

end HomPlacement

theorem LeftIdeal.locallyPrincipal_translate {R : Order a b} (I : LeftIdeal R)
    (hI : I.LocallyPrincipal) (u : (B a b)ˣ) : (I.translate u).LocallyPrincipal := by
  intro p _
  obtain ⟨v, hv⟩ := hI p
  let up := Units.map (toLocal p).toMonoidHom u
  refine ⟨v * up, ?_⟩
  have he : (localLattice p (I.translate u).lattice : Set (Bp p a b)) =
      (fun x : Bp p a b => x * (up : Bp p a b)) '' (localLattice p I.lattice : Set _) := by
    let f : Bp p a b →ₗ[ℤ_[p]] Bp p a b :=
      { toFun := fun x => x * (up : Bp p a b)
        map_add' := fun x y => add_mul _ _ _
        map_smul' := fun r x => smul_mul_assoc _ _ _ }
    have hloc : localLattice p (I.translate u).lattice = (localLattice p I.lattice).map f := by
      unfold localLattice
      rw [Submodule.map_span]
      change Submodule.span ℤ_[p] (toLocal p ''
        (I.lattice.map ((mulRightEquiv u).restrictScalars ℤ).toLinearMap : Set (B a b))) = _
      rw [Submodule.map_coe, Set.image_image, Set.image_image]
      congr 2
    rw [hloc, Submodule.map_coe]
    rfl
  rw [he, hv, Set.image_image]
  simp only [Units.val_mul, mul_assoc]

section Level

variable {C : Subgroup (E.Pt k)} {C₀ : Subgroup (E₀.Pt k)} {N : ℕ}

/-- The placed level-`N` Hom lattice: the image of the maps sending `C` into `C₀`. -/
def levelLattice (P : HomPlacement S j E) (C : Subgroup (E.Pt k)) (C₀ : Subgroup (E₀.Pt k)) :
    Submodule ℤ (B a b) :=
  (levelHom (L := k) C C₀).toIntSubmodule.map P.emb.toIntLinearMap

theorem mem_levelLattice (P : HomPlacement S j E) (x : B a b) :
    x ∈ levelLattice P C C₀ ↔ ∃ α ∈ levelHom (L := k) C C₀, P.emb α = x :=
  Iff.rfl

theorem levelLattice_le (P : HomPlacement S j E) :
    levelLattice P C C₀ ≤ P.ideal.val.lattice := by
  rintro _ ⟨α, -, rfl⟩
  exact P.mem_ideal α

theorem nsmul_mem_levelHom (hC : ∀ x ∈ C, x ^ N = 1) (α : Hom E E₀) :
    N • α ∈ levelHom (L := k) C C₀ := by
  intro x hx
  change x ≫ (N • α).hom ∈ C₀
  rw [show (N • α).hom = α.hom ^ N from rfl, MonObj.comp_pow, ← MonObj.pow_comp, hC x hx,
    MonObj.one_comp]
  exact C₀.one_mem

theorem postcomp_mem_levelHom {o : E₀.End} (ho : o ∈ levelEnd E₀ C₀) {α : Hom E E₀}
    (hα : α ∈ levelHom (L := k) C C₀) : postcomp o α ∈ levelHom (L := k) C C₀ := by
  intro x hx
  change x ≫ (α.hom ≫ o.hom) ∈ C₀
  rw [← Category.assoc]
  exact ho _ (hα x hx)

/-- The placed level-`N` Hom lattice is a full left ideal of the enhanced
reference order. -/
def levelIdeal (P : HomPlacement S j E) (C₀ : Subgroup (E₀.Pt k)) (hN : N ≠ 0)
    (hC₀ : ∀ x ∈ C₀, x ^ N = 1) (C : Subgroup (E.Pt k)) (hC : ∀ x ∈ C, x ^ N = 1) :
    LeftIdeal (levelOrderOfEndOrder S j C₀ N hN hC₀) where
  lattice := levelLattice P C C₀
  full := by
    refine ⟨P.ideal.val.full.fg.of_le (levelLattice_le P), ?_⟩
    apply top_unique
    rw [← P.ideal.val.full.span_eq_top]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨α, rfl⟩ := P.exists_of_mem hx
    have hm : P.emb (N • α) ∈ Submodule.span ℚ (levelLattice P C C₀ : Set (B a b)) :=
      Submodule.subset_span ⟨_, nsmul_mem_levelHom hC α, rfl⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at hm
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    simpa [smul_smul, inv_mul_cancel₀ hN'] using
      Submodule.smul_mem _ ((N : ℚ)⁻¹) hm
  mul_mem := by
    rintro _ _ ⟨o, ho, rfl⟩ ⟨α, hα, rfl⟩
    refine ⟨postcomp o α, postcomp_mem_levelHom ho hα, ?_⟩
    change P.emb (postcomp o α) = (j o : B a b) * P.emb α
    exact P.map_postcomp o α

/-- Away from the level the placed level ideal has the completion of the
level-one ideal. -/
theorem localLattice_levelLattice_eq (P : HomPlacement S j E) (hC : ∀ x ∈ C, x ^ N = 1)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (N : ℤ_[p])) :
    localLattice p (levelLattice P C C₀) = localLattice p P.ideal.val.lattice := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono (levelLattice_le P))
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨α, rfl⟩ := P.exists_of_mem hx
    have hm : toLocal p (P.emb (N • α)) ∈ localLattice p (levelLattice P C C₀) :=
      Submodule.subset_span ⟨_, ⟨N • α, nsmul_mem_levelHom hC α, rfl⟩, rfl⟩
    rw [map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p]] at hm
    have hinv : (↑hp.unit⁻¹ : ℤ_[p]) * (N : ℤ_[p]) = 1 :=
      (congrArg ((↑hp.unit⁻¹ : ℤ_[p]) * ·) hp.unit_spec.symm).trans (Units.inv_mul hp.unit)
    have h2 : toLocal p (P.emb α) ∈ localLattice p (levelLattice P C C₀) := by
      simpa only [smul_smul, hinv, one_smul] using
        (localLattice p (levelLattice P C C₀)).smul_mem (↑hp.unit⁻¹ : ℤ_[p]) hm
    exact h2

/-- Away from the level the placed level ideal is principal over the
enhanced order. -/
theorem levelIdeal_locallyPrincipal_away (P : HomPlacement S j E) (C₀ : Subgroup (E₀.Pt k))
    (hN : N ≠ 0) (hC₀ : ∀ x ∈ C₀, x ^ N = 1) (hC : ∀ x ∈ C, x ^ N = 1)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (N : ℤ_[p])) :
    ∃ u : (Bp p a b)ˣ,
      (localLattice p (levelIdeal P C₀ hN hC₀ C hC).lattice : Set (Bp p a b)) =
        (fun x : Bp p a b => x * (u : Bp p a b)) ''
          ((levelOrderOfEndOrder S j C₀ N hN hC₀).completion p : Set (Bp p a b)) := by
  obtain ⟨u, hu⟩ := P.ideal.prop p
  refine ⟨u, ?_⟩
  change (localLattice p (levelLattice P C C₀) : Set (Bp p a b)) = _
  rw [localLattice_levelLattice_eq P hC p hp, hu,
    levelOrderOfEndOrder_completion_eq S j C₀ N hN hC₀ p hp]

/-- Transporting a placement along an isomorphism carrying `C` onto `C'`
keeps the placed level lattice. -/
theorem levelLattice_transport (P : HomPlacement S j E') (f : Hom E E') (g : Hom E' E)
    (hfg : f.hom ≫ g.hom = 𝟙 _) (hgf : g.hom ≫ f.hom = 𝟙 _) (C : Subgroup (E.Pt k))
    (C' : Subgroup (E'.Pt k)) (hC : C.map (ptMap (L := k) f) = C') :
    levelLattice (P.transport f g hfg hgf) C C₀ = levelLattice P C' C₀ := by
  have hC' : C'.map (ptMap (L := k) g) = C := by
    rw [← hC, Subgroup.map_map, ← ptMap_mk'_comp]
    have h : (Hom.mk' (f.hom ≫ g.hom) : Hom E E) = Hom.mk' (𝟙 _) := Hom.ext' hfg
    rw [h, ptMap_mk'_id, Subgroup.map_id]
  ext x
  constructor
  · rintro ⟨α, hα, rfl⟩
    refine ⟨homPull g α, ?_, rfl⟩
    intro y hy
    change y ≫ (g.hom ≫ α.hom) ∈ C₀
    rw [← Category.assoc]
    have hy' : y ≫ g.hom ∈ C := by
      rw [← hC']
      exact ⟨y, hy, rfl⟩
    exact hα _ hy'
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨homPull f β, ?_, ?_⟩
    · intro y hy
      change y ≫ (f.hom ≫ β.hom) ∈ C₀
      rw [← Category.assoc]
      have hy' : y ≫ f.hom ∈ C' := by
        rw [← hC]
        exact ⟨y, hy, rfl⟩
      exact hβ _ hy'
    · change P.emb (homPull g (homPull f β)) = P.emb β
      congr 1
      apply Hom.ext'
      simp [homPull, ← Category.assoc, hgf]

/-- Right translation of a placement translates the placed level lattice. -/
theorem levelLattice_translate (P : HomPlacement S j E) (u : (B a b)ˣ)
    (hu : (P.ideal.val.translate u).LocallyPrincipal) :
    levelLattice (P.translate u hu) C C₀ =
      (levelLattice P C C₀).map ((mulRightEquiv u).restrictScalars ℤ).toLinearMap := by
  ext x
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨P.emb α, ⟨α, hα, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    exact ⟨α, hα, rfl⟩

end Level

end ZInQ.Manuscript.RC.HCMV21
