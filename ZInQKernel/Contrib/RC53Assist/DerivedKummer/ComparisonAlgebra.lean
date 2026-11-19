import ZInQKernel.Contrib.CloudB3RC53.Torsion.ConeRing
import ZInQKernel.Contrib.CloudB3RC53.Torsion.Exists

/-!
# Cohomological comparison, mapping cones, and derived Nakayama

This file supplies the comparison algebra between a perfect residue-cohomology
comparison and the contraction required by derived Nakayama. The cohomology
models below are explicit cycle-class maps with their kernels and surjectivity.
They are identification data, not printed arithmetic leaves. In the Kummer
application the odd comparison is the quotient-to-dual map and the even
comparison is the dual of the retained degree-zero torsion.

No contraction of the reduced cone is assumed in the final theorem. It is
constructed from the two comparisons, using the proved contraction theorem for
exact based complexes over a field.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion

variable {R : Type*} [CommRing R]
  {κe κo κe' κo' : Type*} [Fintype κe] [Fintype κo] [Fintype κe'] [Fintype κo']
  [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo']
  {C : BasedCx R κe κo} {D : BasedCx R κe' κo'}

/-- The cycle-level forms of surjectivity and injectivity of a based chain map
on the two parity cohomology groups. -/
structure CohomologyComparison (f : ChainMapR C D) : Prop where
  liftE : ∀ y : κe' → R, D.dOE *ᵥ y = 0 →
    ∃ x : κe → R, C.dOE *ᵥ x = 0 ∧ ∃ b : κo' → R, f.fE *ᵥ x + D.dEO *ᵥ b = y
  detectE : ∀ x : κe → R, C.dOE *ᵥ x = 0 →
    (∃ b : κo' → R, D.dEO *ᵥ b = f.fE *ᵥ x) → ∃ a : κo → R, C.dEO *ᵥ a = x
  liftO : ∀ y : κo' → R, D.dEO *ᵥ y = 0 →
    ∃ x : κo → R, C.dEO *ᵥ x = 0 ∧ ∃ b : κe' → R, f.fO *ᵥ x + D.dOE *ᵥ b = y
  detectO : ∀ x : κo → R, C.dEO *ᵥ x = 0 →
    (∃ b : κe' → R, D.dOE *ᵥ b = f.fO *ᵥ x) → ∃ a : κe → R, C.dOE *ᵥ a = x

/-- A chain map bijective on cohomology has exact mapping cone. This theorem is
valid over a commutative ring; the field assumption is only needed to contract
that exact cone. -/
theorem coneR_isExact_of_cohomology (f : ChainMapR C D) (h : CohomologyComparison f) :
    (BasedCx.coneR f).IsExact := by
  constructor
  · intro z hz
    let y : κe' → R := z ∘ Sum.inl
    let x : κo → R := z ∘ Sum.inr
    change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ z = 0 at hz
    rw [fromBlocks_mulVec] at hz
    have h₁ : D.dOE *ᵥ y + f.fO *ᵥ x = 0 := by
      funext i
      exact congrFun hz (Sum.inl i)
    have h₂ : C.dEO *ᵥ x = 0 := by
      apply neg_eq_zero.mp
      funext i
      simpa [x, neg_mulVec] using congrFun hz (Sum.inr i)
    obtain ⟨a, ha⟩ := h.detectO x h₂ ⟨-y, by
      rw [mulVec_neg, neg_eq_iff_add_eq_zero]
      exact h₁⟩
    have hcy : D.dOE *ᵥ (y + f.fE *ᵥ a) = 0 := by
      rw [mulVec_add, mulVec_mulVec, f.commOE, ← mulVec_mulVec, ha]
      exact h₁
    obtain ⟨c, hc, b, hb⟩ := h.liftE (y + f.fE *ᵥ a) hcy
    have htop : D.dEO *ᵥ b + f.fE *ᵥ (c - a) = y := by
      calc
        D.dEO *ᵥ b + f.fE *ᵥ (c - a) = (f.fE *ᵥ c + D.dEO *ᵥ b) - f.fE *ᵥ a := by
          rw [mulVec_sub]
          abel
        _ = y := by rw [hb]; abel
    have hbottom : -(C.dOE *ᵥ (c - a)) = x := by
      rw [mulVec_sub, hc, ha, zero_sub, neg_neg]
    refine ⟨Sum.elim b (c - a), ?_⟩
    change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ Sum.elim b (c - a) = z
    rw [fromBlocks_mulVec]
    funext i
    rcases i with i | i
    · exact congrFun htop i
    · simpa [x, neg_mulVec] using congrFun hbottom i
  · intro z hz
    let y : κo' → R := z ∘ Sum.inl
    let x : κe → R := z ∘ Sum.inr
    change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ z = 0 at hz
    rw [fromBlocks_mulVec] at hz
    have h₁ : D.dEO *ᵥ y + f.fE *ᵥ x = 0 := by
      funext i
      exact congrFun hz (Sum.inl i)
    have h₂ : C.dOE *ᵥ x = 0 := by
      apply neg_eq_zero.mp
      funext i
      simpa [x, neg_mulVec] using congrFun hz (Sum.inr i)
    obtain ⟨a, ha⟩ := h.detectE x h₂ ⟨-y, by
      rw [mulVec_neg, neg_eq_iff_add_eq_zero]
      exact h₁⟩
    have hcy : D.dEO *ᵥ (y + f.fO *ᵥ a) = 0 := by
      rw [mulVec_add, mulVec_mulVec, f.commEO, ← mulVec_mulVec, ha]
      exact h₁
    obtain ⟨c, hc, b, hb⟩ := h.liftO (y + f.fO *ᵥ a) hcy
    have htop : D.dOE *ᵥ b + f.fO *ᵥ (c - a) = y := by
      calc
        D.dOE *ᵥ b + f.fO *ᵥ (c - a) = (f.fO *ᵥ c + D.dOE *ᵥ b) - f.fO *ᵥ a := by
          rw [mulVec_sub]
          abel
        _ = y := by rw [hb]; abel
    have hbottom : -(C.dEO *ᵥ (c - a)) = x := by
      rw [mulVec_sub, hc, ha, zero_sub, neg_neg]
    refine ⟨Sum.elim b (c - a), ?_⟩
    change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ Sum.elim b (c - a) = z
    rw [fromBlocks_mulVec]
    funext i
    rcases i with i | i
    · exact congrFun htop i
    · simpa [x, neg_mulVec] using congrFun hbottom i

/-- The even cycles of a based complex. -/
def cyclesE (C : BasedCx R κe κo) : Submodule R (κe → R) :=
  LinearMap.ker (Matrix.mulVecLin C.dOE)

/-- The odd cycles of a based complex. -/
def cyclesO (C : BasedCx R κe κo) : Submodule R (κo → R) :=
  LinearMap.ker (Matrix.mulVecLin C.dEO)

/-- The map on even cycles induced by a based chain map. -/
def cycleMapE (f : ChainMapR C D) : cyclesE C →ₗ[R] cyclesE D :=
  ((Matrix.mulVecLin f.fE).domRestrict (cyclesE C)).codRestrict (cyclesE D) (fun x => by
    change D.dOE *ᵥ (f.fE *ᵥ x.val) = 0
    rw [mulVec_mulVec, f.commOE, ← mulVec_mulVec]
    have hx : C.dOE *ᵥ x.val = 0 := x.2
    rw [hx, mulVec_zero])

/-- The map on odd cycles induced by a based chain map. -/
def cycleMapO (f : ChainMapR C D) : cyclesO C →ₗ[R] cyclesO D :=
  ((Matrix.mulVecLin f.fO).domRestrict (cyclesO C)).codRestrict (cyclesO D) (fun x => by
    change D.dEO *ᵥ (f.fO *ᵥ x.val) = 0
    rw [mulVec_mulVec, f.commEO, ← mulVec_mulVec]
    have hx : C.dEO *ᵥ x.val = 0 := x.2
    rw [hx, mulVec_zero])

/-- Explicit cohomology identifications: the class maps are onto and their
kernels are precisely boundaries. In the actual local application HE and HO
are the degree-two and degree-one groups, respectively; no other cohomology
is allowed to disappear without being accounted for by the kernel assertions. -/
structure CohomologyModel (C : BasedCx R κe κo) (HE HO : Type*)
    [AddCommGroup HE] [Module R HE] [AddCommGroup HO] [Module R HO] where
  classE : cyclesE C →ₗ[R] HE
  ontoE : Function.Surjective classE
  kernelE : ∀ x, classE x = 0 ↔ ∃ b : κo → R, C.dEO *ᵥ b = x.val
  classO : cyclesO C →ₗ[R] HO
  ontoO : Function.Surjective classO
  kernelO : ∀ x, classO x = 0 ↔ ∃ b : κe → R, C.dOE *ᵥ b = x.val

variable {HE HO HE' HO' : Type*}
  [AddCommGroup HE] [Module R HE] [AddCommGroup HO] [Module R HO]
  [AddCommGroup HE'] [Module R HE'] [AddCommGroup HO'] [Module R HO']

/-- Bijective comparisons of the identified cohomology groups supply the four
cycle-level properties needed for an exact comparison cone. The commuting
squares specify the actual map induced on cohomology. -/
theorem comparison_of_models (f : ChainMapR C D)
    (M : CohomologyModel C HE HO) (N : CohomologyModel D HE' HO')
    (αE : HE →ₗ[R] HE') (αO : HO →ₗ[R] HO')
    (hE : Function.Bijective αE) (hO : Function.Bijective αO)
    (commE : ∀ x, N.classE (cycleMapE f x) = αE (M.classE x))
    (commO : ∀ x, N.classO (cycleMapO f x) = αO (M.classO x)) :
    CohomologyComparison f := by
  constructor
  · intro y hy
    let z : cyclesE D := ⟨y, hy⟩
    obtain ⟨a, ha⟩ := hE.2 (N.classE z)
    obtain ⟨x, hx⟩ := M.ontoE a
    have hz : N.classE (z - cycleMapE f x) = 0 := by
      rw [map_sub, commE, hx, ha, sub_self]
    obtain ⟨b, hb⟩ := (N.kernelE _).1 hz
    refine ⟨x.val, x.2, b, ?_⟩
    change D.dEO *ᵥ b = y - f.fE *ᵥ x.val at hb
    rw [hb]
    abel
  · intro x hx hb
    let z : cyclesE C := ⟨x, hx⟩
    have hz : N.classE (cycleMapE f z) = 0 := (N.kernelE _).2 hb
    have hzero : M.classE z = 0 := hE.1 (by
      rw [map_zero]
      exact (commE z).symm.trans hz)
    exact (M.kernelE z).1 hzero
  · intro y hy
    let z : cyclesO D := ⟨y, hy⟩
    obtain ⟨a, ha⟩ := hO.2 (N.classO z)
    obtain ⟨x, hx⟩ := M.ontoO a
    have hz : N.classO (z - cycleMapO f x) = 0 := by
      rw [map_sub, commO, hx, ha, sub_self]
    obtain ⟨b, hb⟩ := (N.kernelO _).1 hz
    refine ⟨x.val, x.2, b, ?_⟩
    change D.dOE *ᵥ b = y - f.fO *ᵥ x.val at hb
    rw [hb]
    abel
  · intro x hx hb
    let z : cyclesO C := ⟨x, hx⟩
    have hz : N.classO (cycleMapO f z) = 0 := (N.kernelO _).2 hb
    have hzero : M.classO z = 0 := hO.1 (by
      rw [map_zero]
      exact (commO z).symm.trans hz)
    exact (M.kernelO z).1 hzero

/-- Over a field, the exact comparison cone has a contraction. -/
theorem contraction_of_cohomology {K : Type*} [Field K]
    {C : BasedCx K κe κo} {D : BasedCx K κe' κo'}
    (f : ChainMapR C D) (h : CohomologyComparison f) :
    Nonempty (Contraction (BasedCx.coneR f)) :=
  exists_contraction _ (coneR_isExact_of_cohomology f h)

section Nakayama

variable [IsLocalRing R]
  {C : BasedCx R κe κo} {D : BasedCx R κe' κo'}
  {VE VO VE' VO' : Type*}
  [AddCommGroup VE] [Module (IsLocalRing.ResidueField R) VE]
  [AddCommGroup VO] [Module (IsLocalRing.ResidueField R) VO]
  [AddCommGroup VE'] [Module (IsLocalRing.ResidueField R) VE']
  [AddCommGroup VO'] [Module (IsLocalRing.ResidueField R) VO']

/-- Derived Nakayama with its reduced-cone hypothesis proved from the two
perfect cohomology comparisons and their actual cycle-class identifications. -/
theorem nakayama_comparison_of_models (f : ChainMapR C D)
    (M : CohomologyModel (C.map (IsLocalRing.residue R)) VE VO)
    (N : CohomologyModel (D.map (IsLocalRing.residue R)) VE' VO')
    (αE : VE →ₗ[IsLocalRing.ResidueField R] VE')
    (αO : VO →ₗ[IsLocalRing.ResidueField R] VO')
    (hE : Function.Bijective αE) (hO : Function.Bijective αO)
    (commE : ∀ x, N.classE (cycleMapE (f.map (IsLocalRing.residue R)) x) = αE (M.classE x))
    (commO : ∀ x, N.classO (cycleMapO (f.map (IsLocalRing.residue R)) x) = αO (M.classO x)) :
    Nonempty (Contraction (BasedCx.coneR f)) := by
  obtain ⟨hbar⟩ := contraction_of_cohomology (f.map (IsLocalRing.residue R))
    (comparison_of_models _ M N αE αO hE hO commE commO)
  exact nakayama_comparison f hbar

end Nakayama

section ModTwoNakayama

/-- Change of coefficients of a contraction. -/
def contraction_map {S : Type*} [CommRing S] (π : R →+* S)
    {C : BasedCx R κe κo} (h : Contraction C) : Contraction (C.map π) where
  hOE := h.hOE.map π
  hEO := h.hEO.map π
  deg_hOE i j hij := h.deg_hOE i j (fun h0 => hij (by simp [h0]))
  deg_hEO i j hij := h.deg_hEO i j (fun h0 => hij (by simp [h0]))
  htpy_E := by
    change C.dEO.map π * h.hOE.map π + h.hEO.map π * C.dOE.map π = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π), h.htpy_E]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  htpy_O := by
    change C.dOE.map π * h.hEO.map π + h.hOE.map π * C.dEO.map π = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π), h.htpy_O]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- Coefficient change of a based complex is functorial. -/
theorem based_map_comp {S T : Type*} [CommRing S] [CommRing T]
    (C : BasedCx R κe κo) (π : R →+* S) (ρ : S →+* T) :
    (C.map π).map ρ = C.map (ρ.comp π) := rfl

/-- The residue map of Z₂ is the canonical mod-two map followed by the inverse
of the canonical residue-field identification. -/
theorem residue_eq_comp_modTwo :
    (PadicInt.residueField (p := 2)).symm.toRingHom.comp (PadicInt.toZMod (p := 2)) =
      IsLocalRing.residue ℤ_[2] := by
  ext z
  change (PadicInt.residueField (p := 2)).symm (PadicInt.toZMod z) =
    IsLocalRing.residue ℤ_[2] z
  rw [PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply]
  exact (PadicInt.residueField (p := 2)).symm_apply_apply _

/-- A contraction modulo two supplies the contraction over the residue field
used in derived Nakayama; no unsupported identification of the two fields is
assumed. -/
def residueContractionOfModTwo {C : BasedCx ℤ_[2] κe κo}
    (h : Contraction (C.map (PadicInt.toZMod (p := 2)))) :
    Contraction (C.map (IsLocalRing.residue ℤ_[2])) := by
  have h' := contraction_map (PadicInt.residueField (p := 2)).symm.toRingHom h
  rw [based_map_comp, residue_eq_comp_modTwo] at h'
  exact h'

/-- The comparison form of derived Nakayama with its input expressed over
F₂, as in the manuscript. -/
theorem nakayama_comparison_modTwo
    {C : BasedCx ℤ_[2] κe κo} {D : BasedCx ℤ_[2] κe' κo'}
    (f : ChainMapR C D)
    (hbar : Contraction (BasedCx.coneR (f.map (PadicInt.toZMod (p := 2))))) :
    Nonempty (Contraction (BasedCx.coneR f)) :=
  nakayama_contraction _ (residueContractionOfModTwo
    ((coneR_map (PadicInt.toZMod (p := 2)) f).symm ▸ hbar))

variable {VE VO VE' VO' : Type*}
  [AddCommGroup VE] [Module (ZMod 2) VE] [AddCommGroup VO] [Module (ZMod 2) VO]
  [AddCommGroup VE'] [Module (ZMod 2) VE'] [AddCommGroup VO'] [Module (ZMod 2) VO']

/-- The final Z₂ comparison theorem: two bijective F₂ cohomology comparisons,
identified with the actual reduced chain map by the two commuting squares,
produce an integral contraction of its cone. -/
theorem nakayama_comparison_of_modTwo_models
    {C : BasedCx ℤ_[2] κe κo} {D : BasedCx ℤ_[2] κe' κo'} (f : ChainMapR C D)
    (M : CohomologyModel (C.map (PadicInt.toZMod (p := 2))) VE VO)
    (N : CohomologyModel (D.map (PadicInt.toZMod (p := 2))) VE' VO')
    (αE : VE →ₗ[ZMod 2] VE') (αO : VO →ₗ[ZMod 2] VO')
    (hE : Function.Bijective αE) (hO : Function.Bijective αO)
    (commE : ∀ x, N.classE (cycleMapE (f.map (PadicInt.toZMod (p := 2))) x) = αE (M.classE x))
    (commO : ∀ x, N.classO (cycleMapO (f.map (PadicInt.toZMod (p := 2))) x) = αO (M.classO x)) :
    Nonempty (Contraction (BasedCx.coneR f)) := by
  obtain ⟨hbar⟩ := contraction_of_cohomology (f.map (PadicInt.toZMod (p := 2)))
    (comparison_of_models _ M N αE αO hE hO commE commO)
  exact nakayama_comparison_modTwo f hbar

end ModTwoNakayama

end ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison
