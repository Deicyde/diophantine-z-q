import ZInQKernel.Contrib.OneProof.H.D2A6Chain
import ZInQKernel.Contrib.OneProof.NeronOggShafarevich

/-! # Good reduction implies trivial inertia on prime-to-residue-characteristic torsion

The kernel field (diophantine_zq.tex L557–560) and A6/G11 (L752–753) use only this implication.
The proofs below carry that implication through the two readers. The perfect-residue-field
criterion records the reported print hypothesis; the bypass does not assume it.
-/

set_option linter.style.longLine false
set_option linter.style.haveILetI false

namespace NOSNarrow

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety HasGoodReduction InertiaTrivialOn)

/-- Print-form record (UNVERIFIED): Serre–Tate §1 assumes a perfect residue field
(recalled, and so described in Milne's survey, arXiv:1210.7459 §2.7; the paper itself
was not read). BLR §7.4 Thm 5 gives the Tate-module form over any discrete valuation
ring (UNVERIFIED). Serre–Tate 1968 is absent from the manuscript's bibliography
(diophantine_zq.tex L11009–11247). The two torsion equivalences use a separable
closure and the same definitions as `NOSSepDict.NeronOggShafarevichSep`. -/
def NeronOggShafarevichSepPerfect : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ks : Type) [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
    (w : ValuationSubring Ks), w.comap (algebraMap K Ks) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)

theorem perfect_of_sep (h : NOSSepDict.NeronOggShafarevichSep) : NeronOggShafarevichSepPerfect :=
  fun K _ O _ _ Ks _ _ _ w hw A _ => h K O Ks w hw A

/-- The uncited implication used at diophantine_zq.tex L557–559 and L752–753 (provenance (a)). -/
def NOSForward : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      HasGoodReduction A O → ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m

theorem nosForward_proof : NOSForward :=
  fun _ _ O _ w hw A _ => NOSProof.inertiaTrivialOn_of_goodReduction O w hw A

theorem nosForward_of_r7a (h : PkgI2.NeronOggShafarevich.{0}) : NOSForward :=
  fun K _ O _ w hw A _ => (h K O w hw A).1.mp

end NOSNarrow

-- copied from ZInQKernel/Contrib/OneProof/H/TailC.lean:5203 (point_fixed)
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
section PartInertia
namespace G4WeilRes
open GlueB3Unram CategoryTheory AlgebraicGeometry Limits MonObj PkgI3 PkgI3.AbVar InertiaHoms
variable (K : IntermediateField ℚ Qbar)
/-- Transport prime-to-residue-characteristic torsion triviality along the embedding. -/
theorem point_fixed_nos (hF : _root_.NOSNarrow.NOSForward)
    (A : AbVar K) (e : K →ₐ[ℚ] Qbar) (w : ValuationSubring Qbar)
    [IsDiscreteValuationRing (w.comap (e : K →+* Qbar))]
    (hgood : PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar)))
    (s : Gal) (hs : s ∈ inertiaGQ w) (hse : ∀ x, s (e x) = e x)
    (m : ℕ) (hm : 0 < m) (hmO : IsUnit ((m : ℕ) : w.comap (e : K →+* Qbar)))
    (q : CategoryTheory.Over.mk (specEmb K e) ⟶ A.X) (hq : q ^ m = 1) :
    specGal s ≫ q.left = q.left := by
  obtain ⟨ie, hie⟩ := exists_closure_equiv K e
  have hies : ∀ x : K, ie.symm (e x) = algebraMap K (AlgebraicClosure K) x := fun x => by
    rw [← hie, RingEquiv.symm_apply_apply]
  let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := (ie.trans s.toRingEquiv).trans ie.symm) (fun x => by
      simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hie, hse, hies])
  have hσ : ∀ x, σ x = ie.symm (s (ie x)) := fun x => rfl
  let w' : ValuationSubring (AlgebraicClosure K) := w.comap (ie : AlgebraicClosure K →+* Qbar)
  have hw' : w'.comap (algebraMap K (AlgebraicClosure K)) = w.comap (e : K →+* Qbar) := by
    ext x
    simp only [w', ValuationSubring.mem_comap, RingEquiv.coe_toRingHom]
    rw [hie]
    rfl
  have hsI : (∀ x, s x ∈ w ↔ x ∈ w) ∧ (∀ x ∈ w, s x - x = 0 ∨ (s x - x)⁻¹ ∉ w) := by
    obtain ⟨g, hg, hgs⟩ := Subgroup.mem_map.mp hs
    have := (isInertia_iff w g.1).mp ⟨g.2, hg⟩
    rw [← hgs]
    exact this
  have hIσ : PkgI2.IsInertia w' σ := by
    rw [PkgI2.IsInertia, isInertia_iff]
    exact inertia_transport ie w s.toRingEquiv hsI.1 hsI.2
  let J : PkgI2.specOver K (AlgebraicClosure K) ⟶ CategoryTheory.Over.mk (specEmb K e) :=
    CategoryTheory.Over.homMk
      (Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K))) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [specMap_comp]
        congr 2
        ext x
        exact hies x)
  let x : PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure K) := J ≫ q
  have hx : x ∈ PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure K) m := by
    show (J ≫ q) ^ m = 1
    rw [← MonObj.comp_pow, hq, MonObj.comp_one]
  have hfix := (hF K (w.comap (e : K →+* Qbar)) w' hw' (ObjBridge.toGrp A) hgood)
    m hm hmO σ hIσ x hx
  have h2 : Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
      Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K)) ≫ q.left =
      Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K)) ≫ q.left := by
    have := congrArg (fun t => Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      CategoryTheory.Over.Hom.left t) hfix
    exact this
  rw [← Category.assoc, ← Category.assoc, specMap_comp, specMap_comp, ← Category.assoc,
    specMap_comp] at h2
  have e1 : ((ie : AlgebraicClosure K →+* Qbar).comp
      (σ : AlgebraicClosure K →+* AlgebraicClosure K)).comp
      (ie.symm : Qbar →+* AlgebraicClosure K) = (s : Qbar →+* Qbar) := by
    ext y
    simp [hσ]
  have e2 : (ie : AlgebraicClosure K →+* Qbar).comp (ie.symm : Qbar →+* AlgebraicClosure K) =
      RingHom.id Qbar := by
    ext y
    simp
  rw [e1, e2] at h2
  rw [h2, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
end G4WeilRes
end PartInertia
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean:1033 (inertiaFixesHomsMon_hf)
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
section PartInertia
namespace G4WeilRes
open GlueB3Unram CategoryTheory AlgebraicGeometry Limits MonObj PkgI3 PkgI3.AbVar InertiaHoms
variable (K : IntermediateField ℚ Qbar)
/-- Inertia fixes the conjugacy Hom lattice, by agreement on torsion. -/
theorem inertiaFixesHomsMon_hf_nos (hF : _root_.NOSNarrow.NOSForward) (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hDVR : ComapDVR) : InertiaFixesHomsMon := by
  intro K _ A B e₁ e₂ φ w p hp hw hA hB s hs hf hg
  have := hDVR K (e₁ : K →+* Qbar) w p hp hw
  have := hDVR K (e₂ : K →+* Qbar) w p hp hw
  -- an auxiliary prime `ℓ ≠ p`
  obtain ⟨ℓ, hℓ, hℓp⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p := by
    by_cases h2 : p = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun h => h2 h.symm⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hse₁ := fixes_of_spec K s e₁ hf
  have hse₂ := fixes_of_spec K s e₂ hg
  have hunit : ∀ (e : K →ₐ[ℚ] Qbar) (n : ℕ),
      IsUnit (((ℓ ^ n : ℕ) : ℕ) : w.comap (e : K →+* Qbar)) := fun e n => by
    rw [Nat.cast_pow]
    exact (isUnit_prime_of_liesOver (e : K →+* Qbar) w p hp hw ℓ hℓ hℓp).pow n
  let A₁ := bcAlong A (e₁ : K →+* Qbar)
  let B₂ := bcAlong B (e₂ : K →+* Qbar)
  let ψ : A₁.X ⟶ B₂.X := G4Conj.conj A.X B.X (specGal s) hf hg φ.hom
  have hψ : IsMonHom ψ :=
    G4Conj.conj_isMonHom' A.X B.X (specGal s) hf hg φ.hom (show IsMonHom φ.hom from inferInstance)
  -- agreement on torsion sections over `Spec ℚ̄`
  have hsec : ∀ (n : ℕ) (Q : CategoryTheory.Over.mk (𝟙 (Spec (CommRingCat.of Qbar))) ⟶ A₁.X),
      Q ^ (ℓ ^ n) = 1 → Q.left ≫ ψ.left = Q.left ≫ φ.hom.left := by
    intro n Q hQ
    have hfixA : Q.left ≫ G4Conj.cmp A.X (specGal s) hf = specGal s ≫ Q.left := by
      apply G4Conj.cmp_fixed_of_fst A.X (specGal s) hf Q.left (CategoryTheory.Over.w Q)
      have hq : G4Conj.secFst A.X (specEmb K e₁) Q ^ (ℓ ^ n) = 1 :=
        (G4Conj.secFst_pow A.X (specEmb K e₁) Q (ℓ ^ n)).symm.trans
          ((congrArg (G4Conj.secFst A.X (specEmb K e₁)) hQ).trans (G4Conj.secFst_one _ _))
      have := point_fixed_nos K hF A e₁ w hA s hs hse₁ (ℓ ^ n) (pow_pos hℓ.pos n) (hunit e₁ n)
        (G4Conj.secFst A.X (specEmb K e₁) Q) hq
      exact this
    have hfixB : (Q ≫ φ.hom).left ≫ G4Conj.cmp B.X (specGal s) hg =
        specGal s ≫ (Q ≫ φ.hom).left := by
      apply G4Conj.cmp_fixed_of_fst B.X (specGal s) hg (Q ≫ φ.hom).left (CategoryTheory.Over.w _)
      have hQφ : (Q ≫ φ.hom) ^ (ℓ ^ n) = 1 := by
        rw [← MonObj.pow_comp, hQ, MonObj.one_comp]
      have hq : G4Conj.secFst B.X (specEmb K e₂) (Q ≫ φ.hom) ^ (ℓ ^ n) = 1 :=
        (G4Conj.secFst_pow B.X (specEmb K e₂) (Q ≫ φ.hom) (ℓ ^ n)).symm.trans
          ((congrArg (G4Conj.secFst B.X (specEmb K e₂)) hQφ).trans (G4Conj.secFst_one _ _))
      have := point_fixed_nos K hF B e₂ w hB s hs hse₂ (ℓ ^ n) (pow_pos hℓ.pos n) (hunit e₂ n)
        (G4Conj.secFst B.X (specEmb K e₂) (Q ≫ φ.hom)) hq
      exact this
    exact G4Conj.conj_agree A.X B.X (specGal s) hf hg φ.hom Q.left (specGal s) hfixA
      hfixB
  -- conclude with Mumford's injectivity into Hom of Tate modules
  have hne : (ℓ : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  let Ψ : AbVar.Hom A₁ B₂ := @AbVar.Hom.mk' _ _ A₁ B₂ ψ hψ
  have key : tateHom ℓ A₁ B₂ Ψ = tateHom ℓ A₁ B₂ φ := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext n
    have htor : (Additive.toMul (t.1 n)) ^ (ℓ ^ n) = 1 :=
      congrArg Additive.toMul (PkgI3.Tate.pow_smul_eq_zero t.2 n)
    set P := Additive.toMul (t.1 n)
    have hP : (ptIso.inv ≫ P) ^ (ℓ ^ n) = 1 := by
      rw [← MonObj.comp_pow, htor, MonObj.comp_one]
    have h1 := hsec n (ptIso.inv ≫ P) hP
    have hPl : P.left = ptIso.hom.left ≫ (ptIso.inv ≫ P).left :=
      congrArg CategoryTheory.Over.Hom.left (Iso.hom_inv_id_assoc ptIso P).symm
    have h2 : P ≫ ψ = P ≫ φ.hom := by
      apply CategoryTheory.Over.OverMorphism.ext
      show P.left ≫ ψ.left = P.left ≫ φ.hom.left
      rw [hPl, Category.assoc, Category.assoc, h1]
    show Additive.ofMul (P ≫ ψ) = Additive.ofMul (P ≫ φ.hom)
    rw [h2]
  have := tateHom_injective_hf hHFF _root_.HFReroute.sigmaQbar A₁ B₂ ℓ hne key
  exact congrArg AbVar.Hom.hom this
end G4WeilRes
end PartInertia
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean:1120 (inertiaFixesHomsMon_of_leaves_hf)
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
section PartInertia
namespace G4WeilRes
open GlueB3Unram CategoryTheory AlgebraicGeometry Limits MonObj PkgI3 PkgI3.AbVar InertiaHoms
variable (K : IntermediateField ℚ Qbar)
/-- Hom lattice inertia for the DVR obtained by restriction. -/
theorem inertiaFixesHomsMon_of_leaves_hf_nos (hF : _root_.NOSNarrow.NOSForward)
    (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) : InertiaFixesHomsMon :=
  inertiaFixesHomsMon_hf_nos hF hHFF comapDVR
end G4WeilRes
end PartInertia
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean:1143 (kernelField_of_model_hf)
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
section KernelCore
open GlueB3Unram hiding UnramifiedAt
open GlueDescent.B2Q NumberField PkgI3 PkgI3.AbVar CategoryTheory MonObj
namespace G0ModField.KernelField
/-- Construct the Hom kernel field and prove unramifiedness outside the given set. -/
theorem kernelField_of_model_hf_nos (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hF : _root_.NOSNarrow.NOSForward)
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((G4WeilRes.conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ r : ℕ, r ≤ 16 * ZInQ.heightF0 ^ 2 ∧
    ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IntermediateField ℚ Qbar)
      (_ : FiniteDimensional ℚ E) (_ : IsGalois ℚ E),
      Module.finrank ℚ E = Nat.card G ∧
      (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt E p) ∧
      (∀ σ ∈ (E ⊔ K).fixingSubgroup, G4WeilRes.conjAction K A σ = 1) := by
  obtain ⟨hfree, hfin, hrank⟩ := G4WeilRes.homLattice_free_hf hHFF (G4WeilRes.conjData K A).A hdim
  have hr : Module.finrank ℤ (G4WeilRes.HomLattice (G4WeilRes.conjData K A).A) ≤
      16 * ZInQ.heightF0 ^ 2 :=
    hrank.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (by rw [G4WeilRes.card_conjugates]; exact hKF) 2))
  obtain ⟨G, hG, E, hfE, hgE, hEG, hfix, hram⟩ :=
    kernelField_core (Module.finBasisOfFinrankEq ℤ _ rfl) (G4WeilRes.conjAction K A)
      (G4WeilRes.conjAction_continuous K G4WeilRes.homDescends A) T
      (G4WeilRes.conjAction_inertia' K (G4WeilRes.inertiaFixesHomsMon_of_leaves_hf_nos hF hHFF) A T
        hK hgood)
  exact ⟨_, hr, G, hG, E, hfE, hgE, hEG, hram,
    fun σ hσ => hfix σ (IntermediateField.fixingSubgroup_antitone le_sup_left hσ)⟩
end G0ModField.KernelField
end KernelCore
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/D2A6Wrap.lean:109 (good_of_QML3U)
namespace HDec
section D2A6WrapKF
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace G0ModField.KernelField
/-- Good reduction from the proper model over ℤ[1/30]. -/
theorem good_of_QML3U_nos (hRay : D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (K : IF) [FiniteDimensional ℚ K] (PK : QML3 K)
    (T : Finset ℕ) (hT : D2A6.T324 ⊆ T) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, GlueB3Unram.LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar,
        PkgI2.HasGoodReduction (ObjBridge.toGrp PK.A) (w.comap (e : K →+* Qbar)) := by
  intro p hp hpT w hw e
  haveI : Fact p.Prime := ⟨hp⟩
  refine _root_.D2A6.hasGoodReduction_of_z30 hRay.2 PK _ p
    (_root_.D2A6.not_dvd_thirty_of_lt (D2A6.lt_of_notMem_T324 hp (fun h => hpT (hT h)))) ?_
  intro hu
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hu
  have hc' : (p : Qbar) * e (c : K) = 1 := by
    have := congrArg (fun z : w.comap (e : K →+* Qbar) => e (z : K)) hc
    simpa using this
  have hcw : e (c : K) ∈ w := c.2
  have h1 : w.valuation (e (c : K)) ≤ 1 := (w.valuation_le_one_iff _).mpr hcw
  have h2 : w.valuation (p : Qbar) < 1 := hw
  have h3 := congrArg w.valuation hc'
  rw [map_mul, map_one] at h3
  have h4 : w.valuation (p : Qbar) * w.valuation (e (c : K)) < 1 :=
    mul_lt_one_of_lt_of_le h2 h1
  exact absurd h3 (ne_of_lt h4)
end G0ModField.KernelField
end D2A6WrapKF
end HDec

-- copied from ZInQKernel/Contrib/OneProof/H/D2A6Chain.lean:393 (kernelFieldExists_of_pieces_hf_u)
set_option linter.unusedVariables false
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace G0ModField.KernelField
open G0ModField
/-- Construct the kernel field for the chosen fibre. -/
theorem kernelFieldExists_of_pieces_hf_u_nos (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hF : _root_.NOSNarrow.NOSForward) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (hCount : TorsionCountPts)
    (hMaps : ConjMapsOnHomField) : KernelFieldExists := by
  intro Y Φ π u P hctx K _ _ hKF hramK PK hPK
  have hK : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model_hf_nos hHFF hF K hKF PK.A (conj_dim K PK.A PK.surface) (T u) hK
      (good_of_QML3U_nos hRay hTors K PK (T u) (_root_.HDec.D2A6.T324_subset_T u))
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  obtain ⟨m, hm⟩ := hMaps Y Φ π u P hctx K hKF hramK PK hPK (E ⊔ K) le_sup_right hfix
  obtain ⟨c, hc⟩ := conjugacyData_of_conjMaps _ _ m
    (hCount _ _ (bc_dim le_sup_right PK.A PK.surface)) hm
  exact ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hc⟩
end G0ModField.KernelField
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/H/D2A6Chain.lean:424 (kernelFieldExists_of_leaves_hf_u)
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace G0ModField.KernelField
open G0ModField
/-- Supply the torsion count for the kernel field. -/
theorem kernelFieldExists_of_leaves_hf_u_nos (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hF : _root_.NOSNarrow.NOSForward) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (hMaps : ConjMapsOnHomField) : KernelFieldExists :=
  kernelFieldExists_of_pieces_hf_u_nos hHFF hF hRay hTors (torsionCountPts_of_leaf hTors) hMaps
end G0ModField.KernelField
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/H/D2A6Chain.lean:446 (kernelFieldExists_of_leaves_FS5_hf_u)
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace G0ModField.KernelField
open G0ModField
/-- Use fibre simplicity to supply the conjugacy maps. -/
theorem kernelFieldExists_of_leaves_FS5_hf_u_nos (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hF : _root_.NOSNarrow.NOSForward) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hMaps : ConjMapsNoCM) : KernelFieldExists :=
  kernelFieldExists_of_leaves_hf_u_nos hHFF hF hRay hTors (conjMapsOnHomField_of h5 hMaps)
end G0ModField.KernelField
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/H/D2A6Chain.lean:470 (kernelFieldExists_of_split_hf_u)
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace G0ModField.KernelField
open G0ModField
/-- Assemble the kernel field from the split conjugacy inputs. -/
theorem kernelFieldExists_of_split_hf_u_nos (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hF : _root_.NOSNarrow.NOSForward) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) (hE : EndEqOOnHomField) : KernelFieldExists :=
  kernelFieldExists_of_leaves_FS5_hf_u_nos hHFF hF hRay hTors h5 (conjMapsNoCM_of hTors hG hE)
end G0ModField.KernelField
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/H/D2A6Chain.lean:494 (kernelFieldExists_of_split_hf_u')
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace G0ModField.KernelField
open G0ModField
/-- Assemble the endomorphism-ring input by transport. -/
theorem kernelFieldExists_of_split_hf_u'_nos (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hF : _root_.NOSNarrow.NOSForward) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) (ha : EndEqOFibre) (hb : EndTransport) : KernelFieldExists :=
  kernelFieldExists_of_split_hf_u_nos hHFF hF hRay hTors h5 hG (endEqOOnHomField_of ha hb)
end G0ModField.KernelField
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/H/D2A6Chain.lean:521 (kernelFieldExists_of_split_hf_u'')
namespace HDec
set_option maxHeartbeats 1000000
section G0A2_a75_kernelfield
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
section EndEqOSec
open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct Quaternion
namespace G0ModField.KernelField
/-- Kernel-field reader (L557–560) with only the forward implication. -/
theorem kernelFieldExists_of_split_hf_u''_nos (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hF : _root_.NOSNarrow.NOSForward) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (hYu : QMLattice.YuB6Alg)
    (h5 : G0FibreSimple.FibreComTrivial) (hmax : OMaximal) (hb : EndTransport)
    (hG : ConjIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_split_hf_u'_nos hHFF hF hRay hTors h5 hG (endEqOFibre_of_hf hYu hHFF hmax) hb

example (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (hYu : QMLattice.YuB6Alg)
    (h5 : G0FibreSimple.FibreComTrivial) (hmax : OMaximal) (hb : EndTransport)
    (hG : ConjIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_split_hf_u''_nos hHFF (_root_.NOSNarrow.nosForward_of_r7a hNOS) hRay hTors hYu h5 hmax hb hG

end G0ModField.KernelField
end EndEqOSec
end G0A2_a75_kernelfield
end HDec

-- copied from ZInQKernel/Contrib/OneProof/A6IntModel.lean:165 (GoodRedTorsionT)
namespace HDec
namespace D2A6
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField
/-- Good reduction outside the given set gives inertia triviality on prime-power torsion. -/
def GoodRedTorsionTF (T : Finset ℕ) : Prop :=
  _root_.NOSNarrow.NOSForward →
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (A : PkgI3.AbVar K),
    (∀ (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov] (p : ℕ), p.Prime → p ∉ T →
      ¬ IsUnit (p : Ov) → PkgI2.HasGoodReduction (ObjBridge.toGrp A) Ov) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      letI : NumberField L' := numberField_of_fd L'
      ∀ p : ℕ, p.Prime → p ∉ T → p ≠ ℓ →
        ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
        ∀ σ' : Field.absoluteGaloisGroup L',
          (∃ σ ∈ v.inertiaSubgroup ℚ,
            ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = G0Galois.resQ L' σ') →
          ∀ (n : ℕ) (x : (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).Pt
              (AlgebraicClosure L')),
            x ^ (ℓ ^ n) = 1 →
            (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct σ' x = x
end D2A6
end HDec

-- copied from ZInQKernel/Contrib/OneProof/A6IntModel.lean:203 (goodRedTorsionT)
namespace HDec
open _root_.ZInQ (Contrib.AbVarBC.G0FibreSimple.MulIsogeny Contrib.AbVarBC.MulRigidity.CotangentMulN Contrib.AbVarBC.MulRigidity.KerUnitOpen Contrib.AbVarBC.MulRigidity.KerUnitOpenOfCotangentSurj Contrib.AbVarBC.MulRigidity.MulEtale Contrib.AbVarBC.MulRigidity.MulUnramified Contrib.AbVarBC.MulRigidity.O0 Contrib.AbVarBC.MulRigidity.QuasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.charZero_residueField Contrib.AbVarBC.MulRigidity.cotangentMap Contrib.AbVarBC.MulRigidity.diagonal_isPullback Contrib.AbVarBC.MulRigidity.diffKer Contrib.AbVarBC.MulRigidity.formallyUnramified_of_kerUnit Contrib.AbVarBC.MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section Contrib.AbVarBC.MulRigidity.isProper_left Contrib.AbVarBC.MulRigidity.kerUnit Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_cotangent Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_mulEtale Contrib.AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified Contrib.AbVarBC.MulRigidity.map_origin Contrib.AbVarBC.MulRigidity.mulIsogeny_of_cotangent Contrib.AbVarBC.MulRigidity.mulIsogeny_of_kerUnitOpen Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulEtale Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified' Contrib.AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen Contrib.AbVarBC.MulRigidity.mulUnramified_of_mulEtale Contrib.AbVarBC.MulRigidity.ne_of_specializes_of_lqf Contrib.AbVarBC.MulRigidity.origin Contrib.AbVarBC.MulRigidity.quasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.stalkEndo Contrib.AbVarBC.MulRigidity.surjective_of_lqf_self) -- op-dedupe
set_option maxHeartbeats 1000000
section G0A2_c75_ltgoodred
section LTGoodRedSec
set_option linter.style.haveILetI false
noncomputable section
open scoped Pointwise
namespace LTGoodRed
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField
set_option maxHeartbeats 1000000 in
/-- Transport inertia triviality to torsion on the base-changed variety. -/
theorem goodRedTorsionT_nos (T : Finset ℕ) : _root_.HDec.D2A6.GoodRedTorsionTF T := by
  intro hF K L L' _ hKL hLL' A hA ℓ _
  letI hNF : NumberField L' := numberField_of_fd L'
  intro p hp hp3 hpl v hv σ' hσ n x hx
  -- `K` is a number field
  haveI hKfd : FiniteDimensional ℚ K := FiniteDimensional.of_injective
    (IntermediateField.inclusion (hKL.trans hLL')).toLinearMap
    (IntermediateField.inclusion (hKL.trans hLL')).toRingHom.injective
  haveI hKNF : NumberField K := numberField_of_fd K
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  letI iKL' : Algebra K L' := incAlg (hKL.trans hLL')
  haveI tKLL' : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tLΩ : IsScalarTower L L' (AlgebraicClosure L') := inferInstance
  haveI tKL'Ω : IsScalarTower K L' (AlgebraicClosure L') := inferInstance
  haveI tKLΩ : IsScalarTower K L (AlgebraicClosure L') := IsScalarTower.of_algebraMap_eq
    (fun y => by
      rw [IsScalarTower.algebraMap_apply K L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply L L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply K L L'])
  -- `Ω = \bar{L'}` is an algebraic closure of `K`
  haveI tQKL' : IsScalarTower ℚ K L' := IsScalarTower.of_algebraMap_eq (fun q => by
    rw [eq_ratCast (algebraMap ℚ L') q, eq_ratCast (algebraMap ℚ K) q, map_ratCast])
  haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
  haveI : Algebra.IsAlgebraic K L' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans K L' (AlgebraicClosure L')
  haveI : IsAlgClosure K (AlgebraicClosure L') := ⟨inferInstance, inferInstance⟩
  let τ : AlgebraicClosure L' ≃ₐ[K] AlgebraicClosure K :=
    IsAlgClosure.equiv K (AlgebraicClosure L') (AlgebraicClosure K)
  -- `g : ℚ̄ → Ω` is bijective
  let g : PkgI4.Qbar →ₐ[ℚ] AlgebraicClosure L' := (G0Galois.qEmbRing L').toRatAlgHom
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  have hgbij : Function.Bijective g := by
    letI : Algebra PkgI4.Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ PkgI4.Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral PkgI4.Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ge : PkgI4.Qbar ≃+* AlgebraicClosure L' := RingEquiv.ofBijective (G0Galois.qEmbRing L') hgbij
  have hge : ∀ z, ge z = G0Galois.qEmbRing L' z := fun _ => rfl
  -- the transport `ψ : \bar K ≃ ℚ̄`, the place `w` of `\bar K` and `O = w ∩ K`
  let ψ : AlgebraicClosure K ≃+* PkgI4.Qbar := τ.symm.toRingEquiv.trans ge.symm
  have hψ : ∀ y, ψ y = ge.symm (τ.symm y) := fun _ => rfl
  let w : ValuationSubring (AlgebraicClosure K) := v.comap (ψ : AlgebraicClosure K →+* PkgI4.Qbar)
  let O : ValuationSubring K := w.comap (algebraMap K (AlgebraicClosure K))
  -- `p ∈ 𝔪_w`
  have hpw : ((p : ℕ) : AlgebraicClosure K) ∈ w.nonunits := by
    rw [mem_nonunits_comap v ψ, map_natCast]; exact hv
  -- integers prime to `p` are units of `O`
  have hunit : ∀ m : ℕ, Nat.Coprime m p → IsUnit (m : O) := by
    intro m hm
    obtain ⟨hm0, hmi⟩ := inv_mem_of_notMem_nonunits w (natCast_notMem_nonunits w hpw hm)
    have hm0K : (m : K) ≠ 0 := by
      intro h; apply hm0
      rw [← map_natCast (algebraMap K (AlgebraicClosure K)), h, map_zero]
    have hmO : (m : K)⁻¹ ∈ O := by
      rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]; exact hmi
    refine isUnit_iff_exists_inv.mpr ⟨⟨(m : K)⁻¹, hmO⟩, Subtype.ext ?_⟩
    push_cast
    exact mul_inv_cancel₀ hm0K
  -- `O ≠ K`: `p⁻¹ ∉ O`
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hpi : ((p : K))⁻¹ ∈ O := by rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hpi
    rw [ValuationSubring.mem_nonunits_iff_or] at hpw
    rcases hpw with h | h
    · exact hp.ne_zero (by exact_mod_cast h)
    · exact h hpi
  haveI hODVR : IsDiscreteValuationRing O := NLG.isDiscreteValuationRing_of_ne_top O hOtop
  -- `3` and `ℓⁿ` are units in `O`
  have hpO : ¬ IsUnit ((p : ℕ) : O) := by
    intro hu
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hu
    have hc' : (p : K) * (c : K) = 1 := by
      have := congrArg Subtype.val hc
      push_cast at this
      exact this
    have hpi : ((p : K))⁻¹ ∈ O := by
      rw [← eq_inv_of_mul_eq_one_right hc']
      exact c.2
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hpi
    rw [ValuationSubring.mem_nonunits_iff_or] at hpw
    rcases hpw with h | h
    · exact hp.ne_zero (by exact_mod_cast h)
    · exact h hpi
  have hℓp : Nat.Coprime (ℓ ^ n) p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes (Fact.out : ℓ.Prime) hp).mpr (Ne.symm hpl))
  -- NOS (a) ⇒ (b) at `(O, w)`
  have htriv := (hF K O w rfl (ObjBridge.toGrp A) (hA O p hp hp3 hpO)) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (by exact_mod_cast hunit (ℓ ^ n) hℓp)
  -- the inertia element `σ_K = τ σ' τ⁻¹` at `w`
  obtain ⟨σ, hσI, hσeq⟩ := hσ
  obtain ⟨hv1, hv2⟩ := of_mem_inertia ℚ v σ hσI
  rw [hσeq] at hv1 hv2
  let s' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L' := σ'
  let σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    (τ.symm.trans (s'.restrictScalars K)).trans τ
  have hσK : ∀ y, σK y = τ (s' (τ.symm y)) := fun _ => rfl
  have hres : ∀ y, ψ (σK y) = (G0Galois.resQ L' σ') (ψ y) := by
    intro y
    apply ge.injective
    show ge (ge.symm (τ.symm (σK y))) = ge ((G0Galois.resQ L' σ') (ge.symm (τ.symm y)))
    rw [RingEquiv.apply_symm_apply, hσK, AlgEquiv.symm_apply_apply]
    have hspec := G0Galois.resQ_spec L' σ' (ge.symm (τ.symm y))
    rw [← hge, ← hge, RingEquiv.apply_symm_apply] at hspec
    exact hspec.symm
  have hI : PkgI2.IsInertia w σK := by
    refine isInertia_of K w σK (fun y => ?_) (fun a ha => ?_)
    · show ψ (σK y) ∈ v ↔ ψ y ∈ v
      rw [hres]; exact hv1 (ψ y)
    · rw [mem_nonunits_comap v ψ, map_sub, hres]
      exact hv2 (ψ a) ha
  -- the points
  let E := (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
    (AlgebraicClosure L')).trans ((UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')).trans
      (UnramTate.trPt A τ))
  have hE : ∀ y, E ((@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y) =
      A.galAct σK (E y) := by
    intro y
    show UnramTate.trPt A τ (UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')
        (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
          (AlgebraicClosure L')
          ((@PkgI3.AbVar.baseChange L _
            (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y))) = _
    rw [UnramTate.bcPt_galAct, UnramTate.bcPt_galAct]
    exact UnramTate.trPt_galAct A τ _ σK (fun z => by rw [hσK, AlgEquiv.symm_apply_apply]; rfl) _
  have hEx : E x ^ (ℓ ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hfix : A.galAct σK (E x) = E x := htriv σK hI (E x) hEx
  apply E.injective
  exact (hE x).trans hfix
end LTGoodRed
end
end LTGoodRedSec
end G0A2_c75_ltgoodred
end HDec

-- copied from ZInQKernel/Contrib/OneProof/A6Z30.lean:161 (qmModelG3U_of_z30)
namespace HDec
namespace D2A6
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField
/-- Good reduction outside the primes ≤ 324 gives unramified Tate modules. -/
theorem qmModelG3U_of_z30_nos (hF : _root_.NOSNarrow.NOSForward) (hY : _root_.Y3RouteA.Y3FullThreeRepZ30) :
    QMModelG3U := by
  intro K L L' _ hKL hLL' PK ℓ _
  letI : NumberField L' := numberField_of_fd L'
  intro p hp hpT hpl v hv σ' hσ
  exact HSyn.LinkedTate.tate_eq_one_of_torsion _ ℓ σ'
    (LTGoodRed.goodRedTorsionT_nos T324 hF K L L' hKL hLL' PK.A
      (fun Ov _ q hq hqT hqO =>
        haveI : Fact q.Prime := ⟨hq⟩
        _root_.D2A6.hasGoodReduction_of_z30 hY PK Ov q
          (_root_.D2A6.not_dvd_thirty_of_lt (lt_of_notMem_T324 hq hqT)) hqO)
      ℓ p hp hpT hpl v hv σ' hσ)
end D2A6
end HDec

-- copied from ZInQKernel/Contrib/OneProof/A6Z30.lean:175 (modelG3G6_of_leavesU_z30)
namespace HDec
namespace D2A6
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField
/-- G3 and G5–G6 from the proper model and the forward implication. -/
theorem modelG3G6_of_leavesU_z30_nos (hFS : HSyn.G0Split.FibreSimple) (hF : _root_.NOSNarrow.NOSForward)
    (hY : _root_.Y3RouteA.Y3FullThreeRepZ30) : HSyn.G0AssembleMod.ModelG3G6 :=
  modelG3G6_of_U hFS (qmModelG3U_of_z30_nos hF hY)
end D2A6
end HDec

-- copied from ZInQKernel/Contrib/OneProof/D2A6Wrap.lean:89 (modelG3G6_of_leaves3U)
namespace HDec
section D2A6WrapA6
noncomputable section
namespace HSyn
open CategoryTheory AlgebraicGeometry G0Split
/-- A6 reader for G11 (L752–753) with only the forward implication. -/
theorem modelG3G6_of_leaves3U_nos (hFS : G0Split.FibreSimple) (hF : _root_.NOSNarrow.NOSForward)
    (hRay : D2A6.R6U) (hTors : PkgI2.TorsionStructure.{0}) :
    G0AssembleMod.ModelG3G6 :=
  D2A6.modelG3G6_of_leavesU_z30_nos hFS hF hRay.2

example (hFS : G0Split.FibreSimple) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : D2A6.R6U) (hTors : PkgI2.TorsionStructure.{0}) :
    G0AssembleMod.ModelG3G6 :=
  modelG3G6_of_leaves3U_nos hFS (_root_.NOSNarrow.nosForward_of_r7a hNOS) hRay hTors

end HSyn
end
end D2A6WrapA6
end HDec

#print axioms NOSNarrow.perfect_of_sep
#print axioms NOSNarrow.nosForward_proof
#print axioms NOSNarrow.nosForward_of_r7a
#print axioms HDec.G4WeilRes.point_fixed_nos
#print axioms HDec.G4WeilRes.inertiaFixesHomsMon_hf_nos
#print axioms HDec.G4WeilRes.inertiaFixesHomsMon_of_leaves_hf_nos
#print axioms HDec.G0ModField.KernelField.kernelField_of_model_hf_nos
#print axioms HDec.G0ModField.KernelField.good_of_QML3U_nos
#print axioms HDec.G0ModField.KernelField.kernelFieldExists_of_pieces_hf_u_nos
#print axioms HDec.G0ModField.KernelField.kernelFieldExists_of_leaves_hf_u_nos
#print axioms HDec.G0ModField.KernelField.kernelFieldExists_of_leaves_FS5_hf_u_nos
#print axioms HDec.G0ModField.KernelField.kernelFieldExists_of_split_hf_u_nos
#print axioms HDec.G0ModField.KernelField.kernelFieldExists_of_split_hf_u'_nos
#print axioms HDec.G0ModField.KernelField.kernelFieldExists_of_split_hf_u''_nos
#print axioms HDec.LTGoodRed.goodRedTorsionT_nos
#print axioms HDec.D2A6.qmModelG3U_of_z30_nos
#print axioms HDec.D2A6.modelG3G6_of_leavesU_z30_nos
#print axioms HDec.HSyn.modelG3G6_of_leaves3U_nos
