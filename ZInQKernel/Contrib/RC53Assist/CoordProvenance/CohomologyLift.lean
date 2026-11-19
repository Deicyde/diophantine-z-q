import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1aG
import ZInQKernel.Contrib.RC53Assist.CoordLink.Patterns
import ZInQKernel.Contrib.RC53Assist.CoordLink.Correction

/-!
# Lifting the same actual class through a finite Selmer model

A quasi-isomorphism from a finite model to the continuous-cochain Selmer
complex permits the actual class to be lifted with a retained boundary.
Two such lifts differ by a boundary in the finite model.  These statements
hold over the original coefficient ring, not only after passing to a field.

The locators are Definition ex:arith-coordinate, TeX 3877–3892, the actual
paired-functional construction, TeX 3844–3861, and the transport of the same
cochains in ex:limits-fixed-field-clearing, TeX 5509–5516.  The results are
proved from the homology and cochain definitions.  No additional printed
proposition is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Determinant (OO SignGroup)

universe u

section Classes

variable {R : Type u} [CommRing R]

/-- The kernel description of the cycles maps to the homology cycles. -/
def liftCycle (C : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ModuleCat.of R (LinearMap.ker (C.d n (n + 1)).hom) ⟶ C.cycles n :=
  C.liftCycles (ModuleCat.ofHom (LinearMap.ker (C.d n (n + 1)).hom).subtype)
    (n + 1) (by simp) (by ext x; exact x.2)

/-- The class of a cochain cycle over the original coefficient ring. -/
def classOf (C : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    LinearMap.ker (C.d n (n + 1)).hom →ₗ[R] C.homology n :=
  (C.homologyπ n).hom.comp (liftCycle C n).hom

/-- The homology cycle underlying a kernel cycle has the same cochain. -/
theorem liftCycle_cochain (C : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : LinearMap.ker (C.d n (n + 1)).hom) :
    (C.iCycles n).hom ((liftCycle C n).hom x) = x.1 := by
  have h := congrArg (fun f => f.hom x)
    (C.liftCycles_i (ModuleCat.ofHom (LinearMap.ker (C.d n (n + 1)).hom).subtype)
      (n + 1) (by simp) (by ext x; exact x.2))
  exact h

/-- Every cohomology class has a cochain representative, over any commutative ring. -/
theorem classOf_surjective (C : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Function.Surjective (classOf C n) := by
  intro a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance a
  have hz : (C.d n (n + 1)).hom ((C.iCycles n).hom z) = 0 := by
    have h := congrArg (fun f => f.hom z) (C.iCycles_d n (n + 1))
    exact h
  refine ⟨⟨_, hz⟩, ?_⟩
  change (C.homologyπ n).hom ((liftCycle C n).hom _) = _
  congr 1
  apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
  rw [liftCycle_cochain]

/-- A cycle with zero class is the boundary of a cochain in the preceding degree. -/
theorem boundary_of_classOf_zero (C : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : LinearMap.ker (C.d n (n + 1)).hom) (hx : classOf C n x = 0) :
    ∃ b : C.X (n - 1), (C.d (n - 1) n).hom b = x.1 := by
  let S := ShortComplex.mk (C.toCycles (n - 1) n) (C.homologyπ n)
    (C.toCycles_comp_homologyπ (n - 1) n)
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (C.homologyIsCokernel (n - 1) n (by simp))
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS ((liftCycle C n).hom x) hx
  refine ⟨b, ?_⟩
  have h1 := congrArg (C.iCycles n).hom hb
  rw [liftCycle_cochain] at h1
  have h2 := congrArg (fun f => f.hom b) (C.toCycles_i (n - 1) n)
  exact h2.symm.trans h1

/-- The class map is natural for an actual cochain map. -/
theorem classOf_natural {C D : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : C ⟶ D) (n : ℤ) (x : LinearMap.ker (C.d n (n + 1)).hom)
    (hf : (D.d n (n + 1)).hom ((f.f n).hom x.1) = 0) :
    (HomologicalComplex.homologyMap f n).hom (classOf C n x) =
      classOf D n ⟨(f.f n).hom x.1, LinearMap.mem_ker.mpr hf⟩ := by
  have hn := congrArg (fun g => g.hom ((liftCycle C n).hom x))
    (HomologicalComplex.homologyπ_naturality f n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  change (HomologicalComplex.homologyMap f n).hom
      ((C.homologyπ n).hom ((liftCycle C n).hom x)) = _
  rw [hn]
  change (D.homologyπ n).hom ((HomologicalComplex.cyclesMap f n).hom ((liftCycle C n).hom x)) =
    (D.homologyπ n).hom ((liftCycle D n).hom ⟨(f.f n).hom x.1, LinearMap.mem_ker.mpr hf⟩)
  congr 1
  apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
  have hi := congrArg (fun g => g.hom ((liftCycle C n).hom x))
    (HomologicalComplex.cyclesMap_i f n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [liftCycle_cochain]
  exact hi.trans (congrArg (f.f n).hom (liftCycle_cochain C n x))

/-- The actual class lifts through a quasi-isomorphism with an explicit boundary witness. -/
theorem exists_lift_with_boundary {C D : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : C ⟶ D) (qis : QuasiIso f) (n : ℤ) (z : D.X n)
    (hz : (D.d n (n + 1)).hom z = 0) :
    ∃ a : C.X n, (C.d n (n + 1)).hom a = 0 ∧
      ∃ b : D.X (n - 1), (f.f n).hom a - z = (D.d (n - 1) n).hom b := by
  have hIso : IsIso (HomologicalComplex.homologyMap f n) :=
    (quasiIsoAt_iff_isIso_homologyMap f n).mp inferInstance
  obtain ⟨v, hv⟩ := (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap f n)).2 (classOf D n ⟨z, hz⟩)
  obtain ⟨a, ha⟩ := classOf_surjective C n v
  have hf : (D.d n (n + 1)).hom ((f.f n).hom a.1) = 0 := by
    have h := congrArg (fun g => g.hom a.1) (f.comm n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.trans ((congrArg (f.f (n + 1)).hom (LinearMap.mem_ker.mp a.2)).trans (map_zero _))
  have hclass : classOf D n ⟨(f.f n).hom a.1, hf⟩ = classOf D n ⟨z, hz⟩ := by
    rw [← classOf_natural f n a hf, ha, hv]
  let d : LinearMap.ker (D.d n (n + 1)).hom := ⟨(f.f n).hom a.1, hf⟩ - ⟨z, hz⟩
  have hd : classOf D n d = 0 := by
    change classOf D n (⟨(f.f n).hom a.1, hf⟩ - ⟨z, hz⟩) = 0
    rw [map_sub, hclass, sub_self]
  obtain ⟨b, hb⟩ := boundary_of_classOf_zero D n d hd
  exact ⟨a.1, a.2, b, hb.symm⟩

/-- Two lifts of the same actual class differ by a boundary in the model. -/
theorem lifts_differ_by_boundary {C D : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : C ⟶ D) (qis : QuasiIso f) (n : ℤ)
    (a a' : C.X n) (ha : (C.d n (n + 1)).hom a = 0)
    (ha' : (C.d n (n + 1)).hom a' = 0)
    (b : D.X (n - 1))
    (hb : (f.f n).hom a - (f.f n).hom a' = (D.d (n - 1) n).hom b) :
    ∃ c : C.X (n - 1), a - a' = (C.d (n - 1) n).hom c := by
  have hIso : IsIso (HomologicalComplex.homologyMap f n) :=
    (quasiIsoAt_iff_isIso_homologyMap f n).mp inferInstance
  let x : LinearMap.ker (C.d n (n + 1)).hom :=
    ⟨a - a', LinearMap.mem_ker.mpr (by rw [map_sub, ha, ha', sub_self])⟩
  have hxmap : (D.d n (n + 1)).hom ((f.f n).hom x.1) = 0 := by
    have h := congrArg (fun g => g.hom x.1) (f.comm n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.trans ((congrArg (f.f (n + 1)).hom (LinearMap.mem_ker.mp x.2)).trans (map_zero _))
  have hzmap : classOf D n ⟨(f.f n).hom x.1, hxmap⟩ = 0 := by
    have he : (f.f n).hom x.1 = (D.d (n - 1) n).hom b := by
      change (f.f n).hom (a - a') = _
      rw [map_sub, hb]
    have hi : (liftCycle D n).hom ⟨(f.f n).hom x.1, hxmap⟩ = (D.toCycles (n - 1) n).hom b := by
      apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
      rw [liftCycle_cochain]
      exact he.trans (congrArg (fun g => g.hom b) (D.toCycles_i (n - 1) n)).symm
    change (D.homologyπ n).hom ((liftCycle D n).hom _) = 0
    rw [hi]
    exact congrArg (fun g => g.hom b) (D.toCycles_comp_homologyπ (n - 1) n)
  have hx : classOf C n x = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap f n)).1
    rw [classOf_natural f n x hxmap, hzmap, map_zero]
  obtain ⟨c, hc⟩ := boundary_of_classOf_zero C n x hx
  exact ⟨c, hc.symm⟩

end Classes

section Functionals

variable {R : Type u} [CommRing R]
  {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The row consists of the values of the given functional in the original basis. -/
def rowOf (L : (ι → R) →ₗ[R] R) : ι → R := fun i => L (Pi.single i 1)

/-- The original functional is represented by its original-basis row. -/
theorem rowOf_apply (L : (ι → R) →ₗ[R] R) (x : ι → R) : L x = rowOf L ⬝ᵥ x := by
  conv_lhs => rw [show x = ∑ i, x i • Pi.single i (1 : R) from by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  simp only [map_sum, map_smul, smul_eq_mul, rowOf, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Closedness of the same functional is closedness of its original-basis row. -/
theorem rowOf_closed (L : (ι → R) →ₗ[R] R) (A : Matrix ι κ R)
    (hL : ∀ x : κ → R, L (A *ᵥ x) = 0) : rowOf L ᵥ* A = 0 := by
  ext j
  have h := hL (Pi.single j 1)
  rw [rowOf_apply, dotProduct_mulVec] at h
  simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using h

/-- Scalar realization preserves the value of the same original-basis functional. -/
theorem rowOf_scalar_value {F : Type u} [CommRing F] (φ : R →+* F)
    (L : (ι → R) →ₗ[R] R) (x : ι → R) :
    (φ ∘ rowOf L) ⬝ᵥ (φ ∘ x) = φ (L x) := by
  rw [rowOf_apply]
  simp only [dotProduct, Function.comp_apply, map_sum, map_mul]

/-- The actual traced cup pairing of a cycle is a closed degree-two functional. -/
theorem pairedFun_closed {D D' : SelData R} (P : SelPairData D D')
    (tr : (coneCx P.resE).X 3 →ₗ[R] R)
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (z : (selCx D).X 1) (hz : (selCx D).d 1 2 rfl z = 0)
    (w : (selCx D').X 1) :
    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.pairedFun P tr z ((selCx D').d 1 2 rfl w) = 0 := by
  have hl := selmerCupLeibniz_proof R D D' P 1 2 1 2 2 3 rfl rfl rfl rfl z w
  rw [hz] at hl
  erw [map_zero, LinearMap.zero_apply, zero_add, sgn_one, neg_smul, one_smul] at hl
  have h0 := htr (selCup P 1 1 2 rfl z w)
  rw [hl] at h0
  exact neg_eq_zero.mp ((map_neg tr _).symm.trans h0)

end Functionals

section GenuineModel

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Determinant (Lam)

variable {K : Type} [Field K] [NumberField K]
  {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
  [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

/-- The target of the model comparison is the actual continuous-cochain Selmer complex. -/
abbrev actualSelmerCxG (M : Identification2G K S S' hS b dK hK cE tK) :
    GCx (MonoidAlgebra OO (SignGroup b)) :=
  selCx (galoisSelData K S' (MonoidAlgebra OO (SignGroup b)) M.Mf M.Δf)

/-- Lift the given actual Selmer class, retaining the comparison boundary.
The cycle is not chosen independently of that class. -/
theorem actual_class_has_model_cycle (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0) :
    ∃ z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b),
      M.D.d1 *ᵥ z = 0 ∧
      ∃ c : (actualSelmerCxG M).X 0,
        (M.ψf.f 1).hom z - zSel = (actualSelmerCxG M).d 0 1 rfl c := by
  have hzCC : ((actualSelmerCxG M).toCC.d 1 2).hom zSel = 0 :=
    (GCx.toCC_d_hom (actualSelmerCxG M) 1 2 rfl zSel).trans hzSel
  obtain ⟨z, hz, c, hc⟩ := exists_lift_with_boundary M.ψf M.qisf 1 zSel hzCC
  have hzPre : fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y *ᵥ z = 0 :=
    (GCx.toCC_d_hom (M.C.map (φO b)).toGCx 1 2 rfl z).symm.trans hz
  refine ⟨z, hz_cancel (M.C.map (φO b)) M.isUnit_B hzPre, c, ?_⟩
  exact hc.trans (GCx.toCC_d_hom (actualSelmerCxG M) (1 - 1) 1 (by decide) c)

/-- The same actual closed functional pulled back into the original model basis. -/
def actualModelRowG (M : Identification2G K S S' hS b dK hK cE tK)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b)) :
    (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b) :=
  rowOf (ι := (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N) (L.comp (M.ψf.f 2).hom)

/-- No new scalar or normalization is inserted in the pulled-back functional. -/
theorem actualModelRowG_value (M : Identification2G K S S' hS b dK hK cE tK)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (v : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b)) :
    L ((M.ψf.f 2).hom v) = actualModelRowG M L ⬝ᵥ v :=
  rowOf_apply (ι := (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N) (L.comp (M.ψf.f 2).hom) v

/-- The pulled-back actual functional is integrally closed on the original complex. -/
theorem actualModelRowG_closed (M : Identification2G K S S' hS b dK hK cE tK)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (hL : ∀ w, L ((actualSelmerCxG M).d 1 2 rfl w) = 0) :
    actualModelRowG M L ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0 := by
  apply rowOf_closed
  intro w
  let f := ofCCHom M.ψf
  have hf := f.comm 1 2 1 2 rfl rfl rfl rfl w
  exact (congrArg L hf).trans (hL _)

/-- The class and functional in the model are both derived from the given actual objects. -/
theorem same_class_and_functional_in_model (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (hL : ∀ w, L ((actualSelmerCxG M).d 1 2 rfl w) = 0) :
    ∃ (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
      (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b)),
      M.D.d1 *ᵥ z = 0 ∧
      lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0 ∧
      (∃ c : (actualSelmerCxG M).X 0,
        (M.ψf.f 1).hom z - zSel = (actualSelmerCxG M).d 0 1 rfl c) ∧
      ∀ v, L ((M.ψf.f 2).hom v) = lam ⬝ᵥ v := by
  obtain ⟨z, hz, c, hc⟩ := actual_class_has_model_cycle M zSel hzSel
  exact ⟨z, actualModelRowG M L, hz, actualModelRowG_closed M L hL,
    ⟨c, hc⟩, actualModelRowG_value M L⟩

open ZInQ.Contrib.RC53Assist.CoordLink (rankOneScalarG RankOneCoordinateProvenanceG
  AcyclicCoordinateConventionG kmOrig_rankOne_formula relIsKMG_of_provenance_and_convention)

/-- A representative of the given actual class in the original finite model. -/
def actualCycleG (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0) :
    Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b) :=
  Classical.choose (actual_class_has_model_cycle M zSel hzSel)

/-- The chosen model cycle represents the given actual class with a retained boundary. -/
theorem actualCycleG_spec (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0) :
    M.D.d1 *ᵥ actualCycleG M zSel hzSel = 0 ∧
      ∃ c : (actualSelmerCxG M).X 0,
        (M.ψf.f 1).hom (actualCycleG M zSel hzSel) - zSel = (actualSelmerCxG M).d 0 1 rfl c :=
  Classical.choose_spec (actual_class_has_model_cycle M zSel hzSel)

open Classical in
/-- The coordinate of the given actual class and functional, in the original
model's determinant basis.  This reconstructs the coordinate; it does not
identify an independently supplied scalar from a correction identity. -/
def actualCoordinateG (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (x : ZInQ.Manuscript.RC.Addr b) : FractionRing OO :=
  if M.D.RankOnePattern x then rankOneScalarG M (actualCycleG M zSel hzSel) (actualModelRowG M L) x
  else 0

/-- The reconstructed coordinate has rank-one provenance for the actual class
and the actual functional, rather than for independently chosen vectors. -/
theorem actualCoordinateG_provenance (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b)) :
    RankOneCoordinateProvenanceG M (actualCoordinateG M zSel hzSel L)
      (actualCycleG M zSel hzSel) (actualModelRowG M L) := by
  intro x _ hR
  simp only [actualCoordinateG, ite_eq_left hR]

/-- The reconstructed coordinate obeys the manuscript's acyclic convention. -/
theorem actualCoordinateG_convention (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b)) :
    AcyclicCoordinateConventionG M (actualCoordinateG M zSel hzSel L) := by
  intro x _ hA
  have hn : ¬ M.D.RankOnePattern x := by
    intro hR
    have h1 := hR.2.1
    rw [hA 1] at h1
    exact zero_ne_one h1
  simp only [actualCoordinateG, ite_eq_right hn]

/-- The reconstructed actual-object coordinate satisfies the original-coordinate link. -/
theorem relIsKMG_actualCoordinateG (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (hL : ∀ w, L ((actualSelmerCxG M).d 1 2 rfl w) = 0) :
    ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M (actualCoordinateG M zSel hzSel L)
      (actualCycleG M zSel hzSel) (actualModelRowG M L) (actualCycleG_spec M zSel hzSel).1
      (actualModelRowG_closed M L hL) :=
  relIsKMG_of_provenance_and_convention M _ _ _ _ _
    (actualCoordinateG_provenance M zSel hzSel L) (actualCoordinateG_convention M zSel hzSel L)

/-- The free-line coefficient is unchanged by a boundary of the original model. -/
theorem alphaB_add_boundary {F : Type} [Field F] (E : BlockComplex F)
    (hA0 : IsUnit E.A0.det) (z : Fin E.m0 ⊕ Unit ⊕ Fin E.m1 → F) (c : Fin E.m0 → F) :
    E.alphaB (z + E.d0 *ᵥ c) = E.alphaB z := by
  have hc := alphaB_of_boundary E hA0 c
  have hlin : E.alphaB (z + E.d0 *ᵥ c) = E.alphaB z + E.alphaB (E.d0 *ᵥ c) := by
    have he : (z + E.d0 *ᵥ c) ∘ Sum.inl = z ∘ Sum.inl + (E.d0 *ᵥ c) ∘ Sum.inl := rfl
    simp only [BlockComplex.alphaB, he, Pi.add_apply, Matrix.mulVec_add, dotProduct_add]
    ring
  rw [hlin, hc, add_zero]

/-- Any other lift of the same actual class gives the same original coordinate.
The comparison boundary is used to prove this independence. -/
theorem actualCoordinateG_of_lift (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (hL : ∀ w, L ((actualSelmerCxG M).d 1 2 rfl w) = 0)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (c : (actualSelmerCxG M).X 0)
    (hc : (M.ψf.f 1).hom z - zSel = (actualSelmerCxG M).d 0 1 rfl c)
    (x : ZInQ.Manuscript.RC.Addr b)
    (hΔ : ZInQ.Manuscript.RC.Determinant.evK (ZInQ.Manuscript.RC.Determinant.sgnChar x)
      M.toIdentification.B.Δ ≠ 0) :
    kmOrig M z (actualModelRowG M L) hz (actualModelRowG_closed M L hL) x =
      actualCoordinateG M zSel hzSel L x := by
  let z0 := actualCycleG M zSel hzSel
  have hz0 := (actualCycleG_spec M zSel hzSel).1
  obtain ⟨c0, hc0⟩ := (actualCycleG_spec M zSel hzSel).2
  let C := (M.C.map (φO b)).toGCx.toCC
  let T := (actualSelmerCxG M).toCC
  let f : C ⟶ T := M.ψf
  let a : C.X 1 := z
  let a0 : C.X 1 := z0
  let zs : T.X 1 := zSel
  let t : T.X 0 := c
  let t0 : T.X 0 := c0
  have hpre : (C.d 1 2).hom a = 0 :=
    (GCx.toCC_d_hom (M.C.map (φO b)).toGCx 1 2 rfl z).trans
      (hzC (C := M.C.map (φO b)) M.isUnit_B hz)
  have hpre0 : (C.d 1 2).hom a0 = 0 :=
    (GCx.toCC_d_hom (M.C.map (φO b)).toGCx 1 2 rfl z0).trans
      (hzC (C := M.C.map (φO b)) M.isUnit_B hz0)
  have ht : (f.f 1).hom a - zs = (T.d 0 1).hom t :=
    hc.trans (GCx.toCC_d_hom (actualSelmerCxG M) 0 1 rfl c).symm
  have ht0 : (f.f 1).hom a0 - zs = (T.d 0 1).hom t0 :=
    hc0.trans (GCx.toCC_d_hom (actualSelmerCxG M) 0 1 rfl c0).symm
  have hdiff : (f.f 1).hom a - (f.f 1).hom a0 = (T.d 0 1).hom (t - t0) := by
    rw [map_sub, ← ht, ← ht0]
    abel
  have hgen := lifts_differ_by_boundary f M.qisf (1 : ℤ) a a0 hpre hpre0
  obtain ⟨d, hd⟩ := hgen (t - t0) hdiff
  let dv : Fin M.D.m0 → MonoidAlgebra OO (SignGroup b) := d
  have hdz : z - z0 = M.D.d0 *ᵥ dv :=
    hd.trans (GCx.toCC_d_hom (M.C.map (φO b)).toGCx 0 1 rfl dv)
  have he : z = z0 + M.D.d0 *ᵥ dv := by
    calc z = (z - z0) + z0 := by abel
         _ = z0 + M.D.d0 *ᵥ dv := by rw [hdz]; abel
  let ev : MonoidAlgebra OO (SignGroup b) →+* FractionRing OO :=
    ZInQ.Manuscript.RC.Determinant.evK (O := OO) (ZInQ.Manuscript.RC.Determinant.sgnChar x)
  have hev : ev ∘ z = ev ∘ z0 + M.D.d0.map ev *ᵥ (ev ∘ dv) := by
    funext i
    have hi := congrArg ev (congrFun he i)
    simpa only [Pi.add_apply, Function.comp_apply, map_add, RingHom.map_mulVec] using hi
  obtain ⟨h0, h1, h2⟩ := M.D.dets_of_Δ M.toIdentification.A0 M.toIdentification.s
    M.toIdentification.s_ne M.toIdentification.central x hΔ
  have hA0 : IsUnit (Dx M.D x).A0.det := by
    rw [← evK_det_A0]
    exact isUnit_iff_ne_zero.mpr h0
  have hα : (Dx M.D x).alphaB (ev ∘ z) = (Dx M.D x).alphaB (ev ∘ z0) := by
    erw [hev]
    exact alphaB_add_boundary (Dx M.D x) hA0 (ev ∘ z0) (ev ∘ dv)
  rcases M.D.patterns_of_det_ne_zero x h0 h1 h2 with hR | hA
  · rw [kmOrig_rankOne_formula M z (actualModelRowG M L) hz (actualModelRowG_closed M L hL) x hΔ hR]
    simp only [actualCoordinateG, ite_eq_left hR]
    unfold rankOneScalarG
    erw [hα]
  · rw [kmOrig_zero_of_acyclic M z (actualModelRowG M L) hz (actualModelRowG_closed M L hL) x hΔ hA]
    exact ((actualCoordinateG_convention M zSel hzSel L) x hΔ hA).symm

/-- The only remaining scalar input after reconstructing the same actual class
and functional: identify the supplied relaxed scalar with that coordinate.
This input is not a printed proposition. -/
theorem provenance_of_actual_dictionary (M : Identification2G K S S' hS b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (hL : ∀ w, L ((actualSelmerCxG M).d 1 2 rfl w) = 0)
    (urel : ZInQ.Manuscript.RC.Addr b → FractionRing OO)
    (hdictionary : ∀ x, ZInQ.Manuscript.RC.Determinant.evK (ZInQ.Manuscript.RC.Determinant.sgnChar x)
      M.toIdentification.B.Δ ≠ 0 → urel x = actualCoordinateG M zSel hzSel L x) :
    RankOneCoordinateProvenanceG M urel (actualCycleG M zSel hzSel) (actualModelRowG M L) ∧
      AcyclicCoordinateConventionG M urel ∧
      ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M urel (actualCycleG M zSel hzSel) (actualModelRowG M L)
        (actualCycleG_spec M zSel hzSel).1 (actualModelRowG_closed M L hL) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hΔ hR
    exact (hdictionary x hΔ).trans ((actualCoordinateG_provenance M zSel hzSel L) x hΔ hR)
  · intro x hΔ hA
    exact (hdictionary x hΔ).trans ((actualCoordinateG_convention M zSel hzSel L) x hΔ hA)
  · intro x hΔ
    exact (hdictionary x hΔ).trans ((relIsKMG_actualCoordinateG M zSel hzSel L hL) x hΔ)

/-- The actual-object scalar dictionary and the original correction supply the
clearing interface, without a power-series-unit correction premise. -/
theorem origCoordLink_of_actual_dictionary {ℓ : ℕ} (Dd : ZInQ.Manuscript.RC.RCData ℓ)
    (F : ZInQ.Manuscript.RC.Family) (M : Identification2G K S S' hS F.b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup F.b)] MonoidAlgebra OO (SignGroup F.b))
    (hL : ∀ w, L ((actualSelmerCxG M).d 1 2 rfl w) = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (urel : ZInQ.Manuscript.RC.Addr F.b → FractionRing OO)
    (hη : CorrectedIsEta Dd F η urel)
    (hdictionary : ∀ x, ZInQ.Manuscript.RC.Determinant.evK (ZInQ.Manuscript.RC.Determinant.sgnChar x)
      M.toIdentification.B.Δ ≠ 0 → urel x = actualCoordinateG M zSel hzSel L x) :
    ZInQ.Manuscript.RC.Wiring.OrigCoordLink Dd F M (actualCycleG M zSel hzSel) (actualModelRowG M L)
      (actualCycleG_spec M zSel hzSel).1 (actualModelRowG_closed M L hL) η :=
  ZInQ.Manuscript.RC.Wiring.origCoordLink_of_eta_rel hη
    (provenance_of_actual_dictionary M zSel hzSel L hL urel hdictionary).2.2

/-- Exact residual obligation for the supplied relaxed scalar, with its actual
class and functional already reconstructed.  Only fraction-field nonvanishing
of the original correction is used in the reverse implication. -/
theorem origCoordLink_iff_actual_dictionary {ℓ : ℕ} (Dd : ZInQ.Manuscript.RC.RCData ℓ)
    (F : ZInQ.Manuscript.RC.Family) (M : Identification2G K S S' hS F.b dK hK cE tK)
    (zSel : (actualSelmerCxG M).toCC.X 1) (hzSel : (actualSelmerCxG M).d 1 2 rfl zSel = 0)
    (L : (actualSelmerCxG M).X 2 →ₗ[MonoidAlgebra OO (SignGroup F.b)] MonoidAlgebra OO (SignGroup F.b))
    (hL : ∀ w, L ((actualSelmerCxG M).d 1 2 rfl w) = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (urel : ZInQ.Manuscript.RC.Addr F.b → FractionRing OO)
    (hη : CorrectedIsEta Dd F η urel) (e₀ : ZInQ.Manuscript.RC.Addr F.b → ℕ)
    (g₀ : ZInQ.Manuscript.RC.Addr F.b → Lam) (h₀ : ZInQ.Manuscript.RC.Wiring.UTildeRep Dd F e₀ g₀)
    (hne : ∀ x, ZInQ.Manuscript.RC.Determinant.evK (ZInQ.Manuscript.RC.Determinant.sgnChar x)
      M.toIdentification.B.Δ ≠ 0 →
      ZInQ.Manuscript.RC.Determinant.evK (ZInQ.Manuscript.RC.Determinant.sgnChar x) η ≠ 0) :
    ZInQ.Manuscript.RC.Wiring.OrigCoordLink Dd F M (actualCycleG M zSel hzSel) (actualModelRowG M L)
      (actualCycleG_spec M zSel hzSel).1 (actualModelRowG_closed M L hL) η ↔
      ∀ x, ZInQ.Manuscript.RC.Determinant.evK (ZInQ.Manuscript.RC.Determinant.sgnChar x)
        M.toIdentification.B.Δ ≠ 0 → urel x = actualCoordinateG M zSel hzSel L x := by
  have hprev := ZInQ.Contrib.RC53Assist.CoordLink.relIsKMG_iff_origCoordLink Dd F M
    (actualCycleG M zSel hzSel) (actualModelRowG M L) (actualCycleG_spec M zSel hzSel).1
    (actualModelRowG_closed M L hL) η urel hη e₀ g₀ h₀ hne
  refine hprev.symm.trans ?_
  constructor
  · intro h x hΔ
    exact (h x hΔ).trans ((relIsKMG_actualCoordinateG M zSel hzSel L hL) x hΔ).symm
  · intro h x hΔ
    exact (h x hΔ).trans ((relIsKMG_actualCoordinateG M zSel hzSel L hL) x hΔ)

end GenuineModel

end ZInQ.Contrib.RC53Assist.CoordProvenance
