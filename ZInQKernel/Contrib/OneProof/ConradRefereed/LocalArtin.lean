import ZInQKernel.Contrib.G9.I4Layer
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Padic
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift
import ZInQKernel.Contrib.OneProof.ConradRefereed.NormForm

/-! The only printed input is `SerreA6Prop6`. The ground field and the
coefficient field are both `K`, a finite Galois extension of `ℚ_p` in the fixed algebraic
closure. The right side uses the arithmetic Artin map at `K` and the actual integer units, the
depth-zero term of Tau Ceti's unit filtration. This module proves the transport of the Galois
action, norm functoriality, and the topology comparisons. Provenance (c) for these comparisons. -/
noncomputable section
namespace HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The spectral local-field norm on the finite embedded extension is the inherited norm. -/
theorem norm_eq [FiniteDimensional ℚ_[p] K] (x : K) :
    letI := TauCeti.finiteIntermediateFieldNormedField ℚ_[p] (PadicAlgCl p) K
    ‖x‖ = ‖(x : PadicAlgCl p)‖ := by
  let f : AbsoluteValue K ℝ :=
    { toFun := fun y => ‖(y : PadicAlgCl p)‖
      map_mul' := fun a b => norm_mul (a : PadicAlgCl p) (b : PadicAlgCl p)
      nonneg' := fun y => norm_nonneg (y : PadicAlgCl p)
      eq_zero' := by
        intro y
        constructor
        · exact fun hy => Subtype.ext (norm_eq_zero.mp hy)
        · rintro rfl
          exact norm_zero
      add_le' := fun a b => norm_add_le (a : PadicAlgCl p) (b : PadicAlgCl p) }
  exact (TauCeti.algebraicExtensionNormedField_norm_unique ℚ_[p]
    (M := K) (f := f) (fun z => by
      change ‖(z : PadicAlgCl p)‖ = (TauCeti.normalizedAbsoluteValue ℚ_[p] z : ℝ)
      rw [PadicAlgCl.norm_extends]
      exact (congrArg (fun a : NNReal => (a : ℝ))
        (Padic.normalizedAbsoluteValue_eq_nnnorm p z)).symm) x).symm

/-- Equality of topologies, not merely equivalent topologies on the units near one. -/
theorem topology_eq [FiniteDimensional ℚ_[p] K] :
    TauCeti.finiteIntermediateFieldTopology ℚ_[p] (PadicAlgCl p) K =
      (inferInstance : TopologicalSpace K) := by
  let N := TauCeti.finiteIntermediateFieldNormedField ℚ_[p] (PadicAlgCl p) K
  let m : MetricSpace K := @NormedField.toMetricSpace _ N
  let m' : MetricSpace K := MetricSpace.induced (fun x : K => (x : PadicAlgCl p))
    Subtype.val_injective (inferInstance : MetricSpace (PadicAlgCl p))
  have hm : m = m' := by
    apply MetricSpace.ext
    have hdist : @dist K m.toDist = @dist K m'.toDist := by
      funext x y
      calc
        @dist K m.toDist x y = @norm K N.toNorm (x - y) := by
          let _ : NormedField K := N
          exact dist_eq_norm x y
        _ = ‖((x - y : K) : PadicAlgCl p)‖ := norm_eq p K _
        _ = @dist K m'.toDist x y := by
          change ‖((x - y : K) : PadicAlgCl p)‖ = dist (x : PadicAlgCl p) (y : PadicAlgCl p)
          rw [dist_eq_norm]
          rfl
    exact Dist.ext hdist
  exact congrArg (fun d : MetricSpace K =>
    @UniformSpace.toTopologicalSpace K (@PseudoMetricSpace.toUniformSpace K
      (@MetricSpace.toPseudoMetricSpace K d))) hm

/-- The embedding is the original inclusion, with the separability witness attached. -/
def toSep : K →ₐ[ℚ_[p]] SeparableClosure ℚ_[p] :=
  K.val.codRestrict (separableClosure ℚ_[p] (PadicAlgCl p)).toSubalgebra
    (fun x => mem_separableClosure_iff.mpr
      ((Algebra.IsAlgebraic.isSeparable_of_perfectField (K := ℚ_[p]) (L := PadicAlgCl p)).isSeparable'
        (x : PadicAlgCl p)))

/-- Tau Ceti's map has exactly the expected embedded fixing subgroup as image. -/
theorem range_eq_fixing [FiniteDimensional ℚ_[p] K] :
    (TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K)).range =
      (K.fixingSubgroup : Subgroup (Field.absoluteGaloisGroup ℚ_[p])) := by
  ext g
  rw [TauCeti.mem_range_absoluteGaloisGroupExtend_iff, TauCeti.mem_galoisSubgroup_iff]
  let g' : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p := g
  change _ ↔ g' ∈ K.fixingSubgroup
  have hpoint (x : K) :
      ((TauCeti.absoluteGaloisGroupRestrictEquiv ℚ_[p] g) (toSep p K x) : PadicAlgCl p) = g' x :=
    TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply ℚ_[p] g' (toSep p K x)
  constructor
  · intro h
    apply (IntermediateField.mem_fixingSubgroup_iff K g').mpr
    intro x hx
    let a : K := ⟨x, hx⟩
    rw [← hpoint a, h a]
    rfl
  · intro h x
    apply Subtype.ext
    rw [hpoint x, (IntermediateField.mem_fixingSubgroup_iff K g').mp h x x.2]
    rfl

/-- The Artin map of the embedded finite extension, with its lexical local-field instances. -/
def artinK [FiniteDimensional ℚ_[p] K] : Kˣ →* Field.absoluteGaloisGroupAbelianization K :=
  letI := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[p] (PadicAlgCl p) K
  letI := TauCeti.finiteIntermediateFieldTopology ℚ_[p] (PadicAlgCl p) K
  letI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (PadicAlgCl p) K
  TauCeti.ClassFieldTheory.artinMap K

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A]

/-- Character-level norm functoriality, with the same absolute Galois group and the
same downstairs Artin map used by the projected character. -/
theorem character_norm [FiniteDimensional ℚ_[p] K]
    (ψ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* A) (u : Kˣ) :
    let τ := TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K)
    let ρ : Field.absoluteGaloisGroup K →ₜ* A := ψ.comp
      { toMonoidHom := τ
        continuous_toFun := TauCeti.continuous_absoluteGaloisGroupExtend ℚ_[p] K (toSep p K) }
    TopologicalAbelianization.lift ρ (artinK p K u) =
      TopologicalAbelianization.lift ψ
        (TauCeti.ClassFieldTheory.artinMap ℚ_[p] (TauCeti.Algebra.normUnits ℚ_[p] u)) := by
  let j := TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K)
  let ρ : Field.absoluteGaloisGroup K →ₜ* A := ψ.comp
    { toMonoidHom := j
      continuous_toFun := TauCeti.continuous_absoluteGaloisGroupExtend ℚ_[p] K (toSep p K) }
  change TopologicalAbelianization.lift ρ (artinK p K u) = _
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (artinK p K u)
  have hn : (j g : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      TauCeti.ClassFieldTheory.artinMap ℚ_[p] (TauCeti.Algebra.normUnits ℚ_[p] u) := by
    let _ := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[p] (PadicAlgCl p) K
    let _ := TauCeti.finiteIntermediateFieldTopology ℚ_[p] (PadicAlgCl p) K
    let _ := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (PadicAlgCl p) K
    have := TauCeti.finiteIntermediateField_valuativeExtension ℚ_[p] (PadicAlgCl p) K
    exact TauCeti.ClassFieldTheory.artinMap_norm K (toSep p K) u g hg
  rw [← hg, ← hn, TopologicalAbelianization.lift_mk, TopologicalAbelianization.lift_mk]
  rfl

/-- The same quantification over the restricted action, whether expressed with the
shared algebraic closure or with the absolute Galois group of the finite extension. -/
theorem forall_fixing_iff_forall_extend [FiniteDimensional ℚ_[p] K]
    (R : Field.absoluteGaloisGroup ℚ_[p] → Prop) :
    (∀ g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p, R (K.fixingSubgroupEquiv.symm g).val) ↔
      ∀ τ : Field.absoluteGaloisGroup K,
        R (TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K) τ) := by
  constructor
  · intro h τ
    let j := TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K)
    have ht : j τ ∈ (K.fixingSubgroup : Subgroup (Field.absoluteGaloisGroup ℚ_[p])) :=
      (range_eq_fixing p K) ▸ ⟨τ, rfl⟩
    simpa only [MulEquiv.symm_apply_apply] using h (K.fixingSubgroupEquiv ⟨j τ, ht⟩)
  · intro h g
    have hg : ((K.fixingSubgroupEquiv.symm g).val : Field.absoluteGaloisGroup ℚ_[p]) ∈
        (TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K)).range :=
      (range_eq_fixing p K).symm ▸ (K.fixingSubgroupEquiv.symm g).property
    obtain ⟨τ, hτ⟩ := hg
    exact hτ ▸ h τ

open scoped Topology
open _root_.ZInQ.Contrib.G9.PkgI4 (GQp cpAct cycPow)

/-- A continuous character on the project’s absolute Galois group, re-expressed without
changing its values or its topology. -/
def continuousCharacter (ψ : GQp p →* Kˣ)
    (hc : Continuous (fun g => (((ψ g : Kˣ) : K) : PadicAlgCl p))) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* Kˣ where
  toMonoidHom := ψ
  continuous_toFun := Units.isEmbedding_val₀.isInducing.continuous_iff.mpr
    (Topology.IsInducing.subtypeVal.continuous_iff.mpr hc)

/-- The unit sphere is open on the embedded coefficient field and on its unit group. -/
theorem normOne_isOpen : IsOpen {u : Kˣ | ‖((u : K) : PadicAlgCl p)‖ = 1} := by
  have hs : IsOpen {x : PadicAlgCl p | ‖x‖ = 1} := by
    let v : Valuation (PadicAlgCl p) NNReal := Valued.v
    have h := Valued.isOpen_sphere (PadicAlgCl p) (r := v.restrict 1) (by simp)
    convert h using 1
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, v.restrict_inj]
    change ‖x‖ = 1 ↔ ‖x‖₊ = ‖(1 : PadicAlgCl p)‖₊
    constructor
    · intro hx
      apply NNReal.eq
      simpa using hx
    · intro hx
      simpa using congrArg (fun a : NNReal => (a : ℝ)) hx
  exact hs.preimage (continuous_subtype_val.comp Units.continuous_val)

/-- A continuous unit-valued character of a compact group has norm-one values in the
coefficient field, expressed with the original ambient p-adic norm. -/
theorem character_norm_one (ψ : GQp p →* Kˣ)
    (hc : Continuous (fun g => (((ψ g : Kˣ) : K) : PadicAlgCl p)))
    (g : GQp p) : ‖(((ψ g : Kˣ) : K) : PadicAlgCl p)‖ = 1 := by
  let f : GQp p →* PadicAlgCl p :=
    { toFun := fun s => (((ψ s : Kˣ) : K) : PadicAlgCl p)
      map_one' := by simp
      map_mul' := fun a b => by simp }
  have hfc : Continuous (fun s => ‖f s‖) := hc.norm
  obtain ⟨B, hB⟩ := (isCompact_range hfc).bddAbove
  have hle (s : GQp p) : ‖f s‖ ≤ 1 := by
    by_contra! hz
    have hlarge := (tendsto_pow_atTop_atTop_of_one_lt hz).eventually
      (Filter.eventually_gt_atTop B)
    obtain ⟨n, hn⟩ := hlarge.exists
    exact (not_lt_of_ge (hB ⟨s ^ n, rfl⟩)) (by simpa only [map_pow, norm_pow] using hn)
  change ‖f g‖ = 1
  apply le_antisymm (hle g)
  have hginv : ‖(f g)⁻¹‖ ≤ 1 := by simpa only [map_inv] using hle g⁻¹
  have hne : f g ≠ 0 := by
    change (((ψ g : Kˣ) : K) : PadicAlgCl p) ≠ 0
    exact fun z => Units.ne_zero (ψ g) (K.val.injective (by simp at z))
  rw [norm_inv, inv_le_one₀ (norm_pos_iff.mpr hne)] at hginv
  exact hginv

/-- The continuous restriction of a character along the embedded Galois subgroup. -/
def restrictCharacter [FiniteDimensional ℚ_[p] K]
    (ψ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Kˣ) :
    Field.absoluteGaloisGroup K →ₜ* Kˣ := ψ.comp
  { toMonoidHom := TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K)
    continuous_toFun := TauCeti.continuous_absoluteGaloisGroupExtend ℚ_[p] K (toSep p K) }

/-- The open subgroup of units of the valuation ring, inside `Kˣ`. -/
def normOneUnits : Subgroup Kˣ where
  carrier := {u | ‖((u : K) : PadicAlgCl p)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ‖((a : K) : PadicAlgCl p)‖ = 1 at ha
    change ‖((b : K) : PadicAlgCl p)‖ = 1 at hb
    change ‖((a : K) : PadicAlgCl p) * ((b : K) : PadicAlgCl p)‖ = 1
    rw [norm_mul, ha, hb, mul_one]
  inv_mem' := by
    intro a ha
    change ‖((a : K) : PadicAlgCl p)‖ = 1 at ha
    change ‖((↑(a⁻¹) : K) : PadicAlgCl p)‖ = 1
    rw [Units.val_inv_eq_inv_val]
    change ‖K.val ((a : K)⁻¹)‖ = 1
    rw [map_inv₀ K.val, norm_inv]
    change ‖((a : K) : PadicAlgCl p)‖⁻¹ = 1
    rw [ha, inv_one]

/-- Passing between open subgroups of the norm-one units and open subgroups of the
field's units lying in the norm-one units, with the same predicate on members. -/
theorem openSubgroup_normOne_iff (P : Kˣ → Prop) :
    (∃ U : Subgroup (normOneUnits p K), IsOpen (U : Set (normOneUnits p K)) ∧
      ∀ u ∈ U, P u.val) ↔
    (∃ U : Subgroup Kˣ, IsOpen (U : Set Kˣ) ∧ ∀ u ∈ U,
      ‖((u : K) : PadicAlgCl p)‖ = 1 ∧ P u) := by
  constructor
  · rintro ⟨U, hU, hP⟩
    let V := U.map (normOneUnits p K).subtype
    refine ⟨V, ?_, ?_⟩
    · change IsOpen ((U.map (normOneUnits p K).subtype : Subgroup Kˣ) : Set Kˣ)
      rw [Subgroup.coe_map]
      exact (normOne_isOpen p K).isOpenMap_subtype_val _ hU
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      exact ⟨v.property, hP v hv⟩
  · rintro ⟨U, hU, hP⟩
    let V := U.comap (normOneUnits p K).subtype
    refine ⟨V, hU.preimage continuous_subtype_val, fun u hu => (hP u.val hu).2⟩

open ValuativeRel in
/-- The explicit unit subgroup in the transcription is exactly depth zero of the
actual local field's unit filtration. -/
theorem normOneUnits_eq_unitFiltration [FiniteDimensional ℚ_[p] K] :
    let _ := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[p] (PadicAlgCl p) K
    let _ := TauCeti.finiteIntermediateFieldTopology ℚ_[p] (PadicAlgCl p) K
    let _ := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (PadicAlgCl p) K
    normOneUnits p K = TauCeti.unitFiltration K 0 := by
  let _ := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[p] (PadicAlgCl p) K
  let _ := TauCeti.finiteIntermediateFieldTopology ℚ_[p] (PadicAlgCl p) K
  let _ := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (PadicAlgCl p) K
  let _ := TauCeti.finiteIntermediateFieldNormedField ℚ_[p] (PadicAlgCl p) K
  have := TauCeti.finiteIntermediateField_valuativeExtension ℚ_[p] (PadicAlgCl p) K
  ext u
  rw [TauCeti.mem_unitFiltration_zero]
  change ‖((u : K) : PadicAlgCl p)‖ = 1 ↔ valuation K (u : K) = 1
  rw [← norm_eq p K (u : K), ← norm_one (α := K), ← map_one (valuation K)]
  rw [le_antisymm_iff, @le_antisymm_iff _ _ (valuation K (u : K))]
  rw [← (valuation K).vle_iff_le, ← (valuation K).vle_iff_le]
  rw [TauCeti.vle_iff_algebraicExtensionNormedField_norm_le ℚ_[p],
    TauCeti.vle_iff_algebraicExtensionNormedField_norm_le ℚ_[p]]

/-- Serre's group `U_K`, as the actual depth-zero subgroup in the local-field
unit filtration, with the local-field structures installed lexically. -/
def serreUnits [FiniteDimensional ℚ_[p] K] : Subgroup Kˣ :=
  letI := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[p] (PadicAlgCl p) K
  letI := TauCeti.finiteIntermediateFieldTopology ℚ_[p] (PadicAlgCl p) K
  letI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (PadicAlgCl p) K
  TauCeti.unitFiltration K 0

/-- The depth-zero unit subgroup uses the inherited topology on `Kˣ`. -/
theorem serreUnits_eq_normOne [FiniteDimensional ℚ_[p] K] :
    serreUnits p K = normOneUnits p K :=
  (normOneUnits_eq_unitFiltration p K).symm

/-- Condition (ii): `σ ∘ ρ ∼ χ^m`. The comparison means that
`(σ ∘ ρ)⁻¹χ^m` has a nonzero period. The absolute action of `G_K` is transported
to the common completed algebraic closure. -/
def serreConditionII [FiniteDimensional ℚ_[p] K]
    (ρ : Field.absoluteGaloisGroup K →ₜ* Kˣ) (σ : K ≃ₐ[ℚ_[p]] K) (m : ℤ) : Prop :=
  ∃ b : ℂ_[p], b ≠ 0 ∧ ∀ τ : Field.absoluteGaloisGroup K,
    let g : GQp p := TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K) τ
    cpAct p g b = (algebraMap K ℂ_[p] (σ (ρ τ : K)))⁻¹ *
      algebraMap ℚ_[p] ℂ_[p] (cycPow p g m) * b

/-- Condition (iv): the character and the algebraic factor cancel on an open subgroup
of the integer units. For ground and coefficient field both `K`, the factor indexed
by `σ` uses `σ⁻¹` (the norm from `K` to `σK = K` is the identity). -/
def serreConditionIV [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ρ : Field.absoluteGaloisGroup K →ₜ* Kˣ)
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ) : Prop :=
  let _ : T1Space Kˣ :=
    (show Topology.IsEmbedding ((↑) : Kˣ → K) from Units.isEmbedding_val₀).t1Space
  ∃ U : Subgroup (serreUnits p K), IsOpen (U : Set (serreUnits p K)) ∧ ∀ u ∈ U,
    (TopologicalAbelianization.lift ρ (artinK p K u.val) : K) *
      ∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm ((u.val : Kˣ) : K) ^ n σ = 1

/-- The single printed input: Serre, *Abelian ℓ-adic representations and elliptic curves*,
Addison–Wesley (1989), Ch. III Appendix A6, Proposition 6 (iv), equivalence with
condition (ii) of A5, Theorem 2 (III-49–50 and III-44; all locators UNVERIFIED).
Here the coefficient field equals the ground field `K`, finite and Galois over `ℚ_p`;
`ρ` is any continuous character into the integer units of `K`.
Condition (iv) is at the arithmetic Artin map of `K` itself. -/
def SerreA6Prop6 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ρ : Field.absoluteGaloisGroup K →ₜ* Kˣ),
    (∀ τ, ρ τ ∈ serreUnits p K) →
    ∀ n : (K ≃ₐ[ℚ_[p]] K) → ℤ,
    (∀ σ, serreConditionII p K ρ σ (n σ)) ↔ serreConditionIV p K ρ n

/-- Provenance (c): specialize to the restricted character, transport the action, and
rewrite reciprocity by the norm. The norm form is a consequence of the single print. -/
theorem serreA6NormEquivalence_of_prop6 (h : SerreA6Prop6) : SerreA6NormEquivalence := by
  intro p _ K _ _ ψ hc n
  let ψc := continuousCharacter p K ψ hc
  let ρ := restrictCharacter p K ψc
  have hunit (τ : Field.absoluteGaloisGroup K) : ρ τ ∈ serreUnits p K := by
    rw [serreUnits_eq_normOne]
    exact character_norm_one p K ψ hc (TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K) τ)
  have changeGroup (σ : K ≃ₐ[ℚ_[p]] K) (b : ℂ_[p]) :=
    forall_fixing_iff_forall_extend p K (fun g =>
      cpAct p g b = (algebraMap K ℂ_[p] (σ (ψ g : K)))⁻¹ *
        algebraMap ℚ_[p] ℂ_[p] (cycPow p g (n σ)) * b)
  calc
    _ ↔ ∀ σ, serreConditionII p K ρ σ (n σ) := by
      exact forall_congr' fun σ => exists_congr fun b =>
        and_congr Iff.rfl (changeGroup σ b)
    _ ↔ serreConditionIV p K ρ n := h p K ρ hunit n
    _ ↔ _ := by
      unfold serreConditionIV SerreA6NormForm
      rw [serreUnits_eq_normOne]
      let _ : T1Space Kˣ :=
        (show Topology.IsEmbedding ((↑) : Kˣ → K) from Units.isEmbedding_val₀).t1Space
      let P (u : Kˣ) : Prop :=
        (TopologicalAbelianization.lift ρ (artinK p K u) : K) *
          ∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm (u : K) ^ n σ = 1
      refine (openSubgroup_normOne_iff p K P).trans ?_
      have hval (u : Kˣ) :
          TopologicalAbelianization.lift ρ (artinK p K u) =
            Bridges.conradAbelianChar p ψ hc
              (TauCeti.ClassFieldTheory.artinMap ℚ_[p] (TauCeti.Algebra.normUnits ℚ_[p] u)) :=
        character_norm p K ψc u
      simp only [P, hval]

#print axioms norm_eq
#print axioms topology_eq
#print axioms range_eq_fixing
#print axioms character_norm
#print axioms forall_fixing_iff_forall_extend
#print axioms normOne_isOpen
#print axioms character_norm_one
#print axioms openSubgroup_normOne_iff
#print axioms normOneUnits_eq_unitFiltration
#print axioms serreUnits_eq_normOne
#print axioms serreA6NormEquivalence_of_prop6

end HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin
