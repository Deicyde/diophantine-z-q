import ZInQKernel.Contrib.G9.I4Layer
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Padic
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift
import ZInQKernel.Contrib.CloudB3E1SerreAppB.SerreA6

/-!
# Serre's condition (iv) at the Artin map of `K`, and the norm rewrite

This module removes the GLUE step of `SerreA6Print` (`SerreA6.lean`). `serreA6OnIntegerUnits`
transcribes Serre, *Abelian `l`-adic representations and elliptic curves*, Addison-Wesley 1989,
III-44 (A5, Theorem 2 (ii)) ⇔ III-49/50 (A6, Proposition 6 (iv)), with admissibility as on
III-34 (A2). It is specialized to ground field = coefficient field = a finite Galois `K/ℚ_p`
inside `ℚ̄_p`, and to `ρ = ψ|_{G_K}`. In (iv), `U'` is an open subgroup of Serre's `U_K`, here
depth zero of Tau Ceti's unit filtration of `K`, and `ρ` is evaluated at Tau Ceti's local Artin
map of `K`. The local-field structure on `K` is Tau Ceti's `finiteIntermediateField…`
construction, installed lexically. It is compared with the inherited norm and topology
(`norm_eq`, `topology_eq`) and with the fixing subgroup of `K` in `G_{ℚ_p}`
(`range_eq_fixing`).

`serreA6Print_of_integerUnits` then proves `SerreA6Print` from `serreA6OnIntegerUnits`. The
norm rewrite in (iv) is now a theorem (Tau Ceti `artinMap_norm`), not GLUE.

Source notes (page-checked in the 1989 edition):

* III-38 (A3): the coefficient field `E` is a finite extension of `ℚ_p` whose conjugates
  lie in the ground field `K`. Here `E = K` and `K/ℚ_p` is Galois (normal).
* III-34 (A2, Remark 1): `φ ∼ φ'` means `φ⁻¹ φ'` is admissible. `serreConditionII`
  writes the admissibility of `(σ ∘ ρ)⁻¹ χ^n` with that inverse character.
* III-47–49 (A6): `r_σ = σ⁻¹ ∘ N_{K/σE}`. For `E = K` Galois, `σE = K` and `r_σ = σ⁻¹`,
  which is the factor `σ.symm u ^ n σ` in (iv).
* III-42 (A4, Remark) and III-2 (Example 1): the reciprocity map is arithmetically
  normalized, `χ(i(u)) = u⁻¹` on units. This is Tau Ceti's normalization (`IsArtinLift`).
  The trivial-character check `serreA6_integerUnits_trivial` tests the model, not the sign.
* Serre's `ρ` takes values in `U_E`. For a continuous `ψ : G_{ℚ_p} → K^×` this holds
  automatically by compactness (`character_norm_one`).

Kind: `serreA6OnIntegerUnits` is the named input (PRINT, pending independent source review);
everything else is proved.
-/
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

/-- Every Artin class upstairs has a lift in the original fixing subgroup whose Artin
class downstairs is the norm. The local-field instances are confined to this statement. -/
theorem exists_norm_artin_lift [FiniteDimensional ℚ_[p] K] (u : Kˣ) :
    ∃ (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p),
      (QuotientGroup.mk (α := Field.absoluteGaloisGroup ℚ_[p])
          (K.fixingSubgroupEquiv.symm g).val : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
        TauCeti.ClassFieldTheory.artinMap ℚ_[p] (TauCeti.Algebra.normUnits ℚ_[p] u) := by
  let _ := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[p] (PadicAlgCl p) K
  let _ := TauCeti.finiteIntermediateFieldTopology ℚ_[p] (PadicAlgCl p) K
  let _ := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (PadicAlgCl p) K
  have := TauCeti.finiteIntermediateField_valuativeExtension ℚ_[p] (PadicAlgCl p) K
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective
    (TauCeti.ClassFieldTheory.artinMap K u)
  let γ := TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K) τ
  have hγ : γ ∈ (K.fixingSubgroup : Subgroup (Field.absoluteGaloisGroup ℚ_[p])) := by
    rw [← range_eq_fixing p K]
    exact ⟨τ, rfl⟩
  refine ⟨K.fixingSubgroupEquiv ⟨γ, hγ⟩, ?_⟩
  rw [MulEquiv.symm_apply_apply]
  exact TauCeti.ClassFieldTheory.artinMap_norm K (toSep p K) u τ hτ

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

/-- The open-subgroup formulation of the character norm rewrite. The same predicate `P`
is used on both sides; no special property of the exponent or product is assumed. -/
theorem open_subgroup_norm_iff [FiniteDimensional ℚ_[p] K]
    {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A]
    (ψ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* A) (P : Kˣ → A → Prop) :
    let j : Field.absoluteGaloisGroup K →ₜ* Field.absoluteGaloisGroup ℚ_[p] :=
      { toMonoidHom := TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K)
        continuous_toFun := TauCeti.continuous_absoluteGaloisGroupExtend ℚ_[p] K (toSep p K) }
    (∃ U : Subgroup Kˣ, IsOpen (U : Set Kˣ) ∧ ∀ u ∈ U,
      P u (TopologicalAbelianization.lift (ψ.comp j) (artinK p K u))) ↔
    (∃ U : Subgroup Kˣ, IsOpen (U : Set Kˣ) ∧ ∀ u ∈ U,
      P u (TopologicalAbelianization.lift ψ
        (TauCeti.ClassFieldTheory.artinMap ℚ_[p] (TauCeti.Algebra.normUnits ℚ_[p] u)))) := by
  simp only [character_norm]

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

/-- Serre III-A6, Prop. 6(iv), in the case that the ground and Galois coefficient
fields are both `K`: evaluate the restricted character at the Artin map of `K` itself.
The norm-one constraint identifies the open subgroup with one in the units of the
ring of integers; this unit group is open in `Kˣ`. -/
def serreConditionIV [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : GQp p →* Kˣ) (hc : Continuous (fun g => (((ψ g : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ) : Prop :=
  let _ : T1Space Kˣ :=
    (show Topology.IsEmbedding ((↑) : Kˣ → K) from Units.isEmbedding_val₀).t1Space
  ∃ U : Subgroup Kˣ, IsOpen (U : Set Kˣ) ∧ ∀ u ∈ U,
    ‖((u : K) : PadicAlgCl p)‖ = 1 ∧
    (TopologicalAbelianization.lift (restrictCharacter p K (continuousCharacter p K ψ hc))
      (artinK p K u) : K) * ∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm (u : K) ^ n σ = 1

/-- The same formula after the proved Artin norm rewrite, with no new hypothesis. -/
def serreNormConditionIV [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : GQp p →* Kˣ) (hc : Continuous (fun g => (((ψ g : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ) : Prop :=
  let _ : T1Space Kˣ :=
    (show Topology.IsEmbedding ((↑) : Kˣ → K) from Units.isEmbedding_val₀).t1Space
  ∃ U : Subgroup Kˣ, IsOpen (U : Set Kˣ) ∧ ∀ u ∈ U,
    ‖((u : K) : PadicAlgCl p)‖ = 1 ∧
    (TopologicalAbelianization.lift (continuousCharacter p K ψ hc)
      (TauCeti.ClassFieldTheory.artinMap ℚ_[p] (TauCeti.Algebra.normUnits ℚ_[p] u)) : K) *
        ∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm (u : K) ^ n σ = 1

/-- The norm-functoriality reading of Serre (iv) is a theorem for the genuine data. -/
theorem serreConditionIV_iff_norm [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : GQp p →* Kˣ) (hc : Continuous (fun g => (((ψ g : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ) :
    serreConditionIV p K ψ hc n ↔ serreNormConditionIV p K ψ hc n := by
  simp only [serreConditionIV, serreNormConditionIV, restrictCharacter, character_norm]

/-- Serre III-A5, Theorem 2(ii), with admissibility as in III-A2, for the
restriction of the given character to the absolute Galois group of `K`. -/
def serreConditionII [FiniteDimensional ℚ_[p] K] (ψ : GQp p →* Kˣ)
    (σ : K ≃ₐ[ℚ_[p]] K) (n : ℤ) : Prop :=
  ∃ b : ℂ_[p], b ≠ 0 ∧ ∀ τ : Field.absoluteGaloisGroup K,
    let g : GQp p := TauCeti.absoluteGaloisGroupExtend ℚ_[p] K (toSep p K) τ
    cpAct p g b = (algebraMap K ℂ_[p] (σ (ψ g : K)))⁻¹ *
      algebraMap ℚ_[p] ℂ_[p] (cycPow p g n) * b

/-- Serre, *Abelian ℓ-adic representations and elliptic curves*, Addison–Wesley
(1989), III-A5 Thm. 2(ii), p. III-44, and III-A6 Prop. 6(iv), pp. III-49–50.
Specialized to a finite Galois extension used as both the coefficient and ground field,
and to a representation restricted from the absolute Galois group of `ℚ_p`.
The character in (iv) is evaluated at the Artin map of `K`, before the norm rewrite. -/
def serreA6Local : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : GQp p →* Kˣ) (hc : Continuous (fun g => (((ψ g : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ),
    (∀ σ, serreConditionII p K ψ σ (n σ)) ↔ serreConditionIV p K ψ hc n

/-- Change from Serre's own absolute Galois model to the fixing subgroup in the common closure,
and from its Artin-map expression to the norm-rewritten expression. -/
theorem serreA6_norm_form_of_local (h : serreA6Local) [FiniteDimensional ℚ_[p] K]
    [IsGalois ℚ_[p] K] (ψ : GQp p →* Kˣ)
    (hc : Continuous (fun g => (((ψ g : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ) :
    (∀ σ : K ≃ₐ[ℚ_[p]] K, ∃ b : ℂ_[p], b ≠ 0 ∧
      ∀ τ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p,
        let g := (K.fixingSubgroupEquiv.symm τ).val
        cpAct p g b = (algebraMap K ℂ_[p] (σ (ψ g : K)))⁻¹ *
          algebraMap ℚ_[p] ℂ_[p] (cycPow p g (n σ)) * b) ↔
        serreNormConditionIV p K ψ hc n := by
  have changeGroup (σ : K ≃ₐ[ℚ_[p]] K) (b : ℂ_[p]) :=
    forall_fixing_iff_forall_extend p K (fun g =>
      cpAct p g b = (algebraMap K ℂ_[p] (σ (ψ g : K)))⁻¹ *
        algebraMap ℚ_[p] ℂ_[p] (cycPow p g (n σ)) * b)
  calc
    _ ↔ ∀ σ, serreConditionII p K ψ σ (n σ) := by
      simp only [serreConditionII, changeGroup]
    _ ↔ serreConditionIV p K ψ hc n := h p K ψ hc n
    _ ↔ _ := serreConditionIV_iff_norm p K ψ hc n

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

/-- Serre III-A6, Proposition 6(iv), with its open subgroup taken inside `U_K`
itself and with the character evaluated at the Artin map of `K`. -/
def serreConditionIVUnits [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : GQp p →* Kˣ) (hc : Continuous (fun g => (((ψ g : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ) : Prop :=
  let _ : T1Space Kˣ :=
    (show Topology.IsEmbedding ((↑) : Kˣ → K) from Units.isEmbedding_val₀).t1Space
  ∃ U : Subgroup (serreUnits p K), IsOpen (U : Set (serreUnits p K)) ∧ ∀ u ∈ U,
    (TopologicalAbelianization.lift (restrictCharacter p K (continuousCharacter p K ψ hc))
      (artinK p K u.val) : K) * ∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm ((u.val : Kˣ) : K) ^ n σ = 1

/-- Proposed print: Serre, *Abelian ℓ-adic representations and elliptic curves*,
Addison–Wesley (1989), III-A5 Thm. 2(ii), p. III-44, and III-A6 Prop. 6(iv), pp. III-49–50,
with admissibility as in III-A2, p. III-34. Specialize both ground and coefficient fields
to the same finite Galois extension of `ℚ_p`, and restrict the continuous character
from `G_ℚp`. The right side uses Serre's open subgroup of `U_K` and local Artin map at `K`. -/
def serreA6OnIntegerUnits : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : GQp p →* Kˣ) (hc : Continuous (fun g => (((ψ g : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ),
    (∀ σ, serreConditionII p K ψ σ (n σ)) ↔ serreConditionIVUnits p K ψ hc n

/-- Read the open subgroup of `U_K` as an open subgroup of `Kˣ` whose elements
have norm one. -/
theorem serreA6Local_of_integerUnits (h : serreA6OnIntegerUnits) : serreA6Local := by
  intro p _ K _ _ ψ hc n
  apply (h p K ψ hc n).trans
  unfold serreConditionIVUnits serreConditionIV
  rw [serreUnits_eq_normOne p K]
  let _ : T1Space Kˣ :=
    (show Topology.IsEmbedding ((↑) : Kˣ → K) from Units.isEmbedding_val₀).t1Space
  exact openSubgroup_normOne_iff p K (fun u =>
    (TopologicalAbelianization.lift (restrictCharacter p K (continuousCharacter p K ψ hc))
      (artinK p K u) : K) * ∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm (u : K) ^ n σ = 1)

/-- Regression check: the genuine trivial character has weight zero and satisfies the printed
open-subgroup identity on the whole group of integer units, not just at the identity. -/
theorem serreA6_integerUnits_trivial [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K] :
    (∀ σ : K ≃ₐ[ℚ_[p]] K, serreConditionII p K 1 σ 0) ∧
      serreConditionIVUnits p K 1 (by simpa using (continuous_const :
        Continuous (fun _ : GQp p => (1 : PadicAlgCl p)))) (fun _ => 0) := by
  constructor
  · intro σ
    refine ⟨1, one_ne_zero, fun τ => ?_⟩
    simp [cycPow, map_one]
    rfl
  · unfold serreConditionIVUnits
    refine ⟨⊤, by simp, fun u _ => ?_⟩
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinK p K u.val)
    rw [← hτ, TopologicalAbelianization.lift_mk]
    simp [restrictCharacter, continuousCharacter]
    rfl

/-- **The GLUE step of `SerreA6Print` is a theorem.** The integer-unit form of Serre's
(ii) ⇔ (iv), evaluated at the Artin map of `K` itself, implies `SerreA6Print`, whose (iv) side
is read through norm functoriality. The rewrite is Tau Ceti's `artinMap_norm` at the local-field
structure on `K` (`character_norm`), transported to the fixing subgroup of `K` in `G_{ℚ_p}`
(`forall_fixing_iff_forall_extend`) and to open subgroups of `Kˣ` made of units
(`openSubgroup_normOne_iff`). Kind: proved from the named input `serreA6OnIntegerUnits`. -/
theorem serreA6Print_of_integerUnits (h : serreA6OnIntegerUnits) :
    HDec.G0Galois.C8Conrad.SerreAppB.SerreA6Print := by
  intro p _ K _ _ ψ hc n
  exact serreA6_norm_form_of_local p K (serreA6Local_of_integerUnits h) ψ hc n

end HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin
