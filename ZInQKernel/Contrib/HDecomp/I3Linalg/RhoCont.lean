import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.FieldTheory.KrullTopology
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Topology.Instances.Matrix
import ZInQKernel.HDecomp.Objects

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-rho-cont/RhoCont.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-
glue-rho-cont: continuity of the ℓ-adic Galois representation of pkg-I3.

Sections 1-2 are copied verbatim from scratch/pkg-I3/I3.lean (lines 15-335: the definitions
`Tate.T`, `AbVar`, `Pt`, `galAct`, `galT`, `galRep`, unchanged), plus six imports needed for
section 3 (module topology, Krull topology, residue fields, proper morphisms, base change of
bases, matrix topology). Section 3 is new: the topology on `T_ℓ`, open stabilizers on `A(K̄)`,
continuity of `ρ_ℓ` on `T_ℓ(A)` and on `V_ℓ(A)`. No sorry; axioms propext, Classical.choice,
Quot.sound (see the `#print axioms` at the end).
-/

noncomputable section

/-! pkg-I3's object layer and leaves (§1-§4 of the draft, a verbatim copy of
`scratch/pkg-I3/I3.lean`) are imported from `ZInQKernel.HDecomp.Objects` (§A), whose
QM leaf is `PkgI3.QMDichotomyYu`. -/

/-! ## 3. Continuity of `ρ_ℓ` (new: task glue-rho-cont) -/

/-! ### 3a. A discrete action with open stabilizers is continuous -/

namespace PkgI3.RhoCont

theorem continuous_orbit {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [DiscreteTopology X] (act : G → X → X)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x))
    (hstab : ∀ x, ∃ H : OpenSubgroup G, ∀ g ∈ H, act g x = x) (x : X) :
    Continuous (fun g => act g x) := by
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_forall_mem_open]
  intro g₀ hg₀
  obtain ⟨H, hH⟩ := hstab x
  refine ⟨(fun g => g₀⁻¹ * g) ⁻¹' (H : Set G), ?_,
    H.isOpen.preimage (continuous_const.mul continuous_id), by simp⟩
  intro g hg
  simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe] at hg hg₀ ⊢
  have : g = g₀ * (g₀⁻¹ * g) := by group
  rw [this, hmul, hH _ hg, hg₀]

theorem continuous_act {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [DiscreteTopology X] (act : G → X → X)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x))
    (hstab : ∀ x, ∃ H : OpenSubgroup G, ∀ g ∈ H, act g x = x) :
    Continuous (fun p : G × X => act p.1 p.2) :=
  continuous_prod_of_discrete_right.2 (continuous_orbit act hmul hstab)

end PkgI3.RhoCont

/-! ### 3b. The inverse-limit topology on `T_ℓ(M)` for a discrete group `M`

`T ℓ M` is a subgroup of `ℕ → M`; with `M` discrete it carries the subspace topology of the
product, i.e. the inverse-limit topology of the discrete groups `M[ℓⁿ]` (Mathlib's instances,
no new definition). -/

namespace PkgI3.Tate

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M]

omit hℓ in
lemma isOpen_coord_eq (n : ℕ) (m : M) : IsOpen {x : T ℓ M | x.1 n = m} := by
  have hc : Continuous (fun x : T ℓ M => x.1 n) := (continuous_apply n).comp continuous_subtype_val
  exact hc.isOpen_preimage {m} (isOpen_discrete _)

omit hℓ [TopologicalSpace M] [DiscreteTopology M] in
lemma pow_smul_shift {x : ℕ → M} (hx : x ∈ T ℓ M) (n k : ℕ) : (ℓ ^ n) • x (k + n) = x k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, ← add_assoc, hx.2 (k + n), ih]

omit [TopologicalSpace M] [DiscreteTopology M] in
/-- The kernel of the `n`-th coordinate is `ℓⁿ T_ℓ(M)`. -/
lemma coord_eq_zero_iff (x : T ℓ M) (n : ℕ) :
    x.1 n = 0 ↔ ∃ y : T ℓ M, x = ((ℓ : ℤ_[ℓ]) ^ n) • y := by
  constructor
  · intro hx
    let y : T ℓ M := ⟨fun k => x.1 (n + k), by simpa using hx, fun k => by
      show ℓ • x.1 (n + (k + 1)) = x.1 (n + k)
      rw [← add_assoc]; exact x.2.2 (n + k)⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext; funext k
    change x.1 k = smulSeq ((ℓ : ℤ_[ℓ]) ^ n) y.1 k
    rw [smulSeq_congr y.2 k (c := ℓ ^ n) (by rw [map_pow, map_natCast, Nat.cast_pow])]
    change x.1 k = (ℓ ^ n) • x.1 (n + k)
    rw [add_comm n k, pow_smul_shift x.2 n k]
  · rintro ⟨y, rfl⟩
    rw [smul_apply]
    have : (PadicInt.toZModPow n ((ℓ : ℤ_[ℓ]) ^ n)) = 0 := by
      rw [map_pow, map_natCast]; exact_mod_cast ZMod.natCast_self (ℓ ^ n)
    rw [this, ZMod.val_zero, zero_smul]

end PkgI3.Tate

namespace PkgI3.Tate

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M]

/-- The inverse-limit topology on `T_ℓ(M)` is the `ℓ`-adic one: every `ℤ_ℓ`-linear functional
`T_ℓ(M) → ℤ_ℓ` is continuous. -/
theorem continuous_of_linearMap_padicInt (c : T ℓ M →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) : Continuous c := by
  apply continuous_of_continuousAt_zero c
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt ℓ hε
  filter_upwards [(isOpen_coord_eq (ℓ := ℓ) (M := M) n 0).mem_nhds rfl] with x hx
  obtain ⟨y, rfl⟩ := (coord_eq_zero_iff x n).1 hx
  rw [map_smul, dist_zero_right, smul_eq_mul, norm_mul, PadicInt.norm_p_pow]
  calc (ℓ : ℝ) ^ (-(n : ℤ)) * ‖c y‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (zpow_nonneg (Nat.cast_nonneg _) _)
    _ < ε := by simpa using hn

omit hℓ [TopologicalSpace M] [DiscreteTopology M] in
lemma coord_eq_zero_of_le {x : T ℓ M} {n k : ℕ} (hx : x.1 n = 0) (hk : k ≤ n) : x.1 k = 0 := by
  rw [← pow_smul_shift x.2 (n - k) k, Nat.add_sub_cancel' hk, hx, smul_zero]

omit hℓ in
/-- **The inverse-limit topology is the `ℓ`-adic topology.** The sets `{x | xₙ = 0} = ℓⁿ T_ℓ(M)`
(`coord_eq_zero_iff`) form a basis of neighbourhoods of `0`. -/
theorem nhds_zero_hasBasis :
    (nhds (0 : T ℓ M)).HasBasis (fun _ : ℕ => True) (fun n => {x : T ℓ M | x.1 n = 0}) := by
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨n, _, hn⟩ =>
    Filter.mem_of_superset ((isOpen_coord_eq n 0).mem_nhds rfl) hn⟩⟩
  rw [nhds_subtype, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hIt⟩ := hV
  refine ⟨I.sup id, trivial, fun x hx => hVU (hIt fun k hk => ?_)⟩
  have hk' : k ≤ I.sup id := Finset.le_sup (f := id) hk
  show x.1 k ∈ t k
  rw [coord_eq_zero_of_le hx hk']
  exact mem_of_mem_nhds (ht k)

omit [DiscreteTopology M] in
/-- Functoriality is jointly continuous: if `G` acts continuously on the discrete group `M`, the
induced action on `T_ℓ(M)` is continuous. -/
theorem continuous_map_action {G : Type*} [TopologicalSpace G] (act : G → (M →+ M))
    (hc : Continuous (fun p : G × M => act p.1 p.2)) :
    Continuous (fun p : G × T ℓ M => map (ℓ := ℓ) (act p.1) p.2) := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro n
  exact hc.comp (continuous_fst.prodMk
    ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd)))

end PkgI3.Tate

/-! ### 3c. Open stabilizers on `A(K̄)`

Each `K̄`-point `P` of a scheme locally of finite type over `K` is fixed by the open subgroup
`Gal(K̄/E)` for a finite extension `E/K`: the stalk map `κ = 𝒪_{A,x} → K̄` of `P` is determined
by finitely many values (`𝒪_{A,x}` is essentially of finite type over `K`), and these generate
a finite extension `E` because `K̄/K` is algebraic. -/

namespace PkgI3.RhoCont

open CategoryTheory AlgebraicGeometry Limits AbVar

universe u

variable {K : Type u} [Field K]

local notation "Kbar" => AlgebraicClosure K

lemma stalkClosedPointTo_comp_galois
    (g : Spec (CommRingCat.of Kbar) ⟶ Spec (CommRingCat.of K))
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) (σ : Kbar ≃ₐ[K] Kbar) :
    Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom (σ : Kbar →+* Kbar) =
      Scheme.stalkClosedPointTo g := by
  subst hg
  ext y
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ y
  have hUtop : U = ⊤ := by
    ext z
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : z = (Spec.map (CommRingCat.ofHom (algebraMap K Kbar)))
        (IsLocalRing.closedPoint Kbar) := Subsingleton.elim _ _
    rw [this]; exact hU
  subst hUtop
  have h := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap K Kbar))
  have h2 : (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) ≫
        CommRingCat.ofHom (σ : Kbar →+* Kbar) =
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) := by
    rw [← Category.assoc, h, Category.assoc, ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    exact σ.commutes c
  exact congrArg (fun φ => φ.hom s) h2

/-- **Open stabilizers.** Every `K̄`-point of an abelian variety (indeed of any `K`-scheme locally
of finite type) is fixed by an open subgroup of `G_K`. -/
theorem exists_openSubgroup_galAct_eq (A : AbVar K) (P : A.Pt Kbar) :
    ∃ H : OpenSubgroup (Field.absoluteGaloisGroup K), ∀ σ ∈ H, A.galAct σ P = P := by
  set p : Spec (CommRingCat.of Kbar) ⟶ A.X.left := P.left with hp
  set x := p (IsLocalRing.closedPoint Kbar)
  set s := Scheme.stalkClosedPointTo p
  have hfin : (A.X.hom.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap (f := A.X.hom)
      x
  let S : Set Kbar := s.hom '' (hfin.finset : Set _)
  have : Finite S := ((hfin.finset.finite_toSet).image _).to_subtype
  let E := IntermediateField.adjoin K S
  have : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin (fun z _ => Algebra.IsIntegral.isIntegral z)
  refine ⟨⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩, fun (σ : Kbar ≃ₐ[K] Kbar) hσ => ?_⟩
  have key : s ≫ CommRingCat.ofHom (σ : Kbar →+* Kbar) = s := by
    apply CommRingCat.hom_ext
    refine RingHom.EssFiniteType.ext hfin ?_ ?_
    · have hw : p ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Kbar)) := by
        simpa [ptObj] using Over.w P
      have h := stalkClosedPointTo_comp_galois (p ≫ A.X.hom) hw σ
      rw [Scheme.stalkClosedPointTo_comp] at h
      have := congrArg CommRingCat.Hom.hom h
      simp only [CommRingCat.hom_comp, RingHom.comp_assoc] at this ⊢
      exact this
    · intro y hy
      exact (IntermediateField.mem_fixingSubgroup_iff E σ).1 hσ _
        (IntermediateField.subset_adjoin K S ⟨y, hy, rfl⟩)
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (σ : Kbar →+* Kbar)) ≫ p = p
  conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk p]
  rw [← Spec.map_comp_assoc, key, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

end PkgI3.RhoCont

/-! ### 3d. Continuity of `ρ_ℓ` on `T_ℓ(A)` and on `V_ℓ(A)` -/

namespace PkgI3.RhoCont

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj AbVar
open scoped TensorProduct

universe u

variable {K : Type u} [Field K]

local notation "Kbar" => AlgebraicClosure K

/-- `A(K̄)` with the discrete topology (so `A[ℓⁿ](K̄)` is discrete and `T_ℓ(A)` carries the
inverse-limit topology of section 3b). -/
instance instTopologicalSpacePt (A : AbVar K) : TopologicalSpace (Additive (A.Pt Kbar)) := ⊥

instance (A : AbVar K) : DiscreteTopology (Additive (A.Pt Kbar)) := ⟨rfl⟩

lemma galAct_mul (A : AbVar K) (σ τ : Field.absoluteGaloisGroup K) (P : A.Pt Kbar) :
    A.galAct (σ * τ) P = A.galAct σ (A.galAct τ P) := by
  have h := galHom_mul (K := K) (L := Kbar) σ τ
  exact (congrArg (· ≫ P) h).trans (Category.assoc _ _ _)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`ρ_ℓ` is continuous on `T_ℓ(A)`**: the action map `G_K × T_ℓ(A) → T_ℓ(A)` is continuous
for the Krull topology on `G_K` and the inverse-limit topology on `T_ℓ(A)`. Unconditional. -/
theorem continuous_galT (A : AbVar K) :
    Continuous (fun p : Field.absoluteGaloisGroup K × A.T ℓ => A.galT p.1 p.2) := by
  apply Tate.continuous_map_action (act := fun σ => MonoidHom.toAdditive (A.galAct (L := Kbar) σ))
  exact continuous_act (fun σ (m : Additive (A.Pt Kbar)) => MonoidHom.toAdditive (A.galAct (L :=
      Kbar) σ) m)
    (fun σ τ m => galAct_mul A σ τ (Additive.toMul m))
    (fun m => exists_openSubgroup_galAct_eq A (Additive.toMul m))

/-- The `ℓ`-adic topology on `V_ℓ(A)`: the module topology over `ℚ_ℓ` (when `T_ℓ(A) ≅ ℤ_ℓ^r`,
this is the product topology of `ℚ_ℓ^r`, see `continuous_galRep`). -/
instance instTopologicalSpaceV (A : AbVar K) : TopologicalSpace (A.V ℓ) :=
  moduleTopology ℚ_[ℓ] (A.V ℓ)

instance (A : AbVar K) : IsModuleTopology ℚ_[ℓ] (A.V ℓ) := ⟨rfl⟩

/-- `T_ℓ(A) → V_ℓ(A)`, `x ↦ 1 ⊗ x`, is continuous when `T_ℓ(A)` is free of finite rank. -/
theorem continuous_one_tmul (A : AbVar K) [Module.Free ℤ_[ℓ] (A.T ℓ)]
    [Module.Finite ℤ_[ℓ] (A.T ℓ)] :
    Continuous (fun x : A.T ℓ => (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) := by
  have := IsModuleTopology.toContinuousAdd ℚ_[ℓ] (A.V ℓ)
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  have h : (fun x : A.T ℓ => (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) = fun x =>
      ∑ i, ((b.coord i x : ℤ_[ℓ]) : ℚ_[ℓ]) • (b.baseChange ℚ_[ℓ] i) := by
    funext x
    conv_lhs => rw [← b.sum_repr x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, Module.Basis.baseChange_apply, Module.Basis.coord_apply,
      ← algebraMap_smul ℚ_[ℓ] (b.repr x i)]
    rfl
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_smul.comp ((continuous_subtype_val.comp
    (Tate.continuous_of_linearMap_padicInt (b.coord i))).prodMk continuous_const)

/-- **`ρ_ℓ` is continuous on `V_ℓ(A)`**: if `T_ℓ(A)` is free of finite rank over `ℤ_ℓ` (Mumford,
leaf I3.M0 `TateModuleFree`), the action map `G_K × V_ℓ(A) → V_ℓ(A)` is continuous for the Krull
topology and the `ℓ`-adic topology. -/
theorem continuous_galRep (A : AbVar K) [Module.Free ℤ_[ℓ] (A.T ℓ)]
    [Module.Finite ℤ_[ℓ] (A.T ℓ)] :
    Continuous (fun p : Field.absoluteGaloisGroup K × A.V ℓ => A.galRep ℓ p.1 p.2) := by
  have := IsModuleTopology.toContinuousAdd ℚ_[ℓ] (A.V ℓ)
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  let bV := b.baseChange ℚ_[ℓ]
  have h : (fun p : Field.absoluteGaloisGroup K × A.V ℓ => A.galRep ℓ p.1 p.2) = fun p =>
      ∑ j, bV.coord j p.2 • ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] A.galT p.1 (b j)) := by
    funext ⟨σ, v⟩
    conv_lhs => rw [← bV.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Module.Basis.coord_apply]
    congr 1
    change (A.galT σ).baseChange ℚ_[ℓ] (bV j) = _
    rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
  rw [h]
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_smul.comp
    (((IsModuleTopology.continuous_of_linearMap (bV.coord j)).comp continuous_snd).prodMk
      ((continuous_one_tmul ℓ A).comp
        ((continuous_galT ℓ A).comp (continuous_fst.prodMk continuous_const))))

/-- **Continuous traces** (the input C10 needs: Chebotarev density with Brauer–Nesbitt):
`σ ↦ tr ρ_ℓ(σ)` is continuous `G_K → ℚ_ℓ`. -/
theorem continuous_trace_galRep (A : AbVar K) [Module.Free ℤ_[ℓ] (A.T ℓ)]
    [Module.Finite ℤ_[ℓ] (A.T ℓ)] :
    Continuous (fun σ : Field.absoluteGaloisGroup K =>
      LinearMap.trace ℚ_[ℓ] (A.V ℓ) (A.galRep ℓ σ)) := by
  have := IsModuleTopology.toContinuousAdd ℚ_[ℓ] (A.V ℓ)
  let bV := (Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)).baseChange ℚ_[ℓ]
  have h : (fun σ : Field.absoluteGaloisGroup K =>
      LinearMap.trace ℚ_[ℓ] (A.V ℓ) (A.galRep ℓ σ)) =
      fun σ => ∑ i, bV.coord i (A.galRep ℓ σ (bV i)) := by
    funext σ
    classical
    rw [LinearMap.trace_eq_matrix_trace ℚ_[ℓ] bV]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
      Module.Basis.coord_apply]
  have hρ : ∀ v : A.V ℓ, Continuous (fun σ : Field.absoluteGaloisGroup K => A.galRep ℓ σ v) := by
    intro v
    have h1 : Continuous (fun σ : Field.absoluteGaloisGroup K => (σ, v)) :=
      continuous_id.prodMk continuous_const
    have h2 := (continuous_galRep ℓ A).comp h1
    refine h2.congr fun σ => ?_
    simp only [Function.comp_apply]
  have hc : ∀ i, Continuous (bV.coord i) := fun i =>
    IsModuleTopology.continuous_of_linearMap (bV.coord i)
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  refine ((hc i).comp (hρ (bV i))).congr fun σ => ?_
  simp only [Function.comp_apply]

/-- **Matrix form (`ρ_ℓ : G_K → GL_r(ℚ_ℓ)` continuous).** In any finite `ℚ_ℓ`-basis `b` of
`V_ℓ(A)`, the matrix of `ρ_ℓ(σ)` depends continuously on `σ` (entrywise topology). -/
theorem continuous_toMatrix_galRep (A : AbVar K) [Module.Free ℤ_[ℓ] (A.T ℓ)]
    [Module.Finite ℤ_[ℓ] (A.T ℓ)] {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    Continuous (fun σ : Field.absoluteGaloisGroup K => LinearMap.toMatrix b b (A.galRep ℓ σ)) := by
  have := IsModuleTopology.toContinuousAdd ℚ_[ℓ] (A.V ℓ)
  have hρ : ∀ v : A.V ℓ, Continuous (fun σ : Field.absoluteGaloisGroup K => A.galRep ℓ σ v) := by
    intro v
    have h1 : Continuous (fun σ : Field.absoluteGaloisGroup K => (σ, v)) :=
      continuous_id.prodMk continuous_const
    refine ((continuous_galRep ℓ A).comp h1).congr fun σ => ?_
    simp only [Function.comp_apply]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine ((IsModuleTopology.continuous_of_linearMap (b.coord i)).comp (hρ (b j))).congr
    fun σ => ?_
  simp only [Function.comp_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end PkgI3.RhoCont

/-! ### 3e. With pkg-I3's leaf I3.M0 -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj AbVar

/-! `TateModuleFree` (leaf I3.M0) is `PkgI3.TateModuleFree` of `Objects`. -/

/-- **Continuity of `ρ_ℓ` from leaf I3.M0.** For `ℓ ≠ char K` (every `ℓ` for a number field),
`ρ_ℓ : G_K × V_ℓ(A) → V_ℓ(A)` is continuous and `σ ↦ tr ρ_ℓ(σ)` is continuous. -/
theorem continuous_galRep_of_tateModuleFree (hT : TateModuleFree) {K : Type} [Field K]
    (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    Continuous (fun p : Field.absoluteGaloisGroup K × A.V ℓ => A.galRep ℓ p.1 p.2) ∧
      Continuous (fun σ : Field.absoluteGaloisGroup K =>
        LinearMap.trace ℚ_[ℓ] (A.V ℓ) (A.galRep ℓ σ)) := by
  obtain ⟨h1, h2, -⟩ := hT K A ℓ hℓ
  exact ⟨RhoCont.continuous_galRep ℓ A, RhoCont.continuous_trace_galRep ℓ A⟩

end PkgI3

