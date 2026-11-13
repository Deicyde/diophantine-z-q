/-! ## c9-rhof (wave 25; leaf-adopt3 fold): glue C9 for R16's `ρ_{f,ι}` (`LeafModCurves.rhoF`)

From `scratch/c9-rhof/C9.lean` (which imported `ZInQKernel.HDecomp.ModCurves.Glue`,
`ZInQKernel.HDecomp.I3Linalg.C2`, `ZInQKernel.HDecomp.I3Linalg.RhoCont`). Needs the e1-sub
fragment before it (for `GlueI3.isSemisimpleRepresentation_baseChange`, which needs glue-ssbc's
section `GlueSSBCSec`).
* Kernel `I3Linalg/RhoCont.lean` (glue-rho-cont), none of which is in Leaves.lean, is copied
  first, verbatim (namespaces `PkgI3.RhoCont`, `PkgI3.Tate`, and
  `PkgI3.continuous_galRep_of_tateModuleFree`). It declares the global instances
  `PkgI3.RhoCont.instTopologicalSpacePt`, `PkgI3.RhoCont.instTopologicalSpaceV` (module topology on
  `V_ℓ(A)`) and two `DiscreteTopology`/`IsModuleTopology` instances.
* The c9-rhof text is verbatim except: no import, no `#print axioms`; its §7 (`PkgI4.EigenformRepExists`,
  `PkgI4.EigenformTwist`, `PkgI4.NewformOfEigenform`, `PkgI4.GaloisRep.AttachedUpToTwist`) is deleted
  (identical copies already in Leaves.lean, section `PkgI4`); `open ... LeafModCurves` gets `hiding`.
  `C9Rhof.FrobeniusDense` (a verbatim copy of `HSyn.FrobeniusDense` over `PkgI4`'s names) is kept;
  bridges to the bundle forms are added at the end (`frobeniusDense_of_hsyn`, `c9_hsyn`, ...).
No proof holes (the task file's one occurrence of the word is in its module docstring, not copied). -/

section C9RhofSec

noncomputable section

/-! ### Kernel `I3Linalg/RhoCont.lean` §3 (verbatim; not in Leaves.lean) -/

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

/-! ### c9-rhof (verbatim from `scratch/c9-rhof/C9.lean`; §7 deleted as duplicate) -/

namespace C9Rhof

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
-- leaf-adopt3: `LeafModCurves` opened with `hiding` (Leaves.lean has `LeafModCurves` copies of
-- these `PkgI4` names; the kernel had none, so the names below are `PkgI4`'s as in the kernel)
open PkgI3 PkgI3.AbVar
open LeafModCurves hiding Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ## §1. `rhoF` as a quotient of `V_ℓ(A) ⊗ ℚ̄_ℓ` -/

section Quot

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

/-- Evaluation `v ↦ (φ ↦ φ v)`, `V_ℓ(A) → (ι-eigenfunctionals)^∨`, `ℚ_ℓ`-linear. -/
def ev : A.V ℓ →ₗ[ℚ_[ℓ]] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) where
  toFun v :=
    { toFun := fun φ => (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' v w := by
    ext φ
    simp
  map_smul' c v := by
    ext φ
    simp [Algebra.smul_def]

@[simp] theorem ev_apply (v : A.V ℓ) (φ : eigenFun ℓ A θ emb) :
    ev ℓ A θ emb v φ = (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v := rfl

/-- The `ℚ̄_ℓ`-linear extension `V_ℓ(A) ⊗_{ℚ_ℓ} ℚ̄_ℓ → (ι-eigenfunctionals)^∨` of `ev`. -/
def quotMap : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) →ₗ[PadicAlgCl ℓ]
    Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
  (ev ℓ A θ emb).liftBaseChange (PadicAlgCl ℓ)

theorem rhoF_ev (σ : GQ) (v : A.V ℓ) :
    rhoF ℓ A θ emb σ (ev ℓ A θ emb v) = ev ℓ A θ emb (A.galRep ℓ σ v) := by
  ext φ
  rfl

/-- `quotMap` is `G_ℚ`-equivariant from the base change of `ρ_ℓ` to `rhoF`. -/
theorem quotMap_equivariant (σ : GQ) (x : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)) :
    quotMap ℓ A θ emb (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ x) =
      rhoF ℓ A θ emb σ (quotMap ℓ A θ emb x) := by
  induction x using TensorProduct.inductionOn with
  | tmul e v =>
    change quotMap ℓ A θ emb ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) (e ⊗ₜ v)) = _
    rw [LinearMap.baseChange_tmul]
    simp only [quotMap, LinearMap.liftBaseChange_tmul, map_smul, rhoF_ev]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `quotMap` is onto when the eigenfunctionals are finite-dimensional. -/
theorem quotMap_surjective [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    Function.Surjective (quotMap ℓ A θ emb) := by
  rw [← LinearMap.range_eq_top, quotMap, LinearMap.range_liftBaseChange]
  apply Submodule.span_eq_top_of_ne_zero
  intro z hz
  have : (z : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) ≠ 0 := by
    intro h; exact hz (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, (z : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v ≠ 0 := by
    by_contra h
    push Not at h
    exact this (LinearMap.ext h)
  exact ⟨ev ℓ A θ emb v, ⟨v, rfl⟩, hv⟩

end Quot

/-! ## §2. Semisimplicity -/

section SS

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

instance : CharZero (PadicAlgCl ℓ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

/-- `V_ℓ(A)` is finite-dimensional over `ℚ_ℓ` (from the leaf I3.M0). -/
theorem finiteDimensional_V (hT : TateModuleFree) : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨h1, h2, -⟩ := hT ℚ A ℓ hℓ
  infer_instance

/-- **Semisimplicity of `ρ_{f,ι}` (GLUE, proved from Faltings' Satz 3 and I3.M0).** -/
theorem rhoF_semisimple (hS : FaltingsSemisimple) (hT : TateModuleFree)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    (rhoF ℓ A θ emb).IsSemisimpleRepresentation := by
  have := finiteDimensional_V ℓ A hT
  have h1 : (A.galRep ℓ).IsSemisimpleRepresentation := hS ℚ A ℓ
  have h2 := GlueI3.isSemisimpleRepresentation_baseChange (PadicAlgCl ℓ) (A.galRep ℓ) h1
  exact GlueI3.isSemisimple_of_surjective _ _ h2 (quotMap ℓ A θ emb)
    (quotMap_surjective ℓ A θ emb) (fun σ x => quotMap_equivariant ℓ A θ emb σ x)

/-- The same, in the form `GlueC10` consumes. -/
theorem rhoF_isSemisimpleModule (hS : FaltingsSemisimple) (hT : TateModuleFree)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) (rhoF ℓ A θ emb).asModule :=
  (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
    (rhoF_semisimple ℓ A θ emb hS hT)

end SS

/-! ## §3. Continuity -/

section Cont

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

/-- For every `x ∈ V_ℓ(A) ⊗ ℚ̄_ℓ` and every linear form `c` on `(ι-eigenfunctionals)^∨`,
`σ ↦ c(ρ_{f,ι}(σ) (quotMap x))` is continuous. -/
theorem continuous_coord (hT : TateModuleFree)
    (c : Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) →ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ)
    (x : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)) :
    Continuous fun σ : GQ => c (rhoF ℓ A θ emb σ (quotMap ℓ A θ emb x)) := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hρ : ∀ v : A.V ℓ, Continuous fun σ : GQ => A.galRep ℓ σ v := by
    intro v
    have h1 : Continuous fun σ : GQ => (σ, v) := continuous_id.prodMk continuous_const
    exact ((continuous_galRep_of_tateModuleFree hT A ℓ hℓ).1.comp h1).congr fun σ => rfl
  induction x using TensorProduct.inductionOn with
  | tmul e v =>
    have hL : Continuous ((c.restrictScalars ℚ_[ℓ]) ∘ₗ ev ℓ A θ emb) :=
      IsModuleTopology.continuous_of_linearMap _
    have : (fun σ : GQ => c (rhoF ℓ A θ emb σ (quotMap ℓ A θ emb (e ⊗ₜ v)))) =
        fun σ => e * ((c.restrictScalars ℚ_[ℓ]) ∘ₗ ev ℓ A θ emb) (A.galRep ℓ σ v) := by
      funext σ
      simp only [quotMap, LinearMap.liftBaseChange_tmul, map_smul, rhoF_ev, smul_eq_mul,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [this]
    exact continuous_const.mul (hL.comp (hρ v))
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

/-- **Continuity of `ρ_{f,ι}` (GLUE, proved from I3.M0).** In any finite basis `b` of the
representation space, `σ ↦ [ρ_{f,ι}(σ)]_b` is continuous (Krull topology on `G_ℚ`, the
spectral-norm topology on `ℚ̄_ℓ`). -/
theorem rhoF_continuous (hT : TateModuleFree)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))) :
    Continuous fun σ : GQ => LinearMap.toMatrix b b (rhoF ℓ A θ emb σ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  obtain ⟨x, hx⟩ := quotMap_surjective ℓ A θ emb (b j)
  refine (continuous_coord ℓ A θ emb hT (b.coord i) x).congr fun σ => ?_
  simp only [LinearMap.toMatrix_apply, Module.Basis.coord_apply, hx]

end Cont

/-! ## §4. Density of arithmetic Frobenius elements (leaf T18) -/

/-- **L18 = T18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. Copied verbatim from
`HSyn.FrobeniusDense` of `scratch/h-decomposition/Leaves.lean`. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- Two continuous functions on `G_ℚ` with Hausdorff values that agree at every arithmetic
Frobenius (`PkgI4.IsArithFrob`) above every prime outside `S` are equal (GLUE, proved from T18). -/
theorem eq_of_eq_on_arithFrob (hD : FrobeniusDense) {X : Type*} [TopologicalSpace X] [T2Space X]
    (S : Finset ℕ) (f₁ f₂ : GQ → X) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hfr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → f₁ τ = f₂ τ) : f₁ = f₂ := by
  funext g
  by_contra hne
  have hopen : IsOpen {x | f₁ x ≠ f₂ x} := isOpen_ne_fun h₁ h₂
  have hmem : (fun y => g * y) ⁻¹' {x | f₁ x ≠ f₂ x} ∈ nhds (1 : GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hne
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hmem
  have hU : IsOpen (E.fixingSubgroup : Set GQ) := IntermediateField.fixingSubgroup_isOpen E
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := hD E.fixingSubgroup hU g S
  have hfix : g⁻¹ * τ ∈ E.fixingSubgroup := by
    have := E.fixingSubgroup.inv_mem hU'
    simpa using this
  have := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_ofPred_eq] at this
  exact this (hfr p hp hpS v τ hv hτ)

/-! ## §5. Brauer–Nesbitt (leaf T19) with arithmetic Frobenius traces -/

section BN

variable {k V W ι κ : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Continuous representations with equal traces at arithmetic Frobenius outside `S` have equal
traces everywhere (GLUE, proved from T18). -/
theorem trace_eq_of_arithFrob (hD : FrobeniusDense) (S : Finset ℕ)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (ρ : Representation k GQ V) (σ : Representation k GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → LinearMap.trace k V (ρ τ) = LinearMap.trace k W (σ τ)) :
    ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g) :=
  congrFun (eq_of_eq_on_arithFrob hD S _ _ (GlueC10.continuous_trace bV ρ hρc)
    (GlueC10.continuous_trace bW σ hσc) htr)

/-- **C10-type comparison with `IsArithFrob` (GLUE, proved from T18 and T19).** -/
theorem iso_of_arithFrob [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W]
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense) (S : Finset ℕ)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (ρ : Representation k GQ V) (σ : Representation k GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k GQ) σ.asModule)
    (htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → LinearMap.trace k V (ρ τ) = LinearMap.trace k W (σ τ)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k GQ] σ.asModule) :=
  hBN k GQ V W ρ σ hρ hσ (trace_eq_of_arithFrob hD S bV bW ρ σ hρc hσc htr)

end BN

/-! ## §6. C9 -/

section C9

/-- The core of C9 for a fixed `A`, `θ`, `ι` (GLUE, proved). -/
theorem c9_core (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    (N : ℕ) (hN : 0 < N) {F : Type} [Field F] (a : ℕ → F)
    (A : AbVar ℚ) (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)
    (h2 : Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2)
    (hfr : ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
      LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb (a p))
    (S : Finset ℕ) {W κ : Type} [AddCommGroup W] [Module (PadicAlgCl ℓ) W]
    [FiniteDimensional (PadicAlgCl ℓ) W] [Fintype κ] [DecidableEq κ]
    (bW : Module.Basis κ (PadicAlgCl ℓ) W) (r : Representation (PadicAlgCl ℓ) GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bW bW (r g))
    (hr : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) r.asModule)
    (hatt : ∀ p, p.Prime → p ∉ S → ¬ p ∣ N * ℓ → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p → LinearMap.trace (PadicAlgCl ℓ) W (r τ) = emb (a p)) :
    (rhoF ℓ A θ emb).IsSemisimpleRepresentation ∧
      (∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
          (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))),
        Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ emb g)) ∧
      Nonempty (r.asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ] (rhoF ℓ A θ emb).asModule) ∧
      (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) W (r g) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g)) ∧
      (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) = emb (a p)) := by
  have hfd : FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
    Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hFrob : ∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
      LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) = emb (a p) := by
    intro g p hp hpN hg
    rw [trace_rhoF ℓ A θ emb h2]
    exact hfr p hp hpN g hg
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  have htr : ∀ p, p.Prime → p ∉ S ∪ (N * ℓ).primeFactors → ∀ (v : ValuationSubring Qbar)
      (τ : GQ), LiesOver v p → IsArithFrob τ v p → LinearMap.trace (PadicAlgCl ℓ) W (r τ) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb τ) := by
    intro p hp hpS v τ hv hτ
    have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
    have hpN : ¬ p ∣ N * ℓ := fun h =>
      hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hNℓ⟩))
    rw [hatt p hp hpS1 hpN v τ hv hτ, hFrob τ p hp hpN (isFrobAt_of_isArithFrob τ v p hp hv hτ)]
  have hcont : ∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
      (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))),
      Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ emb g) :=
    fun b => rhoF_continuous ℓ A θ emb hT b
  let bV := Module.finBasis (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))
  refine ⟨rhoF_semisimple ℓ A θ emb hS hT, hcont, ?_, ?_, hFrob⟩
  · exact iso_of_arithFrob hBN hD _ bW bV r _ hrc (hcont bV) hr
      (rhoF_isSemisimpleModule ℓ A θ emb hS hT) htr
  · exact trace_eq_of_arithFrob hD _ bW bV r _ hrc (hcont bV) htr

/-- **C9 (GLUE, proved from R16, Faltings' Satz 3, I3.M0, T18 and T19).** Let `f` be a newform of
weight 2, level `N` and nebentypus `χ`, `J` a `J₁(N)`, `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`. Let `r` be a
continuous semisimple finite-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` whose arithmetic
Frobenius traces outside a finite set `S` are those of `f` (through `ιC`, `ιL`). Then for R16's
`A_f` and `ρ_{f,ι} = rhoF` with `ι = ιL ∘ ιC⁻¹` (`embOf`):
(i) `ρ_{f,ι}` is 2-dimensional, semisimple and continuous;
(ii) `r ≅ ρ_{f,ι}` (Brauer–Nesbitt);
(iii) `tr r(g) = tr ρ_{f,ι}(g)` for every `g ∈ G_ℚ` (needs T18 and continuity only), which is the
hypothesis `h₅` of `GlueC10.c10`;
(iv) `tr ρ_{f,ι}(g) = ι(a_p(f))` at every `GlueC10.IsFrobAt g p`, `p ∤ Nℓ`: the hypothesis `hρ₅`. -/
theorem c9 (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ)
    (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (S : Finset ℕ) {W κ : Type} [AddCommGroup W] [Module (PadicAlgCl ℓ) W]
    [FiniteDimensional (PadicAlgCl ℓ) W] [Fintype κ] [DecidableEq κ]
    (bW : Module.Basis κ (PadicAlgCl ℓ) W) (r : Representation (PadicAlgCl ℓ) GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bW bW (r g))
    (hr : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) r.asModule)
    (hatt : ∀ p, p.Prime → p ∉ S → ¬ p ∣ N * ℓ → ∃ α : Qbar, ιC α = coeff f p ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        LinearMap.trace (PadicAlgCl ℓ) W (r τ) = ιL α) :
    ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
      (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
      Module.finrank (PadicAlgCl ℓ)
        (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f)))) = 2 ∧
      (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).IsSemisimpleRepresentation ∧
      (∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
          (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f))))),
        Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      Nonempty (r.asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
        (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
      (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) W (r g) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
          embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) := by
  obtain ⟨hfin, A, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  obtain ⟨h2, hfr⟩ := hrest ℓ (embOf ℓ ιC ιL (coeffField f))
  refine ⟨hfin, A, π, θ, hπ, finrank_rhoF ℓ A θ _ h2,
    c9_core ℓ hS hT hBN hD N hN (fun p => ⟨coeff f p, coeff_mem_coeffField f p⟩) A θ _ h2
      (fun p hp hpN σ hσ => (hfr p hp hpN σ hσ).1 _ rfl) S bW r hrc hr ?_⟩
  intro p hp hpS hpN v τ hv hτ
  obtain ⟨α, hα, hrα⟩ := hatt p hp hpS hpN
  rw [hrα v τ hv hτ]
  exact (embOf_spec ℓ ιC ιL (coeffField f) _ α hα).symm

end C9

end C9Rhof

namespace C9Rhof

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
-- leaf-adopt3: `LeafModCurves` opened with `hiding` (Leaves.lean has `LeafModCurves` copies of
-- these `PkgI4` names; the kernel had none, so the names below are `PkgI4`'s as in the kernel)
open PkgI3 PkgI3.AbVar
open LeafModCurves hiding Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform

/-! ## §8. `GaloisRep` (matrix form) as a `Representation` -/

section Bridge

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- A `GaloisRep` as a `Representation` on `ℚ̄_ℓ^n`. -/
def toRep (ρ : GaloisRep ℓ n) : Representation (PadicAlgCl ℓ) GQ (Fin n → PadicAlgCl ℓ) where
  toFun σ := Matrix.toLin' (ρ.mat σ)
  map_one' := by
    simp only [GaloisRep.mat, map_one, Units.val_one, Matrix.toLin'_one]; rfl
  map_mul' σ τ := by
    simp only [GaloisRep.mat, map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl

theorem toRep_apply (ρ : GaloisRep ℓ n) (σ : GQ) : toRep ρ σ = Matrix.toLin' (ρ.mat σ) := rfl

theorem toMatrix_toRep (ρ : GaloisRep ℓ n) (σ : GQ) :
    LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (toRep ρ σ) = ρ.mat σ := by
  rw [toRep_apply, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem toRep_continuous (ρ : GaloisRep ℓ n) :
    Continuous fun σ => LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (toRep ρ σ) := by
  simp_rw [toMatrix_toRep]
  exact Units.continuous_val.comp ρ.continuous_toHom

theorem trace_toRep (ρ : GaloisRep ℓ n) (σ : GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (toRep ρ σ) = (ρ.mat σ).trace := by
  rw [LinearMap.trace_eq_matrix_trace (PadicAlgCl ℓ) (Pi.basisFun (PadicAlgCl ℓ) (Fin n)),
    toMatrix_toRep]

/-- Invariant complements give a semisimple representation. -/
theorem semisimple_of_complements {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V)
    (h : ∀ W : Submodule k V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule k V, IsCompl W W' ∧ ∀ g, ∀ v ∈ W', ρ g v ∈ W') :
    ρ.IsSemisimpleRepresentation := by
  refine ⟨fun a => ?_⟩
  obtain ⟨W', hc, hW'⟩ := h a.toSubmodule (fun g v hv => a.apply_mem_toSubmodule g hv)
  refine ⟨⟨W', fun g v hv => hW' g v hv⟩, ⟨?_, ?_⟩⟩
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact hc.inf_eq_bot
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact hc.sup_eq_top

/-- `GaloisRep.IsSemisimple` gives a semisimple `MonoidAlgebra`-module. -/
theorem toRep_semisimple (ρ : GaloisRep ℓ n) (h : ρ.IsSemisimple) :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) (toRep ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  apply semisimple_of_complements
  intro W hW
  obtain ⟨W', hc, hW'⟩ := h W (fun σ => Submodule.map_le_iff_le_comap.mpr
    (fun v hv => hW σ v hv))
  exact ⟨W', hc, fun σ v hv => hW' σ (Submodule.mem_map_of_mem hv)⟩

/-- **Irreducible (Burnside form) implies semisimple (GLUE, proved).** If the image of `ρ` spans
`M_n(ℚ̄_ℓ)` as an algebra, the only invariant subspaces are `⊥` and `⊤`. -/
theorem isSemisimple_of_isIrreducible (ρ : GaloisRep ℓ n) (h : ρ.IsIrreducible) :
    ρ.IsSemisimple := by
  intro W hW
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {M | ∀ v ∈ W, M.mulVec v ∈ W}
      mul_mem' := fun {M N} hM hN v hv => by
        rw [← Matrix.mulVec_mulVec]; exact hM _ (hN v hv)
      add_mem' := fun {M N} hM hN v hv => by
        rw [Matrix.add_mulVec]; exact W.add_mem (hM v hv) (hN v hv)
      algebraMap_mem' := fun c v hv => by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.smul_mem c hv }
  have hrange : Set.range ρ.mat ⊆ S := by
    rintro _ ⟨σ, rfl⟩ v hv
    exact hW σ ⟨v, hv, rfl⟩
  have hall : ∀ M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ), ∀ v ∈ W, M.mulVec v ∈ W := by
    intro M
    have : M ∈ S := by
      have h1 := Algebra.adjoin_le hrange
      rw [h] at h1
      exact h1 Algebra.mem_top
    exact this
  by_cases hbot : W = ⊥
  · refine ⟨⊤, hbot ▸ isCompl_bot_top, fun σ => le_top⟩
  · obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw0 (funext hc)
    have htop : W = ⊤ := by
      rw [eq_top_iff]
      intro u _
      let M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) :=
        Matrix.of fun a b => if b = i then u a * (w i)⁻¹ else 0
      have hM : M.mulVec w = u := by
        funext a
        simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        field_simp
      rw [← hM]
      exact hall M w hwW
    refine ⟨⊥, htop ▸ isCompl_top_bot, fun σ => ?_⟩
    rw [Submodule.map_bot]

end Bridge

/-! ## §9. C9 against R14 and against C8's `r₅` -/

section Apps

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **C9 against R14 (GLUE, proved from R14, R16, Faltings' Satz 3, I3.M0, T18, T19).** For a
newform `f` of weight 2 and level `N`, a `J₁(N)` `J` and embeddings `ιC`, `ιL`: R14's semisimple
`ρ` attached to `f` is isomorphic to R16's `ρ_{f,ι}` (`ι = ιL ∘ ιC⁻¹`), and they have the same
trace at every `g ∈ G_ℚ`. -/
theorem c9_R14 (hR14 : PkgI4.EigenformRepExists) (hR16 : R16_EichlerShimuraJ1')
    (hS : FaltingsSemisimple) (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2)
    (hf : IsNewform f χ) (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep ρ).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        ∀ g : GQ, (ρ.mat g).trace =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) := by
  obtain ⟨ρ, hss, hatt⟩ := hR14 ℓ ιC ιL N 2 χ f hN (by norm_num) hf.1
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfin, A, π, θ, hπ, -, -, -, hiso, htr, -⟩ := c9 ℓ hR16 hS hT hBN hD N hN χ f hf J hJ
    ιC ιL (N * ℓ).primeFactors (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (toRep ρ)
    (toRep_continuous ρ) (toRep_semisimple ρ hss) (by
      intro p hp hpS _
      have hpN : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.mpr ⟨hp, h, hNℓ⟩)
      obtain ⟨-, α, hα, h⟩ := hatt p hp hpN
      exact ⟨α, hα, fun v τ hv hτ => by rw [trace_toRep]; exact h v τ hv hτ⟩)
  exact ⟨ρ, hss, hatt, hfin, A, π, θ, hπ, hiso, fun g => by rw [← trace_toRep]; exact htr g⟩

/-- **C9 for C8's `r₅` (GLUE, proved from T24 EigenformTwist, T25 NewformOfEigenform, R16,
Faltings' Satz 3, I3.M0, T18, T19).** C8's output: a semisimple `r : G_ℚ → GL₂(ℚ̄_ℓ)` attached up
to the twist `ψ` to a normalized eigenform `g` of weight 2 and level `M` (Pan's trace form,
`PkgI4.GaloisRep.AttachedUpToTwist`), where `ψ` is (at arithmetic Frobenius outside `S`) the
Dirichlet character `ψD` mod `m` through `ιC`, `ιL` (C8 steps 1-4: determinant argument and
Kronecker–Weber). Then there is a newform `f` of weight 2 and level `N ∣ M m²` such that for every
`J₁(N)`: `r ≅ ρ_{f,ι}` (`ι = ιL ∘ ιC⁻¹`), their traces agree on all of `G_ℚ` (`h₅` of
`GlueC10.c10`), and `tr ρ_{f,ι}(g) = ι(a_p(f))` at every `IsFrobAt g p`, `p ∤ Nℓ` (`hρ₅`).
The hypothesis `hr` follows from Pan's hypothesis `r.IsIrreducible` by
`isSemisimple_of_isIrreducible`. -/
theorem c9_r5 (hTw : PkgI4.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (M : ℕ) (hM : 0 < M) (χg : DirichletCharacter ℂ M) (g : CF M 2)
    (hg : IsNormalizedEigenform g χg) (m : ℕ) (hm : 0 < m) (ψD : DirichletCharacter ℂ m)
    (ψ : GaloisChar ℓ) (S : Finset ℕ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (hrg : r.AttachedUpToTwist ψ ιC ιL g S)
    (hψ : ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        (ψ.toHom τ : PadicAlgCl ℓ) = ιL β) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N ∧ N ∣ M * m ^ 2 ∧
      IsNewform f χ ∧ ∀ J : AbVar ℚ, IsJ1 N J →
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep r).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) _ (toRep r g) =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
        (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
            embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) := by
  obtain ⟨χ', g', hg', hcoef⟩ := hTw M m 2 χg ψD g hM hm hg
  obtain ⟨N, χ, f, hN, hNd, hf, hcf⟩ := hNew (M * m ^ 2) 2 χ' g' (by positivity) hg'
  refine ⟨N, χ, f, hN, hNd, hf, fun J hJ => ?_⟩
  have hMm : M * m ≠ 0 := Nat.mul_ne_zero hM.ne' hm.ne'
  obtain ⟨hfin, A, π, θ, hπ, -, -, -, hiso, htr, hFrob⟩ := c9 ℓ hR16 hS hT hBN hD N hN χ f hf J
    hJ ιC ιL (S ∪ (M * m).primeFactors) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (toRep r)
    (toRep_continuous r) (toRep_semisimple r hr) (by
      intro p hp hpS _
      have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
      have hpMm : ¬ p ∣ M * m := fun h =>
        hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hMm⟩))
      have hpMm2 : ¬ p ∣ M * m ^ 2 := by
        intro h
        rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
        · exact hpMm (dvd_mul_of_dvd_left h1 _)
        · exact hpMm (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h1) _)
      obtain ⟨-, α, hα, htrα⟩ := hrg p hp hpS1
      obtain ⟨β, hβ, hψp⟩ := hψ p hp hpS1
      refine ⟨β * α, ?_, fun v τ hv hτ => ?_⟩
      · rw [map_mul, hβ, hα, hcf p hp hpMm2, hcoef p hp hpMm]
      · rw [trace_toRep, htrα v τ hv hτ, hψp v τ hv hτ, map_mul])
  exact ⟨hfin, A, π, θ, hπ, hiso, htr, hFrob⟩

/-- **C9's outputs fit `GlueC10.c10` (GLUE, proved).** With `ρ₅ := ρ_{f,ι}` (`rhoF`), C9's
trace identity `tr r₅ = tr ρ_{f,ι}` (from `c9`, `c9_r5`) is `h₅`, and its Frobenius clause is
`hρ₅` for every `S` containing the primes of `Nℓ`; the remaining inputs of `c10` (the
abelian-variety traces `hr₅`, `hr₃` and the data at 3) are passed through. -/
theorem c10_via_c9 (hC : GlueC10.ChebotarevExists) (hBN : GlueC10.BrauerNesbittChar0)
    (N : ℕ) {C : Type} [Field C] (c a : ℕ → C) (A : AbVar ℚ) (θ : C →+* A.End0)
    (emb : C →+* PadicAlgCl ℓ) (S : Finset ℕ) (hSN : ∀ p, p.Prime → p ∣ N * ℓ → p ∈ S)
    {V₅ : Type} [AddCommGroup V₅] [Module (PadicAlgCl ℓ) V₅]
    (r₅ : Representation (PadicAlgCl ℓ) GQ V₅)
    (h₅ : ∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) V₅ (r₅ g) =
      LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g))
    (hFrob : ∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
      LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) = emb (a p))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace (PadicAlgCl ℓ) V₅ (r₅ g) = emb (c p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GQ V) (ρ₃ : Representation k GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GQ] ρ₃.asModule) :=
  GlueC10.c10 hC hBN S C c a (PadicAlgCl ℓ) V₅ _ emb r₅ (rhoF ℓ A θ emb)
    (fun g _ _ _ _ => h₅ g) hr₅
    (fun g p hp hpS hg => hFrob g p hp (fun h => hpS (hSN p hp h)) hg)
    k V W ι κ ι₃ bV bW r₃ ρ₃ hrc hρc hr hρ hr₃ hρ₃

end Apps

/-! ## leaf-adopt3: bridges to the bundle forms of the leaves

`TextbookLeaves.t18 : HSyn.FrobeniusDense`, `ResearchLeaves.r14 : HSyn.EigenformRepExists` and
`TextbookLeaves.t24 : HSyn.EigenformTwist` are stated over `HSyn`'s copies of `Qbar`, `GQ`,
`LiesOver`, `IsArithFrob`, `GaloisRep`, `CF`, `coeff`, `IsNormalizedEigenform`; this file uses
`PkgI4`'s (same bodies). The three conversions are definitional unfoldings. -/

section HSynBridges

/-- T18, bundle form (`HSyn.FrobeniusDense`, field `t18`) ⇒ this file's verbatim copy. -/
theorem frobeniusDense_of_hsyn (h : HSyn.FrobeniusDense) : FrobeniusDense := by
  intro U hU σ S
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := h U hU σ S
  exact ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩

/-- R14, bundle form (`HSyn.EigenformRepExists`, field `r14`, over `HSyn.GaloisRep`) ⇒
`PkgI4.EigenformRepExists` (the same statement over `PkgI4.GaloisRep`). -/
theorem eigenformRepExists_of_hsyn (h : HSyn.EigenformRepExists) :
    PkgI4.EigenformRepExists := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hss, hatt⟩ := h ℓ ιC ιL N k χ g hN hk hg
  exact ⟨⟨ρ.toHom, ρ.continuous_toHom⟩, hss, hatt⟩

/-- T24, bundle form (`HSyn.EigenformTwist`, field `t24`) ⇒ `PkgI4.EigenformTwist`. -/
theorem eigenformTwist_of_hsyn (h : HSyn.EigenformTwist) : PkgI4.EigenformTwist := by
  intro N m k χ ψ g hN hm hg
  obtain ⟨χ', g', hg', hc⟩ := h N m k χ ψ g hN hm hg
  exact ⟨χ', g', hg', hc⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **C9, bundle form**: `c9` with T18 as `HSyn.FrobeniusDense` (field `t18`). Other hypotheses:
R16 (`r16`), Faltings Satz 3 (`r9a`), I3.M0 (`t26`), T19 module form
(`GlueC10.BrauerNesbittChar0`; proved by t-skolem-kw, `TSkolemKW.brauerNesbittChar0`). -/
theorem c9_hsyn (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : HSyn.FrobeniusDense)
    (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ)
    (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (S : Finset ℕ) {W κ : Type} [AddCommGroup W] [Module (PadicAlgCl ℓ) W]
    [FiniteDimensional (PadicAlgCl ℓ) W] [Fintype κ] [DecidableEq κ]
    (bW : Module.Basis κ (PadicAlgCl ℓ) W) (r : Representation (PadicAlgCl ℓ) GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bW bW (r g))
    (hr : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) r.asModule)
    (hatt : ∀ p, p.Prime → p ∉ S → ¬ p ∣ N * ℓ → ∃ α : Qbar, ιC α = coeff f p ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        LinearMap.trace (PadicAlgCl ℓ) W (r τ) = ιL α) :
    ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
      (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
      Module.finrank (PadicAlgCl ℓ)
        (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f)))) = 2 ∧
      (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).IsSemisimpleRepresentation ∧
      (∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
          (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f))))),
        Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      Nonempty (r.asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
        (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
      (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) W (r g) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
          embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) :=
  c9 ℓ hR16 hS hT hBN (frobeniusDense_of_hsyn hD) N hN χ f hf J hJ ιC ιL S bW r hrc hr hatt

/-- **C9 against R14, bundle form** (`r14`, `r16`, `r9a`, `t26`, `t18`; T19 module form). -/
theorem c9_R14_hsyn (hR14 : HSyn.EigenformRepExists) (hR16 : R16_EichlerShimuraJ1')
    (hS : FaltingsSemisimple) (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : HSyn.FrobeniusDense) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2)
    (hf : IsNewform f χ) (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep ρ).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        ∀ g : GQ, (ρ.mat g).trace =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) :=
  c9_R14 ℓ (eigenformRepExists_of_hsyn hR14) hR16 hS hT hBN (frobeniusDense_of_hsyn hD) N hN χ f
    hf J hJ ιC ιL

/-- **C9 for C8's `r₅`, bundle form** (`t24`, `t25`, `r16`, `r9a`, `t26`, `t18`; T19 module
form). -/
theorem c9_r5_hsyn (hTw : HSyn.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : HSyn.FrobeniusDense)
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (M : ℕ) (hM : 0 < M) (χg : DirichletCharacter ℂ M) (g : CF M 2)
    (hg : IsNormalizedEigenform g χg) (m : ℕ) (hm : 0 < m) (ψD : DirichletCharacter ℂ m)
    (ψ : GaloisChar ℓ) (S : Finset ℕ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (hrg : r.AttachedUpToTwist ψ ιC ιL g S)
    (hψ : ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        (ψ.toHom τ : PadicAlgCl ℓ) = ιL β) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N ∧ N ∣ M * m ^ 2 ∧
      IsNewform f χ ∧ ∀ J : AbVar ℚ, IsJ1 N J →
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep r).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) _ (toRep r g) =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
        (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
            embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) :=
  c9_r5 ℓ (eigenformTwist_of_hsyn hTw) hNew hR16 hS hT hBN (frobeniusDense_of_hsyn hD) ιC ιL M hM
    χg g hg m hm ψD ψ S r hr hrg hψ

end HSynBridges

end C9Rhof

end

end C9RhofSec
