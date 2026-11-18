import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.Places
import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic

/-!
# UnramifiedComplex: inflation–restriction — `H¹_ur` is the kernel of restriction to inertia

Manuscript `diophantine_zq.tex`, tex 4699–4701 (the unramified condition injects in degree one;
its image is the unramified subgroup).

For a continuous surjection `π : Γ → G` (`Γ` compact, `G` Hausdorff) with kernel `I = inertia π`,
and a discrete continuous `G`-module `W` (so `I` acts trivially on `W`, `W^I = W`,
`inertia_acts_trivially`):

`0 → H¹(G, W^I) --infl--> H¹(Γ, W) --resInertia--> H¹(I, W)`

is exact on Mathlib's `continuousCohomology`: `infl_injective` (`Inflation.lean`) and
`h1ur_eq_ker_resInertia : range infl = ker resInertia`, where `resInertia` is Tau Ceti's
`ContinuousCohomology.res`. The proof is on Tau Ceti's explicit model (`range_inflE_eq_ker_resE`):
a cocycle vanishing on `I` (restriction classes vanish because `B¹(I, W) = 0`) is constant on the
fibres of `π`, so it descends to `G`, continuously because `π` is a closed map.

At a finite place (`π = resUr : G_{K_w} → Gal(K_w^ur/K_w)`): `ur_h1ur_eq_ker_resInertia` and the
node `UnramifiedInflationRestriction`.

Kinds: everything PROVED.
-/

open CategoryTheory TauCeti.ContCohomology
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {k : Type} [Ring k] [TopologicalSpace k] (X : TopRep.{0} k G)
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (π : Γ →ₜ* G)

attribute [local instance] TopRep.distribMulAction continuousSMul_resRep

/-- The inertia subgroup `I = ker (π : Γ → G)`. -/
abbrev inertia : Subgroup Γ := (π : Γ →* G).ker

/-- `W` as an `I`-module (restricted from `Γ`). -/
abbrev resI : TopRep k (inertia π) := TopRep.res ((inertia π).subtype) (resRep X π)

/-- The inertia acts trivially on `W`, so `W^I = W`. -/
theorem inertia_acts_trivially (i : inertia π) (m : X.V) : (resI X π).ρ i m = m := by
  change X.ρ (π (i : Γ)) m = m
  rw [show π (i : Γ) = 1 from i.2, map_one]
  rfl

/-- The inertia action is continuous. -/
theorem continuousSMul_resI [ContinuousSMul G X.V] : ContinuousSMul (inertia π) (resI X π).V :=
  ⟨(continuous_smul (M := Γ) (X := (resRep X π).V)).comp
    (continuous_subtype_val.prodMap continuous_id)⟩

attribute [local instance] continuousSMul_resI

/-- **Restriction to inertia** `H¹(Γ, W) → H¹(I, W)`. -/
def resInertia : continuousCohomology 1 (resRep X π) →ₗ[k] continuousCohomology 1 (resI X π) :=
  (TauCeti.ContinuousCohomology.res (inertia π) (resRep X π) 1).hom.toLinearMap

variable [ContinuousSMul G X.V] [DiscreteTopology X.V]

/-- Explicit inflation along `π`. -/
abbrev inflE : H1 G X.V →+ H1 Γ (resRep X π).V :=
  explicitMap1 G X.V Γ (resRep X π).V π (AddMonoidHom.id X.V) continuous_id (fun _ _ => rfl)

/-- Explicit restriction to inertia. -/
abbrev resE : H1 Γ (resRep X π).V →+ H1 (inertia π) (resI X π).V :=
  explicitMap1 Γ (resRep X π).V (inertia π) (resI X π).V
    (TauCeti.ContinuousMonoidHom.subgroupSubtype (inertia π)) (AddMonoidHom.id X.V) continuous_id
    (fun _ _ => rfl)

/-- Explicit inflation–restriction exactness. PROVED. -/
theorem range_inflE_eq_ker_resE [CompactSpace Γ] [T2Space G] (hπ : Function.Surjective π) :
    (inflE X π).range = (resE X π).ker := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    induction x using QuotientAddGroup.induction_on with
    | H f =>
      rw [AddMonoidHom.mem_ker]
      erw [explicitMap1_mk]
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      refine AddMonoidHom.mem_range.2 ⟨0, funext fun i => ?_⟩
      rw [map_zero, Pi.zero_apply]
      change (0 : X.V) = f.1 (π (i : Γ))
      rw [show π (i : Γ) = 1 from i.2, map_one_of_mem_Z1 f.2]
  · intro hy
    induction y using QuotientAddGroup.induction_on with
    | H c =>
      rw [AddMonoidHom.mem_ker] at hy
      erw [explicitMap1_mk] at hy
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hy
      obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 hy
      obtain ⟨hcont, hcoc⟩ := mem_Z1_iff.1 c.2
      -- `c` vanishes on the inertia
      have hI : ∀ i : Γ, π i = 1 → c.1 i = 0 := by
        intro i hi
        have := congrFun hm ⟨i, hi⟩
        change (π i • m - m : X.V) = c.1 i at this
        rw [hi, one_smul, sub_self] at this
        exact this.symm
      have hwd : ∀ γ γ' : Γ, π γ = π γ' → c.1 γ = c.1 γ' := by
        intro γ γ' h
        have h1 : π (γ⁻¹ * γ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
        have := hcoc γ (γ⁻¹ * γ')
        rw [mul_inv_cancel_left, hI _ h1, smul_zero, zero_add] at this
        exact this.symm
      let f : G → X.V := fun g => c.1 (Classical.choose (hπ g))
      have hf : ∀ γ, f (π γ) = c.1 γ := fun γ =>
        hwd _ _ (Classical.choose_spec (hπ (π γ)))
      have hfc : Continuous f := by
        rw [continuous_iff_isClosed]
        intro C _
        have : f ⁻¹' C = π '' (c.1 ⁻¹' C) := by
          ext g
          obtain ⟨γ, rfl⟩ := hπ g
          simp only [Set.mem_preimage, Set.mem_image, hf]
          constructor
          · intro h; exact ⟨γ, h, rfl⟩
          · rintro ⟨γ', h, hγ'⟩; rw [← hwd _ _ hγ']; exact h
        rw [this]
        exact ((isClosed_discrete C).preimage hcont).isCompact.image (map_continuous π)
          |>.isClosed
      have hfZ : f ∈ Z1 G X.V := by
        rw [mem_Z1_iff]
        refine ⟨hfc, fun g h => ?_⟩
        obtain ⟨γ, rfl⟩ := hπ g
        obtain ⟨η, rfl⟩ := hπ h
        rw [← map_mul, hf, hf, hf, hcoc]
        rfl
      refine ⟨QuotientAddGroup.mk ⟨f, hfZ⟩, ?_⟩
      erw [explicitMap1_mk]
      congr 1
      apply Subtype.ext
      funext γ
      exact hf γ

/-- **Inflation–restriction in degree one** (tex 4699–4701): for `π : Γ → G` surjective with `Γ`
compact and `G` Hausdorff, and `W` a discrete continuous `G`-module (so the inertia `I = ker π` acts
trivially and `W^I = W`, `inertia_acts_trivially`), the unramified classes `H¹_ur` (the image of
inflation, injective by `infl_injective`) are exactly the classes whose restriction to `I` vanishes:
`0 → H¹(G, W^I) → H¹(Γ, W) → H¹(I, W)` is exact. PROVED. -/
theorem h1ur_eq_ker_resInertia [CompactSpace Γ] [T2Space G] (hπ : Function.Surjective π) :
    h1ur X π = LinearMap.ker (resInertia X π) := by
  have key1 := X.explicitH1AddEquivContinuousCohomologyOfDiscrete_map (resRep X π) π
    (𝟙 (resRep X π)) (AddMonoidHom.id X.V) (fun _ => rfl) (fun _ _ => rfl)
  have key2 := (resRep X π).explicitH1AddEquivContinuousCohomologyOfDiscrete_map (resI X π)
    (TauCeti.ContinuousMonoidHom.subgroupSubtype (inertia π)) (𝟙 (resI X π))
    (AddMonoidHom.id X.V) (fun _ => rfl) (fun _ _ => rfl)
  have hex := range_inflE_eq_ker_resE X π hπ
  ext z
  obtain ⟨y, rfl⟩ := (resRep X π).explicitH1AddEquivContinuousCohomologyOfDiscrete.surjective z
  rw [LinearMap.mem_ker]
  change _ ↔ _root_.ContinuousCohomology.map _ _ 1
    ((resRep X π).explicitH1AddEquivContinuousCohomologyOfDiscrete y) = 0
  erw [key2, AddEquiv.map_eq_zero_iff]
  rw [← AddMonoidHom.mem_ker]
  change _ ↔ y ∈ (resE X π).ker
  rw [← hex]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := X.explicitH1AddEquivContinuousCohomologyOfDiscrete.surjective a
    have : _root_.ContinuousCohomology.map π (𝟙 (resRep X π)) 1
        (X.explicitH1AddEquivContinuousCohomologyOfDiscrete x) =
        (resRep X π).explicitH1AddEquivContinuousCohomologyOfDiscrete y := ha
    rw [key1] at this
    exact ⟨x, (resRep X π).explicitH1AddEquivContinuousCohomologyOfDiscrete.injective this⟩
  · rintro ⟨x, rfl⟩
    exact ⟨X.explicitH1AddEquivContinuousCohomologyOfDiscrete x, key1 x⟩

section Places

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.RankCounts

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

set_option synthInstance.maxHeartbeats 400000 in
/-- `G_{K_w}` is compact. -/
theorem compactSpace_absGal : CompactSpace (Field.absoluteGaloisGroup (w.adicCompletion K)) :=
  inferInstance

/-- **At a finite place `w`: `H¹_ur(K_w, W) = ker (H¹(G_{K_w}, W) → H¹(I_w, W))`** for a finite
discrete unramified module `W`, with `I_w = ker (G_{K_w} → Gal(K_w^ur/K_w))`. PROVED. -/
theorem ur_h1ur_eq_ker_resInertia {k : Type} [Ring k] [TopologicalSpace k]
    (X : TopRep.{0} k (GUr K w)) [ContinuousSMul (GUr K w) X.V] [DiscreteTopology X.V] :
    h1ur X (resUr K w) = LinearMap.ker (resInertia X (resUr K w)) :=
  have := compactSpace_absGal K w
  have : T2Space (GUr K w) := krullTopology_t2
  h1ur_eq_ker_resInertia X (resUr K w) (resUr_surjective K w)

/-- **Tex 4699–4701 (PROVED): inflation–restriction at a finite place.** For a discrete
continuous `Gal(K_w^ur/K_w)`-module `W` (unramified: the inertia `I_w` acts trivially, `W^{I_w} = W`),
`0 → H¹(Gal(K_w^ur/K_w), W^{I_w}) → H¹(G_{K_w}, W) → H¹(I_w, W)` is exact: inflation is injective
and its image, the unramified classes, is the kernel of restriction to inertia. -/
def UnramifiedInflationRestriction : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k : Type) [Ring k]
    [TopologicalSpace k] (X : TopRep.{0} k (GUr K w)) [ContinuousSMul (GUr K w) X.V]
    [DiscreteTopology X.V],
    (∀ (i : inertia (resUr K w)) (m : X.V), (resI X (resUr K w)).ρ i m = m) ∧
      Function.Injective (infl X (resUr K w)) ∧
      LinearMap.range (infl X (resUr K w)) = LinearMap.ker (resInertia X (resUr K w))

theorem unramifiedInflationRestriction_proof : UnramifiedInflationRestriction :=
  fun K _ _ w _ _ _ X _ _ => ⟨inertia_acts_trivially X (resUr K w),
    infl_injective X (resUr K w) (resUr_surjective K w), ur_h1ur_eq_ker_resInertia K w X⟩

end Places

end ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
