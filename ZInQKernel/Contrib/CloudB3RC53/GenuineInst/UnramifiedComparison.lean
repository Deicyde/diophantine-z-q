import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.CdOne

/-!
# Genuine instantiations, part 3: the unramified condition is a quasi-isomorphism onto the
unramified part

Manuscript `diophantine_zq.tex`, tex 3478–3487 (the unramified complex `[Φ−1]` as the condition at
the new places) and tex 4699–4701 (it has the degree-zero invariants of the full local complex and
injects in degree one).

The other team's `urToLocal e π X f hf : [W --(Φ−1)--> W] ⟶ C^•_cont(G, M)` (degree `0`:
constants; degree `1`: `x ↦ (g ↦ f (c_x (π g)))` with the `ℤ̂`-cocycle `c_x = urCocycle e X x`) and
its place form `urToLocal_galois` are compared with `urH0Equiv`, `urH1Equiv` and inflation:

* `homologyπ_h1Iso_hom`, `h1Iso_homologyπ`: `h1Iso` sends the class of a `1`-cycle to its value in
  `W ⧸ (Φ − 1)W`;
* `h1Equiv_homologyπ`: `urH1Equiv` sends it to the class of `c_x` (Tau Ceti's explicit model);
* `urToLocal_one_apply`, **`urToLocal_H1`**: the `H¹` map induced by `urToLocal` is `urH1Equiv`
  followed by inflation along `π` and `f` (`explicitMap1 π f`);
* `explicitMap1_injective`, **`urToLocal_H1_injective_range`**: for `π` surjective and `f`
  bijective it is injective, with image the inflated classes — the unramified part `H¹_ur`;
* `urToLocal_zero_apply`, `urToLocal_zero_invariant`: in degree `0`, `x ∈ ker (Φ − 1) = W^H` goes
  to the invariant `f x`;
* node `UrToLocalOntoUnramified` at a place of a number field (`π = resUr`, surjective), together
  with the vanishing in degrees `≥ 2` on both sides (`CdOne`).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open CategoryTheory Limits TauCeti.ContCohomology ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Manuscript.RC.SelmerComplex

section H1Iso

variable {k : Type} [Ring k] {W : Type} [AddCommGroup W] [Module k W] (Φ : W →ₗ[k] W)

/-- **`h1Iso` on classes**: the class of a `1`-cycle `c` of `[W --(Φ−1)--> W]` goes to the class
of its value in `W ⧸ (Φ − 1)W`. -/
theorem homologyπ_h1Iso_hom : (frobCx Φ).homologyπ 1 ≫ (h1Iso Φ).hom =
    (frobCx Φ).iCycles 1 ≫ (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Φ - 1)) rel01
      (by decide)).hom ≫ ModuleCat.ofHom (LinearMap.range (Φ - 1)).mkQ := by
  have e : (h1Iso Φ).hom = (frobCx Φ).homologyι 1 ≫
      ((frobCx Φ).opcyclesIsoSc' 0 1 2 prev1 next1).hom ≫
      (ShortComplex.opcyclesIsoCokernel _).hom ≫ (cokernelIsoOfEq ((frobCx_d01 Φ).trans
        (Category.assoc _ _ _).symm)).hom ≫
      (cokernelCompIsIso ((HomologicalComplex.doubleXIso₀ _ rel01).hom ≫ ModuleCat.ofHom (Φ - 1))
        (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Φ - 1)) rel01 (by decide)).inv).hom ≫
      (cokernelEpiComp (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Φ - 1)) rel01).hom
        (ModuleCat.ofHom (Φ - 1))).hom ≫
      (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom (Φ - 1))).hom := rfl
  rw [e, HomologicalComplex.homology_π_ι_assoc,
    HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom_assoc]
  simp [ShortComplex.opcyclesIsoCokernel_hom, cokernelCompIsIso_hom, cokernelEpiComp_hom]
  erw [π_comp_cokernelIsoOfEq_hom_assoc, cokernel.π_desc_assoc]
  erw [Category.assoc, cokernel.π_desc_assoc, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]

/-- The value in `W` of a `1`-cycle of `[W --(Φ−1)--> W]`. -/
abbrev cycVal1 (c : (frobCx Φ).cycles 1) : W :=
  (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Φ - 1)) rel01 (by decide)).hom.hom
    (((frobCx Φ).iCycles 1).hom c)

theorem h1Iso_homologyπ (c : (frobCx Φ).cycles 1) :
    (h1Iso Φ).hom (((frobCx Φ).homologyπ 1).hom c) = Submodule.Quotient.mk (cycVal1 Φ c) :=
  congrArg (fun g => g.hom c) (homologyπ_h1Iso_hom Φ)

end H1Iso

section Agree

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]

/-- **`urH1Equiv` on classes** (read through Tau Ceti's explicit comparison): the class of a
`1`-cycle with value `x` goes to the class of the cocycle `c_x` (`urCocycle`). -/
theorem h1Equiv_homologyπ (c : (frobCx (frob e X)).cycles 1) :
    X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm
        (h1Equiv e X (((frobCx (frob e X)).homologyπ 1).hom c)) =
      H1pi H X.V ⟨urCocycle e X (cycVal1 (frob e X) c), urCocycle_mem e X _⟩ := by
  have h0 : X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm
      (h1Equiv e X (((frobCx (frob e X)).homologyπ 1).hom c)) =
      (h1CoinvEquiv e X).symm ((h1Iso (frob e X)).hom (((frobCx (frob e X)).homologyπ 1).hom c)) := by
    simp only [h1Equiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rfl
  rw [h0, h1Iso_homologyπ, AddEquiv.symm_apply_eq]
  change _ = h1ToCoinv e X (QuotientAddGroup.mk _)
  rw [h1ToCoinv_mk]
  exact congrArg _ (urCocycle_frob e X _).symm

variable {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)

/-- The degree-`1` image under `urToLocal` of a `1`-cycle with value `x` is the cocycle
`g ↦ f (c_x (π g))`, the inflation of `c_x` along `π` pushed by `f`. -/
theorem urToLocal_one_apply (c : (frobCx (frob e X)).cycles 1) (g : G) :
    contFun (k := k) (G := G) (M := M)
        (((urToLocal e π X f hf).f 1).hom (((frobCx (frob e X)).iCycles 1).hom c)) (fun _ => g) =
      f (urCocycle e X (cycVal1 (frob e X) c) (π g)) := by
  rw [urToLocal_f₁]
  rfl

/-- **The `H¹` map induced by `urToLocal` is `urH1Equiv` followed by inflation along `π` and
`f`** (explicit classes, Tau Ceti's model): for every `1`-cycle `c` of `[W --(Φ−1)--> W]`, the
explicit class of its image cocycle in `C¹_cont(G, M)` is
`explicitMap1 π f (urH1Equiv [c])`. PROVED. -/
theorem urToLocal_H1 (c : (frobCx (frob e X)).cycles 1)
    (hz : (fun g : G => contFun (k := k) (G := G) (M := M)
      (((urToLocal e π X f hf).f 1).hom (((frobCx (frob e X)).iCycles 1).hom c)) (fun _ => g)) ∈
        Z1 G M) :
    H1pi G M ⟨_, hz⟩ =
      explicitMap1 H X.V G M π f.toAddMonoidHom continuous_of_discreteTopology hf
        (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm
          (h1Equiv e X (((frobCx (frob e X)).homologyπ 1).hom c))) := by
  rw [h1Equiv_homologyπ]
  erw [explicitMap1_mk]
  change H1pi G M _ = H1pi G M _
  congr 1
  apply Subtype.ext
  funext g
  erw [cocyclesMap1_apply]
  exact urToLocal_one_apply e π X f hf c g

/-- Inflation-pushforward `explicitMap1 π f` is injective for `π` surjective and `f` bijective. PROVED. -/
theorem explicitMap1_injective (hπ : Function.Surjective π) (hfb : Function.Bijective f) :
    Function.Injective (explicitMap1 H X.V G M π f.toAddMonoidHom continuous_of_discreteTopology hf) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    erw [explicitMap1_mk] at hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    obtain ⟨m', rfl⟩ := hfb.2 m
    refine AddMonoidHom.mem_range.2 ⟨m', funext fun h => ?_⟩
    obtain ⟨g, rfl⟩ := hπ h
    apply hfb.1
    have := congrFun hm g
    rw [d0_apply] at this ⊢
    rw [map_sub, hf]
    exact this

/-- **On `H¹`, `urToLocal` is injective onto the unramified part** (`π` surjective, `f` bijective):
the map `H¹([W --(Φ−1)--> W]) → H¹(G, M)` induced by `urToLocal` (`urToLocal_H1`), i.e.
`y ↦ explicitMap1 π f (urH1Equiv y)`, is injective, and its image is the image of
inflation-pushforward `explicitMap1 π f`: the unramified classes. PROVED. -/
theorem urToLocal_H1_injective_range (hπ : Function.Surjective π) (hfb : Function.Bijective f) :
    Function.Injective (fun y => explicitMap1 H X.V G M π f.toAddMonoidHom
        continuous_of_discreteTopology hf
        (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm (h1Equiv e X y))) ∧
      Set.range (fun y => explicitMap1 H X.V G M π f.toAddMonoidHom
        continuous_of_discreteTopology hf
        (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm (h1Equiv e X y))) =
      Set.range (explicitMap1 H X.V G M π f.toAddMonoidHom continuous_of_discreteTopology hf) := by
  refine ⟨fun a b hab => (h1Equiv e X).injective
    (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm.injective
      (explicitMap1_injective π X f hf hπ hfb hab)), ?_⟩
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(h1Equiv e X).symm (X.explicitH1AddEquivContinuousCohomologyOfDiscrete x), ?_⟩
    simp only [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]

/-- The degree-`0` image under `urToLocal` of `x ∈ W` is the constant `0`-cochain `f x`; for
`x ∈ ker (Φ − 1) = W^H` (`ker_frob_sub_one`) it is invariant, `f x ∈ M^G`. PROVED. -/
theorem urToLocal_zero_apply (x : X.V) (v : Fin 0 → G) :
    contFun (k := k) (G := G) (M := M) (((urToLocal e π X f hf).f 0).hom
      ((HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob e X - 1)) rel01).inv.hom x)) v =
      f x := by
  rw [urToLocal_f₀]
  erw [ModuleCat.hom_comp, LinearMap.comp_apply, Iso.inv_hom_id_apply]
  rfl

include hf in
/-- The degree-`0` image of an invariant is invariant. -/
theorem urToLocal_zero_invariant (x : X.V) (hx : x ∈ LinearMap.ker (frob e X - 1)) (g : G) :
    g • f x = f x := by
  rw [← hf]
  have hinv : x ∈ X.ρ.invariants := ker_frob_sub_one e X ▸ hx
  exact congrArg f (hinv (π g))

end Agree

section Galois

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **(PROVED) The unramified condition `urToLocal_galois` is a quasi-isomorphism onto the
unramified part** (tex 3478–3487, 4699–4701), at a place `w ∈ S` of a number field, for a finite
discrete `Gal(K_w^ur/K_w)`-module `W` identified with the coefficients `M` by a `G_{K_w}`-equivariant
bijection `f`:
* on `H¹`, the induced map `y ↦ inflation∘f (urH1Equiv y)` (`urToLocal_H1`) is injective with image
  the inflated (unramified) classes `explicitMap1 (resUr) f`;
* in every degree `n ≥ 2` both `Hⁿ(U_w^ur)` and `Hⁿ(Gal(K_w^ur/K_w), W)` vanish (`CdOne`).
(On `H⁰`, `urToLocal` sends `W^{Gal(K_w^ur/K_w)} = ker (Φ − 1)` to the invariants by `f`:
`urToLocal_zero_apply`, `urToLocal_zero_invariant`.) -/
def UrToLocalOntoUnramified : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (w : Places K S)
    (k : Type) [CommRing k] [TopologicalSpace k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x),
    Function.Bijective f →
      (Function.Injective (fun y => explicitMap1 (GUr K w.1) X.V (Gloc K w.1)
          (ResMod (locMap K S w.1) M) (resUr K w.1) f.toAddMonoidHom
          continuous_of_discreteTopology hf
          (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm (urH1Equiv K w.1 X y))) ∧
        Set.range (fun y => explicitMap1 (GUr K w.1) X.V (Gloc K w.1)
          (ResMod (locMap K S w.1) M) (resUr K w.1) f.toAddMonoidHom
          continuous_of_discreteTopology hf
          (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm (urH1Equiv K w.1 X y))) =
        Set.range (explicitMap1 (GUr K w.1) X.V (Gloc K w.1) (ResMod (locMap K S w.1) M)
          (resUr K w.1) f.toAddMonoidHom continuous_of_discreteTopology hf)) ∧
      ∀ n : ℕ, 2 ≤ n → IsZero ((urCx K w.1 X).homology (n : ℤ)) ∧
        Subsingleton (continuousCohomology n X)

theorem urToLocalOntoUnramified_proof : UrToLocalOntoUnramified := by
  intro K _ _ S w k _ _ M _ _ _ _ _ _ _ X _ _ _ f hf hfb
  have hsc := instSMulCommClassResMod (k := k) (locMap K S w.1) M
  exact ⟨@urToLocal_H1_injective_range k _ _ (Gloc K w.1) _ _ _ (GUr K w.1) _ _ _ (eUr K w.1)
        (resUr K w.1) X _ _ _ (ResMod (locMap K S w.1) M) _ _ _ hsc _ _ _ f hf
        (resUr_surjective K w.1) hfb,
      fun n hn => ⟨isZero_homology _ (n : ℤ) (by omega) (by omega),
        ur_subsingleton_continuousCohomology_ge_two K w.1 X n hn⟩⟩

end Galois

end ZInQ.Contrib.CloudB3RC53.GenuineInst
