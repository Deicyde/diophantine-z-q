import ZInQKernel.Contrib.OneProof.RC.KummerMaps.UrMilne
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthLocalDuality
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthUnramified
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CycloInfl
import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.InflationRestriction

/-!
# Lane RC29, round 3 (item 2): the unramified conditions from Milne's local duality

Manuscript `diophantine_zq.tex`, the support comparisons (tex 3470–3500, in particular tex
3483–3498: the unramified condition `[Φ−1]` at the new places of `S − S₀`, "Use it only when the
actual coefficient representation is unramified at the removed place") and tex 3815–3816 ("The
remaining good unramified conditions use the integral unramified comparison"). Round 1 of this
lane obtained the per-place quasi-isomorphism for (unramified, unramified) at `w ∈ S − S₀` from
Nekovář's 7.5.6 (`NekovarProp756`, `orthUr_quasiIso_of_print`). This file derives it instead from
Milne's Theorem I.2.6 (`MilneADT_I_2_6`, `UrMilne.lean`) and Nekovář's local duality 5.2.4
(lane RC26's `NekovarProp524`), through round 2's homological reduction
`orthPerPlace_of_localDuality` (`OrthLocalDuality.lean`).

* `urM_descend_eq` (generic, PROVED): a continuous `1`-cocycle of `G` whose values factor through
  `π : G ↠ H ≃ ℤ̂` (with `G` compact) is the inflation of the `ℤ̂`-cocycle `c_u` of its value `u` at
  the Frobenius (lane RC26's `urCocycle`): the descended function is continuous (`π` is closed),
  a cocycle, and determined by its value at the Frobenius (`closure_frob_eq_top`).
* At `w ∈ S − S₀` for lane RC28's `urAt` (the inflation of `[M₀ --(Φ−1)--> M₀]`):
  - `urM_unramified`: the inertia group acts trivially on `M₀` (lane RC26's `urFactor_spec`);
  - `urM_order`: under the standing setting, `|M₀|` is prime to the residue characteristic of `w`;
  - `urM_inflated_eq`, `urM_urLin_inflated`: Milne's inflated classes `H¹(G/I, M₀)` are exactly
    the classes of the degree-one image of `urAt`;
  - `urM_h01` (PROVED): `urAt` satisfies `OrthH01At` (`H⁰(urAt) = H⁰(G_{K_w}, M₀)` and
    `H¹(urAt) ↪ H¹(G_{K_w}, M₀)`).
* **(c) The trace-free cocycle form** for `urAt`:
  - (ISO) `urM_iso`: the cup products of two inflated unramified `1`-cocycles are coboundaries
    (round 1's PROVED cochain form of Nekovář's Lemma 7.5.2, `orthUr_cup_coboundary`; no print);
  - (ANN) **`urM_ann`** (PROVED from `MilneADT_I_2_6`): a `1`-cocycle of `C(G_{K_w}, M₀)` whose cup
    products with all inflated unramified `1`-cocycles of `M₀'` are coboundaries is an inflated
    unramified cocycle up to a coboundary, given `UrMDualForm` (the coefficient pairing in Milne's
    form, below).
* (d) `urM_annihilator` (the analogue for `urAt` of round 2's bridge
  `orthKummerAnnihilator_of_cup`): `OrthKummerAnnihilator` for (unramified, unramified);
  **`urM_quasiIso_of_milne`** (PROVED from `MilneADT_I_2_6`, `NekovarProp524`, the standing
  setting and `UrMDualForm`): the per-place quasi-isomorphism of `orthUr_quasiIso_of_print` for
  every isotropy homotopy, without `NekovarProp756`.

**The hypothesis `UrMDualForm`** (a property of the coefficient data at `w`, not a print). Milne
pairs `M` with `M^D = Hom(M, K^{s×})` (`ℤ`-linear duals); the lane's coefficients pair `M₀` with
`M₀'` through an `R`-bilinear perfect pairing `β₀ : M₀ × M₀' → T₀`, `T₀ ≅ R(1)` (Nekovář's
`D(M)(1)`). `UrMDualForm` asks for an equivariant additive `λ : T₀ → F̄_w^×` such that
`m' ↦ λ ∘ β₀(·, m')` is a bijection `M₀' ≃ M₀^D`. For a finite Frobenius coefficient ring this is
the standard passage from `R`-duals to `ℤ`-duals through a generating character of `R` (for the
actual `A_i = (ℤ/2^i)[t]/t^i`, the top coefficient: compare tex 3465–3467, "a top-coefficient
functional used to test a finite Frobenius ring's perfection"). It is a hypothesis in this file;
`UrMilneActual.lean` derives it from any generating character (`urMDualForm_of_generating`) and
proves it for the actual pair `M_i(α) × M_i(α⁻¹) → A_i(1)` (`urMDualForm_actual`, under lane
RC28's GLUE `FullTorsion`). Non-vacuity: `urMDualForm_of_subsingleton` and `urMDualForm_actual`.

Kinds: definitions and PROVED from the hypotheses named in each statement (PRINTs
`MilneADT_I_2_6` and lane RC26's `NekovarProp524`; the hypothesis predicate `UrMDualForm`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)
open scoped ValuativeRel

attribute [local instance] TopRep.distribMulAction

/-! ### Descent of inflated cocycles -/

section Descent

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {N : Type} [AddCommGroup N] [DistribMulAction G N] [TopologicalSpace N] [DiscreteTopology N]

omit [IsTopologicalGroup G] in
/-- PROVED. **A continuous `1`-cocycle of `G` with values factoring through `π : G ↠ H ≃ ℤ̂` is
the inflation of the cocycle `c_u` (`urCocycle`) of its value `u` at the Frobenius**: if
`c(g) = f₀(a(π g))` for an injective equivariant `f₀ : X → N`, then `a = c_{a(Frob)}`. The function
`a` is continuous because `π` is a closed surjection (`G` compact, `H` Hausdorff), a cocycle because
`f₀` is injective and equivariant, and determined by its value at the Frobenius, whose powers are
dense (`closure_frob_eq_top`). -/
theorem urM_descend_eq (hπ : Function.Surjective π) (f₀ : X.V →+ N)
    (hinj : Function.Injective f₀) (hf₀ : ∀ (g : G) (x : X.V), f₀ (π g • x) = g • f₀ x)
    (c : G → N) (hc : Continuous c) (hcoc : ∀ g h : G, c (g * h) = g • c h + c g)
    (a : H → X.V) (ha : ∀ g, c g = f₀ (a (π g))) :
    a = urCocycle e X (a (frobElt e)) := by
  have hc' : Continuous (fun g => a (π g)) := by
    refine continuous_discrete_rng.2 fun x => ?_
    have he : (fun g => a (π g)) ⁻¹' {x} = c ⁻¹' {f₀ x} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ha g]
      exact hinj.eq_iff.symm
    rw [he]
    exact (isOpen_discrete _).preimage hc
  have hac : Continuous a := by
    rw [continuous_iff_isClosed]
    intro C _
    have he : a ⁻¹' C = π '' ((fun g => a (π g)) ⁻¹' C) := by
      ext γ
      obtain ⟨g, rfl⟩ := hπ γ
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro h
        exact ⟨g, h, rfl⟩
      · rintro ⟨g', h, hg'⟩
        rw [← hg']
        exact h
    rw [he]
    exact ((isClosed_discrete C).preimage hc').isCompact.image (map_continuous π) |>.isClosed
  have hacoc : ∀ γ δ : H, a (γ * δ) = γ • a δ + a γ := by
    intro γ δ
    obtain ⟨g, rfl⟩ := hπ γ
    obtain ⟨h, rfl⟩ := hπ δ
    apply hinj
    rw [← map_mul, ← ha, hcoc, ha, ha, map_add, hf₀]
  have haZ : a ∈ TauCeti.ContCohomology.Z1 H X.V :=
    TauCeti.ContCohomology.mem_Z1_iff.2 ⟨hac, fun γ δ => hacoc γ δ⟩
  refine TauCeti.ContCohomology.eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top haZ
    (urCocycle_mem e X _) (closure_frob_eq_top e) ?_
  intro γ hγ
  rw [Set.mem_singleton_iff] at hγ
  subst hγ
  rw [urCocycle_frob]

end Descent

/-! ### The cocycle identity of a `1`-cocycle -/

section Cocycle

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {k : Type} [CommRing k]
  {N : Type} [AddCommGroup N] [Module k N] [DistribMulAction G N] [SMulCommClass G k N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- PROVED. **A `1`-cocycle satisfies `c(gh) = g • c(h) + c(g)`** (lane RC26's `dFun_one_apply`). -/
theorem urM_cocycle_apply (c : contCochain k G N 1) (hc : contD k G N 1 c = 0) (g h : G) :
    cfun c (fun _ => g * h) = g • cfun c (fun _ => h) + cfun c (fun _ => g) := by
  have e := congrArg (fun c' : contCochain k G N 2 => cfun c' ![g, h]) hc
  simp only at e
  rw [kann_cfun_contD, dFun_one_apply] at e
  have h0 : cfun (0 : contCochain k G N 2) ![g, h] = 0 := rfl
  rw [h0] at e
  change g • cfun c (fun _ => h) - cfun c (fun _ => g * h) + cfun c (fun _ => g) = 0 at e
  rw [← sub_eq_zero, ← neg_eq_zero, ← e]
  abel

omit [IsTopologicalGroup G] [ContinuousSMul G N] in
/-- PROVED. A `1`-cochain is determined by its values at the constant tuples. -/
theorem urM_cfun_const (c : contCochain k G N 1) (g : Fin 1 → G) :
    cfun c g = cfun c (fun _ => g 0) := by
  congr 1
  funext i
  rw [Subsingleton.elim i 0]

end Cocycle

/-! ### At a new place `w ∈ S − S₀` -/

section Place

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

section OneModule

variable {M₀ : Type} [AddCommGroup M₀] [Module R M₀] [DistribMulAction (GKS K S₀) M₀]
  [SMulCommClass (GKS K S₀) R M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
  [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]

/-- PROVED. `M₀` is a discrete `Gal(K_w^ur/K_w)`-module at `w ∈ S − S₀` (lane RC28's
`urRep_continuousSMul`, as an instance at the places of `S − S₀`). -/
theorem urM_continuousSMul (w : Places K S) (hw : w.1 ∉ S₀) :
    ContinuousSMul (GUr K w.1) (urRep R M₀ (newPlace w hw)).V :=
  urRep_continuousSMul R M₀ (newPlace w hw)

attribute [local instance] urM_continuousSMul

omit [TopologicalSpace R] [DiscreteTopology R] [Module R M₀] [SMulCommClass (GKS K S₀) R M₀]
  [Finite M₀] [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] in
/-- PROVED (tex 3483–3487: the coefficients are unramified at the new places). **The inertia
group of `w ∈ S − S₀` acts trivially on `M₀`**: `G_{K_w}` acts on `M₀` through lane RC26's
factorization `urFactor : Gal(K_w^ur/K_w) → G_{K,S₀}` (`urFactor_spec`). -/
theorem urM_unramified (w : Places K S) (hw : w.1 ∉ S₀) (σ : Gloc K w.1)
    (hσ : urMRes (w.1.adicCompletion K) σ = 1) (m : ResMod (locMap K S w.1) (InflMod hS M₀)) :
    σ • m = m := by
  change inflMap K hS (locMap K S w.1 σ) • (show M₀ from m) = (show M₀ from m)
  have h1 : urRes K (newPlace w hw).1 σ = 1 := hσ
  rw [locMap_compat K hS w.1 σ, urFactor_spec K (newPlace w hw) σ, h1, map_one, one_smul]

omit [TopologicalSpace R] [DiscreteTopology R] [SMulCommClass (GKS K S₀) R M₀]
  [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀]
  [DistribMulAction (GKS K S₀) M₀] in
/-- PROVED (Nekovář 5.1, the standing hypotheses: `p` is nilpotent in `R` and the primes above `p`
lie in `S₀`). **`|M₀|` is prime to the residue characteristic of `w ∈ S − S₀`**: `M₀` is a
`p`-group, and `w ∤ p`. -/
theorem urM_order [IsLocalRing R] (p : ℕ) (hset : NekovarFiniteSetting K S₀ p R)
    (w : Places K S) (hw : w.1 ∉ S₀) :
    ¬ ringChar 𝓀[w.1.adicCompletion K] ∣ Nat.card (ResMod (locMap K S w.1) (InflMod hS M₀)) := by
  intro h
  have : Fact p.Prime := ⟨hset.prime⟩
  obtain ⟨n, hn⟩ := hset.nilpotent_p
  have hpg : IsPGroup p (Multiplicative M₀) := by
    intro g
    refine ⟨n, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow, hn, zero_smul]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p) (G := Multiplicative M₀)).1 hpg
  have hcard : Nat.card (ResMod (locMap K S w.1) (InflMod hS M₀)) = p ^ a := ha
  rw [hcard] at h
  have hmem := (w.1.ringChar_residueField_adicCompletion_dvd_iff (K := K)).1 h
  rw [Nat.cast_pow] at hmem
  exact hw (hset.above_p w.1 (w.1.isPrime.mem_of_pow_mem a hmem))

variable (R M₀) in
/-- Definition. **The degree-one map of the unramified condition `urAt` at `w ∈ S − S₀`**:
`u ↦ (g ↦ c_u(g|K_w^ur))`, lane RC26's `urLin₁` for `urRep` and `urId`. -/
abbrev urMLin (w : Places K S) (hw : w.1 ∉ S₀) :
    (urRep R M₀ (newPlace w hw)).V →ₗ[R]
      contCochain R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 1 :=
  urLin₁ (eUr K w.1) (resUr K w.1) (urRep R M₀ (newPlace w hw))
    (M := ResMod (locMap K S w.1) (InflMod hS M₀)) (urId hS R M₀ (newPlace w hw))

/-- PROVED. The values of `urMLin u`: `g ↦ c_u(g|K_w^ur)`. -/
theorem urMLin_cfun (w : Places K S) (hw : w.1 ∉ S₀) (u : (urRep R M₀ (newPlace w hw)).V)
    (g : Fin 1 → Gloc K w.1) :
    cfun (urMLin hS R M₀ w hw u) g =
      urId hS R M₀ (newPlace w hw)
        (urCocycle (eUr K w.1) (urRep R M₀ (newPlace w hw)) u (resUr K w.1 (g 0))) :=
  rfl

/-- PROVED. **Milne's inflated classes are the classes of the unramified condition**: a
`1`-cocycle of `C(G_{K_w}, M₀)` (with `ℤ` coefficients) inflated from `G_w/I_w` is
`urMLin u` for `u` its value at a lift of the Frobenius (`urM_descend_eq`). -/
theorem urM_inflated_eq (w : Places K S) (hw : w.1 ∉ S₀)
    (c : contCochain ℤ (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 1)
    (hc : contD ℤ (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 1 c = 0)
    (hinf : UrMInflated (F := w.1.adicCompletion K) c) :
    ∃ u : (urRep R M₀ (newPlace w hw)).V, ∀ g : Fin 1 → Gloc K w.1,
      cfun c g = cfun (urMLin hS R M₀ w hw u) g := by
  have := compactSpace_absGal K w.1
  have : T2Space (GUr K w.1) := krullTopology_t2
  obtain ⟨a, ha⟩ := hinf
  have hdesc := urM_descend_eq (eUr K w.1) (resUr K w.1) (urRep R M₀ (newPlace w hw))
    (N := ResMod (locMap K S w.1) (InflMod hS M₀)) (resUr_surjective K w.1)
    (urId hS R M₀ (newPlace w hw)).toAddMonoidHom (fun _ _ h => h) (urId_compat hS R M₀ w hw)
    (fun g => cfun c (fun _ => g))
    ((mem_contCochain.1 c.2).comp (continuous_pi fun _ => continuous_id))
    (fun g h => urM_cocycle_apply c hc g h) a (fun g => ha (fun _ => g))
  refine ⟨a (frobElt (eUr K w.1)), fun g => ?_⟩
  rw [urM_cfun_const c g]
  exact (ha (fun _ => g 0)).trans (congrFun hdesc (resUr K w.1 (g 0)))

/-- PROVED. Conversely, the degree-one image of the unramified condition consists of inflated
cocycles. -/
theorem urM_urLin_inflated (w : Places K S) (hw : w.1 ∉ S₀) (u : (urRep R M₀ (newPlace w hw)).V) :
    UrMInflated (F := w.1.adicCompletion K)
      (kannPost (k' := ℤ) (AddMonoidHom.id _) (urMLin hS R M₀ w hw u)) :=
  ⟨fun γ => urCocycle (eUr K w.1) (urRep R M₀ (newPlace w hw)) u γ, fun _ => rfl⟩

variable (R M₀) in
/-- Definition. The structural isomorphism `U⁰ ≅ M₀` of the double complex `urAt` at `w`. -/
def urMIso₀ (w : Places K S) (hw : w.1 ∉ S₀) :
    (urAt hS R M₀ w hw).U.X 0 ≅ ModuleCat.of R (urRep R M₀ (newPlace w hw)).V :=
  HomologicalComplex.doubleXIso₀
    (ModuleCat.ofHom (frob (eUr K w.1) (urRep R M₀ (newPlace w hw)) - 1)) rel01

variable (R M₀) in
/-- Definition. The structural isomorphism `U¹ ≅ M₀` of the double complex `urAt` at `w`. -/
def urMIso₁ (w : Places K S) (hw : w.1 ∉ S₀) :
    (urAt hS R M₀ w hw).U.X 1 ≅ ModuleCat.of R (urRep R M₀ (newPlace w hw)).V :=
  HomologicalComplex.doubleXIso₁
    (ModuleCat.ofHom (frob (eUr K w.1) (urRep R M₀ (newPlace w hw)) - 1)) rel01 (by decide)

/-- PROVED. `U⁰ ≅ M₀ ≅ U⁰` is the identity on `M₀`. -/
theorem urMIso₀_hom_inv (w : Places K S) (hw : w.1 ∉ S₀) (m : (urRep R M₀ (newPlace w hw)).V) :
    (urMIso₀ hS R M₀ w hw).hom.hom ((urMIso₀ hS R M₀ w hw).inv.hom m) = m :=
  congrArg (fun f => ModuleCat.Hom.hom f m) (urMIso₀ hS R M₀ w hw).inv_hom_id

/-- PROVED. `U¹ ≅ M₀ ≅ U¹` is the identity on `U¹`. -/
theorem urMIso₁_inv_hom (w : Places K S) (hw : w.1 ∉ S₀) (u : (urAt hS R M₀ w hw).U.X 1) :
    (urMIso₁ hS R M₀ w hw).inv.hom ((urMIso₁ hS R M₀ w hw).hom.hom u) = u :=
  congrArg (fun f => ModuleCat.Hom.hom f u) (urMIso₁ hS R M₀ w hw).hom_inv_id

/-- PROVED. `M₀ ≅ U¹ ≅ M₀` is the identity on `M₀`. -/
theorem urMIso₁_hom_inv (w : Places K S) (hw : w.1 ∉ S₀) (m : (urRep R M₀ (newPlace w hw)).V) :
    (urMIso₁ hS R M₀ w hw).hom.hom ((urMIso₁ hS R M₀ w hw).inv.hom m) = m :=
  congrArg (fun f => ModuleCat.Hom.hom f m) (urMIso₁ hS R M₀ w hw).inv_hom_id

/-- PROVED. **The degree-one component of `urAt`** is `urMLin` after the structural isomorphism
`U¹ ≅ M₀` of the double complex (lane RC26's `urToLocal_f₁`). -/
theorem urM_i_one (w : Places K S) (hw : w.1 ∉ S₀) (u : (urAt hS R M₀ w hw).U.X 1) :
    (urAt hS R M₀ w hw).i.f 1 1 rfl u = urMLin hS R M₀ w hw ((urMIso₁ hS R M₀ w hw).hom.hom u) := by
  have h1 : (urToLocal_galois K S w (urRep R M₀ (newPlace w hw)) (urId hS R M₀ (newPlace w hw))
      (urId_compat hS R M₀ w hw)).f 1 = _ :=
    @urToLocal_f₁ R _ _ (Gloc K w.1) _ _ _ (GUr K w.1) _ _ _ (eUr K w.1) (resUr K w.1)
      (urRep R M₀ (newPlace w hw)) _ _ _ (ResMod (locMap K S w.1) (InflMod hS M₀)) inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (urId hS R M₀ (newPlace w hw)) (urId_compat hS R M₀ w hw)
  change ((urToLocal_galois K S w (urRep R M₀ (newPlace w hw)) (urId hS R M₀ (newPlace w hw))
    (urId_compat hS R M₀ w hw)).f 1).hom u = _
  rw [h1]
  rfl

/-- PROVED. **The degree-zero component of `urAt`** is `u ↦` the constant cochain `u`, after the
structural isomorphism `U⁰ ≅ M₀` (lane RC26's `urToLocal_f₀`). -/
theorem urM_i_zero (w : Places K S) (hw : w.1 ∉ S₀) (u : (urAt hS R M₀ w hw).U.X 0) :
    (urAt hS R M₀ w hw).i.f 0 0 rfl u = constCochain (k := R) (G := Gloc K w.1)
      (M := ResMod (locMap K S w.1) (InflMod hS M₀)) ((urMIso₀ hS R M₀ w hw).hom.hom u) := by
  have h0 : (urToLocal_galois K S w (urRep R M₀ (newPlace w hw)) (urId hS R M₀ (newPlace w hw))
      (urId_compat hS R M₀ w hw)).f 0 = _ :=
    @urToLocal_f₀ R _ _ (Gloc K w.1) _ _ _ (GUr K w.1) _ _ _ (eUr K w.1) (resUr K w.1)
      (urRep R M₀ (newPlace w hw)) _ _ _ (ResMod (locMap K S w.1) (InflMod hS M₀)) inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (urId hS R M₀ (newPlace w hw)) (urId_compat hS R M₀ w hw)
  change ((urToLocal_galois K S w (urRep R M₀ (newPlace w hw)) (urId hS R M₀ (newPlace w hw))
    (urId_compat hS R M₀ w hw)).f 0).hom u = _
  rw [h0]
  rfl

/-- PROVED. **The differential of `urAt`** is `Φ − 1` after the structural isomorphisms
(lane RC26's `frobCx_d01`). -/
theorem urM_d01 (w : Places K S) (hw : w.1 ∉ S₀) (u : (urAt hS R M₀ w hw).U.X 0) :
    (urAt hS R M₀ w hw).U.d 0 1 rfl u =
      (urMIso₁ hS R M₀ w hw).inv.hom
        (frob (eUr K w.1) (urRep R M₀ (newPlace w hw)) ((urMIso₀ hS R M₀ w hw).hom.hom u) -
          (urMIso₀ hS R M₀ w hw).hom.hom u) := by
  change ((urCx K w.1 (urRep R M₀ (newPlace w hw))).d 0 1).hom u = _
  rw [show (urCx K w.1 (urRep R M₀ (newPlace w hw))).d 0 1 = _ from frobCx_d01 _]
  rfl

/-- PROVED. **The Frobenius of `Gal(K_w^ur/K_w)` acts on `M₀` as any lift `g₀ ∈ G_{K_w}`**. -/
theorem urM_frob_eq (w : Places K S) (hw : w.1 ∉ S₀) (g₀ : Gloc K w.1)
    (hg₀ : resUr K w.1 g₀ = frobElt (eUr K w.1)) (m : (urRep R M₀ (newPlace w hw)).V) :
    frob (eUr K w.1) (urRep R M₀ (newPlace w hw)) m =
      g₀ • @id (ResMod (locMap K S w.1) (InflMod hS M₀)) m := by
  rw [frob_apply, ← hg₀]
  exact urId_compat hS R M₀ w hw g₀ m

/-- PROVED. **`urAt` computes `H⁰` and injects on `H¹`** (`OrthH01At`): `ker(Φ − 1) = M₀^{G_{K_w}}`
(the Frobenius acts as a lift `g₀`, and `G_{K_w}` acts through `Gal(K_w^ur/K_w)`), and a
degree-one element whose image `urMLin u` is a coboundary `g ↦ g m − m` has `u = Φ m − m`
(evaluate at the lift `g₀`, `urCocycle_frob`). -/
theorem urM_h01 (w : Places K S) (hw : w.1 ∉ S₀) : OrthH01At (urAt hS R M₀ w hw) := by
  obtain ⟨g₀, hg₀⟩ := resUr_surjective K w.1 (frobElt (eUr K w.1))
  refine ⟨fun u _ hu => ?_, fun z hz => ?_, fun u x hx => ?_⟩
  · exact urAt_isInjective hS R M₀ w hw 0 (hu.trans (map_zero _).symm)
  · obtain ⟨m, rfl⟩ : ∃ m : (urRep R M₀ (newPlace w hw)).V,
        constCochain (k := R) (G := Gloc K w.1) (M := ResMod (locMap K S w.1) (InflMod hS M₀)) m =
          z :=
      ⟨_, (eq_constCochain z).symm⟩
    have hm : ∀ g : Gloc K w.1, g • @id (ResMod (locMap K S w.1) (InflMod hS M₀)) m =
        @id (ResMod (locMap K S w.1) (InflMod hS M₀)) m :=
      (contD_zero_eq_zero_iff _).1 hz
    have e2 : frob (eUr K w.1) (urRep R M₀ (newPlace w hw)) m - m = 0 :=
      sub_eq_zero.2 ((urM_frob_eq hS w hw g₀ hg₀ m).trans (hm g₀))
    refine ⟨(urMIso₀ hS R M₀ w hw).inv.hom m, ?_, ?_⟩
    · refine (urM_d01 hS w hw _).trans ?_
      rw [urMIso₀_hom_inv, e2]
      exact map_zero _
    · refine (urM_i_zero hS w hw _).trans ?_
      exact congrArg _ (urMIso₀_hom_inv hS w hw m)
  · obtain ⟨m, rfl⟩ : ∃ m : (urRep R M₀ (newPlace w hw)).V,
        constCochain (k := R) (G := Gloc K w.1) (M := ResMod (locMap K S w.1) (InflMod hS M₀)) m =
          x :=
      ⟨_, (eq_constCochain x).symm⟩
    have hx' : contD R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 0
        (constCochain (k := R) (G := Gloc K w.1) (M := ResMod (locMap K S w.1) (InflMod hS M₀))
          m) = urMLin hS R M₀ w hw ((urMIso₁ hS R M₀ w hw).hom.hom u) :=
      hx.trans (urM_i_one hS w hw u)
    have e := congrArg
      (fun c : contCochain R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 1 =>
        cfun c (fun _ : Fin 1 => g₀)) hx'
    have h1 : g₀ • @id (ResMod (locMap K S w.1) (InflMod hS M₀)) m -
        @id (ResMod (locMap K S w.1) (InflMod hS M₀)) m =
        cfun (urMLin hS R M₀ w hw ((urMIso₁ hS R M₀ w hw).hom.hom u)) (fun _ : Fin 1 => g₀) :=
      (cfun_contD_constCochain _ (fun _ : Fin 1 => g₀)).symm.trans e
    have h2 : cfun (urMLin hS R M₀ w hw ((urMIso₁ hS R M₀ w hw).hom.hom u))
        (fun _ : Fin 1 => g₀) = (urMIso₁ hS R M₀ w hw).hom.hom u := by
      change urCocycle (eUr K w.1) (urRep R M₀ (newPlace w hw)) ((urMIso₁ hS R M₀ w hw).hom.hom u)
        (resUr K w.1 g₀) = (urMIso₁ hS R M₀ w hw).hom.hom u
      rw [hg₀, urCocycle_frob]
    have h' : frob (eUr K w.1) (urRep R M₀ (newPlace w hw)) m - m =
        (urMIso₁ hS R M₀ w hw).hom.hom u :=
      (congrArg (fun t => t - m) (urM_frob_eq hS w hw g₀ hg₀ m)).trans (h1.trans h2)
    refine ⟨(urMIso₀ hS R M₀ w hw).inv.hom m, ?_⟩
    refine (urM_d01 hS w hw _).trans ?_
    rw [urMIso₀_hom_inv, h']
    exact urMIso₁_inv_hom hS w hw u

end OneModule

section Pair

variable {M₀ M₀' T₀ : Type}
  [AddCommGroup M₀] [Module R M₀] [DistribMulAction (GKS K S₀) M₀] [SMulCommClass (GKS K S₀) R M₀]
  [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  [AddCommGroup M₀'] [Module R M₀'] [DistribMulAction (GKS K S₀) M₀']
  [SMulCommClass (GKS K S₀) R M₀'] [TopologicalSpace M₀'] [DiscreteTopology M₀']
  [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀']
  [AddCommGroup T₀] [Module R T₀] [DistribMulAction (GKS K S₀) T₀] [SMulCommClass (GKS K S₀) R T₀]
  [TopologicalSpace T₀] [DiscreteTopology T₀] [ContinuousSMul (GKS K S₀) T₀]
  (β₀ : M₀ →ₗ[R] M₀' →ₗ[R] T₀)
  (hβ₀ : ∀ (g : GKS K S₀) (a : M₀) (b : M₀'), β₀ (g • a) (g • b) = g • β₀ a b)

attribute [local instance] urM_continuousSMul

/-- Definition (hypothesis predicate for the support comparisons, tex 3483–3498; compare tex
3465–3467, "a top-coefficient functional used to test a finite Frobenius ring's perfection").
**The coefficient pairing in Milne's form at `w`**: an additive map `λ : T₀ → F̄_w^×`, equivariant
for `G_{K_w}` (acting on `T₀` through `G_{K,S₀}`), such that `m' ↦ λ ∘ β₀(·, m')` is a bijection
`M₀' ≃ Hom(M₀, F̄_w^×)` (Milne's `M₀^D`). It converts the `R`-linear perfect pairing `β₀` into
Milne's `ℤ`-linear duality; `λ` is used only to test the annihilators, never as the arithmetic
trace (the per-place maps keep the coefficient-valued trace `tr_w`, as tex 3465–3467 requires). -/
def UrMDualForm (w : Places K S) : Prop :=
  ∃ lam : T₀ →+ UrMUnits (w.1.adicCompletion K),
    (∀ (g : Gloc K w.1) (t : T₀), lam (inflMap K hS (locMap K S w.1 g) • t) = g • lam t) ∧
    Function.Bijective fun m' : M₀' => lam.comp (β₀.flip m').toAddMonoidHom

omit [SMulCommClass (GKS K S₀) R M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
  [ContinuousSMul (GKS K S₀) M₀] [Finite M₀] [SMulCommClass (GKS K S₀) R M₀']
  [TopologicalSpace M₀'] [DiscreteTopology M₀'] [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀']
  [SMulCommClass (GKS K S₀) R T₀] [TopologicalSpace T₀] [DiscreteTopology T₀]
  [ContinuousSMul (GKS K S₀) T₀] [TopologicalSpace R] [DiscreteTopology R]
  [DistribMulAction (GKS K S₀) M₀] [DistribMulAction (GKS K S₀) M₀'] in
/-- PROVED. **Non-vacuity of `UrMDualForm`**: zero coefficient modules, with `λ = 0`. -/
theorem urMDualForm_of_subsingleton [Subsingleton M₀] [Subsingleton M₀'] (w : Places K S) :
    UrMDualForm hS β₀ w := by
  refine ⟨0, fun g t => (smul_zero g).symm, fun a b _ => Subsingleton.elim a b, fun φ => ⟨0, ?_⟩⟩
  ext m
  rw [Subsingleton.elim m 0, map_zero, map_zero]

/-- Definition. **The `ℤ`-bilinear pairing `λ ∘ β₀`** on the local modules at `w`, with values in
`F̄_w^×`. -/
def urMPairZ (w : Places K S) (lam : T₀ →+ UrMUnits (w.1.adicCompletion K)) :
    ResMod (locMap K S w.1) (InflMod hS M₀) →ₗ[ℤ] ResMod (locMap K S w.1) (InflMod hS M₀') →ₗ[ℤ]
      UrMUnits (w.1.adicCompletion K) :=
  LinearMap.mk₂ ℤ (fun m m' => lam (β₀ (show M₀ from m) (show M₀' from m')))
    (fun m₁ m₂ m' => map_add (lam.comp (β₀.flip (show M₀' from m')).toAddMonoidHom)
      (show M₀ from m₁) (show M₀ from m₂))
    (fun c m m' => map_zsmul (lam.comp (β₀.flip (show M₀' from m')).toAddMonoidHom) c
      (show M₀ from m))
    (fun m m₁ m₂ => map_add (lam.comp (β₀ (show M₀ from m)).toAddMonoidHom)
      (show M₀' from m₁) (show M₀' from m₂))
    (fun c m m' => map_zsmul (lam.comp (β₀ (show M₀ from m)).toAddMonoidHom) c
      (show M₀' from m'))

omit [TopologicalSpace R] [DiscreteTopology R] [SMulCommClass (GKS K S₀) R M₀]
  [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  [SMulCommClass (GKS K S₀) R M₀'] [TopologicalSpace M₀'] [DiscreteTopology M₀']
  [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀'] [SMulCommClass (GKS K S₀) R T₀]
  [TopologicalSpace T₀] [DiscreteTopology T₀] [ContinuousSMul (GKS K S₀) T₀]
  [DistribMulAction (GKS K S₀) M₀] [DistribMulAction (GKS K S₀) M₀']
  [DistribMulAction (GKS K S₀) T₀] in
/-- PROVED. The pairing `λ ∘ β₀` evaluates. -/
theorem urMPairZ_apply (w : Places K S) (lam : T₀ →+ UrMUnits (w.1.adicCompletion K))
    (m : ResMod (locMap K S w.1) (InflMod hS M₀)) (m' : ResMod (locMap K S w.1) (InflMod hS M₀')) :
    urMPairZ hS β₀ w lam m m' = lam (β₀ (show M₀ from m) (show M₀' from m')) :=
  rfl

omit [TopologicalSpace R] [DiscreteTopology R] [SMulCommClass (GKS K S₀) R M₀]
  [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  [SMulCommClass (GKS K S₀) R M₀'] [TopologicalSpace M₀'] [DiscreteTopology M₀']
  [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀'] [SMulCommClass (GKS K S₀) R T₀]
  [TopologicalSpace T₀] [DiscreteTopology T₀] [ContinuousSMul (GKS K S₀) T₀] in
include hβ₀ in
/-- PROVED. **`λ ∘ β₀` is `G_{K_w}`-equivariant** for an equivariant `λ`. -/
theorem urMPairZ_smul (w : Places K S) (lam : T₀ →+ UrMUnits (w.1.adicCompletion K))
    (hlam : ∀ (g : Gloc K w.1) (t : T₀), lam (inflMap K hS (locMap K S w.1 g) • t) = g • lam t)
    (σ : Gloc K w.1) (a : ResMod (locMap K S w.1) (InflMod hS M₀))
    (b : ResMod (locMap K S w.1) (InflMod hS M₀')) :
    urMPairZ hS β₀ w lam (σ • a) (σ • b) = σ • urMPairZ hS β₀ w lam a b := by
  rw [urMPairZ_apply, urMPairZ_apply, ← hlam]
  exact congrArg lam (hβ₀ (inflMap K hS (locMap K S w.1 σ)) a b)

omit [TopologicalSpace R] [DiscreteTopology R] [SMulCommClass (GKS K S₀) R M₀]
  [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  [SMulCommClass (GKS K S₀) R M₀'] [TopologicalSpace M₀'] [DiscreteTopology M₀']
  [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀'] [SMulCommClass (GKS K S₀) R T₀]
  [TopologicalSpace T₀] [DiscreteTopology T₀] [ContinuousSMul (GKS K S₀) T₀]
  [DistribMulAction (GKS K S₀) M₀] [DistribMulAction (GKS K S₀) M₀']
  [DistribMulAction (GKS K S₀) T₀] in
/-- PROVED. `m' ↦ (λ ∘ β₀)(·, m')` is the map of `UrMDualForm`. -/
theorem urMPhi_urMPairZ_bijective (w : Places K S) (lam : T₀ →+ UrMUnits (w.1.adicCompletion K))
    (hbij : Function.Bijective fun m' : M₀' => lam.comp (β₀.flip m').toAddMonoidHom) :
    Function.Bijective (urMPhi (urMPairZ hS β₀ w lam)) := by
  have he : (urMPhi (urMPairZ hS β₀ w lam) : ResMod (locMap K S w.1) (InflMod hS M₀') →
      UrMDual (w.1.adicCompletion K) (ResMod (locMap K S w.1) (InflMod hS M₀))) =
      fun m' : M₀' => lam.comp (β₀.flip m').toAddMonoidHom :=
    funext fun _ => AddMonoidHom.ext fun _ => rfl
  rw [he]
  exact hbij

include hβ₀ in
/-- PROVED. **(ISO) The cup products of two inflated unramified `1`-cocycles are coboundaries**
(Nekovář's Lemma 7.5.2 at cochain level, round 1's `orthUr_cup_coboundary`; no print). -/
theorem urM_iso (w : Places K S) (hw : w.1 ∉ S₀) (u : (urRep R M₀ (newPlace w hw)).V)
    (u' : (urRep R M₀' (newPlace w hw)).V) :
    kannCup (resPairing R (GKS K S) (orthInflPair hS R β₀) (locMap K S w.1))
        (urMLin hS R M₀ w hw u) (urMLin hS R M₀' w hw u') ∈
      LinearMap.range (contD R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS T₀)) 1) :=
  ⟨_, @orthUr_cup_coboundary R _ _ (Gloc K w.1) _ _ _ (GUr K w.1) _ _ _ (eUr K w.1) (resUr K w.1)
    (urRep R M₀ (newPlace w hw)) (urRep R M₀' (newPlace w hw)) _ _ _ _ _ _
    (ResMod (locMap K S w.1) (InflMod hS M₀)) (ResMod (locMap K S w.1) (InflMod hS M₀'))
    (ResMod (locMap K S w.1) (InflMod hS T₀))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (urId hS R M₀ (newPlace w hw)) (urId hS R M₀' (newPlace w hw))
    (resPairing R (GKS K S) (orthInflPair hS R β₀) (locMap K S w.1))
    (urId_compat hS R M₀ w hw) (urId_compat hS R M₀' w hw)
    (fun g a b => orthInflPair_smul hS R β₀ hβ₀ (locMap K S w.1 g) a b) u u'⟩

include hβ₀ in
/-- PROVED from the PRINT `MilneADT_I_2_6` (Milne ADT I.2.6). **(ANN) The unramified condition is
its own exact annihilator, trace-free cocycle form**: at `w ∈ S − S₀`, a `1`-cocycle `x` of
`C(G_{K_w}, M₀)` whose cup products with all inflated unramified `1`-cocycles `urMLin u'` of `M₀'`
are coboundaries is an inflated unramified cocycle `urMLin u` up to a coboundary. Hypotheses: the
PRINT `MilneADT_I_2_6` (tex 3483–3498, 3815–3816); the standing setting for `S₀` (`hset`, lane
RC26's `NekovarFiniteSetting`, Nekovář 5.1, cited at tex 3455–3456: `p` nilpotent in `R` and the
primes above `p` in `S₀`, so `|M₀|` is prime to the residue characteristic, `urM_order`); and
`UrMDualForm` (the coefficient pairing in Milne's form, tex 3465–3467). Route: Milne's (ii) for the
`ℤ`-pairing `λ ∘ β₀` (`urM_exactAnn_of_pairing`), whose inflated classes are the classes of
`urMLin` (`urM_inflated_eq`). -/
theorem urM_ann [IsLocalRing R] (hM : MilneADT_I_2_6) (p : ℕ)
    (hset : NekovarFiniteSetting K S₀ p R) (w : Places K S) (hw : w.1 ∉ S₀)
    (hdual : UrMDualForm hS β₀ w)
    (x : contCochain R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 1)
    (hx : contD R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 1 x = 0)
    (horth : ∀ u' : (urRep R M₀' (newPlace w hw)).V,
      kannCup (resPairing R (GKS K S) (orthInflPair hS R β₀) (locMap K S w.1)) x
          (urMLin hS R M₀' w hw u') ∈
        LinearMap.range (contD R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS T₀)) 1)) :
    ∃ u : (urRep R M₀ (newPlace w hw)).V,
      x - urMLin hS R M₀ w hw u ∈
        contB1 R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) := by
  obtain ⟨lam, hlam, hbij⟩ := hdual
  have : Finite (ResMod (locMap K S w.1) (InflMod hS M₀)) := inferInstanceAs (Finite M₀)
  obtain ⟨-, h2, -⟩ := urM_exactAnn_of_pairing (F := w.1.adicCompletion K)
    (urMPairZ hS β₀ w lam) (urMPairZ_smul hS β₀ hβ₀ w lam hlam) hM (urM_unramified hS w hw)
    (urM_order hS p hset w hw) (urMPhi_urMPairZ_bijective hS β₀ w lam hbij)
  let lamL : ResMod (locMap K S w.1) (InflMod hS T₀) →+ UrMUnits (w.1.adicCompletion K) := lam
  have hlamL : ∀ (g : Gloc K w.1) (t : ResMod (locMap K S w.1) (InflMod hS T₀)),
      lamL (g • t) = g • lamL t := hlam
  let idM : ResMod (locMap K S w.1) (InflMod hS M₀) →+ ResMod (locMap K S w.1) (InflMod hS M₀) :=
    AddMonoidHom.id _
  have hxZ : contD ℤ (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 1
      (kannPost (k' := ℤ) idM x) = 0 :=
    kannPost_cocycle idM (fun _ _ => rfl) hx
  obtain ⟨x₀, hix₀, hdiff⟩ := h2 (kannPost (k' := ℤ) idM x) hxZ fun y hy hiy => by
    obtain ⟨u', hu'⟩ := urM_inflated_eq (R := R) hS w hw y hy hiy
    have he : kannCup (urMPairZ hS β₀ w lam) (kannPost (k' := ℤ) idM x) y =
        kannPost (k' := ℤ) lamL
          (kannCup (resPairing R (GKS K S) (orthInflPair hS R β₀) (locMap K S w.1)) x
            (urMLin hS R M₀' w hw u')) := by
      apply Subtype.ext
      funext g
      change cupFun (urMPairZ hS β₀ w lam) 1 1 2 rfl (cfun (kannPost (k' := ℤ) idM x)) (cfun y) g =
        lamL (cupFun (resPairing R (GKS K S) (orthInflPair hS R β₀) (locMap K S w.1)) 1 1 2 rfl
          (cfun x) (cfun (urMLin hS R M₀' w hw u')) g)
      rw [cupFun_one_one_apply, cupFun_one_one_apply, hu' (fun _ => g 1)]
      rfl
    rw [he]
    exact kannPost_mem_range_two lamL hlamL (horth u')
  have hx₀ : contD ℤ (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 1 x₀ = 0 := by
    obtain ⟨z, hz⟩ := (mem_contB1_iff _).1 hdiff
    have h1 : x₀ = kannPost (k' := ℤ) idM x -
        contD ℤ (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 0 z := by
      rw [hz, sub_sub_cancel]
    rw [h1, map_sub, hxZ, contD_contD, sub_zero]
  obtain ⟨u, hu⟩ := urM_inflated_eq (R := R) hS w hw x₀ hx₀ hix₀
  obtain ⟨z, hz⟩ := (mem_contB1_iff _).1 hdiff
  refine ⟨u, (mem_contB1_iff _).2 ⟨kannPost (k' := R) idM z, ?_⟩⟩
  rw [← kannPost_contD_zero idM (fun _ _ => rfl), hz]
  apply Subtype.ext
  funext g
  change cfun (kannPost (k' := ℤ) idM x) g - cfun x₀ g = cfun x g - cfun (urMLin hS R M₀ w hw u) g
  rw [hu g]
  rfl

include hβ₀ in
/-- PROVED from `MilneADT_I_2_6`. **The annihilator condition for (unramified, unramified)** at
`w ∈ S − S₀` (the analogue for `urAt` of round 2's bridge `orthKummerAnnihilator_of_cup`): (ISO)
from `urM_iso` and a trace killing coboundaries; (ANN) from `urM_ann`, the cup products of a
cocycle with the degree-one image of `urAt` being cocycles of trace zero, hence coboundaries
(`InducesIsoH2`). Hypotheses as for `urM_ann`, and a trace `tr_w` on `C²_cont(G_{K_w}, T₀)`
killing coboundaries and inducing `H² ≅ R` (the coefficient-valued local trace of (4.3), tex
3465). -/
theorem urM_annihilator [IsLocalRing R] (hM : MilneADT_I_2_6) (p : ℕ)
    (hset : NekovarFiniteSetting K S₀ p R) (w : Places K S) (hw : w.1 ∉ S₀)
    (hdual : UrMDualForm hS β₀ w)
    (trv : (locAt K S R (InflMod hS T₀) w).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((locAt K S R (InflMod hS T₀) w).d 1 2 rfl z) = 0)
    (h2 : InducesIsoH2 trv) :
    OrthKummerAnnihilator (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (urAt hS R M₀ w hw) (urAt hS R M₀' w hw) trv := by
  refine ⟨fun u y => ?_, fun x hx horth => ?_⟩
  · obtain ⟨z, hz⟩ := orthUr_cup_mem_range hS R β₀ hβ₀ w hw u y
    have h := htrv z
    rw [hz] at h
    exact h
  · have hcup : ∀ u' : (urRep R M₀' (newPlace w hw)).V,
        kannCup (resPairing R (GKS K S) (orthInflPair hS R β₀) (locMap K S w.1)) x
            (urMLin hS R M₀' w hw u') ∈
          LinearMap.range (contD R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS T₀)) 1) := by
      intro u'
      have hy : (urAt hS R M₀' w hw).i.f 1 1 rfl ((urMIso₁ hS R M₀' w hw).inv.hom u') =
          urMLin hS R M₀' w hw u' := by
        rw [urM_i_one, urMIso₁_hom_inv]
      have hsub : Subsingleton ((urAt hS R M₀' w hw).U.X 2) :=
        orth_urAt_vanishes hS R M₀' w hw 2 (by norm_num) (by norm_num)
      have hdy : (locAt K S R (InflMod hS M₀') w).d 1 2 rfl (urMLin hS R M₀' w hw u') = 0 := by
        have e := (urAt hS R M₀' w hw).i.comm 1 2 1 2 rfl rfl rfl rfl
          ((urMIso₁ hS R M₀' w hw).inv.hom u')
        rw [Subsingleton.elim ((urAt hS R M₀' w hw).U.d 1 2 rfl
          ((urMIso₁ hS R M₀' w hw).inv.hom u')) 0, map_zero, hy] at e
        exact e.symm
      have hcoc : (locAt K S R (InflMod hS T₀) w).d 2 3 rfl
          ((orthGaloisPair K (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀) w).P 1 1 2 rfl
            x (urMLin hS R M₀' w hw u')) = 0 := by
        rw [(orthGaloisPair K (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀) w).leib
          1 2 1 2 2 3 rfl rfl rfl rfl x (urMLin hS R M₀' w hw u')]
        change (orthGaloisPair K (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀) w).P
            2 1 3 _ ((locAt K S R (InflMod hS M₀) w).d 1 2 rfl x) (urMLin hS R M₀' w hw u') +
          sgn 1 • (orthGaloisPair K (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀) w).P
            1 2 3 _ x ((locAt K S R (InflMod hS M₀') w).d 1 2 rfl (urMLin hS R M₀' w hw u')) = 0
        rw [hx, hdy, map_zero, map_zero, smul_zero, add_zero]
        rfl
      have htr := horth ((urMIso₁ hS R M₀' w hw).inv.hom u')
      rw [hy] at htr
      obtain ⟨z, hz⟩ := h2.1 _ hcoc htr
      exact ⟨z, hz⟩
    obtain ⟨u, hu⟩ := urM_ann hS β₀ hβ₀ hM p hset w hw hdual x hx hcup
    obtain ⟨z, hz⟩ := (mem_contB1_iff _).1 hu
    refine ⟨(urMIso₁ hS R M₀ w hw).inv.hom u, z, ?_⟩
    rw [urM_i_one, urMIso₁_hom_inv]
    change x = urMLin hS R M₀ w hw u +
      contD R (Gloc K w.1) (ResMod (locMap K S w.1) (InflMod hS M₀)) 0 z
    rw [hz]
    exact (add_sub_cancel _ _).symm

include hβ₀ in
/-- PROVED from the PRINTs `MilneADT_I_2_6` (Milne ADT I.2.6) and lane RC26's `NekovarProp524`
(Nekovář 5.2.4). **The per-place quasi-isomorphism for (unramified, unramified) at `w ∈ S − S₀`,
by Milne's route**: the conclusion of `orthUr_quasiIso_of_print` (for every isotropy homotopy `J`)
without `NekovarProp756`, through round 2's `orthPerPlace_of_localDuality`. Hypotheses: the
PRINTs (`MilneADT_I_2_6`: tex 3483–3498, 3815–3816; `NekovarProp524`: tex 3455–3456); the standing
setting for `S₀` (`hset`) and `S.Finite`, so that it holds for `S` (Nekovář 5.1, tex 3455–3456);
the perfect pairing `β₀` into the cyclotomic twist `T₀` (`hb`, `hb'`, `hT`, inflated to `G_{K,S}`
by `cycloInfl_isCyclotomicTwist`; tex 2798–2804); a trace `tr_w` killing coboundaries and inducing
`H² ≅ R` (tex 3465); and the coefficient pairing in Milne's form `UrMDualForm` (tex
3465–3467). -/
theorem urM_quasiIso_of_milne [IsLocalRing R] (hM : MilneADT_I_2_6) (h524 : NekovarProp524 K)
    (p : ℕ) (hset : NekovarFiniteSetting K S₀ p R) (hSfin : S.Finite)
    (hb : Function.Bijective β₀) (hb' : Function.Bijective β₀.flip)
    (hT : IsCyclotomicTwist K S₀ R T₀) (w : Places K S) (hw : w.1 ∉ S₀)
    (hdual : UrMDualForm hS β₀ w)
    (J : LocalTruncIsotropy (urAt hS R M₀ w hw).i (urAt hS R M₀' w hw).i
      (orthUrPair hS R β₀ hβ₀ w))
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS T₀) w).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS T₀) w).d 1 2 rfl z) = 0)
    (htrv2 : InducesIsoH2 trv) :
    QuasiIso (GHom.toCC (orthLocalMap (urAt hS R M₀ w hw).i (urAt hS R M₀' w hw).i
      (orthUrPair hS R β₀ hβ₀ w) J trv htrv)) := by
  have hsetS : NekovarFiniteSetting K S p R :=
    { hset with
      finite_S := hSfin
      above_p := fun v hv => hS (hset.above_p v hv) }
  have := hset.selfInjective
  have : Finite (InflMod hS M₀) := inferInstanceAs (Finite M₀)
  have : Finite (InflMod hS M₀') := inferInstanceAs (Finite M₀')
  exact orthPerPlace_of_localDuality (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
    (urAt hS R M₀ w hw) (urAt hS R M₀' w hw) J trv htrv
    (h524 S p R hsetS (InflMod hS M₀) (InflMod hS M₀') (InflMod hS T₀) (orthInflPair hS R β₀)
      (orthInflPair_smul hS R β₀ hβ₀) hb hb' (cycloInfl_isCyclotomicTwist hS hT) w trv htrv
      htrv2)
    (orth_urAt_vanishes hS R M₀ w hw) (orth_urAt_vanishes hS R M₀' w hw)
    (urM_h01 hS w hw) (urM_h01 hS w hw)
    (urM_annihilator hS β₀ hβ₀ hM p hset w hw hdual trv htrv htrv2)

end Pair

end Place

end ZInQ.Manuscript.RC.KummerMaps
