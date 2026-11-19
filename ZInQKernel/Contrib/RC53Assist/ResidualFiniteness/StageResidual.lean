import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageInputs
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageFlat
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer

/-!
# Residual finiteness of the stage Selmer complexes, by base change of continuous cochains

The finite free model of the retained inner-limit lemma (manuscript lines 4391–4414) applies at
every coefficient stage `A_i = (ℤ/2^i)[t]/t^i` to a stage complex `C` whose residual cohomology
`H^n(k ⊗_{A_i} C)` is finite over the residue field `k` in every degree
(`ResidualCohomologyFinite`). This file proves this for the actual stage Selmer complexes, from the
finiteness prints `MilneLocalFiniteness` and `MilneGlobalFiniteness` (Milne, *Arithmetic duality
theorems*, I, Theorem 2.1 and Corollary 4.15), through the base-change comparison of continuous
cochains.

## The base-change comparison for continuous cochains

For a commutative ring `A`, an `A`-algebra `B`, a compact topological group `G` and a discrete
`A`-module `N` with continuous `G`-action:

* `BCoef A B N`: the module `B ⊗_A N` with the action `g ↦ id ⊗ g` and the discrete topology; the
  action is continuous (`BCoef.continuousSMul`), `B ⊗_A N` is finite for finite `B` and `N`
  (`finite_bcoef`), and its order divides that of `N` when `A → B` is onto (`card_bcoef_dvd`).
* `lcTensorEquiv`: `B ⊗_A LC(X, N) ≅ LC(X, B ⊗_A N)` for a compact space `X`: a locally constant
  function factors through a finite discrete quotient `Q` of `X`, and
  `B ⊗_A (Q → N) ≅ (Q → B ⊗_A N)` (`TensorProduct.piRight`); the modules of functions on the
  blocks of finite clopen partitions form a directed family exhausting `LC(X, N)`.
* `cochainBaseChangeEquivOf`, `cochainBaseChangeEquivOf_comm`: `B ⊗_A C^n_cont(G, N) ≅
  C^n_cont(G, N')`, `b ⊗ f ↦ (x ↦ e(b ⊗ f(x)))`, for a `G`-equivariant identification
  `e : B ⊗_A N ≅ N'`, compatibly with the differentials (continuous cochains with discrete
  coefficients are the locally constant functions on `G^n`, `contCochainLCEquiv`);
  `cochainBaseChangeEquiv` for `N' = B ⊗_A N`.
* `natCochainsBaseChangeHom`, `natCochainsBaseChangeIso`, `natCochainsBaseChange_homologyIso`: the
  comparison as an isomorphism of complexes `B ⊗_A C^•_cont(G, N) ≅ C^•_cont(G, B ⊗_A N)` and
  `H^n(B ⊗_A C^•_cont(G, N)) ≅ H^n_cont(G, B ⊗_A N)`; `natBaseChangeF_res`: it commutes with
  restriction along a continuous homomorphism.

## Through the Selmer cone and the local conditions

* `ghomBaseChange`, `piBaseChangeHom`, `selDataBaseChange`, `selBaseChangeHom`: base change of chain
  maps, of finite products of complexes and of Selmer data, `B ⊗_A C_U(D) ≅ C_U(B ⊗_A D)`.
* `selCxMap`: a map of Selmer data `G --res--> L <--ι-- U` induces a chain map of Selmer complexes.
* `residualConditions`: the local conditions `B ⊗_A U_v → B ⊗_A C^•_cont(G_v, M) ≅
  C^•_cont(G_v, B ⊗_A M)`; `residualSelmerHom`, `residualSelmerIso`, `residualGaloisSelmerIso`:
  `B ⊗_A C_U(G_S, M) ≅ C_{B ⊗ U}(G_S, B ⊗_A M)`, the Selmer complex of the base-changed module.

## Residual finiteness

* `galoisSelmer_residualCohomologyFinite`: for a finite local ring `A`, a finite discrete module
  `M`, a finite `S` containing the primes dividing `#M` and local conditions with finite residual
  cohomology, the actual Selmer complex has finite residual cohomology: its residual complex is the
  Selmer complex of the finite discrete module `k ⊗_A M` with the residual conditions, whose
  cohomology is finite by `galoisSelmerCohomologyFinite_of_prints`.
* `stageSelmer_residualCohomologyFinite`: the same at the stage `A_i` for the actual module
  `M_i = (E[2^i] ⊗ A_i)(α)` and a finite `S` containing the primes above `2`;
  `stageStrictSelmer_residualCohomologyFinite`, `stageRelaxedSelmer_residualCohomologyFinite`: the
  strict and the relaxed stage Selmer complexes; `stageKummerSelmer_residualCohomologyFinite`: the
  Kummer conditions at every place of `S`; `actualStageSelmer_residualCohomologyFinite` and its full
  and zero variants: the old conditions at `S₀` and the unramified conditions at `S − S₀`.
* The local conditions: `residualCohomologyFinite_zeroCx` (zero condition),
  `localCx_residualCohomologyFinite` (full condition), `urAt_residualCohomologyFinite` (unramified
  condition), `residualCohomologyFinite_cocycleCondition` (cocycle conditions, in particular the
  Kummer conditions, when `H¹(G_v, M)` is finite), `residualCohomologyFinite_of_finite_X` (any
  complex with finite terms).

Sources: the retained inner-limit lemma, manuscript lines 4385–4451; the finiteness inputs, lines
3442, 4526 and 4547.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.ResidualFiniteness

open CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Manuscript.RC.Limits (blockFunctionsMap blockFunctionsMap_apply)
open scoped TensorProduct

/-! ### Base change of chain maps, finite products and Selmer data -/

section BaseChange

variable {A : Type} [CommRing A] (B : Type) [CommRing B] [Algebra A B]

theorem gcxBaseChange_d_tmul (C : GCx A) (i j : ℤ) (h : i + 1 = j) (b : B) (x : C.X i) :
    (gcxBaseChange B C).d i j h (b ⊗ₜ[A] x) = b ⊗ₜ[A] C.d i j h x :=
  rfl

/-- Base change preserves commutative squares of linear maps. -/
theorem baseChange_comp_apply_eq {M N P Q : Type} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] (f₁ : M →ₗ[A] N)
    (f₂ : N →ₗ[A] P) (g₁ : M →ₗ[A] Q) (g₂ : Q →ₗ[A] P) (h : f₂ ∘ₗ f₁ = g₂ ∘ₗ g₁)
    (x : B ⊗[A] M) : f₂.baseChange B (f₁.baseChange B x) = g₂.baseChange B (g₁.baseChange B x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h, LinearMap.baseChange_comp,
    LinearMap.comp_apply]

/-- **The base change of a chain map** `f : C → C'`: the components `id_B ⊗ f`. -/
def ghomBaseChange {C C' : GCx A} (f : GHom C C') :
    GHom (gcxBaseChange B C) (gcxBaseChange B C') where
  f i j h := (f.f i j h).baseChange B
  comm i i₁ j j₁ hij h₁ h₂ hj x :=
    baseChange_comp_apply_eq B (C.d i i₁ h₁) (f.f i₁ j₁ hj) (f.f i j hij) (C'.d j j₁ h₂)
      (LinearMap.ext fun y => f.comm i i₁ j j₁ hij h₁ h₂ hj y) x

theorem ghomBaseChange_f_tmul {C C' : GCx A} (f : GHom C C') (i j : ℤ) (h : i = j) (b : B)
    (x : C.X i) : (ghomBaseChange B f).f i j h (b ⊗ₜ[A] x) = b ⊗ₜ[A] f.f i j h x :=
  rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The degreewise comparison `B ⊗_A ∏_v C_v^n ≅ ∏_v (B ⊗_A C_v^n)` for finitely many `v`. -/
def piBaseChangeEquiv (Cs : ι → GCx A) (n : ℤ) :
    B ⊗[A] (∀ v, (Cs v).X n) ≃ₗ[B] ∀ v, B ⊗[A] (Cs v).X n :=
  TensorProduct.piRight A B B (fun v => (Cs v).X n)

theorem piBaseChangeEquiv_tmul (Cs : ι → GCx A) (n : ℤ) (b : B) (x : ∀ v, (Cs v).X n) :
    piBaseChangeEquiv B Cs n (b ⊗ₜ[A] x) = fun v => b ⊗ₜ[A] x v :=
  rfl

/-- The degreewise comparison for finite products commutes with the differentials. -/
theorem piBaseChangeEquiv_comm (Cs : ι → GCx A) (i i₁ : ℤ) (h : i + 1 = i₁) :
    (piBaseChangeEquiv B Cs i₁).toLinearMap ∘ₗ ((piCx Cs).d i i₁ h).baseChange B =
      ((piCx fun v => gcxBaseChange B (Cs v)).d i i₁ h) ∘ₗ
        (piBaseChangeEquiv B Cs i).toLinearMap :=
  TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl

/-- **Base change commutes with finite products of complexes**: the chain map
`B ⊗_A ∏_v C_v → ∏_v (B ⊗_A C_v)`, `b ⊗ (x_v)_v ↦ (b ⊗ x_v)_v`. -/
def piBaseChangeHom (Cs : ι → GCx A) :
    GHom (gcxBaseChange B (piCx Cs)) (piCx fun v => gcxBaseChange B (Cs v)) where
  f i j h := by
    subst h
    exact (piBaseChangeEquiv B Cs i).toLinearMap
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    exact LinearMap.congr_fun (piBaseChangeEquiv_comm B Cs i i₁ h₁) x

theorem piBaseChangeHom_bijective (Cs : ι → GCx A) (n : ℤ) :
    Function.Bijective ((piBaseChangeHom B Cs).f n n rfl) :=
  (piBaseChangeEquiv B Cs n).bijective

/-- **The base change of Selmer data** `G --res--> L <--ι-- U`: base change of the three complexes
and of the two chain maps. -/
def selDataBaseChange (D : SelData A) : SelData B :=
  ⟨gcxBaseChange B D.G, gcxBaseChange B D.U, gcxBaseChange B D.L, ghomBaseChange B D.res,
    ghomBaseChange B D.ι⟩

/-- The degreewise comparison
`B ⊗_A (G^n × U^n × L^{n−1}) ≅ (B ⊗ G^n) × (B ⊗ U^n) × (B ⊗ L^{n−1})`. -/
def selBaseChangeEquiv (D : SelData A) (n : ℤ) :
    B ⊗[A] selT D n ≃ₗ[B] (B ⊗[A] D.G.X n) × (B ⊗[A] D.U.X n) × (B ⊗[A] D.L.X (n - 1)) :=
  (TensorProduct.prodRight A B B (D.G.X n) (D.U.X n × D.L.X (n - 1))).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl B (B ⊗[A] D.G.X n))
      (TensorProduct.prodRight A B B (D.U.X n) (D.L.X (n - 1))))

theorem selBaseChangeEquiv_tmul (D : SelData A) (n : ℤ) (b : B) (c : selT D n) :
    selBaseChangeEquiv B D n (b ⊗ₜ[A] c) = (b ⊗ₜ[A] c.1, b ⊗ₜ[A] c.2.1, b ⊗ₜ[A] c.2.2) :=
  rfl

/-- The degreewise comparison for Selmer complexes commutes with the differentials. -/
theorem selBaseChangeEquiv_comm (D : SelData A) (i i₁ : ℤ) (h : i + 1 = i₁) :
    (selBaseChangeEquiv B D i₁).toLinearMap ∘ₗ ((selCx D).d i i₁ h).baseChange B =
      ((selCx (selDataBaseChange B D)).d i i₁ h) ∘ₗ (selBaseChangeEquiv B D i).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun b c => ?_
  obtain ⟨a, u, y⟩ := c
  change ((b ⊗ₜ[A] D.G.d i i₁ h a, b ⊗ₜ[A] D.U.d i i₁ h u,
      b ⊗ₜ[A] (D.res.f i (i₁ - 1) (by omega) a - D.ι.f i (i₁ - 1) (by omega) u -
        D.L.d (i - 1) (i₁ - 1) (by omega) y)) :
        (B ⊗[A] D.G.X i₁) × (B ⊗[A] D.U.X i₁) × (B ⊗[A] D.L.X (i₁ - 1))) =
    (b ⊗ₜ[A] D.G.d i i₁ h a, b ⊗ₜ[A] D.U.d i i₁ h u,
      (b ⊗ₜ[A] D.res.f i (i₁ - 1) (by omega) a - b ⊗ₜ[A] D.ι.f i (i₁ - 1) (by omega) u -
        b ⊗ₜ[A] D.L.d (i - 1) (i₁ - 1) (by omega) y : B ⊗[A] D.L.X (i₁ - 1)))
  rw [TensorProduct.tmul_sub, TensorProduct.tmul_sub]

/-- **Base change commutes with the Selmer complex**: the chain map
`B ⊗_A C_U(D) → C_U(B ⊗_A D)`, `b ⊗ (a, u, x) ↦ (b ⊗ a, b ⊗ u, b ⊗ x)`. -/
def selBaseChangeHom (D : SelData A) :
    GHom (gcxBaseChange B (selCx D)) (selCx (selDataBaseChange B D)) where
  f i j h := by
    subst h
    exact (selBaseChangeEquiv B D i).toLinearMap
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    exact LinearMap.congr_fun (selBaseChangeEquiv_comm B D i i₁ h₁) x

theorem selBaseChangeHom_bijective (D : SelData A) (n : ℤ) :
    Function.Bijective ((selBaseChangeHom B D).f n n rfl) :=
  (selBaseChangeEquiv B D n).bijective

end BaseChange

/-! ### Finiteness of cohomology -/

section Finiteness

variable {R : Type} [CommRing R]

/-- **A chain map with bijective components is an isomorphism of complexes.** -/
theorem isIso_toCC_of_bijective {C C' : GCx R} (f : GHom C C')
    (hf : ∀ n, Function.Bijective (f.f n n rfl)) : IsIso (GHom.toCC f) := by
  have : ∀ m, IsIso ((GHom.toCC f).f m) := fun m => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hf m
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The isomorphism of cohomology induced by a chain map with bijective components. -/
def homologyIsoOfBijective {C C' : GCx R} (f : GHom C C')
    (hf : ∀ n, Function.Bijective (f.f n n rfl)) (n : ℤ) :
    C.toCC.homology n ≅ C'.toCC.homology n :=
  haveI := isIso_toCC_of_bijective f hf
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℤ) n).mapIso
    (asIso (GHom.toCC f))

/-- **A chain map with bijective components preserves and reflects the finiteness of
cohomology.** -/
theorem finite_homology_iff_of_bijective {C C' : GCx R} (f : GHom C C')
    (hf : ∀ n, Function.Bijective (f.f n n rfl)) (n : ℤ) :
    Finite (C.toCC.homology n) ↔ Finite (C'.toCC.homology n) :=
  ⟨fun _ => Finite.of_equiv _ (homologyIsoOfBijective f hf n).toLinearEquiv.toEquiv,
    fun _ => Finite.of_equiv _ (homologyIsoOfBijective f hf n).toLinearEquiv.symm.toEquiv⟩

/-- The cohomology of a complex is finite in every degree in which its term is finite. -/
theorem finite_homology_of_finite_X (C : GCx R) (n : ℤ) (h : Finite (C.X n)) :
    Finite (C.toCC.homology n) := by
  rw [finite_gcx_homology_iff]
  exact Finite.of_surjective _ (Submodule.mkQ_surjective _)

end Finiteness

/-! ### Residual finiteness for complexes with finite terms -/

section FiniteTerms

variable {A : Type} [CommRing A] [IsLocalRing A]

/-- The residue field of a finite local ring is finite. -/
theorem finite_residueField [Finite A] : Finite (IsLocalRing.ResidueField A) :=
  Finite.of_surjective _ IsLocalRing.residue_surjective

/-- The base change of a finite module to the residue field of a finite local ring is finite. -/
theorem finite_residue_tensor [Finite A] (X : Type) [AddCommGroup X] [Module A X] [Finite X] :
    Finite (IsLocalRing.ResidueField A ⊗[A] X) := by
  have := finite_residueField (A := A)
  have : Module.Finite A X := Module.Finite.of_finite
  exact Module.finite_of_finite (IsLocalRing.ResidueField A)

/-- **Over a finite local ring, a complex with finite terms has finite residual cohomology.** -/
theorem residualCohomologyFinite_of_finite_X [Finite A] (C : GCx A) (hC : ∀ n, Finite (C.X n)) :
    ResidualCohomologyFinite C := by
  intro n
  have := hC n
  have : Finite ((gcxBaseChange (IsLocalRing.ResidueField A) C).X n) :=
    finite_residue_tensor (C.X n)
  have := finite_homology_of_finite_X (gcxBaseChange (IsLocalRing.ResidueField A) C) n this
  exact Module.Finite.of_finite

/-- The zero complex has finite residual cohomology (the strict local condition). -/
theorem residualCohomologyFinite_zeroCx [Finite A] :
    ResidualCohomologyFinite (ZInQ.Manuscript.RC.SelmerComplex.zeroCx A) :=
  residualCohomologyFinite_of_finite_X _ fun _ => inferInstanceAs (Finite PUnit)

/-- Residual finiteness of cohomology in the form of finite sets, over a finite local ring. -/
theorem residualCohomologyFinite_iff_finite [Finite A] (C : GCx A) :
    ResidualCohomologyFinite C ↔
      ∀ n, Finite ((gcxBaseChange (IsLocalRing.ResidueField A) C).toCC.homology n) := by
  have := finite_residueField (A := A)
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · have := h n
    exact Module.finite_of_finite (IsLocalRing.ResidueField A)
  · have := h n
    exact Module.Finite.of_finite

end FiniteTerms

/-! ### The base-changed coefficient module -/

section Coefficients

variable (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
  (N : Type) [AddCommGroup N] [Module A N]

/-- **The base-changed coefficient module** `B ⊗_A N`, a type synonym which carries the action of a
group on the right factor and the discrete topology. -/
def BCoef : Type := B ⊗[A] N

instance : AddCommGroup (BCoef A B N) := inferInstanceAs (AddCommGroup (B ⊗[A] N))

instance : Module B (BCoef A B N) := inferInstanceAs (Module B (B ⊗[A] N))

instance : TopologicalSpace (BCoef A B N) := ⊥

instance : DiscreteTopology (BCoef A B N) := ⟨rfl⟩

/-- A pure tensor of the base-changed coefficient module. -/
def bcTmul (b : B) (n : N) : BCoef A B N := b ⊗ₜ[A] n

variable {G : Type} [Group G] [DistribMulAction G N] [SMulCommClass G A N]

/-- The action of `g` on `B ⊗_A N`: `id_B ⊗ g`. -/
def bcAct (g : G) : BCoef A B N →ₗ[B] BCoef A B N :=
  (DistribSMul.toLinearMap A N g).baseChange B

theorem bcAct_tmul (g : G) (b : B) (n : N) :
    bcAct A B N g (bcTmul A B N b n) = bcTmul A B N b (g • n) :=
  rfl

theorem distribToLinearMap_one : DistribSMul.toLinearMap A N (1 : G) = LinearMap.id :=
  LinearMap.ext fun n => one_smul G n

theorem distribToLinearMap_mul (g h : G) :
    DistribSMul.toLinearMap A N (g * h) =
      DistribSMul.toLinearMap A N g ∘ₗ DistribSMul.toLinearMap A N h :=
  LinearMap.ext fun n => mul_smul g h n

instance : DistribMulAction G (BCoef A B N) where
  smul g x := bcAct A B N g x
  one_smul x := by
    change (DistribSMul.toLinearMap A N (1 : G)).baseChange B x = x
    rw [distribToLinearMap_one, LinearMap.baseChange_id]
    rfl
  mul_smul g h x := by
    change (DistribSMul.toLinearMap A N (g * h)).baseChange B x =
      (DistribSMul.toLinearMap A N g).baseChange B
        ((DistribSMul.toLinearMap A N h).baseChange B x)
    rw [distribToLinearMap_mul, LinearMap.baseChange_comp]
    rfl
  smul_zero g := map_zero (bcAct A B N g)
  smul_add g x y := map_add (bcAct A B N g) x y

theorem bcoef_smul_def (g : G) (x : BCoef A B N) : g • x = bcAct A B N g x :=
  rfl

theorem smul_bcTmul (g : G) (b : B) (n : N) :
    g • bcTmul A B N b n = bcTmul A B N b (g • n) :=
  rfl

instance : SMulCommClass G B (BCoef A B N) where
  smul_comm g b x := (bcAct A B N g).map_smul b x

/-- Every element of `B ⊗_A N` is a sum of pure tensors (induction principle on `BCoef`). -/
@[elab_as_elim]
theorem BCoef.induction_on {P : BCoef A B N → Prop} (x : BCoef A B N)
    (ht : ∀ b n, P (bcTmul A B N b n)) (ha : ∀ x y, P x → P y → P (x + y)) : P x :=
  TensorProduct.inductionOn (motive := P) x ht ha

/-- **The action on `B ⊗_A N` is continuous** for a topological group acting continuously on the
discrete module `N`: the stabilizer of a pure tensor `b ⊗ n` contains that of `n`, and the
stabilizer of a sum contains the intersection of the stabilizers. -/
instance BCoef.continuousSMul [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace N]
    [DiscreteTopology N] [ContinuousSMul G N] : ContinuousSMul G (BCoef A B N) := by
  refine continuousSMul_iff_stabilizer_isOpen.mpr fun x => ?_
  refine BCoef.induction_on A B N x ?_ ?_
  · intro b n
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G n) ?_ (stabilizer_isOpen G n)
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [smul_bcTmul, hg]
  · intro x y hx hy
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) ?_
      (hx.inter hy)
    intro g hg
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff] at hg
    rw [MulAction.mem_stabilizer_iff, smul_add, hg.1, hg.2]

omit [DistribMulAction G N] [SMulCommClass G A N] in
/-- `B ⊗_A N` is finite for finite `B` and `N`. -/
theorem finite_bcoef [Finite B] [Finite N] : Finite (BCoef A B N) := by
  have : Module.Finite A N := Module.Finite.of_finite
  have : Module.Finite B (B ⊗[A] N) := Module.Finite.base_change A B N
  exact Module.finite_of_finite B (M := B ⊗[A] N)

omit [DistribMulAction G N] [SMulCommClass G A N] in
theorem bcTmul_add (b : B) (n n' : N) :
    bcTmul A B N b (n + n') = bcTmul A B N b n + bcTmul A B N b n' :=
  TensorProduct.tmul_add b n n'

omit [DistribMulAction G N] [SMulCommClass G A N] in
theorem bcTmul_sum {ι : Type} (s : Finset ι) (b : B) (n : ι → N) :
    bcTmul A B N b (∑ j ∈ s, n j) = ∑ j ∈ s, bcTmul A B N b (n j) :=
  TensorProduct.tmul_sum b s n

omit [DistribMulAction G N] [SMulCommClass G A N] in
theorem bcTmul_smul (b : B) (a : A) (n : N) :
    bcTmul A B N b (a • n) = algebraMap A B a • bcTmul A B N b n := by
  change b ⊗ₜ[A] (a • n) = algebraMap A B a • (b ⊗ₜ[A] n)
  rw [TensorProduct.tmul_smul, algebraMap_smul]

omit [DistribMulAction G N] [SMulCommClass G A N] in
/-- When `A → B` is surjective (e.g. `B` the residue field of `A`), every element of `B ⊗_A N` is
`1 ⊗ n`. -/
theorem bcTmul_one_surjective (hB : Function.Surjective (algebraMap A B)) :
    Function.Surjective fun n : N => bcTmul A B N 1 n := by
  intro x
  refine BCoef.induction_on A B N x (fun b n => ?_) (fun x y hx hy => ?_)
  · obtain ⟨a, rfl⟩ := hB b
    refine ⟨a • n, ?_⟩
    change (1 : B) ⊗ₜ[A] (a • n) = algebraMap A B a ⊗ₜ[A] n
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    exact ⟨m + m', bcTmul_add A B N 1 m m'⟩

omit [DistribMulAction G N] [SMulCommClass G A N] in
/-- When `A → B` is surjective, the order of `B ⊗_A N` divides that of `N`. -/
theorem card_bcoef_dvd (hB : Function.Surjective (algebraMap A B)) :
    Nat.card (BCoef A B N) ∣ Nat.card N :=
  AddSubgroup.card_dvd_of_surjective
    (f := ({ toFun := fun n => bcTmul A B N 1 n
             map_zero' := TensorProduct.tmul_zero N (1 : B)
             map_add' := bcTmul_add A B N 1 } : N →+ BCoef A B N))
    (bcTmul_one_surjective A B N hB)

end Coefficients

/-! ### Locally constant functions on a compact space -/

section LocallyConstant

variable (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
  (X : Type) [TopologicalSpace X] (N : Type) [AddCommGroup N] [Module A N]

/-- The pointwise map `B ⊗_A LC(X, N) → (X → B ⊗_A N)`, `b ⊗ f ↦ (x ↦ b ⊗ f x)`. -/
def lcTensorFun : B ⊗[A] LocallyConstant X N →ₗ[B] X → B ⊗[A] N :=
  TensorProduct.piRightHom A B B (fun _ : X => N) ∘ₗ (LocallyConstant.coeFnₗ A).baseChange B

theorem lcTensorFun_tmul (b : B) (f : LocallyConstant X N) (x : X) :
    lcTensorFun A B X N (b ⊗ₜ[A] f) x = b ⊗ₜ[A] f x :=
  rfl

theorem isLocallyConstant_lcTensorFun (z : B ⊗[A] LocallyConstant X N) :
    IsLocallyConstant (lcTensorFun A B X N z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b f => exact f.isLocallyConstant.comp fun n => b ⊗ₜ[A] n
  | add z w hz hw =>
    rw [map_add]
    exact hz.add hw

/-- **The comparison map** `B ⊗_A LC(X, N) → LC(X, B ⊗_A N)`, `b ⊗ f ↦ (x ↦ b ⊗ f x)`. -/
def lcTensorMap : B ⊗[A] LocallyConstant X N →ₗ[B] LocallyConstant X (B ⊗[A] N) where
  toFun z := ⟨lcTensorFun A B X N z, isLocallyConstant_lcTensorFun A B X N z⟩
  map_add' z w := LocallyConstant.ext fun x => by
    change lcTensorFun A B X N (z + w) x = lcTensorFun A B X N z x + lcTensorFun A B X N w x
    rw [map_add, Pi.add_apply]
  map_smul' c z := LocallyConstant.ext fun x => by
    change lcTensorFun A B X N (c • z) x = c • lcTensorFun A B X N z x
    rw [map_smul, Pi.smul_apply]

theorem lcTensorMap_apply (z : B ⊗[A] LocallyConstant X N) (x : X) :
    lcTensorMap A B X N z x = lcTensorFun A B X N z x :=
  rfl

theorem lcTensorMap_tmul (b : B) (f : LocallyConstant X N) (x : X) :
    lcTensorMap A B X N (b ⊗ₜ[A] f) x = b ⊗ₜ[A] f x :=
  rfl

/-- On functions pulled back from a discrete quotient `Q`, the comparison map is the evaluation
of `B ⊗_A (Q → N) → (Q → B ⊗_A N)` at the block. -/
theorem lcTensorMap_blockFunctions (Q : DiscreteQuotient X) (y : B ⊗[A] (Q → N)) (x : X) :
    lcTensorMap A B X N ((blockFunctionsMap A N Q).baseChange B y) x =
      TensorProduct.piRightHom A B B (fun _ : Q => N) y (Q.proj x) := by
  rw [lcTensorMap_apply]
  induction y using TensorProduct.inductionOn with
  | tmul b g => rfl
  | add y y' hy hy' => rw [map_add, map_add, Pi.add_apply, hy, hy', map_add, Pi.add_apply]

/-- Functions on a coarser discrete quotient are functions on a finer one. -/
theorem blockFunctionsMap_ofLE {Q Q' : DiscreteQuotient X} (h : Q' ≤ Q) :
    blockFunctionsMap A N Q =
      blockFunctionsMap A N Q' ∘ₗ LinearMap.funLeft A N (DiscreteQuotient.ofLE h) := by
  ext g x
  change g (Q.proj x) = g (DiscreteQuotient.ofLE h (Q'.proj x))
  rw [DiscreteQuotient.ofLE_proj]

/-- **Every element of `B ⊗_A LC(X, N)` comes from functions on a discrete quotient.** -/
theorem exists_blockFunctions_baseChange (z : B ⊗[A] LocallyConstant X N) :
    ∃ (Q : DiscreteQuotient X) (y : B ⊗[A] (Q → N)),
      (blockFunctionsMap A N Q).baseChange B y = z := by
  induction z using TensorProduct.inductionOn with
  | tmul b f =>
    refine ⟨f.discreteQuotient, b ⊗ₜ[A] ⇑f.lift, ?_⟩
    rw [LinearMap.baseChange_tmul]
    congr 1
  | add z w hz hw =>
    obtain ⟨Q₁, y₁, rfl⟩ := hz
    obtain ⟨Q₂, y₂, rfl⟩ := hw
    refine ⟨Q₁ ⊓ Q₂,
      (LinearMap.funLeft A N (DiscreteQuotient.ofLE (inf_le_left : Q₁ ⊓ Q₂ ≤ Q₁))).baseChange B y₁ +
        (LinearMap.funLeft A N (DiscreteQuotient.ofLE (inf_le_right : Q₁ ⊓ Q₂ ≤ Q₂))).baseChange B
          y₂, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp, ← blockFunctionsMap_ofLE, ← blockFunctionsMap_ofLE]

/-- **The comparison map is bijective for compact `X`.** -/
theorem lcTensorMap_bijective [CompactSpace X] : Function.Bijective (lcTensorMap A B X N) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨Q, y, rfl⟩ := exists_blockFunctions_baseChange A B X N z
    have : Fintype Q := Fintype.ofFinite Q
    have hy : TensorProduct.piRight A B B (fun _ : Q => N) y = 0 := by
      funext q
      obtain ⟨x, rfl⟩ := Q.proj_surjective q
      rw [TensorProduct.piRight_apply, ← lcTensorMap_blockFunctions, hz]
      rfl
    rw [(LinearEquiv.map_eq_zero_iff _).mp hy, map_zero]
  · intro F
    have : Fintype F.discreteQuotient := Fintype.ofFinite _
    refine ⟨(blockFunctionsMap A N F.discreteQuotient).baseChange B
      ((TensorProduct.piRight A B B (fun _ : F.discreteQuotient => N)).symm ⇑F.lift), ?_⟩
    refine LocallyConstant.ext fun x => ?_
    rw [lcTensorMap_blockFunctions, ← TensorProduct.piRight_apply, LinearEquiv.apply_symm_apply]
    rfl

/-- **`B ⊗_A LC(X, N) ≅ LC(X, B ⊗_A N)` for compact `X`.** -/
def lcTensorEquiv [CompactSpace X] :
    B ⊗[A] LocallyConstant X N ≃ₗ[B] LocallyConstant X (B ⊗[A] N) :=
  LinearEquiv.ofBijective (lcTensorMap A B X N) (lcTensorMap_bijective A B X N)

theorem lcTensorEquiv_tmul [CompactSpace X] (b : B) (f : LocallyConstant X N) (x : X) :
    lcTensorEquiv A B X N (b ⊗ₜ[A] f) x = b ⊗ₜ[A] f x :=
  rfl

omit [Algebra A B] in
/-- Post-composition with a linear equivalence, on locally constant functions. -/
def lcCongrRight {P P' : Type} [AddCommGroup P] [Module B P] [AddCommGroup P'] [Module B P']
    (e : P ≃ₗ[B] P') : LocallyConstant X P ≃ₗ[B] LocallyConstant X P' where
  toFun f := f.map e
  invFun f := f.map e.symm
  map_add' f g := LocallyConstant.ext fun x => map_add e (f x) (g x)
  map_smul' c f := LocallyConstant.ext fun x => map_smul e c (f x)
  left_inv f := LocallyConstant.ext fun x => e.symm_apply_apply (f x)
  right_inv f := LocallyConstant.ext fun x => e.apply_symm_apply (f x)

end LocallyConstant

/-! ### Continuous cochains with discrete coefficients -/

section Cochains

variable (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
  (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (N : Type) [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulCommClass G A N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]
  {N' : Type} [AddCommGroup N'] [Module B N'] [DistribMulAction G N'] [SMulCommClass G B N']
  [TopologicalSpace N'] [DiscreteTopology N'] [ContinuousSMul G N']
  (e : B ⊗[A] N ≃ₗ[B] N')

/-- **The base-change comparison for continuous cochains with discrete coefficients**, for a
`B`-linear identification `e : B ⊗_A N ≅ N'`: `B ⊗_A C^n_cont(G, N) ≅ C^n_cont(G, N')`,
`b ⊗ f ↦ (x ↦ e(b ⊗ f(x)))` (continuous cochains are the locally constant functions on the
compact space `G^n`). -/
def cochainBaseChangeEquivOf (n : ℕ) :
    B ⊗[A] (contCochains A G N).X n ≃ₗ[B] (contCochains B G N').X n :=
  ((LinearEquiv.baseChange A B _ _ (contCochainLCEquiv A G N n)).trans
    (lcTensorEquiv A B (Fin n → G) N)).trans
    ((lcCongrRight B (Fin n → G) e).trans (contCochainLCEquiv B G N' n).symm)

/-- The comparison evaluated: `(b ⊗ f)(x) = e(b ⊗ f(x))`. -/
theorem cochainBaseChangeEquivOf_tmul_apply (n : ℕ) (b : B) (f : (contCochains A G N).X n)
    (x : Fin n → G) :
    cFun (cochainBaseChangeEquivOf A B G N e n (b ⊗ₜ[A] f)) x = e (b ⊗ₜ[A] cFun f x) :=
  rfl

variable (he : ∀ (g : G) (b : B) (n : N), e (b ⊗ₜ[A] (g • n)) = g • e (b ⊗ₜ[A] n))

include he in
/-- **The comparison commutes with the differentials** when `e` is `G`-equivariant: for `b ⊗ f`,
both sides are
`(g₀, …, gₙ) ↦ g₀ • e(b ⊗ f(g₁, …, gₙ)) + ∑_j (−1)^{j+1} e(b ⊗ f(…, g_j g_{j+1}, …))`. -/
theorem cochainBaseChangeEquivOf_comm (n : ℕ) (z : B ⊗[A] (contCochains A G N).X n) :
    cochainBaseChangeEquivOf A B G N e (n + 1)
        (((contCochains A G N).d n (n + 1)).hom.baseChange B z) =
      ((contCochains B G N').d n (n + 1)).hom (cochainBaseChangeEquivOf A B G N e n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b f =>
    apply Subtype.ext
    funext g
    change e (b ⊗ₜ[A] asFun A G N ((contSubCx A G N).el
        (((contCochains A G N).d n (n + 1)).hom f) : contCochain A G N (n + 1)) g) =
      asFun B G N' ((contSubCx B G N').el
        (((contCochains B G N').d n (n + 1)).hom
          (cochainBaseChangeEquivOf A B G N e n (b ⊗ₜ[A] f))) : contCochain B G N' (n + 1)) g
    rw [contCochains_d_apply, contCochains_d_apply, TensorProduct.tmul_add, map_add,
      TensorProduct.tmul_sum, map_sum]
    congr 1
    · exact he (g 0) b _
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.tmul_smul, ← algebraMap_smul B ((-1 : A) ^ ((j : ℕ) + 1)), map_smul,
        map_pow, map_neg, map_one]
      rfl
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]

/-- The components of the comparison on the complexes extended by zero. -/
def natBaseChangeFOf :
    ∀ i : ℤ, B ⊗[A] natX (contCochains A G N) i →ₗ[B] natX (contCochains B G N') i
  | Int.ofNat n => (cochainBaseChangeEquivOf A B G N e n).toLinearMap
  | Int.negSucc _ => 0

include he in
theorem natBaseChangeFOf_comm :
    ∀ (i j : ℤ) (h : i + 1 = j) (x : B ⊗[A] natX (contCochains A G N) i),
      natBaseChangeFOf A B G N e j ((natD (contCochains A G N) i j h).baseChange B x) =
        natD (contCochains B G N') i j h (natBaseChangeFOf A B G N e i x)
  | Int.ofNat n, Int.ofNat m, h, x => by
    obtain rfl : m = n + 1 := by
      have h' := h
      simp only [Int.ofNat_eq_natCast] at h'
      omega
    exact cochainBaseChangeEquivOf_comm A B G N e he n x
  | Int.negSucc a, j, h, x => by
    have e1 : natD (contCochains A G N) (Int.negSucc a) j h = 0 := rfl
    have e2 : natD (contCochains B G N') (Int.negSucc a) j h = 0 := rfl
    rw [e1, e2, LinearMap.baseChange_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  | Int.ofNat n, Int.negSucc m, h, _ => absurd h (ofNat_add_one_ne_negSucc n m)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [DistribMulAction G N] [SMulCommClass G A N] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul G N] in
/-- `B ⊗_A 0 = 0`. -/
theorem subsingleton_tensor_punit : Subsingleton (B ⊗[A] PUnit.{1}) := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : B ⊗[A] PUnit.{1}, z = 0 := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul b p =>
      rw [show p = 0 from Subsingleton.elim _ _, TensorProduct.tmul_zero]
    | add z w hz hw => rw [hz, hw, add_zero]
  rw [h x, h y]

theorem natBaseChangeFOf_bijective :
    ∀ i : ℤ, Function.Bijective (natBaseChangeFOf A B G N e i)
  | Int.ofNat n => (cochainBaseChangeEquivOf A B G N e n).bijective
  | Int.negSucc _ => by
    have := subsingleton_tensor_punit A B
    refine ⟨fun x y _ => Subsingleton.elim (α := B ⊗[A] PUnit.{1}) x y, fun y => ⟨0, ?_⟩⟩
    exact Subsingleton.elim (α := PUnit.{1}) _ _

/-- **The base-change comparison as a chain map** `B ⊗_A C^•_cont(G, N) → C^•_cont(G, N')`
(both extended by zero to `ℤ`), for a `G`-equivariant identification `B ⊗_A N ≅ N'`. -/
def natCochainsBaseChangeHomOf :
    GHom (gcxBaseChange B (natCx (contCochains A G N))) (natCx (contCochains B G N')) where
  f i j h := by
    subst h
    exact natBaseChangeFOf A B G N e i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    exact natBaseChangeFOf_comm A B G N e he i i₁ h₁ x

theorem natCochainsBaseChangeHomOf_bijective (n : ℤ) :
    Function.Bijective ((natCochainsBaseChangeHomOf A B G N e he).f n n rfl) :=
  natBaseChangeFOf_bijective A B G N e n

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [DistribMulAction G N] [SMulCommClass G A N] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul G N] in
/-- The identification `B ⊗_A N = BCoef A B N`. -/
def bcoefEquiv : B ⊗[A] N ≃ₗ[B] BCoef A B N :=
  LinearEquiv.refl B (B ⊗[A] N)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace N]
  [DiscreteTopology N] [ContinuousSMul G N] in
theorem bcoefEquiv_smul (g : G) (b : B) (n : N) :
    bcoefEquiv A B N (b ⊗ₜ[A] (g • n)) = g • bcoefEquiv A B N (b ⊗ₜ[A] n) :=
  rfl

/-- **`B ⊗_A C^n_cont(G, N) ≅ C^n_cont(G, B ⊗_A N)`**, `b ⊗ f ↦ (x ↦ b ⊗ f(x))`. -/
abbrev cochainBaseChangeEquiv (n : ℕ) :
    B ⊗[A] (contCochains A G N).X n ≃ₗ[B] (contCochains B G (BCoef A B N)).X n :=
  cochainBaseChangeEquivOf A B G N (bcoefEquiv A B N) n

/-- The comparison evaluated: `(b ⊗ f)(x) = b ⊗ f(x)`. -/
theorem cochainBaseChangeEquiv_tmul_apply (n : ℕ) (b : B) (f : (contCochains A G N).X n)
    (x : Fin n → G) :
    cFun (cochainBaseChangeEquiv A B G N n (b ⊗ₜ[A] f)) x = bcTmul A B N b (cFun f x) :=
  rfl

/-- **`B ⊗_A C^•_cont(G, N) ≅ C^•_cont(G, B ⊗_A N)` commutes with the differentials.** -/
theorem cochainBaseChangeEquiv_comm (n : ℕ) (z : B ⊗[A] (contCochains A G N).X n) :
    cochainBaseChangeEquiv A B G N (n + 1)
        (((contCochains A G N).d n (n + 1)).hom.baseChange B z) =
      ((contCochains B G (BCoef A B N)).d n (n + 1)).hom (cochainBaseChangeEquiv A B G N n z) :=
  cochainBaseChangeEquivOf_comm A B G N _ (bcoefEquiv_smul A B G N) n z

/-- **The base-change comparison as a chain map** `B ⊗_A C^•_cont(G, N) → C^•_cont(G, B ⊗_A N)`
(both extended by zero to `ℤ`). -/
abbrev natCochainsBaseChangeHom :
    GHom (gcxBaseChange B (natCx (contCochains A G N))) (natCx (contCochains B G (BCoef A B N))) :=
  natCochainsBaseChangeHomOf A B G N (bcoefEquiv A B N) (bcoefEquiv_smul A B G N)

theorem natCochainsBaseChangeHom_bijective (n : ℤ) :
    Function.Bijective ((natCochainsBaseChangeHom A B G N).f n n rfl) :=
  natCochainsBaseChangeHomOf_bijective A B G N _ _ n

/-- **`B ⊗_A C^•_cont(G, N) ≅ C^•_cont(G, B ⊗_A N)`** as cochain complexes. -/
def natCochainsBaseChangeIso :
    (gcxBaseChange B (natCx (contCochains A G N))).toCC ≅
      (natCx (contCochains B G (BCoef A B N))).toCC :=
  haveI := isIso_toCC_of_bijective _ (natCochainsBaseChangeHom_bijective A B G N)
  asIso (GHom.toCC (natCochainsBaseChangeHom A B G N))

/-- **`H^n(B ⊗_A C^•_cont(G, N)) ≅ H^n_cont(G, B ⊗_A N)`**. -/
def natCochainsBaseChange_homologyIso (n : ℤ) :
    (gcxBaseChange B (natCx (contCochains A G N))).toCC.homology n ≅
      (natCx (contCochains B G (BCoef A B N))).toCC.homology n :=
  homologyIsoOfBijective _ (natCochainsBaseChangeHom_bijective A B G N) n

end Cochains

/-! ### Naturality with respect to restriction -/

section Restriction

variable (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (φ : H →ₜ* G)
  (N : Type) [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulCommClass G A N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

omit [IsTopologicalGroup G] [CompactSpace G] [IsTopologicalGroup H] [CompactSpace H]
  [DistribMulAction G N] [SMulCommClass G A N] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul G N] in
/-- The identification `B ⊗_A Res_φ N = Res_φ (B ⊗_A N)`. -/
def resBCoefEquiv : B ⊗[A] ResMod φ N ≃ₗ[B] ResMod φ (BCoef A B N) :=
  LinearEquiv.refl B (B ⊗[A] ResMod φ N)

omit [IsTopologicalGroup G] [CompactSpace G] [IsTopologicalGroup H] [CompactSpace H]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N] in
theorem resBCoefEquiv_smul (h : H) (b : B) (n : ResMod φ N) :
    resBCoefEquiv A B φ N (b ⊗ₜ[A] (h • n)) = h • resBCoefEquiv A B φ N (b ⊗ₜ[A] n) :=
  rfl

/-- The comparison for the restricted module: `B ⊗_A C^•_cont(H, Res_φ N) ≅
C^•_cont(H, Res_φ (B ⊗_A N))`. -/
abbrev natCochainsBaseChangeHomRes :
    GHom (gcxBaseChange B (natCx (contCochains A H (ResMod φ N))))
      (natCx (contCochains B H (ResMod φ (BCoef A B N)))) :=
  natCochainsBaseChangeHomOf A B H (ResMod φ N) (resBCoefEquiv A B φ N)
    (resBCoefEquiv_smul A B φ N)

/-- **The comparison commutes with restriction** along `φ : H → G`: both composites send
`b ⊗ f` to `x ↦ b ⊗ f(φ ∘ x)`. -/
theorem natBaseChangeF_res : ∀ (i : ℤ) (z : B ⊗[A] natX (contCochains A G N) i),
    natBaseChangeFOf A B H (ResMod φ N) (resBCoefEquiv A B φ N) i
        ((natF (resCochains (k := A) (M := N) φ) i).baseChange B z) =
      natF (resCochains (k := B) (M := BCoef A B N) φ) i
        (natBaseChangeFOf A B G N (bcoefEquiv A B N) i z)
  | Int.ofNat n, z => by
    induction z using TensorProduct.inductionOn with
    | tmul b f => rfl
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  | Int.negSucc _, _ => rfl

end Restriction

/-! ### Maps of Selmer data -/

section SelMap

variable {R : Type} [CommRing R] {D₁ D₂ : SelData R} (φG : GHom D₁.G D₂.G)
  (φU : GHom D₁.U D₂.U) (φL : GHom D₁.L D₂.L)

/-- The degreewise map `(a, u, x) ↦ (φ_G a, φ_U u, φ_L x)` of Selmer cochains. -/
def selCxMapF (i : ℤ) : selT D₁ i →ₗ[R] selT D₂ i :=
  (φG.f i i rfl).prodMap ((φU.f i i rfl).prodMap (φL.f (i - 1) (i - 1) rfl))

variable
  (hres : ∀ i j (h : i = j) (a : D₁.G.X i),
    φL.f j j rfl (D₁.res.f i j h a) = D₂.res.f i j h (φG.f i i rfl a))
  (hι : ∀ i j (h : i = j) (u : D₁.U.X i),
    φL.f j j rfl (D₁.ι.f i j h u) = D₂.ι.f i j h (φU.f i i rfl u))

include hres hι in
/-- **A map of Selmer data induces a chain map of Selmer complexes**: chain maps `φ_G`, `φ_U`,
`φ_L` with `φ_L ∘ res = res ∘ φ_G` and `φ_L ∘ ι = ι ∘ φ_U` give
`(a, u, x) ↦ (φ_G a, φ_U u, φ_L x)`. -/
def selCxMap : GHom (selCx D₁) (selCx D₂) where
  f i j h := by
    subst h
    exact selCxMapF φG φU φL i
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    have e1 := φG.comm i i₁ i i₁ rfl h₁ h₂ rfl a
    have e2 := φU.comm i i₁ i i₁ rfl h₁ h₂ rfl u
    have e4 := φL.comm (i - 1) (i₁ - 1) (i - 1) (i₁ - 1) rfl (by omega) (by omega) rfl x
    change (φG.f i₁ i₁ rfl (D₁.G.d i i₁ h₁ a), φU.f i₁ i₁ rfl (D₁.U.d i i₁ h₁ u),
        φL.f (i₁ - 1) (i₁ - 1) rfl (D₁.res.f i (i₁ - 1) (by omega) a -
          D₁.ι.f i (i₁ - 1) (by omega) u - D₁.L.d (i - 1) (i₁ - 1) (by omega) x)) =
      (D₂.G.d i i₁ h₂ (φG.f i i rfl a), D₂.U.d i i₁ h₂ (φU.f i i rfl u),
        D₂.res.f i (i₁ - 1) (by omega) (φG.f i i rfl a) -
          D₂.ι.f i (i₁ - 1) (by omega) (φU.f i i rfl u) -
          D₂.L.d (i - 1) (i₁ - 1) (by omega) (φL.f (i - 1) (i - 1) rfl x))
    rw [e1, e2, map_sub, map_sub, hres i (i₁ - 1) (by omega) a, hι i (i₁ - 1) (by omega) u, e4]

theorem selCxMap_bijective (hG : ∀ n, Function.Bijective (φG.f n n rfl))
    (hU : ∀ n, Function.Bijective (φU.f n n rfl)) (hL : ∀ n, Function.Bijective (φL.f n n rfl))
    (n : ℤ) : Function.Bijective ((selCxMap φG φU φL hres hι).f n n rfl) := by
  change Function.Bijective (selCxMapF φG φU φL n)
  rw [selCxMapF, LinearMap.coe_prodMap, LinearMap.coe_prodMap]
  exact (hG n).prodMap ((hU n).prodMap (hL (n - 1)))

end SelMap

theorem ghomComp_bijective {R : Type} [CommRing R] {C₁ C₂ C₃ : GCx R} (f : GHom C₁ C₂)
    (g : GHom C₂ C₃) (hf : ∀ n, Function.Bijective (f.f n n rfl))
    (hg : ∀ n, Function.Bijective (g.f n n rfl)) (n : ℤ) :
    Function.Bijective ((ghomComp f g).f n n rfl) :=
  (hg n).comp (hf n)

theorem piMap_bijective {R : Type} [CommRing R] {ι : Type} {Cs Cs' : ι → GCx R}
    (f : ∀ v, GHom (Cs v) (Cs' v)) (hf : ∀ v n, Function.Bijective ((f v).f n n rfl)) (n : ℤ) :
    Function.Bijective ((piMap f).f n n rfl) := by
  constructor
  · intro x y hxy
    funext v
    exact (hf v n).1 (congrFun hxy v)
  · intro y
    choose x hx using fun v => (hf v n).2 (y v)
    exact ⟨x, funext hx⟩

/-! ### The residual Selmer complex is the Selmer complex of the residual module -/

section ResidualSelmer

variable (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
  (GS : Type) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS] [CompactSpace GS]
  {ι : Type} (Gv : ι → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] [∀ v, CompactSpace (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type) [AddCommGroup M] [Module A M] [DistribMulAction GS M] [SMulCommClass GS A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul GS M]

/-- The comparison of the local complexes at `v`:
`B ⊗_A C^•_cont(G_v, M) ≅ C^•_cont(G_v, B ⊗_A M)`. -/
abbrev localBaseChangeHom (v : ι) :
    GHom (gcxBaseChange B (localCx A GS Gv loc M v)) (localCx B GS Gv loc (BCoef A B M) v) :=
  natCochainsBaseChangeHomRes A B (loc v) M

/-- **The residual local conditions**: `B ⊗_A U_v` with the map
`B ⊗_A U_v → B ⊗_A C^•_cont(G_v, M) ≅ C^•_cont(G_v, B ⊗_A M)`. -/
def residualConditions (Δ : LocalConditions A GS Gv loc M) :
    LocalConditions B GS Gv loc (BCoef A B M) :=
  ⟨fun v => gcxBaseChange B (Δ.U v),
    fun v => ghomComp (ghomBaseChange B (Δ.i v)) (localBaseChangeHom A B GS Gv loc M v)⟩

variable [Fintype ι] [DecidableEq ι]

/-- The comparison of the full local complexes
`B ⊗_A ∏_v C^•_cont(G_v, M) ≅ ∏_v C^•_cont(G_v, B ⊗_A M)`. -/
def localSumBaseChangeHom :
    GHom (gcxBaseChange B (localSumCx A GS Gv loc M)) (localSumCx B GS Gv loc (BCoef A B M)) :=
  ghomComp (piBaseChangeHom B (localCx A GS Gv loc M))
    (piMap (localBaseChangeHom A B GS Gv loc M))

omit [IsTopologicalGroup GS] [CompactSpace GS] [∀ v, IsTopologicalGroup (Gv v)]
  [∀ v, CompactSpace (Gv v)] [DistribMulAction GS M] [SMulCommClass GS A M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul GS M] in
/-- The comparison for finite products and the base change of a map into a product. -/
theorem piBaseChangeEquiv_piLift {Cs : ι → GCx A} {C : GCx A} (f : ∀ v, GHom C (Cs v))
    (i : ℤ) (v : ι) :
    LinearMap.proj v ∘ₗ (piBaseChangeEquiv B Cs i).toLinearMap ∘ₗ
        ((piLift f).f i i rfl).baseChange B = ((f v).f i i rfl).baseChange B :=
  TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl

omit [IsTopologicalGroup GS] [CompactSpace GS] [∀ v, IsTopologicalGroup (Gv v)]
  [∀ v, CompactSpace (Gv v)] [DistribMulAction GS M] [SMulCommClass GS A M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul GS M] in
/-- The comparison for finite products and the base change of a product of maps. -/
theorem piBaseChangeEquiv_piMap {Cs Cs' : ι → GCx A} (f : ∀ v, GHom (Cs v) (Cs' v)) (i : ℤ)
    (v : ι) :
    LinearMap.proj v ∘ₗ (piBaseChangeEquiv B Cs' i).toLinearMap ∘ₗ
        ((piMap f).f i i rfl).baseChange B =
      ((f v).f i i rfl).baseChange B ∘ₗ LinearMap.proj v ∘ₗ
        (piBaseChangeEquiv B Cs i).toLinearMap :=
  TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl

/-- The comparison commutes with the restriction maps `res_S`. -/
theorem localSumBaseChangeHom_res (Δ : LocalConditions A GS Gv loc M) :
    ∀ i j (h : i = j) (a : (selDataBaseChange B (selData A GS Gv loc M Δ)).G.X i),
      (localSumBaseChangeHom A B GS Gv loc M).f j j rfl
          ((selDataBaseChange B (selData A GS Gv loc M Δ)).res.f i j h a) =
        (selData B GS Gv loc (BCoef A B M) (residualConditions A B GS Gv loc M Δ)).res.f i j h
          ((natCochainsBaseChangeHom A B GS M).f i i rfl a) := by
  intro i j h a
  subst h
  refine funext fun v => ?_
  have h1 := LinearMap.congr_fun (piBaseChangeEquiv_piLift A B
    (fun v => natHom (resCochains (k := A) (M := M) (loc v))) i v) a
  change (localBaseChangeHom A B GS Gv loc M v).f i i rfl
      ((LinearMap.proj v ∘ₗ (piBaseChangeEquiv B (localCx A GS Gv loc M) i).toLinearMap ∘ₗ
        ((piLift fun v => natHom (resCochains (k := A) (M := M) (loc v))).f i i rfl).baseChange
          B) a) = _
  rw [h1]
  exact natBaseChangeF_res A B (loc v) M i a

omit [CompactSpace GS] in
/-- The comparison commutes with the local-condition maps. -/
theorem localSumBaseChangeHom_ι (Δ : LocalConditions A GS Gv loc M) :
    ∀ i j (h : i = j) (u : (selDataBaseChange B (selData A GS Gv loc M Δ)).U.X i),
      (localSumBaseChangeHom A B GS Gv loc M).f j j rfl
          ((selDataBaseChange B (selData A GS Gv loc M Δ)).ι.f i j h u) =
        (selData B GS Gv loc (BCoef A B M) (residualConditions A B GS Gv loc M Δ)).ι.f i j h
          ((piBaseChangeHom B Δ.U).f i i rfl u) := by
  intro i j h u
  subst h
  refine funext fun v => ?_
  have h1 := LinearMap.congr_fun (piBaseChangeEquiv_piMap A B Δ.i i v) u
  change (localBaseChangeHom A B GS Gv loc M v).f i i rfl
      ((LinearMap.proj v ∘ₗ (piBaseChangeEquiv B (localCx A GS Gv loc M) i).toLinearMap ∘ₗ
        ((piMap Δ.i).f i i rfl).baseChange B) u) = _
  rw [h1]
  rfl

/-- **The base-change comparison of Selmer complexes**: the chain map
`B ⊗_A C_U(G_S, M) → C_{B ⊗ U}(G_S, B ⊗_A M)`, `b ⊗ (a, u, x) ↦ (b ⊗ a, b ⊗ u, b ⊗ x)` read
through `B ⊗_A C^•_cont(−, M) ≅ C^•_cont(−, B ⊗_A M)`, onto the genuine Selmer complex of the
base-changed module with the residual local conditions. -/
def residualSelmerHom (Δ : LocalConditions A GS Gv loc M) :
    GHom (gcxBaseChange B (selCx (selData A GS Gv loc M Δ)))
      (selCx (selData B GS Gv loc (BCoef A B M) (residualConditions A B GS Gv loc M Δ))) :=
  ghomComp (selBaseChangeHom B (selData A GS Gv loc M Δ))
    (selCxMap (D₁ := selDataBaseChange B (selData A GS Gv loc M Δ))
      (D₂ := selData B GS Gv loc (BCoef A B M) (residualConditions A B GS Gv loc M Δ))
      (natCochainsBaseChangeHom A B GS M) (piBaseChangeHom B Δ.U)
      (localSumBaseChangeHom A B GS Gv loc M) (localSumBaseChangeHom_res A B GS Gv loc M Δ)
      (localSumBaseChangeHom_ι A B GS Gv loc M Δ))

theorem residualSelmerHom_bijective (Δ : LocalConditions A GS Gv loc M) (n : ℤ) :
    Function.Bijective ((residualSelmerHom A B GS Gv loc M Δ).f n n rfl) :=
  ghomComp_bijective _ _ (selBaseChangeHom_bijective B _)
    (selCxMap_bijective _ _ _ _ _ (natCochainsBaseChangeHom_bijective A B GS M)
      (piBaseChangeHom_bijective B Δ.U)
      (ghomComp_bijective _ _ (piBaseChangeHom_bijective B _)
        (piMap_bijective _ fun v => natCochainsBaseChangeHomOf_bijective A B (Gv v)
          (ResMod (loc v) M) _ _))) n

/-- **`B ⊗_A C_U(G_S, M) ≅ C_{B ⊗ U}(G_S, B ⊗_A M)`** as cochain complexes. -/
def residualSelmerIso (Δ : LocalConditions A GS Gv loc M) :
    (gcxBaseChange B (selCx (selData A GS Gv loc M Δ))).toCC ≅
      (selCx (selData B GS Gv loc (BCoef A B M) (residualConditions A B GS Gv loc M Δ))).toCC :=
  haveI := isIso_toCC_of_bijective _ (residualSelmerHom_bijective A B GS Gv loc M Δ)
  asIso (GHom.toCC (residualSelmerHom A B GS Gv loc M Δ))

end ResidualSelmer

/-! ### Cocycle conditions (the Kummer conditions) -/

section Cocycle

open ZInQ.Manuscript.RC.CoefModules

/-- **A module with a finite submodule and a finite quotient is finite.** -/
theorem finite_of_finite_submodule {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (W : Submodule R V) (hW : Finite W) (hQ : Finite (V ⧸ W)) : Finite V := by
  let S : ShortComplex (ModuleCat.{0} R) :=
    ShortComplex.mk (ModuleCat.ofHom W.subtype) (ModuleCat.ofHom W.mkQ) (by
      ext x
      exact (Submodule.Quotient.mk_eq_zero W).2 x.2)
  have hS : S.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero W).1 hx⟩, rfl⟩
  exact finite_of_exact hS hW hQ

variable {A : Type} [CommRing A] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulCommClass G A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
/-- The continuous `0`-cochains with finite coefficients are finite (`G⁰` is a point). -/
theorem finite_contCochain_zero [Finite M] : Finite (contCochain A G M 0) := by
  have h : Finite ((Fin 0 → G) → M) := Finite.of_injective (fun f : (Fin 0 → G) → M => f default)
    (fun f f' h => funext fun x => by rw [Subsingleton.elim x default]; exact h)
  have : Finite ((groupCohomology.inhomogeneousCochains (rep A G M)).X 0) := h
  exact Subtype.finite

/-- The elements of `Z ⊔ B¹` are cocycles. -/
theorem contD_one_eq_zero_of_mem_sup (Z : Submodule A (contCochain A G M 1))
    (hZ : ∀ z ∈ Z, contD A G M 1 z = 0) (x : contCochain A G M 1) (hx : x ∈ Z ⊔ contB1 A G M) :
    contD A G M 1 x = 0 := by
  obtain ⟨z, hz, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hb
  rw [map_add, hZ z hz, contD_contD 0 c, add_zero]

/-- **The continuous `1`-cocycles with finite coefficients are finite when `H¹(G, M)` is**: the
coboundaries are the image of the finite module of `0`-cochains, and the cocycles modulo the
coboundaries are `H¹(G, M)`. -/
theorem finite_cocycles_one [Finite M]
    (hH1 : Finite (subquot (LinearMap.range (contD A G M 0)) (LinearMap.ker (contD A G M 1)))) :
    Finite (LinearMap.ker (contD A G M 1)) := by
  have := finite_contCochain_zero (A := A) (G := G) (M := M)
  have hB : Finite ↥(LinearMap.range (contD A G M 0)) :=
    Finite.of_surjective _ (LinearMap.surjective_rangeRestrict (contD A G M 0))
  have hW : Finite ↥((LinearMap.range (contD A G M 0)).comap
      (LinearMap.ker (contD A G M 1)).subtype) :=
    Finite.of_injective
      (fun w => (⟨(w : LinearMap.ker (contD A G M 1)).1, w.2⟩ :
        ↥(LinearMap.range (contD A G M 0))))
      (fun w w' h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  exact finite_of_finite_submodule _ hW hH1

/-- **The degree-one term `Z ⊔ B¹` of a cocycle condition is finite** for finite coefficients and
finite `H¹(G, M)`: it consists of cocycles. -/
theorem finite_cocycleCondition_one [Finite M] (Z : Submodule A (contCochain A G M 1))
    (hZ : ∀ z ∈ Z, contD A G M 1 z = 0)
    (hH1 : Finite (subquot (LinearMap.range (contD A G M 0)) (LinearMap.ker (contD A G M 1)))) :
    Finite ↥(Z ⊔ contB1 A G M) := by
  have := finite_cocycles_one hH1
  exact Finite.of_injective
    (fun x : ↥(Z ⊔ contB1 A G M) => (⟨x.1, contD_one_eq_zero_of_mem_sup Z hZ x.1 x.2⟩ :
      LinearMap.ker (contD A G M 1)))
    (fun x x' h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h')

/-- **A cocycle condition has finite terms** for finite coefficients and finite `H¹(G, M)`. -/
theorem finite_cocycleCondition_X [Finite M] (Z : Submodule A (contCochain A G M 1))
    (hZ : ∀ z ∈ Z, contD A G M 1 z = 0)
    (hH1 : Finite (subquot (LinearMap.range (contD A G M 0)) (LinearMap.ker (contD A G M 1)))) :
    ∀ n : ℤ, Finite ((cocycleCondition Z hZ).X n)
  | Int.ofNat 0 => by
    have h := finite_contCochain_zero (A := A) (G := G) (M := M)
    have : Finite ((contCochains A G M).X 0) := h
    exact Subtype.finite
  | Int.ofNat 1 => finite_cocycleCondition_one Z hZ hH1
  | Int.ofNat (_ + 2) => by
    change Finite ↥(⊥ : Submodule A (contCochain A G M _))
    exact Finite.of_subsingleton
  | Int.negSucc _ => inferInstanceAs (Finite PUnit)

/-- `H¹` of the local complex in the form of cocycles modulo coboundaries. -/
theorem finite_subquot_one_of_homology
    (h : Finite ((natCx (contCochains A G M)).toCC.homology 1)) :
    Finite (subquot (LinearMap.range (contD A G M 0)) (LinearMap.ker (contD A G M 1))) :=
  (finite_gcx_homology_iff (natCx (contCochains A G M)) 1).1 h

/-- **The cocycle conditions (in particular the Kummer conditions) have finite residual
cohomology** over a finite local ring, for finite coefficients with finite `H¹(G, M)`. -/
theorem residualCohomologyFinite_cocycleCondition [IsLocalRing A] [Finite A] [Finite M]
    (Z : Submodule A (contCochain A G M 1)) (hZ : ∀ z ∈ Z, contD A G M 1 z = 0)
    (h : Finite ((natCx (contCochains A G M)).toCC.homology 1)) :
    ResidualCohomologyFinite (cocycleCondition Z hZ) :=
  residualCohomologyFinite_of_finite_X _
    (finite_cocycleCondition_X Z hZ (finite_subquot_one_of_homology h))

end Cocycle

/-! ### The genuine Galois Selmer complexes with finite coefficients -/

section Galois

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  {A : Type} [CommRing A] [IsLocalRing A] [Finite A]
  (M : Type) [AddCommGroup M] [Module A M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) A M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] [Finite M]

omit [Finite A] in
/-- The algebra map of a local ring onto its residue field is surjective. -/
theorem algebraMap_residueField_surjective :
    Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) :=
  IsLocalRing.residue_surjective

omit [NumberField K] [Finite A] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M] in
/-- The primes dividing the order of `k ⊗_A M` divide the order of `M` (`k ⊗_A M` is a quotient of
`M`), so they lie in `S` when those of `#M` do. -/
theorem residue_card_primes_mem
    (hM : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ((Nat.card (BCoef A (IsLocalRing.ResidueField A) M) : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v ∈ S := by
  obtain ⟨c, hc⟩ := card_bcoef_dvd A (IsLocalRing.ResidueField A) M
    algebraMap_residueField_surjective
  apply hM v
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hv

/-- **The residual cohomology of the actual global complex `C^•_cont(G_{K,S}, M)` is finite**:
`k ⊗_A C^•_cont(G_{K,S}, M) ≅ C^•_cont(G_{K,S}, k ⊗_A M)`, and `k ⊗_A M` is a finite discrete
module whose order divides `#M`, so Milne I, Corollary 4.15 applies to it. -/
theorem globalCx_residualCohomologyFinite (hglob : MilneGlobalFiniteness) (hS : S.Finite)
    (hM : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ResidualCohomologyFinite (globalCx A (GKS K S) M) := by
  have := finite_residueField (A := A)
  have : Finite (BCoef A (IsLocalRing.ResidueField A) M) := finite_bcoef _ _ _
  rw [residualCohomologyFinite_iff_finite]
  intro n
  exact (finite_homology_iff_of_bijective _
    (natCochainsBaseChangeHom_bijective A (IsLocalRing.ResidueField A) (GKS K S) M) n).2
    (hglob K S hS (IsLocalRing.ResidueField A) (BCoef A (IsLocalRing.ResidueField A) M)
      inferInstance (residue_card_primes_mem K S M hM) n)

/-- **The residual cohomology of the actual local complex `C^•_cont(G_{K_v}, M)` is finite**
(Milne I, Theorem 2.1, for the finite discrete module `k ⊗_A M`). -/
theorem localCx_residualCohomologyFinite (hloc : MilneLocalFiniteness) (v : Places K S) :
    ResidualCohomologyFinite
      (localCx A (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M v) := by
  have := finite_residueField (A := A)
  have : Finite (ResMod (locMap K S v.1) M) := inferInstanceAs (Finite M)
  have : Finite (BCoef A (IsLocalRing.ResidueField A) (ResMod (locMap K S v.1) M)) :=
    finite_bcoef _ _ _
  rw [residualCohomologyFinite_iff_finite]
  intro n
  exact (finite_homology_iff_of_bijective _
    (natCochainsBaseChangeHom_bijective A (IsLocalRing.ResidueField A) (Gloc K v.1)
      (ResMod (locMap K S v.1) M)) n).2
    (hloc K v.1 (IsLocalRing.ResidueField A)
      (BCoef A (IsLocalRing.ResidueField A) (ResMod (locMap K S v.1) M)) inferInstance n)

omit [IsLocalRing A] [Finite A] [Finite M] in
/-- **The base change of the actual Selmer complex is the actual Selmer complex of the base-changed
module** with the residual local conditions: `B ⊗_A C_U(G_{K,S}, M) ≅ C_{B ⊗ U}(G_{K,S}, B ⊗_A M)`
for any `A`-algebra `B` (in the application the residue field of `A`). -/
def residualGaloisSelmerIso (B : Type) [CommRing B] [Algebra A B] [Fintype (Places K S)]
    [DecidableEq (Places K S)] (Δ : GaloisLocalConditions K S A M) :
    (gcxBaseChange B (selCx (galoisSelData K S A M Δ))).toCC ≅
      (selCx (galoisSelData K S B (BCoef A B M)
        (residualConditions A B (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) M Δ))).toCC :=
  residualSelmerIso A B (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M Δ

/-- **The residual cohomology of the actual Selmer complex is finite** for a finite local
coefficient ring `A` and a finite discrete module `M`, for a finite `S` containing the primes
dividing `#M`, when the residual cohomology of the local conditions is finite: the residual
Selmer complex is the Selmer complex of the finite discrete module `k ⊗_A M` with the residual
local conditions (`residualSelmerHom`), whose cohomology is finite by the finiteness prints
(`galoisSelmerCohomologyFinite_of_prints`). -/
theorem galoisSelmer_residualCohomologyFinite (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hS : S.Finite)
    (hM : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Δ : GaloisLocalConditions K S A M) (hΔ : ∀ v, ResidualCohomologyFinite (Δ.U v)) :
    ResidualCohomologyFinite (selCx (galoisSelData K S A M Δ)) := by
  classical
  have : Fintype (Places K S) := hS.fintype
  have := finite_residueField (A := A)
  have : Finite (BCoef A (IsLocalRing.ResidueField A) M) := finite_bcoef _ _ _
  rw [residualCohomologyFinite_iff_finite]
  intro n
  refine (finite_homology_iff_of_bijective _
    (residualSelmerHom_bijective A (IsLocalRing.ResidueField A) (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M Δ) n).2 ?_
  exact galoisSelmerCohomologyFinite_of_prints K S (IsLocalRing.ResidueField A)
    (BCoef A (IsLocalRing.ResidueField A) M) hloc hglob hS (residue_card_primes_mem K S M hM)
    (residualConditions A (IsLocalRing.ResidueField A) (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M Δ)
    (fun v m => (residualCohomologyFinite_iff_finite _).1 (hΔ v) m) n

end Galois

/-! ### The actual stage Selmer complexes -/

section Stage

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (α : GKS K S →* (Acoef i)ˣ)
  [IsOpenKer α]

/-- **The residual cohomology of the actual stage Selmer complexes is finite**: for the actual
coefficient module `M_i = (E[2^i] ⊗ A_i)(α)` over `A_i = (ℤ/2^i)[t]/t^i`, a finite `S` containing
the primes above `2`, and local conditions whose residual cohomology is finite, every residual
cohomology group `H^n(k ⊗_{A_i} C_U(M_i))` is finite over the residue field `k` (from the
finiteness prints Milne I, Theorem 2.1 and Corollary 4.15, applied to the finite discrete module
`k ⊗_{A_i} M_i`). -/
theorem stageSelmer_residualCohomologyFinite (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Δ : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i α))
    (hΔ : ∀ v, ResidualCohomologyFinite (Δ.U v)) :
    ResidualCohomologyFinite (selCx (galoisSelData K S (Acoef i) (Mcoef K S W i α) Δ)) := by
  obtain ⟨k, hk⟩ := card_mcoef_eq_two_pow W i α
  refine galoisSelmer_residualCohomologyFinite K S (Mcoef K S W i α) hloc hglob hSfin ?_ Δ hΔ
  intro v hv
  rw [hk, Nat.cast_pow, Nat.cast_ofNat] at hv
  exact h2 v (v.isPrime.mem_of_pow_mem k hv)

/-- **The strict (compactly supported) stage Selmer complex has finite residual cohomology**:
the zero condition at every place of `S`. -/
theorem stageStrictSelmer_residualCohomologyFinite (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ResidualCohomologyFinite (selCx (actualSelData_zero W i α)) :=
  stageSelmer_residualCohomologyFinite W i α hloc hglob hSfin h2 _
    fun _ => residualCohomologyFinite_zeroCx

/-- **The relaxed stage Selmer complex has finite residual cohomology**: the full condition
`C^•_cont(G_{K_v}, M_i)` at every place of `S`. -/
theorem stageRelaxedSelmer_residualCohomologyFinite (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ResidualCohomologyFinite (selCx (actualSelData_full W i α)) :=
  stageSelmer_residualCohomologyFinite W i α hloc hglob hSfin h2 _
    fun v => localCx_residualCohomologyFinite K S (Mcoef K S W i α) hloc v

/-- **The stage Selmer complexes with the Kummer conditions have finite residual cohomology**:
at every `v ∈ S` the Kummer condition `[C⁰_cont(G_{K_v}, M_i) → Z_v ⊔ B¹]` attached to an
elliptic curve `B_v` over `K_v` and an equivariant map `ι_v : B_v[m] → M_i` has finite terms, since
`H¹(K_v, M_i)` is finite (Milne I, Theorem 2.1). -/
theorem stageKummerSelmer_residualCohomologyFinite (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
    (B : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (m : ℕ) [NeZero m]
    (ι : ∀ v : Places K S,
      TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) (Mcoef K S W i α))
    (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι v (σ • t) = σ • ι v t) :
    ResidualCohomologyFinite (selCx (galoisSelData K S (Acoef i) (Mcoef K S W i α)
      (kummerGaloisLocalConditions K S B m (Acoef i) (Mcoef K S W i α) ι hι))) :=
  stageSelmer_residualCohomologyFinite W i α hloc hglob hSfin h2 _ fun v => by
    have : Finite (ResMod (locMap K S v.1) (Mcoef K S W i α)) :=
      inferInstanceAs (Finite (Mcoef K S W i α))
    exact residualCohomologyFinite_cocycleCondition _ _
      (hloc K v.1 (Acoef i) (ResMod (locMap K S v.1) (Mcoef K S W i α)) inferInstance 1)

end Stage

/-! ### The actual conditions: old conditions at `S₀`, unramified conditions at `S − S₀` -/

section Actual

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (frobCx rel01 frob eUr)

/-- **The unramified complex `[W --(Φ−1)--> W]` has finite terms** for a finite module `W`. -/
theorem finite_frobCx_X {k : Type} [Ring k] {W : Type} [AddCommGroup W] [Module k W] [Finite W]
    (Φ : W →ₗ[k] W) (n : ℤ) : Finite ((frobCx Φ).X n) := by
  change Finite ((HomologicalComplex.double (ModuleCat.ofHom (Φ - 1)) rel01).X n)
  by_cases h0 : n = 0
  · subst h0
    exact Finite.of_equiv _
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Φ - 1)) rel01).toLinearEquiv.symm.toEquiv
  · by_cases h1 : n = 1
    · subst h1
      exact Finite.of_equiv _ (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Φ - 1)) rel01
        (by decide)).toLinearEquiv.symm.toEquiv
    · have := ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_double_X (ModuleCat.ofHom (Φ - 1)) rel01 n h0 h1)
      exact Finite.of_subsingleton

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S)

/-- **The unramified condition has finite residual cohomology**: its complex
`[M₀ --(Φ_w−1)--> M₀]` has finite terms. -/
theorem urAt_residualCohomologyFinite {k : Type} [CommRing k] [IsLocalRing k] [Finite k]
    [TopologicalSpace k] [DiscreteTopology k] (M₀ : Type) [AddCommGroup M₀] [Module k M₀]
    [DistribMulAction (GKS K S₀) M₀] [SMulCommClass (GKS K S₀) k M₀] [TopologicalSpace M₀]
    [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀] (w : Places K S)
    (hw : w.1 ∉ S₀) : ResidualCohomologyFinite (urAt hS k M₀ w hw).U :=
  residualCohomologyFinite_of_finite_X _ fun n =>
    finite_frobCx_X (frob (eUr K w.1) (urRep k M₀ (newPlace w hw))) n

variable (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (α : GKS K S₀ →* (Acoef i)ˣ)
  [IsOpenKer α]

/-- **The actual stage Selmer complexes with the old conditions at `S₀` and the unramified
conditions at `S − S₀` have finite residual cohomology**, for old conditions with finite residual
cohomology. -/
theorem actualStageSelmer_residualCohomologyFinite (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v h, ResidualCohomologyFinite (c v h).U) :
    ResidualCohomologyFinite (selCx (actualSelData hS W i α c)) := by
  let _ : TopologicalSpace (Acoef i) := acoefTop i
  have _ : DiscreteTopology (Acoef i) := acoefTop_discrete i
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  obtain ⟨k, hk⟩ := card_mcoef_eq_two_pow W i α
  refine galoisSelmer_residualCohomologyFinite K S (MinS hS W i α) hloc hglob hSfin ?_
    (actualConditions hS W i α c) ?_
  · intro v hv
    have hk' : Nat.card (MinS hS W i α) = 2 ^ k := hk
    rw [hk', Nat.cast_pow, Nat.cast_ofNat] at hv
    exact h2 v (v.isPrime.mem_of_pow_mem k hv)
  · intro v
    change ResidualCohomologyFinite (urOutside hS (Acoef i) (Mcoef K S₀ W i α) c v).U
    unfold urOutside
    split_ifs with h
    · exact hc v h
    · exact urAt_residualCohomologyFinite hS (Mcoef K S₀ W i α) v h

/-- The actual stage Selmer complex with the full conditions at the old places `S₀` and the
unramified conditions at `S − S₀` has finite residual cohomology. -/
theorem actualStageSelmer_full_residualCohomologyFinite (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ResidualCohomologyFinite (selCx (actualSelData hS W i α
      (fun v _ => fullAt K S (Acoef i) (MinS hS W i α) v))) := by
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  exact actualStageSelmer_residualCohomologyFinite hS W i α hloc hglob hSfin h2 _
    fun v _ => localCx_residualCohomologyFinite K S (MinS hS W i α) hloc v

/-- The actual stage Selmer complex with the zero conditions at the old places `S₀` and the
unramified conditions at `S − S₀` has finite residual cohomology. -/
theorem actualStageSelmer_zero_residualCohomologyFinite (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ResidualCohomologyFinite (selCx (actualSelData hS W i α
      (fun v _ => zeroAt K S (Acoef i) (MinS hS W i α) v))) :=
  actualStageSelmer_residualCohomologyFinite hS W i α hloc hglob hSfin h2 _
    fun _ _ => residualCohomologyFinite_zeroCx

end Actual

end ZInQ.Contrib.RC53Assist.ResidualFiniteness
