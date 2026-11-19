import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel

/-!
# Lane RC31, round 3, part 1: graded finite free models (Elliot's construction)

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451): "Let `A` be an Artin
local ring with nilpotent maximal ideal, and let a complex of flat `A`-modules have finite bounded
residual cohomology. … [It has] a bounded finite free model with actual inclusion, projection
and contraction homotopy."

Elliot's proof (tex 4408–4437), followed step by step:

1. split the residual complex `k ⊗_A X` into cohomology and disks, degree by degree
   (`exists_residual_graded_disk_basis`, tex 4416–4418);
2. lift the graded bases (flatness and nilpotence, `FlatFree`), assemble them into a homogeneous
   basis of the total module `⨁ₙ Xⁿ` indexed by `((ιS ⊕ ιH) ⊕ ιS)`, so that `FiniteFreeModel`'s
   lifted disk data `d₀, h₀, i₀, p₀` apply; `ε = d − d₀` has entries in `𝔪` and `d₀, h₀, i₀, p₀`
   have degrees `1, −1, 0, 0` (`exists_graded_lifted_disk_basis`, tex 4416–4427);
3. perturb: `d_C = p₀ε(1+h₀ε)⁻¹i₀`, `i = (1+h₀ε)⁻¹i₀`, `p = p₀(1+εh₀)⁻¹`, `h = h₀(1+εh₀)⁻¹`
   (`perturbation_lemma_artin`, `perturbed_degrees_artin`; `exists_elliotGradedRetract`,
   tex 4428–4437);
4. cut the homogeneous total data into degrees (`gradedModelOfTotal`): the model module in degree
   `n` is `A^(rank n)`, `rank n = dim_k Hⁿ(k ⊗_A X)`, and every map is the degreewise component of
   Elliot's map.

Main results: `exists_gradedModel`, `exists_gradedModel_bounded`.

DEPARTURE (representation): the perturbation is carried out on the total module `⨁ₙ Xⁿ` with the
total model `A^(Σₙ Fin (rank n))`, and degreewise components are extracted afterwards; homogeneity
of all four perturbed maps (`perturbed_degrees_artin`) makes this equal to the degreewise
construction. Disk targets in degree `n` are indexed by disk sources `⟨m, s⟩` with `m + 1 = n`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory TensorProduct IsLocalRing Module
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

section Generic

/-- The basis `DFinsupp.basis b` of a direct sum sends the index `⟨i, j⟩` to the single vector
`b i j` in summand `i` (used for the lifted graded basis, tex 4417–4418). Kind: PROVED. -/
theorem dfinsupp_basis_apply_sigma {ι R : Type*} [DecidableEq ι] [Semiring R] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {η : ι → Type*}
    (b : ∀ i, Basis (η i) R (M i)) (x : Σ i, η i) :
    DFinsupp.basis b x = DFinsupp.single x.1 (b x.1 x.2) := by
  rw [Basis.apply_eq_iff]
  simp [DFinsupp.basis, sigmaFinsuppLequivDFinsupp]
  rw [Equiv.symm_apply_eq, sigmaFinsuppEquivDFinsupp_single]

/-- A linear map sends everything into a submodule `Q` as soon as it sends every basis vector into
`Q`. Auxiliary (basis induction, tex 4417–4420). Kind: PROVED. -/
theorem map_mem_of_basis_apply {A : Type*} [CommRing A] {ι M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (B : Basis ι A M) (f : M →ₗ[A] N) (Q : Submodule A N)
    (hf : ∀ j, f (B j) ∈ Q) (x : M) : f x ∈ Q := by
  have h : Submodule.span A (Set.range B) ≤ Q.comap f :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hf j)
  rw [B.span_eq] at h
  exact h Submodule.mem_top

/-- A map of degree `k` sends degree `a` into degree `b` whenever `a + k = b`. Auxiliary for the
degreewise components (tex 4417–4436). Kind: PROVED. -/
theorem HasDegree.mem_at {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {Mdeg : ℤ → Submodule A M} {Ndeg : ℤ → Submodule A N} {k : ℤ}
    {f : M →ₗ[A] N} (hf : HasDegree Mdeg Ndeg k f) {a b : ℤ} {x : M} (hx : x ∈ Mdeg a)
    (hab : a + k = b) : f x ∈ Ndeg b :=
  hab ▸ hf a x hx

end Generic

section Total

variable {A : Type} [CommRing A]

/-- The total module `⨁ₙ Xⁿ` of a relation-indexed complex: Elliot's graded decomposition is
built and perturbed here and then cut back into degrees (tex 4417–4436). Kind: definition. -/
abbrev gTotal (X : GCx A) : Type := DirectSum ℤ (fun n => X.X n)

/-- The inclusion of the degree-`n` summand `Xⁿ` into the total module.
(tex 4417–4436) Kind: definition. -/
abbrev gTotalOf (X : GCx A) (n : ℤ) : X.X n →ₗ[A] gTotal X :=
  DirectSum.lof A ℤ (fun n => X.X n) n

/-- The degree-`n` component `⨁ₘ Xᵐ → Xⁿ` of the total module. (tex 4417–4436) Kind: definition. -/
abbrev gTotalComp (X : GCx A) (n : ℤ) : gTotal X →ₗ[A] X.X n :=
  DirectSum.component A ℤ (fun n => X.X n) n

/-- The degree-`n` piece of the total module: the image of `Xⁿ` (tex 4417, "graded
decomposition"). Kind: definition. -/
def gTotalDeg (X : GCx A) (n : ℤ) : Submodule A (gTotal X) :=
  LinearMap.range (gTotalOf X n)

/-- The total differential `d` on `⨁ₙ Xⁿ`, of degree `1`, assembled from the differentials of `X`
(tex 4418: "`d = d₀ + ε`"). Kind: definition. -/
def gTotalDiff (X : GCx A) : Module.End A (gTotal X) :=
  DirectSum.toModule A ℤ (gTotal X) fun a => gTotalOf X (a + 1) ∘ₗ X.d a (a + 1) rfl

/-- The total differential on the degree-`a` summand is the differential `Xᵃ → Xᵇ`, `a + 1 = b`.
(tex 4418) Kind: PROVED. -/
theorem gTotalDiff_of (X : GCx A) (a b : ℤ) (h : a + 1 = b) (x : X.X a) :
    gTotalDiff X (gTotalOf X a x) = gTotalOf X b (X.d a b h x) := by
  subst h
  simp [gTotalDiff, DirectSum.toModule_lof]

/-- `d² = 0` for the total differential (from `X.d_d`; tex 4437 uses `d² = 0`). Kind: PROVED. -/
theorem gTotalDiff_mul_self (X : GCx A) : gTotalDiff X * gTotalDiff X = 0 := by
  refine DirectSum.linearMap_ext _ fun a => LinearMap.ext fun x => ?_
  change gTotalDiff X (gTotalDiff X (gTotalOf X a x)) = 0
  rw [gTotalDiff_of X a (a + 1) rfl, gTotalDiff_of X (a + 1) (a + 1 + 1) rfl, X.d_d, map_zero]

/-- The degree-`n` component of the degree-`n` summand is the identity.
(tex 4417–4436) Kind: PROVED. -/
theorem gTotalComp_of (X : GCx A) (n : ℤ) (x : X.X n) : gTotalComp X n (gTotalOf X n x) = x := by
  simp [gTotalComp, gTotalOf]

/-- A homogeneous element of degree `n` is recovered from its degree-`n` component.
(tex 4417–4436) Kind: PROVED. -/
theorem gTotalOf_comp (X : GCx A) {n : ℤ} {y : gTotal X} (hy : y ∈ gTotalDeg X n) :
    gTotalOf X n (gTotalComp X n y) = y := by
  obtain ⟨z, rfl⟩ := hy
  rw [gTotalComp_of]

/-- The inclusion of a summand is injective. (tex 4417–4436) Kind: PROVED. -/
theorem gTotalOf_injective (X : GCx A) (n : ℤ) {x y : X.X n} (h : gTotalOf X n x = gTotalOf X n y) :
    x = y := by
  rw [← gTotalComp_of X n x, h, gTotalComp_of]

/-- The degree-`n` summand lies in degree `n`. (tex 4417–4436) Kind: PROVED. -/
theorem gTotalOf_mem (X : GCx A) (n : ℤ) (x : X.X n) : gTotalOf X n x ∈ gTotalDeg X n := ⟨x, rfl⟩

/-- The total differential has degree `1`. (tex 4418) Kind: PROVED. -/
theorem gTotalDiff_hasDegree (X : GCx A) :
    HasDegree (gTotalDeg X) (gTotalDeg X) 1 (gTotalDiff X) := by
  rintro n _ ⟨z, rfl⟩
  exact ⟨_, (gTotalDiff_of X n (n + 1) rfl z).symm⟩

end Total

section ModelSide

variable {A : Type} [CommRing A]

/-- The cohomology index set `Σₙ Fin (rank n)` of the model (tex 4417–4418: lifted bases of the
cohomology summands, degree `n` of size `rank n`). Kind: definition. -/
abbrev gModelIndex (rank : ℤ → ℕ) : Type := Σ n, Fin (rank n)

/-- The degree-`n` piece of the total model `A^(Σₙ Fin (rank n))`: the vectors supported in
degree `n`. (tex 4417–4436) Kind: definition. -/
def gModelDeg (rank : ℤ → ℕ) (n : ℤ) : Submodule A (gModelIndex rank →₀ A) :=
  Finsupp.supported A A {j : gModelIndex rank | j.1 = n}

/-- The inclusion of the degree-`n` model module `A^(rank n)` into the total model.
(tex 4417–4436) Kind: definition. -/
def gModelOf (rank : ℤ → ℕ) (n : ℤ) : (Fin (rank n) → A) →ₗ[A] (gModelIndex rank →₀ A) :=
  Finsupp.lmapDomain A A (Sigma.mk n) ∘ₗ
    (Finsupp.linearEquivFunOnFinite A A (Fin (rank n))).symm.toLinearMap

/-- The degree-`n` component `A^(Σₘ Fin (rank m)) → A^(rank n)` of the total model.
(tex 4417–4436) Kind: definition. -/
def gModelComp (rank : ℤ → ℕ) (n : ℤ) : (gModelIndex rank →₀ A) →ₗ[A] (Fin (rank n) → A) :=
  LinearMap.pi fun r => Finsupp.lapply ⟨n, r⟩

/-- The degree-`n` component of the degree-`n` inclusion is the identity.
(tex 4417–4436) Kind: PROVED. -/
theorem gModelComp_of (rank : ℤ → ℕ) (n : ℤ) (y : Fin (rank n) → A) :
    gModelComp rank n (gModelOf rank n y) = y := by
  funext r
  simp [gModelComp, gModelOf, Finsupp.mapDomain_apply_of_injective sigma_mk_injective]

/-- The degree-`n` model module lies in degree `n`. (tex 4417–4436) Kind: PROVED. -/
theorem gModelOf_mem (rank : ℤ → ℕ) (n : ℤ) (y : Fin (rank n) → A) :
    gModelOf rank n y ∈ gModelDeg rank n := by
  rw [gModelDeg, Finsupp.mem_supported]
  intro j hj
  obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hj)
  rfl

/-- An element of the total model of degree `n` is recovered from its degree-`n` component.
(tex 4417–4436) Kind: PROVED. -/
theorem gModelOf_comp (rank : ℤ → ℕ) {n : ℤ} {y : gModelIndex rank →₀ A}
    (hy : y ∈ gModelDeg rank n) : gModelOf rank n (gModelComp rank n y) = y := by
  ext ⟨m, t⟩
  by_cases hm : m = n
  · subst hm
    simp [gModelComp, gModelOf, Finsupp.mapDomain_apply_of_injective sigma_mk_injective]
  · have h1 : (⟨m, t⟩ : gModelIndex rank) ∉ Set.range (Sigma.mk n) := by
      rintro ⟨r, hr⟩
      exact hm (congrArg Sigma.fst hr).symm
    rw [gModelOf, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_of_notMem_range _ _ h1]
    exact ((Finsupp.mem_supported' _ _).1 hy _ hm).symm

end ModelSide

section Assemble

variable {A : Type} [CommRing A]

/-- Total normalized deformation retract data of `⨁ₙ Xⁿ` onto the total model
`A^(Σₙ Fin (rank n))` whose maps are homogeneous: `d_C, i, p, h` of degrees `1, 0, 0, −1`
(tex 4428–4437 together with the graded refinement of tex 4417–4436). Kind: definition
(hypothesis bundle). -/
structure GradedTotalRetract (X : GCx A) (rank : ℤ → ℕ) (dC : Module.End A (gModelIndex rank →₀ A))
    (i : (gModelIndex rank →₀ A) →ₗ[A] gTotal X) (p : gTotal X →ₗ[A] (gModelIndex rank →₀ A))
    (h : Module.End A (gTotal X)) : Prop where
  /-- Normalized deformation retract data on the total module. -/
  retract : IsNormalizedDeformationRetract (gTotalDiff X) dC i p h
  /-- The model differential has degree `1`. -/
  deg_dC : HasDegree (gModelDeg rank) (gModelDeg rank) 1 dC
  /-- The inclusion has degree `0`. -/
  deg_i : HasDegree (gModelDeg rank) (gTotalDeg X) 0 i
  /-- The projection has degree `0`. -/
  deg_p : HasDegree (gTotalDeg X) (gModelDeg rank) 0 p
  /-- The homotopy has degree `−1`. -/
  deg_h : HasDegree (gTotalDeg X) (gTotalDeg X) (-1) h

/-- The degree-`(a → b)` component of a total model differential, as a matrix
`Fin (rank b) × Fin (rank a)` (tex 4431: the model differential `d_C`, degreewise).
Kind: definition. -/
def gModelMatrix (rank : ℤ → ℕ) (dC : Module.End A (gModelIndex rank →₀ A)) (a b : ℤ) :
    Matrix (Fin (rank b)) (Fin (rank a)) A :=
  LinearMap.toMatrix' (gModelComp rank b ∘ₗ dC ∘ₗ gModelOf rank a)

variable {X : GCx A} {rank : ℤ → ℕ} {dC : Module.End A (gModelIndex rank →₀ A)}
  {i : (gModelIndex rank →₀ A) →ₗ[A] gTotal X} {p : gTotal X →ₗ[A] (gModelIndex rank →₀ A)}
  {h : Module.End A (gTotal X)}

/-- The degreewise model matrices square to zero (`d_C² = 0`, degreewise; tex 4437).
Kind: PROVED. -/
theorem gModelMatrix_mul (H : GradedTotalRetract X rank dC i p h) (a b c : ℤ) (hab : a + 1 = b)
    (_hbc : b + 1 = c) : gModelMatrix rank dC b c * gModelMatrix rank dC a b = 0 := by
  rw [gModelMatrix, gModelMatrix, ← LinearMap.toMatrix'_comp]
  have : (gModelComp rank c ∘ₗ dC ∘ₗ gModelOf rank b) ∘ₗ
      (gModelComp rank b ∘ₗ dC ∘ₗ gModelOf rank a) = 0 := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [gModelOf_comp rank (H.deg_dC.mem_at (gModelOf_mem rank a y) hab),
      ← Module.End.mul_apply, H.retract.model_diff_mul_self, LinearMap.zero_apply, map_zero]
  rw [this, map_zero]

/-- **The graded finite free model cut out of homogeneous total retract data** (tex 4428–4437).
Model module `A^(rank n)` in degree `n`; model matrices, inclusion, projection and homotopy
are the degreewise components `π_b ∘ f ∘ ι_a` of the total `d_C, i, p, h`. Homogeneity makes
every identity of `IsNormalizedDeformationRetract` hold degreewise.
Kind: definition (PROVED identities). -/
def gradedModelOfTotal (H : GradedTotalRetract X rank dC i p h) : GradedModel X where
  rank := rank
  dC a b _ := gModelMatrix rank dC a b
  dC_sq a b c hab hbc := gModelMatrix_mul H a b c hab hbc
  retract :=
    { i :=
        { f := fun a b _ => gTotalComp X b ∘ₗ i ∘ₗ gModelOf rank a
          comm := by
            intro a a₁ b b₁ hab h₁ h₂ hb (x : Fin (rank a) → A)
            subst hab h₁ hb
            change gTotalComp X (a + 1) (i (gModelOf rank (a + 1)
                (Matrix.toLin' (gModelMatrix rank dC a (a + 1)) x))) =
              X.d a (a + 1) h₂ (gTotalComp X a (i (gModelOf rank a x)))
            rw [gModelMatrix, Matrix.toLin'_toMatrix']
            simp only [LinearMap.comp_apply]
            rw [gModelOf_comp rank (H.deg_dC.mem_at (gModelOf_mem rank a x) rfl),
              ← LinearMap.comp_apply i dC, ← H.retract.diff_comp_incl, LinearMap.comp_apply,
              ← gTotalOf_comp X (H.deg_i.mem_at (gModelOf_mem rank a x) (add_zero a)),
              gTotalDiff_of X a (a + 1) h₂, gTotalComp_of, gTotalComp_of] }
      p :=
        { f := fun a b _ => gModelComp rank b ∘ₗ p ∘ₗ gTotalOf X a
          comm := by
            intro a a₁ b b₁ hab h₁ h₂ hb (x : X.X a)
            subst hab h₁ hb
            change gModelComp rank (a + 1) (p (gTotalOf X (a + 1) (X.d a (a + 1) rfl x))) =
              Matrix.toLin' (gModelMatrix rank dC a (a + 1))
                (gModelComp rank a (p (gTotalOf X a x)))
            rw [gModelMatrix, Matrix.toLin'_toMatrix', ← gTotalDiff_of X a (a + 1) rfl]
            simp only [LinearMap.comp_apply]
            rw [gModelOf_comp rank (H.deg_p.mem_at (gTotalOf_mem X a x) (add_zero a)),
              ← LinearMap.comp_apply p (gTotalDiff X), H.retract.proj_comp_diff,
              LinearMap.comp_apply] }
      h := fun a b _ => gTotalComp X b ∘ₗ h ∘ₗ gTotalOf X a
      p_i := by
        intro n (y : Fin (rank n) → A)
        change gModelComp rank n (p (gTotalOf X n (gTotalComp X n (i (gModelOf rank n y))))) = y
        rw [gTotalOf_comp X (H.deg_i.mem_at (gModelOf_mem rank n y) (add_zero n)),
          ← LinearMap.comp_apply p i, H.retract.proj_comp_incl, LinearMap.id_apply,
          gModelComp_of]
      homotopy := by
        intro n x
        apply gTotalOf_injective X n
        change gTotalOf X n
            (x - gTotalComp X n (i (gModelOf rank n (gModelComp rank n (p (gTotalOf X n x)))))) =
          gTotalOf X n (X.d (n - 1) n (by omega) (gTotalComp X (n - 1) (h (gTotalOf X n x))) +
            gTotalComp X n (h (gTotalOf X (n + 1) (X.d n (n + 1) rfl x))))
        have hp := H.deg_p.mem_at (gTotalOf_mem X n x) (add_zero n)
        have hD : gTotalDiff X (gTotalOf X n x) ∈ gTotalDeg X (n + 1) :=
          ⟨_, (gTotalDiff_of X n (n + 1) rfl x).symm⟩
        rw [map_sub, map_add, gModelOf_comp rank hp,
          gTotalOf_comp X (H.deg_i.mem_at hp (add_zero n)),
          ← gTotalDiff_of X (n - 1) n (by omega),
          gTotalOf_comp X (H.deg_h.mem_at (gTotalOf_mem X n x) (by omega)),
          ← gTotalDiff_of X n (n + 1) rfl, gTotalOf_comp X (H.deg_h.mem_at hD (by omega))]
        have := LinearMap.congr_fun H.retract.homotopy (gTotalOf X n x)
        simpa only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply,
          LinearMap.add_apply, Module.End.mul_apply] using this
      h_h := by
        intro a b c hab hbc x
        change gTotalComp X c (h (gTotalOf X b (gTotalComp X b (h (gTotalOf X a x))))) = 0
        rw [gTotalOf_comp X (H.deg_h.mem_at (gTotalOf_mem X a x) (by omega)),
          ← Module.End.mul_apply,
          H.retract.homotopy_mul_self, LinearMap.zero_apply, map_zero]
      h_i := by
        intro a b hab (y : Fin (rank a) → A)
        change gTotalComp X b (h (gTotalOf X a (gTotalComp X a (i (gModelOf rank a y))))) = 0
        rw [gTotalOf_comp X (H.deg_i.mem_at (gModelOf_mem rank a y) (add_zero a)),
          ← LinearMap.comp_apply h i, H.retract.homotopy_comp_incl, LinearMap.zero_apply,
          map_zero]
      p_h := by
        intro a b hab x
        change gModelComp rank b (p (gTotalOf X b (gTotalComp X b (h (gTotalOf X a x))))) = 0
        rw [gTotalOf_comp X (H.deg_h.mem_at (gTotalOf_mem X a x) (by omega)),
          ← LinearMap.comp_apply p h, H.retract.proj_comp_homotopy, LinearMap.zero_apply,
          map_zero] }

/-- The rank of `gradedModelOfTotal`. (tex 4428–4437) Kind: PROVED (definitional). -/
theorem gradedModelOfTotal_rank (H : GradedTotalRetract X rank dC i p h) :
    (gradedModelOfTotal H).rank = rank :=
  rfl

/-- The model matrices of `gradedModelOfTotal` are the degree components of the total model
differential (tex 4431). Kind: PROVED (definitional). -/
theorem gradedModelOfTotal_dC (H : GradedTotalRetract X rank dC i p h) (a b : ℤ) (hab : a + 1 = b) :
    (gradedModelOfTotal H).dC a b hab = gModelMatrix rank dC a b :=
  rfl

/-- The inclusion of `gradedModelOfTotal` in degree `a` is the degree component of the total
inclusion (tex 4432). Kind: PROVED (definitional). -/
theorem gradedModelOfTotal_i (H : GradedTotalRetract X rank dC i p h) (a b : ℤ) (hab : a = b)
    (y : Fin (rank a) → A) :
    (gradedModelOfTotal H).retract.i.f a b hab y = gTotalComp X b (i (gModelOf rank a y)) :=
  rfl

/-- The projection of `gradedModelOfTotal` in degree `a` is the degree component of the total
projection (tex 4433). Kind: PROVED (definitional). -/
theorem gradedModelOfTotal_p (H : GradedTotalRetract X rank dC i p h) (a b : ℤ) (hab : a = b)
    (x : X.X a) :
    (gradedModelOfTotal H).retract.p.f a b hab x = gModelComp rank b (p (gTotalOf X a x)) :=
  rfl

/-- The homotopy of `gradedModelOfTotal` from degree `a` to degree `b` is the degree component of
the total homotopy (tex 4434). Kind: PROVED (definitional). -/
theorem gradedModelOfTotal_h (H : GradedTotalRetract X rank dC i p h) (a b : ℤ) (hab : b + 1 = a)
    (x : X.X a) :
    (gradedModelOfTotal H).retract.h a b hab x = gTotalComp X b (h (gTotalOf X a x)) :=
  rfl

end Assemble

section Residual

variable {A : Type} [CommRing A] [IsLocalRing A]

/-- The rank `dim_k Hⁿ(k ⊗_A X)` of the residual cohomology in degree `n` (tex 4392–4394).
Kind: definition. -/
abbrev residualRankAt (X : GCx A) (n : ℤ) : ℕ :=
  Module.finrank (ResidueField A) (residualCohomologyAt X n)

/-- The residual differentials compose to zero (`d² = 0` after base change; tex 4416).
Kind: PROVED. -/
theorem residualDiff_comp_apply (X : GCx A) (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c)
    (y : ResidueField A ⊗[A] X.X a) : residualDiff X b c hbc (residualDiff X a b hab y) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  have : X.d b c hbc ∘ₗ X.d a b hab = 0 := LinearMap.ext (X.d_d a b c hab hbc)
  rw [this, LinearMap.baseChange_zero, LinearMap.zero_apply]

/-- The kernel of a residual differential does not depend on how its target index is written.
(tex 4416) Kind: PROVED. -/
theorem residualDiff_ker_congr (X : GCx A) (a b b' : ℤ) (h : a + 1 = b) (h' : a + 1 = b') :
    LinearMap.ker (residualDiff X a b h) = LinearMap.ker (residualDiff X a b' h') := by
  subst h
  subst h'
  rfl

/-- **One degree of the split residual complex** (tex 4416–4418), linear algebra over a
field: for `δ₀ : V₀ → V`, `δ : V → V₂` with `δ δ₀ = 0`, complements `Sp₀` of `ker δ₀` and
`Sp` of `ker δ` with bases, and finite cohomology `ker δ / im δ₀` of dimension `r`, `V` has
a basis indexed by `(S₀ ⊕ Fin r) ⊕ S`: disk targets `δ₀(bS₀ s)`, cohomology vectors in
`ker δ`, and disk sources `bS s`. Kind: PROVED. -/
theorem exists_residual_degree_basis_aux {k V₀ V V₂ : Type} [Field k] [AddCommGroup V₀]
    [Module k V₀] [AddCommGroup V] [Module k V] [AddCommGroup V₂] [Module k V₂] (δ₀ : V₀ →ₗ[k] V)
    (δ : V →ₗ[k] V₂) (hδδ : ∀ x, δ (δ₀ x) = 0) {Sp₀ : Submodule k V₀}
    (h₀ : IsCompl (LinearMap.ker δ₀) Sp₀) {Sp : Submodule k V} (h : IsCompl (LinearMap.ker δ) Sp)
    {S₀ S : Type} (bS₀ : Basis S₀ k Sp₀) (bS : Basis S k Sp) {r : ℕ}
    [Module.Finite k (subquotientOf δ₀ δ)] (hr : Module.finrank k (subquotientOf δ₀ δ) = r) :
    ∃ b : Basis ((S₀ ⊕ Fin r) ⊕ S) k V,
      (∀ s, b (.inl (.inl s)) = δ₀ (bS₀ s)) ∧ (∀ j, δ (b (.inl (.inr j))) = 0) ∧
      (∀ s, b (.inr s) = bS s) := by
  set K := LinearMap.ker δ with hK
  set R := LinearMap.range δ₀ with hR
  have hRK : R ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hδδ x
  set R' : Submodule k K := R.comap K.subtype with hR'
  obtain ⟨H', hRH⟩ := Submodule.exists_isCompl R'
  have hinj : Function.Injective (δ₀.domRestrict Sp₀) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hxK : (x : V₀) ∈ LinearMap.ker δ₀ := hx
    have : (x : V₀) ∈ LinearMap.ker δ₀ ⊓ Sp₀ := ⟨hxK, x.2⟩
    rw [h₀.inf_eq_bot, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hSR : Sp₀.map δ₀ = R := by
    have h1 : (LinearMap.ker δ₀).map δ₀ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot _).mpr hx
    rw [hR, LinearMap.range_eq_map, ← h₀.sup_eq_top, Submodule.map_sup, h1, bot_sup_eq]
  let eSR : Sp₀ ≃ₗ[k] R := (LinearEquiv.ofInjective (δ₀.domRestrict Sp₀) hinj).trans
    (LinearEquiv.ofEq _ _ (by rw [LinearMap.range_domRestrict, hSR]))
  have heSR : ∀ x : Sp₀, (eSR x : V) = δ₀ x := fun x => rfl
  let eRR' : R ≃ₗ[k] R' := (Submodule.comapSubtypeEquivOfLe hRK).symm
  have heRR' : ∀ y : R, ((eRR' y : K) : V) = y := fun y => rfl
  have hfinH : Module.Finite k H' :=
    Module.Finite.equiv (Submodule.quotientEquivOfIsCompl R' H' hRH)
  have hrank : Module.finrank k H' = r :=
    (Submodule.quotientEquivOfIsCompl R' H' hRH).finrank_eq.symm.trans hr
  let bR' := (bS₀.map eSR).map eRR'
  let bH' := Module.finBasisOfFinrankEq k H' hrank
  let bK := (bR'.prod bH').map (Submodule.prodEquivOfIsCompl R' H' hRH)
  let b := (bK.prod bS).map (Submodule.prodEquivOfIsCompl K Sp h)
  have hbK_inl : ∀ s, ((bK (.inl s) : K) : V) = δ₀ (bS₀ s) := by
    intro s
    simp only [bK, Basis.map_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
      LinearMap.inl_apply, Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
    simp only [bR', Basis.map_apply]
    rw [heRR', heSR]
  refine ⟨b, ?_, ?_, ?_⟩
  · intro s
    rw [← hbK_inl]
    simp [b, Basis.map_apply, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  · intro j
    have : b (.inl (.inr j)) = ((bK (.inr j) : K) : V) := by
      simp [b, Basis.map_apply, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    rw [this]
    exact (bK (.inr j)).2
  · intro s
    simp [b, Basis.map_apply, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

/-- **One degree of the split residual complex of `X`** (tex 4416–4418): the specialization of
`exists_residual_degree_basis_aux` to `δ₀ = d ⊗ k : Xⁿ⁻¹ → Xⁿ` and `δ = d ⊗ k : Xⁿ → Xⁿ⁺¹`.
Kind: PROVED. -/
theorem exists_residual_degree_basis (X : GCx A) (n : ℤ)
    (hfin : Module.Finite (ResidueField A) (residualCohomologyAt X n))
    {Sp₀ : Submodule (ResidueField A) (ResidueField A ⊗[A] X.X (n - 1))}
    (h₀ : IsCompl (LinearMap.ker (residualDiff X (n - 1) (n - 1 + 1) rfl)) Sp₀)
    {Sp : Submodule (ResidueField A) (ResidueField A ⊗[A] X.X n)}
    (h : IsCompl (LinearMap.ker (residualDiff X n (n + 1) rfl)) Sp)
    {S₀ S : Type} (bS₀ : Basis S₀ (ResidueField A) Sp₀) (bS : Basis S (ResidueField A) Sp) :
    ∃ b : Basis ((S₀ ⊕ Fin (residualRankAt X n)) ⊕ S) (ResidueField A)
        (ResidueField A ⊗[A] X.X n),
      (∀ s, b (.inl (.inl s)) = residualDiff X (n - 1) n (by omega) (bS₀ s)) ∧
      (∀ r, residualDiff X n (n + 1) rfl (b (.inl (.inr r))) = 0) ∧
      (∀ s, b (.inr s) = bS s) := by
  have h₀' : IsCompl (LinearMap.ker (residualDiff X (n - 1) n (by omega))) Sp₀ := by
    rw [residualDiff_ker_congr X (n - 1) n (n - 1 + 1) (by omega) rfl]
    exact h₀
  exact exists_residual_degree_basis_aux _ _ (residualDiff_comp_apply X _ _ _ _ _) h₀' h bS₀ bS rfl

/-- The disk-target indices in degree `n`: disk sources `s ∈ S m` with `m + 1 = n` (tex 4418).
Kind: definition. -/
abbrev gradedDiskTgt (S : ℤ → Type) (n : ℤ) : Type := {p : Σ m, S m // p.1 + 1 = n}

/-- The disk targets in degree `n` are the disk sources in degree `n − 1`.
(tex 4418) Kind: definition. -/
def gradedDiskTgtEquiv (S : ℤ → Type) (n : ℤ) : gradedDiskTgt S n ≃ S (n - 1) :=
  (Equiv.subtypeEquivRight fun p => by omega).trans (Equiv.sigmaSubtype (n - 1))

/-- Transport along `gradedDiskTgtEquiv`: an index-dependent family takes the same value on a
disk target and on its source. (tex 4418) Kind: PROVED. -/
theorem gradedDiskTgtEquiv_spec (S : ℤ → Type) (n : ℤ) {W : Type*}
    (F : ∀ m, m + 1 = n → S m → W) (t : gradedDiskTgt S n) :
    F (n - 1) (by omega) (gradedDiskTgtEquiv S n t) = F t.1.1 t.2 t.1.2 := by
  obtain ⟨⟨m, s⟩, hm⟩ := t
  have hm' : m + 1 = n := hm
  obtain rfl : m = n - 1 := by omega
  rfl

/-- **Split the residual complex into cohomology and disks, gradedwise** (tex 4416–4418). For
finite residual cohomology, every `k ⊗_A Xⁿ` has a basis indexed by
`(disk targets ⊕ Fin (rank n)) ⊕ disk sources`, where the disk target `⟨m, s⟩` (`m + 1 = n`) is
`d ⊗ k` of the disk source `s` in degree `m`, and cohomology vectors and disk targets are
cycles. Kind: PROVED. -/
theorem exists_residual_graded_disk_basis (X : GCx A)
    (hfin : ∀ n, Module.Finite (ResidueField A) (residualCohomologyAt X n)) :
    ∃ (S : ℤ → Type) (b : ∀ n, Basis ((gradedDiskTgt S n ⊕ Fin (residualRankAt X n)) ⊕ S n)
        (ResidueField A) (ResidueField A ⊗[A] X.X n)),
      (∀ n (t : gradedDiskTgt S n), b n (.inl (.inl t)) =
        residualDiff X t.1.1 n t.2 (b t.1.1 (.inr t.1.2))) ∧
      (∀ n r, residualDiff X n (n + 1) rfl (b n (.inl (.inr r))) = 0) ∧
      (∀ n t, residualDiff X n (n + 1) rfl (b n (.inl (.inl t))) = 0) := by
  choose Sp hSp using fun n => Submodule.exists_isCompl
    (LinearMap.ker (residualDiff X n (n + 1) rfl))
  let S : ℤ → Type := fun n => Basis.ofVectorSpaceIndex (ResidueField A) (Sp n)
  let bS : ∀ n, Basis (S n) (ResidueField A) (Sp n) := fun n =>
    Basis.ofVectorSpace (ResidueField A) (Sp n)
  have key : ∀ n, ∃ b : Basis ((gradedDiskTgt S n ⊕ Fin (residualRankAt X n)) ⊕ S n)
      (ResidueField A) (ResidueField A ⊗[A] X.X n),
      (∀ t : gradedDiskTgt S n, b (.inl (.inl t)) = residualDiff X t.1.1 n t.2 (bS t.1.1 t.1.2)) ∧
      (∀ r, residualDiff X n (n + 1) rfl (b (.inl (.inr r))) = 0) ∧
      (∀ s, b (.inr s) = bS n s) := by
    intro n
    obtain ⟨b, hb1, hb2, hb3⟩ := exists_residual_degree_basis X n (hfin n) (hSp (n - 1)) (hSp n)
      (bS (n - 1)) (bS n)
    refine ⟨b.reindex (Equiv.sumCongr (Equiv.sumCongr (gradedDiskTgtEquiv S n).symm (Equiv.refl _))
      (Equiv.refl _)), ?_, ?_, ?_⟩
    · intro t
      rw [Basis.reindex_apply]
      exact (hb1 (gradedDiskTgtEquiv S n t)).trans
        (gradedDiskTgtEquiv_spec S n (fun m hm s => residualDiff X m n hm (bS m s)) t)
    · intro r
      rw [Basis.reindex_apply]
      exact hb2 r
    · intro s
      rw [Basis.reindex_apply]
      exact hb3 s
  choose b hb1 hb2 hb3 using key
  refine ⟨S, b, fun n t => by rw [hb1, hb3], hb2, fun n t => ?_⟩
  rw [hb1]
  exact residualDiff_comp_apply X _ _ _ _ _ _

end Residual

section Lifted

variable {A : Type} [CommRing A] [IsLocalRing A]

/-- Reindex the total graded disk basis by Elliot's index `((ιS ⊕ ιH) ⊕ ιS)`, with
`ιS = Σₙ Sₙ` and `ιH = Σₙ Fin (rank n)` (tex 4417–4418). Kind: definition. -/
def gradedDiskIndexEquiv (S : ℤ → Type) (rank : ℤ → ℕ) :
    (Σ n, (gradedDiskTgt S n ⊕ Fin (rank n)) ⊕ S n) ≃
      ((Σ n, S n) ⊕ gModelIndex rank) ⊕ Σ n, S n where
  toFun
    | ⟨_, .inl (.inl t)⟩ => .inl (.inl t.1)
    | ⟨n, .inl (.inr r)⟩ => .inl (.inr ⟨n, r⟩)
    | ⟨n, .inr s⟩ => .inr ⟨n, s⟩
  invFun
    | .inl (.inl ⟨m, s⟩) => ⟨m + 1, .inl (.inl ⟨⟨m, s⟩, rfl⟩)⟩
    | .inl (.inr ⟨n, r⟩) => ⟨n, .inl (.inr r)⟩
    | .inr ⟨n, s⟩ => ⟨n, .inr s⟩
  left_inv := by
    rintro ⟨n, (⟨⟨m, s⟩, hm⟩ | r) | s⟩
    · subst hm
      rfl
    · rfl
    · rfl
  right_inv := by
    rintro ((⟨m, s⟩ | ⟨n, r⟩) | ⟨n, s⟩) <;> rfl

/-- A summand vector whose residue vanishes lies in `𝔪 · (⨁ₙ Xⁿ)`. (tex 4419–4420) Kind: PROVED. -/
theorem gTotalOf_mem_smul (X : GCx A) (n : ℤ) (w : X.X n)
    (hw : (1 : ResidueField A) ⊗ₜ[A] w = 0) :
    gTotalOf X n w ∈ maximalIdeal A • (⊤ : Submodule A (gTotal X)) := by
  have : w ∈ maximalIdeal A • (⊤ : Submodule A (X.X n)) := by
    rw [← ker_residue_tmul]
    exact hw
  exact Submodule.smul_top_le_comap_smul_top _ (gTotalOf X n) this

/-- **Lift graded bases** (tex 4416–4420). For `A` local with nilpotent maximal ideal, `X`
degreewise flat with finite residual cohomology, the total module has a basis `B` indexed by
`((ιS ⊕ ιH) ⊕ ιS)` lifting the graded residual disk bases degreewise; `B` is homogeneous
(disk target of degree `deg s + 1`, cohomology vector `j` of degree `j.1`, disk source of
degree `deg s`); `ε = d − d₀` has entries in `𝔪`; and `d₀, h₀, i₀, p₀` (FiniteFreeModel's
lifted disk data) have degrees `1, −1, 0, 0`. Kind: PROVED. -/
theorem exists_graded_lifted_disk_basis (hnil : IsNilpotent (maximalIdeal A)) (X : GCx A)
    [∀ n, Module.Flat A (X.X n)]
    (hfin : ∀ n, Module.Finite (ResidueField A) (residualCohomologyAt X n)) :
    ∃ (ιS : Type) (deg : ιS → ℤ)
      (B : Basis ((ιS ⊕ gModelIndex (residualRankAt X)) ⊕ ιS) A (gTotal X)),
      (∀ s, B (.inl (.inl s)) ∈ gTotalDeg X (deg s + 1)) ∧
      (∀ j, B (.inl (.inr j)) ∈ gTotalDeg X j.1) ∧
      (∀ s, B (.inr s) ∈ gTotalDeg X (deg s)) ∧
      (∀ x, (gTotalDiff X - liftedDiskDifferential B) x ∈
        maximalIdeal A • (⊤ : Submodule A (gTotal X))) ∧
      HasDegree (gTotalDeg X) (gTotalDeg X) 1 (liftedDiskDifferential B) ∧
      HasDegree (gTotalDeg X) (gTotalDeg X) (-1) (liftedDiskHomotopy B) ∧
      HasDegree (gModelDeg (residualRankAt X)) (gTotalDeg X) 0 (cohomologyInclusion B) ∧
      HasDegree (gTotalDeg X) (gModelDeg (residualRankAt X)) 0 (cohomologyProjection B) := by
  obtain ⟨S, b, hb1, hb2, hb3⟩ := exists_residual_graded_disk_basis X hfin
  choose v hv using fun n j => exists_residual_lift (b n j)
  let Bl : ∀ n, Basis ((gradedDiskTgt S n ⊕ Fin (residualRankAt X n)) ⊕ S n) A (X.X n) := fun n =>
    liftedResidualBasisOfBasis hnil (b n) (v n) (hv n)
  have hBl : ∀ n j, Bl n j = v n j := fun n j => by
    simp only [Bl, coe_liftedResidualBasisOfBasis]
  let E := gradedDiskIndexEquiv S (residualRankAt X)
  let B : Basis _ A (gTotal X) := (DFinsupp.basis Bl).reindex E
  have hB : ∀ x, B (E x) = gTotalOf X x.1 (v x.1 x.2) := by
    intro x
    rw [Basis.reindex_apply, Equiv.symm_apply_apply, dfinsupp_basis_apply_sigma, hBl]
    rfl
  have e1 : ∀ n (t : gradedDiskTgt S n), gTotalOf X n (v n (.inl (.inl t))) = B (.inl (.inl t.1)) :=
    fun n t => (hB ⟨n, .inl (.inl t)⟩).symm
  have e2 : ∀ n r, gTotalOf X n (v n (.inl (.inr r))) = B (.inl (.inr ⟨n, r⟩)) :=
    fun n r => (hB ⟨n, .inl (.inr r)⟩).symm
  have e3 : ∀ n s, gTotalOf X n (v n (.inr s)) = B (.inr ⟨n, s⟩) :=
    fun n s => (hB ⟨n, .inr s⟩).symm
  have e4 : ∀ m s, B (.inl (.inl ⟨m, s⟩)) =
      gTotalOf X (m + 1) (v (m + 1) (.inl (.inl ⟨⟨m, s⟩, rfl⟩))) :=
    fun m s => hB ⟨m + 1, .inl (.inl ⟨⟨m, s⟩, rfl⟩)⟩
  have hvd : ∀ n j, (1 : ResidueField A) ⊗ₜ[A] X.d n (n + 1) rfl (v n j) =
      residualDiff X n (n + 1) rfl (b n j) := by
    intro n j
    rw [← hv n j, LinearMap.baseChange_tmul]
  have hdeg : ∀ {N : Type} [AddCommGroup N] [Module A N] (Ndeg : ℤ → Submodule A N) (k : ℤ)
      (f : gTotal X →ₗ[A] N), (∀ n j, f (gTotalOf X n (v n j)) ∈ Ndeg (n + k)) →
      HasDegree (gTotalDeg X) Ndeg k f := by
    intro N _ _ Ndeg k f hf n x hx
    obtain ⟨z, rfl⟩ := hx
    exact map_mem_of_basis_apply (Bl n) (f ∘ₗ gTotalOf X n) _
      (fun j => by rw [LinearMap.comp_apply, hBl]; exact hf n j) z
  refine ⟨Σ n, S n, Sigma.fst, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨m, s⟩
    rw [e4]
    exact gTotalOf_mem X _ _
  · rintro ⟨n, r⟩
    rw [← e2]
    exact gTotalOf_mem X _ _
  · rintro ⟨n, s⟩
    rw [← e3]
    exact gTotalOf_mem X _ _
  · intro x
    refine map_mem_of_basis_apply B _ _ (fun i => ?_) x
    obtain ⟨⟨n, j⟩, rfl⟩ := E.surjective i
    rw [hB, LinearMap.sub_apply, gTotalDiff_of X n (n + 1) rfl]
    rcases j with (t | r) | s
    · rw [e1, liftedDiskDifferential_tgt, sub_zero]
      apply gTotalOf_mem_smul
      rw [hvd]
      exact hb3 n t
    · rw [e2, liftedDiskDifferential_coh, sub_zero]
      apply gTotalOf_mem_smul
      rw [hvd]
      exact hb2 n r
    · rw [e3, liftedDiskDifferential_src, e4, ← map_sub]
      apply gTotalOf_mem_smul
      rw [TensorProduct.tmul_sub, hvd, hv, sub_eq_zero]
      exact (hb1 (n + 1) ⟨⟨n, s⟩, rfl⟩).symm
  · refine hdeg _ 1 _ fun n j => ?_
    rcases j with (t | r) | s
    · rw [e1, liftedDiskDifferential_tgt]
      exact zero_mem _
    · rw [e2, liftedDiskDifferential_coh]
      exact zero_mem _
    · rw [e3, liftedDiskDifferential_src, e4]
      exact gTotalOf_mem X _ _
  · refine hdeg _ (-1) _ fun n j => ?_
    rcases j with (⟨⟨m, s⟩, hm⟩ | r) | s
    · have hm' : m + 1 = n := hm
      rw [e1]
      change liftedDiskHomotopy B (B (.inl (.inl ⟨m, s⟩))) ∈ _
      rw [liftedDiskHomotopy_tgt, ← e3, show n + -1 = m by omega]
      exact gTotalOf_mem X _ _
    · rw [e2, liftedDiskHomotopy_coh]
      exact zero_mem _
    · rw [e3, liftedDiskHomotopy_src]
      exact zero_mem _
  · intro n x hx
    rw [add_zero]
    rw [gModelDeg, Finsupp.supported_eq_span_single] at hx
    refine (Submodule.span_le.2 ?_ : _ ≤ (gTotalDeg X n).comap (cohomologyInclusion B)) hx
    rintro _ ⟨⟨m, r⟩, hm, rfl⟩
    have hm' : m = n := hm
    subst hm'
    change cohomologyInclusion B (Finsupp.single ⟨m, r⟩ 1) ∈ gTotalDeg X m
    rw [cohomologyInclusion_single, one_smul, ← e2]
    exact gTotalOf_mem X _ _
  · refine hdeg _ 0 _ fun n j => ?_
    rw [add_zero]
    rcases j with (t | r) | s
    · rw [e1, cohomologyProjection_tgt]
      exact zero_mem _
    · rw [e2, cohomologyProjection_coh]
      exact Finsupp.single_mem_supported A _ rfl
    · rw [e3, cohomologyProjection_src]
      exact zero_mem _

/-- **Elliot's perturbation on lifted homogeneous disk data** (tex 4416–4437). With `B` as in
`exists_graded_lifted_disk_basis`, `d₀ = liftedDiskDifferential B`, `h₀ = liftedDiskHomotopy B`,
`i₀, p₀` the cohomology inclusion and projection and `ε = d − d₀`, the perturbed maps
`d_C = p₀ε(1+h₀ε)⁻¹i₀`, `i = (1+h₀ε)⁻¹i₀`, `p = p₀(1+εh₀)⁻¹`, `h = h₀(1+εh₀)⁻¹` form
homogeneous total retract data (`GradedTotalRetract`). Kind: PROVED. -/
theorem exists_elliotGradedRetract (hnil : IsNilpotent (maximalIdeal A)) (X : GCx A)
    [∀ n, Module.Flat A (X.X n)]
    (hfin : ∀ n, Module.Finite (ResidueField A) (residualCohomologyAt X n)) :
    ∃ (ιS : Type) (deg : ιS → ℤ)
      (B : Basis ((ιS ⊕ gModelIndex (residualRankAt X)) ⊕ ιS) A (gTotal X)),
      (∀ s, B (.inl (.inl s)) ∈ gTotalDeg X (deg s + 1)) ∧
      (∀ j, B (.inl (.inr j)) ∈ gTotalDeg X j.1) ∧
      (∀ s, B (.inr s) ∈ gTotalDeg X (deg s)) ∧
      (∀ x, (gTotalDiff X - liftedDiskDifferential B) x ∈
        maximalIdeal A • (⊤ : Submodule A (gTotal X))) ∧
      GradedTotalRetract X (residualRankAt X)
        (perturbedDifferential (gTotalDiff X - liftedDiskDifferential B) (liftedDiskHomotopy B)
          (cohomologyInclusion B) (cohomologyProjection B))
        (perturbedInclusion (gTotalDiff X - liftedDiskDifferential B) (liftedDiskHomotopy B)
          (cohomologyInclusion B))
        (perturbedProjection (gTotalDiff X - liftedDiskDifferential B) (liftedDiskHomotopy B)
          (cohomologyProjection B))
        (perturbedHomotopy (gTotalDiff X - liftedDiskDifferential B) (liftedDiskHomotopy B)) := by
  obtain ⟨ιS, deg, B, h1, h2, h3, hε, hd0, hh0, hi0, hp0⟩ :=
    exists_graded_lifted_disk_basis hnil X hfin
  have hsum : liftedDiskDifferential B + (gTotalDiff X - liftedDiskDifferential B) =
      gTotalDiff X := by abel
  have hd' : (liftedDiskDifferential B + (gTotalDiff X - liftedDiskDifferential B)) *
      (liftedDiskDifferential B + (gTotalDiff X - liftedDiskDifferential B)) = 0 := by
    rw [hsum]
    exact gTotalDiff_mul_self X
  have key := perturbation_lemma_artin (maximalIdeal A) hnil hε
    (normalizedContraction_liftedDisk B) (splitResidualComplex_liftedDisk B) hd'
  rw [hsum] at key
  have hεdeg : HasDegree (gTotalDeg X) (gTotalDeg X) 1
      (gTotalDiff X - liftedDiskDifferential B) := by
    rw [sub_eq_add_neg]
    exact (gTotalDiff_hasDegree X).add hd0.neg
  obtain ⟨g1, g2, g3, g4⟩ := perturbed_degrees_artin (maximalIdeal A) hnil hε (gTotalDeg X)
    (gModelDeg (residualRankAt X)) hεdeg hh0 hi0 hp0
  exact ⟨ιS, deg, B, h1, h2, h3, hε, ⟨key, g1, g2, g3, g4⟩⟩

/-- **Graded finite free models** (Lemma `ex:limits-inner-limit`, tex 4391–4399, proof
4408–4437). Let `A` be local with nilpotent maximal ideal and `X` a complex of flat `A`-modules
whose residual cohomology `Hⁿ(k ⊗_A X)` is finite in every degree. Then `X` has a graded finite
free model of rank `dim_k Hⁿ(k ⊗_A X)` in degree `n`, with actual inclusion, projection and
contraction homotopy (`GRetract`). The model is Elliot's: `gradedModelOfTotal` of
`exists_elliotGradedRetract`, i.e. the degreewise components of
`d_C = p₀ε(1+h₀ε)⁻¹i₀`, `i = (1+h₀ε)⁻¹i₀`, `p = p₀(1+εh₀)⁻¹`, `h = h₀(1+εh₀)⁻¹` for lifted
homogeneous disk data. Kind: PROVED. -/
theorem exists_gradedModel {A : Type} [CommRing A] [IsLocalRing A]
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal A)) (X : GCx A) [∀ n, Module.Flat A (X.X n)]
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField A) (residualCohomologyAt X n)) :
    ∃ R : GradedModel X, ∀ n, R.rank n =
      Module.finrank (IsLocalRing.ResidueField A) (residualCohomologyAt X n) := by
  obtain ⟨_, _, _, -, -, -, -, H⟩ := exists_elliotGradedRetract hnil X hfin
  exact ⟨gradedModelOfTotal H, fun n => rfl⟩

/-- **Bounded graded finite free models** (tex 4391–4396: "a bounded finite free model"). If
moreover `Xⁿ = 0` outside `[lo, hi]`, the model of `exists_gradedModel` has rank `0` there.
Kind: PROVED. -/
theorem exists_gradedModel_bounded {A : Type} [CommRing A] [IsLocalRing A]
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal A)) (X : GCx A) [∀ n, Module.Flat A (X.X n)]
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField A) (residualCohomologyAt X n))
    (lo hi : ℤ) (hX : ∀ n, n < lo ∨ hi < n → Subsingleton (X.X n)) :
    ∃ R : GradedModel X, (∀ n, R.rank n =
      Module.finrank (IsLocalRing.ResidueField A) (residualCohomologyAt X n)) ∧
      ∀ n, n < lo ∨ hi < n → R.rank n = 0 := by
  obtain ⟨R, hR⟩ := exists_gradedModel hnil X hfin
  refine ⟨R, hR, fun n hn => ?_⟩
  rw [hR]
  have := hX n hn
  have : Subsingleton (ResidueField A ⊗[A] X.X n) := ⟨fun y z => by
    obtain ⟨x, rfl⟩ := exists_residual_lift y
    obtain ⟨x', rfl⟩ := exists_residual_lift z
    rw [Subsingleton.elim x x']⟩
  exact Module.finrank_zero_of_subsingleton

end Lifted

end ZInQ.Manuscript.RC.Limits
