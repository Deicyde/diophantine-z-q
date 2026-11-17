import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Limits.FlatFree
import ZInQKernel.Contrib.OneProof.RC.Limits.Perturbation

/-!
# Lane RC6 (limits): finite free models (Lemma `ex:limits-inner-limit`, first part)

Manuscript tex 4391–4399 (statement) and 4408–4437 (proof): *"Let `A` be an Artin local ring with
nilpotent maximal ideal, and let a complex of flat `A`-modules have finite bounded residual
cohomology. … It admits a bounded finite free model with actual inclusion, projection and
contraction homotopy."*

This file assembles Elliot's proof from its three steps, all `PROVED`:
1. flat modules over `A` are free, and lifted residual bases are bases (`FlatFree`, tex 4409–4412);
2. the residual complex splits into cohomology and disks, and its adapted basis lifts; the lifted
   disk data form Elliot's normalized contraction, and `ε = d − d₀` has entries in `𝔪`
   (this file, tex 4416–4427);
3. the perturbation formulas give the model (`Perturbation`, tex 4428–4437).

The result is `exists_finiteFreeModel`: a finite free module `C = A^{(ι)}`, `ι` finite of
cardinality the residual cohomology dimension, with differential `d_C`, inclusion `i`, projection
`p` and contraction homotopy `h` satisfying `p i = 1`, `1 − i p = d h + h d`, `d i = i d_C`,
`p d = d_C p`, `d_C² = 0`, `h² = h i = p h = 0`.

DEPARTURE (total module): as in `Perturbation`, the complex is represented by its total module `M`
(all degrees summed) with the differential `d` as an endomorphism; "finite bounded residual
cohomology" becomes finiteness of the total residual cohomology `ker(d ⊗ k)/im(d ⊗ k)`, and
"bounded finite free model" becomes a finite free model.  The construction is degreewise in
Elliot's graded setting; degrees are not tracked here.
DEPARTURE (residual complex): "the residual complex" is the base change `k ⊗_A M`, `k = A/𝔪`
(canonically `M/𝔪M`).
-/

namespace ZInQ.Manuscript.RC.Limits

open Module IsLocalRing TensorProduct


section DiskData

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {ιS ιH : Type*}

/-- Elliot's lifted disk differential `d₀` (tex 4418): it sends the lifted basis vector of the disk
source `s` to the lifted basis vector of the disk target `s`, and kills the lifted cohomology and
disk-target vectors.  Index convention: `inl (inl s)` disk target, `inl (inr h)` cohomology,
`inr s` disk source. -/
noncomputable def liftedDiskDifferential (B : Basis ((ιS ⊕ ιH) ⊕ ιS) A M) : Module.End A M :=
  B.constr A (Sum.elim (fun _ => 0) (fun s => B (.inl (.inl s))))

/-- Elliot's `h₀` (tex 4422): it inverts `d₀` from disk targets to disk sources and is zero on the
other summands. -/
noncomputable def liftedDiskHomotopy (B : Basis ((ιS ⊕ ιH) ⊕ ιS) A M) : Module.End A M :=
  B.constr A (Sum.elim (Sum.elim (fun s => B (.inr s)) (fun _ => 0)) (fun _ => 0))

/-- Elliot's `i₀` (tex 4421): inclusion of the (lifted) cohomology summand. -/
noncomputable def cohomologyInclusion (B : Basis ((ιS ⊕ ιH) ⊕ ιS) A M) : (ιH →₀ A) →ₗ[A] M :=
  Finsupp.linearCombination A (fun h => B (.inl (.inr h)))

/-- Elliot's `p₀` (tex 4421): projection onto the (lifted) cohomology summand. -/
noncomputable def cohomologyProjection (B : Basis ((ιS ⊕ ιH) ⊕ ιS) A M) : M →ₗ[A] (ιH →₀ A) :=
  B.constr A (Sum.elim (Sum.elim (fun _ => 0) (fun h => Finsupp.single h 1)) (fun _ => 0))

variable (B : Basis ((ιS ⊕ ιH) ⊕ ιS) A M)

@[simp] theorem liftedDiskDifferential_tgt (s : ιS) :
    liftedDiskDifferential B (B (.inl (.inl s))) = 0 := by
  simp [liftedDiskDifferential]

@[simp] theorem liftedDiskDifferential_coh (h : ιH) :
    liftedDiskDifferential B (B (.inl (.inr h))) = 0 := by
  simp [liftedDiskDifferential]

@[simp] theorem liftedDiskDifferential_src (s : ιS) :
    liftedDiskDifferential B (B (.inr s)) = B (.inl (.inl s)) := by
  simp [liftedDiskDifferential]

@[simp] theorem liftedDiskHomotopy_tgt (s : ιS) :
    liftedDiskHomotopy B (B (.inl (.inl s))) = B (.inr s) := by
  simp [liftedDiskHomotopy]

@[simp] theorem liftedDiskHomotopy_coh (h : ιH) :
    liftedDiskHomotopy B (B (.inl (.inr h))) = 0 := by
  simp [liftedDiskHomotopy]

@[simp] theorem liftedDiskHomotopy_src (s : ιS) :
    liftedDiskHomotopy B (B (.inr s)) = 0 := by
  simp [liftedDiskHomotopy]

@[simp] theorem cohomologyProjection_tgt (s : ιS) :
    cohomologyProjection B (B (.inl (.inl s))) = 0 := by
  simp [cohomologyProjection]

@[simp] theorem cohomologyProjection_coh (h : ιH) :
    cohomologyProjection B (B (.inl (.inr h))) = Finsupp.single h 1 := by
  simp [cohomologyProjection]

@[simp] theorem cohomologyProjection_src (s : ιS) :
    cohomologyProjection B (B (.inr s)) = 0 := by
  simp [cohomologyProjection]

@[simp] theorem cohomologyInclusion_single (h : ιH) (a : A) :
    cohomologyInclusion B (Finsupp.single h a) = a • B (.inl (.inr h)) := by
  simp [cohomologyInclusion]

/-- The lifted disk data form a normalized contraction (tex 4423–4427). PROVED. -/
theorem normalizedContraction_liftedDisk :
    NormalizedContraction (liftedDiskDifferential B) (liftedDiskHomotopy B)
      (cohomologyInclusion B) (cohomologyProjection B) where
  proj_comp_incl := by
    ext h
    simp
  homotopy_mul_self := by
    refine B.ext fun i => ?_
    rcases i with (s | h) | s <;> simp
  homotopy_comp_incl := by
    ext h
    simp
  proj_comp_homotopy := by
    refine B.ext fun i => ?_
    rcases i with (s | h) | s <;> simp
  contraction := by
    refine B.ext fun i => ?_
    rcases i with (s | h) | s <;> simp

/-- The lifted disk differential is zero on the cohomology summand and lands in disk targets.
PROVED. -/
theorem splitResidualComplex_liftedDisk :
    SplitResidualComplex (liftedDiskDifferential B) (cohomologyInclusion B)
      (cohomologyProjection B) where
  diff_mul_self := by
    refine B.ext fun i => ?_
    rcases i with (s | h) | s <;> simp
  diff_comp_incl := by
    ext h
    simp
  proj_comp_diff := by
    refine B.ext fun i => ?_
    rcases i with (s | h) | s <;> simp

end DiskData

section Cohomology

/-- The cohomology `ker δ / im δ` of a square-zero endomorphism `δ` (a differential module). -/
abbrev cohomologyOf {k V : Type*} [Ring k] [AddCommGroup V] [Module k V] (δ : Module.End k V) :
    Type _ :=
  LinearMap.ker δ ⧸ (LinearMap.range δ).comap (LinearMap.ker δ).subtype

end Cohomology

section DiskBasis

universe w

/-- **Split the residual complex into cohomology and disks** (tex 4417–4418).  PROVED.

Over a field `k`, a square-zero endomorphism `δ` of a vector space `V` has a basis indexed by
`(ιS ⊕ ιH) ⊕ ιS`: disk targets `inl (inl s) = δ(inr s)`, cohomology vectors `inl (inr h)` and disk
sources `inr s`; the cohomology vectors and disk targets lie in `ker δ`, and the cohomology
`ker δ / im δ` is free on `ιH`. -/
theorem exists_disk_basis {k : Type*} {V : Type w} [Field k] [AddCommGroup V] [Module k V]
    (δ : Module.End k V) (hδ : δ * δ = 0) :
    ∃ (ιS ιH : Type w) (b : Basis ((ιS ⊕ ιH) ⊕ ιS) k V),
      (∀ s, b (.inl (.inl s)) = δ (b (.inr s))) ∧
      (∀ h, δ (b (.inl (.inr h))) = 0) ∧
      (∀ s, δ (b (.inl (.inl s))) = 0) ∧
      Nonempty (cohomologyOf δ ≃ₗ[k] (ιH →₀ k)) := by
  set K := LinearMap.ker δ with hK
  set R := LinearMap.range δ with hR
  have hδδ : ∀ x, δ (δ x) = 0 := fun x => by
    rw [← Module.End.mul_apply, hδ, LinearMap.zero_apply]
  have hRK : R ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hδδ x
  obtain ⟨S, hKS⟩ := Submodule.exists_isCompl K
  set R' : Submodule k K := R.comap K.subtype with hR'
  obtain ⟨H', hRH⟩ := Submodule.exists_isCompl R'
  have hinj : Function.Injective (δ.domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hxK : (x : V) ∈ K := hx
    have : (x : V) ∈ K ⊓ S := ⟨hxK, x.2⟩
    rw [hKS.inf_eq_bot, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hSR : S.map δ = R := by
    have h1 : K.map δ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot k).mpr hx
    rw [hR, LinearMap.range_eq_map, ← hKS.sup_eq_top, Submodule.map_sup, h1, bot_sup_eq]
  let eSR : S ≃ₗ[k] R := (LinearEquiv.ofInjective (δ.domRestrict S) hinj).trans
    (LinearEquiv.ofEq _ _ (by rw [LinearMap.range_domRestrict, hSR]))
  have heSR : ∀ x : S, (eSR x : V) = δ x := fun x => rfl
  let eRR' : R ≃ₗ[k] R' := (Submodule.comapSubtypeEquivOfLe hRK).symm
  have heRR' : ∀ y : R, ((eRR' y : K) : V) = y := fun y => rfl
  let bS := Basis.ofVectorSpace k S
  let bR' := (bS.map eSR).map eRR'
  let bH' := Basis.ofVectorSpace k H'
  let bK := (bR'.prod bH').map (Submodule.prodEquivOfIsCompl R' H' hRH)
  let b := (bK.prod bS).map (Submodule.prodEquivOfIsCompl K S hKS)
  have hb_inr : ∀ s, b (.inr s) = (bS s : V) := by
    intro s
    simp [b, Basis.map_apply, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hbK_inl : ∀ s, ((bK (.inl s) : K) : V) = δ (bS s : V) := by
    intro s
    simp only [bK, Basis.map_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
      LinearMap.inl_apply, Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
    simp only [bR', Basis.map_apply]
    rw [heRR', heSR]
  have hb_inl_inl : ∀ s, b (.inl (.inl s)) = δ (bS s : V) := by
    intro s
    rw [← hbK_inl]
    simp [b, Basis.map_apply, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hb_inl_inr : ∀ h, b (.inl (.inr h)) = ((bK (.inr h) : K) : V) := by
    intro h
    simp [b, Basis.map_apply, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨_, _, b, ?_, ?_, ?_, ?_⟩
  · intro s; rw [hb_inl_inl, hb_inr]
  · intro h; rw [hb_inl_inr]; exact (bK (.inr h)).2
  · intro s; rw [hb_inl_inl]; exact hδδ _
  · exact ⟨(Submodule.quotientEquivOfIsCompl R' H' hRH).trans bH'.repr⟩


end DiskBasis

section Residual

universe u v

variable {A : Type u} [CommRing A] [IsLocalRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- The residual differential `d ⊗ k` on the residual complex `k ⊗_A M`, `k = A/𝔪`. -/
noncomputable abbrev residualDifferential (d : Module.End A M) :
    Module.End (ResidueField A) (ResidueField A ⊗[A] M) :=
  d.baseChange (ResidueField A)

theorem residualDifferential_mul_self (d : Module.End A M) (hd : d * d = 0) :
    residualDifferential d * residualDifferential d = 0 := by
  rw [Module.End.mul_eq_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, hd,
    LinearMap.baseChange_zero]

/-- The residual cohomology `ker(d ⊗ k) / im(d ⊗ k)` (tex 4393–4394, 4416). -/
abbrev residualCohomology (d : Module.End A M) : Type (max u v) :=
  cohomologyOf (residualDifferential d)

/-- **Split the residual complex into cohomology and disks, and lift graded bases** (tex
4416–4420).  PROVED.

For a flat module `M` over a local ring with nilpotent maximal ideal and a differential `d`, there
is a basis `B` of `M` lifting a basis of the residual complex adapted to cohomology, disk sources
and disk targets, such that `ε = d − d₀` has entries in `𝔪` (`d₀` the lifted disk differential),
and the cohomology index set is a basis of the residual cohomology. -/
theorem exists_lifted_disk_basis (hnil : IsNilpotent (maximalIdeal A)) [Module.Flat A M]
    (d : Module.End A M) (hd : d * d = 0) :
    ∃ (ιS ιH : Type (max u v)) (B : Basis ((ιS ⊕ ιH) ⊕ ιS) A M),
      (∀ x, (d - liftedDiskDifferential B) x ∈ maximalIdeal A • (⊤ : Submodule A M)) ∧
      Nonempty (residualCohomology d ≃ₗ[ResidueField A] (ιH →₀ ResidueField A)) := by
  obtain ⟨ιS, ιH, b, h1, h2, h3, ⟨e⟩⟩ :=
    exists_disk_basis (residualDifferential d) (residualDifferential_mul_self d hd)
  have hsurj : Function.Surjective (TensorProduct.mk A (ResidueField A) M 1) :=
    TensorProduct.mk_surjective A M (ResidueField A)
      (by rw [ResidueField.algebraMap_eq]; exact residue_surjective)
  choose v hv using fun i => hsurj (b i)
  have hv' : ∀ i, (1 : ResidueField A) ⊗ₜ[A] v i = b i := fun i => hv i
  let B := liftedResidualBasisOfBasis hnil b v hv'
  have hB : ∀ i, B i = v i := fun i => by
    simp only [B, coe_liftedResidualBasisOfBasis]
  refine ⟨ιS, ιH, B, ?_, ⟨e⟩⟩
  -- the set of `x` with `(d - d₀) x ∈ 𝔪 M` is a submodule containing every basis vector
  have hbasis : ∀ i, (d - liftedDiskDifferential B) (B i) ∈ maximalIdeal A • (⊤ : Submodule A M) := by
    intro i
    rw [← ker_residue_tmul, LinearMap.mem_ker, TensorProduct.mk_apply, LinearMap.sub_apply,
      TensorProduct.tmul_sub, sub_eq_zero]
    have hd1 : ∀ j, (1 : ResidueField A) ⊗ₜ[A] d (B j) = residualDifferential d (b j) := by
      intro j
      rw [← hv' j, hB j, LinearMap.baseChange_tmul]
    rw [hd1]
    rcases i with (s | h) | s
    · rw [liftedDiskDifferential_tgt, TensorProduct.tmul_zero]; exact h3 s
    · rw [liftedDiskDifferential_coh, TensorProduct.tmul_zero]; exact h2 h
    · rw [liftedDiskDifferential_src, hB, hv', h1]
  intro x
  have hspan : x ∈ Submodule.span A (Set.range B) := by rw [B.span_eq]; trivial
  refine Submodule.span_induction (p := fun x _ =>
      (d - liftedDiskDifferential B) x ∈ maximalIdeal A • (⊤ : Submodule A M)) ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨i, rfl⟩; exact hbasis i
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- **The finite free model data** (tex 4416–4427).  PROVED.

If moreover the residual cohomology is finite (tex 4392–4394), the cohomology index set is finite,
of cardinality the residual cohomology dimension, and the lifted data satisfy Elliot's normalized
contraction identities, the split-complex identities, and `ε = d − d₀ ≡ 0 mod 𝔪`.  These are
exactly the hypotheses of the perturbation lemma. -/
theorem exists_finiteFreeModel_data (hnil : IsNilpotent (maximalIdeal A)) [Module.Flat A M]
    (d : Module.End A M) (hd : d * d = 0)
    (hfin : Module.Finite (ResidueField A) (residualCohomology d)) :
    ∃ (ι : Type (max u v)) (_ : Fintype ι) (d₀ h₀ : Module.End A M)
      (i₀ : (ι →₀ A) →ₗ[A] M) (p₀ : M →ₗ[A] (ι →₀ A)),
      NormalizedContraction d₀ h₀ i₀ p₀ ∧ SplitResidualComplex d₀ i₀ p₀ ∧
      (∀ x, (d - d₀) x ∈ maximalIdeal A • (⊤ : Submodule A M)) ∧
      Fintype.card ι = Module.finrank (ResidueField A) (residualCohomology d) := by
  obtain ⟨ιS, ιH, B, hε, ⟨e⟩⟩ := exists_lifted_disk_basis hnil d hd
  have hfinH : Module.Finite (ResidueField A) (ιH →₀ ResidueField A) :=
    Module.Finite.equiv e
  have : Finite ιH :=
    Module.Finite.finite_basis (Finsupp.basisSingleOne : Basis ιH (ResidueField A) _)
  let _ : Fintype ιH := Fintype.ofFinite ιH
  refine ⟨ιH, inferInstance, liftedDiskDifferential B, liftedDiskHomotopy B,
    cohomologyInclusion B, cohomologyProjection B, normalizedContraction_liftedDisk B,
    splitResidualComplex_liftedDisk B, hε, ?_⟩
  rw [e.finrank_eq, Module.finrank_finsupp_self]

/-- **Finite free models** (Lemma `ex:limits-inner-limit`, tex 4391–4399 and 4408–4437).  PROVED.

Let `A` be a local ring whose maximal ideal is nilpotent (an Artin local ring), `M` a flat
`A`-module with a differential `d` (`d² = 0`) whose residual cohomology `ker(d ⊗ k)/im(d ⊗ k)` is
finite-dimensional.  Then there are a finite type `ι` with `#ι = dim_k` (residual cohomology), a
differential `d_C` on the finite free module `A^{(ι)}`, and `A`-linear `i : A^{(ι)} → M`,
`p : M → A^{(ι)}`, `h : M → M` forming normalized deformation retract data:
`p i = 1`, `1 − i p = d h + h d`, `d i = i d_C`, `p d = d_C p`, `d_C² = 0`, `h² = h i = p h = 0`.
The maps are Elliot's: `d_C = p₀ ε (1 + h₀ ε)⁻¹ i₀`, `i = (1 + h₀ ε)⁻¹ i₀`, `p = p₀ (1 + ε h₀)⁻¹`,
`h = h₀ (1 + ε h₀)⁻¹`, for the lifted disk data `(d₀, h₀, i₀, p₀)` and `ε = d − d₀`. -/
theorem exists_finiteFreeModel {A : Type u} [CommRing A] [IsLocalRing A]
    (hnil : IsNilpotent (maximalIdeal A)) {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Flat A M] (d : Module.End A M) (hd : d * d = 0)
    (hfin : Module.Finite (ResidueField A) (residualCohomology d)) :
    ∃ (ι : Type (max u v)) (_ : Fintype ι) (dC : Module.End A (ι →₀ A)) (i : (ι →₀ A) →ₗ[A] M)
      (p : M →ₗ[A] (ι →₀ A)) (h : Module.End A M),
      IsNormalizedDeformationRetract d dC i p h ∧
      Fintype.card ι = Module.finrank (ResidueField A) (residualCohomology d) := by
  obtain ⟨ι, hι, d₀, h₀, i₀, p₀, hN, hS, hε, hcard⟩ := exists_finiteFreeModel_data hnil d hd hfin
  have hsum : d₀ + (d - d₀) = d := by abel
  have hd' : (d₀ + (d - d₀)) * (d₀ + (d - d₀)) = 0 := by rw [hsum]; exact hd
  have key := perturbation_lemma_artin (maximalIdeal A) hnil hε hN hS hd'
  rw [hsum] at key
  exact ⟨ι, hι, _, _, _, _, key, hcard⟩

/-- Every fixed finite diagram transports to the model (tex 4397–4399, 4439–4442): the finite free
model of `exists_finiteFreeModel` is in particular deformation retract data, so the transport
lemmas of `Perturbation` (`retractTransport_chainMap`, `retractTransport_homotopy`,
`retractTransport_comp`, `retractTransport_square`, `retractTransport_linear_relation_add`, …)
apply to it.  PROVED. -/
theorem exists_finiteFreeModel_isDeformationRetract {A : Type u} [CommRing A] [IsLocalRing A]
    (hnil : IsNilpotent (maximalIdeal A)) {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Flat A M] (d : Module.End A M) (hd : d * d = 0)
    (hfin : Module.Finite (ResidueField A) (residualCohomology d)) :
    ∃ (ι : Type (max u v)) (_ : Fintype ι) (dC : Module.End A (ι →₀ A)) (i : (ι →₀ A) →ₗ[A] M)
      (p : M →ₗ[A] (ι →₀ A)) (h : Module.End A M), IsDeformationRetract d dC i p h := by
  obtain ⟨ι, hι, dC, i, p, h, hR, -⟩ := exists_finiteFreeModel hnil d hd hfin
  exact ⟨ι, hι, dC, i, p, h, hR.toIsDeformationRetract⟩

end Residual

end ZInQ.Manuscript.RC.Limits
