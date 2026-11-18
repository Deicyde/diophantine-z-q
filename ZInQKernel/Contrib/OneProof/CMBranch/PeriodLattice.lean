import ZInQKernel.Contrib.OneProof.CMBranch.ReducedPeriod
import ZInQKernel.OneProof.H.TailF

/-! # cm-branch2: `CMPeriodLattice` proved from T35, `HomLatticeCorr` and T11b

`CMBranch.CMPeriodLattice` (the period lattice of a CM elliptic curve has multiplier ring `≅ R`) follows from
three textbook statements already on the chain (`OpenTextbookLeaves4HFPZ` fields `t35`, `homLatticeCorr`,
`t11b`) and proved tree results:

1. `E_ℂ := (E_{K̄})_ℂ` (base change along an extension `σ̄ : K̄ → ℂ` of `σ`) has a uniformization
   `Φ : ℂ → E_ℂ(ℂ)` with full lattice `Λ` (T35, `ZInQ.LeafPush2.UniformizationExists`);
2. it transports to a uniformization of `E(ℂ)_σ` with the same `Λ`
   (`HSyn.G0Split.FibreQM.CPtsT.cPts_of_isPullback`, proved; the two base-change squares pasted);
3. `End(E_ℂ) ≅ {α ∈ ℂ | αΛ ⊆ Λ}` as rings (`HomUnify.HomLatticeCorr`: every endomorphism lifts to a
   `ℂ`-linear map of `ℂ`, i.e. a multiplication by some `α`, unique since `Λ` is discrete; every
   multiplier is induced by a unique endomorphism);
4. `End(E_{K̄}) ≅ End(E_ℂ)` as rings (T11b, rigidity: base change is bijective on homomorphisms).
-/

namespace HDec
namespace CMBranch

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open _root_.ZInQ.LeafPush2 (CPts IsUniformization cDom cEvalAt)

/-! ## 1. Endomorphisms of a uniformized elliptic curve over `ℂ` and lattice multipliers -/

section Mult

variable {A : PkgI3.AbVar ℂ} {Λ : Submodule ℤ (Fin 1 → ℂ)}
  {Φ : (Fin 1 → ℂ) → CPts A (RingHom.id ℂ)}

theorem fin1_eq_smul (z : Fin 1 → ℂ) : z = z 0 • (fun _ => (1 : ℂ)) := by
  funext i; rw [Subsingleton.elim i 0]; simp

/-- In a discrete `Λ ⊂ ℂ¹`, `(α − β)ℂ ⊆ Λ` forces `α = β`. -/
theorem eq_of_smul_mem [DiscreteTopology Λ] {t : ℂ} (h : ∀ z : Fin 1 → ℂ, t • z ∈ Λ) : t = 0 := by
  by_contra ht
  have hopen : IsOpen ({0} : Set Λ) := isOpen_discrete _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_singleton_iff.mp hopen
  let w : Fin 1 → ℂ := fun _ => ((ε / 2 : ℝ) : ℂ)
  have hw : w ∈ Λ := by
    have := h (t⁻¹ • w)
    rwa [smul_smul, mul_inv_cancel₀ ht, one_smul] at this
  have hlt : dist (⟨w, hw⟩ : Λ) 0 < ε := by
    rw [Subtype.dist_eq]
    simp only [ZeroMemClass.coe_zero, dist_zero_right, w]
    rw [pi_norm_const, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have h0 := congrArg Subtype.val (hball _ hlt)
  have : ((ε / 2 : ℝ) : ℂ) = 0 := congrFun h0 0
  have : ε / 2 = 0 := by exact_mod_cast this
  linarith

/-- The multiplier of an endomorphism is unique. -/
theorem mult_unique [DiscreteTopology Λ] (hU : IsUniformization (RingHom.id ℂ) Λ Φ) {α β : ℂ}
    (h : ∀ z, Φ (α • z) = Φ (β • z)) : α = β := by
  have hmem : ∀ z : Fin 1 → ℂ, (α - β) • z ∈ Λ := by
    intro z
    rw [← hU.2.1]
    have e1 := hU.1 ((α - β) • z) (β • z)
    rw [← add_smul, sub_add_cancel, h z] at e1
    exact (mul_eq_right.mp e1.symm)
  exact sub_eq_zero.mp (eq_of_smul_mem hmem)

/-- Every endomorphism of `A` acts on `ℂ¹` by a multiplication (from `HomLatticeCorr`, clause 1). -/
theorem exists_mult (hcorr : HomUnify.HomLatticeCorr) (hdim : A.dim = ((1 : ℕ) : WithBot ℕ∞))
    (hU : IsUniformization (RingHom.id ℂ) Λ Φ) (f : PkgI3.AbVar.End A) :
    ∃ α : ℂ, ∀ z, Φ (α • z) = Φ z ≫ f.hom := by
  obtain ⟨M, hM⟩ := hcorr.1 ℂ A A (RingHom.id ℂ) 1 1 Λ Λ Φ Φ hdim hdim hU hU f
  refine ⟨M (fun _ => 1) 0, fun z => ?_⟩
  rw [← hM z]
  congr 1
  conv_rhs => rw [fin1_eq_smul z, map_smul]
  funext i
  rw [Subsingleton.elim i 0]
  simp [mul_comm]

/-- The multiplier `θ(f)` of an endomorphism. -/
noncomputable def mult (hcorr : HomUnify.HomLatticeCorr) (hdim : A.dim = ((1 : ℕ) : WithBot ℕ∞))
    (hU : IsUniformization (RingHom.id ℂ) Λ Φ) (f : PkgI3.AbVar.End A) : ℂ :=
  (exists_mult hcorr hdim hU f).choose

theorem mult_spec (hcorr : HomUnify.HomLatticeCorr) (hdim : A.dim = ((1 : ℕ) : WithBot ℕ∞))
    (hU : IsUniformization (RingHom.id ℂ) Λ Φ) (f : PkgI3.AbVar.End A) (z : Fin 1 → ℂ) :
    Φ (mult hcorr hdim hU f • z) = Φ z ≫ f.hom :=
  (exists_mult hcorr hdim hU f).choose_spec z

theorem mult_mem (hcorr : HomUnify.HomLatticeCorr) (hdim : A.dim = ((1 : ℕ) : WithBot ℕ∞))
    (hU : IsUniformization (RingHom.id ℂ) Λ Φ) (f : PkgI3.AbVar.End A) :
    mult hcorr hdim hU f ∈ latticeMultipliers Λ := by
  intro z hz
  rw [← hU.2.1, mult_spec hcorr hdim hU f z, (hU.2.1 z).mpr hz, CategoryTheory.Hom.one_def,
    Category.assoc, IsMonHom.one_hom]

/-- **`End(A) ≅ {α | αΛ ⊆ Λ}` as rings** (`HomLatticeCorr`). -/
theorem end_ringEquiv_mult (hcorr : HomUnify.HomLatticeCorr) (hdim : A.dim = ((1 : ℕ) : WithBot ℕ∞))
    [DiscreteTopology Λ] (hU : IsUniformization (RingHom.id ℂ) Λ Φ) :
    Nonempty (PkgI3.AbVar.End A ≃+* latticeMultipliers Λ) := by
  have key : ∀ (f : PkgI3.AbVar.End A) (α : ℂ), (∀ z, Φ (α • z) = Φ z ≫ f.hom) →
      mult hcorr hdim hU f = α := fun f α h =>
    mult_unique hU (fun z => by rw [mult_spec hcorr hdim hU f z, h])
  let θ : PkgI3.AbVar.End A →+* latticeMultipliers Λ :=
    { toFun := fun f => ⟨mult hcorr hdim hU f, mult_mem hcorr hdim hU f⟩
      map_one' := Subtype.ext (key 1 1 (fun z => by
        rw [one_smul]; exact (Category.comp_id _).symm))
      map_mul' := fun f g => Subtype.ext (key (f * g) _ (fun z => by
        show Φ ((mult hcorr hdim hU f * mult hcorr hdim hU g) • z) = Φ z ≫ (g.hom ≫ f.hom)
        rw [mul_smul, mult_spec hcorr hdim hU f, mult_spec hcorr hdim hU g, Category.assoc]))
      map_zero' := Subtype.ext (key 0 0 (fun z => by
        rw [zero_smul, (hU.2.1 0).mpr (Submodule.zero_mem _)]
        show (1 : CPts A (RingHom.id ℂ)) = Φ z ≫ (1 : A.X ⟶ A.X)
        rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, ← Category.assoc,
          toUnit_unique (Φ z ≫ toUnit A.X) (toUnit _)]))
      map_add' := fun f g => Subtype.ext (key (f + g) _ (fun z => by
        show Φ ((mult hcorr hdim hU f + mult hcorr hdim hU g) • z) = Φ z ≫ (f.hom * g.hom)
        rw [add_smul, hU.1, mult_spec hcorr hdim hU f, mult_spec hcorr hdim hU g,
          MonObj.comp_mul])) }
  refine ⟨RingEquiv.ofBijective θ ⟨fun f g hfg => ?_, fun ⟨α, hα⟩ => ?_⟩⟩
  · have hfg' : mult hcorr hdim hU f = mult hcorr hdim hU g := congrArg Subtype.val hfg
    let M : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := mult hcorr hdim hU f • LinearMap.id
    have hM : ∀ z ∈ Λ, M z ∈ Λ := fun z hz => mult_mem hcorr hdim hU f z hz
    obtain ⟨h0, -, huniq⟩ := hcorr.2 A A 1 1 Λ Λ Φ Φ hdim hdim hU hU M hM
    have e1 := huniq f (fun z => mult_spec hcorr hdim hU f z)
    have e2 := huniq g (fun z => by
      show Φ (mult hcorr hdim hU f • z) = _
      rw [hfg']; exact mult_spec hcorr hdim hU g z)
    exact e1.trans e2.symm
  · let M : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := α • LinearMap.id
    have hM : ∀ z ∈ Λ, M z ∈ Λ := fun z hz => hα z hz
    obtain ⟨f, hf, -⟩ := hcorr.2 A A 1 1 Λ Λ Φ Φ hdim hdim hU hU M hM
    exact ⟨f, Subtype.ext (key f α hf)⟩

end Mult

/-! ## 2. Rigidity: endomorphisms over `K̄` and over `ℂ` -/

/-- **`End(B) ≅ End(B_L)` as rings for `B` over an algebraically closed field of characteristic 0** (T11b). -/
theorem end_ringEquiv_baseChange (h11b : ZInQ.LeafPush2.T11b_Rigidity) (k : Type) [Field k]
    [IsAlgClosed k] [CharZero k] (L : Type) [Field L] [Algebra k L] (B : PkgI3.AbVar k) :
    Nonempty (PkgI3.AbVar.End B ≃+* PkgI3.AbVar.End (B.baseChange L)) := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  have hm : ∀ f : PkgI3.AbVar.End B, IsMonHom (F.map f.hom) := fun f => by
    exact Functor.map.instIsMonHom (F := F) (f := f.hom)
  let β : PkgI3.AbVar.End B →+* PkgI3.AbVar.End (B.baseChange L) :=
    { toFun := fun f => @PkgI3.AbVar.Hom.mk' L _ (B.baseChange L) (B.baseChange L) (F.map f.hom)
        (hm f)
      map_one' := PkgI3.AbVar.Hom.ext' (by
        show F.map (𝟙 _) = 𝟙 _
        exact F.map_id _)
      map_mul' := fun f g => PkgI3.AbVar.Hom.ext' (by
        show F.map (g.hom ≫ f.hom) = F.map g.hom ≫ F.map f.hom
        exact F.map_comp _ _)
      map_zero' := PkgI3.AbVar.Hom.ext' (by
        show F.map (1 : B.X ⟶ B.X) = 1
        exact Functor.map_one F)
      map_add' := fun f g => PkgI3.AbVar.Hom.ext' (by
        show F.map (f.hom * g.hom) = F.map f.hom * F.map g.hom
        exact Functor.map_mul F _ _) }
  refine ⟨RingEquiv.ofBijective β ⟨fun f g hfg => ?_, fun h => ?_⟩⟩
  · have e : F.map f.hom = F.map g.hom := congrArg PkgI3.AbVar.Hom.hom hfg
    obtain ⟨φ, -, huniq⟩ := h11b k L B B (F.map f.hom) (hm f)
    have e1 := huniq f.hom ⟨inferInstance, rfl⟩
    have e2 := huniq g.hom ⟨inferInstance, e.symm⟩
    exact PkgI3.AbVar.Hom.ext' (e1.trans e2.symm)
  · obtain ⟨φ, ⟨hφ, hφe⟩, -⟩ := h11b k L B B h.hom inferInstance
    exact ⟨@PkgI3.AbVar.Hom.mk' k _ B B φ hφ, PkgI3.AbVar.Hom.ext' hφe⟩

/-! ## 3. `CMPeriodLattice` -/

/-- **`CMPeriodLattice` from T35, `HomLatticeCorr` and T11b.** -/
theorem cmPeriodLattice_of (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hcorr : HomUnify.HomLatticeCorr) (h11b : ZInQ.LeafPush2.T11b_Rigidity) : CMPeriodLattice := by
  intro K _ _ E hE1 k _ _ R hR hCM σ
  set A : PkgI3.AbVar K := LeafAdopt.abVarEquiv K E
  let Kb := AlgebraicClosure K
  letI iKC : Algebra K ℂ := σ.toAlgebra
  let σb : Kb →ₐ[K] ℂ := IsAlgClosed.lift
  letI iKbC : Algebra Kb ℂ := σb.toRingHom.toAlgebra
  let Ab : PkgI3.AbVar Kb := A.baseChange Kb
  let Q : PkgI3.AbVar ℂ := Ab.baseChange ℂ
  -- dimensions
  have hdA : A.dim = 1 := by rw [LeafAdopt.abVarEquiv_dim]; exact hE1
  have h1 : Q.dim = Ab.dim := G0Dim.dim_baseChange ℂ Ab.X.left Ab.X.hom
  have h2 : Ab.dim = A.dim := G0Dim.dim_baseChange Kb A.X.left A.X.hom
  have hdQ : Q.dim = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [h1, h2, hdA]; simp
  -- the uniformization of `Q` (T35)
  obtain ⟨Λ, ΦQ, hdisc, hZ, hU⟩ := hT35 ℂ Q (RingHom.id ℂ) 1 hdQ
  -- the pullback square `Q → A` over `σ`
  let f₁ := Spec.map (CommRingCat.ofHom (algebraMap K Kb))
  let f₂ := Spec.map (CommRingCat.ofHom (algebraMap Kb ℂ))
  have S1 : IsPullback (pullback.fst Ab.X.hom f₂) (pullback.snd Ab.X.hom f₂) Ab.X.hom f₂ :=
    IsPullback.of_hasPullback _ _
  have S2 : IsPullback (pullback.fst A.X.hom f₁) (pullback.snd A.X.hom f₁) A.X.hom f₁ :=
    IsPullback.of_hasPullback _ _
  have S12 := S1.paste_horiz S2
  have hσ : f₂ ≫ f₁ = Spec.map (CommRingCat.ofHom σ) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σb.commutes x
  have S : IsPullback (pullback.fst Ab.X.hom f₂ ≫ pullback.fst A.X.hom f₁) Q.X.hom A.X.hom
      (Spec.map (CommRingCat.ofHom σ)) := hσ ▸ S12
  obtain ⟨ψ, hψ⟩ := HSyn.G0Split.FibreQM.CPtsT.cPts_of_isPullback A σ Q _ S
  -- the uniformization of `A` at `σ` (as `UnifTransport`)
  obtain ⟨hadd, hker, hsurj, hopen, hhol⟩ := hU
  have hdom : ∀ (U : A.X.left.Opens) (U' : Q.X.left.Opens),
      (∀ x : CPts Q (RingHom.id ℂ), (⊤ ≤ (ψ x).left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ U')) →
      cDom (fun z => ψ (ΦQ z)) U = cDom ΦQ U' := by
    intro U U' h
    ext z
    exact h (ΦQ z)
  have hUA : IsUniformization σ Λ (fun z => ψ (ΦQ z)) := by
    refine ⟨fun z w => ?_, fun z => ?_, fun x => ?_, fun U => ?_, fun U s => ?_⟩
    · simp only [hadd, map_mul]
    · rw [← hker]
      exact MulEquiv.map_eq_one_iff ψ
    · obtain ⟨y, rfl⟩ := ψ.surjective x
      obtain ⟨z, rfl⟩ := hsurj y
      exact ⟨z, rfl⟩
    · obtain ⟨U', s', h⟩ := hψ U 0
      rw [hdom U U' (fun x => (h x).1)]
      exact hopen U'
    · obtain ⟨U', s', h⟩ := hψ U s
      rw [hdom U U' (fun x => (h x).1)]
      exact (hhol U' s').congr (fun z hz => (h (ΦQ z)).2 hz)
  refine ⟨Λ, fun z => ψ (ΦQ z), hUA, ⟨hdisc, hZ⟩, ?_⟩
  -- the rings
  obtain ⟨e1⟩ := hCM
  obtain ⟨e2⟩ := end_ringEquiv_baseChange h11b Kb ℂ Ab
  obtain ⟨e3⟩ := @end_ringEquiv_mult Q Λ ΦQ hcorr hdQ hdisc ⟨hadd, hker, hsurj, hopen, hhol⟩
  exact ⟨(e1.symm.trans e2).trans e3⟩

/-- **`ReducedCMPeriod` from T35, `HomLatticeCorr`, T11b and the textbook leaf `CoxProperLattice`.** -/
theorem reducedCMPeriod_of_leaves (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hcorr : HomUnify.HomLatticeCorr) (h11b : ZInQ.LeafPush2.T11b_Rigidity)
    (hC : CoxProperLattice) : ReducedCMPeriod :=
  reducedCMPeriod_of (cmPeriodLattice_of hT35 hcorr h11b) hC

end CMBranch
end HDec
