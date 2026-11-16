import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.CotTan

/-! faltings5-lower, part 11: `IsogCotBijective`. -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings IsLocalRing

section Final

variable {K : Type} [Field K] [NumberField K] {A B : PkgI3.AbVar K}

theorem dCls_congr (𝒢 : GroupModel A K) {x y : maximalIdeal 𝒢.genStalk}
    (h : (x : 𝒢.genStalk) = y) : 𝒢.dCls x = 𝒢.dCls y := by
  rw [Subtype.ext h]

/-- **`f^*` is onto.** -/
theorem cotMapK_surjective (φ : A.X ⟶ B.X)
    (hφ : IsIsogeny φ) (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (f : 𝒩A.G ⟶ 𝒩B.G)
    [IsMonHom f] (he : CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f) :
    Function.Surjective (cotMapK 𝒩A 𝒩B f) := by
  by_contra hns
  have hlt : LinearMap.range (cotMapK 𝒩A 𝒩B f) < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hns (LinearMap.range_eq_top.mp h)
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set ev := (εMap 𝒩A).hom with hev
  set j := jA 𝒩A with hj
  set I := maximalIdeal 𝒩A.genStalk
  let L : I.Cotangent →+ K := l.toAddMonoidHom
  have hL : ∀ z : I.Cotangent, L z = l z := fun z => rfl
  have hlj : ∀ (k : K) (z : I.Cotangent), L (j k • z) = k * L z := by
    intro k z
    exact l.map_smul k z
  let D : 𝒩A.genStalk → K := fun r => L (I.toCotangent ⟨r - j (ev r), sub_mem_max 𝒩A r⟩)
  have hD : ∀ r, D r = L (I.toCotangent ⟨r - j (ev r), sub_mem_max 𝒩A r⟩) := fun r => rfl
  have hadd : ∀ a b, D (a + b) = D a + D b := by
    intro a b
    rw [hD, hD, hD, ← map_add, ← map_add]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    ring
  have hmul : ∀ a b, D (a * b) = ev a * D b + ev b * D a := by
    intro a b
    have hx : a - j (ev a) ∈ I := sub_mem_max 𝒩A a
    have hy : b - j (ev b) ∈ I := sub_mem_max 𝒩A b
    have hxy : (a - j (ev a)) * (b - j (ev b)) ∈ I := Ideal.mul_mem_right _ _ hx
    have hsplit : (⟨a * b - j (ev (a * b)), sub_mem_max 𝒩A (a * b)⟩ : I) =
        ⟨_, hxy⟩ + j (ev b) • (⟨_, hx⟩ : I) + j (ev a) • (⟨_, hy⟩ : I) := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
      ring
    have h0 : I.toCotangent ⟨_, hxy⟩ = 0 := by
      rw [Ideal.toCotangent_eq_zero, pow_two]
      exact Ideal.mul_mem_mul hx hy
    rw [hD, hsplit, I.toCotangent.map_add, I.toCotangent.map_add, h0, zero_add,
      I.toCotangent.map_smul, I.toCotangent.map_smul, map_add, hlj, hlj, hD, hD]
    ring
  have hs : ∀ c, D (𝒩A.structMap c) = 0 := by
    intro c
    rw [hD]
    have h1 : (⟨𝒩A.structMap c - j (ev (𝒩A.structMap c)), sub_mem_max 𝒩A _⟩ : I) = 0 := by
      apply Subtype.ext
      show 𝒩A.structMap c - jA 𝒩A ((εMap 𝒩A).hom (𝒩A.structMap c)) = 0
      rw [εMap_structMap, jA_alg, sub_self]
    rw [h1, map_zero, map_zero]
  have hg : ∀ b, D ((genMap 𝒩A 𝒩B f).hom b) = 0 := by
    intro b
    rw [hD]
    have hb := sub_mem_max 𝒩B b
    have h1 : I.toCotangent ⟨(genMap 𝒩A 𝒩B f).hom b - j (ev ((genMap 𝒩A 𝒩B f).hom b)),
        sub_mem_max 𝒩A _⟩ = cotMap 𝒩A 𝒩B f (𝒩B.dCls ⟨_, hb⟩) := by
      rw [cotMap_dCls]
      unfold GroupModel.dCls
      congr 1
      apply Subtype.ext
      have he1 : ev ((genMap 𝒩A 𝒩B f).hom b) = (εMap 𝒩B).hom b := by
        rw [hev, ← genMap_εMap 𝒩A 𝒩B f]
        rfl
      simp only [he1, hj, ← genMap_jA 𝒩A 𝒩B f, map_sub]
    rw [h1]
    exact LinearMap.mem_ker.mp (hl ⟨𝒩B.dCls ⟨_, hb⟩, rfl⟩)
  have hD0 := derivation_eq_zero φ hφ 𝒩A 𝒩B f he D hadd hmul hs hg
  apply hl0
  ext z
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective I z
  have hm : ev m = 0 := by
    have h1 := map_nonunit (εMap 𝒩A).hom (m : 𝒩A.genStalk) m.2
    by_contra h2
    exact h1 (isUnit_iff_ne_zero.mpr h2)
  have h3 := hD0 m
  rw [hD] at h3
  have h4 : (⟨↑m - j (ev ↑m), sub_mem_max 𝒩A m⟩ : I) = m := Subtype.ext (by simp [hm])
  show l (I.toCotangent m) = 0
  exact (congrArg (fun x => l (I.toCotangent x)) h4).symm.trans h3

/-- `TangentDim`, from the kernel's proved pieces. -/
theorem tangentDim : ZInQ.DefFaltings.HodgeLattice.TangentDim :=
  ZInQ.DefFaltings.HodgeLattice.tangentDim_of_regular
    (ZInQ.DefFaltings.HodgeLattice.regularOrigin_of
      (ZInQ.DefFaltings.HodgeLattice.originStalkIso_of
        ZInQ.DefFaltings.HodgeLattice.genericFibreStalkIso) ZInQ.Contrib.Dim.regularAtOrigin)
    (ZInQ.DefFaltings.HodgeLattice.dimOrigin_of
      (ZInQ.DefFaltings.HodgeLattice.originStalkIso_of
        ZInQ.DefFaltings.HodgeLattice.genericFibreStalkIso)
      ZInQ.Contrib.Dim.dimAtOrigin ZInQ.Contrib.Dim.dimBaseChange)

/-- `dim_K ω_{A_K} = dim A`. -/
theorem finrank_cotK (𝒢 : GroupModel A K) (g : ℕ) (hg : A.dim = g) :
    Module.finrank K (cotK 𝒢) = g ∧ FiniteDimensional K (cotK 𝒢) := by
  haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
  have td := tangentDim K A K 𝒢 g hg
  let i : K → ResidueField 𝒢.genStalk := fun k => residue 𝒢.genStalk (jA 𝒢 k)
  have hi : Function.Bijective i := by
    refine ⟨((residue 𝒢.genStalk).comp (jA 𝒢)).injective, fun z => ?_⟩
    obtain ⟨w, rfl⟩ := residue_surjective z
    refine ⟨(εMap 𝒢).hom w, ?_⟩
    show residue _ (jA 𝒢 ((εMap 𝒢).hom w)) = residue _ w
    rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact sub_mem_max 𝒢 w
  let e : cotK 𝒢 ≃+ CotangentSpace 𝒢.genStalk := AddEquiv.refl (cotK 𝒢)
  have hc : ∀ (k : K) (x : cotK 𝒢), e (k • x) = i k • e x := by
    intro k x
    exact (algebraMap_smul (ResidueField 𝒢.genStalk) (jA 𝒢 k)
      (show CotangentSpace 𝒢.genStalk from x)).symm
  have hrank := rank_eq_of_equiv_equiv i e hi hc
  rw [← Module.finrank_eq_rank (R := ResidueField 𝒢.genStalk) (M := CotangentSpace 𝒢.genStalk),
    td] at hrank
  exact ⟨Module.finrank_eq_of_rank_eq hrank, Module.finite_of_rank_eq_nat hrank⟩

/-- **`IsogCotBijective`, proved.** -/
theorem isogCotBijective : IsogCotBijective := by
  intro K _ _ A B φ hφ 𝒩A 𝒩B f _ he
  haveI := hφ.2.1
  haveI := hφ.2.2
  obtain ⟨hdA, hsp⟩ := ZInQ.Contrib.Dim.originPt_dims A
  set g := (maximalIdeal (A.X.left.presheaf.stalk (ZInQ.DefFaltings.HodgeLattice.originPt A))).spanFinrank
  have hgA : A.dim = g := hdA.trans hsp.symm
  have hgB : B.dim = g := by
    rw [← hgA]
    exact (ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_finite_surjective φ.left).symm
  obtain ⟨hA1, hA2⟩ := finrank_cotK 𝒩A g hgA
  obtain ⟨hB1, hB2⟩ := finrank_cotK 𝒩B g hgB
  have hs := cotMapK_surjective φ hφ 𝒩A 𝒩B f he
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hB1.trans hA1.symm)).mpr hs
  exact ⟨hi, hs⟩

end Final

end GapHeight
