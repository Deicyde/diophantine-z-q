import ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyWeil

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PhiSurj

open T09Pic PkgI3 PkgI3.AbVar PicDict

variable {k : Type} [Field k]

/-- The class of `c ∈ Pic(X)` as a `k`-point of a representing object of `Pic_{X/k}`. -/
noncomputable def kClass {X : AbVar k} {P : Over (Spec (CommRingCat.of k))}
    (rep : (picardFunctor X.X.hom).obj.RepresentableBy P) (c : X.X.left.Pic) :
    𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ P :=
  rep.homEquiv.symm ((toPicardFunctor X.X.hom).app (op (𝟙_ _))
    (Scheme.Pic.map (pullback.fst X.X.hom (𝟙_ (Over (Spec (CommRingCat.of k)))).hom) c))

/-- **(a): translation-invariant classes are points of `Pic⁰`.** Over `k = k̄`, for `X` an abelian variety, a
representation `P` of `Pic_{X/k}` and its identity component `(B, j)`, every translation-invariant class `c`
(Mumford's `Pic⁰`) is the class of a `k`-point of `B`. The part of Mumford §8 Thm 1 (with §13 and Kleiman §9.5,
locators UNVERIFIED) that this task does not prove; a consequence of `PicDict.MumfordPhiSurjectiveAC`
(`tiClassesInPicZeroAC_of_phiSurjective`). Not used by the recommended fold (the field is rerouted). -/
def TIClassesInPicZeroAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (P : Over (Spec (CommRingCat.of k)))
    (rep : (picardFunctor X.X.hom).obj.RepresentableBy P) (B : AbVar k) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ c : X.X.left.Pic, AC.IsTI c → ∃ y : AC.Kpt B, y ≫ j = kClass rep c

/-- `x ≫ φ_L` is the class of `φ_L(x)`. -/
lemma kpt_comp_phiL {X : AbVar k} {P : Over (Spec (CommRingCat.of k))}
    (rep : (picardFunctor X.X.hom).obj.RepresentableBy P) (c₀ : X.X.left.Pic) (x : AC.Kpt X) :
    x ≫ phiL rep c₀ = kClass rep (AC.phi c₀ x) := by
  rw [phiL, comp_classify, PhiAmple.map_mumfordBundle_kpt]
  rfl

/-- At `Spec k`, `k = k̄`, every fppf covering sieve of `𝟙_` is maximal. -/
theorem over_fppf_unit_mem [IsAlgClosed k] {S : Sieve (𝟙_ (Over (Spec (CommRingCat.of k))))}
    (hS : S ∈ (Scheme.fppfTopology.over (Spec (CommRingCat.of k))) (𝟙_ _)) : S.arrows (𝟙 _) := by
  rw [GrothendieckTopology.mem_over_iff] at hS
  have h := fppf_arrows_of_isAlgClosed hS (k := k) (𝟙 _)
  replace h := (Sieve.overEquiv_iff S _).1 h
  have h2 := S.downward_closed h
    (Over.homMk (𝟙 (𝟙_ (Over (Spec (CommRingCat.of k)))).left) (by simp) :
      𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Over.mk (𝟙 _ ≫ (𝟙_ (Over (Spec (CommRingCat.of k)))).hom))
  convert h2 using 1
  ext
  exact (Category.id_comp _).symm

/-- `Pic(X ×_k k) → Pic_{X/k}(k)` is injective for `k = k̄`. -/
theorem toPicardFunctor_unit_injective [IsAlgClosed k] (X : AbVar k) :
    Function.Injective ((toPicardFunctor X.X.hom).app (op (𝟙_ (Over (Spec (CommRingCat.of k)))))) := by
  intro c c' h
  have : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (CommRingCat.of k)))
    (toPicardFunctor X.X.hom) := Presheaf.isLocallyInjective_toSheafify' _ (picardPresheaf X.X.hom)
  have hm := Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of k)))
    (toPicardFunctor X.X.hom) c c' h
  have := over_fppf_unit_mem hm
  simpa [Presheaf.equalizerSieve] using this

/-- `kClass` is injective for `k = k̄`. -/
theorem kClass_injective [IsAlgClosed k] {X : AbVar k} {P : Over (Spec (CommRingCat.of k))}
    (rep : (picardFunctor X.X.hom).obj.RepresentableBy P) : Function.Injective (kClass rep) := by
  intro c c' h
  have h1 := toPicardFunctor_unit_injective X (rep.homEquiv.symm.injective h)
  have : IsIso (pullback.fst X.X.hom (𝟙_ (Over (Spec (CommRingCat.of k)))).hom) := by
    change IsIso (pullback.fst X.X.hom (𝟙 _)); infer_instance
  have h2 := congrArg (Scheme.Pic.map (inv (pullback.fst X.X.hom (𝟙_ (Over (Spec (CommRingCat.of k)))).hom))) h1
  simp only [← Scheme.Pic.map_comp, IsIso.inv_hom_id, Scheme.Pic.map_id] at h2
  exact h2

/-- `k`-points lift along a surjective morphism locally of finite type, `k = k̄`. -/
theorem exists_lift_kpt [IsAlgClosed k] {A B : AbVar k} (lam : A.X ⟶ B.X)
    [LocallyOfFiniteType lam.left] (hs : Surjective lam.left) (y : AC.Kpt B) :
    ∃ x : AC.Kpt A, x ≫ lam = y := by
  obtain ⟨a, ha⟩ := hs.surj (y.left (IsLocalRing.closedPoint k))
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := lam.left) (g := y.left) a
    (IsLocalRing.closedPoint k) ha
  have hlft : LocallyOfFiniteType (pullback.snd lam.left y.left) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback _ _)
      inferInstance
  obtain ⟨σ, hσ⟩ := exists_section_of_isAlgClosed (k := k) (pullback.snd lam.left y.left) hlft z
  refine ⟨Over.homMk (σ ≫ pullback.fst lam.left y.left) ?_, ?_⟩
  · change (σ ≫ pullback.fst _ _) ≫ A.X.hom = 𝟙 _
    rw [Category.assoc, ← Over.w lam, pullback.condition_assoc, reassoc_of% hσ]
    exact Over.w y
  · apply Over.OverMorphism.ext
    change (σ ≫ pullback.fst _ _) ≫ lam.left = y.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

/-- **Mumford §8 Thm 1 from (a)**: `MumfordPhiSurjectiveAC` follows from `TIClassesInPicZeroAC` and the inputs of
`phiAmpleIsogeny_of_weil` (with L1, L2). So (a) is exactly what is missing. -/
theorem mumfordPhiSurjectiveAC_of_ti (ha : TIClassesInPicZeroAC) (h1 : PicRepresentableAbVar)
    (h2 : PicZeroAbVar) (h4 : WeilPairingMumford) (hT : AvSplit.MumfordTorsionAlgClosed) :
    MumfordPhiSurjectiveAC := by
  intro k _ _ X c₀ hc₀ c hc
  obtain ⟨P, ⟨rep⟩⟩ := h1 k X
  obtain ⟨B, j, hj⟩ := h2 k X P rep
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj c₀
  have hiso := phiAmpleIsogeny_of_weil h4 hT k X P rep B j hj c₀ hc₀ lam.hom hlam
  have : IsFinite lam.hom.left := hiso.1
  obtain ⟨y, hy⟩ := ha k X P rep B j hj c hc
  obtain ⟨x, hx⟩ := exists_lift_kpt lam.hom hiso.2 y
  refine ⟨x, kClass_injective rep ?_⟩
  rw [← hy, ← hx, Category.assoc, hlam, kpt_comp_phiL]

/-- (a) is a consequence of `MumfordPhiSurjectiveAC` (never stronger than the field it would replace). -/
theorem tiClassesInPicZeroAC_of_phiSurjective (h8 : MumfordPhiSurjectiveAC) :
    TIClassesInPicZeroAC := by
  intro k _ _ X P rep B j hj c hc
  obtain ⟨L, hamp⟩ := exists_isAmple_of_isAlgClosed X
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj L
  obtain ⟨x, rfl⟩ := h8 k X L hamp c hc
  exact ⟨x ≫ lam.hom, by rw [Category.assoc, hlam, kpt_comp_phiL]⟩

end PhiSurj

#print axioms PhiSurj.mumfordPhiSurjectiveAC_of_ti
#print axioms PhiSurj.tiClassesInPicZeroAC_of_phiSurjective
