import ZInQKernel.Contrib.OneProof.PhiSurjDescent
import ZInQKernel.Contrib.OneProof.WeilFormulaTheta
import ZInQKernel.Contrib.OneProof.MumfordSquareMulN

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PhiSurj.AVDesc

open PicDict PkgI3 PkgI3.AbVar PicDict.Transport WeilProof WeilProof.Theta

variable {k : Type} [Field k]

/-- `[n]` is étale, surjective and proper (from weil-proof's `divisibleAC` argument). -/
theorem mul_props [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0) :
    Etale (AC.mul X n).left ∧ Surjective (AC.mul X n).left ∧ IsProper (AC.mul X n).left := by
  have : GeometricallyConnected X.X.hom := geomConn_of_geomInt X.X.hom
  have : PkgI2.IsAbelianScheme (ObjBridge.toGrp X) := ⟨X.proper, X.smooth, inferInstance⟩
  have hE : Etale ((𝟙 (ObjBridge.toGrp X).X ^ n : (ObjBridge.toGrp X).X ⟶ (ObjBridge.toGrp X).X).left) :=
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof k (ObjBridge.toGrp X) n
      (by exact (IsUnit.mk0 _ hnk))
  have hE' : Etale (AC.mul X n).left := hE
  set f := (AC.mul X n).left with hfdef
  have hopen : IsOpenMap f := isOpenMap_of_generalizingMap f (Flat.generalizingMap f)
  have hw : f ≫ X.X.hom = X.X.hom := Over.w (AC.mul X n)
  have : IsProper (f ≫ X.X.hom) := by rw [hw]; infer_instance
  have hP : IsProper f := IsProper.of_comp f X.X.hom
  have hclosed : IsClosedMap f := f.isClosedMap
  have : IsIntegral X.X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.X.hom
  have hrange : Set.range f = Set.univ := by
    have hne : (Set.range f).Nonempty := by
      obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
      exact ⟨_, ⟨η[X.X].left p, rfl⟩⟩
    exact (IsClopen.eq_univ ⟨hclosed.isClosed_range, hopen.isOpen_range⟩ hne)
  refine ⟨hE', ⟨fun y => ?_⟩, hP⟩
  have : y ∈ Set.range f := by rw [hrange]; trivial
  exact this

/-- `[n]` generates an fpqc covering. -/
theorem mul_cover [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0) :
    Sieve.ofArrows (fun _ : PUnit.{1} => X.X.left) (fun _ => (AC.mul X n).left) ∈
      Scheme.fpqcTopology X.X.left := by
  obtain ⟨hE, hS, hP⟩ := mul_props X n hnk
  change Sieve.generate (Presieve.ofArrows _ _) ∈ _
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fpqcPrecoverage _)

lemma tr_left_comp_mul {X : AbVar k} {n : ℕ} (x : AC.Kpt X) (hx : x ^ n = 1) :
    (AC.tr x).left ≫ (AC.mul X n).left = (AC.mul X n).left := by
  rw [← Over.comp_left, AC.tr_comp_mul x hx]

/-- The sections `y ↦ (y, y + x)`, `x ∈ X[n]`, are open immersions. -/
theorem sec_isOpenImmersion [IsAlgClosed k] {X : AbVar k} {n : ℕ} [hF : Fact ((n : k) ≠ 0)] (x : AC.Kpt X) (hx : x ^ n = 1) :
    IsOpenImmersion (Desc.sec (AC.mul X n).left (tr_left_comp_mul x hx)) := by
  obtain ⟨hE, -, -⟩ := mul_props X n (Fact.out)
  exact ZInQ.Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section _
    (pullback.fst (AC.mul X n).left (AC.mul X n).left) (pullback.lift_fst _ _ _)

lemma kpt_comp_tr {X : AbVar k} (y x : AC.Kpt X) : y ≫ AC.tr x = y * x := by
  simp only [AC.tr, ← CategoryTheory.Hom.mul_def]
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    CartesianMonoidalCategory.toUnit_unique (y ≫ CartesianMonoidalCategory.toUnit X.X) (𝟙 _),
    Category.id_comp]

lemma kpt_comp_mul {X : AbVar k} (y : AC.Kpt X) (n : ℕ) : y ≫ AC.mul X n = y ^ n := by
  simp only [AC.mul]
  rw [MonObj.comp_pow, Category.comp_id]

/-- The sections `y ↦ (y, y + x)`, `x ∈ X[n](k)`, cover `X ×_{[n],X,[n]} X` (on points). -/
theorem sec_cover [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0)
    (y : (pullback (AC.mul X n).left (AC.mul X n).left : Scheme)) :
    ∃ i : {x : AC.Kpt X // x ^ n = 1},
      y ∈ Set.range (Desc.sec (AC.mul X n).left (tr_left_comp_mul i.1 i.2)).base := by
  obtain ⟨hE, -, -⟩ := mul_props X n hnk
  let m := (AC.mul X n).left
  have hmw : m ≫ X.X.hom = X.X.hom := Over.w (AC.mul X n)
  let str : pullback m m ⟶ Spec (CommRingCat.of k) := pullback.fst m m ≫ X.X.hom
  have : LocallyOfFiniteType str := by dsimp [str]; infer_instance
  have : JacobsonSpace (pullback m m : Scheme) := LocallyOfFiniteType.jacobsonSpace str
  by_contra hy
  push_neg at hy
  let V : Set (pullback m m : Scheme) :=
    ⋃ i : {x : AC.Kpt X // x ^ n = 1}, Set.range (Desc.sec m (tr_left_comp_mul i.1 i.2)).base
  have hVo : IsOpen V := by
    refine isOpen_iUnion fun i => ?_
    have := sec_isOpenImmersion (n := n) (hF := ⟨hnk⟩) i.1 i.2
    exact (Desc.sec m (tr_left_comp_mul i.1 i.2)).isOpenEmbedding.isOpen_range
  have hZ : (Vᶜ).Nonempty := ⟨y, by simpa [V] using hy⟩
  obtain ⟨z, hzZ, hzc⟩ := nonempty_inter_closedPoints hZ hVo.isClosed_compl.isLocallyClosed
  let σ := pointOfClosedPoint str z hzc
  have hσ : σ ≫ str = 𝟙 _ := pointOfClosedPoint_comp str z hzc
  let x1 : AC.Kpt X := Over.homMk (σ ≫ pullback.fst m m) (by
    change (σ ≫ pullback.fst m m) ≫ X.X.hom = 𝟙 _
    rw [Category.assoc]; exact hσ)
  let x2 : AC.Kpt X := Over.homMk (σ ≫ pullback.snd m m) (by
    change (σ ≫ pullback.snd m m) ≫ X.X.hom = 𝟙 _
    rw [Category.assoc, ← hmw, ← Category.assoc (pullback.snd m m), ← pullback.condition, Category.assoc,
      hmw]
    exact hσ)
  have hx12 : x1 ≫ AC.mul X n = x2 ≫ AC.mul X n := by
    apply Over.OverMorphism.ext
    change (σ ≫ pullback.fst m m) ≫ m = (σ ≫ pullback.snd m m) ≫ m
    rw [Category.assoc, Category.assoc, pullback.condition]
  rw [kpt_comp_mul, kpt_comp_mul] at hx12
  let x := x1⁻¹ * x2
  have hx : x ^ n = 1 := by
    simp only [x, mul_pow, inv_pow, hx12, inv_mul_cancel]
  apply hzZ
  refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
  have hsec : x1.left ≫ Desc.sec m (tr_left_comp_mul x hx) = σ := by
    apply pullback.hom_ext
    · simp [x1]
    · have h2 : (x1 ≫ AC.tr x).left = x2.left := by
        rw [kpt_comp_tr]
        congr 1
        simp only [x, mul_inv_cancel_left]
      simp only [Category.assoc, pullback.lift_snd]
      exact h2
  refine ⟨x1.left (IsLocalRing.closedPoint k), ?_⟩
  have e := congrArg (fun f : Spec (CommRingCat.of k) ⟶ (pullback m m : Scheme) =>
    f.base (IsLocalRing.closedPoint k)) hsec
  simp only [Scheme.Hom.comp_base] at e
  have hσz : σ.base (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply str z hzc _
  rw [hσz] at e
  exact e

/-- A trivialization of `n^*M` exists when `n^*c = 1`. -/
theorem nonempty_triv_ac {X : AbVar k} {n : ℕ} {c : X.X.left.Pic}
    (h : Scheme.Pic.map (AC.mul X n).left c = 1) : Nonempty (AC.Triv X n c) := by
  obtain ⟨e⟩ := Scheme.Pic.eq_iff_nonempty_iso.1 h
  exact ⟨(Scheme.Pic.oneIso).symm ≪≫ e.symm ≪≫ Scheme.Pic.mkIso _⟩

/-- **The right kernel of Mumford's pairing is trivial** (Mumford §20, the descent half): over `k = k̄`, for `n`
invertible, if `ψ : 𝒪 ≅ n^*M` has Mumford's formula `1` at every `x ∈ X[n](k)`, then `M ≅ 𝒪`. -/
theorem formula_nondeg_right [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0)
    (c : X.X.left.Pic) (ψ : AC.Triv X n c)
    (h : ∀ (x : AC.Kpt X) (hx : x ^ n = 1), AC.formula x hx c ψ = 1) : c = 1 := by
  have hF : Fact ((n : k) ≠ 0) := ⟨hnk⟩
  have hM : (AC.modX c).IsQuasicoherent := SheafOfModules.IsInvertible.isQuasicoherent c.isInvertible
  have hsurj : ⨆ i : {x : AC.Kpt X // x ^ n = 1},
      @Scheme.Hom.opensRange _ _ (Desc.sec (AC.mul X n).left (tr_left_comp_mul i.1 i.2))
        (sec_isOpenImmersion i.1 i.2) = ⊤ := by
    apply le_antisymm le_top
    intro y _
    obtain ⟨i, hi⟩ := sec_cover X n hnk y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hinv : ∀ i : {x : AC.Kpt X // x ^ n = 1},
      (pOU (AC.tr i.1).left).inv ≫ (Scheme.Modules.pullback (AC.tr i.1).left).map ψ.hom ≫
        (Scheme.Modules.pullbackComp (AC.tr i.1).left (AC.mul X n).left).hom.app (AC.modX c) ≫
        (Scheme.Modules.pullbackCongr (tr_left_comp_mul i.1 i.2)).hom.app (AC.modX c) ≫ ψ.inv = 𝟙 _ := by
    intro i
    have hi := h i.1 i.2
    unfold AC.formula at hi
    rw [wf_eq_alpha] at hi
    apply (Scheme.Modules.unitHomAddEquiv (Scheme.Modules.unit _)).injective
    rw [Scheme.Modules.unitHomAddEquiv_apply, Scheme.Modules.unitHomAddEquiv_apply]
    exact hi.trans rfl
  obtain ⟨e⟩ := @Desc.nonempty_iso_of_invariant X.X.left (AC.mul X n).left (mul_cover X n hnk)
    {x : AC.Kpt X // x ^ n = 1} (fun i => (AC.tr i.1).left) (fun i => tr_left_comp_mul i.1 i.2)
    (fun i => sec_isOpenImmersion i.1 i.2) hsurj (AC.modX c) hM ψ hinv
  exact Scheme.Pic.eq_iff_nonempty_iso.2 ⟨e.symm ≪≫ (Scheme.Pic.oneIso).symm⟩

/-! ## Counting `X̂[n]` -/

/-- `X(k)[n]`. -/
def torsK (X : AbVar k) (n : ℕ) : Subgroup (AC.Kpt X) := (powMonoidHom n : AC.Kpt X →* AC.Kpt X).ker

lemma mem_torsK {X : AbVar k} {n : ℕ} {x : AC.Kpt X} : x ∈ torsK X n ↔ x ^ n = 1 := by
  simp [torsK]

/-- `Spec L` over itself, as the unit object. -/
def unitIsoL (L : Type) [Field L] : PkgI2.specOver L L ≅ 𝟙_ (Over (Spec (CommRingCat.of L))) :=
  Over.isoMk (Iso.refl _) (by simp [PkgI2.specOver])

/-- `X(k)[n] ≅ (ℤ/n)^{2g}` from Mumford's theorem (the textbook leaf), transported to `k`-points. -/
theorem exists_torsK_addEquiv [IsAlgClosed k] (hT : AvSplit.MumfordTorsionAlgClosed) (X : AbVar k)
    (g n : ℕ) (hg : topologicalKrullDim X.X.left = g) (hn : 0 < n) (hnk : (n : k) ≠ 0) :
    Nonempty (Additive (torsK X n) ≃+ (Fin (2 * g) → ZMod n)) := by
  have := isAV X
  obtain ⟨e, he⟩ := hT k (grpOf X) g n hg hn hnk
  let φ : AC.Kpt X ≃ PkgI2.Pts (grpOf X) k :=
    { toFun := fun x => (unitIsoL k).hom ≫ x
      invFun := fun z => (unitIsoL k).inv ≫ z
      left_inv := fun x => by simp
      right_inv := fun z => by simp }
  have hφmul : ∀ x y, φ (x * y) = φ x * φ y := fun x y => by
    change (unitIsoL k).hom ≫ (x * y) = ((unitIsoL k).hom ≫ x) * ((unitIsoL k).hom ≫ y)
    exact MonObj.comp_mul _ _ _
  have hφpow : ∀ x (m : ℕ), φ (x ^ m) = φ x ^ m := fun x m => by
    change (unitIsoL k).hom ≫ (x ^ m) = ((unitIsoL k).hom ≫ x) ^ m
    exact MonObj.comp_pow _ _ _
  have hφone : φ 1 = 1 := by simpa using hφpow 1 0
  let ψ : torsK X n ≃ PkgI2.torsion (grpOf X) k n :=
    Equiv.subtypeEquiv φ (by
      intro x
      change x ∈ torsK X n ↔ φ x ^ n = 1
      rw [mem_torsK, ← hφpow, ← hφone, φ.injective.eq_iff])
  refine ⟨AddEquiv.mk' (Additive.toMul.trans (ψ.trans e)) ?_⟩
  intro x y
  have hmem : (ψ (Additive.toMul x)).1 * (ψ (Additive.toMul y)).1 ∈ PkgI2.torsion (grpOf X) k n := by
    have h := (ψ (Additive.toMul (x + y))).2
    have e1 : (ψ (Additive.toMul (x + y))).1 = (ψ (Additive.toMul x)).1 * (ψ (Additive.toMul y)).1 :=
      hφmul _ _
    rwa [e1] at h
  have e2 : ψ (Additive.toMul (x + y)) = ⟨_, hmem⟩ := Subtype.ext (hφmul _ _)
  simp only [Equiv.trans_apply]
  rw [e2, he]

/-- Homomorphisms out of `(ℤ/n)^m` into a finite group: at most `#M^m`. -/
theorem card_hom_le {G : Type*} [AddCommGroup G] {M : Type*} [AddCommGroup M] [Finite M] {n m : ℕ}
    [NeZero n] (E : G ≃+ (Fin m → ZMod n)) : Nat.card (G →+ M) ≤ Nat.card M ^ m := by
  classical
  let basis : Fin m → G := fun i => E.symm (Pi.single i 1)
  have hspan : ∀ x : G, x = ∑ i, (E x i).val • basis i := by
    intro x
    apply E.injective
    rw [map_sum]
    simp only [map_nsmul, basis, AddEquiv.apply_symm_apply]
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    · intro i _ hij
      rw [Pi.smul_apply, Pi.single_eq_of_ne hij.symm, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hinj : Function.Injective (fun f : G →+ M => fun i => f (basis i)) := by
    intro f f' h
    ext x
    rw [hspan x, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, map_nsmul]
    exact congrArg _ (congrFun h i)
  calc Nat.card (G →+ M) ≤ Nat.card (Fin m → M) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card M ^ m := by simp [Nat.card_fun]

lemma const_injective [IsAlgClosed k] (X : AbVar k) : Function.Injective (AC.const X) := by
  have : Nonempty (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : Nonempty X.X.left := ⟨η[X.X].left (Nonempty.some inferInstance)⟩
  have : Nonempty (⊤ : X.X.left.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  exact (X.X.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).injective

lemma const_mul (X : AbVar k) (a b : k) : AC.const X (a * b) = AC.const X a * AC.const X b := by
  simp only [AC.const, map_mul]

lemma formula_eq_of_eq {X : AbVar k} {n : ℕ} {x : AC.Kpt X} {hx : x ^ n = 1} {c₁ c₂ : X.X.left.Pic}
    (h : c₁ = c₂) (ψ₁ : AC.Triv X n c₁) (ψ₂ : AC.Triv X n c₂)
    (hind : ∀ ψ ψ' : AC.Triv X n c₂, AC.formula x hx c₂ ψ = AC.formula x hx c₂ ψ') :
    AC.formula x hx c₁ ψ₁ = AC.formula x hx c₂ ψ₂ := by
  subst h; exact hind ψ₁ ψ₂

lemma isDT_mul {X : AbVar k} {n : ℕ} {c c' : X.X.left.Pic} (hc : AC.IsDT n c) (hc' : AC.IsDT n c') :
    AC.IsDT n (c * c') :=
  ⟨fun x => by rw [Scheme.Pic.map_mul, hc.1 x, hc'.1 x], by rw [mul_pow, hc.2, hc'.2, mul_one]⟩

lemma isDT_inv {X : AbVar k} {n : ℕ} {c : X.X.left.Pic} (hc : AC.IsDT n c) : AC.IsDT n c⁻¹ :=
  ⟨fun x => by rw [← Scheme.Pic.mapHom_apply, map_inv, Scheme.Pic.mapHom_apply, hc.1 x],
    by rw [inv_pow, hc.2, inv_one]⟩

/-- **`#X̂[n] ≤ n^{2g}`** over `k = k̄`, `n` invertible: `c ↦ ē_n(·, c)` embeds the translation-invariant classes
of order dividing `n` into `Hom(X[n], μ_n)` (Mumford §20: the formula is a well-defined bilinear `μ_n`-valued
pairing, weil-proof's `mumfordWeilPairingAC_proof`; its right kernel is trivial, `formula_nondeg_right`), and
`X[n] ≅ (ℤ/n)^{2g}`. -/
theorem card_isDT_le [IsAlgClosed k] (h1 : T09Pic.PicRepresentableAbVar) (h2 : T09Pic.PicZeroAbVar)
    (hT : AvSplit.MumfordTorsionAlgClosed) (X : AbVar k) (g n : ℕ)
    (hg : topologicalKrullDim X.X.left = g) (hn : 0 < n) (hnk : (n : k) ≠ 0) :
    Finite {c : X.X.left.Pic // AC.IsDT n c} ∧ Nat.card {c : X.X.left.Pic // AC.IsDT n c} ≤ n ^ (2 * g) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨E⟩ := exists_torsK_addEquiv hT X g n hg hn hnk
  have hW := WeilProof.mumfordWeilPairingAC_proof
  have htriv : ∀ c, AC.IsDT n c → Nonempty (AC.Triv X n c) := fun c hc =>
    nonempty_triv_ac (by rw [PhiSurj.mumfordMulNPicZeroAC_of_open h1 h2 k X c hc.1 n, hc.2])
  have hval : ∀ (c : X.X.left.Pic) (hc : AC.IsDT n c) (x : torsK X n), ∃ u : rootsOfUnity n k,
      AC.const X ((u : kˣ) : k) = AC.formula x.1 (mem_torsK.1 x.2) c (htriv c hc).some := by
    intro c hc x
    obtain ⟨-, h2', -, -⟩ := hW k X n hn hnk x.1 x.1 (mem_torsK.1 x.2) (mem_torsK.1 x.2) c c hc hc
    obtain ⟨u, hu, hu'⟩ := h2' (htriv c hc).some
    exact ⟨⟨u, (mem_rootsOfUnity n u).2 hu⟩, hu'⟩
  choose χ hχ using hval
  have hmul : ∀ c (hc : AC.IsDT n c) (x y : torsK X n), χ c hc (x * y) = χ c hc x * χ c hc y := by
    intro c hc x y
    obtain ⟨-, -, h3, -⟩ := hW k X n hn hnk x.1 y.1 (mem_torsK.1 x.2) (mem_torsK.1 y.2) c c hc hc
    apply Subtype.ext; apply Units.ext
    apply const_injective X
    have e1 := hχ c hc (x * y)
    have e2 := hχ c hc x
    have e3 := hχ c hc y
    have e4 : AC.formula (x * y).1 (mem_torsK.1 (x * y).2) c (htriv c hc).some =
        AC.formula x.1 (mem_torsK.1 x.2) c (htriv c hc).some *
          AC.formula y.1 (mem_torsK.1 y.2) c (htriv c hc).some := h3 _
    rw [e1, e4, ← e2, ← e3, ← const_mul]
    rfl
  let Φ : {c : X.X.left.Pic // AC.IsDT n c} → (Additive (torsK X n) →+ Additive (rootsOfUnity n k)) :=
    fun c => AddMonoidHom.mk' (fun x => Additive.ofMul (χ c.1 c.2 (Additive.toMul x)))
      (fun x y => by
        change Additive.ofMul (χ c.1 c.2 (Additive.toMul x * Additive.toMul y)) = _
        rw [hmul]; rfl)
  have hΦ : Function.Injective Φ := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have hχeq : ∀ x : torsK X n, χ c hc x = χ c' hc' x := fun x =>
      Additive.ofMul.injective (DFunLike.congr_fun h (Additive.ofMul x))
    let d := c * c'⁻¹
    have hd : AC.IsDT n d := isDT_mul hc (isDT_inv hc')
    have hdc : c = d * c' := by simp [d]
    have hone : ∀ (x : AC.Kpt X) (hx : x ^ n = 1), AC.formula x hx d (htriv d hd).some = 1 := by
      intro x hx
      let xt : torsK X n := ⟨x, mem_torsK.2 hx⟩
      obtain ⟨h1', h2', -, h4'⟩ := hW k X n hn hnk x x hx hx d c' hd hc'
      obtain ⟨-, -, -, -⟩ := hW k X n hn hnk x x hx hx c c hc hc
      obtain ⟨hi, -, -, -⟩ := hW k X n hn hnk x x hx hx (d * c') (d * c') (isDT_mul hd hc')
        (isDT_mul hd hc')
      have e1 : AC.formula x hx c (htriv c hc).some =
          AC.formula x hx (d * c') (htriv (d * c') (isDT_mul hd hc')).some :=
        formula_eq_of_eq hdc _ _ hi
      have e2 := h4' (htriv d hd).some (htriv c' hc').some (htriv (d * c') (isDT_mul hd hc')).some
      have e3 : AC.formula x hx c (htriv c hc).some = AC.formula x hx c' (htriv c' hc').some := by
        rw [← hχ c hc xt, ← hχ c' hc' xt, hχeq]
      have hunit : IsUnit (AC.formula x hx c' (htriv c' hc').some) := by
        rw [← hχ c' hc' xt]
        exact ((χ c' hc' xt : kˣ).isUnit).map
          (X.X.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
      rw [e1, e2] at e3
      exact (IsUnit.mul_left_inj hunit).1 (e3.trans (one_mul _).symm)
    have hd1 := formula_nondeg_right X n hnk d (htriv d hd).some hone
    apply Subtype.ext
    show c = c'
    rw [hdc, hd1, one_mul]
  have : Finite (Additive (torsK X n)) := Finite.of_equiv _ E.symm.toEquiv
  have : Finite (Additive (torsK X n) →+ Additive (rootsOfUnity n k)) := DFunLike.finite _
  refine ⟨Finite.of_injective Φ hΦ, ?_⟩
  calc Nat.card {c : X.X.left.Pic // AC.IsDT n c}
      ≤ Nat.card (Additive (torsK X n) →+ Additive (rootsOfUnity n k)) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ ≤ Nat.card (Additive (rootsOfUnity n k)) ^ (2 * g) := card_hom_le E
    _ ≤ n ^ (2 * g) := by
        apply Nat.pow_le_pow_left
        rw [Nat.card_congr (Additive.toMul : Additive (rootsOfUnity n k) ≃ _)]
        exact card_rootsOfUnity _ _

end PhiSurj.AVDesc

namespace PhiSurj

open T09Pic PkgI3 PkgI3.AbVar PicDict HDec.WeilPairing

variable {K : Type} [Field K]

/-- **`dim Pic⁰ ≤ dim A`** from L1, L2 and the torsion leaf only: `B[ℓ] ↪ Â[ℓ](A_K̄)` (`y ↦ M_y`, injective,
translation-invariant) and `#Â[ℓ] ≤ ℓ^{2 dim A}` (`AVDesc.card_isDT_le`), while `#B[ℓ] = ℓ^{2 dim B}`. -/
theorem dim_le_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (hT : AvSplit.MumfordTorsionAlgClosed) {A : AbVar K}
    {P : Over (Spec (CommRingCat.of K))} (rep : (picardFunctor A.X.hom).obj.RepresentableBy P)
    {B : AbVar K} {j : B.X ⟶ P} (hj : IsPicZero rep B j) (a b : ℕ)
    (ha : topologicalKrullDim A.X.left = a) (hb : topologicalKrullDim B.X.left = b) : b ≤ a := by
  obtain ⟨ℓ, hℓ2, hℓK⟩ := exists_two_le_natCast_ne_zero (K := K)
  have hℓ0 : 0 < ℓ := by omega
  have : NeZero ℓ := ⟨by omega⟩
  have hℓK' : (ℓ : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
    exact (map_ne_zero _).mpr hℓK
  have ha' : topologicalKrullDim (AKbar A).X.left = a :=
    (ZInQ.Contrib.AbVarBC.dim_baseChange_scheme (AlgebraicClosure K) A.X.left A.X.hom).trans ha
  obtain ⟨EB⟩ := exists_torsAddEquiv hT B b ℓ hb hℓ0 hℓK
  have hsub := picZeroPtsTranslInv_of_leaves pushforwardUnitUniversal geomIntegralProd
  let emb : tors B ℓ → {c : (AKbar A).X.left.Pic // AC.IsDT ℓ c} := fun y =>
    ⟨picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)), (isTI_iff _).2 (hsub K A P rep B j hj _), by
      have hy : (Additive.toMul (y : HDec.WeilPairing.P B)) ^ ℓ = 1 := by
        have := congrArg Additive.toMul (show ℓ • (y : HDec.WeilPairing.P B) = 0 from y.2)
        simpa using this
      change picHom rep hj _ ^ ℓ = 1
      rw [← map_pow, hy, map_one]⟩
  have hemb : Function.Injective emb := by
    intro y y' h
    have h' : picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)) =
        picClass rep j (Additive.toMul (y' : HDec.WeilPairing.P B)) := congrArg Subtype.val h
    exact Subtype.ext (Additive.toMul.injective (picClass_injective rep hj h'))
  obtain ⟨hfin, hcount⟩ := AVDesc.card_isDT_le h1 h2 hT (AKbar A) a ℓ ha' hℓ0 hℓK'
  have hle := Nat.card_le_card_of_injective emb hemb
  have hB : Nat.card (tors B ℓ) = ℓ ^ (2 * b) := by
    rw [Nat.card_congr EB.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [hB] at hle
  have := (Nat.pow_le_pow_iff_right (by omega : 1 < ℓ)).mp (hle.trans hcount)
  omega

/-- **`λ_L` is an isogeny for every ample `L`, from L1, L2 and the torsion leaf** (no Weil-pairing leaf). -/
theorem phiAmpleIsogeny_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (hT : AvSplit.MumfordTorsionAlgClosed) : PhiAmpleIsogeny := by
  intro K _ A P rep B j hj L hL lam hlam
  obtain ⟨lam', hlam'⟩ := exists_hom_comp_eq_phiL rep hj L
  have hjm : Mono j := by
    have : IsOpenImmersion j.left := hj.1
    exact (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have he : lam = lam'.hom := by rw [← cancel_mono j, hlam, hlam']
  subst he
  have hfin := finiteOfFiniteKerPts K A B lam' (PhiAmple.finite_ker_pts rep hj hL hlam)
  refine ⟨hfin, ⟨?_⟩⟩
  have := hfin
  have : IsProper (lam'.hom.left ≫ B.X.hom) := by rw [Over.w lam'.hom]; infer_instance
  have : IsProper lam'.hom.left := IsProper.of_comp lam'.hom.left B.X.hom
  have : IrreducibleSpace B.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := B.X.hom)
  have : Nonempty A.X.left := ⟨η[A.X].left (IsLocalRing.closedPoint K)⟩
  obtain ⟨a, ha⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨b, hb⟩ := PkgI3.AbVar.dim_finite B
  have hba := dim_le_of_open h1 h2 hT rep hj a b ha hb
  refine surjective_of_dim_le lam'.hom.left lam'.hom.left.isClosedMap a ha ?_
  have hb' : topologicalKrullDim B.X.left = b := hb
  rw [hb']
  exact_mod_cast hba

end PhiSurj

#print axioms PhiSurj.AVDesc.formula_nondeg_right
#print axioms PhiSurj.AVDesc.card_isDT_le
#print axioms PhiSurj.phiAmpleIsogeny_of_open
