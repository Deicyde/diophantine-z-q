
/-! ## §11. `QMDescentCM` replaced by the kernel's rigidity leaf T11b and a CM-descent leaf

Route: base change `P ↦ P_ℂ` of QM pairs (`bcPair`), with `End` and isomorphisms controlled by the
kernel's textbook leaf `ZInQ.LeafPush2.T11b_Rigidity` (`Hom_ℚ̄ = Hom_ℂ`), and the leaf `CMDescent`
(a QM pair over `ℂ` with CM by `R` is isomorphic to the base change of one over `ℚ̄`). -/

namespace ZInQ.HeightGlue.QM

open LeafQM LeafQM.AV NumberField ZInQ.HeightSplit.R5
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (copied verbatim from alg-frob-red's copy of bp-qmmoduli's
`endBC`, `scratch/alg-frob-red/AlgFrobRed.lean` l. 1592-1618). -/
noncomputable def endBC (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl

end BaseChangeEnd

section Descent

variable [Algebra Qbar ℂ]

/-- `Over.pullback (Spec ℂ → Spec ℚ̄)`. -/
noncomputable abbrev bcF :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))

open scoped CategoryTheory.Obj in
theorem bcF_isMonHom {A B : PkgI3.AbVar Qbar} (f : A.X ⟶ B.X) [IsMonHom f] :
    IsMonHom (M := (A.baseChange ℂ).X) (N := (B.baseChange ℂ).X) (bcF.map f) :=
  Functor.map.instIsMonHom (F := bcF) (f := f)

theorem bc_unique (hT : ZInQ.LeafPush2.T11b_Rigidity) {A B : PkgI3.AbVar Qbar}
    {φ₁ φ₂ : A.X ⟶ B.X} [IsMonHom φ₁] [IsMonHom φ₂] (h : bcF.map φ₁ = bcF.map φ₂) : φ₁ = φ₂ := by
  obtain ⟨φ, -, hφ⟩ := hT Qbar ℂ A B (bcF.map φ₁) (bcF_isMonHom φ₁)
  exact (hφ φ₁ ⟨inferInstance, rfl⟩).trans (hφ φ₂ ⟨inferInstance, h.symm⟩).symm

theorem bc_exists (hT : ZInQ.LeafPush2.T11b_Rigidity) {A B : PkgI3.AbVar Qbar}
    (ψ : (A.baseChange ℂ).X ⟶ (B.baseChange ℂ).X) [IsMonHom ψ] :
    ∃ φ : A.X ⟶ B.X, IsMonHom φ ∧ bcF.map φ = ψ :=
  (hT Qbar ℂ A B ψ inferInstance).exists

theorem endBC_injective (hT : ZInQ.LeafPush2.T11b_Rigidity) (A : PkgI3.AbVar Qbar) :
    Function.Injective (endBC A ℂ) := fun f g h =>
  PkgI3.AbVar.Hom.ext' (bc_unique hT (congrArg PkgI3.AbVar.Hom.hom h))

/-- **The base change `P_ℂ` of a QM pair over `ℚ̄`.** -/
noncomputable def bcPair (hT : ZInQ.LeafPush2.T11b_Rigidity) (P : QMPair Qbar) : QMPair ℂ where
  A := P.A.baseChange ℂ
  surface := by rw [PkgI3.AbVar.dim_baseChange]; exact P.surface
  q := ⟨(endBC P.A ℂ).comp P.q.iota, (endBC_injective hT P.A).comp P.q.injective⟩

open scoped CategoryTheory.Obj in
/-- Base change of homomorphisms. -/
noncomputable def homBC {A B : PkgI3.AbVar Qbar} (f : PkgI3.AbVar.Hom A B) :
    PkgI3.AbVar.Hom (A.baseChange ℂ) (B.baseChange ℂ) :=
  @PkgI3.AbVar.Hom.mk' ℂ _ (A.baseChange ℂ) (B.baseChange ℂ) (bcF.map f.hom) (bcF_isMonHom f.hom)

/-- **(b′) `End_𝒪(P_ℂ) ≅ End_𝒪(P)`** (rigidity). -/
theorem nonempty_com_bc (hT : ZInQ.LeafPush2.T11b_Rigidity) (P : QMPair Qbar) :
    Nonempty (com (bcPair hT P).q ≃+* com P.q) := by
  have hmem : ∀ x ∈ com P.q, (endBC P.A ℂ x : (bcPair hT P).A.End) ∈ com (bcPair hT P).q := by
    intro x hx
    rw [com, Subring.mem_centralizer_iff] at hx
    apply Subring.mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    show endBC P.A ℂ (P.q.iota a) * endBC P.A ℂ x = endBC P.A ℂ x * endBC P.A ℂ (P.q.iota a)
    rw [← map_mul, ← map_mul, hx _ ⟨a, rfl⟩]
  let f : com P.q →+* com (bcPair hT P).q :=
    { toFun := fun x => ⟨endBC P.A ℂ x, hmem x x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  have hinj : Function.Injective f := fun x y h =>
    Subtype.ext (endBC_injective hT P.A (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨φ, hφ, hφy⟩ := @bc_exists _ hT P.A P.A y.hom (Additive.toMul y).2
    haveI := hφ
    let x : PkgI3.AbVar.End P.A := PkgI3.AbVar.Hom.mk' φ
    have hxy : endBC P.A ℂ x = y := PkgI3.AbVar.Hom.ext' hφy
    have hx : x ∈ com P.q := by
      apply Subring.mem_centralizer_iff.mpr
      rintro _ ⟨a, rfl⟩
      apply endBC_injective hT P.A
      rw [map_mul, map_mul, hxy]
      exact Subring.mem_centralizer_iff.mp hy _ ⟨a, rfl⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact ⟨(RingEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

/-- **(c′) `P_ℂ ≅ P'_ℂ` iff `P ≅ P'`** (functoriality and rigidity). -/
theorem nonempty_qmIso_bc_iff (hT : ZInQ.LeafPush2.T11b_Rigidity) (P P' : QMPair Qbar) :
    Nonempty (QMIso (bcPair hT P).q (bcPair hT P').q) ↔ Nonempty (QMIso P.q P'.q) := by
  constructor
  · rintro ⟨g⟩
    obtain ⟨φ, hφ, hφg⟩ := @bc_exists _ hT P.A P'.A g.φ.hom (Additive.toMul g.φ).2
    obtain ⟨ψ, hψ, hψg⟩ := @bc_exists _ hT P'.A P.A g.ψ.hom (Additive.toMul g.ψ).2
    haveI := hφ; haveI := hψ
    refine ⟨⟨PkgI3.AbVar.Hom.mk' φ, PkgI3.AbVar.Hom.mk' ψ, ?_, ?_, ?_⟩⟩
    · apply bc_unique hT
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
      simp only [PkgI3.AbVar.Hom.hom_mk', hφg, hψg]
      exact g.left
    · apply bc_unique hT
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
      simp only [PkgI3.AbVar.Hom.hom_mk', hφg, hψg]
      exact g.right
    · intro a
      apply bc_unique hT
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      simp only [PkgI3.AbVar.Hom.hom_mk', hφg]
      exact g.equivariant a
  · rintro ⟨f⟩
    refine ⟨⟨homBC f.φ, homBC f.ψ, ?_, ?_, ?_⟩⟩
    · show bcF.map f.φ.hom ≫ bcF.map f.ψ.hom = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, f.left, CategoryTheory.Functor.map_id]
    · show bcF.map f.ψ.hom ≫ bcF.map f.φ.hom = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, f.right, CategoryTheory.Functor.map_id]
    · intro a
      show bcF.map (P.q.iota a).hom ≫ bcF.map f.φ.hom = bcF.map f.φ.hom ≫ bcF.map (P'.q.iota a).hom
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, f.equivariant a]

end Descent

/-- **LEAF `CMDescent`** (abelian varieties with complex multiplication, and their endomorphisms,
are defined over `ℚ̄`: G. Shimura, Y. Taniyama, *Complex multiplication of abelian varieties*
(1961), §12.4 Prop. 26 / Shimura 1998, locators UNVERIFIED; with the kernel's rigidity
`T11b_Rigidity` for `ι`). For an embedding `ℚ̄ → ℂ`: a QM pair `(A, ι)` over `ℂ` whose `End_𝒪` is an
imaginary quadratic order `R` (conductor prime to `6`) is isomorphic, compatibly with `ι`, to the
base change `(P.A)_ℂ` of a QM pair `P` over `ℚ̄` with its base-changed `ι`. Stated with the
homomorphisms `φ`, `ψ` (inverse to each other) and the base change `endBC` of `ι`. Also bundled
(standard; independent review, RISK): the classification of endomorphism algebras of abelian
surfaces (Albert; Mumford, *Abelian varieties* §21, UNVERIFIED), which turns `End_𝒪 ≅ R` into CM
(`A ~ E²`, `E` with CM by a field splitting `B`); alternatively Shioda–Mitani 1974. -/
def CMDescent : Prop :=
  ∀ (ε : Qbar →+* ℂ), letI : Algebra Qbar ℂ := ε.toAlgebra;
    ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
    ∀ Q : QMPair ℂ, Nonempty (com Q.q ≃+* R) →
      ∃ (P : QMPair Qbar) (φ : PkgI3.AbVar.Hom (P.A.baseChange ℂ) Q.A)
        (ψ : PkgI3.AbVar.Hom Q.A (P.A.baseChange ℂ)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (endBC P.A ℂ (P.q.iota a)).hom ≫ φ.hom = φ.hom ≫ (Q.q.iota a).hom

/-- **Descent of classes from T11b and `CMDescent`**: `QMClasses k R ≃ QMClassesC k R`. -/
theorem nonempty_qmClasses_equiv_t11b (hT : ZInQ.LeafPush2.T11b_Rigidity) (hCM : CMDescent)
    (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k]
    (hk : Module.finrank ℚ k = 2) (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (conductor R) 6) :
    Nonempty (QMClasses k R ≃ QMClassesC k R) := by
  classical
  let ε : Qbar →+* ℂ := (IsAlgClosed.lift : Qbar →ₐ[ℚ] ℂ).toRingHom
  letI : Algebra Qbar ℂ := ε.toAlgebra
  let f : Quotient (pairSetoid Qbar) → Quotient (pairSetoid ℂ) :=
    Quotient.lift (fun P => Quotient.mk (pairSetoid ℂ) (bcPair hT P)) (fun P P' hPP' =>
      Quotient.sound ((nonempty_qmIso_bc_iff hT P P').mpr hPP'))
  have hf : ∀ P, f (Quotient.mk _ P) = Quotient.mk _ (bcPair hT P) := fun P => rfl
  have hfi : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with | h P => ?_
    induction y using Quotient.inductionOn with | h P' => ?_
    rw [hf, hf] at hxy
    exact Quotient.sound ((nonempty_qmIso_bc_iff hT P P').mp (Quotient.exact hxy))
  let F : QMClasses k R → QMClassesC k R := fun c => ⟨f c.1, by
    obtain ⟨P, hP, ⟨e⟩⟩ := c.2
    obtain ⟨e'⟩ := nonempty_com_bc hT P
    exact ⟨bcPair hT P, by rw [← hP, hf], ⟨e'.trans e⟩⟩⟩
  refine ⟨Equiv.ofBijective F ⟨fun c d hcd => Subtype.ext (hfi (congrArg Subtype.val hcd)), ?_⟩⟩
  rintro ⟨c', Q, hQ, ⟨e⟩⟩
  obtain ⟨P, φ, ψ, hl, hr, heq⟩ := hCM ε k hk R hR hc Q ⟨e⟩
  have hiso : QMIso (bcPair hT P).q Q.q := ⟨φ, ψ, hl, hr, heq⟩
  obtain ⟨e'⟩ := nonempty_com_bc hT P
  refine ⟨⟨Quotient.mk _ P, P, rfl, ⟨e'.symm.trans ((comEquiv hiso).trans e)⟩⟩, Subtype.ext ?_⟩
  show f (Quotient.mk _ P) = c'
  rw [hf, ← hQ]
  exact Quotient.sound ⟨hiso⟩

/-- **height-split's glue `QMPairEmbeddingCorrespondence` from the kernel's T11b, `CMDescent` and
`QMUniformizationC`** (proved). -/
theorem qmPairEmbeddingCorrespondence_of_t11b (hT : ZInQ.LeafPush2.T11b_Rigidity)
    (hCM : CMDescent) (hU : QMUniformizationC) : QMPairEmbeddingCorrespondence := by
  intro k _ _ _ hk R hR hc
  obtain ⟨e₁⟩ := nonempty_qmClasses_equiv_t11b hT hCM k hk R hR hc
  obtain ⟨e₂⟩ := nonempty_qmClassesC_equiv k hU R
  obtain ⟨e₃⟩ := cmPointEmbeddingCorrespondence k hk R hR hc
  exact ⟨(e₁.trans e₂).trans e₃⟩

/-- **The row H-3 (`R5fpCount`) from Eichler's count, T11b, `CMDescent` and `QMUniformizationC`.** -/
theorem r5fpCount_of_t11b (hE : EichlerOptimalEmbeddingCount) (hT : ZInQ.LeafPush2.T11b_Rigidity)
    (hCM : CMDescent) (hU : QMUniformizationC) : LeafQM.AV.R5fpCount :=
  r5fpCount_of hE (qmPairEmbeddingCorrespondence_of_t11b hT hCM hU)

end ZInQ.HeightGlue.QM
