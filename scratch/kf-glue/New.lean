
/-! # kf-glue, part 1: `EndTransport` (scratch/kernel-field/New.lean, statement unchanged)

`EndTransport` is defined above (verbatim from scratch/kernel-field). kernel-field proved
`endTransport_of : EndTransportBC → EndTransport` and
`endTransportBC_of_rigidity : RigidityHom → EndTransportBC`; mul-rigidity proved `RigidityHom`
from Mathlib (`MulRigidity.isMonHom_of_geometricallyIntegral`). -/

section KfGlueEndTransport

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`RigidityHom` holds** (mul-rigidity's proof, verbatim apart from the name). -/
theorem G0FibreSimple.rigidityHom : G0FibreSimple.RigidityHom := fun _ _ A B h h0 =>
  MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X h h0

/-- **`EndTransport` is a theorem** (no hypotheses). -/
theorem G0ModField.KernelField.endTransport : G0ModField.KernelField.EndTransport :=
  G0ModField.KernelField.endTransport_of
    (G0ModField.KernelField.endTransportBC_of_rigidity G0FibreSimple.rigidityHom)

/-- `KernelFieldExists` with `RigidityHom` discharged: five leaves and two glue Props. -/
theorem G0ModField.KernelField.kernelFieldExists_of_five (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hG : G0ModField.KernelField.ConjIsogMaps) :
    G0ModField.KernelFieldExists :=
  G0ModField.KernelField.kernelFieldExists_of_rigidity hHFF hNOS hRay hTors t27
    G0FibreSimple.rigidityHom h5 hG

end KfGlueEndTransport


#print axioms G0ModField.KernelField.endTransport
#print axioms G0ModField.KernelField.kernelFieldExists_of_five

/-! # kf-glue, part 2: `ConjIsogMaps`, level 1 — the points bookkeeping (proved)

`ConjIsogMaps` (verbatim above, from scratch/kernel-field) asks for maps `m_σ` on `A_L(ℚ̄)`. We
prove it from `SemilinearIsogMaps`, the same statement one level down: σ-semilinear finite
surjective scheme endomorphisms `F_σ` of `A_L` (the conjugacy isogenies `μ_σ` composed with the
identification of `^σA_L` and `A_L` as schemes), respecting the group law and the `𝒪`-action,
inflated from `Gal(L/ℚ)`, with discrepancy in `End_L(A_L)` up to an integer; plus two general
glue facts about `ℚ̄`-points of finite morphisms. Then `m_σ(x) = F_σ ∘ x ∘ Spec σ`. -/

section KfGlueLevel1

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-- **Glue (general scheme theory; Stacks, finite morphisms and points over algebraically closed
fields).** A finite surjective morphism of schemes is surjective on `ℚ̄`-points: the fibre over the
image point `y` of `Spec ℚ̄ → Y` is nonempty, and for `x` in it `κ(x)/κ(y)` is algebraic, so the
embedding `κ(y) → ℚ̄` extends to `κ(x)` (`ℚ̄` algebraically closed). -/
def LiftQbarPoints : Prop :=
  ∀ (X Y : Scheme.{0}) (F : X ⟶ Y), IsFinite F → Surjective F →
    ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y, ∃ x : Spec (CommRingCat.of Qbar) ⟶ X, x ≫ F = y

/-- **Glue (general scheme theory).** The `ℚ̄`-points of `X` over a fixed `ℚ̄`-point of `Y` under a
finite morphism form a finite set: the fibre is finite and each `κ(x)/κ(y)` is a finite extension,
which has finitely many `κ(y)`-embeddings into `ℚ̄`. -/
def FiniteFibreQbarPoints : Prop :=
  ∀ (X Y : Scheme.{0}) (F : X ⟶ Y), IsFinite F →
    ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y,
      {x : Spec (CommRingCat.of Qbar) ⟶ X | x ≫ F = y}.Finite

/-- **The σ-semilinear conjugacy isogenies on `A/L` (geometric clauses).** For each `σ ∈ G_ℚ` a
morphism of schemes `F_σ : A → A` with:
* `F_σ` lies over `Spec(σ⁻¹|_L)` on `Spec L` and respects the group law (it is `μ_σ ∘ c_σ`,
  `c_σ : A ≅ ^σA` the identification of underlying schemes, `μ_σ : ^σA → A` a homomorphism);
* `F_σ` commutes with `ι'(𝒪)` (`μ_σ` is `𝒪`-linear: A7 + Skolem–Noether);
* `F_σ` is finite and surjective (`μ_σ` an isogeny);
* `F_k = id` for `k ∈ G_L` and `F` is constant on double cosets of `G_L` (`μ` inflated from
  `Gal(L/ℚ)`, defined over `L`);
* `F_τ ≫ F_σ ≫ [e] = F_{στ} ≫ δ` with `e ≠ 0` and `δ ∈ End_L(A)` (`δ = μ_σ ^σμ_τ ψ_{στ}` with
  `ψ_{στ} μ_{στ} = [e]` a quasi-inverse, Mumford §8). -/
def SemilinearIsogAt (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (F : GQ → (A.X.left ⟶ A.X.left)) : Prop :=
  ∀ σ : GQ,
    (∃ τ : L ≃+* L, (∀ x : L, (τ x : Qbar) = act σ⁻¹ x) ∧
      ∃ hτ : F σ ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ F σ =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom (F σ) (F σ)
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ F σ = F σ ≫ (ι' a).hom.left) ∧
    IsFinite (F σ) ∧ Surjective (F σ) ∧
    (∀ k ∈ GQL L, F k = 𝟙 _ ∧ F (σ * k) = F σ ∧ F (k * σ) = F σ) ∧
    (∀ τ : GQ, ∃ e : ℤ, e ≠ 0 ∧ ∃ δ : PkgI3.AbVar.End A,
      F τ ≫ F σ ≫ (e : PkgI3.AbVar.End A).hom.left = F (σ * τ) ≫ δ.hom.left)

/-- **`ConjIsogMaps` one level down (geometric glue).** Same context as `ConjIsogMaps`; asks for
the σ-semilinear isogenies `F_σ` of `SemilinearIsogAt` on `A_L` for `ι_L = endBC ∘ PK.q.iota`. -/
def SemilinearIsogMaps : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ F : GQ → ((@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left ⟶
            (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left),
          SemilinearIsogAt L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
            ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) F

/-- `Spec σ` for `σ ∈ G_ℚ`. -/
noncomputable abbrev specA (σ : GQ) : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of Qbar) :=
  Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar))

theorem specA_mul (σ τ : GQ) : specA (σ * τ) = specA σ ≫ specA τ := by
  rw [specA, specA, specA, ← Spec.map_comp]; rfl

theorem specA_one : specA 1 = 𝟙 _ := by
  rw [specA, ← Spec.map_id]; rfl

theorem specA_inv (σ : GQ) : specA σ ≫ specA σ⁻¹ = 𝟙 _ := by
  rw [← specA_mul, mul_inv_cancel, specA_one]

theorem specA_inv' (σ : GQ) : specA σ⁻¹ ≫ specA σ = 𝟙 _ := by
  rw [← specA_mul, inv_mul_cancel, specA_one]

instance (σ : GQ) : IsIso (specA σ) := ⟨⟨specA σ⁻¹, specA_inv σ, specA_inv' σ⟩⟩

section Pts

variable {L : IF} (A : PkgI3.AbVar L)

/-- The underlying morphism `Spec ℚ̄ → A` of a point. -/
noncomputable def ptl (x : A.Pt Qbar) : Spec (CommRingCat.of Qbar) ⟶ A.X.left := x.left

theorem ptl_w (x : A.Pt Qbar) :
    ptl A x ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := Over.w x

theorem ptl_ext {x y : A.Pt Qbar} (h : ptl A x = ptl A y) : x = y := Over.OverMorphism.ext h

theorem ptl_mul (x y : A.Pt Qbar) :
    ptl A (x * y) = pullback.lift (ptl A x) (ptl A y) ((ptl_w A x).trans (ptl_w A y).symm) ≫
      μ[A.X].left := by
  unfold ptl
  rw [Hom.mul_def, Over.comp_left, Over.lift_left]
  exact rfl

/-- The group-law clause for a semilinear `G` over `Spec τ`. -/
def SemMul (τ : L ≃+* L) (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L))) : Prop :=
  μ[A.X].left ≫ G =
    pullback.map A.X.hom A.X.hom A.X.hom A.X.hom G G
      (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hG.symm hG.symm ≫ μ[A.X].left

/-- The image of a point under a σ-semilinear map. -/
noncomputable def semPt (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (x : A.Pt Qbar) : A.Pt Qbar :=
  Over.homMk (specA σ ≫ ptl A x ≫ G) (by
    have hw : (specA σ ≫ ptl A x ≫ G) ≫ A.X.hom =
        Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
      rw [Category.assoc, Category.assoc, hG, ← Category.assoc (ptl A x), ptl_w, specA,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext z
      change act σ ((τ z : L) : Qbar) = (z : Qbar)
      rw [hτσ z, ← act_mul, mul_inv_cancel]; rfl
    exact hw)

theorem semPt_ptl (σ : GQ) (τ : L ≃+* L) (hτσ) (G : A.X.left ⟶ A.X.left) (hG)
    (x : A.Pt Qbar) : ptl A (semPt A σ τ hτσ G hG x) = specA σ ≫ ptl A x ≫ G := rfl

theorem semPt_mul (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (hμ : SemMul A τ G hG) (x y : A.Pt Qbar) :
    semPt A σ τ hτσ G hG (x * y) = semPt A σ τ hτσ G hG x * semPt A σ τ hτσ G hG y := by
  apply ptl_ext
  have hμ' : μ[A.X].left ≫ G = pullback.map A.X.hom A.X.hom A.X.hom A.X.hom G G
      (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hG.symm hG.symm ≫ μ[A.X].left := hμ
  rw [semPt_ptl, ptl_mul, ptl_mul, Category.assoc, hμ', ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [semPt_ptl]
  · simp [semPt_ptl]

/-- `semPt` as a group homomorphism of `A(ℚ̄)`. -/
noncomputable def semHom (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (hμ : SemMul A τ G hG) : PtQ L A →+ PtQ L A :=
  MonoidHom.toAdditive (MonoidHom.mk' (semPt A σ τ hτσ G hG) (semPt_mul A σ τ hτσ G hG hμ))

/-- The underlying morphism of a point of `PtQ`. -/
noncomputable abbrev ptq (x : PtQ L A) : Spec (CommRingCat.of Qbar) ⟶ A.X.left := ptl A (Additive.toMul x)

theorem ptq_ext {x y : PtQ L A} (h : ptq A x = ptq A y) : x = y :=
  Additive.toMul.injective (ptl_ext A h)

theorem semHom_ptq (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (hμ : SemMul A τ G hG) (x : PtQ L A) :
    ptq A (semHom A σ τ hτσ G hG hμ x) = specA σ ≫ ptq A x ≫ G := rfl

theorem endPt_ptq (f : PkgI3.AbVar.End A) (x : PtQ L A) :
    ptq A (endPt A Qbar f x) = ptq A x ≫ f.hom.left := rfl

theorem zsmul_ptq (e : ℤ) (x : PtQ L A) :
    ptq A (e • x) = ptq A x ≫ (e : PkgI3.AbVar.End A).hom.left := by
  have h1 : endPt A Qbar (e : PkgI3.AbVar.End A) x = e • x := by
    rw [map_intCast, AddMonoid.End.intCast_apply]
  rw [← h1, endPt_ptq]

theorem galAct_ptq (σ' : Qbar ≃ₐ[L] Qbar) (x : PtQ L A) :
    ptq A (MonoidHom.toAdditive (A.galAct σ') x) =
      Spec.map (CommRingCat.ofHom (σ' : Qbar →+* Qbar)) ≫ ptq A x := rfl

end Pts

/-- **Level 1 (proved): the points bookkeeping.** σ-semilinear isogenies on `A/L` give the maps
`m_σ(x) = F_σ ∘ x ∘ Spec σ` with all clauses of `ConjIsogMapsAt`. -/
theorem conjIsogMapsAt_of_semilinear (hLift : LiftQbarPoints) (hFib : FiniteFibreQbarPoints)
    (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (F : GQ → (A.X.left ⟶ A.X.left)) (hF : SemilinearIsogAt L A ι' F) :
    ∃ m : GQ → (PtQ L A →+ PtQ L A), ConjIsogMapsAt L A ι' m := by
  choose τ hτσ hτ hμ using fun σ => (hF σ).1
  let m : GQ → (PtQ L A →+ PtQ L A) := fun σ => semHom A σ (τ σ) (hτσ σ) (F σ) (hτ σ) (hμ σ)
  have hm : ∀ σ x, ptq A (m σ x) = specA σ ≫ ptq A x ≫ F σ := fun σ x => rfl
  refine ⟨m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- clause 1: the Galois action on `G_L`
    intro σ σ' hσ'
    have hσL : σ ∈ GQL L := mem_GQL.mpr fun x hx => by
      rw [← hσ' x]; exact σ'.commutes ⟨x, hx⟩
    refine AddMonoidHom.ext fun x => ptq_ext A ?_
    have hσσ : specA σ = Spec.map (CommRingCat.ofHom (σ' : Qbar →+* Qbar)) := by
      rw [specA]; congr 1; ext z; exact (hσ' z).symm
    rw [hm, galAct_ptq, ((hF σ).2.2.2.2.1 σ hσL).1, Category.comp_id, hσσ]
  · -- clause 2: inflation
    intro σ k hk
    obtain ⟨h1, h2, h3⟩ := (hF σ).2.2.2.2.1 k hk
    refine ⟨AddMonoidHom.ext fun x => ptq_ext A ?_, AddMonoidHom.ext fun x => ptq_ext A ?_⟩
    · show ptq A (m (σ * k) x) = ptq A (m σ (m k x))
      rw [hm, hm, hm, h2, h1, specA_mul]
      simp only [Category.assoc, Category.comp_id]
    · show ptq A (m (k * σ) x) = ptq A (m k (m σ x))
      rw [hm, hm, hm, h3, h1, specA_mul]
      simp only [Category.assoc, Category.comp_id]
  · -- clause 3: `𝒪`-linearity
    intro σ a
    refine AddMonoidHom.ext fun x => ptq_ext A ?_
    show ptq A (m σ (endPt A Qbar (ι' a) x)) = ptq A (endPt A Qbar (ι' a) (m σ x))
    rw [hm, endPt_ptq, endPt_ptq, hm]
    simp only [Category.assoc]
    rw [(hF σ).2.1 a]
  · -- clause 4: surjective with finite kernel
    intro σ
    obtain ⟨-, -, hfin, hsurj, -, -⟩ := hF σ
    refine ⟨fun y => ?_, ?_⟩
    · obtain ⟨x', hx'⟩ := hLift _ _ (F σ) hfin hsurj (ptq A y)
      have hiso : IsIso (Spec.map (CommRingCat.ofHom ((τ σ : L ≃+* L) : L →+* L))) :=
        ⟨⟨Spec.map (CommRingCat.ofHom ((τ σ).symm : L →+* L)), by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z; simp,
          by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z;
             simp⟩⟩
      have hy : x' ≫ A.X.hom ≫ Spec.map (CommRingCat.ofHom ((τ σ : L ≃+* L) : L →+* L)) =
          Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
        rw [← hτ σ, ← Category.assoc, hx']; exact ptl_w A _
      have hx'' : x' ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫
          inv (Spec.map (CommRingCat.ofHom ((τ σ : L ≃+* L) : L →+* L))) := by
        rw [← hy]; simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have hw : (specA σ⁻¹ ≫ x') ≫ A.X.hom =
          Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
        rw [Category.assoc, hx'', ← Category.assoc, IsIso.comp_inv_eq, specA, ← Spec.map_comp,
          ← Spec.map_comp]
        congr 1
        ext z
        change act σ⁻¹ (z : Qbar) = ((τ σ z : L) : Qbar)
        rw [hτσ σ z]
      refine ⟨Additive.ofMul (Over.homMk (specA σ⁻¹ ≫ x') hw), ptq_ext A ?_⟩
      rw [hm]
      change specA σ ≫ (specA σ⁻¹ ≫ x') ≫ F σ = _
      rw [← Category.assoc, ← Category.assoc, specA_inv, Category.id_comp, hx']
    · have hsub : ((m σ).ker : Set (PtQ L A)) ⊆
          (fun x : PtQ L A => specA σ ≫ ptq A x) ⁻¹'
            {x' | x' ≫ F σ = ptq A (0 : PtQ L A)} := by
        intro x hx
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at hx
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        rw [Category.assoc, ← hm, hx]
      refine Set.Finite.subset (Set.Finite.preimage ?_ (hFib _ _ (F σ) hfin _)) hsub
      intro x _ x₂ _ h
      exact ptq_ext A ((cancel_epi (specA σ)).mp h)
  · -- clause 5: the discrepancy
    intro σ τ'
    obtain ⟨e, he, δ, hδ⟩ := (hF σ).2.2.2.2.2 τ'
    refine ⟨e, he, δ, AddMonoidHom.ext fun x => ptq_ext A ?_⟩
    show ptq A (e • m σ (m τ' x)) = ptq A (endPt A Qbar δ (m (σ * τ') x))
    rw [zsmul_ptq, endPt_ptq, hm, hm, hm, specA_mul]
    simp only [Category.assoc]
    rw [hδ]
  · -- clause 6: algebraicity
    exact ⟨F, fun σ => ⟨(hF σ).2.2.1, (hF σ).2.2.2.1, fun x => hm σ x⟩⟩

/-- **`ConjIsogMaps` from `SemilinearIsogMaps` and the two point lemmas (proved).** -/
theorem conjIsogMaps_of_semilinear (hLift : LiftQbarPoints) (hFib : FiniteFibreQbarPoints)
    (h : SemilinearIsogMaps) : ConjIsogMaps := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨F, hF⟩ := h Y Φ π hR1 hR2 j₀ y P hy hπ K PK hPK L hKL hfix
  exact conjIsogMapsAt_of_semilinear hLift hFib L _ _ F hF

/-- **`LiftQbarPoints` holds** (proved from Mathlib, `scratch/kf-glue/Points.lean`: the pullback of
`F` along `y` is a nonempty finite scheme `Spec B` over `Spec ℚ̄`; a maximal quotient of `B` is a
finite field extension of `ℚ̄`, hence `ℚ̄`, giving a section). -/
theorem liftQbarPoints : LiftQbarPoints := fun X Y F hF hs y =>
  KfGluePoints.liftQbar X Y F hF hs y

/-- **`FiniteFibreQbarPoints` holds** (proved from Mathlib: the points over `y` inject into the
sections of the finite `Spec B → Spec ℚ̄`, i.e. into `B →ₐ[ℚ̄] ℚ̄`, finite by Mathlib's
`Finite.algHom`). -/
theorem finiteFibreQbarPoints : FiniteFibreQbarPoints := fun X Y F hF y =>
  KfGluePoints.finiteFibreQbar X Y F hF y

/-- **`ConjIsogMaps` from `SemilinearIsogMaps` alone (proved).** -/
theorem conjIsogMaps_of_semilinearIsogMaps (h : SemilinearIsogMaps) : ConjIsogMaps :=
  conjIsogMaps_of_semilinear liftQbarPoints finiteFibreQbarPoints h

/-- `KernelFieldExists` with `ConjIsogMaps` replaced by `SemilinearIsogMaps`. -/
theorem kernelFieldExists_of_semilinear (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hS : SemilinearIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_semilinearIsogMaps hS)

end G0ModField.KernelField

end KfGlueLevel1

/-! # kf-glue, part 3: `SemilinearIsogMaps`, level 2 — Skolem–Noether, the isogeny `ι(b)`, the
quasi-inverse and the discrepancy (proved)

`SemilinearIsogMaps` is proved from `SemilinearTwistIsos`: σ-semilinear scheme *automorphisms*
`E_σ` of `A/L` preserving the origin and the group law and twisting `ι` by some `α_σ ∈ Aut(𝒪)`
(A7's twisted QM isomorphisms `(A, ι∘α) ≅ (^σA, ^σι)`, descended to `L`), plus `MulIsogeny`
(mul-rigidity: from `KerUnitOpen` or two cotangent glue statements) and `RigidityHom` (proved).
Then `F_σ = E_σ ≫ ι(b_σ)` with `b_σ ∈ 𝒪` from Skolem–Noether (`aut_O_inner`), `ι(b)` is an isogeny
with quasi-inverse `ι(N b⁻¹)` (so no quasi-inverse leaf is needed), and the discrepancy is
`δ = ι(b_σ) ι(α_σ b_τ) D ι(c)` with `D = E_{στ}⁻¹ E_τ E_σ ∈ End_L(A)` (rigidity). -/

section KfGlueLevel2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

/- `G0FibreSimple.MulIsogeny` is in Part MR (MulRigidity.lean L321-323, verbatim). -/

namespace G0ModField.KernelField

open G0ModField

/-- **The core geometric glue: A7's twisted isomorphisms, descended to `L`, as σ-semilinear
automorphisms.** For each `σ ∈ G_ℚ` an automorphism `E_σ` of the scheme `A` lying over
`Spec(σ⁻¹|_L)`, preserving the group law and the origin, with `ι(a) E_σ = E_σ ι(α_σ a)` for an
`α_σ ∈ Aut(𝒪)`; `E_k = id`, `α_k = id` on `G_L`, and `E`, `α` constant on cosets of `G_L`. -/
def SemilinearTwistAt (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (E : GQ → (A.X.left ⟶ A.X.left)) (α : GQ → (O ≃+* O)) : Prop :=
  ∀ σ : GQ,
    IsIso (E σ) ∧
    (∃ τ : L ≃+* L, (∀ x : L, (τ x : Qbar) = act σ⁻¹ x) ∧
      ∃ hτ : E σ ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ E σ =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom (E σ) (E σ)
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left ∧
        η[A.X].left ≫ E σ = Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ η[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ E σ = E σ ≫ (ι' (α σ a)).hom.left) ∧
    (∀ k ∈ GQL L, E k = 𝟙 _ ∧ α k = RingEquiv.refl O ∧ E (σ * k) = E σ ∧ E (k * σ) = E σ ∧
      α (σ * k) = α σ ∧ α (k * σ) = α σ)

/-- **`SemilinearIsogMaps` one level down (geometric glue).** Same context as `ConjIsogMaps`. -/
def SemilinearTwistIsos : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ (E : GQ → ((@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left ⟶
            (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left)) (α : GQ → (O ≃+* O)),
          SemilinearTwistAt L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
            ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) E α

/-! ### Algebra in `𝒪` -/

/-- Skolem–Noether, linear form: for `α ∈ Aut 𝒪` there is `b ≠ 0` with `b α(a) = a b`. -/
theorem exists_b (α : O ≃+* O) : ∃ b : O, b ≠ 0 ∧ ∀ a : O, b * α a = a * b := by
  obtain ⟨u, hu⟩ := aut_O_inner α
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O ((u⁻¹ : Bˣ) : B)
  let b : O := ⟨(N : B) * (u⁻¹ : Bˣ), hmem⟩
  refine ⟨b, fun hb => ?_, fun a => ?_⟩
  · have h0 := congrArg Subtype.val hb
    change (N : B) * (u⁻¹ : Bˣ) = 0 at h0
    have h1 := congrArg (· * (u : B)) h0
    simp only [_root_.mul_assoc, Units.inv_mul, _root_.mul_one, zero_mul] at h1
    have h2 := congrArg QuaternionAlgebra.re h1
    simp at h2
    omega
  · apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, hu a]
    show (N : B) * (u⁻¹ : Bˣ) * (u * a * (u⁻¹ : Bˣ)) = a * ((N : B) * (u⁻¹ : Bˣ))
    have hc : ((u⁻¹ : Bˣ) : B) * (u * a * (u⁻¹ : Bˣ)) = a * (u⁻¹ : Bˣ) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [_root_.mul_assoc, hc, ← _root_.mul_assoc, (Nat.cast_commute N (a : B)).eq,
      _root_.mul_assoc]

/-- A quasi-inverse in `𝒪`: for `b ≠ 0` there are `c` and `N > 0` with `c b = N = b c`. -/
theorem exists_quasi_inv {b : O} (hb : b ≠ 0) :
    ∃ c : O, ∃ N : ℕ, 0 < N ∧ c * b = (N : O) ∧ b * c = (N : O) := by
  have hb' : (b : B) ≠ 0 := fun h => hb (Subtype.ext h)
  obtain ⟨v, hv⟩ := G0FibreSimple.B6_isUnit (b : B) hb'
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O ((v⁻¹ : Bˣ) : B)
  refine ⟨⟨(N : B) * (v⁻¹ : Bˣ), hmem⟩, N, hN, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Subring.coe_mul]
    show (N : B) * (v⁻¹ : Bˣ) * b = ((N : O) : B)
    rw [← hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]; rfl
  · rw [Subring.coe_mul]
    show (b : B) * ((N : B) * (v⁻¹ : Bˣ)) = ((N : O) : B)
    rw [← hv, ← _root_.mul_assoc, (Nat.cast_commute N (v : B)).eq.symm, _root_.mul_assoc,
      Units.mul_inv, _root_.mul_one]; rfl

/-- **`ι(b)` is an isogeny for `b ≠ 0`** (from `MulIsogeny`; `ι(c) ι(b) = [N] = ι(b) ι(c)`). -/
theorem iota_isogeny (hMul : G0FibreSimple.MulIsogeny) {k : Type} [Field k] [CharZero k]
    {A : PkgI3.AbVar k} (ι' : O →+* PkgI3.AbVar.End A) {b : O} (hb : b ≠ 0) :
    IsFinite (ι' b).hom.left ∧ Surjective (ι' b).hom.left := by
  obtain ⟨c, N, hN, hcb, hbc⟩ := exists_quasi_inv hb
  have hNz : ((N : ℤ) : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨hfin, hsurj⟩ := hMul k A (N : ℤ) hNz
  have e1 : (ι' b).hom.left ≫ (ι' c).hom.left = ((N : ℤ) : PkgI3.AbVar.End A).hom.left := by
    have : ι' c * ι' b = ((N : ℤ) : PkgI3.AbVar.End A) := by
      rw [← map_mul, hcb, Int.cast_natCast, map_natCast]
    rw [← this]; rfl
  have e2 : (ι' c).hom.left ≫ (ι' b).hom.left = ((N : ℤ) : PkgI3.AbVar.End A).hom.left := by
    have : ι' b * ι' c = ((N : ℤ) : PkgI3.AbVar.End A) := by
      rw [← map_mul, hbc, Int.cast_natCast, map_natCast]
    rw [← this]; rfl
  refine ⟨?_, ?_⟩
  · have : IsFinite ((ι' b).hom.left ≫ (ι' c).hom.left) := by rw [e1]; exact hfin
    have : IsSeparated (ι' c).hom.left := by
      have : IsSeparated ((ι' c).hom.left ≫ A.X.hom) := by rw [Over.w]; infer_instance
      exact IsSeparated.of_comp (ι' c).hom.left A.X.hom
    exact IsFinite.of_comp (ι' b).hom.left (ι' c).hom.left
  · have hs : Surjective ((ι' c).hom.left ≫ (ι' b).hom.left) := by rw [e2]; exact hsurj
    refine ⟨fun z => ?_⟩
    obtain ⟨w, hw⟩ := ((ι' c).hom.left ≫ (ι' b).hom.left).surjective z
    exact ⟨(ι' c).hom.left w, by rw [← Scheme.Hom.comp_apply]; exact hw⟩

/-! ### The assembly -/

theorem spec_comp_spec {L : IF} (a b c : L ≃+* L) (h : ∀ x, c x = a (b x)) :
    Spec.map (CommRingCat.ofHom (a : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (b : L →+* L)) =
      Spec.map (CommRingCat.ofHom (c : L →+* L)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  show a (b x) = c x
  exact (h x).symm

/-- **Level 2 (proved).** `SemilinearTwistAt` + `MulIsogeny` + `RigidityHom` ⟹ `SemilinearIsogAt`. -/
theorem semilinearIsogAt_of_twist (hMul : G0FibreSimple.MulIsogeny)
    (hR : G0FibreSimple.RigidityHom) (L : IF) (A : PkgI3.AbVar L)
    (ι' : O →+* PkgI3.AbVar.End A) (E : GQ → (A.X.left ⟶ A.X.left)) (α : GQ → (O ≃+* O))
    (h : SemilinearTwistAt L A ι' E α) : ∃ F : GQ → (A.X.left ⟶ A.X.left), SemilinearIsogAt L A ι' F := by
  classical
  choose bOf hbOf0 hbOf using exists_b
  let b : GQ → O := fun σ => if α σ = RingEquiv.refl O then 1 else bOf (α σ)
  have hb0 : ∀ σ, b σ ≠ 0 := fun σ => by
    by_cases hσ : α σ = RingEquiv.refl O
    · simp only [b, hσ, ite_true]; exact O_nontrivial
    · simp only [b, hσ, ite_false]; exact hbOf0 _
  have hb : ∀ σ a, b σ * α σ a = a * b σ := fun σ a => by
    by_cases hσ : α σ = RingEquiv.refl O
    · simp only [b, hσ, ite_true, RingEquiv.refl_apply, _root_.one_mul, _root_.mul_one]
    · simp only [b, hσ, ite_false]; exact hbOf _ a
  choose hiso τ hτσ hτ hμ hη using fun σ => And.intro (h σ).1 (h σ).2.1
  have htw := fun σ => (h σ).2.2.1
  have hk := fun σ => (h σ).2.2.2
  let F : GQ → (A.X.left ⟶ A.X.left) := fun σ => E σ ≫ (ι' (b σ)).hom.left
  have hFτ : ∀ σ, F σ ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ σ : L →+* L)) :=
    fun σ => by
      simp only [F, Category.assoc]
      rw [Over.w (ι' (b σ)).hom, hτ σ]
  -- twist relation, pushed through `ι(x)`
  have htwx : ∀ σ (x : O), (ι' x).hom.left ≫ E σ = E σ ≫ (ι' (α σ x)).hom.left := fun σ x =>
    htw σ x
  -- composite of `ι`'s
  have hcomp : ∀ x y : O, (ι' x).hom.left ≫ (ι' y).hom.left = (ι' (y * x)).hom.left := by
    intro x y; rw [map_mul]; rfl
  refine ⟨F, fun σ => ⟨⟨τ σ, hτσ σ, hFτ σ, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- group law
    have hf : μ[A.X].left ≫ (ι' (b σ)).hom.left =
        ((ι' (b σ)).hom ⊗ₘ (ι' (b σ)).hom).left ≫ μ[A.X].left := by
      rw [← Over.comp_left, IsMonHom.mul_hom, Over.comp_left]
    show μ[A.X].left ≫ E σ ≫ (ι' (b σ)).hom.left = _
    rw [← Category.assoc, hμ σ, Category.assoc, hf, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp [F, Over.tensorHom_left]
    · simp [F, Over.tensorHom_left]
  · -- `𝒪`-linearity
    intro a
    show (ι' a).hom.left ≫ E σ ≫ (ι' (b σ)).hom.left = (E σ ≫ (ι' (b σ)).hom.left) ≫ (ι' a).hom.left
    rw [← Category.assoc, htwx, Category.assoc, Category.assoc, hcomp, hcomp, hb]
  · -- finite
    haveI := hiso σ
    haveI := (iota_isogeny hMul ι' (hb0 σ)).1
    show IsFinite (E σ ≫ (ι' (b σ)).hom.left)
    infer_instance
  · -- surjective
    haveI := hiso σ
    haveI := (iota_isogeny hMul ι' (hb0 σ)).2
    show Surjective (E σ ≫ (ι' (b σ)).hom.left)
    infer_instance
  · -- inflation from `Gal(L/ℚ)`
    intro k hkL
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk σ k hkL
    have hbk : b k = 1 := by simp only [b, h2, ite_true]
    have hbσk : b (σ * k) = b σ := by simp only [b, h5]
    have hbkσ : b (k * σ) = b σ := by simp only [b, h6]
    refine ⟨?_, ?_, ?_⟩
    · show E k ≫ (ι' (b k)).hom.left = 𝟙 _
      rw [h1, hbk, map_one, Category.id_comp]; rfl
    · show E (σ * k) ≫ (ι' (b (σ * k))).hom.left = E σ ≫ (ι' (b σ)).hom.left
      rw [h3, hbσk]
    · show E (k * σ) ≫ (ι' (b (k * σ))).hom.left = E σ ≫ (ι' (b σ)).hom.left
      rw [h4, hbkσ]
  · -- the discrepancy
    intro ρ
    haveI := hiso (σ * ρ)
    -- `E_ρ E_σ` lies over `Spec τ_{σρ}`
    have hsp : Spec.map (CommRingCat.ofHom (τ ρ : L →+* L)) ≫
        Spec.map (CommRingCat.ofHom (τ σ : L →+* L)) =
          Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L)) := by
      apply spec_comp_spec
      intro x
      apply Subtype.ext
      change ((τ (σ * ρ) x : L) : Qbar) = ((τ ρ (τ σ x) : L) : Qbar)
      rw [hτσ, hτσ, hτσ, mul_inv_rev, act_mul]
    haveI : IsIso (Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L))) :=
      ⟨⟨Spec.map (CommRingCat.ofHom ((τ (σ * ρ)).symm : L →+* L)), by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z; simp,
        by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z;
           simp⟩⟩
    let Dl : A.X.left ⟶ A.X.left := inv (E (σ * ρ)) ≫ E ρ ≫ E σ
    have hDw : Dl ≫ A.X.hom = A.X.hom := by
      have e1 : inv (E (σ * ρ)) ≫ A.X.hom =
          A.X.hom ≫ inv (Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L))) := by
        rw [IsIso.eq_comp_inv, Category.assoc, ← hτ, IsIso.inv_hom_id_assoc]
      simp only [Dl, Category.assoc]
      rw [hτ σ, reassoc_of% (hτ ρ), hsp, reassoc_of% e1, IsIso.inv_hom_id, Category.comp_id]
    let D : A.X ⟶ A.X := Over.homMk Dl hDw
    have hDη : η[A.X] ≫ D = η[A.X] := by
      apply Over.OverMorphism.ext
      have e2 : η[A.X].left ≫ inv (E (σ * ρ)) =
          inv (Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L))) ≫ η[A.X].left := by
        rw [IsIso.comp_inv_eq, Category.assoc, hη, IsIso.inv_hom_id_assoc]
      rw [Over.comp_left]
      show η[A.X].left ≫ inv (E (σ * ρ)) ≫ E ρ ≫ E σ = η[A.X].left
      rw [reassoc_of% e2, reassoc_of% (hη ρ), hη σ, reassoc_of% hsp, IsIso.inv_hom_id_assoc]
    haveI : IsMonHom D := hR L A A D hDη
    let Dm : PkgI3.AbVar.End A := PkgI3.AbVar.Hom.mk' D
    obtain ⟨c, N, hN, hcb, hbc⟩ := exists_quasi_inv (hb0 (σ * ρ))
    let Y : PkgI3.AbVar.End A := ι' (b σ) * ι' (α σ (b ρ)) * Dm
    refine ⟨(N : ℤ), by exact_mod_cast hN.ne', Y * ι' c, ?_⟩
    -- left side: `E_ρ ι(b_ρ) E_σ ι(b_σ) [N] = E_{σρ} D ι(α_σ b_ρ) ι(b_σ) [N]`
    have hL : F ρ ≫ F σ = E (σ * ρ) ≫ Y.hom.left := by
      show (E ρ ≫ (ι' (b ρ)).hom.left) ≫ E σ ≫ (ι' (b σ)).hom.left = _
      have hY : Y.hom.left = Dl ≫ (ι' (α σ (b ρ))).hom.left ≫ (ι' (b σ)).hom.left := rfl
      rw [hY, Category.assoc, reassoc_of% (htwx σ (b ρ))]
      simp only [Dl, Category.assoc, IsIso.hom_inv_id_assoc]
    have hNc : ((N : ℤ) : PkgI3.AbVar.End A) = ι' c * ι' (b (σ * ρ)) := by
      rw [← map_mul, hcb, Int.cast_natCast, map_natCast]
    have hcomm : Y * ((N : ℤ) : PkgI3.AbVar.End A) = ((N : ℤ) : PkgI3.AbVar.End A) * Y :=
      (Int.cast_commute (N : ℤ) Y).eq.symm
    show F ρ ≫ F σ ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom.left =
      (E (σ * ρ) ≫ (ι' (b (σ * ρ))).hom.left) ≫ (Y * ι' c).hom.left
    have e3 : ((N : ℤ) : PkgI3.AbVar.End A).hom.left ≫ Y.hom.left =
        Y.hom.left ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom.left := by
      show (Y * ((N : ℤ) : PkgI3.AbVar.End A)).hom.left =
        (((N : ℤ) : PkgI3.AbVar.End A) * Y).hom.left
      rw [hcomm]
    rw [← Category.assoc, hL, Category.assoc, ← e3, hNc]
    show E (σ * ρ) ≫ ((ι' (b (σ * ρ))).hom.left ≫ (ι' c).hom.left) ≫ Y.hom.left = _
    simp only [Category.assoc]
    rfl

/-- **Sanity check (proved): `SemilinearTwistAt` is satisfiable** — over `L = ℚ`, `E_σ = 𝟙`,
`α_σ = id`, `τ = id`, for any abelian variety and any `ι'`. -/
theorem semilinearTwistAt_bot (A : PkgI3.AbVar (⊥ : IF)) (ι' : O →+* PkgI3.AbVar.End A) :
    SemilinearTwistAt ⊥ A ι' (fun _ => 𝟙 _) (fun _ => RingEquiv.refl O) := by
  have hid : Spec.map (CommRingCat.ofHom ((RingEquiv.refl (⊥ : IF) : (⊥ : IF) ≃+* (⊥ : IF)) :
      (⊥ : IF) →+* (⊥ : IF))) = 𝟙 _ := by
    rw [← Spec.map_id]; rfl
  intro σ
  refine ⟨inferInstance, ⟨RingEquiv.refl _, fun x => ?_, ?_, ?_, ?_⟩, fun a => ?_, fun k _ => ?_⟩
  · obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
    show (x : Qbar) = act σ⁻¹ (x : Qbar)
    rw [← hq]; exact ((act σ⁻¹).commutes q).symm
  · rw [hid, Category.id_comp, Category.comp_id]
  · rw [Category.comp_id]
    symm
    refine Eq.trans (congrArg (fun m => m ≫ μ[A.X].left) ?_) (Category.id_comp _)
    apply pullback.hom_ext <;> simp
  · rw [hid, Category.id_comp, Category.comp_id]
  · simp
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `SemilinearIsogMaps` from `SemilinearTwistIsos`, `MulIsogeny` and `RigidityHom` (proved). -/
theorem semilinearIsogMaps_of_twist (hMul : G0FibreSimple.MulIsogeny)
    (hR : G0FibreSimple.RigidityHom) (h : SemilinearTwistIsos) : SemilinearIsogMaps := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨E, α, hE⟩ := h Y Φ π hR1 hR2 j₀ y P hy hπ K PK hPK L hKL hfix
  exact semilinearIsogAt_of_twist hMul hR L _ _ E α hE

/-- **`ConjIsogMaps` from `SemilinearTwistIsos` and `MulIsogeny` (proved; `RigidityHom` and the
point lemmas are theorems).** -/
theorem conjIsogMaps_of_twist (hMul : G0FibreSimple.MulIsogeny) (h : SemilinearTwistIsos) :
    ConjIsogMaps :=
  conjIsogMaps_of_semilinearIsogMaps
    (semilinearIsogMaps_of_twist hMul G0FibreSimple.rigidityHom h)

/-- `KernelFieldExists` from the five leaves, FS5, `MulIsogeny` and `SemilinearTwistIsos`. -/
theorem kernelFieldExists_of_twist (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny)
    (hS : SemilinearTwistIsos) : KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_twist hMul hS)

end G0ModField.KernelField

end KfGlueLevel2

/-! # kf-glue, part 4: `SemilinearTwistIsos`, level 3 — A7 on the conjugates (proved)

`SemilinearTwistIsos` is proved from `TwistDescent`, a statement with no moduli content: for an
abelian variety `B` with a ring map `ι : 𝒪 → End B` over a Galois number field `K ⊆ ℚ̄` and a Hom
field `L ⊇ K` (`G_L` fixes every homomorphism between the conjugates `B_e = B ×_{K,e} ℚ̄`), if any
two conjugates are isomorphic over `ℚ̄` by an isomorphism twisting `ι` by some `α ∈ Aut 𝒪`, then
`B_L` has σ-semilinear twisted automorphisms `E_σ` (`SemilinearTwistAt`). This is Galois descent
from `ℚ̄` to `L` plus the bookkeeping of conjugate varieties. The hypothesis is proved for the
rational fibre `PK`: A7 in the manuscript's form (`LeafQM.AV.conj_iso_of_rational`, from R1fp and
R2fp) gives twisted QM isomorphisms between the base changes `Q_e` of `PK` along `e`, and
`IsBaseChangeOf` + rigidity (`rigidityHom`) identify `Q_e` with the conjugate `B_e` as abelian
varieties with `𝒪`-action. -/

section KfGlueLevel3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-- Base change of an endomorphism of `B/K` to the conjugate `B_e = B ×_{K,e} ℚ̄`. -/
noncomputable def bcEnd (K : IF) (B : PkgI3.AbVar K) (e : K →ₐ[ℚ] Qbar)
    (f : PkgI3.AbVar.End B) : PkgI3.AbVar.End ((G4WeilRes.conjData K B).A e) :=
  @PkgI3.AbVar.Hom.mk' Qbar _ ((G4WeilRes.conjData K B).A e) ((G4WeilRes.conjData K B).A e)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (e : K →+* Qbar)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (e : K →+* Qbar))))
      (f := f.hom))

/-- **Glue (Galois descent of twisted isomorphisms; no moduli content).** For `B/K` with
`ι : 𝒪 → End B`, `K ⊆ L ⊆ ℚ̄` finite Galois with `L` a Hom field of `B` (`G_L` acts trivially on
the Hom lattice of the conjugates), if any two conjugates `B_{e₁}`, `B_{e₂}` are isomorphic over `ℚ̄`
by an isomorphism `φ` with `ι_{e₁}(α a) φ = φ ι_{e₂}(a)` for some `α ∈ Aut 𝒪`, then `B_L` has the
σ-semilinear twisted automorphisms of `SemilinearTwistAt` for `ι_L = endBC ∘ ι`.
*Argument* (model check): for `σ ∈ G_ℚ` let `Ē_σ = φ ≫ cmp_σ` on `B_{ℚ̄} = B_{K.val}` (`φ` the
twisted isomorphism `B_{K.val} → B_{σ⁻¹ K.val}`, chosen on representatives of `G_ℚ/G_L` with
`φ = id` on `G_L`, and `cmp` the comparison of `G4Conj` over `Spec σ⁻¹`); it is σ-semilinear,
preserves the group law and the origin, and twists `ι`. Since `L` is a Hom field, `φ` is fixed by
conjugation through `G_L`, so `Ē_σ` commutes with the descent datum of `B_{ℚ̄}/B_L`; Galois descent
for morphisms (Mathlib: the fpqc topology is subcanonical, `Sites/Fpqc.lean`, with
`morphismsDescend` to reach a finite Galois `L'/L`) gives `E_σ` on `B_L`. -/
def TwistDescent : Prop :=
  ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (B : PkgI3.AbVar K)
    (ιB : O →+* PkgI3.AbVar.End B) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hKL : K ≤ L),
    (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1) →
    (∀ e₁ e₂ : K →ₐ[ℚ] Qbar, ∃ (α : O ≃+* O)
        (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
        (ψ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₂) ((G4WeilRes.conjData K B).A e₁)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (bcEnd K B e₁ (ιB (α a))).hom ≫ φ.hom = φ.hom ≫ (bcEnd K B e₂ (ιB a)).hom) →
    ∃ (E : GQ → ((@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left)) (α : GQ → (O ≃+* O)),
      SemilinearTwistAt L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
        ((@endBC K _ B L _ (incAlg hKL)).comp ιB) E α

/-- **The standard theorem behind `TwistDescent` (statement only; not used in any proof).**
Galois descent of morphisms along `ℚ̄/L`: for `L ⊆ ℚ̄` a number field, `X` quasi-compact and
quasi-separated and `Y` locally of finite presentation over `L`, every `ℚ̄`-morphism
`φ : X_ℚ̄ → Y_ℚ̄` fixed by conjugation through `G_L` (`G4Conj.conj`, as in `HomDescends`) is the base
change of a unique `L`-morphism. (SGA 1 VIII; Stacks, descent along fpqc coverings; locators
UNVERIFIED.) In the project: `morphismsDescend` (EGA IV 8.8.2, proved) descends `φ` to a finite
`L'`; Mathlib's `EffectiveEpi` for flat surjective quasi-compact morphisms (`Sites/Fpqc.lean`)
then needs `L' ⊗_L L' ≅ ∏_{Gal(L'/L)} L'` (not in Mathlib v4.35). `TwistDescent` follows from this
statement applied to the σ-semilinear maps `Ē_σ` (after identifying them with maps out of `^σB_L`)
together with the conjugate bookkeeping; that deduction is a model check, not compiled. -/
def GaloisDescentMor : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (X Y : Over (Spec (CommRingCat.of L)))
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation Y.hom]
    (φ : (Over.pullback (G4WeilRes.specIncl L)).obj X ⟶ (Over.pullback (G4WeilRes.specIncl L)).obj Y),
    (∀ σ ∈ L.fixingSubgroup,
      ∀ hf : G4WeilRes.specIncl L = G4WeilRes.specGal σ ≫ G4WeilRes.specIncl L,
        G4Conj.conj X Y (G4WeilRes.specGal σ) hf hf φ = φ) →
    ∃! ψ : X ⟶ Y, (Over.pullback (G4WeilRes.specIncl L)).map ψ = φ

/-- **Transport (proved, rigidity).** A base change `Q` of `PK` along `e : K → ℚ̄`
(`IsBaseChangeOf`, a pullback square compatible with `ι` and `η`) is isomorphic to the conjugate
`B_e` as an abelian variety with `𝒪`-action. -/
theorem bc_transport (hR : G0FibreSimple.RigidityHom) {K : IF} (PK : QML3 K)
    (e : K →ₐ[ℚ] Qbar) (Q : QML3 Qbar) (hb : IsBaseChangeOf (e : K →+* Qbar) PK Q) :
    ∃ (θ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K PK.A).A e) Q.A)
      (θ' : PkgI3.AbVar.Hom Q.A ((G4WeilRes.conjData K PK.A).A e)),
      θ.hom ≫ θ'.hom = 𝟙 _ ∧ θ'.hom ≫ θ.hom = 𝟙 _ ∧
      ∀ a : O, (bcEnd K PK.A e (PK.q.iota a)).hom ≫ θ.hom = θ.hom ≫ (Q.q.iota a).hom := by
  obtain ⟨g, hpb, hι, hη⟩ := hb
  let s := Spec.map (CommRingCat.ofHom (e : K →+* Qbar))
  let Ae : PkgI3.AbVar Qbar := (G4WeilRes.conjData K PK.A).A e
  have hpb0 : IsPullback (pullback.fst PK.A.X.hom s) (pullback.snd PK.A.X.hom s) PK.A.X.hom s :=
    IsPullback.of_hasPullback _ _
  let θ : pullback PK.A.X.hom s ≅ Q.A.X.left := hpb0.isoIsPullback _ _ hpb
  have hθfst : θ.hom ≫ g = pullback.fst PK.A.X.hom s := hpb0.isoIsPullback_hom_fst _ _ hpb
  have hθsnd : θ.hom ≫ Q.A.X.hom = pullback.snd PK.A.X.hom s :=
    hpb0.isoIsPullback_hom_snd _ _ hpb
  let h : Ae.X ⟶ Q.A.X := Over.homMk θ.hom hθsnd
  let hinv : Q.A.X ⟶ Ae.X := Over.homMk θ.inv ((Iso.inv_comp_eq θ).mpr hθsnd.symm)
  have hhi : h ≫ hinv = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.hom_inv_id
  have hih : hinv ≫ h = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.inv_hom_id
  have hu : ∀ {R : Type} [Field R] {U : Over (Spec (CommRingCat.of R))},
      (toUnit U).left = U.hom := fun {R _ U} => by
    have := Over.w (toUnit U); simpa using this
  have hid : ∀ (R : Type) [Field R], Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ :=
    fun R _ => by rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hηQ : η[Q.A.X].left ≫ g = s ≫ η[PK.A.X].left := by
    have := hη 0
    have h0Q : Additive.toMul (Q.e.eta 0) = 1 := by rw [map_zero]; rfl
    have h0P : Additive.toMul (PK.e.eta 0) = 1 := by rw [map_zero]; rfl
    rw [h0Q, h0P] at this
    change (toUnit (PkgI3.AbVar.ptObj (K := Qbar) Qbar) ≫ η[Q.A.X]).left ≫ g =
      s ≫ (toUnit (PkgI3.AbVar.ptObj (K := K) K) ≫ η[PK.A.X]).left at this
    rw [Over.comp_left, Over.comp_left, hu, hu] at this
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, hid, Category.assoc] at this
    erw [Category.id_comp, Category.id_comp] at this
    exact this
  have hηW : η[Ae.X].left ≫ pullback.fst PK.A.X.hom s = s ≫ η[PK.A.X].left := by
    have e1 := G4Conj.one_left_fst s PK.A.X
    erw [e1]
  have hunit : η[Ae.X] ≫ h = η[Q.A.X] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply hpb.hom_ext
    · have hh : h.left ≫ g = pullback.fst PK.A.X.hom s := hθfst
      rw [Category.assoc, hh, hηW, hηQ]
    · rw [Category.assoc, Over.w h, Over.w η[Ae.X], Over.w η[Q.A.X]]
  have hunit' : η[Q.A.X] ≫ hinv = η[Ae.X] := by
    rw [← hunit, Category.assoc, hhi, Category.comp_id]
  haveI hmh : IsMonHom h := hR Qbar Ae Q.A h hunit
  haveI hmi : IsMonHom hinv := hR Qbar Q.A Ae hinv hunit'
  refine ⟨PkgI3.AbVar.Hom.mk' h, PkgI3.AbVar.Hom.mk' hinv, hhi, hih, fun a => ?_⟩
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left]
  apply hpb.hom_ext
  · change ((Over.pullback s).map (PK.q.iota a).hom).left ≫ θ.hom ≫ g =
      θ.hom ≫ (Q.q.iota a).hom.left ≫ g
    rw [hι a, hθfst, ← Category.assoc θ.hom g, hθfst]
    exact pullback.lift_fst _ _ _
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [Over.w h, Over.w (Q.q.iota a).hom, Over.w h]
    exact Over.w (bcEnd K PK.A e (PK.q.iota a)).hom

/-- **A7 on the conjugates (proved).** For a `K`-point `yK` with object `PK` and rational
`π`-value, any two conjugates `PK.A_{e₁}`, `PK.A_{e₂}` are isomorphic over `ℚ̄` by an
isomorphism twisting `ι` by some `α ∈ Aut 𝒪`. -/
theorem conjTwist_of_rational (hR : G0FibreSimple.RigidityHom)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (hR1 : R1fpProps Y Φ) (hR2 : R2fpProps Y Φ π) {K : IF} (yK : fieldPt K ⟶ Y) (PK : QML3 K)
    (hyK : Φ K yK = M3.mk PK) (j₀ : ℚ)
    (hj : π.val (K := K) yK.left = OnePoint.some (algebraMap ℚ K j₀))
    (e₁ e₂ : K →ₐ[ℚ] Qbar) : ∃ (α : O ≃+* O)
        (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K PK.A).A e₁) ((G4WeilRes.conjData K PK.A).A e₂))
        (ψ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K PK.A).A e₂) ((G4WeilRes.conjData K PK.A).A e₁)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (bcEnd K PK.A e₁ (PK.q.iota (α a))).hom ≫ φ.hom =
          φ.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom := by
  obtain ⟨Q₁, Q₂, hb₁, hb₂, α, ⟨f⟩⟩ := conj_iso_of_rational hR1 hR2 yK PK hyK j₀ hj e₁ e₂
  obtain ⟨θ₁, θ₁', h11, h12, hι1⟩ := bc_transport hR PK e₁ Q₁ hb₁
  obtain ⟨θ₂, θ₂', h21, h22, hι2⟩ := bc_transport hR PK e₂ Q₂ hb₂
  have hι2' : ∀ a : O, (Q₂.q.iota a).hom ≫ θ₂'.hom = θ₂'.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom :=
    fun a => by
      calc (Q₂.q.iota a).hom ≫ θ₂'.hom
          = θ₂'.hom ≫ θ₂.hom ≫ (Q₂.q.iota a).hom ≫ θ₂'.hom := by rw [reassoc_of% h22]
        _ = θ₂'.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom ≫ θ₂.hom ≫ θ₂'.hom := by
            rw [reassoc_of% (hι2 a)]
        _ = θ₂'.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom := by rw [h21, Category.comp_id]
  refine ⟨α, PkgI3.AbVar.Hom.mk' (θ₁.hom ≫ f.φ.hom ≫ θ₂'.hom),
    PkgI3.AbVar.Hom.mk' (θ₂.hom ≫ f.ψ.hom ≫ θ₁'.hom), ?_, ?_, fun a => ?_⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h22, reassoc_of% f.left, h11]
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h12, reassoc_of% f.right, h21]
  · simp only [PkgI3.AbVar.Hom.hom_mk']
    have hf : (Q₁.q.iota (α a)).hom ≫ f.φ.hom = f.φ.hom ≫ (Q₂.q.iota a).hom := f.equivariant a
    simp only [Category.assoc]
    rw [reassoc_of% (hι1 (α a)), reassoc_of% hf, hι2' a]

/-- **`SemilinearTwistIsos` from `TwistDescent` (proved; A7 and rigidity).** -/
theorem semilinearTwistIsos_of_descent (hD : TwistDescent) : SemilinearTwistIsos := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨⟨yK, hyK, hyKP⟩, -⟩ := hPK
  have hyy : fieldMap K.val ≫ yK = y := (Φ Qbar).injective (hyKP.trans hy.symm)
  have hj : π.val (K := K) yK.left = OnePoint.some (algebraMap ℚ K j₀) := by
    have h2 : (π.val (K := K) yK.left).map (K.val : K →+* Qbar) =
        OnePoint.some (algebraMap ℚ Qbar j₀) := by
      have h1 := π.val_comp ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar) yK.left
      rw [← hyy] at hπ
      exact h1.symm.trans hπ
    generalize π.val (K := K) yK.left = v at h2 ⊢
    induction v using OnePoint.rec with
    | infty => simp at h2
    | coe x =>
      rw [OnePoint.map_some] at h2
      have h3 : (K.val : K →+* Qbar) x = (K.val : K →+* Qbar) (algebraMap ℚ K j₀) := by
        rw [OnePoint.coe_eq_coe] at h2
        rw [h2]; exact (K.val.commutes j₀).symm
      rw [RingHom.injective _ h3]
  exact hD K PK.A PK.q.iota L hKL hfix
    (conjTwist_of_rational G0FibreSimple.rigidityHom hR1 hR2 yK PK hyK j₀ hj)

/-- **`ConjIsogMaps` from `TwistDescent` and `MulIsogeny` (proved).** -/
theorem conjIsogMaps_of_descent (hMul : G0FibreSimple.MulIsogeny) (hD : TwistDescent) :
    ConjIsogMaps :=
  conjIsogMaps_of_twist hMul (semilinearTwistIsos_of_descent hD)

/-- `KernelFieldExists` from the five leaves, FS5, `MulIsogeny` and `TwistDescent`. -/
theorem kernelFieldExists_of_descent (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny)
    (hD : TwistDescent) : KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_descent hMul hD)

/-- **`ConjIsogMaps` from mul-rigidity's leaf `KerUnitOpen` and `TwistDescent` (proved).** -/
theorem conjIsogMaps_of_kerUnitOpen (hK : MulRigidity.KerUnitOpen) (hD : TwistDescent) :
    ConjIsogMaps :=
  conjIsogMaps_of_descent (MulRigidity.mulIsogeny_of_kerUnitOpen hK) hD

/-- **`ConjIsogMaps` from glue only (proved):** mul-rigidity's two cotangent glue statements and
`TwistDescent`. -/
theorem conjIsogMaps_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) (hD : TwistDescent) : ConjIsogMaps :=
  conjIsogMaps_of_descent (MulRigidity.mulIsogeny_of_cotangent h1 h2) hD

/-- **`KernelFieldExists`, final form (proved).** Leaves: `HomFreeFinite` (T6),
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`, `QMDichotomyYu` (T27),
`KerUnitOpen` (mul-rigidity; implied by the published `MulEtale`). Glue: FS5 `FibreComTrivial`
(g0-fibresimple) and `TwistDescent` (Galois descent). -/
theorem kernelFieldExists_of_kerUnitOpen (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hK : MulRigidity.KerUnitOpen) (hD : TwistDescent) :
    KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_kerUnitOpen hK hD)

end G0ModField.KernelField

end KfGlueLevel3

#print axioms G0ModField.KernelField.conjIsogMapsAt_of_semilinear
#print axioms G0ModField.KernelField.conjIsogMaps_of_semilinear
#print axioms G0ModField.KernelField.liftQbarPoints
#print axioms G0ModField.KernelField.finiteFibreQbarPoints
#print axioms G0ModField.KernelField.conjIsogMaps_of_semilinearIsogMaps
#print axioms G0ModField.KernelField.kernelFieldExists_of_semilinear
#print axioms G0ModField.KernelField.semilinearIsogAt_of_twist
#print axioms G0ModField.KernelField.conjIsogMaps_of_twist
#print axioms G0ModField.KernelField.kernelFieldExists_of_twist
#print axioms G0ModField.KernelField.iota_isogeny
#print axioms G0ModField.KernelField.bc_transport
#print axioms G0ModField.KernelField.conjTwist_of_rational
#print axioms G0ModField.KernelField.semilinearTwistIsos_of_descent
#print axioms G0ModField.KernelField.conjIsogMaps_of_descent
#print axioms G0ModField.KernelField.kernelFieldExists_of_descent
#print axioms G0ModField.KernelField.conjIsogMaps_of_kerUnitOpen
#print axioms G0ModField.KernelField.conjIsogMaps_of_cotangent
#print axioms G0ModField.KernelField.kernelFieldExists_of_kerUnitOpen
#print axioms G0ModField.KernelField.semilinearTwistAt_bot
