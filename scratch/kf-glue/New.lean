
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

#print axioms G0ModField.KernelField.conjIsogMapsAt_of_semilinear
#print axioms G0ModField.KernelField.conjIsogMaps_of_semilinear
#print axioms G0ModField.KernelField.liftQbarPoints
#print axioms G0ModField.KernelField.finiteFibreQbarPoints
#print axioms G0ModField.KernelField.conjIsogMaps_of_semilinearIsogMaps
#print axioms G0ModField.KernelField.kernelFieldExists_of_semilinear
