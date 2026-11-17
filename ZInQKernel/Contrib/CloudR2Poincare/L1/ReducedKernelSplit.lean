import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedConstantRank

/-!
# Locally split kernels of constant-rank differentials over reduced bases

The degree-zero kernel is cut out by an actual idempotent, not an assumed
single-degree homology Fact. Splitting it near a point gives uniform free
kernel/homology data after EVERY base change. Positive-degree homology is
unrestricted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Locally, the kernel of a constant-rank matrix is a split free summand;
the splitting remains valid after arbitrary scheme-valued base change. -/
theorem exists_opens_split_kernel_of_constant_residueRank
    {Y : Scheme.{u}} [AlgebraicGeometry.IsReduced Y]
    {a m n : Type u} [Fintype a] [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n Γ(Y, ⊤)) (ρ : ℕ)
    (hρ : ∀ y : Y, (A.map (Y.fromSpecResidueField y).appTop).rank = ρ)
    (y : Y) :
    ∃ W : Y.Opens, y ∈ W ∧ ∀ {Z : Scheme.{u}} (g : Z ⟶ Y), Set.range g ⊆ W →
      Matrix.HasSplitHomology (0 : Matrix n a Γ(Z, ⊤)) (A.map g.appTop)
        (Fin (Fintype.card n - ρ)) := by
  classical
  obtain ⟨U, hyU, splitA⟩ := exists_opens_split_of_constant_residueRank A ρ hρ y
  obtain ⟨L, M, L', M', hA, hL, hM⟩ := splitA U.ι (by rw [Scheme.Opens.range_ι])
  let B := A.map U.ι.appTop
  let ε : Matrix n n Γ(U.toScheme, ⊤) :=
    Matrix.splitIdempotent (0 : Matrix n (Fin 0) Γ(U.toScheme, ⊤))
      (0 : Matrix (Fin 0) n Γ(U.toScheme, ⊤)) M M'
  have first : (0 : Matrix n a Γ(U.toScheme, ⊤)) =
      (0 : Matrix n (Fin 0) Γ(U.toScheme, ⊤)) *
        (0 : Matrix (Fin 0) a Γ(U.toScheme, ⊤)) ∧
      (0 : Matrix (Fin 0) n Γ(U.toScheme, ⊤)) *
        (0 : Matrix n (Fin 0) Γ(U.toScheme, ⊤)) = 1 ∧
      (0 : Matrix (Fin 0) a Γ(U.toScheme, ⊤)) *
        (0 : Matrix a (Fin 0) Γ(U.toScheme, ⊤)) = 1 := by
    exact ⟨by simp, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have second : B = L * M ∧ L' * L = 1 ∧ M * M' = 1 := ⟨hA, hL, hM⟩
  have he : ε * ε = ε :=
    Matrix.splitIdempotent_mul_self
      (L₁ := (0 : Matrix n (Fin 0) Γ(U.toScheme, ⊤)))
      (L₁' := (0 : Matrix (Fin 0) n Γ(U.toScheme, ⊤)))
      (M₂ := M) (M₂' := M') first.2.1 hM (by simp)
  have hrank : ∀ z : U.toScheme,
      (ε.map (U.toScheme.fromSpecResidueField z).appTop).rank = Fintype.card n - ρ := by
    intro z
    letI : Field Γ(Spec (U.toScheme.residueField z), ⊤) :=
      (Scheme.Modules.isField_Γ_Spec_residueField z).toField
    have h := Matrix.rank_splitIdempotent_map (A₁ := (0 : Matrix n a Γ(U.toScheme, ⊤)))
      (by simp) first second (U.toScheme.fromSpecResidueField z).appTop.hom
    simpa only [Nat.sub_zero] using h
  let yu : U.toScheme := ⟨y, hyU⟩
  obtain ⟨V, hyV, splitE⟩ := exists_opens_split_of_constant_residueRank ε
    (Fintype.card n - ρ) hrank yu
  refine ⟨U.ι ''ᵁ V, ⟨yu, hyV, rfl⟩, fun g hg ↦ ?_⟩
  have hgU : Set.range g ⊆ Set.range U.ι := by
    refine hg.trans ?_
    rintro _ ⟨z, _, rfl⟩
    exact ⟨z, rfl⟩
  let gU := IsOpenImmersion.lift U.ι g hgU
  have gU_fac : gU ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hgV : Set.range gU ⊆ V := by
    rintro _ ⟨z, rfl⟩
    rw [← Scheme.Hom.preimage_image_eq U.ι V]
    change U.ι (gU z) ∈ U.ι ''ᵁ V
    rw [← Scheme.Hom.comp_apply, gU_fac]
    exact hg ⟨z, rfl⟩
  obtain ⟨I, P, I', P', hEP, hI, hP⟩ := splitE gU hgV
  have heG : (ε.map gU.appTop) * (ε.map gU.appTop) = ε.map gU.appTop := by
    rw [← Matrix.map_mul, he]
  have hPI : P * I = 1 := Matrix.mul_eq_one_of_isIdempotentElem
    (by rw [← hEP]; exact heG) hI hP
  have mappedFirst := Matrix.split_map gU.appTop.hom first
  have mappedSecond := Matrix.split_map gU.appTop.hom second
  have hAcomp : B.map gU.appTop = A.map g.appTop := by
    rw [← gU_fac, Scheme.Modules.map_appTop_comp]
  have hεcomp : Matrix.splitIdempotent
      ((0 : Matrix n (Fin 0) Γ(U.toScheme, ⊤)).map gU.appTop.hom)
      ((0 : Matrix (Fin 0) n Γ(U.toScheme, ⊤)).map gU.appTop.hom)
      (M.map gU.appTop.hom) (M'.map gU.appTop.hom) = I * P := by
    rw [← Matrix.splitIdempotent_map]
    exact hEP
  have hsplit := Matrix.hasSplitHomology_of_splitIdempotent
    (by simp : B.map gU.appTop.hom *
      (0 : Matrix n a Γ(U.toScheme, ⊤)).map gU.appTop.hom = 0)
    mappedFirst mappedSecond hεcomp hPI
  rw [hAcomp] at hsplit
  simpa using hsplit

/-- A finite free complex with no degree -1 term and constant fibre H0=1 has
locally free H0 of rank one after every base change, with explicit split data.
This does not yet identify those data with the CANONICAL coefficient-sheaf
base-change map. -/
theorem exists_opens_free_H0_of_constant_dimension_one
    {Y : Scheme.{u}} [AlgebraicGeometry.IsReduced Y]
    (P : CochainComplex Y.Modules ℤ) (r : ℤ → ℕ)
    (e : ∀ q, P.X q ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r q))))
    (hneg : r (-1) = 0) (hH0 : ∀ y : Y, derivedFiberDimension P 0 y = 1) (y : Y) :
    ∃ W : Y.Opens, y ∈ W ∧ ∀ {Z : Scheme.{u}} (g : Z ⟶ Y), Set.range g ⊆ W →
      Nonempty (((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology 0) ≅
        SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin 1))) := by
  classical
  let A := Scheme.Modules.freeMatrix ((e 0).inv ≫ P.d 0 1 ≫ (e 1).hom)
  have rankA := outgoing_residueRank_eq_of_H0_dimension_one P r e hneg hH0
  have hpositive : 0 < r 0 := by
    have hdim := Scheme.Modules.finrank_homology_pullback_add_rank_add_rank e
      (Field.toIsField (Y.residueField y)) (Y.fromSpecResidueField y) 0
    change derivedFiberDimension P 0 y + _ + _ = r 0 at hdim
    rw [hH0] at hdim
    omega
  have hcard : Fintype.card (ULift.{u} (Fin (r 0))) - (r 0 - 1) = 1 := by
    simp only [Fintype.card_ulift, Fintype.card_fin]
    omega
  obtain ⟨W, hyW, split⟩ := exists_opens_split_kernel_of_constant_residueRank
    (a := ULift.{u} (Fin (r (-1)))) A (r 0 - 1) rankA y
  refine ⟨W, hyW, fun {Z} g hg ↦ ?_⟩
  have hs := split g hg
  rw [hcard] at hs
  have hsU := hs.of_equiv (Equiv.ulift.symm : Fin 1 ≃ ULift.{u} (Fin 1))
  obtain ⟨I, Q, σ, τ, hQI, hAI, hQzero, hsum⟩ := hsU
  let P' := ((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P
  let e' (q : ℤ) : P'.X q ≅
      SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin (r q))) :=
    (Scheme.Modules.pullback g).mapIso (e q) ≪≫ Scheme.Modules.pullbackFreeIso g _
  haveI : IsEmpty (ULift.{u} (Fin (r (-1)))) := by rw [hneg]; infer_instance
  have incoming : Scheme.Modules.freeMatrix ((e' (-1)).inv ≫ P'.d (-1) 0 ≫ (e' 0).hom) = 0 :=
    Subsingleton.elim _ _
  have outgoing : Scheme.Modules.freeMatrix ((e' 0).inv ≫ P'.d 0 1 ≫ (e' 1).hom) =
      A.map g.appTop := Scheme.Modules.freeMatrix_pullback_d g P (e 0) (e 1)
  apply Scheme.Modules.nonempty_homology_iso_free_of_split P' 0 (e' (0 - 1)) (e' 0) (e' (0 + 1))
    σ τ I Q hQI
  · change Scheme.Modules.freeMatrix ((e' 0).inv ≫ P'.d 0 1 ≫ (e' 1).hom) * I = 0
    rw [outgoing]
    exact hAI
  · change Q * Scheme.Modules.freeMatrix ((e' (-1)).inv ≫ P'.d (-1) 0 ≫ (e' 0).hom) = 0
    rw [incoming]
    exact hQzero
  · change I * Q + Scheme.Modules.freeMatrix ((e' (-1)).inv ≫ P'.d (-1) 0 ≫ (e' 0).hom) * σ +
      τ * Scheme.Modules.freeMatrix ((e' 0).inv ≫ P'.d 0 1 ≫ (e' 1).hom) = 1
    rw [incoming, outgoing]
    exact hsum

end ZInQ.Contrib.CloudR2Poincare.L1
