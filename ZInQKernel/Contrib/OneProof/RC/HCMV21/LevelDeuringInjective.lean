import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelDeuringOrder

/-! **Injectivity of the level-`N` Deuring class map.** Equal classes give
right-translate placed level ideals `I_N(X) u = I_N(Y)`. The level-one ideal is
recovered as `O₀ · I_N` (at a prime dividing the level a chain isomorphism of
Tate modules lies in the completed level ideal and generates the completed
level-one ideal over `O₀`; away from the level the two completions agree), so
`I(X) u = I(Y)`. Right multiplication by `u⁻¹` is then a bijective left
`O₀`-module map `Hom(E_Y, E₀) → Hom(E_X, E₀)`; the bijection clause of the
Theorem 42.3.2 candidate (étale maps, separable scope; its reach premises for
the two curves come from `SeparableReach E₀`) writes it and its inverse
as `φ*` and `ψ*` for étale `φ, ψ`, and the injectivity clause gives
`ψ ∘ φ = 1`, `φ ∘ ψ = 1`. The level subgroups correspond by the recovery of the
level from the Hom lattice (`mem_levelHom_of_comp`) and a cardinality count. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

section Recover

variable {k : Type} [Field k] [IsAlgClosed k] {a b : ℚ} {E₀ E : PkgI3.AbVar k}
  {S : Order a b} {j : E₀.End ≃+* S.ring}

/-- The left `O₀`-span of a lattice. -/
def orderSpan (S : Order a b) (L : Submodule ℤ (B a b)) : Submodule ℤ (B a b) :=
  Submodule.span ℤ {x | ∃ o ∈ S.ring, ∃ y ∈ L, x = o * y}

theorem orderSpan_map_mulRight (S : Order a b) (L : Submodule ℤ (B a b)) (u : (B a b)ˣ) :
    orderSpan S (L.map ((mulRightEquiv u).restrictScalars ℤ).toLinearMap) =
      (orderSpan S L).map ((mulRightEquiv u).restrictScalars ℤ).toLinearMap := by
  unfold orderSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨o, ho, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨o * y, ⟨o, ho, y, hy, rfl⟩, by
      change o * y * u = o * (y * u)
      rw [mul_assoc]⟩
  · rintro ⟨_, ⟨o, ho, y, hy, rfl⟩, rfl⟩
    exact ⟨o, ho, y * u, ⟨y, hy, rfl⟩, by
      change o * y * u = o * (y * u)
      rw [mul_assoc]⟩

/-- **The level-one ideal is the `O₀`-span of the level ideal.** -/
theorem orderSpan_levelLattice (P : HomPlacement S j E) (hE : E.dim = 1) (hE₀ : E₀.dim = 1)
    (N : ℕ) (hN : N ≠ 0) (Pt : E.Pt k) (hPt : orderOf Pt = N) (P₀ : E₀.Pt k)
    (hP₀ : orderOf P₀ = N) (hpk : ∀ p : ℕ, p.Prime → p ∣ N → (p : k) ≠ 0) :
    orderSpan S (levelLattice P (Subgroup.zpowers Pt) (Subgroup.zpowers P₀)) =
      P.ideal.val.lattice := by
  set L := levelLattice P (Subgroup.zpowers Pt) (Subgroup.zpowers P₀)
  have hC : ∀ x ∈ Subgroup.zpowers Pt, x ^ N = 1 := zpowers_pow_eq_one N Pt hPt
  have hsub : orderSpan S L ≤ P.ideal.val.lattice := by
    apply Submodule.span_le.mpr
    rintro _ ⟨o, ho, y, hy, rfl⟩
    exact P.ideal.val.mul_mem ho (levelLattice_le P hy)
  have hLle : L ≤ orderSpan S L := fun y hy =>
    Submodule.subset_span ⟨1, S.ring.one_mem, y, hy, (one_mul y).symm⟩
  have hfull : FullLattice (orderSpan S L) := by
    refine ⟨P.ideal.val.full.fg.of_le hsub, ?_⟩
    apply top_unique
    have hfl := (levelIdeal P (Subgroup.zpowers P₀) hN (zpowers_pow_eq_one N P₀ hP₀)
      (Subgroup.zpowers Pt) hC).full.span_eq_top
    rw [← hfl]
    exact Submodule.span_mono hLle
  apply le_antisymm hsub
  intro x hx
  apply (mem_iff_all_local hfull x).mpr
  intro p
  by_cases hpN : p.val ∣ N
  · have hpk' := hpk p.val p.property hpN
    obtain ⟨β, hβ⟩ := exists_chainIso hE hE₀ p.val hpk' N hN hpN Pt hPt P₀ hP₀
    have hfullE := span_tateHom_eq_top P hpk' hE hE₀
    let bE₀ := S.basis.map j.symm.toAddEquiv.toIntLinearEquiv
    have hfull₀ : Submodule.span ℤ_[p.val] (Set.range (tateHom p.val E₀ E₀)) = ⊤ :=
      span_homT_eq_top_of_basis p.val 4 hpk' bE₀ (tateHomBasisFour hpk' hE₀ hE₀)
    have hβM := (mem_span_levelHom_primary p.val hpk' N hN Pt hPt P₀ hP₀ hfullE
      β.toLinearMap).mpr (fun y hy => (hβ y).mp hy)
    have hβΛ : tateToLocal P hpk' hE hE₀ β.toLinearMap ∈ localLattice p.val L := by
      rw [localLattice_levelLattice_eq_map P p.val hpk' hE hE₀]
      exact ⟨_, hβM, rfl⟩
    -- left multiplication by `O₀` on the completed level lattice
    have hleft : ∀ o : E₀.End, ∀ y ∈ localLattice p.val L,
        toLocal p.val (j o : B a b) * y ∈ localLattice p.val (orderSpan S L) := by
      intro o y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨z, hz, rfl⟩ := hy
        rw [← map_mul]
        exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨_, (j o).prop, z, hz, rfl⟩, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
      | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
    have hcomb : ∀ ψ ∈ Submodule.span ℤ_[p.val] (Set.range (tateHom p.val E₀ E₀)),
        tateToLocal P hpk' hE hE₀ (ψ.comp β.toLinearMap) ∈ localLattice p.val (orderSpan S L) := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨o, rfl⟩ := hψ
        change tateToLocal P hpk' hE hE₀ ((homT (ℓ := p.val) o).comp β.toLinearMap) ∈ _
        rw [tateToLocal_comp]
        exact hleft o _ hβΛ
      | zero => rw [LinearMap.zero_comp, map_zero]; exact Submodule.zero_mem _
      | add ψ ψ' _ _ h h' => rw [LinearMap.add_comp, map_add]; exact Submodule.add_mem _ h h'
      | smul c ψ _ h => rw [LinearMap.smul_comp, map_smul]; exact Submodule.smul_mem _ c h
    obtain ⟨α, rfl⟩ := P.exists_of_mem hx
    have hψ : (tateHom p.val E E₀ α).comp β.symm.toLinearMap ∈
        Submodule.span ℤ_[p.val] (Set.range (tateHom p.val E₀ E₀)) := by
      rw [hfull₀]
      trivial
    have h := hcomb _ hψ
    have he : ((tateHom p.val E E₀ α).comp β.symm.toLinearMap).comp β.toLinearMap =
        tateHom p.val E E₀ α := by
      ext y
      simp
    rw [he, tateToLocal_tateHom] at h
    exact h
  · have hpN' : IsUnit (N : ℤ_[p.val]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
        ((Nat.Prime.coprime_iff_not_dvd p.property).mpr hpN))
    have h1 : toLocal p.val x ∈ localLattice p.val P.ideal.val.lattice :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [← localLattice_levelLattice_eq P hC p.val hpN'] at h1
    exact Submodule.span_mono (Set.image_mono hLle) h1

end Recover

section Injective

variable {q : ℕ} [Fact q.Prime] (h : q % 4 = 3) {k : Type} [Field k] [Algebra (ZMod q) k]
  [IsAlgClosure (ZMod q) k] {N : ℕ} (hN : 0 < N) (hcop : N.Coprime q)
  {E₀ : PkgI3.AbVar k} (h₀ : IsSupersingular E₀) {P₀ : E₀.Pt k} (hP₀ : orderOf P₀ = N)
  {S : Order (-1) (-(q : ℚ))} (j : E₀.End ≃+* S.ring)
  (hmax : ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring)
  (hInv : VoightThm4232Invertible)

theorem IsEtaleIsogeny.comp {k : Type} [Field k] {A B C : PkgI3.AbVar k} {f : Hom A B}
    {g : Hom B C} (hf : IsEtaleIsogeny f) (hg : IsEtaleIsogeny g) :
    IsEtaleIsogeny (Hom.mk' (f.hom ≫ g.hom)) := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hg1, hg2, hg3⟩ := hg
  refine ⟨?_, ?_, ?_⟩ <;> rw [Hom.hom_mk', Over.comp_left] <;> infer_instance

theorem IsEtaleIsogeny.id {k : Type} [Field k] (A : PkgI3.AbVar k) :
    IsEtaleIsogeny (Hom.mk' (𝟙 A.X) : Hom A A) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Hom.hom_mk', Over.id_left] <;> infer_instance

include hcop h₀ in
/-- An isomorphism of enhanced curves from equal placed level classes. -/
theorem nonempty_enhancedIso_of_translate (hEt : VoightThm4232Etale)
    (X Y : SupersingularEnhanced q k N) (PX : HomPlacement S j X.curve)
    (PY : HomPlacement S j Y.curve) (u : (Eichler.B (-1) (-(q : ℚ)))ˣ)
    (hu : (placedLevelIdeal hN hP₀ X PX).translate u = placedLevelIdeal hN hP₀ Y PY)
    (rX : ∃ φ : Hom E₀ X.curve, IsSeparableIsogeny φ)
    (rY : ∃ φ : Hom E₀ Y.curve, IsSeparableIsogeny φ) :
    Nonempty (EnhancedIso X Y) := by
  haveI := charP_of_isAlgClosure q k
  haveI := isAlgClosed_of_isAlgClosure q k
  have hpk : ∀ p : ℕ, p.Prime → p ∣ N → (p : k) ≠ 0 := by
    intro p hp hpN hz
    have hd := (CharP.cast_eq_zero_iff k q p).mp hz
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq Fact.out hp).mp hd
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop.symm (hqp ▸ hpN)
  obtain ⟨PtX, hXl, hPtX⟩ := X.exists_generator
  obtain ⟨PtY, hYl, hPtY⟩ := Y.exists_generator
  set mR := ((mulRightEquiv u).restrictScalars ℤ).toLinearMap with hmR
  -- the level lattices
  have hLN : (levelLattice PX (Subgroup.zpowers PtX) (Subgroup.zpowers P₀)).map mR =
      levelLattice PY (Subgroup.zpowers PtY) (Subgroup.zpowers P₀) := by
    have h1 := congrArg LeftIdeal.lattice hu
    change (levelLattice PX X.level _).map mR = levelLattice PY Y.level _ at h1
    rwa [hXl, hYl] at h1
  -- the level-one ideals
  have hL1 : PX.ideal.val.lattice.map mR = PY.ideal.val.lattice := by
    rw [← orderSpan_levelLattice PX X.supersingular.1 h₀.1 N hN.ne' PtX hPtX P₀ hP₀ hpk,
      ← orderSpan_levelLattice PY Y.supersingular.1 h₀.1 N hN.ne' PtY hPtY P₀ hP₀ hpk,
      ← hLN, orderSpan_map_mulRight]
  have hmem (β : Hom Y.curve E₀) : PY.emb β * (↑u⁻¹ : B (-1) (-(q : ℚ))) ∈ PX.ideal.val.lattice := by
    have h1 : PY.emb β ∈ PX.ideal.val.lattice.map mR := by rw [hL1]; exact PY.mem_ideal β
    obtain ⟨y, hy, hye⟩ := h1
    change y * u = PY.emb β at hye
    rw [← hye, mul_assoc, Units.mul_inv, mul_one]
    exact hy
  have hmem' (α : Hom X.curve E₀) : PX.emb α * (u : B (-1) (-(q : ℚ))) ∈ PY.ideal.val.lattice := by
    rw [← hL1]
    exact ⟨_, PX.mem_ideal α, rfl⟩
  -- the bijective module map `Hom(E_Y, E₀) → Hom(E_X, E₀)`
  let Ffun : Hom Y.curve E₀ → Hom X.curve E₀ := fun β => Classical.choose (PX.exists_of_mem (hmem β))
  have hF (β : Hom Y.curve E₀) : PX.emb (Ffun β) = PY.emb β * ↑u⁻¹ :=
    Classical.choose_spec (PX.exists_of_mem (hmem β))
  let Gfun : Hom X.curve E₀ → Hom Y.curve E₀ := fun α => Classical.choose (PY.exists_of_mem (hmem' α))
  have hG (α : Hom X.curve E₀) : PY.emb (Gfun α) = PX.emb α * u :=
    Classical.choose_spec (PY.exists_of_mem (hmem' α))
  let F : Hom Y.curve E₀ ≃+ Hom X.curve E₀ :=
    { toFun := Ffun
      invFun := Gfun
      left_inv := fun β => PY.injective (by rw [hG, hF, mul_assoc, Units.inv_mul, mul_one])
      right_inv := fun α => PX.injective (by rw [hF, hG, mul_assoc, Units.mul_inv, mul_one])
      map_add' := fun β β' => PX.injective (by rw [map_add, hF, hF, hF, map_add, add_mul]) }
  have hFlin : ∀ (o : E₀.End) (β : Hom Y.curve E₀), F (postcomp o β) = postcomp o (F β) := by
    intro o β
    apply PX.injective
    change PX.emb (Ffun (postcomp o β)) = PX.emb (postcomp o (Ffun β))
    rw [hF, PX.map_postcomp, PY.map_postcomp, hF, mul_assoc]
  have hGlin : ∀ (o : E₀.End) (α : Hom X.curve E₀),
      F.symm (postcomp o α) = postcomp o (F.symm α) := by
    intro o α
    apply PY.injective
    change PY.emb (Gfun (postcomp o α)) = PY.emb (postcomp o (Gfun α))
    rw [hG, PX.map_postcomp, PY.map_postcomp, hG, mul_assoc]
  obtain ⟨-, hfull⟩ := hEt q k E₀ h₀ X.curve Y.curve X.supersingular Y.supersingular rX rY
  obtain ⟨-, hfull'⟩ := hEt q k E₀ h₀ Y.curve X.curve Y.supersingular X.supersingular rY rX
  obtain ⟨hinjX, -⟩ := hEt q k E₀ h₀ X.curve X.curve X.supersingular X.supersingular rX rX
  obtain ⟨hinjY, -⟩ := hEt q k E₀ h₀ Y.curve Y.curve Y.supersingular Y.supersingular rY rY
  obtain ⟨φ, hφ, hφF⟩ := hfull F hFlin
  obtain ⟨ψ, hψ, hψF⟩ := hfull' F.symm hGlin
  have hφψ : φ.hom ≫ ψ.hom = 𝟙 _ := by
    have hpull : homPull (E₀ := E₀) (Hom.mk' (φ.hom ≫ ψ.hom) : Hom X.curve X.curve) =
        homPull (Hom.mk' (𝟙 X.curve.X)) := by
      refine AddMonoidHom.ext fun α => ?_
      apply Hom.ext'
      simp only [homPull_hom, Hom.hom_mk', Category.id_comp, Category.assoc]
      have h2 : homPull φ (homPull ψ α) = α := by
        rw [← hφF, ← hψF, F.apply_symm_apply]
      exact congrArg Hom.hom h2
    exact congrArg Hom.hom (hinjX _ _ (hφ.comp hψ) (IsEtaleIsogeny.id X.curve) hpull)
  have hψφ : ψ.hom ≫ φ.hom = 𝟙 _ := by
    have hpull : homPull (E₀ := E₀) (Hom.mk' (ψ.hom ≫ φ.hom) : Hom Y.curve Y.curve) =
        homPull (Hom.mk' (𝟙 Y.curve.X)) := by
      refine AddMonoidHom.ext fun β => ?_
      apply Hom.ext'
      simp only [homPull_hom, Hom.hom_mk', Category.id_comp, Category.assoc]
      have h2 : homPull ψ (homPull φ β) = β := by
        rw [← hψF, ← hφF, F.symm_apply_apply]
      exact congrArg Hom.hom h2
    exact congrArg Hom.hom (hinjY _ _ (hψ.comp hφ) (IsEtaleIsogeny.id Y.curve) hpull)
  -- the level subgroups
  have hlev : ∀ α ∈ levelHom (L := k) (Subgroup.zpowers PtY) (Subgroup.zpowers P₀),
      homPull φ α ∈ levelHom (L := k) (Subgroup.zpowers PtX) (Subgroup.zpowers P₀) := by
    intro α hα
    have h1 : PY.emb α ∈ (levelLattice PX (Subgroup.zpowers PtX) (Subgroup.zpowers P₀)).map mR := by
      rw [hLN]
      exact ⟨α, hα, rfl⟩
    obtain ⟨y, ⟨α', hα', rfl⟩, hye⟩ := h1
    change PX.emb α' * u = PY.emb α at hye
    have he : homPull φ α = α' := by
      rw [← hφF]
      apply PX.injective
      change PX.emb (Ffun α) = PX.emb α'
      rw [hF, ← hye, mul_assoc, Units.mul_inv, mul_one]
    rw [he]
    exact hα'
  have hfullX : ∀ (p : ℕ) [Fact p.Prime], (p : k) ≠ 0 →
      Submodule.span ℤ_[p] (Set.range (tateHom p X.curve E₀)) = ⊤ :=
    fun p _ hp => span_tateHom_eq_top PX hp X.supersingular.1 h₀.1
  have hφlev := mem_levelHom_of_comp PY X.supersingular.1 Y.supersingular.1 h₀.1 N hN.ne'
    PtX hPtX PtY hPtY P₀ hP₀ hpk hfullX φ hlev
  refine ⟨{ hom := φ, inv := ψ, hom_inv := hφψ, inv_hom := hψφ, map_level := ?_ }⟩
  have hle : X.level.map (ptMap (L := k) φ) ≤ Y.level := by
    rw [hXl, hYl, Subgroup.map_le_iff_le_comap]
    intro R hR
    exact hφlev R hR
  have hinj : Function.Injective (ptMap (L := k) φ) := by
    intro R R' hRR
    have h1 : R ≫ φ.hom ≫ ψ.hom = R' ≫ φ.hom ≫ ψ.hom := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ ψ.hom) hRR
    rwa [hφψ, Category.comp_id, Category.comp_id] at h1
  haveI : Finite Y.level := Nat.finite_of_card_ne_zero (by rw [Y.card_level]; exact hN.ne')
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective hinj, X.card_level, Y.card_level]

include h hmax in
/-- **Injectivity.** Equal classes come from isomorphic enhanced curves. Rests on
`hEt` (bijection clause in separable scope), `hInv` and the reach binder
`hR : SeparableReach E₀` (a specialization of Voight p. 786, GLUE), which supplies
the reach premises of `hEt` for the two curves. -/
theorem levelDeuringClass_injective (hEt : VoightThm4232Etale) (hR : SeparableReach E₀) :
    Function.Injective (levelDeuringClass h hN hcop h₀ hP₀ j hmax hInv) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ X =>
  induction y using Quotient.inductionOn with
  | _ Y =>
  have h1 : enhancedLeftClass hN hcop hP₀ hInv h₀ (S := S) (j := j) (Quotient.mk _ X) =
      enhancedLeftClass hN hcop hP₀ hInv h₀ (S := S) (j := j) (Quotient.mk _ Y) := by
    apply (leftClassSetEquiv _).injective
    exact (classSetEquivOfReference (enhancedReferenceCoordinate_spec h hN hcop h₀ hP₀ j hmax)).injective hxy
  obtain ⟨u, hu⟩ := Quotient.exact h1
  exact Quotient.sound (nonempty_enhancedIso_of_translate hN hcop h₀ hP₀ j hEt X Y _ _ u hu
    (hR X.curve X.supersingular) (hR Y.curve Y.supersingular))

end Injective

end ZInQ.Manuscript.RC.HCMV21
