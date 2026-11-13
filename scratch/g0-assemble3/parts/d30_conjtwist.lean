/-! ## g0-assemble3: conj-twist §13-§16 (scratch/conj-twist/ConjTwist.lean lines 1624-1996, verbatim, inside its
file's `noncomputable section`, `namespace G0Galois` and opens, lines 37-43). §1-§12 are part a30 (whose
`ConjUniformization` now carries `[NumberField K]`, as in L1093-1102 there). §17 is not copied: its `G10Glue` is
g10-odd's opaque-hypothesis version; part 70's `G10Glue` with `g10Glue_of_conjTwist` (part a30) is used. -/
noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj

/-! ## §13. N1-surj from T5 and a uniformization (proved)

Given a uniformization `Φ : ℂ^g → A(ℂ)_σ` with full lattice `Λ`, `A(ℂ)[n]` injects into
`(ℤ/n)^{2g}` (`Q = Φ(z) ↦` the coordinates of `nz ∈ Λ` mod `n`), and `A(K̄)[n] ≅ (ℤ/n)^{2g}` by T5
(`PkgI2.TorsionStructure`). `toC` is injective, so it is a bijection on `n`-torsion. -/

/-- **Torsion surjectivity from T5 (proved).** -/
theorem torsion_surj_of_T5 (h5 : PkgI2.TorsionStructure.{0}) {K : Type} [Field K]
    (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))
    (hΦ : IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ)
    (hd : A.dim = (g : WithBot ℕ∞)) (n : ℕ) (hn : 0 < n)
    (Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))) (hQ : Q ^ n = 1) :
    ∃ P, toC A emb P = Q := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  have hnK : (n : K) ≠ 0 := by
    intro h0
    have := congrArg (emb.comp (algebraMap K (AlgebraicClosure K))) h0
    rw [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.mpr hn.ne') this
  obtain ⟨e, -⟩ := h5 K (ObjBridge.toGrp A) g n hd hn hnK
  let S := {P : A.Pt (AlgebraicClosure K) // P ^ n = 1}
  let T := {Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))) // Q ^ n = 1}
  let f : S → T := fun P => ⟨toC A emb P.1, by rw [← map_pow, P.2, map_one]⟩
  have hf : Function.Injective f := fun P P' h =>
    Subtype.ext (toC_injective A emb (congrArg Subtype.val h))
  have hpre : ∀ Q : T, ∃ z, Φ z = Q.1 := fun Q => hΦ.2.2.1 Q.1
  choose zz hzz using hpre
  have hnz : ∀ Q : T, n • zz Q ∈ Λ := fun Q => by
    rw [← hΦ.2.1, phi_nsmul A emb Φ hΦ.1, hzz, Q.2]
  let code : T → (Module.Free.ChooseBasisIndex ℤ Λ → ZMod n) := fun Q i =>
    ((b.repr ⟨n • zz Q, hnz Q⟩ i : ℤ) : ZMod n)
  have hcode : Function.Injective code := by
    intro Q Q' hQQ
    have hdvd : ∀ i, (n : ℤ) ∣ b.repr ⟨n • zz Q', hnz Q'⟩ i - b.repr ⟨n • zz Q, hnz Q⟩ i :=
      fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hQQ i)
    choose k hk using hdvd
    let mu : Λ := ∑ i, k i • b i
    have hmu : (⟨n • zz Q', hnz Q'⟩ : Λ) - ⟨n • zz Q, hnz Q⟩ = (n : ℤ) • mu := by
      apply b.repr.injective
      refine Finsupp.ext fun i => ?_
      rw [map_sub, Finsupp.sub_apply, hk i, map_smul, Finsupp.smul_apply, smul_eq_mul]
      congr 1
      exact (congrFun (b.repr_sum_self k) i).symm
    have hvec : n • zz Q' - n • zz Q = (n : ℤ) • (mu : Fin g → ℂ) := by
      have := congrArg Subtype.val hmu
      simpa using this
    have e3 : (n : ℂ) • (zz Q' - zz Q) = (n : ℂ) • (mu : Fin g → ℂ) := by
      rw [smul_sub, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hvec,
        natCast_zsmul]
    have e4 : zz Q' - zz Q = mu :=
      smul_right_injective (Fin g → ℂ) (Nat.cast_ne_zero.mpr hn.ne' : (n : ℂ) ≠ 0) e3
    apply Subtype.ext
    rw [← hzz Q, ← hzz Q', show zz Q' = zz Q + mu by rw [← e4]; abel, hΦ.1,
      (hΦ.2.1 _).mpr mu.2, _root_.mul_one]
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Finite T := Finite.of_injective code hcode
  have hcardS : Nat.card S = n ^ (2 * g) := by
    have hSe : Nat.card S = Nat.card (Fin (2 * g) → ZMod n) := Nat.card_congr e
    rw [hSe, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcardT : Nat.card T ≤ n ^ (2 * g) := by
    have h1 := Nat.card_le_card_of_injective code hcode
    rw [Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex ℤ Λ),
      ← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ Λ,
      Module.finrank_pi_fintype] at h1
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h1
    simpa [mul_comm] using h1
  have hbij := hf.bijective_of_nat_card_le (hcardS ▸ hcardT)
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, congrArg Subtype.val hP⟩

/-- **N4' from T5 (proved).** -/
theorem tateLatticeInj_of_T5 (h5 : PkgI2.TorsionStructure.{0}) : TateLatticeInj := by
  intro K _ A emb g Λ Φ hd _ hlat hΦ ℓ _
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  have hsurj := fun n hn Q hQ => torsion_surj_of_T5 h5 A emb g Λ Φ hΦ hd n hn Q hQ
  refine ⟨(xLin A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj).liftBaseChange ℤ_[ℓ],
    xLin_liftBaseChange_injective A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj, fun lam n => ?_⟩
  rw [LinearMap.liftBaseChange_one_tmul]
  exact xSeq_apply A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj lam n

/-- **Final: `ConjTwistNontrivial` from T5, T26, T35, N2 and N3a (proved).** -/
theorem conjTwistNontrivial_final (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) (hN3a : ConjUniformization) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN2 (conjAntiLiftLat_of hN2 hN3a)
    (tateLatticeInj_of_T5 h5)

/-- **Final: `ConjTwistFromLeaves` from N2 and N3a (proved).** T5, T26 and T35 are among the
hypotheses of `ConjTwistFromLeaves`. -/
theorem conjTwistFromLeaves_final (hN2 : HomLinearLift) (hN3a : ConjUniformization) :
    ConjTwistFromLeaves :=
  fun _ _ h35 h5 hT => conjTwistNontrivial_final h5 hT h35 hN2 hN3a

/-! ## §14. N3a split: group-theoretic clauses (proved) and analytic clauses (glue) -/

theorem twistC_inj_aux' {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) :
    mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫
    Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ 𝟙 _ = 𝟙 _
  rw [Category.id_comp, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem twistC_surjective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : Function.Surjective (twistC A σ s h) := by
  intro Q'
  obtain ⟨X, hX⟩ := ((Over.mapPullbackAdj (specS s)).homEquiv (cptObj σ) A.X).surjective
    (show cptObj σ ⟶ (Over.pullback (specS s)).obj A.X from Q')
  refine ⟨conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ X, ?_⟩
  have e : mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ X = X := by
    have := congrArg (· ≫ X) (twistC_inj_aux' σ s h)
    simpa only [Category.assoc, Category.id_comp] using this
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫
    conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ X) = Q'
  rw [e]
  exact hX

theorem twistC_mul {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q Q' : CPts A σ) :
    twistC A σ s h (Q * Q') = twistC A σ s h Q * twistC A σ s h Q' := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ (Q * Q')) =
    (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ Q) *
    (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ Q')
  rw [MonObj.comp_mul, MonObj.comp_mul, homEquiv_mul_conj]

/-- **N3a-an. The analytic clauses for the conjugate uniformization (GLUE, unproved;
STANDARD).** With `ψ(z) = twistC(Φ(z̄))`: the preimages `ψ⁻¹(U(ℂ))` of opens `U` of `A^s` are
open, and regular functions of `A^s` are holomorphic along `ψ`. (`A^s(ℂ)_σ = A(ℂ)_{conj∘σ}`; on
affine charts `twistC` conjugates the values of regular functions, and `z ↦ conj(f(z̄))` is
holomorphic when `f` is; Mumford §1, GAGA.) These are the last two clauses of
`IsUniformization`; the first three are proved (`conjUniformization_of_analytic`). -/
def ConjUniformizationAnalytic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    (∀ U, IsOpen (ZInQ.LeafPush2.cDom (fun z => twistC A σ s h (Φ (conjL g z))) U)) ∧
    (∀ U (f : Γ((conjVar A s).X.left, U)), DifferentiableOn ℂ
      (fun z => ZInQ.LeafPush2.cEvalAt (twistC A σ s h (Φ (conjL g z))) U f)
      (ZInQ.LeafPush2.cDom (fun z => twistC A σ s h (Φ (conjL g z))) U))

/-- **N3a from its analytic clauses (proved).** -/
theorem conjUniformization_of_analytic (h : ConjUniformizationAnalytic) : ConjUniformization := by
  intro K _ _ A σ s hs g Λ Φ hd hΦ
  obtain ⟨h4, h5⟩ := h K A σ s hs g Λ Φ hd hΦ
  refine ⟨fun z w => ?_, fun z => ?_, fun Q => ?_, h4, h5⟩
  · beta_reduce
    rw [map_add, hΦ.1, twistC_mul]
  · beta_reduce
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, ← hΦ.2.1]
    constructor
    · intro h1
      apply twistC_injective A σ s hs
      rw [h1, twistC_one]
    · intro h1
      rw [h1, twistC_one]
  · obtain ⟨Q₀, rfl⟩ := twistC_surjective A σ s hs Q
    obtain ⟨z, hz⟩ := hΦ.2.2.1 Q₀
    exact ⟨conjL g z, by simp only [conjL_conjL, hz]⟩

/-- **Final: `ConjTwistNontrivial` from T5, T26, T35, N2 and N3a-an (proved).** -/
theorem conjTwistNontrivial_final' (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) (hN3 : ConjUniformizationAnalytic) : ConjTwistNontrivial :=
  conjTwistNontrivial_final h5 hT h35 hN2 (conjUniformization_of_analytic hN3)

/-- **Final: `ConjTwistFromLeaves` from N2 and N3a-an (proved).** -/
theorem conjTwistFromLeaves_final' (hN2 : HomLinearLift) (hN3 : ConjUniformizationAnalytic) :
    ConjTwistFromLeaves :=
  conjTwistFromLeaves_final hN2 (conjUniformization_of_analytic hN3)

/-! ## §15. N3a-an from an evaluation identity (proved reduction)

The analytic clauses follow from a purely scheme-theoretic identity (`TwistCEval`): for a number
field, every open `U` of `A^s` is the preimage of an open `V` of `A`, and the value of a section
of `A^s` over `U` at `twistC Q` is the complex conjugate of the value of a section of `A` over `V`
at `Q`. With it, `ψ = twistC ∘ Φ ∘ conj` has open domains `conj⁻¹(cDom Φ V)` and its coordinate
functions are `z ↦ conj(F(z̄))` with `F` holomorphic (`differentiableOn_conj_conj`). -/

theorem conjL_smul {g : ℕ} (c : ℂ) (v : Fin g → ℂ) :
    conjL g (c • v) = starRingEnd ℂ c • conjL g v := by
  funext i; simp [conjL]

/-- **`z ↦ conj(F(z̄))` is holomorphic where `F` is (proved).** -/
theorem differentiableOn_conj_conj {g : ℕ} {F : (Fin g → ℂ) → ℂ} {S : Set (Fin g → ℂ)}
    (hF : DifferentiableOn ℂ F S) :
    DifferentiableOn ℂ (fun z => starRingEnd ℂ (F (conjL g z))) (conjL g ⁻¹' S) := by
  intro x hx
  obtain ⟨F', hF'⟩ := hF (conjL g x) hx
  let cV : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (conjL g)
  let Gl : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => starRingEnd ℂ (F' (conjL g v))
      map_add' := fun v w => by simp [map_add]
      map_smul' := fun c v => by simp [conjL_smul, map_smul, smul_eq_mul] }
  let G' : (Fin g → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap Gl
  have h1 : HasFDerivWithinAt (fun z => F (conjL g z)) ((F'.restrictScalars ℝ).comp cV)
      (conjL g ⁻¹' S) x :=
    (hF'.restrictScalars ℝ).comp x cV.hasFDerivWithinAt (fun z hz => hz)
  have h2 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasFDerivWithinAt x h1
  have h3 : HasFDerivWithinAt (fun z => starRingEnd ℂ (F (conjL g z))) G' (conjL g ⁻¹' S) x := by
    refine h2.of_restrictScalars ℝ ?_
    ext v
    rfl
  exact h3.differentiableWithinAt

/-- **N3a-ev. Values of sections at twisted points (GLUE, unproved; STANDARD; no analysis).**
For a number field `K` (so `A^s → A` is an isomorphism), every open `U` of `A^s` corresponds to an
open `V` of `A` with `twistC Q ∈ U ↔ Q ∈ V`, and every section `f` of `A^s` over `U` to a section
`f'` of `A` over `V` with `f(twistC Q) = conj(f'(Q))`. (`fst ∘ twistC Q = Q ∘ Spec(conj)` as maps
`Spec ℂ → A`; take `V = fst(U)`, `f = fst^* f'`; `Spec(conj)^*` is `conj` on `Γ(Spec ℂ) = ℂ`.) -/
def TwistCEval : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (U : (conjVar A s).X.left.Opens),
    ∃ V : A.X.left.Opens,
      (∀ Q : CPts A σ, (⊤ ≤ (twistC A σ s h Q).left ⁻¹ᵁ U ↔ ⊤ ≤ Q.left ⁻¹ᵁ V)) ∧
      ∀ f : Γ((conjVar A s).X.left, U), ∃ f' : Γ(A.X.left, V), ∀ Q : CPts A σ,
        ⊤ ≤ Q.left ⁻¹ᵁ V →
        ZInQ.LeafPush2.cEvalAt (twistC A σ s h Q) U f =
          starRingEnd ℂ (ZInQ.LeafPush2.cEvalAt Q V f')

/-- **N3a-an (number fields) from N3a-ev (proved).** -/
theorem conjUniformizationAnalytic_of_eval (hE : TwistCEval) : ConjUniformizationAnalytic := by
  intro K _ _ A σ s h g Λ Φ hd hΦ
  have hdom : ∀ U, ∃ V : A.X.left.Opens,
      ZInQ.LeafPush2.cDom (fun z => twistC A σ s h (Φ (conjL g z))) U =
        conjL g ⁻¹' ZInQ.LeafPush2.cDom Φ V ∧
      ∀ f : Γ((conjVar A s).X.left, U), ∃ f' : Γ(A.X.left, V), ∀ z,
        z ∈ conjL g ⁻¹' ZInQ.LeafPush2.cDom Φ V →
        ZInQ.LeafPush2.cEvalAt (twistC A σ s h (Φ (conjL g z))) U f =
          starRingEnd ℂ (ZInQ.LeafPush2.cEvalAt (Φ (conjL g z)) V f') := by
    intro U
    obtain ⟨V, hV, hf⟩ := hE K A σ s h U
    refine ⟨V, ?_, fun f => ?_⟩
    · ext z
      exact hV (Φ (conjL g z))
    · obtain ⟨f', hf'⟩ := hf f
      exact ⟨f', fun z hz => hf' _ hz⟩
  have hcont : Continuous (conjL g) :=
    (LinearMap.toContinuousLinearMap (conjL g)).continuous
  refine ⟨fun U => ?_, fun U f => ?_⟩
  · obtain ⟨V, hV, -⟩ := hdom U
    rw [hV]
    exact (hΦ.2.2.2.1 V).preimage hcont
  · obtain ⟨V, hV, hf⟩ := hdom U
    obtain ⟨f', hf'⟩ := hf f
    rw [hV]
    exact (differentiableOn_conj_conj (hΦ.2.2.2.2 V f')).congr fun z hz => hf' z hz

/-- **Final: `ConjTwistNontrivial` from T5, T26, T35, N2 and N3a-ev (proved).** -/
theorem conjTwistNontrivial_final'' (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) (hE : TwistCEval) : ConjTwistNontrivial :=
  conjTwistNontrivial_final' h5 hT h35 hN2 (conjUniformizationAnalytic_of_eval hE)

/-- **Final: `ConjTwistFromLeaves` from N2 and N3a-ev (proved).** -/
theorem conjTwistFromLeaves_final'' (hN2 : HomLinearLift) (hE : TwistCEval) :
    ConjTwistFromLeaves :=
  conjTwistFromLeaves_final' hN2 (conjUniformizationAnalytic_of_eval hE)

/-! ## §16. `TwistCEval` (N3a-ev) proved

For a number field `Spec(s)` is an isomorphism, hence so is `fst : A^s → A`. The adjunction gives
`(twistC Q).left ≫ fst = Spec(conj) ≫ Q.left`, so `(twistC Q).left = Spec(conj) ≫ Q.left ≫ fst⁻¹`;
take `V = (fst⁻¹)⁻¹(U)`, `f' = (fst⁻¹)^* f`, and use `ΓSpecIso` naturality for `Spec(conj)`. -/

/-- `Spec(conj) : Spec ℂ → Spec ℂ`. -/
abbrev specConj : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (starRingEnd ℂ))

theorem appLE_eq_of_eq {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V (e ▸ h) := by
  subst e; rfl

theorem top_le_specConj_preimage (W : (Spec (CommRingCat.of ℂ)).Opens) :
    ⊤ ≤ specConj ⁻¹ᵁ W ↔ ⊤ ≤ W := by
  constructor
  · intro hW x _
    have hx : x = specConj.base (IsLocalRing.closedPoint ℂ) := Subsingleton.elim _ _
    rw [hx]
    exact hW (Set.mem_univ (IsLocalRing.closedPoint ℂ))
  · intro hW y _
    exact hW (Set.mem_univ (specConj.base y))

/-- Evaluation at `P ∘ Spec(conj)` is the complex conjugate of evaluation at `P` (proved). -/
theorem eval_specConj {X : Scheme} (P : Spec (CommRingCat.of ℂ) ⟶ X) (W : X.Opens)
    (hW : ⊤ ≤ (specConj ≫ P) ⁻¹ᵁ W) (hW' : ⊤ ≤ P ⁻¹ᵁ W) (x : Γ(X, W)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((specConj ≫ P).appLE W ⊤ hW x) =
      starRingEnd ℂ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (P.appLE W ⊤ hW' x)) := by
  have e2 : ⊤ ≤ specConj ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := fun x _ => Set.mem_univ _
  rw [← Scheme.Hom.appLE_comp_appLE specConj P W ⊤ ⊤ hW' e2]
  have e3 : specConj.appLE ⊤ ⊤ e2 = specConj.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [e3]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (starRingEnd ℂ))
  have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (P.appLE W ⊤ hW' x)) h
  exact this

theorem homEquiv_left_fst {K : Type} [Field K] (s : K →+* K) (X Y : Over (Spec (CommRingCat.of K)))
    (u : (Over.map (specS s)).obj X ⟶ Y) :
    ((Over.mapPullbackAdj (specS s)).homEquiv X Y u).left ≫ Limits.pullback.fst Y.hom (specS s) =
      u.left := by
  dsimp [Over.mapPullbackAdj]
  simp

theorem fst_isIso {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (s : K →+* K) :
    IsIso (Limits.pullback.fst A.X.hom (specS s)) := by
  have hb := ringHom_bijective_of_numberField K s
  let e : K ≃+* K := RingEquiv.ofBijective s hb
  haveI : IsIso (CommRingCat.ofHom s) :=
    ⟨⟨CommRingCat.ofHom (e.symm : K →+* K), by ext x; exact e.symm_apply_apply x,
      by ext x; exact e.apply_symm_apply x⟩⟩
  haveI : IsIso (specS s) := by unfold specS; infer_instance
  infer_instance

/-- **N3a-ev (proved).** -/
theorem twistCEval : TwistCEval := by
  intro K _ _ A σ s h U
  let fstC : (conjVar A s).X.left ⟶ A.X.left := Limits.pullback.fst A.X.hom (specS s)
  haveI : IsIso fstC := fst_isIso A s
  let iv : A.X.left ⟶ (conjVar A s).X.left := CategoryTheory.inv fstC
  let QL : CPts A σ → (Spec (CommRingCat.of ℂ) ⟶ A.X.left) := fun Q => Q.left
  let TL : CPts A σ → (Spec (CommRingCat.of ℂ) ⟶ (conjVar A s).X.left) :=
    fun Q => (twistC A σ s h Q).left
  have key : ∀ Q : CPts A σ, TL Q = specConj ≫ QL Q ≫ iv := by
    intro Q
    have e1 : TL Q ≫ fstC = specConj ≫ QL Q :=
      (homEquiv_left_fst s (cptObj σ) A.X (mapPtIso σ s ≫ conjCs A σ s h Q)).trans
        (Category.id_comp _)
    calc TL Q = (TL Q ≫ fstC) ≫ iv := by
          rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      _ = specConj ≫ QL Q ≫ iv := by rw [e1, Category.assoc]
  refine ⟨iv ⁻¹ᵁ U, fun Q => ?_, fun f => ⟨iv.app U f, fun Q hQ => ?_⟩⟩
  · change ⊤ ≤ TL Q ⁻¹ᵁ U ↔ ⊤ ≤ QL Q ⁻¹ᵁ (iv ⁻¹ᵁ U)
    rw [key Q]
    change ⊤ ≤ specConj ⁻¹ᵁ ((QL Q ≫ iv) ⁻¹ᵁ U) ↔ _
    rw [top_le_specConj_preimage]
    rfl
  · have hQ' : ⊤ ≤ TL Q ⁻¹ᵁ U := by
      rw [key Q]
      change ⊤ ≤ specConj ⁻¹ᵁ ((QL Q ≫ iv) ⁻¹ᵁ U)
      rw [top_le_specConj_preimage]
      exact hQ
    unfold ZInQ.LeafPush2.cEvalAt
    rw [dif_pos (show ⊤ ≤ (twistC A σ s h Q).left ⁻¹ᵁ U from hQ'), dif_pos hQ]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((TL Q).appLE U ⊤ hQ' f) =
      starRingEnd ℂ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((QL Q).appLE (iv ⁻¹ᵁ U) ⊤ hQ (iv.app U f)))
    rw [appLE_eq_of_eq (key Q),
      eval_specConj (QL Q ≫ iv) U _ (show ⊤ ≤ (QL Q ≫ iv) ⁻¹ᵁ U from hQ),
      Scheme.Hom.comp_appLE]
    rfl

/-- **Final: `ConjTwistNontrivial` from T5, T26, T35 and N2 (proved).** -/
theorem conjTwistNontrivial_of_leaves (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) : ConjTwistNontrivial :=
  conjTwistNontrivial_final'' h5 hT h35 hN2 twistCEval

/-- **Final: `ConjTwistFromLeaves` from the leaf N2 alone (proved).** -/
theorem conjTwistFromLeaves_of_homLinearLift (hN2 : HomLinearLift) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_final'' hN2 twistCEval

end G0Galois

end
