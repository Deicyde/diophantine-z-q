import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.H1Descent
/-!
# The standard etale case of descent for `H1Cotangent`

Target: `H1DescentStandardEtale` (defined in `Y3H1Descent`): if `S -> T` is standard etale and
`H1(L_{T/R}) = 0`, then `T ⊗[S] H1(L_{S/R}) = 0`.

Printed source: Stacks, More on Algebra, Lemma 15.34.6 (Tag 07D4), standard etale case, together
with the base change description of the naive cotangent complex (Tag 00S2) and the computation of
`H1` by any formally smooth presentation (Tag 00S1, Algebra Lemma 10.134.2).

Construction. Let `A = R[S]` be the canonical presentation of `S`, with kernel `I`, and let
`T ≅ S[x][1/g]/(f)` be a standard etale presentation (`f` monic, `f'` invertible in `T`).
1. Lift `f` to a monic `F` and `g` to `G` over `A` (`Polynomial.lifts_and_degree_eq_and_monic`).
2. `E := A[x][1/(G F')]/(F)` is the standard etale `A`-algebra of the pair `(F, G F')`; it is etale,
   hence flat, over `A`, and formally smooth over `R`.
3. `x` gives an `A`-algebra map `E -> T` (`StandardEtalePair.lift`); it is surjective because every
   element of `T` has the form `p(x) g(x)^(-n)` (`exists_mul_aeval_x_g_pow_eq_aeval_x`).
4. Its kernel is `I E`: the class of `X` in `E / I E` is a root of `(f, g)`, so the presentation of
   `T` gives `T -> E / I E`, and the two composites `E -> E / I E` agree on `X`.
5. Flatness of `E` over `A` makes `E ⊗[A] I -> I E` bijective, so
   `Algebra.Extension.tensorH1CotangentOfFormallyEtale` gives `T ⊗[S] H1(S/R) ≃ H1(T/R)`.
The case `S = 0` is trivial (and is excluded by the monic lift lemma).

Names are prefixed `h1StdEt_`. The module `Y3H1Descent` is imported for the definition of
`H1DescentStandardEtale` and for its reduction lemma, used in the two closing corollaries.
-/

set_option autoImplicit false

noncomputable section

namespace Y3Buzzard.SourceDescent

/-! ## The canonical presentation and the comparison extension -/

/-- The canonical presentation `R[S] -> S`. -/
abbrev h1StdEt_P (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.Extension R S :=
  (Algebra.Generators.self R S).toExtension

/-- The extension of `T` given by a surjective algebra map `E -> T`. -/
abbrev h1StdEt_ext (R T E : Type) [CommRing R] [CommRing T] [CommRing E] [Algebra R T]
    [Algebra R E] [Algebra E T] [IsScalarTower R E T]
    (h : Function.Surjective (algebraMap E T)) : Algebra.Extension R T where
  Ring := E
  commRing := inferInstance
  algebra₁ := inferInstance
  algebra₂ := inferInstance
  isScalarTower := inferInstance
  σ := fun t => Classical.choose (h t)
  algebraMap_σ := fun t => Classical.choose_spec (h t)

/-- The map of extensions from `R[S] -> S` to `E -> T`, given by the algebra map `R[S] -> E`. -/
def h1StdEt_hom (R S T E : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra S T] [CommRing E] [Algebra R E] [Algebra (h1StdEt_P R S).Ring E]
    [IsScalarTower R (h1StdEt_P R S).Ring E] [Algebra E T] [IsScalarTower R E T]
    (hsurj : Function.Surjective (algebraMap E T))
    (hcomp : ∀ a, algebraMap E T (algebraMap (h1StdEt_P R S).Ring E a) =
      algebraMap S T (algebraMap (h1StdEt_P R S).Ring S a)) :
    (h1StdEt_P R S).Hom (h1StdEt_ext R T E hsurj) where
  toRingHom := algebraMap (h1StdEt_P R S).Ring E
  toRingHom_algebraMap := fun r =>
    (IsScalarTower.algebraMap_apply R (h1StdEt_P R S).Ring E r).symm
  algebraMap_toRingHom := hcomp

/-! ## The kernel comparison `E ⊗[A] I ≃ J` -/

/-- If `E` is flat over `A = R[S]` and the kernel of `E -> T` is `I E`, then
`E ⊗[A] I -> ker (E -> T)` is bijective. -/
theorem h1StdEt_liftBaseChange_bijective (R S T E : Type) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [CommRing E] [Algebra R E]
    [Algebra (h1StdEt_P R S).Ring E] [IsScalarTower R (h1StdEt_P R S).Ring E] [Algebra E T]
    [IsScalarTower R E T] [Module.Flat (h1StdEt_P R S).Ring E]
    (hsurj : Function.Surjective (algebraMap E T))
    (hcomp : ∀ a, algebraMap E T (algebraMap (h1StdEt_P R S).Ring E a) =
      algebraMap S T (algebraMap (h1StdEt_P R S).Ring S a))
    (hker : RingHom.ker (algebraMap E T) ≤ Ideal.map (algebraMap (h1StdEt_P R S).Ring E)
      (RingHom.ker (algebraMap (h1StdEt_P R S).Ring S)))
    (halg : algebraMap (h1StdEt_P R S).Ring (h1StdEt_ext R T E hsurj).Ring =
      (h1StdEt_hom R S T E hsurj hcomp).toRingHom) :
    Function.Bijective (LinearMap.liftBaseChange (h1StdEt_ext R T E hsurj).Ring
      ((h1StdEt_hom R S T E hsurj hcomp).mapKer halg)) := by
  -- the inclusion `I -> A`
  let ι : (h1StdEt_P R S).ker →ₗ[(h1StdEt_P R S).Ring] (h1StdEt_P R S).Ring :=
    (h1StdEt_P R S).ker.subtype
  -- after the inclusion `J -> E`, the comparison map is `E ⊗[A] I -> E ⊗[A] A = E`
  have key : ∀ z, (((LinearMap.liftBaseChange (h1StdEt_ext R T E hsurj).Ring
      ((h1StdEt_hom R S T E hsurj hcomp).mapKer halg)) z : (h1StdEt_ext R T E hsurj).ker) : E) =
      TensorProduct.rid (h1StdEt_P R S).Ring E (LinearMap.lTensor E ι z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul e y =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
        Submodule.coe_smul, Algebra.Extension.Hom.mapKer_apply_coe, smul_eq_mul,
        Algebra.smul_def]
      exact mul_comm _ _
    | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]
  have hinj0 : Function.Injective (LinearMap.lTensor E ι) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := E) ι
      ((h1StdEt_P R S).ker.injective_subtype)
  refine ⟨fun z w hzw => hinj0 ((TensorProduct.rid (h1StdEt_P R S).Ring E).injective ?_),
    fun j => ?_⟩
  · exact (key z).symm.trans
      ((congrArg (fun u : (h1StdEt_ext R T E hsurj).ker => (u : E)) hzw).trans (key w))
  · have hj : (j : E) ∈ RingHom.ker (algebraMap E T) := j.2
    have hj' := hker hj
    have hle : Ideal.map (algebraMap (h1StdEt_P R S).Ring E)
        (RingHom.ker (algebraMap (h1StdEt_P R S).Ring S)) ≤
        LinearMap.range (((h1StdEt_ext R T E hsurj).ker.subtype).comp
          (LinearMap.liftBaseChange (h1StdEt_ext R T E hsurj).Ring
            ((h1StdEt_hom R S T E hsurj hcomp).mapKer halg))) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      refine LinearMap.mem_range.mpr
        ⟨(1 : E) ⊗ₜ[(h1StdEt_P R S).Ring] (⟨a, ha⟩ : (h1StdEt_P R S).ker), ?_⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.liftBaseChange_tmul,
        one_smul, Algebra.Extension.Hom.mapKer_apply_coe] <;> rfl
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (hle hj')
    exact ⟨z, Subtype.ext hz⟩

/-! ## The comparison of `H1` from a lift -/

/-- Given an `A = R[S]`-algebra `E` which is formally etale and flat over `A`, formally smooth
over `R`, and maps onto `T` with kernel `I E` compatibly with `S -> T`, there is a `T`-linear
equivalence `T ⊗[S] H1(S/R) ≃ H1(T/R)`. -/
theorem h1StdEt_nonempty_equiv_of_lift (R S T E : Type) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Module.Flat S T]
    [CommRing E] [Algebra R E] [Algebra (h1StdEt_P R S).Ring E]
    [IsScalarTower R (h1StdEt_P R S).Ring E] [Algebra E T] [IsScalarTower R E T]
    [Algebra.FormallyEtale (h1StdEt_P R S).Ring E] [Module.Flat (h1StdEt_P R S).Ring E]
    [Algebra.FormallySmooth R E]
    (hsurj : Function.Surjective (algebraMap E T))
    (hcomp : ∀ a, algebraMap E T (algebraMap (h1StdEt_P R S).Ring E a) =
      algebraMap S T (algebraMap (h1StdEt_P R S).Ring S a))
    (hker : RingHom.ker (algebraMap E T) ≤ Ideal.map (algebraMap (h1StdEt_P R S).Ring E)
      (RingHom.ker (algebraMap (h1StdEt_P R S).Ring S))) :
    Nonempty (TensorProduct S T (Algebra.H1Cotangent R S) ≃ₗ[T] Algebra.H1Cotangent R T) := by
  have halg : algebraMap (h1StdEt_P R S).Ring (h1StdEt_ext R T E hsurj).Ring =
      (h1StdEt_hom R S T E hsurj hcomp).toRingHom := rfl
  have H₁ : (h1StdEt_hom R S T E hsurj hcomp).toRingHom.FormallyEtale := by
    show (algebraMap (h1StdEt_P R S).Ring E).FormallyEtale
    exact RingHom.formallyEtale_algebraMap.mpr inferInstance
  have H₂ := h1StdEt_liftBaseChange_bijective R S T E hsurj hcomp hker halg
  haveI : Algebra.FormallySmooth R (h1StdEt_ext R T E hsurj).Ring :=
    ‹Algebra.FormallySmooth R E›
  exact ⟨(LinearEquiv.baseChange S T _ _
      (Algebra.Generators.self R S).equivH1Cotangent).symm.trans
    ((Algebra.Extension.tensorH1CotangentOfFormallyEtale (h1StdEt_hom R S T E hsurj hcomp)
      halg H₁ H₂).trans (h1StdEt_ext R T E hsurj).equivH1CotangentOfFormallySmooth)⟩

/-! ## The lift of a standard etale algebra -/

/-- For `S -> T` standard etale with `S` nontrivial, `T ⊗[S] H1(S/R) ≃ₗ[T] H1(T/R)`. -/
theorem h1StdEt_nonempty_equiv (R S T : Type) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Nontrivial S]
    (hstd : Algebra.IsStandardEtale S T) :
    Nonempty (TensorProduct S T (Algebra.H1Cotangent R S) ≃ₗ[T] Algebra.H1Cotangent R T) := by
  haveI : Algebra.IsStandardEtale S T := hstd
  haveI : Module.Flat S T := Algebra.Smooth.flat S T
  obtain ⟨pres⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := T)
  -- `A = R[S] -> S` is surjective
  have hπ : Function.Surjective (algebraMap (h1StdEt_P R S).Ring S) := fun s =>
    ⟨(h1StdEt_P R S).σ s, (h1StdEt_P R S).algebraMap_σ s⟩
  -- lift `f` to a monic `F` and `g` to `G` over `A`
  obtain ⟨F, hFmap, -, hFmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (f := algebraMap (h1StdEt_P R S).Ring S)
    ((Polynomial.mem_lifts pres.P.f).mpr (Polynomial.map_surjective _ hπ pres.P.f))
    pres.P.monic_f
  obtain ⟨G, hGmap⟩ := Polynomial.map_surjective (algebraMap (h1StdEt_P R S).Ring S) hπ pres.P.g
  -- the standard etale pair `(F, G F')` over `A`
  obtain ⟨Ep, hEpf, hEpg⟩ : ∃ Ep : StandardEtalePair (h1StdEt_P R S).Ring,
      Ep.f = F ∧ Ep.g = G * Polynomial.derivative F :=
    ⟨⟨F, hFmonic, G * Polynomial.derivative F, ⟨G, 0, 1, by ring⟩⟩, rfl, rfl⟩
  -- algebra structures: `R -> A -> E` and `A -> S -> T`
  letI : Algebra R Ep.Ring :=
    ((algebraMap (h1StdEt_P R S).Ring Ep.Ring).comp (algebraMap R (h1StdEt_P R S).Ring)).toAlgebra
  haveI : IsScalarTower R (h1StdEt_P R S).Ring Ep.Ring :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra (h1StdEt_P R S).Ring T :=
    ((algebraMap S T).comp (algebraMap (h1StdEt_P R S).Ring S)).toAlgebra
  haveI : IsScalarTower (h1StdEt_P R S).Ring S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- `x` is a root of `(F, G F')` in `T`
  have hx : Ep.HasMap pres.x := by
    refine ⟨?_, ?_⟩
    · have h0 : Polynomial.aeval pres.x pres.P.f = 0 := pres.hasMap.1
      rw [← hFmap, Polynomial.aeval_map_algebraMap] at h0
      rw [hEpf]
      exact h0
    · have h1 : IsUnit (Polynomial.aeval pres.x (pres.P.g * Polynomial.derivative pres.P.f)) := by
        rw [map_mul]
        exact pres.hasMap.2.mul (StandardEtalePair.HasMap.isUnit_derivative_f pres.P pres.hasMap)
      rw [← hGmap, ← hFmap, Polynomial.derivative_map, ← Polynomial.map_mul,
        Polynomial.aeval_map_algebraMap] at h1
      rw [hEpg]
      exact h1
  -- the map `E -> T`
  letI : Algebra Ep.Ring T := (Ep.lift pres.x hx).toRingHom.toAlgebra
  haveI : IsScalarTower R Ep.Ring T := IsScalarTower.of_algebraMap_eq (fun r =>
    (IsScalarTower.algebraMap_apply R S T r).trans
      ((congrArg (algebraMap S T)
        (IsScalarTower.algebraMap_apply R (h1StdEt_P R S).Ring S r)).trans
        ((Ep.lift pres.x hx).commutes (algebraMap R (h1StdEt_P R S).Ring r)).symm))
  have hcomp : ∀ a, algebraMap Ep.Ring T (algebraMap (h1StdEt_P R S).Ring Ep.Ring a) =
      algebraMap S T (algebraMap (h1StdEt_P R S).Ring S a) := fun a =>
    (Ep.lift pres.x hx).commutes a
  -- surjectivity
  have hu : IsUnit (Polynomial.aeval Ep.X Ep.g) := (StandardEtalePair.hasMap_X (P := Ep)).2
  have e3 : (Ep.lift pres.x hx) (Polynomial.aeval Ep.X Ep.g) =
      Polynomial.aeval pres.x pres.P.g *
        Polynomial.aeval pres.x (Polynomial.derivative pres.P.f) := by
    rw [← Polynomial.aeval_algHom_apply, StandardEtalePair.lift_X, hEpg, map_mul, ← hGmap,
      ← hFmap, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap,
      Polynomial.aeval_map_algebraMap]
  have e4 : (Ep.lift pres.x hx) (↑hu.unit⁻¹ : Ep.Ring) *
      (Polynomial.aeval pres.x pres.P.g *
        Polynomial.aeval pres.x (Polynomial.derivative pres.P.f)) = 1 := by
    rw [← e3, ← map_mul, IsUnit.val_inv_mul, map_one]
  have hsurj : Function.Surjective (algebraMap Ep.Ring T) := by
    intro t
    obtain ⟨p, n, hpn⟩ := pres.exists_mul_aeval_x_g_pow_eq_aeval_x t
    obtain ⟨P', hP'⟩ := Polynomial.map_surjective (algebraMap (h1StdEt_P R S).Ring S) hπ p
    have e1 : (Ep.lift pres.x hx) (Polynomial.aeval Ep.X P') = Polynomial.aeval pres.x p := by
      rw [← Polynomial.aeval_algHom_apply, StandardEtalePair.lift_X, ← hP',
        Polynomial.aeval_map_algebraMap]
    have e2 : (Ep.lift pres.x hx) (Polynomial.aeval Ep.X (Polynomial.derivative F)) =
        Polynomial.aeval pres.x (Polynomial.derivative pres.P.f) := by
      rw [← Polynomial.aeval_algHom_apply, StandardEtalePair.lift_X, ← hFmap,
        Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
    refine ⟨Polynomial.aeval Ep.X P' * Polynomial.aeval Ep.X (Polynomial.derivative F) ^ n *
      (↑hu.unit⁻¹ : Ep.Ring) ^ n, ?_⟩
    show (Ep.lift pres.x hx) (Polynomial.aeval Ep.X P' *
      Polynomial.aeval Ep.X (Polynomial.derivative F) ^ n * (↑hu.unit⁻¹ : Ep.Ring) ^ n) = t
    rw [map_mul, map_mul, map_pow, map_pow, e1, e2]
    have h5 : (Ep.lift pres.x hx) (↑hu.unit⁻¹ : Ep.Ring) ^ n *
        (Polynomial.aeval pres.x pres.P.g ^ n *
          Polynomial.aeval pres.x (Polynomial.derivative pres.P.f) ^ n) = 1 := by
      rw [← mul_pow, ← mul_pow, e4, one_pow]
    linear_combination (-(Polynomial.aeval pres.x (Polynomial.derivative pres.P.f) ^ n *
      (Ep.lift pres.x hx) (↑hu.unit⁻¹ : Ep.Ring) ^ n)) * hpn + t * h5
  -- the kernel of `E -> T` is `I E`
  have hker : RingHom.ker (algebraMap Ep.Ring T) ≤
      Ideal.map (algebraMap (h1StdEt_P R S).Ring Ep.Ring)
        (RingHom.ker (algebraMap (h1StdEt_P R S).Ring S)) := by
    intro e he
    have he' : (Ep.lift pres.x hx) e = 0 := RingHom.mem_ker.mp he
    obtain ⟨J, hJ⟩ : ∃ J : Ideal Ep.Ring, J = Ideal.map (algebraMap (h1StdEt_P R S).Ring Ep.Ring)
        (RingHom.ker (algebraMap (h1StdEt_P R S).Ring S)) := ⟨_, rfl⟩
    -- `S -> E / I E`
    have hθker : RingHom.ker (algebraMap (h1StdEt_P R S).Ring S) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (algebraMap (h1StdEt_P R S).Ring Ep.Ring)) := by
      intro a ha
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hJ]
      exact Ideal.mem_map_of_mem _ ha
    obtain ⟨θ, hθ⟩ : ∃ θ : S →+* Ep.Ring ⧸ J, ∀ a, θ (algebraMap (h1StdEt_P R S).Ring S a) =
        Ideal.Quotient.mk J (algebraMap (h1StdEt_P R S).Ring Ep.Ring a) :=
      ⟨(algebraMap (h1StdEt_P R S).Ring S).liftOfSurjective hπ ⟨_, hθker⟩, fun a =>
        RingHom.liftOfSurjective_comp_apply _ hπ ⟨_, hθker⟩ a⟩
    letI : Algebra S (Ep.Ring ⧸ J) := θ.toAlgebra
    haveI : IsScalarTower (h1StdEt_P R S).Ring S (Ep.Ring ⧸ J) :=
      IsScalarTower.of_algebraMap_eq (fun a =>
        (Ideal.Quotient.mk_algebraMap (h1StdEt_P R S).Ring J a).symm.trans (hθ a).symm)
    -- the class of `X` is a root of `(f, g)` in `E / I E`
    have hX := StandardEtalePair.HasMap.map (StandardEtalePair.hasMap_X (P := Ep))
      (Ideal.Quotient.mkₐ (h1StdEt_P R S).Ring J)
    have hy : pres.P.HasMap (Ideal.Quotient.mkₐ (h1StdEt_P R S).Ring J Ep.X) := by
      refine ⟨?_, ?_⟩
      · rw [← hFmap, Polynomial.aeval_map_algebraMap, ← hEpf]
        exact hX.1
      · have h1 : IsUnit (Polynomial.aeval (Ideal.Quotient.mkₐ (h1StdEt_P R S).Ring J Ep.X)
            (G * Polynomial.derivative F)) := by
          rw [← hEpg]
          exact hX.2
        have h2 : Polynomial.aeval (Ideal.Quotient.mkₐ (h1StdEt_P R S).Ring J Ep.X)
            (Polynomial.map (algebraMap (h1StdEt_P R S).Ring S) (G * Polynomial.derivative F)) =
            Polynomial.aeval (Ideal.Quotient.mkₐ (h1StdEt_P R S).Ring J Ep.X)
              (G * Polynomial.derivative F) := by
          rw [Polynomial.aeval_map_algebraMap]
        rw [← h2, Polynomial.map_mul, ← Polynomial.derivative_map, hGmap, hFmap, map_mul] at h1
        exact isUnit_of_mul_isUnit_left h1
    -- the composite `E -> T -> E / I E` is the quotient map
    have heq : (AlgHom.restrictScalars (h1StdEt_P R S).Ring
        ((pres.P.lift _ hy).comp (pres.equivRing : T →ₐ[S] pres.P.Ring))).comp
          (Ep.lift pres.x hx) = Ideal.Quotient.mkₐ (h1StdEt_P R S).Ring J := by
      apply StandardEtalePair.hom_ext
      show (pres.P.lift _ hy) (pres.equivRing ((Ep.lift pres.x hx) Ep.X)) =
        Ideal.Quotient.mkₐ (h1StdEt_P R S).Ring J Ep.X
      rw [StandardEtalePair.lift_X, StandardEtalePresentation.equivRing_x,
        StandardEtalePair.lift_X]
    have hval : Ideal.Quotient.mkₐ (h1StdEt_P R S).Ring J e = 0 := by
      rw [← AlgHom.congr_fun heq e]
      show (pres.P.lift _ hy) (pres.equivRing ((Ep.lift pres.x hx) e)) = 0
      rw [he', map_zero, map_zero]
    have hmem : e ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hval
    rw [hJ] at hmem
    exact hmem
  -- flatness and smoothness
  haveI : Module.Flat (h1StdEt_P R S).Ring Ep.Ring := Algebra.Smooth.flat _ _
  haveI : Algebra.FormallySmooth R (h1StdEt_P R S).Ring :=
    (inferInstance : Algebra.FormallySmooth R (MvPolynomial S R))
  haveI : Algebra.FormallySmooth R Ep.Ring :=
    Algebra.FormallySmooth.comp R (h1StdEt_P R S).Ring Ep.Ring
  exact h1StdEt_nonempty_equiv_of_lift R S T Ep.Ring hsurj hcomp hker

/-! ## The standard etale case and its consequences -/

/-- **The standard etale case.** If `S -> T` is standard etale and `H1(L_{T/R}) = 0`, then
`T ⊗[S] H1(L_{S/R}) = 0` (standard etale case of Stacks Tag 07D4). -/
theorem h1DescentStandardEtale : H1DescentStandardEtale := by
  intro R S T _ _ _ _ _ _ _ hstd hT
  haveI : Subsingleton (Algebra.H1Cotangent R T) := hT
  rcases subsingleton_or_nontrivial S with hS | hS
  · -- over the zero ring every module is zero
    have h0 : ∀ z : TensorProduct S T (Algebra.H1Cotangent R S), z = 0 := fun z =>
      calc z = (1 : S) • z := (one_smul S z).symm
        _ = (0 : S) • z := by rw [Subsingleton.elim (1 : S) 0]
        _ = 0 := zero_smul S z
    exact ⟨fun a b => (h0 a).trans (h0 b).symm⟩
  · obtain ⟨e⟩ := h1StdEt_nonempty_equiv R S T hstd
    exact e.injective.subsingleton

/-- Descent of the vanishing of `H1Cotangent` along finite etale faithfully flat maps, from the
reduction in `Y3H1Descent`. -/
theorem h1StdEt_h1CotangentDescentFiniteEtale : H1CotangentDescentFiniteEtale :=
  h1CotangentDescentFiniteEtale_of_standardEtale h1DescentStandardEtale

/-- Source descent of smoothness of relative dimension `n` along finite etale surjections, from
the reduction in `Y3SmoothDescent`. -/
theorem h1StdEt_descentSmoothRelDimFiniteEtale : DescentSmoothRelDimFiniteEtale :=
  descentSmoothRelDimFiniteEtale_of_h1 h1StdEt_h1CotangentDescentFiniteEtale

end Y3Buzzard.SourceDescent

end
