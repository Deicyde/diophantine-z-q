import ZInQKernel.Contrib.OneProof.QuotientP1.Lichtenbaum
import ZInQKernel.Contrib.OneProof.QuotientP1.QuotProper
import ZInQKernel.Contrib.CloudW02Connectedness.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# p1-quot3, helper (L4 part A): the special fibre of a smooth proper model of `P¹_ℚ` is irreducible

Generated from `scratch/p1-quot3/L4A.lean`. `Γ(P¹ by charts over ℚ) = ℚ`; `Γ(𝒵, 𝒪) = ℤ_(p)` for a flat universally
closed model; geometric connectedness by Zariski's theorem (proved in CloudW02); integral fibres; the generic point
`xi` of the special fibre; points of codimension `≤ 1`. No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Polynomial Opposite

namespace HDec.MCRGlue.P1Model

open VertWitness LeafQM.AV ModelGlue

/-! ## Global sections of a `P¹` by charts over `ℚ` -/

section GlobalSections

variable (Z : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 Z.left) (hσ : IsP1CoordinateQ Z σ)

/-- The structure map `ℚ → Γ(Z, ⊤)`. -/
def psiTop : ℚ →+* Γ(Z.left, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ Z.hom.appTop).hom

theorem baseToSectionsOver_eq (W : Z.left.Opens) (a : ℚ) :
    baseToSectionsOver (CommRingCat.of ℚ) Z W a =
      Z.left.presheaf.map (homOfLE le_top).op (psiTop Z a) := rfl

theorem baseToSectionsOver_res (W W' : Z.left.Opens) (h : W' ≤ W) (a : ℚ) :
    Z.left.presheaf.map (homOfLE h).op (baseToSectionsOver (CommRingCat.of ℚ) Z W a) =
      baseToSectionsOver (CommRingCat.of ℚ) Z W' a := by
  rw [baseToSectionsOver_eq, baseToSectionsOver_eq, Scheme.presheaf_map_map]

/-- Restriction to a basic open of an affine open whose sections form a domain is injective, if the
function is nonzero. -/
theorem res_basicOpen_injective {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] (f : Γ(X, U)) (hf : f ≠ 0) :
    Function.Injective (X.presheaf.map (homOfLE (X.basicOpen_le f)).op) := by
  have := hU.isLocalization_basicOpen f
  exact IsLocalization.injective (M := Submonoid.powers f) Γ(X, X.basicOpen f)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

/-- Restriction from `U` to `W ≤ U` is injective if it is injective to a basic open equal to `W`. -/
theorem res_injective_of_eq_basicOpen {X : Scheme.{0}} {U W : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] (f : Γ(X, U)) (hf : f ≠ 0) (hW : X.basicOpen f = W) (h : W ≤ U) :
    Function.Injective (X.presheaf.map (homOfLE h).op) := by
  subst hW
  exact res_basicOpen_injective hU f hf

include hσ in
theorem isDomain_U : IsDomain Γ(Z.left, σ.U) :=
  Function.Injective.isDomain (RingEquiv.ofBijective _ hσ.2.2.1).symm
    (RingEquiv.ofBijective _ hσ.2.2.1).symm.injective

include hσ in
theorem isDomain_V : IsDomain Γ(Z.left, σ.V) :=
  Function.Injective.isDomain (RingEquiv.ofBijective _ hσ.2.2.2).symm
    (RingEquiv.ofBijective _ hσ.2.2.2).symm.injective

include hσ in
theorem f_ne_zero : σ.f ≠ 0 := by
  intro h
  have h1 : eval₂RingHom (baseToSectionsOver _ Z σ.U) σ.f (X : ℚ[X]) =
      eval₂RingHom (baseToSectionsOver _ Z σ.U) σ.f 0 := by
    simp [h]
  have := hσ.2.2.1.1 h1
  exact X_ne_zero this

include hσ in
theorem g_ne_zero : σ.g ≠ 0 := by
  intro h
  have h1 : eval₂RingHom (baseToSectionsOver _ Z σ.V) σ.g (X : ℚ[X]) =
      eval₂RingHom (baseToSectionsOver _ Z σ.V) σ.g 0 := by
    simp [h]
  have := hσ.2.2.2.1 h1
  exact X_ne_zero this

include hσ in
theorem res_injective_U : Function.Injective
    (Z.left.presheaf.map (homOfLE (inf_le_left : σ.U ⊓ σ.V ≤ σ.U)).op) := by
  haveI := isDomain_U Z σ hσ
  exact res_injective_of_eq_basicOpen hσ.1 σ.f (f_ne_zero Z σ hσ) σ.basicOpen_f _

include hσ in
theorem res_injective_V : Function.Injective
    (Z.left.presheaf.map (homOfLE (inf_le_right : σ.U ⊓ σ.V ≤ σ.V)).op) := by
  haveI := isDomain_V Z σ hσ
  exact res_injective_of_eq_basicOpen hσ.2.1 σ.g (g_ne_zero Z σ hσ) σ.basicOpen_g _

/-- `eval₂` commutes with restriction. -/
theorem res_eval₂ (W W' : Z.left.Opens) (h : W' ≤ W) (t : Γ(Z.left, W)) (P : ℚ[X]) :
    Z.left.presheaf.map (homOfLE h).op (eval₂ (baseToSectionsOver _ Z W) t P) =
      eval₂ (baseToSectionsOver _ Z W') (Z.left.presheaf.map (homOfLE h).op t) P := by
  rw [Polynomial.hom_eval₂]
  congr 1
  ext a
  exact baseToSectionsOver_res Z W W' h a

include hσ in
/-- **A `P¹` by charts over `ℚ` has global sections `ℚ`.** -/
theorem psiTop_surjective : Function.Surjective (psiTop Z) := by
  intro b
  set W := σ.U ⊓ σ.V
  set rU := Z.left.presheaf.map (homOfLE (inf_le_left : W ≤ σ.U)).op
  set rV := Z.left.presheaf.map (homOfLE (inf_le_right : W ≤ σ.V)).op
  obtain ⟨P, hP⟩ := hσ.2.2.1.2 (Z.left.presheaf.map (homOfLE le_top : σ.U ⟶ ⊤).op b)
  obtain ⟨Q, hQ⟩ := hσ.2.2.2.2 (Z.left.presheaf.map (homOfLE le_top : σ.V ⟶ ⊤).op b)
  simp only [coe_eval₂RingHom] at hP hQ
  set f' := rU σ.f
  set g' := rV σ.g
  have hfg : f' * g' = 1 := σ.inv
  letI : Invertible g' := invertibleOfRightInverse _ _ (by rw [mul_comm]; exact hfg)
  have hinvg : ⅟g' = f' := by
    rw [← mul_one (⅟g'), ← hfg, ← mul_assoc, mul_comm (⅟g') f', mul_assoc, invOf_mul_self, mul_one]
  have hW : rU (Z.left.presheaf.map (homOfLE le_top : σ.U ⟶ ⊤).op b) =
      rV (Z.left.presheaf.map (homOfLE le_top : σ.V ⟶ ⊤).op b) := by
    simp only [rU, rV, Scheme.presheaf_map_map]
  rw [← hP, ← hQ, res_eval₂, res_eval₂] at hW
  -- `P(f') = Q(g') = reflect(Q)(f') g'^n`
  set n := Q.natDegree
  have hrefl := eval₂_reflect_mul_pow (baseToSectionsOver _ Z W) g' n Q le_rfl
  rw [hinvg] at hrefl
  have hPX : eval₂ (baseToSectionsOver _ Z W) f' (P * X ^ n) =
      eval₂ (baseToSectionsOver _ Z W) f' (reflect n Q) := by
    rw [eval₂_mul, eval₂_X_pow, hW, ← hrefl, mul_assoc, ← mul_pow, mul_comm g' f', hfg, one_pow,
      mul_one]
  have hinj : Function.Injective (fun R : ℚ[X] => eval₂ (baseToSectionsOver _ Z W) f' R) := by
    intro R₁ R₂ h
    simp only at h
    rw [← res_eval₂, ← res_eval₂] at h
    exact hσ.2.2.1.1 (res_injective_U Z σ hσ h)
  have hPQ := hinj hPX
  -- degrees: `P` is constant
  have hdeg : P.natDegree = 0 := by
    by_cases hP0 : P = 0
    · rw [hP0, natDegree_zero]
    · have h1 : (P * X ^ n).natDegree = P.natDegree + n := by
        rw [natDegree_mul hP0 (pow_ne_zero _ X_ne_zero), natDegree_X_pow]
      have h2 : (reflect n Q).natDegree ≤ n := by
        have := natDegree_reflect_le (N := n) (p := Q)
        rwa [max_self] at this
      rw [hPQ] at h1
      omega
  rw [natDegree_eq_zero] at hdeg
  obtain ⟨a, rfl⟩ := hdeg
  refine ⟨a, ?_⟩
  -- equal on `U` and on `V`
  have hUeq : Z.left.presheaf.map (homOfLE le_top : σ.U ⟶ ⊤).op (psiTop Z a) =
      Z.left.presheaf.map (homOfLE le_top : σ.U ⟶ ⊤).op b := by
    rw [← hP, eval₂_C]; rfl
  have hVeq : Z.left.presheaf.map (homOfLE le_top : σ.V ⟶ ⊤).op (psiTop Z a) =
      Z.left.presheaf.map (homOfLE le_top : σ.V ⟶ ⊤).op b := by
    apply res_injective_V Z σ hσ
    have e1 := congrArg rU hUeq
    simp only [rU, Scheme.presheaf_map_map] at e1 ⊢
    exact e1
  exact Z.left.sheaf.eq_of_locally_eq₂ (homOfLE le_top) (homOfLE le_top)
    (by rw [σ.cover]) _ _ hUeq hVeq

end GlobalSections

/-! ## `Γ(𝒵, 𝒪) = ℤ_(p)` and Zariski's connectedness theorem -/

section Model

variable {p : ℕ} [Fact p.Prime]

instance zloc_isNoetherian : IsNoetherianRing (Zloc p) :=
  IsLocalization.isNoetherianRing (pIdeal p).primeCompl (Zloc p) inferInstance

theorem zloc_isDVR' : IsDiscreteValuationRing (Zloc p) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (by
      show Ideal.span {((p : ℕ) : ℤ)} ≠ ⊥
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : p.Prime).ne_zero) _

/-- `ℚ` is the fraction field of `ℤ_(p)` (through `zlocToRat`). -/
theorem zloc_isFractionRing :
    letI : Algebra (Zloc p) ℚ := (zlocToRat p).toAlgebra
    IsFractionRing (Zloc p) ℚ := by
  letI : Algebra (Zloc p) ℚ := (zlocToRat p).toAlgebra
  have hinj : Function.Injective (algebraMap (Zloc p) ℚ) := zlocToRat_injective p
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    refine isUnit_iff_ne_zero.2 ?_
    intro h
    exact nonZeroDivisors.ne_zero hy (hinj (h.trans (map_zero _).symm))
  · intro z
    have hden : ((z.den : ℤ) : Zloc p) ∈ nonZeroDivisors (Zloc p) := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      intro h
      have := congrArg (algebraMap (Zloc p) ℚ) h
      rw [map_intCast, map_zero] at this
      exact_mod_cast z.den_nz (by exact_mod_cast this)
    refine ⟨⟨(z.num : Zloc p), ⟨_, hden⟩⟩, ?_⟩
    change z * algebraMap (Zloc p) ℚ ((z.den : ℤ) : Zloc p) = algebraMap (Zloc p) ℚ (z.num : Zloc p)
    rw [map_intCast, map_intCast]
    push_cast
    exact Rat.mul_den_eq_num z
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

theorem psiTop_injective (Z : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 Z.left)
    (hσ : IsP1CoordinateQ Z σ) : Function.Injective (psiTop Z) := by
  haveI := isDomain_U Z σ hσ
  haveI : Nontrivial Γ(Z.left, ⊤) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrArg (Z.left.presheaf.map (homOfLE le_top : σ.U ⟶ ⊤).op) h
    rw [map_zero, map_one] at this
    exact zero_ne_one this
  exact (psiTop Z).injective

/-- **Global functions on a model of `P¹_ℚ`** (flat and universally closed over `ℤ_(p)`): `ℤ_(p) → Γ(𝒵, 𝒪)` is
bijective. As `ZariskiConn.appTop_bijective_of_generic`, with `Γ(𝒵_ℚ, 𝒪) = ℚ` from the charts. -/
theorem appTop_bijective (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) [Flat 𝒵.hom]
    [UniversallyClosed 𝒵.hom] (σ : ToP1 (genFib 𝒵).left) (hσ : IsP1CoordinateQ (genFib 𝒵) σ) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of (Zloc p))).inv ≫ 𝒵.hom.appTop) := by
  letI : Algebra (Zloc p) ℚ := (zlocToRat p).toAlgebra
  haveI := zloc_isFractionRing (p := p)
  haveI := zloc_isDVR' (p := p)
  set ι := specRatToZloc p
  set p' := 𝒵.hom
  have hinj : Function.Injective (algebraMap (Zloc p) ℚ) := IsFractionRing.injective (Zloc p) ℚ
  have := ZariskiConn.isSchemeTheoreticallyDominant_Spec_map hinj
  have hK : Function.Bijective (psiTop (genFib 𝒵)) :=
    ⟨psiTop_injective _ σ hσ, psiTop_surjective _ σ hσ⟩
  have hj : Function.Injective (pullback.fst p' ι).appTop :=
    (pullback.fst p' ι).app_injective ⊤
  set φ := ((Scheme.ΓSpecIso (.of (Zloc p))).inv ≫ p'.appTop).hom with hφ
  set ψ := psiTop (genFib 𝒵) with hψ
  set j := (pullback.fst p' ι).appTop.hom with hjdef
  have hcomm : ∀ r : Zloc p, j (φ r) = ψ (algebraMap (Zloc p) ℚ r) := by
    intro r
    have h1 : (Scheme.ΓSpecIso (.of (Zloc p))).inv ≫ p'.appTop ≫ (pullback.fst p' ι).appTop =
        CommRingCat.ofHom (algebraMap (Zloc p) ℚ) ≫ (Scheme.ΓSpecIso (.of ℚ)).inv ≫
          (pullback.snd p' ι).appTop := by
      rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
        ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
    exact congrArg (fun g => g.hom r) h1
  have hφint : φ.IsIntegral := by
    rw [hφ, CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _
      (Scheme.ΓSpecIso (.of (Zloc p))).commRingCatIsoToRingEquiv.symm.surjective)
      (isIntegral_appTop_of_universallyClosed p')
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · apply hinj; apply hK.1
    rw [← hcomm, ← hcomm, hab]
  · obtain ⟨c, hc⟩ := hK.2 (j b)
    obtain ⟨q, hqm, hq⟩ := hφint b
    have hcint : IsIntegral (Zloc p) c := by
      refine ⟨q, hqm, hK.1 ?_⟩
      rw [map_zero, Polynomial.hom_eval₂, hc]
      have : (ψ.comp (algebraMap (Zloc p) ℚ)) = j.comp φ := by ext r; exact (hcomm r).symm
      rw [this]
      exact (Polynomial.hom_eval₂ q φ j b).symm.trans (by rw [hq]; exact map_zero j)
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hcint
    refine ⟨r, hj ?_⟩
    change j (φ r) = j b
    rw [hcomm, hr, hc]

/-- **The model is geometrically connected** over `ℤ_(p)` (Zariski's connectedness theorem, proved in
`Contrib/CloudW02Connectedness`). -/
theorem geometricallyConnected (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) [Flat 𝒵.hom]
    [IsProper 𝒵.hom] (σ : ToP1 (genFib 𝒵).left) (hσ : IsP1CoordinateQ (genFib 𝒵) σ) :
    GeometricallyConnected 𝒵.hom := by
  have h := appTop_bijective 𝒵 σ hσ
  have h2 : Function.Bijective 𝒵.hom.appTop := by
    have e : 𝒵.hom.appTop = (Scheme.ΓSpecIso (CommRingCat.of (Zloc p))).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of (Zloc p))).inv ≫ 𝒵.hom.appTop) := by
      rw [Iso.hom_inv_id_assoc]
    rw [e]
    exact h.comp (ConcreteCategory.bijective_of_isIso _)
  exact ZariskiConn.ZariskiConnectedness_proof 𝒵.hom inferInstance inferInstance
    (ZariskiConn.app_bijective_of_appTop_bijective 𝒵.hom h2)

set_option backward.isDefEq.respectTransparency.types false in
/-- **The fibres of a smooth geometrically connected model are integral.** -/
theorem isIntegral_fiber (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
    [SmoothOfRelativeDimension 1 𝒵.hom] [GeometricallyConnected 𝒵.hom]
    (s : Spec (CommRingCat.of (Zloc p))) [Nonempty (𝒵.hom.fiber s)] :
    IsIntegral (𝒵.hom.fiber s) := by
  haveI : Smooth 𝒵.hom := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (𝒵.hom.fiberToSpecResidueField s) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback 𝒵.hom _) inferInstance
  have : IsLocallyNoetherian (𝒵.hom.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝒵.hom.fiberToSpecResidueField s)
  have : ∀ x : 𝒵.hom.fiber s, IsRegularLocalRing ((𝒵.hom.fiber s).presheaf.stalk x) :=
    TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth (𝒵.hom.fiberToSpecResidueField s)
  exact TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _

/-- **Each fibre is irreducible** as a subset of the model. -/
theorem isIrreducible_preimage (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
    [SmoothOfRelativeDimension 1 𝒵.hom] [GeometricallyConnected 𝒵.hom]
    (s : Spec (CommRingCat.of (Zloc p))) : IsIrreducible (𝒵.hom ⁻¹' {s}) := by
  have hne : Nonempty (𝒵.hom.fiber s) := inferInstance
  haveI := isIntegral_fiber 𝒵 s
  rw [← Scheme.Hom.range_fiberι]
  have := (IrreducibleSpace.isIrreducible_univ (𝒵.hom.fiber s)).image _
    (𝒵.hom.fiberι s).continuous.continuousOn
  rwa [Set.image_univ] at this

/-! ## Points of the model -/

/-- The closed point of `Spec ℤ_(p)`. -/
abbrev s0 (p : ℕ) [Fact p.Prime] : Spec (CommRingCat.of (Zloc p)) :=
  haveI := zloc_isDVR' (p := p)
  IsLocalRing.closedPoint (Zloc p)

/-- A point of `Spec ℤ_(p)` other than the closed point is the generic point; it specializes only to itself and the
closed point. -/
theorem eq_s0_of_specializes {u v : Spec (CommRingCat.of (Zloc p))} (h : u ⤳ v) (hu : u = s0 p) :
    v = s0 p := by
  haveI := zloc_isDVR' (p := p)
  exact QuotientP1Proof.eq_closedPoint_of_specializes (Zloc p) h hu

theorem eq_of_specializes_of_ne_s0 {u v : Spec (CommRingCat.of (Zloc p))} (h : u ⤳ v)
    (hv : v ≠ s0 p) : u = v := by
  haveI := zloc_isDVR' (p := p)
  exact QuotientP1Proof.eq_of_specializes_of_ne_closedPoint (Zloc p) h hv

variable (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) [SmoothOfRelativeDimension 1 𝒵.hom]
  [GeometricallyConnected 𝒵.hom]

/-- The special fibre as a subset. -/
abbrev Fs : Set 𝒵.left := 𝒵.hom ⁻¹' {s0 p}

theorem isClosed_Fs : IsClosed (Fs 𝒵) := by
  haveI := zloc_isDVR' (p := p)
  exact ((PrimeSpectrum.isClosed_singleton_iff_isMaximal (s0 p)).mpr
    (IsLocalRing.maximalIdeal.isMaximal (Zloc p))).preimage 𝒵.hom.continuous

/-- The generic point `ξ` of the special fibre. -/
def xi : 𝒵.left := (isIrreducible_preimage 𝒵 (s0 p)).genericPoint

theorem isGenericPoint_xi : IsGenericPoint (xi 𝒵) (Fs 𝒵) :=
  (isIrreducible_preimage 𝒵 (s0 p)).isGenericPoint_genericPoint (isClosed_Fs 𝒵)

theorem xi_mem : xi 𝒵 ∈ Fs 𝒵 := (isGenericPoint_xi 𝒵).mem

theorem xi_specializes {x : 𝒵.left} (hx : 𝒵.hom x = s0 p) : xi 𝒵 ⤳ x :=
  (isGenericPoint_xi 𝒵).specializes hx

/-- **Points of codimension `≤ 1` lie over the generic point of `Spec ℤ_(p)`, or are `ξ`.** -/
theorem eq_xi_of_ringKrullDim_le_one [IsIntegral 𝒵.left] (hgen : ∃ y : 𝒵.left, 𝒵.hom y ≠ s0 p)
    (x : 𝒵.left) (hx : 𝒵.hom x = s0 p)
    (hd : ringKrullDim (𝒵.left.presheaf.stalk x) ≤ 1) : x = xi 𝒵 := by
  by_contra hne
  set η := genericPoint 𝒵.left
  have hξx : xi 𝒵 ⤳ x := xi_specializes 𝒵 hx
  have hηξ : η ⤳ xi 𝒵 := (genericPoint_spec 𝒵.left).specializes (Set.mem_univ _)
  have hηs : 𝒵.hom η ≠ s0 p := by
    obtain ⟨y, hy⟩ := hgen
    intro h
    exact hy (eq_s0_of_specializes ((genericPoint_spec 𝒵.left).specializes (Set.mem_univ y)
      |>.map 𝒵.hom.continuous) h)
  have hlt1 : x < xi 𝒵 := by
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.2 hξx) (fun h => hne ?_)
    exact (hξx.antisymm (Scheme.le_iff_specializes.1 h)).eq.symm
  have hlt2 : xi 𝒵 < η := by
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.2 hηξ) (fun h => hηs ?_)
    rw [(hηξ.antisymm (Scheme.le_iff_specializes.1 h)).eq]
    exact xi_mem 𝒵
  have hc := Order.length_le_coheight_head (p := QuotientP1Proof.lt3 hlt1 hlt2)
  rw [QuotientP1Proof.lt3_length, QuotientP1Proof.lt3_head] at hc
  rw [ringKrullDim_stalk_eq_coheight] at hd
  have h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight x : WithBot ℕ∞) := by exact_mod_cast hc
  have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1 := h2.trans hd
  exact absurd this (by decide)

end Model

end HDec.MCRGlue.P1Model
