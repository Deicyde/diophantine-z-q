import ZInQKernel.Contrib.OneProof.ShimuraSteps
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Kernel
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Descent
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Flatness
import ZInQKernel.Contrib.OneProof.CartierSmooth
import ZInQKernel.OneProof.H.TailR

/-! # The geometric meaning of Shimura's quotient clauses -/

noncomputable section

namespace ShimuraSteps.Quotient

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar R16Thm1
open ZInQ.Contrib.MilneQuasiInverse
open scoped CategoryTheory.MonObj ModularForm

attribute [local instance] Kernel.kernelGroup

local notation "OverQ" => Over (Spec (CommRingCat.of ℚ))

variable {J A B C Q : AbVar ℚ}

/-- A genuine quotient by an abelian subvariety: a surjection with the displayed
scheme-theoretic kernel, universal for homomorphisms killing that kernel. -/
structure IsAbVarQuotient (i : AbVar.Hom C J) (q : AbVar.Hom J Q) : Prop where
  surjective : Surjective q.hom.left
  kernel : IsPullback i.hom (toUnit C.X) q.hom η[Q.X]
  lift_unique : ∀ (D : AbVar ℚ) (v : AbVar.Hom J D),
    i.hom ≫ v.hom = (0 : AbVar.Hom C D).hom →
    ∃! w : AbVar.Hom Q D, q.hom ≫ w.hom = v.hom

/-- Representability target, over `ℚ`. Proved by `abVarQuotientBySubvarietyExists` (`AbVarQuotientComplement.lean`). -/
def AbVarQuotientBySubvarietyExists : Prop :=
  ∀ (J C : AbVar ℚ) (i : AbVar.Hom C J), IsClosedImmersion i.hom.left →
    ∃ (Q : AbVar ℚ) (q : AbVar.Hom J Q), IsAbVarQuotient i q

/-- The sum of scheme-theoretic images, when represented by the abelian subvariety
`i`: it is the least closed subgroup scheme through which all the endomorphisms
factor. The comparison ranges over all closed subgroup schemes of `J`. -/
structure IsImageSum (I : Set (AbVar.End J)) (i : AbVar.Hom C J) : Prop where
  closed : IsClosedImmersion i.hom.left
  factors : ∀ t ∈ I, ∃ u : J.X ⟶ C.X, u ≫ i.hom = t.hom
  least : ∀ (G : OverQ) [GrpObj G] (j : G ⟶ J.X) [IsMonHom j],
    IsClosedImmersion j.left →
    (∀ t ∈ I, ∃ u : J.X ⟶ G, u ≫ j = t.hom) →
    ∃ u : C.X ⟶ G, u ≫ j = i.hom

/-- The unit section of a separated group scheme is a closed immersion. -/
theorem unit_closed (G : OverQ) [GrpObj G] [IsSeparated G.hom] :
    IsClosedImmersion (η[G]).left := by
  have : IsClosedImmersion ((η[G]).left ≫ G.hom) := by
    rw [Over.w]
    change IsClosedImmersion (𝟙 (Spec (CommRingCat.of ℚ)))
    infer_instance
  exact IsClosedImmersion.of_comp (η[G]).left G.hom

/-- The scheme-theoretic kernel is closed in the source. -/
theorem kernelInclusion_closed (v : AbVar.Hom J A) :
    IsClosedImmersion (Kernel.kernelInclusion v.hom).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (Kernel.kernel_isPullback v.hom).flip
    (unit_closed A.X)

/-- Killing the family of endomorphisms is equivalent to killing their
scheme-theoretic image sum. -/
theorem kills_iff_kills_imageSum {I : Set (AbVar.End J)} {i : AbVar.Hom C J}
    (hsum : IsImageSum I i) (v : AbVar.Hom J A) :
    Kills I v ↔ i.hom ≫ v.hom = (0 : AbVar.Hom C A).hom := by
  constructor
  · intro h
    have hf (t : AbVar.End J) (ht : t ∈ I) :
        ∃ u : J.X ⟶ Kernel.kernelObject v.hom, u ≫ Kernel.kernelInclusion v.hom = t.hom := by
      refine ⟨(Kernel.kernelPointsEquiv v.hom J.X).symm ⟨t.hom, h t ht⟩, ?_⟩
      exact pullback.lift_fst _ _ _
    obtain ⟨u, hu⟩ := hsum.least _ (Kernel.kernelInclusion v.hom) (kernelInclusion_closed v) hf
    rw [← hu, Category.assoc, Kernel.kernelInclusion_comp, MonObj.comp_one, Hom.hom_zero]
  · intro h t ht
    obtain ⟨u, hu⟩ := hsum.factors t ht
    rw [← hu, Category.assoc, h, Hom.hom_zero, MonObj.comp_one]
    rfl

/-- Once the image sum and its genuine quotient are supplied, the printed
universal property characterizes the same map up to isomorphism over `ℚ`,
with the isomorphism commuting with the maps from `J`. -/
theorem printQuotient_iff_iso {N : ℕ} {ξ : ℕ → AbVar.End J} {f : PkgI4.CF N 2}
    {i : AbVar.Hom C J} {q : AbVar.Hom J Q} (ν : AbVar.Hom J A)
    (hsum : IsImageSum (Sat (annihilator (printRing ξ f))) i)
    (hq : IsAbVarQuotient i q) :
    PrintQuotient ξ f ν ↔
      ∃ a : AbVar.Hom Q A, IsIso a.hom ∧ q.hom ≫ a.hom = ν.hom := by
  have hqzero : i.hom ≫ q.hom = (0 : AbVar.Hom C Q).hom := hq.kernel.w
  have hqkills := (kills_iff_kills_imageSum hsum q).mpr hqzero
  constructor
  · intro hν
    obtain ⟨a, ha, _⟩ := hq.lift_unique A ν ((kills_iff_kills_imageSum hsum ν).mp hν.1)
    obtain ⟨b, hb, _⟩ := hν.2 Q q hqkills
    have hab : a.hom ≫ b.hom = 𝟙 Q.X := by
      obtain ⟨d, _, hd⟩ := hq.lift_unique Q q hqzero
      have h₁ := hd (Hom.mk' (a.hom ≫ b.hom)) (by
        change q.hom ≫ (a.hom ≫ b.hom) = q.hom
        rw [← Category.assoc, ha, hb])
      have h₂ := hd (Hom.mk' (𝟙 Q.X)) (by simp)
      exact congrArg Hom.hom (h₁.trans h₂.symm)
    have hba : b.hom ≫ a.hom = 𝟙 A.X := by
      obtain ⟨d, _, hd⟩ := hν.2 A ν hν.1
      have h₁ := hd (Hom.mk' (b.hom ≫ a.hom)) (by
        change ν.hom ≫ (b.hom ≫ a.hom) = ν.hom
        rw [← Category.assoc, hb, ha])
      have h₂ := hd (Hom.mk' (𝟙 A.X)) (by simp)
      exact congrArg Hom.hom (h₁.trans h₂.symm)
    exact ⟨a, ⟨⟨b.hom, hab, hba⟩⟩, ha⟩
  · rintro ⟨a, ha, haν⟩
    have := ha
    have hk : Kills (Sat (annihilator (printRing ξ f))) ν := by
      apply (kills_iff_kills_imageSum hsum ν).mpr
      rw [← haν, ← Category.assoc, hqzero, Hom.hom_zero, MonObj.one_comp]
      rfl
    refine ⟨hk, fun D v hv => ?_⟩
    obtain ⟨b, hb, hu⟩ := hq.lift_unique D v ((kills_iff_kills_imageSum hsum v).mp hv)
    let w : AbVar.Hom A D := Hom.mk' ((asIso a.hom).inv ≫ b.hom)
    refine ⟨w, ?_, ?_⟩
    · change ν.hom ≫ (inv a.hom ≫ b.hom) = v.hom
      rw [← haν, Category.assoc, IsIso.hom_inv_id_assoc, hb]
    · intro g hg
      have h := hu (Hom.mk' (a.hom ≫ g.hom)) (by
        change q.hom ≫ (a.hom ≫ g.hom) = v.hom
        rw [← Category.assoc, haν, hg])
      apply Hom.ext'
      apply (cancel_epi a.hom).mp
      change a.hom ≫ g.hom = a.hom ≫ inv a.hom ≫ b.hom
      rw [IsIso.hom_inv_id_assoc]
      exact congrArg Hom.hom h

/-- Connectedness of the ordinary scheme-theoretic kernel over `ℚ`. -/
def SchemeKernelConnected (ν : AbVar.Hom J A) : Prop :=
  ConnectedSpace (Kernel.kernelObject ν.hom).left

/-- The kernel of a genuine quotient by an abelian subvariety is connected. -/
theorem schemeKernelConnected_of_isAbVarQuotient {i : AbVar.Hom C J} {q : AbVar.Hom J Q}
    (hq : IsAbVarQuotient i q) : SchemeKernelConnected q := by
  have : IsIntegral C.X.left := GeometricallyIntegral.isIntegral_of_subsingleton C.X.hom
  let e := (Over.forget (Spec (CommRingCat.of ℚ))).mapIso hq.kernel.isoPullback
  let eh : C.X.left ≃ₜ (Kernel.kernelObject q.hom).left := e.hom.homeomorph
  exact eh.surjective.connectedSpace eh.continuous

/-- A finite homomorphism of abelian varieties over `ℚ` with connected kernel
has trivial kernel: its unit section is an isomorphism. -/
theorem unit_isIso_of_finite_connected (ν : AbVar.Hom J A) [IsFinite ν.hom.left]
    (hc : SchemeKernelConnected ν) : IsIso (η[Kernel.kernelObject ν.hom]) := by
  let G := Kernel.kernelObject ν.hom
  have : ConnectedSpace G.left := hc
  have : IsFinite G.hom := Kernel.kernel_isFinite ν.hom
  have : IsLocallyArtinian G.left :=
    IsLocallyArtinian.of_locallyQuasiFinite G.hom
  have : Subsingleton G.left := subsingleton_of_preconnected_totallyDisconnected
  have : Smooth G.hom :=
    ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof ℚ G inferInstance
  have : IsReduced G.left := CurveSplit.isReduced_of_smooth G.hom
  have : Surjective (η[G]).left := ⟨fun x => ⟨IsLocalRing.closedPoint ℚ, Subsingleton.elim _ _⟩⟩
  have := unit_closed G
  have he : IsIso (η[G]).left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget (Spec (CommRingCat.of ℚ))).map (η[G])) := he
  exact isIso_of_reflects_iso (η[G]) (Over.forget _)

/-- A connected scheme-theoretic kernel implies the factorization criterion
used in the printed clause. Surjectivity of the original map is unnecessary
in this direction: it follows whenever a factorization being tested exists. -/
theorem kerConnected_of_schemeKernelConnected {ν : AbVar.Hom J A}
    (hc : SchemeKernelConnected ν) : KerConnected ν := by
  intro B φ ψ hφ hψ hfac
  let G := Kernel.kernelObject ψ.hom
  let k : Kernel.kernelObject ν.hom ⟶ G :=
    pullback.lift (Kernel.kernelInclusion ν.hom ≫ φ.hom) (pullback.snd ν.hom η[A.X]) (by
      rw [Category.assoc, hfac, Kernel.kernelInclusion, pullback.condition])
  have hk :
      IsPullback (Kernel.kernelInclusion ν.hom) k φ.hom (Kernel.kernelInclusion ψ.hom) := by
    apply IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback ψ.hom η[A.X])
    change IsPullback (Kernel.kernelInclusion ν.hom) (k ≫ pullback.snd ψ.hom η[A.X])
      (φ.hom ≫ ψ.hom) η[A.X]
    have hk' : k ≫ pullback.snd ψ.hom η[A.X] = pullback.snd ν.hom η[A.X] :=
      pullback.lift_snd _ _ _
    rw [hk', hfac]
    exact IsPullback.of_hasPullback ν.hom η[A.X]
  have hs : Surjective k.left := MorphismProperty.of_isPullback (P := @Surjective)
    ((Over.forget _).map_isPullback hk) hφ
  have : ConnectedSpace (Kernel.kernelObject ν.hom).left := hc
  have hcG : SchemeKernelConnected ψ := hs.surj.connectedSpace k.left.continuous
  have : IsFinite ψ.hom.left := hψ.1
  have : IsIso (η[G]) := unit_isIso_of_finite_connected ψ hcG
  have trivial (T : OverQ) (x : T ⟶ B.X) (hx : x ≫ ψ.hom = 1) : x = 1 := by
    let x' := (Kernel.kernelPointsEquiv ψ.hom T).symm ⟨x, hx⟩
    have hp : x' ≫ Kernel.kernelInclusion ψ.hom = x := pullback.lift_fst _ _ _
    have he : x' = toUnit T ≫ η[G] := by
      apply (cancel_mono (inv η[G])).mp
      exact Subsingleton.elim _ _
    rw [← hp, he, Category.assoc, IsMonHom.one_hom]
    rfl
  have : Mono ψ.hom := ⟨fun {T} x y hxy => by
    apply div_eq_one.mp (trivial T (x / y) ?_)
    change Kernel.pointsMap ψ.hom T (x / y) = 1
    rw [map_div]
    exact div_eq_one.mpr hxy⟩
  have : Flat ψ.hom.left := finite_surjective_abVarHom_flat ψ hψ
  have : Surjective ψ.hom.left := hψ.2
  have : EffectiveEpi ψ.hom :=
    ZInQ.Contrib.MilneQuasiInverse.Descent.GroupDescent.Construction.effectiveEpi_over_of_fpqc ψ.hom
  have hr {T : OverQ} (x y : T ⟶ B.X) (h : x ≫ ψ.hom = y ≫ ψ.hom) :
      x ≫ 𝟙 B.X = y ≫ 𝟙 B.X := by rw [(cancel_mono ψ.hom).mp h]
  let r := EffectiveEpi.desc ψ.hom (𝟙 B.X) hr
  have h₁ : ψ.hom ≫ r = 𝟙 B.X := EffectiveEpi.fac _ _ _
  have h₂ : r ≫ ψ.hom = 𝟙 A.X := by
    apply (cancel_epi ψ.hom).mp
    rw [← Category.assoc, h₁, Category.id_comp, Category.comp_id]
  exact ⟨⟨r, h₁, h₂⟩⟩

end ShimuraSteps.Quotient
