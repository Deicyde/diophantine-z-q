import ZInQKernel.Contrib.OneProof.InvariantRingPoints
import ZInQKernel.Contrib.Mobius.ImagePlane

/-! Equality of geometric points in a quotient with affine invariant charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane

namespace InvariantSchemePoints

set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{0}} {K : Type} [Field K]

private theorem appLE_eq_of_hom_eq {f g : X ⟶ Y} (h : f = g)
    (V : Y.Opens) (U : X.Opens) (hle : U ≤ f ⁻¹ᵁ V) :
    f.appLE V U hle = g.appLE V U (h ▸ hle) := by
  subst h
  rfl

private theorem id_appLE' (U : X.Opens) :
    (𝟙 X : X ⟶ X).appLE U U (by simp) = 𝟙 _ := by
  simp [Scheme.Hom.appLE]
  exact X.presheaf.map_id _

private theorem ev_appLE (p : Spec (.of K) ⟶ X) (g : X ⟶ Y) {V : Y.Opens} {U : X.Opens}
    (hle : U ≤ g ⁻¹ᵁ V) (hp : ptOf p ∈ U) (a : Γ(Y, V)) :
    ev (p ≫ g) (hle hp) a = ev p hp (g.appLE V U hle a) := by
  rw [ev_comp, Scheme.Hom.appLE, ConcreteCategory.comp_apply]
  exact (ev_res p hle hp _).symm

private theorem ev_congr {p q : Spec (.of K) ⟶ X} (h : p = q) {U : X.Opens}
    (hp : ptOf p ∈ U) (hq : ptOf q ∈ U) : ev p hp = ev q hq := by
  subst h
  rfl

/-- A point in an affine open is the map determined by evaluation of its sections. -/
theorem affine_point_eq_map (U : X.Opens) (hU : IsAffineOpen U)
    (p : Spec (.of K) ⟶ X) (hp : ptOf p ∈ U) :
    p = Spec.map (CommRingCat.ofHom (ev p hp)) ≫ hU.fromSpec := by
  classical
  let p' := IsOpenImmersion.lift hU.fromSpec p (by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst x
    exact hp)
  have hp' : p' ≫ hU.fromSpec = p := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨v, hv⟩ :=
    Spec.map_surjective (R := Γ(X, U)) (S := CommRingCat.of K) p'
  let φ := v
  have hφ : Spec.map φ ≫ hU.fromSpec = p := by
    change Spec.map v ≫ hU.fromSpec = p
    rw [hv, hp']
  have heq : φ = CommRingCat.ofHom (ev p hp) := by
    ext a
    have h₁ := ev_appLE (Spec.map φ) hU.fromSpec
      (U := ⊤) (V := U) (by rw [hU.fromSpec_preimage_self]) (by simp) a
    have h₂ := hU.fromSpec_app_self_apply a
    have h₃ := ev_spec_top (K := K) φ a
    rw [Scheme.Hom.appLE] at h₁
    rw [ConcreteCategory.comp_apply, h₂, ev_res] at h₁
    rw [ev_congr hφ _ hp] at h₁
    change ev p hp a = ev (Spec.map φ) _
      (res (le_top : hU.fromSpec ⁻¹ᵁ U ≤ ⊤) ((Scheme.ΓSpecIso Γ(X, U)).inv a)) at h₁
    rw [ev_res] at h₁
    exact h₃.symm.trans h₁.symm
  rw [← heq]
  exact hφ.symm

private def coeffMap (f : X ⟶ Spec (.of ℚ)) (U : X.Opens) : ℚ →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of ℚ)).inv ≫ f.appLE ⊤ U (by simp)).hom

private def sectionMap {G : Type*} [Monoid G] (ρ : G →* Aut X) (U : X.Opens)
    (hinv : ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U) (g : G) :
    Γ(X, U) →+* Γ(X, U) :=
  ((ρ g).asIso.hom.appLE U U (hinv g)).hom

private theorem sectionMap_preserves {G : Type*} [Monoid G]
    (ρ : G →* Aut X) (U : X.Opens) (hinv : ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U)
    (f : X ⟶ Spec (.of ℚ)) (hbase : ∀ g, (ρ g).asIso.hom ≫ f = f) (g : G) (q : ℚ) :
    sectionMap ρ U hinv g (coeffMap f U q) = coeffMap f U q := by
  change ((Scheme.ΓSpecIso (.of ℚ)).inv ≫
      f.appLE ⊤ U _ ≫ (ρ g).asIso.hom.appLE U U (hinv g)) q =
    ((Scheme.ΓSpecIso (.of ℚ)).inv ≫ f.appLE ⊤ U _) q
  have he := Scheme.Hom.appLE_comp_appLE (ρ g).asIso.hom f ⊤ U U
    (show U ≤ f ⁻¹ᵁ ⊤ by simp) (hinv g)
  exact congrArg (fun a => ((Scheme.ΓSpecIso (.of ℚ)).inv ≫ a) q)
    (he.trans (appLE_eq_of_hom_eq (hbase g) _ _ _))

private theorem ev_preserves [Algebra ℚ K] (f : X ⟶ Spec (.of ℚ)) (U : X.Opens)
    (p : Spec (.of K) ⟶ X) (hp : ptOf p ∈ U)
    (hbase : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (q : ℚ) :
    ev p hp (coeffMap f U q) = algebraMap ℚ K q := by
  change ev p hp (f.appLE ⊤ U _ ((Scheme.ΓSpecIso (.of ℚ)).inv q)) = _
  rw [← ev_appLE, hbase]
  exact ev_spec_top _ q

private def sectionAlgebraAction {G : Type*} [Group G]
    (ρ : G →* Aut X) (U : X.Opens) (hinv : ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U)
    (f : X ⟶ Spec (.of ℚ)) (hbase : ∀ g, (ρ g).asIso.hom ≫ f = f) :
    letI := (coeffMap f U).toAlgebra
    G →* (Γ(X, U) →ₐ[ℚ] Γ(X, U)) := by
  letI := (coeffMap f U).toAlgebra
  refine
    { toFun := fun g => ⟨sectionMap ρ U hinv g⁻¹, sectionMap_preserves ρ U hinv f hbase g⁻¹⟩
      map_one' := ?_
      map_mul' := ?_ }
  · ext a
    change ((ρ ((1 : G)⁻¹)).asIso.hom.appLE U U _) a = a
    have h : (ρ ((1 : G)⁻¹)).asIso.hom = 𝟙 X := by rw [inv_one, map_one]; rfl
    erw [appLE_eq_of_hom_eq h, id_appLE']
    rfl
  · intro g h
    ext a
    change ((ρ ((g * h)⁻¹)).asIso.hom.appLE U U _) a =
      ((ρ g⁻¹).asIso.hom.appLE U U _) (((ρ h⁻¹).asIso.hom.appLE U U _) a)
    have hm : (ρ ((g * h)⁻¹)).asIso.hom =
        (ρ g⁻¹).asIso.hom ≫ (ρ h⁻¹).asIso.hom := by rw [mul_inv_rev, map_mul]; rfl
    erw [appLE_eq_of_hom_eq hm,
      ← Scheme.Hom.appLE_comp_appLE _ _ U U U (hinv h⁻¹) (hinv g⁻¹),
      ConcreteCategory.comp_apply]

/-- For an affine quotient with sections equal to the invariant sections,
equality of geometric points on the quotient is precisely orbit equivalence. -/
theorem point_orbit_iff {G : Type*} [Group G] [Finite G] (ρ : G →* Aut X)
    (f : X ⟶ Spec (.of ℚ)) (hbase : ∀ g, (ρ g).asIso.hom ≫ f = f)
    (π : X ⟶ Y) [IsAffineHom π] (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    (hsections : ∀ V : Y.Opens, Set.range (π.app V) =
      {a | ∀ g, (ρ g).asIso.hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hπ g]) a = a})
    [Algebra ℚ K] (p q : Spec (.of K) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) :
    p ≫ π = q ≫ π ↔ ∃ g : G, q ≫ (ρ g).asIso.hom = p := by
  constructor
  · intro e
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, _⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (ptOf (p ≫ π))) isOpen_univ
    have hqV : ptOf (q ≫ π) ∈ V := e ▸ hpV
    let W := π ⁻¹ᵁ V
    have hW : IsAffineOpen W := hV.preimage π
    have hinv (g : G) : W ≤ (ρ g).asIso.hom ⁻¹ᵁ W := by
      change π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)
      rw [← Scheme.Hom.comp_preimage, hπ]
    let _ : Algebra ℚ Γ(X, W) := (coeffMap f W).toAlgebra
    let a := sectionAlgebraAction ρ W hinv f hbase
    let P : Γ(X, W) →ₐ[ℚ] K := ⟨ev p hpV, ev_preserves f W p hpV hp⟩
    let Q : Γ(X, W) →ₐ[ℚ] K := ⟨ev q hqV, ev_preserves f W q hqV hq⟩
    have heq (s : Γ(X, W)) (hs : ∀ g, a g s = s) : P s = Q s := by
      have hs' : s ∈ Set.range (π.app V) := by
        rw [hsections]
        intro g
        change sectionMap ρ W hinv g s = s
        have h := hs g⁻¹
        change sectionMap ρ W hinv g⁻¹⁻¹ s = s at h
        exact inv_inv g ▸ h
      obtain ⟨t, rfl⟩ := hs'
      change ev p hpV (π.app V t) = ev q hqV (π.app V t)
      rw [← ev_comp p π hpV, ← ev_comp q π hqV, ev_congr e hpV hqV]
    obtain ⟨g, hg⟩ := AlgHom.exists_comp_eq_of_eq_on_invariant a P Q heq
    refine ⟨g⁻¹, ?_⟩
    have hq' : ptOf (q ≫ (ρ g⁻¹).asIso.hom) ∈ W := hinv g⁻¹ hqV
    rw [affine_point_eq_map W hW (q ≫ (ρ g⁻¹).asIso.hom) hq',
      affine_point_eq_map W hW p hpV]
    congr 2
    ext s
    change ev (q ≫ (ρ g⁻¹).asIso.hom) hq' s = ev p (O := W) hpV s
    rw [ev_appLE q (ρ g⁻¹).asIso.hom (hinv g⁻¹) hqV s]
    exact (DFunLike.congr_fun hg s).symm
  · rintro ⟨g, rfl⟩
    rw [Category.assoc, hπ]

end InvariantSchemePoints

#print axioms InvariantSchemePoints.point_orbit_iff
