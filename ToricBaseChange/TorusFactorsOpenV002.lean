import ToricBaseChange.TorusImageRigidityV002
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Localization.InvSubmonoid

/-!
# A torus lands in every open subgroup (identity component), and the toric rank inequality

Over an algebraically closed field `k`, a homomorphism `𝔾_m → G` of group schemes (functor of
points, natural in `k`-algebras) factors through every open subgroup scheme `U ⊆ G`
(`gmHom_factors_open`): with `D = k[X, X⁻¹]` and the universal unit `X`, the preimage `V` of `U`
under `g = Φ(X) : Spec D → G` is open and contains the point `1`, hence a basic open `D(f)` around
`1`; the `c ∈ kˣ` with `g(c) ∈ U` form a subgroup of `kˣ` containing all `c` off the finite zero
set of the numerator of `f`, so (as `kˣ` is infinite) all of `kˣ`; every closed point of `Spec D` is
such a `c`, and `Spec D` is Jacobson, so `V` is everything. The same holds for `𝔾_m^r`
(`torusHom_factors_open`), coordinatewise.

`toricRank_le_of_torusMap_open` is the toric rank inequality of the rigidity file with the
identity-component hypothesis removed: the image of the torus in `U'` is now proved.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ToricBaseChange

variable {k : Type} [Field k]

/-! ## §1. `𝔾_m = Spec k[X, X⁻¹]` and its points -/

/-- `D = k[X, X⁻¹]`. -/
abbrev Dm (k : Type) [Field k] : Type := Localization.Away (Polynomial.X : Polynomial k)

/-- The universal unit `X ∈ Dˣ`. -/
def TU (k : Type) [Field k] : (Dm k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k) (S := Dm k)).unit

/-- Evaluation `D → R`, `X ↦ t`, at a unit `t` of a `k`-algebra `R`. -/
def evAt {R : Type} [CommRing R] [Algebra k R] (t : Rˣ) : Dm k →ₐ[k] R :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X : Polynomial k))
    (f := Polynomial.aeval (t : R)) (fun y => by
      obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp y.2
      rw [← hn, map_pow, Polynomial.aeval_X]
      exact t.isUnit.pow n)

theorem evAt_algebraMap {R : Type} [CommRing R] [Algebra k R] (t : Rˣ) (p : Polynomial k) :
    evAt t (algebraMap (Polynomial k) (Dm k) p) = Polynomial.aeval (t : R) p := by
  rw [evAt, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem evAt_TU {R : Type} [CommRing R] [Algebra k R] (t : Rˣ) :
    Units.map ((evAt t : Dm k →ₐ[k] R) : Dm k →* R) (TU k) = t := by
  apply Units.ext
  simp only [Units.coe_map, MonoidHom.coe_ofClass, TU, IsUnit.unit_spec]
  rw [evAt_algebraMap, Polynomial.aeval_X]

/-- Every `R`-point of a homomorphism `𝔾_m → G` is the pullback of the universal one. -/
theorem gm_point_universal {G : Over (Spec (CommRingCat.of k))} [GrpObj G]
    (Φ : ∀ (R : Type) [CommRing R] [Algebra k R], Rˣ →* (SpecPt k R ⟶ G))
    (hnat : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
      (t : Rˣ), Φ S (Units.map (f : R →* S) t) = SpecPtMap f ≫ Φ R t)
    (R : Type) [CommRing R] [Algebra k R] (t : Rˣ) :
    Φ R t = SpecPtMap (evAt t) ≫ Φ (Dm k) (TU k) := by
  rw [← hnat, evAt_TU]

theorem algebraMap_X_ne_zero_dm : Polynomial.X ∈ (Submonoid.powers (Polynomial.X : Polynomial k)) :=
  Submonoid.mem_powers _

instance : Algebra.FiniteType k (Dm k) := by
  change Algebra.FiniteType k (Localization (Submonoid.powers (Polynomial.X : Polynomial k)))
  infer_instance

instance : LocallyOfFiniteType (SpecPt k (Dm k)).hom :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- `f · y(c) = x(c)` for `f = x / y` in `D` and `c ∈ kˣ`. -/
theorem evAt_mk' (c : kˣ) (x : Polynomial k) (y : Submonoid.powers (Polynomial.X : Polynomial k)) :
    evAt c (IsLocalization.mk' (Dm k) x y) * (y : Polynomial k).eval (c : k) = x.eval (c : k) := by
  have h := IsLocalization.mk'_spec (Dm k) x y
  have h2 := congrArg (evAt c) h
  rw [map_mul, evAt_algebraMap, evAt_algebraMap] at h2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h2

theorem eval_powers_ne_zero (c : kˣ) (y : Submonoid.powers (Polynomial.X : Polynomial k)) :
    (y : Polynomial k).eval (c : k) ≠ 0 := by
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp y.2
  rw [← hn, Polynomial.eval_pow, Polynomial.eval_X]
  exact pow_ne_zero _ c.ne_zero

theorem evAt_mem_basicOpen (c : kˣ) (a : (SpecPt k k).left) (f : Dm k) :
    (SpecPtMap (evAt c)).left a ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Dm k))) ↔
      evAt c f ≠ 0 := by
  let a' : PrimeSpectrum k := a
  change PrimeSpectrum.comap ((evAt c : Dm k →ₐ[k] k) : Dm k →+* k) a' ∈
    PrimeSpectrum.basicOpen f ↔ _
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime a'.asIdeal,
    Ideal.mem_comap, Ideal.mem_bot]
  rfl

theorem subsingleton_specField' (a b : (SpecPt k k).left) : a = b := by
  change PrimeSpectrum k at a b
  exact Subsingleton.elim a b

/-- Factorization through an open immersion of `k`-schemes, from containment of the image. -/
theorem factor_openImm' {W G U : Over (Spec (CommRingCat.of k))} (inc : U ⟶ G)
    [IsOpenImmersion inc.left] (y : W ⟶ G) (hy : Set.range y.left ⊆ Set.range inc.left) :
    ∃ y' : W ⟶ U, y' ≫ inc = y := by
  refine ⟨Over.homMk (IsOpenImmersion.lift inc.left y.left hy) ?_, ?_⟩
  · rw [← Over.w inc, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w y]
  · ext1
    exact IsOpenImmersion.lift_fac _ _ _

/-! ## §2. Closed points of `𝔾_m` -/

section Closed

variable [IsAlgClosed k]

/-- Every closed point of `Spec D` is the image of a `k`-point `X ↦ c`, `c ∈ kˣ`. -/
theorem closedPoint_eq_evAt (x : (SpecPt k (Dm k)).left) (hx : IsClosed {x}) :
    ∃ c : kˣ, ∀ a, (SpecPtMap (evAt c)).left a = x := by
  let p := pointOfClosedPoint (SpecPt k (Dm k)).hom x hx
  have hp : p ≫ (SpecPt k (Dm k)).hom = 𝟙 _ := pointOfClosedPoint_comp _ x hx
  let φ := Spec.preimage p
  have hφ : Spec.map φ = p := Spec.map_preimage p
  have hφ1 : CommRingCat.ofHom (algebraMap k (Dm k)) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_id]
    exact hp
  have hφk : ∀ r : k, φ.hom (algebraMap k (Dm k) r) = r := fun r => by
    have := congrArg (fun f => f.hom r) hφ1
    simpa using this
  let c : kˣ := ((TU k).isUnit.map φ.hom).unit
  refine ⟨c, fun a => ?_⟩
  have hφe : φ = CommRingCat.ofHom ((evAt c : Dm k →ₐ[k] k) : Dm k →+* k) := by
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k))
    apply Polynomial.ringHom_ext
    · intro r
      change φ.hom (algebraMap (Polynomial k) (Dm k) (Polynomial.C r)) =
        evAt c (algebraMap (Polynomial k) (Dm k) (Polynomial.C r))
      rw [evAt_algebraMap, Polynomial.aeval_C, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, hφk]
      rfl
    · change φ.hom (algebraMap (Polynomial k) (Dm k) Polynomial.X) =
        evAt c (algebraMap (Polynomial k) (Dm k) Polynomial.X)
      rw [evAt_algebraMap, Polynomial.aeval_X]
      rfl
  change (Spec.map (CommRingCat.ofHom ((evAt c : Dm k →ₐ[k] k) : Dm k →+* k))) a = x
  rw [← hφe, hφ]
  exact pointOfClosedPoint_apply _ x hx a

end Closed

/-! ## §3. A homomorphism `𝔾_m → G` lands in every open subgroup -/

section OpenSubgroup

variable [IsAlgClosed k]

/-- **A homomorphism `𝔾_m → G` factors through every open subgroup `U ⊆ G`.** -/
theorem gmHom_factors_open {G U : Over (Spec (CommRingCat.of k))} [GrpObj G] [GrpObj U]
    (inc : U ⟶ G) [IsOpenImmersion inc.left] [IsMonHom inc]
    (Φ : ∀ (R : Type) [CommRing R] [Algebra k R], Rˣ →* (SpecPt k R ⟶ G))
    (hnat : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
      (t : Rˣ), Φ S (Units.map (f : R →* S) t) = SpecPtMap f ≫ Φ R t)
    (R : Type) [CommRing R] [Algebra k R] (t : Rˣ) :
    ∃ y : SpecPt k R ⟶ U, y ≫ inc = Φ R t := by
  let g := Φ (Dm k) (TU k)
  have hk : ∀ c : kˣ, SpecPtMap (evAt c) ≫ g = Φ k c := fun c => (gm_point_universal Φ hnat k c).symm
  let InU : kˣ → Prop := fun c => ∃ y : SpecPt k k ⟶ U, y ≫ inc = Φ k c
  have hmul : ∀ a b, InU a → InU b → InU (a * b) := by
    rintro a b ⟨y1, hy1⟩ ⟨y2, hy2⟩
    exact ⟨y1 * y2, by rw [mul_comp, hy1, hy2, map_mul]⟩
  let V : Set (SpecPt k (Dm k)).left := g.left ⁻¹' Set.range inc.left
  have hVopen : IsOpen V := inc.left.isOpenEmbedding.isOpen_range.preimage g.left.continuous
  have hInU : ∀ c, (∃ a, (SpecPtMap (evAt c)).left a ∈ V) → InU c := by
    rintro c ⟨a, ha⟩
    obtain ⟨y, hy⟩ := factor_openImm' inc (SpecPtMap (evAt c) ≫ g) (by
      rintro _ ⟨b, rfl⟩
      rw [subsingleton_specField' b a]
      exact ha)
    exact ⟨y, hy.trans (hk c)⟩
  have hV : ∀ c, InU c → ∀ a, (SpecPtMap (evAt c)).left a ∈ V := by
    rintro c ⟨y, hy⟩ a
    refine ⟨y.left a, ?_⟩
    change (y ≫ inc).left a = (SpecPtMap (evAt c) ≫ g).left a
    rw [hy, hk]
  have h1 : InU 1 := ⟨1, by rw [one_comp, map_one]⟩
  obtain ⟨a0⟩ : Nonempty (SpecPt k k).left := by
    change Nonempty (PrimeSpectrum k); infer_instance
  obtain ⟨_, ⟨f, rfl⟩, hf1, hfV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (hV 1 h1 a0) hVopen
  have hf1' : evAt (1 : kˣ) f ≠ 0 := (evAt_mem_basicOpen 1 a0 f).mp hf1
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (Polynomial.X : Polynomial k)) f
  simp only at hxy
  have hgood : ∀ c : kˣ, x.eval (c : k) ≠ 0 → InU c := fun c hc => by
    apply hInU c
    refine ⟨a0, hfV ((evAt_mem_basicOpen c a0 f).mpr ?_)⟩
    intro h0
    have := evAt_mk' c x y
    rw [hxy, h0, zero_mul] at this
    exact hc this.symm
  have hx0 : x ≠ 0 := by
    intro hx
    have := evAt_mk' 1 x y
    rw [hxy, hx, Polynomial.eval_zero] at this
    exact (mul_ne_zero hf1' (eval_powers_ne_zero 1 y)) this
  -- every `k`-point lies in `U`
  have hall : ∀ c : kˣ, InU c := by
    intro c
    classical
    let Bad : Finset k := {0} ∪ x.roots.toFinset ∪ x.roots.toFinset.image (fun z => (c : k) * z⁻¹)
    obtain ⟨b', hb'⟩ := Infinite.exists_notMem_finset Bad
    simp only [Bad, Finset.mem_union, Finset.mem_singleton, Multiset.mem_toFinset, Finset.mem_image,
      not_or, not_exists, not_and] at hb'
    obtain ⟨⟨hb0, hbr⟩, hbi⟩ := hb'
    let b : kˣ := Units.mk0 b' hb0
    have hb : x.eval (b : k) ≠ 0 := fun h => hbr ((Polynomial.mem_roots hx0).mpr h)
    have hb2 : x.eval ((b⁻¹ * c : kˣ) : k) ≠ 0 := by
      intro h
      apply hbi ((b⁻¹ * c : kˣ) : k) ((Polynomial.mem_roots hx0).mpr h)
      simp only [b, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    have := hmul b (b⁻¹ * c) (hgood b hb) (hgood _ hb2)
    rwa [mul_inv_cancel_left] at this
  -- hence `V` is everything
  have hJ : JacobsonSpace (SpecPt k (Dm k)).left :=
    LocallyOfFiniteType.jacobsonSpace (SpecPt k (Dm k)).hom
  have hVc : Vᶜ = ∅ := by
    have hcl : IsClosed Vᶜ := hVopen.isClosed_compl
    have hemp : Vᶜ ∩ closedPoints _ = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and,
        not_not]
      intro hz hzc
      obtain ⟨c, hc⟩ := closedPoint_eq_evAt z hzc
      exact hz (hc a0 ▸ hV c (hall c) a0)
    rw [← hcl.closure_eq, ← JacobsonSpace.closure_inter_closedPoints_eq_closure hcl.isLocallyClosed,
      hemp, closure_empty]
  obtain ⟨g', hg'⟩ := factor_openImm' inc g (by
    rintro _ ⟨z, rfl⟩
    have : z ∈ V := by
      by_contra hz
      have : z ∈ Vᶜ := hz
      rw [hVc] at this
      exact this
    exact this)
  refine ⟨SpecPtMap (evAt t) ≫ g', ?_⟩
  rw [Category.assoc, hg', gm_point_universal Φ hnat R t]

/-- **A homomorphism `𝔾_m^r → G` factors through every open subgroup `U ⊆ G`.** -/
theorem torusHom_factors_open {X G U : Over (Spec (CommRingCat.of k))} [GrpObj X] [GrpObj G]
    [GrpObj U] (inc : U ⟶ G) [IsOpenImmersion inc.left] [IsMonHom inc] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (SpecPt k R ⟶ X))
    (hnat : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = SpecPtMap f ≫ e R t)
    (ψ : X ⟶ G) [IsMonHom ψ]
    (R : Type) [CommRing R] [Algebra k R] (t : Fin r → Rˣ) :
    ∃ y : SpecPt k R ⟶ U, y ≫ inc = e R t ≫ ψ := by
  have hcoord : ∀ (i : Fin r) (u : Rˣ), ∃ y : SpecPt k R ⟶ U, y ≫ inc = e R (Pi.mulSingle i u) ≫ ψ := by
    intro i u
    let Φ : ∀ (R : Type) [CommRing R] [Algebra k R], Rˣ →* (SpecPt k R ⟶ G) := fun R _ _ =>
      { toFun := fun u => e R (Pi.mulSingle i u) ≫ ψ
        map_one' := by rw [Pi.mulSingle_one, map_one, one_comp]
        map_mul' := fun u v => by rw [Pi.mulSingle_mul, map_mul, mul_comp] }
    refine gmHom_factors_open inc Φ (fun R S _ _ _ _ f u => ?_) R u
    change e S (Pi.mulSingle i (Units.map (f : R →* S) u)) ≫ ψ = SpecPtMap f ≫ e R (Pi.mulSingle i u) ≫ ψ
    rw [← Category.assoc, ← hnat]
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  have hall : ∀ s : Finset (Fin r), ∃ y : SpecPt k R ⟶ U,
      y ≫ inc = e R (∏ i ∈ s, Pi.mulSingle i (t i)) ≫ ψ := by
    intro s
    classical
    refine Finset.induction_on s ?_ ?_
    · exact ⟨1, by rw [Finset.prod_empty, map_one, one_comp, one_comp]⟩
    · intro a s ha ih
      obtain ⟨y1, hy1⟩ := hcoord a (t a)
      obtain ⟨y2, hy2⟩ := ih
      refine ⟨y1 * y2, ?_⟩
      rw [Finset.prod_insert ha, map_mul, mul_comp, mul_comp, hy1, hy2]
  obtain ⟨y, hy⟩ := hall Finset.univ
  rw [Finset.univ_prod_mulSingle] at hy
  exact ⟨y, hy⟩

end OpenSubgroup

/-! ## §4. The toric rank inequality, identity-component hypothesis discharged -/

section Assembly

variable {K : Type} [Field K] [IsAlgClosed K]

/-- **Toric rank cannot drop along a homomorphism that is injective on the `m`-torsion of a
torus** (over an algebraically closed field): `toricRank_le_of_torusMap` with the factorization of
the torus image through the open subgroup `U'` proved (`torusHom_factors_open`). -/
theorem toricRank_le_of_torusMap_open
    (X : Over (Spec (CommRingCat.of K))) [GrpObj X] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra K R], (Fin r → Rˣ) →* (SpecPt K R ⟶ X))
    (hnat : ∀ (R S : Type) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = SpecPtMap f ≫ e R t)
    (G' U' : Over (Spec (CommRingCat.of K))) [GrpObj G'] [GrpObj U'] (inc : U' ⟶ G')
    [IsOpenImmersion inc.left] [IsMonHom inc]
    (B' : Over (Spec (CommRingCat.of K))) [GrpObj B'] [IsProper B'.hom] (π : U' ⟶ B') [IsMonHom π]
    (r' : ℕ) (e' : ∀ (R : Type) [CommRing R] [Algebra K R], (Fin r' → Rˣ) →* (SpecPt K R ⟶ U'))
    (he'_inj : ∀ (R : Type) [CommRing R] [Algebra K R], Function.Injective (e' R))
    (he'_ker : ∀ (R : Type) [CommRing R] [Algebra K R] (u : SpecPt K R ⟶ U'),
      u ≫ π = 1 ↔ u ∈ (e' R).range)
    (ψ : X ⟶ G') [IsMonHom ψ]
    (m : ℕ) (hm : 2 ≤ m) [NeZero (m : K)]
    (hker : ∀ t : Fin r → Kˣ, t ^ m = 1 → e K t ≫ ψ = 1 → t = 1) :
    r ≤ r' :=
  toricRank_le_of_torusMap X r e hnat G' U' inc B' π r' e' he'_inj he'_ker ψ
    (fun R _ _ t => torusHom_factors_open inc r e hnat ψ R t) m hm hker

end Assembly

end ToricBaseChange
