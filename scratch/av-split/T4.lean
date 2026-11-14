import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.Contrib.AbVarBC.Tangent

/-!
# av-split, row H-24 (`PkgI2.ReductionTorsionBijective`, T4, I2-Red)

The row is imported from `ZInQKernel/HDecomp/Objects.lean` (unchanged; used at universe `0`).

Leaves (published form):
* `MulEtaleAbelianScheme`: `[m]` on an abelian scheme is étale when `m` is invertible on the base;
* `UnramifiedSectionsEq`: two `S`-morphisms from a connected scheme into an unramified separated
  `S`-scheme that agree at one point (with residue fields) are equal;
* `StacksHenselEtaleSection`: étale algebras over a henselian local ring have sections through
  rational primes.

Glue:
* `henselian_of_isAlgClosed` (proved): a valuation subring of an algebraically closed field is a
  henselian local ring;
* `HenselEtaleLift` (GLUE Prop, scheme form of the Hensel property);
* everything else (valuative criterion for the lifts, the adjunction for points of `𝒜_K`, the
  group laws) is proved below from Mathlib.
-/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AvSplit.T4

open PkgI2

/-! ## 1. Leaves -/

/-- **LEAF (H-24, a): multiplication by `m` on an abelian scheme is étale for `m` invertible on
the base.** Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §7.3, Lemma 2 (b) (UNVERIFIED
locator: for a smooth commutative group scheme `G` over `S` with connected fibres, `[n]_G` is étale
if `n` is invertible on `S`; for an abelian scheme it is moreover finite and flat); also Mumford,
*Geometric invariant theory* (3rd ed. 1994), §6.1 and Mumford, *Abelian varieties*, §6 Application
2 over a field (UNVERIFIED). Stated over an affine base `Spec O`, `[m] = (𝟙 𝒜)^m` in the group
`Hom(𝒜, 𝒜)`, and an abelian scheme as in `PkgI2.IsAbelianScheme` (proper, smooth, geometrically
connected fibres; Mumford GIT Def. 6.1). -/
def MulEtaleAbelianScheme : Prop :=
  ∀ (O : Type) [CommRing O] (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] (m : ℕ),
    IsUnit (m : O) → Etale ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left)

/-- **LEAF (H-24, b): morphisms into an unramified separated scheme agreeing at a point.** The
Stacks project, Morphisms, Lemma 29.35.17 (UNVERIFIED tag/number; also EGA IV₄ 17.4.9): let `Y → S`
be unramified and separated, `X` a connected `S`-scheme, `a, b : X → Y` two `S`-morphisms and
`x ∈ X` with `a(x) = b(x)` such that the two induced maps `κ(a(x)) → κ(x)` agree; then `a = b`.
The pair (point, map of residue fields) is the morphism `Spec κ(x) → X → Y`, so the hypothesis is
`(Spec κ(x) → X) ≫ a = (Spec κ(x) → X) ≫ b` (Mathlib's `Scheme.fromSpecResidueField`, and
`Scheme.SpecToEquivOfField`). Unramified = formally unramified and locally of finite type
(Mathlib's notions). -/
def UnramifiedSectionsEq : Prop :=
  ∀ (X Y S : Scheme.{0}) (π : Y ⟶ S) [IsSeparated π] [LocallyOfFiniteType π]
    [FormallyUnramified π] (a b : X ⟶ Y), ConnectedSpace X → a ≫ π = b ≫ π →
    ∀ x : X, X.fromSpecResidueField x ≫ a = X.fromSpecResidueField x ≫ b → a = b

/-- **LEAF (H-24, c): sections of étale algebras over a henselian local ring.** The Stacks
project, Algebra, Lemma 10.153.3 (tag 04GG), (1) ⇒ (8) (UNVERIFIED item number): `(R, 𝔪, κ)`
henselian, `R → S` étale, `𝔮 ⊆ S` a prime over `𝔪` with `κ = κ(𝔮)`; then there is a section
`τ : S → R` of `R → S` (an `R`-algebra map) with `𝔮 = τ⁻¹(𝔪)`. Henselian is Mathlib's
`HenselianLocalRing` (Stacks Def. 10.153.1, simple roots lift). The condition `κ = κ(𝔮)` is
stated as `R → S/𝔮` onto (equivalent: `R/𝔪 ⊆ S/𝔮 ⊆ κ(𝔮)`). Used by the proof of the GLUE
`HenselEtaleLift` (§2). -/
def StacksHenselEtaleSection : Prop :=
  ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (S : Type) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (q : Ideal S) [q.IsPrime],
    q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R →
    Function.Surjective ((Ideal.Quotient.mk q).comp (algebraMap R S)) →
    ∃ τ : S →ₐ[R] R, q = (IsLocalRing.maximalIdeal R).comap τ

/-! ## 2. Glue -/

/-- **GLUE `HenselEtaleLift` (Hensel's property in scheme form).** For a henselian local ring `R`
with residue field `κ`, an étale morphism `f : X → Y`, a morphism `b : Spec R → Y` and a lift
`a₀ : Spec κ → X` of `b|_{Spec κ}`, there is a lift `a : Spec R → X` of `b` restricting to `a₀`.
What it needs: `b` factors through an affine open `U = Spec B ⊆ Y` (an open of the local scheme
`Spec R` containing the closed point is everything), `a₀` through an affine open
`V = Spec C ⊆ f⁻¹U`, `B → C` is étale (Mathlib `HasRingHomProperty`), and Stacks 04GG
(`StacksHenselEtaleSection`) for the étale `R`-algebra `R ⊗_B C` at the prime given by `a₀`. -/
def HenselEtaleLift : Prop :=
  ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) [Etale f]
    (b : Spec (.of R) ⟶ Y) (a₀ : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X),
    a₀ ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ b →
    ∃ a : Spec (.of R) ⟶ X, a ≫ f = b ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ a = a₀

/-- In a linearly ordered commutative monoid with zero, a product of elements `≤ 1` that is `< 1`
has a factor `< 1`. -/
theorem exists_lt_one_of_prod_lt_one {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ]
    (s : Multiset Γ) (hle : ∀ x ∈ s, x ≤ 1) (hlt : s.prod < 1) : ∃ x ∈ s, x < 1 := by
  by_contra h
  push Not at h
  have : s.prod = 1 := by
    rw [Multiset.prod_eq_one]
    intro x hx
    exact le_antisymm (hle x hx) (h x hx)
  exact (ne_of_lt hlt) this

/-- **A valuation subring of an algebraically closed field is a henselian local ring (proved).**
Every monic `f ∈ w[X]` splits over `Ω` with roots integral over `w`, hence in `w` (valuation rings
are integrally closed); if `f(a₀) ∈ 𝔪` then `∏ (a₀ - rᵢ) ∈ 𝔪`, so some `a₀ - rᵢ ∈ 𝔪`. (The
derivative condition is not needed.) -/
theorem henselian_of_isAlgClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (w : ValuationSubring Ω) :
    HenselianLocalRing w := by
  refine ⟨fun f hf a₀ h₁ _ => ?_⟩
  classical
  set F := f.map (algebraMap w Ω) with hF
  have hFm : F.Monic := hf.map _
  have hsplit : F = (F.roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFm
      IsAlgClosed.card_roots_eq_natDegree).symm
  -- every root lies in `w`
  have hroot : ∀ r ∈ F.roots, ∃ y : w, algebraMap w Ω y = r ∧ f.IsRoot y := by
    intro r hr
    have hr' : Polynomial.aeval r f = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact (Polynomial.mem_roots hFm.ne_zero).mp hr
    have hint : IsIntegral w r := ⟨f, hf, hr'⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨y, hy, ?_⟩
    apply IsFractionRing.injective w Ω
    have h2 : Polynomial.aeval (algebraMap w Ω y) f = 0 := hy ▸ hr'
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval] at h2
    rw [map_zero]
    exact h2
  -- `f(a₀) = ∏ (a₀ - r)` in `Ω`
  have h0 : F.eval (algebraMap w Ω a₀) = algebraMap w Ω (f.eval a₀) := by
    rw [hF, Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply,
      Polynomial.coe_aeval_eq_eval]
  have heval : algebraMap w Ω (f.eval a₀) = (F.roots.map fun r => algebraMap w Ω a₀ - r).prod := by
    rw [← h0]
    conv_lhs => rw [hsplit]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp
  have hv : w.valuation (algebraMap w Ω (f.eval a₀)) < 1 :=
    (ValuationSubring.valuation_lt_one_iff w _).mp h₁
  rw [heval, map_multiset_prod, Multiset.map_map] at hv
  obtain ⟨t, ht, hlt⟩ := exists_lt_one_of_prod_lt_one _ (by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
    obtain ⟨y, rfl, -⟩ := hroot r hr
    simp only [Function.comp_apply]
    rw [← map_sub]
    change w.valuation ((a₀ - y : w) : Ω) ≤ 1
    exact w.valuation_le_one _) hv
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
  obtain ⟨y, rfl, hy⟩ := hroot r hr
  refine ⟨y, hy, ?_⟩
  simp only [Function.comp_apply] at hlt
  rw [← map_sub] at hlt
  have : a₀ - y ∈ IsLocalRing.maximalIdeal w := (ValuationSubring.valuation_lt_one_iff w _).mpr hlt
  rw [← neg_sub]
  exact neg_mem this

/-! ## 3. The setting: points of `𝒜` over `w`, `κ(w)` and `K̄` -/

section Setting

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)

/-- `Spec K → Spec O`. -/
abbrev fK (K : Type) [Field K] (O : ValuationSubring K) : Spec (.of K) ⟶ Spec (.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O K))

/-- `Spec w` over `Spec O`. -/
abbrev Pw : Over (Spec (.of O)) := Over.mk (Spec.map (CommRingCat.ofHom (toW O w hw)))

/-- `Spec κ(w)` over `Spec O` (the source of the points `y` in `IsReductionOf`). -/
abbrev Pk : Over (Spec (.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (toW O w hw))))

/-- `Spec K̄` over `Spec O`, as the image of `Spec K̄ / K` under `Over.map`. -/
abbrev PKb (K : Type) [Field K] (O : ValuationSubring K) : Over (Spec (.of O)) :=
  (Over.map (fK K O)).obj (specOver K (AlgebraicClosure K))

/-- `Spec K̄ → Spec w` over `O`. -/
def iota : PKb K O ⟶ Pw hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom w.subtype)) (by
    show Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom (toW O w hw)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap O K))
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl)

/-- `Spec κ(w) → Spec w` over `O`. -/
def rho : Pk hw ⟶ Pw hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue w))) (by
    simp only [Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

theorem iota_left : (iota hw).left = Spec.map (CommRingCat.ofHom w.subtype) := rfl
theorem rho_left : (rho hw).left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) := rfl

end Setting

section RedMul

open scoped CategoryTheory.Obj

/-- The adjunction bijection `Hom(T, g^* M) ≃ Hom(g_! T, M)` is multiplicative (task
alg-frob-red's `pb_symm_mul`, copied). -/
theorem pb_symm_mul {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S')
    (u w : T ⟶ (Over.pullback g).obj M) :
    ((Over.mapPullbackAdj g).homEquiv T M).symm (u * w) =
      ((Over.mapPullbackAdj g).homEquiv T M).symm u *
        ((Over.mapPullbackAdj g).homEquiv T M).symm w := by
  obtain ⟨p, rfl⟩ := ((Over.mapPullbackAdj g).homEquiv T M).surjective u
  obtain ⟨q, rfl⟩ := ((Over.mapPullbackAdj g).homEquiv T M).surjective w
  have hm : (Over.mapPullbackAdj g).homEquiv T M (p * q) =
      (Over.mapPullbackAdj g).homEquiv T M p * (Over.mapPullbackAdj g).homEquiv T M q := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_mul, MonObj.comp_mul]
  rw [← hm, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end RedMul

/-- `pb_symm_mul` for the group law of `(Over.pullback g).mapGrp.obj G`. -/
theorem pb_symm_mul' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (u w : T ⟶ ((Over.pullback g).mapGrp.obj G).X) :
    ((Over.mapPullbackAdj g).homEquiv T G.X).symm (u * w) =
      ((Over.mapPullbackAdj g).homEquiv T G.X).symm u *
        ((Over.mapPullbackAdj g).homEquiv T G.X).symm w :=
  pb_symm_mul g G.X T u w

section Generic

variable {K : Type} [Field K] {O : ValuationSubring K} {A : Grp (Over (Spec (.of K)))}
  (𝒜 : Grp (Over (Spec (.of O))))
  (e : (Over.pullback (fK K O)).mapGrp.obj 𝒜 ≅ A)

/-- `x ∈ A(K̄)` as a `K̄`-point of `𝒜` over `O` (through `e` and the adjunction). -/
def G : Pts A (AlgebraicClosure K) →* (PKb K O ⟶ 𝒜.X) :=
  MonoidHom.mk' (fun x => ((Over.mapPullbackAdj (fK K O)).homEquiv _ 𝒜.X).symm
      (x ≫ e.inv.hom.hom)) (fun x y => by
    let u : Pts A (AlgebraicClosure K) →
        (specOver K (AlgebraicClosure K) ⟶ ((Over.pullback (fK K O)).mapGrp.obj 𝒜).X) :=
      fun x => x ≫ e.inv.hom.hom
    have hmul : u (x * y) = u x * u y := MonObj.mul_comp _ _ _
    show ((Over.mapPullbackAdj (fK K O)).homEquiv _ 𝒜.X).symm (u (x * y)) = _
    rw [hmul]
    exact pb_symm_mul' _ 𝒜 _ _ _)

theorem G_left (x : Pts A (AlgebraicClosure K)) :
    (G 𝒜 e x).left = (x ≫ e.inv.hom.hom).left ≫ pullback.fst 𝒜.X.hom (fK K O) := rfl

theorem inv_hom_hom : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
  congrArg (fun φ => φ.hom.hom) e.inv_hom_id

theorem hom_inv_hom : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ :=
  congrArg (fun φ => φ.hom.hom) e.hom_inv_id

theorem G_injective : Function.Injective (G 𝒜 e) := by
  intro x y h
  have h1 : x ≫ e.inv.hom.hom = y ≫ e.inv.hom.hom :=
    ((Over.mapPullbackAdj (fK K O)).homEquiv _ 𝒜.X).symm.injective h
  have h2 := congrArg (· ≫ e.hom.hom.hom) h1
  simp only [Category.assoc, inv_hom_hom, Category.comp_id] at h2
  exact h2

theorem G_surjective : Function.Surjective (G 𝒜 e) := by
  intro t
  refine ⟨(Over.mapPullbackAdj (fK K O)).homEquiv _ 𝒜.X t ≫ e.hom.hom.hom, ?_⟩
  show ((Over.mapPullbackAdj (fK K O)).homEquiv _ 𝒜.X).symm
    (((Over.mapPullbackAdj (fK K O)).homEquiv _ 𝒜.X t ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) = t
  erw [Category.assoc, hom_inv_hom, Category.comp_id, Equiv.symm_apply_apply]

end Generic

/-! ## 4. The valuative criterion: `𝒜(w) ≅ 𝒜(K̄)` (Mathlib) -/

section Valuative

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O) (𝒜 : Grp (Over (Spec (.of O))))

theorem PKb_hom_eq : (PKb K O).hom =
    Spec.map (CommRingCat.ofHom (algebraMap w (AlgebraicClosure K))) ≫
      Spec.map (CommRingCat.ofHom (toW O w hw)) := by
  show Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O K)) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The valuative square of a `K̄`-point of `𝒜` over `Spec w → Spec O`. -/
def vsq (t : PKb K O ⟶ 𝒜.X) : ValuativeCommSq 𝒜.X.hom where
  R := w
  K := AlgebraicClosure K
  i₁ := t.left
  i₂ := Spec.map (CommRingCat.ofHom (toW O w hw))
  commSq := ⟨(Over.w t).trans (PKb_hom_eq hw)⟩

/-- **Uniqueness of lifts** (Mathlib, valuative criterion of separatedness). -/
theorem iota_comp_injective [h : IsAbelianScheme 𝒜] :
    Function.Injective (fun x' : Pw hw ⟶ 𝒜.X => iota hw ≫ x') := by
  intro x₁ x₂ hx
  haveI := h.proper
  have hU := IsSeparated.valuativeCriterion 𝒜.X.hom (vsq hw 𝒜 (iota hw ≫ x₁))
  have e1 : (⟨x₁.left, rfl, Over.w x₁⟩ : (vsq hw 𝒜 (iota hw ≫ x₁)).commSq.LiftStruct) =
      ⟨x₂.left, (congrArg Over.Hom.left hx).symm, Over.w x₂⟩ := Subsingleton.elim _ _
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l e1)

/-- **Existence of lifts** (Mathlib, valuative criterion of universal closedness). -/
theorem iota_comp_surjective [h : IsAbelianScheme 𝒜] (t : PKb K O ⟶ 𝒜.X) :
    ∃ x' : Pw hw ⟶ 𝒜.X, iota hw ≫ x' = t := by
  haveI := h.proper
  have h1 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) 𝒜.X.hom := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨⟨l, hl1, hl2⟩⟩ := h1.1 (vsq hw 𝒜 t)
  exact ⟨Over.homMk l hl2, Over.OverMorphism.ext hl1⟩

/-- `IsReductionOf` in terms of `iota`, `rho` and `G`. -/
theorem isRed_iff {A : Grp (Over (Spec (.of K)))}
    (e : (Over.pullback (fK K O)).mapGrp.obj 𝒜 ≅ A) (x : Pts A (AlgebraicClosure K))
    (y : Pk hw ⟶ 𝒜.X) :
    IsReductionOf 𝒜 e w hw x y ↔ ∃ x' : Pw hw ⟶ 𝒜.X, iota hw ≫ x' = G 𝒜 e x ∧ rho hw ≫ x' = y := by
  constructor
  · rintro ⟨x', h1, h2⟩
    exact ⟨x', Over.OverMorphism.ext h1.symm, Over.OverMorphism.ext h2.symm⟩
  · rintro ⟨x', h1, h2⟩
    exact ⟨x', (congrArg Over.Hom.left h1).symm, (congrArg Over.Hom.left h2).symm⟩

end Valuative

/-! ## 5. Injectivity and surjectivity of reduction on `m`-torsion of `𝒜(w)` -/

/-- `Spec` of a map of fields is an epimorphism (as task g9-abvarbc's `epi_spec_map_field`). -/
theorem epi_spec_field {Ω Ω₂ : Type} [Field Ω] [Field Ω₂] (κ : Ω →+* Ω₂) :
    Epi (Spec.map (CommRingCat.ofHom κ)) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom κ)) := by
    constructor
    intro y
    refine ⟨IsLocalRing.closedPoint Ω₂, Subsingleton.elim _ _⟩
  haveI : Flat (Spec.map (CommRingCat.ofHom κ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [κ]
    change Module.Flat Ω Ω₂
    infer_instance
  infer_instance

section Torsion

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O) (𝒜 : Grp (Over (Spec (.of O))))

theorem comp_mulN {T : Over (Spec (.of O))} (c : T ⟶ 𝒜.X) (m : ℕ) :
    c ≫ (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X) = c ^ m := by
  rw [MonObj.comp_pow, Category.comp_id]

/-- **Reduction is injective on `m`-torsion of `𝒜(w)`** (from the leaves (a), (b)). -/
theorem rho_inj (hU : UnramifiedSectionsEq) (hE : MulEtaleAbelianScheme) [h : IsAbelianScheme 𝒜]
    (m : ℕ) (hm : IsUnit (m : O)) (a b : Pw hw ⟶ 𝒜.X) (ha : a ^ m = 1) (hb : b ^ m = 1)
    (hab : rho hw ≫ a = rho hw ≫ b) : a = b := by
  haveI := h.proper
  haveI : Etale ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left) := hE O 𝒜 m hm
  haveI : IsSeparated ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left ≫ 𝒜.X.hom) := by
    rw [Over.w (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X)]; infer_instance
  haveI : IsSeparated ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left) :=
    IsSeparated.of_comp _ 𝒜.X.hom
  have hcomp : a.left ≫ (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left =
      b.left ≫ (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left := by
    rw [← Over.comp_left, ← Over.comp_left, comp_mulN, comp_mulN, ha, hb]
  let p : Spec (.of (IsLocalRing.ResidueField w)) ⟶ Spec (.of w) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue w))
  have hp : p ≫ a.left = p ≫ b.left := congrArg Over.Hom.left hab
  have hfac := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
    (IsLocalRing.ResidueField w) (Spec (.of w)) p
  haveI : Epi (Spec.map ((Spec (.of w)).descResidueField (Scheme.stalkClosedPointTo p))) := by
    have := epi_spec_field ((Spec (.of w)).descResidueField (Scheme.stalkClosedPointTo p)).hom
    rwa [CommRingCat.ofHom_hom] at this
  have hx : (Spec (.of w)).fromSpecResidueField (p (IsLocalRing.closedPoint _)) ≫ a.left =
      (Spec (.of w)).fromSpecResidueField (p (IsLocalRing.closedPoint _)) ≫ b.left := by
    rw [← cancel_epi (Spec.map ((Spec (.of w)).descResidueField (Scheme.stalkClosedPointTo p))),
      ← Category.assoc, hfac, ← Category.assoc, hfac]
    exact hp
  exact Over.OverMorphism.ext (hU (Spec (.of w)) 𝒜.X.left 𝒜.X.left _ a.left b.left
    inferInstance hcomp _ hx)

/-- **Reduction is onto the `m`-torsion of `𝒜(κ(w))`** (from the leaf (a), the GLUE
`HenselEtaleLift` and `henselian_of_isAlgClosed`). -/
theorem rho_surj (hH : HenselEtaleLift) (hE : MulEtaleAbelianScheme) [h : IsAbelianScheme 𝒜]
    (m : ℕ) (hm : IsUnit (m : O)) (y : Pk hw ⟶ 𝒜.X) (hy : y ^ m = 1) :
    ∃ a : Pw hw ⟶ 𝒜.X, a ^ m = 1 ∧ rho hw ≫ a = y := by
  haveI := henselian_of_isAlgClosed w
  haveI : Etale ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left) := hE O 𝒜 m hm
  have hc : y.left ≫ (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ (1 : Pw hw ⟶ 𝒜.X).left := by
    rw [← Over.comp_left, comp_mulN, hy]
    exact (congrArg Over.Hom.left (MonObj.comp_one (rho hw))).symm
  obtain ⟨a, ha1, ha2⟩ := hH w 𝒜.X.left 𝒜.X.left _ (1 : Pw hw ⟶ 𝒜.X).left y.left hc
  have hw' : a ≫ 𝒜.X.hom = (Pw hw).hom := by
    rw [← Over.w (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X), ← Category.assoc, ha1]
    exact Over.w (1 : Pw hw ⟶ 𝒜.X)
  refine ⟨Over.homMk a hw', ?_, Over.OverMorphism.ext ha2⟩
  rw [← comp_mulN]
  exact Over.OverMorphism.ext ha1

end Torsion

/-! ## 6. The row -/

/-- **Row H-24 (`PkgI2.ReductionTorsionBijective`, at universe `0`) from the leaves
`MulEtaleAbelianScheme`, `UnramifiedSectionsEq` and the GLUE `HenselEtaleLift` (proved).** -/
theorem reductionTorsionBijective_of (hE : MulEtaleAbelianScheme) (hU : UnramifiedSectionsEq)
    (hH : HenselEtaleLift) : PkgI2.ReductionTorsionBijective.{0} := by
  intro K _ O _ w hw A _ 𝒜 _ e m _ hmO
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have hx' : x ^ m = 1 := hx
    obtain ⟨x', hx'1⟩ := iota_comp_surjective hw 𝒜 (G 𝒜 e x)
    have hx'm : x' ^ m = 1 := by
      apply iota_comp_injective hw 𝒜
      show iota hw ≫ x' ^ m = iota hw ≫ 1
      rw [MonObj.comp_pow, hx'1, MonObj.comp_one, ← map_pow, hx', map_one]
    refine ⟨rho hw ≫ x', ⟨?_, (isRed_iff hw 𝒜 e x _).2 ⟨x', hx'1, rfl⟩⟩, ?_⟩
    · rw [← MonObj.comp_pow, hx'm, MonObj.comp_one]
    · rintro y' ⟨-, hy'⟩
      obtain ⟨x'', h1, h2⟩ := (isRed_iff hw 𝒜 e x y').1 hy'
      have : x'' = x' := iota_comp_injective hw 𝒜 (h1.trans hx'1.symm)
      rw [← h2, this]
  · obtain ⟨a, ham, hay⟩ := rho_surj hw 𝒜 hH hE m hmO y hy
    obtain ⟨x, hx⟩ := G_surjective 𝒜 e (iota hw ≫ a)
    have hxm : x ^ m = 1 := G_injective 𝒜 e (by
      rw [map_pow, hx, ← MonObj.comp_pow, ham, MonObj.comp_one, map_one])
    refine ⟨x, ⟨hxm, (isRed_iff hw 𝒜 e x y).2 ⟨a, hx.symm, hay⟩⟩, ?_⟩
    rintro x2 ⟨hx2, hred⟩
    have hx2' : x2 ^ m = 1 := hx2
    obtain ⟨b, hb1, hb2⟩ := (isRed_iff hw 𝒜 e x2 y).1 hred
    have hbm : b ^ m = 1 := iota_comp_injective hw 𝒜 (by
      show iota hw ≫ b ^ m = iota hw ≫ 1
      rw [MonObj.comp_pow, hb1, MonObj.comp_one, ← map_pow, hx2', map_one])
    have hba : b = a := rho_inj hw 𝒜 hU hE m hmO b a hbm ham (hb2.trans hay.symm)
    apply G_injective 𝒜 e
    rw [← hb1, hba, hx]

/-! ## 7. The GLUE `HenselEtaleLift` from Stacks 04GG -/

open ZInQ.Contrib.AbVarBC.Tangent in
/-- **`HenselEtaleLift` from the leaf `StacksHenselEtaleSection` (proved).** Affine opens
`U ∋ f(a₀(s))`, `V ∋ a₀(s)`, `V ⊆ f⁻¹U`; `b`, `a₀` become ring maps `φ : Γ(U) → R`,
`ψ₀ : Γ(V) → κ` (task g9-abvarbc's `ptRing`); Stacks 04GG for the étale `R`-algebra
`S = R ⊗_{Γ(U)} Γ(V)` at the kernel `𝔮` of `S → κ` gives `τ : S → R`, and `ψ = τ ∘ (1 ⊗ -)`
defines the lift. -/
theorem henselEtaleLift_of_stacks (hS : StacksHenselEtaleSection) : HenselEtaleLift := by
  intro R _ _ X Y f _ b a₀ hc
  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue R)).hom := by
    change IsLocalHom (IsLocalRing.residue R); infer_instance
  set s : Spec (.of (IsLocalRing.ResidueField R)) :=
    IsLocalRing.closedPoint (IsLocalRing.ResidueField R) with hs
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (a₀ s))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show a₀ s ∈ f ⁻¹ᵁ U from hyU)
      (f ⁻¹ᵁ U).isOpen
  have hres : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) s =
      IsLocalRing.closedPoint R := Spec_closedPoint
  have hfs : (a₀ ≫ f) s = b (IsLocalRing.closedPoint R) := by
    rw [hc, Scheme.Hom.comp_apply, hres]
  have hb : b (IsLocalRing.closedPoint R) ∈ U := by
    rw [← hfs]; exact hyU
  have hxV' : a₀ (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) ∈ V := hxV
  have hp1 : (a₀ ≫ f) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) ∈ U := hyU
  have hp2 : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ b)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) ∈ U := by
    rw [← hc]; exact hp1
  set φ : Γ(Y, U) ⟶ CommRingCat.of R := ptRing b hb with hφ
  set ψ₀ : Γ(X, V) ⟶ CommRingCat.of (IsLocalRing.ResidueField R) := ptRing a₀ hxV' with hψ₀
  set θ := f.appLE U V hVU with hθ
  have hcomp : θ ≫ ψ₀ = φ ≫ CommRingCat.ofHom (IsLocalRing.residue R) := by
    have h1 := ptRing_comp hV f hU hVU a₀ hxV' hp1
    have h2 := ptRing_specMap_comp hU (CommRingCat.ofHom (IsLocalRing.residue R)) b hb hp2
    rw [← h1, ← h2]
    exact ptRing_congr hc _ _
  -- the ring-level situation
  letI : Algebra Γ(Y, U) R := φ.hom.toAlgebra
  letI : Algebra Γ(Y, U) Γ(X, V) := θ.hom.toAlgebra
  haveI : Algebra.Etale Γ(Y, U) Γ(X, V) :=
    HasRingHomProperty.appLE (P := @Etale) f ‹Etale f› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  letI : Algebra Γ(Y, U) (IsLocalRing.ResidueField R) :=
    (φ ≫ CommRingCat.ofHom (IsLocalRing.residue R)).hom.toAlgebra
  haveI : IsScalarTower Γ(Y, U) R (IsLocalRing.ResidueField R) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g₁ : Γ(X, V) →ₐ[Γ(Y, U)] IsLocalRing.ResidueField R :=
    { ψ₀.hom with
      commutes' := fun c => congrArg (fun t => t.hom c) hcomp }
  let χ : TensorProduct Γ(Y, U) R Γ(X, V) →ₐ[R] IsLocalRing.ResidueField R :=
    Algebra.TensorProduct.lift (Algebra.ofId R _) g₁ (fun _ _ => Commute.all _ _)
  let q : Ideal (TensorProduct Γ(Y, U) R Γ(X, V)) := RingHom.ker χ
  haveI : q.IsPrime := RingHom.ker_isPrime χ
  have hχr : ∀ r : R, χ (algebraMap R _ r) = IsLocalRing.residue R r := fun r => χ.commutes r
  have hq1 : q.comap (algebraMap R _) = IsLocalRing.maximalIdeal R := by
    ext r
    simp only [Ideal.mem_comap, q, RingHom.mem_ker, hχr]
    exact IsLocalRing.residue_eq_zero_iff r
  have hq2 : Function.Surjective ((Ideal.Quotient.mk q).comp (algebraMap R _)) := by
    intro t
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (χ u)
    refine ⟨r, ?_⟩
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq]
    change χ (algebraMap R _ r - u) = 0
    rw [map_sub, hχr, hr, sub_self]
  obtain ⟨τ, hτ⟩ := hS R (TensorProduct Γ(Y, U) R Γ(X, V)) q hq1 hq2
  -- `res ∘ τ = χ`
  have hkey : ∀ u, IsLocalRing.residue R (τ u) = χ u := by
    intro u
    obtain ⟨r, hr⟩ := hq2 (Ideal.Quotient.mk q u)
    have hmem : algebraMap R _ r - u ∈ q := Ideal.Quotient.eq.mp hr
    have h1 : χ (algebraMap R _ r - u) = 0 := hmem
    have h2 : τ (algebraMap R _ r - u) ∈ IsLocalRing.maximalIdeal R := by
      rw [hτ] at hmem; exact hmem
    rw [map_sub, hχr, sub_eq_zero] at h1
    have h3 := (IsLocalRing.residue_eq_zero_iff _).mpr h2
    rw [map_sub, τ.commutes, Algebra.algebraMap_self, RingHom.id_apply, map_sub,
      sub_eq_zero] at h3
    rw [← h3, h1]
  let ψ : Γ(X, V) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (τ.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := Γ(Y, U)) (A := R)).toRingHom)
  have hψθ : θ ≫ ψ = φ := by
    ext c
    change τ (Algebra.TensorProduct.includeRight (algebraMap Γ(Y, U) Γ(X, V) c)) = φ c
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply Γ(Y, U) R, τ.commutes]
    rfl
  have hψres : ψ ≫ CommRingCat.ofHom (IsLocalRing.residue R) = ψ₀ := by
    ext c
    change IsLocalRing.residue R (τ (1 ⊗ₜ c)) = ψ₀ c
    rw [hkey]
    change Algebra.TensorProduct.lift (Algebra.ofId R _) g₁ _ (1 ⊗ₜ c) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl
  refine ⟨ofRing hV ψ, ?_, ?_⟩
  · show (Spec.map ψ ≫ hV.fromSpec) ≫ f = b
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU,
      ← Category.assoc, ← Spec.map_comp, ← hθ, hψθ]
    conv_rhs => rw [eq_ofRing_ptRing hU b hb]
    rfl
  · show Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ Spec.map ψ ≫ hV.fromSpec = a₀
    rw [← Category.assoc, ← Spec.map_comp, hψres]
    conv_rhs => rw [eq_ofRing_ptRing hV a₀ hxV']
    rfl

/-- **Row H-24 from the three leaves (proved).** -/
theorem reductionTorsionBijective_of_leaves (hE : MulEtaleAbelianScheme)
    (hU : UnramifiedSectionsEq) (hS : StacksHenselEtaleSection) :
    PkgI2.ReductionTorsionBijective.{0} :=
  reductionTorsionBijective_of hE hU (henselEtaleLift_of_stacks hS)

/-! ## 8. Leaf (b) is a theorem of Mathlib -/

/-- **`UnramifiedSectionsEq` holds (proved from Mathlib).** The diagonal `Δ : Y → Y ×_S Y` of
an unramified separated `π` is an open (`isOpenImmersion_diagonal`) and closed immersion; the
preimage of its image under `(a, b)` is clopen, contains `x`, hence is all of the connected `X`;
so `(a, b)` factors through `Δ` and `a = b`. (Stacks, Morphisms, Lemma 29.35.17, proof.) -/
theorem unramifiedSectionsEq : UnramifiedSectionsEq := by
  intro X Y S π _ _ _ a b hX hab x hx
  let p : X ⟶ pullback π π := pullback.lift a b hab
  let Δ : Y ⟶ pullback π π := pullback.diagonal π
  haveI : IsClosedImmersion Δ := IsSeparated.isClosedImmersion_diagonal
  have hopen : IsOpen (Set.range Δ) := Δ.isOpenEmbedding.isOpen_range
  have hclosed : IsClosed (Set.range Δ) := Δ.isClosedEmbedding.isClosed_range
  have hclopen : IsClopen (p ⁻¹' Set.range Δ) :=
    ⟨hclosed.preimage p.continuous, hopen.preimage p.continuous⟩
  have hfac : X.fromSpecResidueField x ≫ p = (X.fromSpecResidueField x ≫ a) ≫ Δ := by
    apply pullback.hom_ext
    · simp only [p, Δ, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [p, Δ, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      exact hx.symm
  have hxU : x ∈ p ⁻¹' Set.range Δ := by
    let pt : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
    refine ⟨(X.fromSpecResidueField x ≫ a) pt, ?_⟩
    calc Δ ((X.fromSpecResidueField x ≫ a) pt) = ((X.fromSpecResidueField x ≫ a) ≫ Δ) pt :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = (X.fromSpecResidueField x ≫ p) pt := by rw [hfac]
      _ = p (X.fromSpecResidueField x pt) := Scheme.Hom.comp_apply _ _ _
      _ = p x := by rw [Scheme.fromSpecResidueField_apply]
  have huniv : p ⁻¹' Set.range Δ = Set.univ := hclopen.eq_univ ⟨x, hxU⟩
  have hrange : Set.range p ⊆ Set.range Δ := by
    rintro _ ⟨y, rfl⟩
    have : y ∈ p ⁻¹' Set.range Δ := huniv ▸ Set.mem_univ y
    exact this
  let q := IsOpenImmersion.lift Δ p hrange
  have hq : q ≫ Δ = p := IsOpenImmersion.lift_fac Δ p hrange
  have ha : a = q := by
    have := congrArg (· ≫ pullback.fst π π) hq
    simp only [Category.assoc, Δ, pullback.diagonal_fst, Category.comp_id, p,
      pullback.lift_fst] at this
    exact this.symm
  have hb : b = q := by
    have := congrArg (· ≫ pullback.snd π π) hq
    simp only [Category.assoc, Δ, pullback.diagonal_snd, Category.comp_id, p,
      pullback.lift_snd] at this
    exact this.symm
  rw [ha, hb]

/-- **Row H-24 from the two leaves (a), (c) (proved).** -/
theorem reductionTorsionBijective_of_leaves' (hE : MulEtaleAbelianScheme)
    (hS : StacksHenselEtaleSection) : PkgI2.ReductionTorsionBijective.{0} :=
  reductionTorsionBijective_of_leaves hE unramifiedSectionsEq hS

/-! ## 9. Leaf (c) is a theorem of Mathlib (via the local structure of étale algebras) -/

open Polynomial in
/-- **`StacksHenselEtaleSection` holds (proved from Mathlib).** Mathlib's local structure theorem
(`Algebra.IsEtaleAt.exists_isStandardEtale`, Stacks 00UE) gives `f ∉ 𝔮` with `S_f` standard étale,
`S_f ≅ R[X]_g/(P)` (`P` monic, `P'` invertible). With `χ : S → S/𝔮 ≅ R/𝔪`, pick `a ∈ R` lifting
the image of `X`; then `P(a) ∈ 𝔪`, `P'(a)` is a unit, Hensel gives a root `α ≡ a`, `g(α)` is a unit,
and `X ↦ α` defines `τ : S → S_f → R`; `res ∘ τ = χ` (both are `R`-algebra maps out of `S_f`
agreeing on `X`), so `τ⁻¹(𝔪) = ker χ = 𝔮`. -/
theorem stacksHenselEtaleSection : StacksHenselEtaleSection := by
  intro R _ _ S _ _ _ q _ hq1 hq2
  classical
  set m := IsLocalRing.maximalIdeal R with hm
  haveI hmax : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  -- `χ : S → S/𝔮 ≅ R/𝔪`
  let jq : R ⧸ m →+* S ⧸ q := Ideal.quotientMap q (algebraMap R S) hq1.ge
  have hjqinj : Function.Injective jq := Ideal.quotientMap_injective' hq1.le
  have hjqsurj : Function.Surjective jq := by
    intro t
    obtain ⟨r, hr⟩ := hq2 t
    exact ⟨Ideal.Quotient.mk m r, by rw [Ideal.quotientMap_mk]; exact hr⟩
  let ejq : R ⧸ m ≃+* S ⧸ q := RingEquiv.ofBijective jq ⟨hjqinj, hjqsurj⟩
  let χ0 : S →+* R ⧸ m := ejq.symm.toRingHom.comp (Ideal.Quotient.mk q)
  have hχr : ∀ r : R, χ0 (algebraMap R S r) = Ideal.Quotient.mk m r := by
    intro r
    apply ejq.injective
    show ejq (ejq.symm (Ideal.Quotient.mk q (algebraMap R S r))) = _
    rw [RingEquiv.apply_symm_apply]
    show _ = jq (Ideal.Quotient.mk m r)
    rw [Ideal.quotientMap_mk]
  have hχker : ∀ s, χ0 s = 0 ↔ s ∈ q := by
    intro s
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    show ejq.symm (Ideal.Quotient.mk q s) = 0 ↔ _
    rw [map_eq_zero_iff _ ejq.symm.injective]
  let χ : S →ₐ[R] R ⧸ m := { χ0 with commutes' := hχr }
  -- local structure
  haveI : Algebra.IsEtaleAt R q := inferInstance
  obtain ⟨f, hfq, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  obtain ⟨Pr⟩ := hstd.nonempty_standardEtalePresentation
  have hχf : IsUnit (χ f) := isUnit_iff_ne_zero.mpr fun h => hfq ((hχker f).1 h)
  let χ' : Localization.Away f →ₐ[R] R ⧸ m := IsLocalization.Away.liftAlgHom f hχf
  have hχ' : ∀ s, χ' (algebraMap S (Localization.Away f) s) = χ s := fun s =>
    IsLocalization.Away.lift_eq f hχf s
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (χ' Pr.x)
  have hev : ∀ (b : R) (p : R[X]), Ideal.Quotient.mk m (p.eval b) =
      aeval (Ideal.Quotient.mk m b) p := by
    intro b p
    rw [← Ideal.Quotient.algebraMap_eq, Polynomial.aeval_algebraMap_apply,
      Polynomial.coe_aeval_eq_eval]
  have hevx : ∀ p : R[X], Ideal.Quotient.mk m (p.eval a) = χ' (aeval Pr.x p) := by
    intro p
    rw [hev, ha, Polynomial.aeval_algHom_apply]
  have h1 : Pr.f.eval a ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hevx, Pr.hasMap.1, map_zero]
  have h2 : IsUnit (Pr.f.derivative.eval a) := by
    have hu := (Pr.hasMap.isUnit_derivative_f).map χ'
    rw [← hevx] at hu
    by_contra hna
    have : Pr.f.derivative.eval a ∈ m := (IsLocalRing.mem_maximalIdeal _).mpr hna
    rw [← Ideal.Quotient.eq_zero_iff_mem] at this
    rw [this] at hu
    exact not_isUnit_zero hu
  obtain ⟨α, hroot, hαa⟩ := HenselianLocalRing.is_henselian Pr.f Pr.monic_f a h1 h2
  have hαres : Ideal.Quotient.mk m α = Ideal.Quotient.mk m a :=
    Ideal.Quotient.eq.mpr hαa
  have hg : IsUnit (aeval α Pr.g) := by
    rw [Polynomial.coe_aeval_eq_eval]
    have hu := Pr.hasMap.2.map χ'
    rw [← hevx] at hu
    have e1 : Ideal.Quotient.mk m (Pr.g.eval α) = Ideal.Quotient.mk m (Pr.g.eval a) := by
      rw [hev, hev, hαres]
    rw [← e1] at hu
    by_contra hna
    have : Pr.g.eval α ∈ m := (IsLocalRing.mem_maximalIdeal _).mpr hna
    rw [← Ideal.Quotient.eq_zero_iff_mem] at this
    rw [this] at hu
    exact not_isUnit_zero hu
  have hmap : Pr.HasMap α := ⟨by rw [Polynomial.coe_aeval_eq_eval]; exact hroot, hg⟩
  let τ' : Localization.Away f →ₐ[R] R :=
    ((StandardEtalePair.lift (P := Pr.P) α hmap)).comp Pr.equivRing.toAlgHom
  have hτ'x : τ' Pr.x = α := by
    show (StandardEtalePair.lift (P := Pr.P) α hmap) (Pr.equivRing Pr.x) = α
    rw [Pr.equivRing_x, StandardEtalePair.lift_X]
  let τ : S →ₐ[R] R := τ'.comp (IsScalarTower.toAlgHom R S (Localization.Away f))
  have hcomp : (Ideal.Quotient.mkₐ R m).comp τ' = χ' := by
    apply Pr.hom_ext
    rw [AlgHom.comp_apply, hτ'x, Ideal.Quotient.mkₐ_eq_mk, hαres, ha]
  refine ⟨τ, ?_⟩
  ext s
  rw [Ideal.mem_comap]
  have key : Ideal.Quotient.mk m (τ s) = χ s := by
    have := congrArg (fun φ : Localization.Away f →ₐ[R] R ⧸ m =>
      φ (algebraMap S (Localization.Away f) s)) hcomp
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    rw [hχ'] at this
    exact this
  have hiff : τ s ∈ m ↔ s ∈ q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, key]
    exact hχker s
  exact hiff.symm

/-- **Row H-24 from the single leaf (a) (proved).** -/
theorem reductionTorsionBijective_of_mulEtale (hE : MulEtaleAbelianScheme) :
    PkgI2.ReductionTorsionBijective.{0} :=
  reductionTorsionBijective_of_leaves hE unramifiedSectionsEq stacksHenselEtaleSection

end AvSplit.T4

#print axioms AvSplit.T4.henselian_of_isAlgClosed
#print axioms AvSplit.T4.reductionTorsionBijective_of
#print axioms AvSplit.T4.henselEtaleLift_of_stacks
#print axioms AvSplit.T4.reductionTorsionBijective_of_leaves
#print axioms AvSplit.T4.unramifiedSectionsEq
#print axioms AvSplit.T4.reductionTorsionBijective_of_leaves'
#print axioms AvSplit.T4.stacksHenselEtaleSection
#print axioms AvSplit.T4.reductionTorsionBijective_of_mulEtale
