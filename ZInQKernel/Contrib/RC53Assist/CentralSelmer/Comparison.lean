import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.Central

/-!
# Central Selmer comparison: rationalization and explicit cohomology

The manuscript's base-zero argument (lines 4341--4352) uses the full Selmer
group, including its possible divisible Shafarevich--Tate part. The central
quasi-isomorphism is described at lines 3952--3962, universal coefficients
at lines 4007--4018 and 5305--5311, and quadratic sum-and-difference descent
at lines 2616--2626. The last maps have bounded two-primary kernel and
cokernel; no integral splitting is required.

The bibliography cites Milne's Arithmetic Duality Theorems, Nekovar's
Selmer Complexes, and Silverman's Arithmetic of Elliptic Curves. No new
printed leaf from any source is introduced in this development.

This development proves the algebraic rationalization step for the existing
`RatTate` construction. Its final comparison constructors require an actual
identification of the matrix model with rational Kummer cohomology. That
identification is not inferred from an arbitrary square matrix or from the
coranks alone. No printed theorem is assumed here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC53Assist.CentralSelmer

open ZInQ.Manuscript.RC.BaseZeroLimit ZInQ.Manuscript.SelmerTwoPower
open TauCeti TauCeti.ContCohomology CategoryTheory Matrix

section Rationalization

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- An additive map has bounded kernel and cokernel, with possibly different
nonzero integer annihilators. This is an algebraic condition, not a printed leaf. -/
def BoundedDefects (f : M →+ N) : Prop :=
  ∃ a b : ℕ, a ≠ 0 ∧ b ≠ 0 ∧
    (∀ x : M, f x = 0 → a • x = 0) ∧
    (∀ y : N, ∃ x : M, f x = b • y)

private theorem exists_scaled_inverse (f : M →+ N) (a b : ℕ)
    (hk : ∀ x : M, f x = 0 → a • x = 0)
    (hc : ∀ y : N, ∃ x : M, f x = b • y) :
    ∃ g : N →+ M, (∀ x : M, g (f x) = (a * b) • x) ∧
      (∀ y : N, f (g y) = (a * b) • y) := by
  classical
  let q : N → M := fun y => Classical.choose (hc y)
  have hq (y : N) : f (q y) = b • y := Classical.choose_spec (hc y)
  have independent (x x' : M) (h : f x = f x') : a • x = a • x' := by
    have hz : f (x - x') = 0 := by rw [map_sub, h, sub_self]
    have := hk (x - x') hz
    rwa [nsmul_sub, sub_eq_zero] at this
  let g : N →+ M :=
    { toFun := fun y => a • q y
      map_zero' := by
        have h := independent (q 0) 0 (by rw [hq, nsmul_zero, map_zero])
        simpa only [nsmul_zero] using h
      map_add' := fun y z => by
        have h := independent (q (y + z)) (q y + q z) (by
          rw [hq, map_add, hq, hq, nsmul_add])
        simpa only [nsmul_add] using h }
  refine ⟨g, fun x => ?_, fun y => ?_⟩
  · change a • q (f x) = (a * b) • x
    have h := independent (q (f x)) (b • x) (by rw [hq, map_nsmul])
    simpa only [← smul_smul] using h
  · change f (a • q y) = (a * b) • y
    rw [map_nsmul, hq, ← smul_smul]

private def ratTateEquivOfScaledInverse (f : M →+ N) (g : N →+ M) (n : ℕ)
    (hn : n ≠ 0) (hgf : ∀ x : M, g (f x) = n • x)
    (hfg : ∀ y : N, f (g y) = n • y) : RatTate M ≃ₗ[ℚ_[2]] RatTate N := by
  have hn' : (n : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine LinearEquiv.ofLinearMap (RatTate.map f)
    ((n : ℚ_[2])⁻¹ • RatTate.map g) ?_ ?_
  · apply LinearMap.ext
    intro t
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RatTate.smul_apply,
      RatTate.map_apply, LinearMap.id_apply]
    rw [hfg, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel_left₀ hn']
  · apply LinearMap.ext
    intro t
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RatTate.smul_apply,
      RatTate.map_apply, LinearMap.id_apply]
    rw [hgf, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel_left₀ hn']

/-- Rational Tate modules invert every additive map with bounded kernel and
cokernel. In particular they invert the manuscript's two-primary
sum-and-difference maps without discarding divisible Selmer classes. -/
theorem ratTate_map_bijective_of_boundedDefects (f : M →+ N) (h : BoundedDefects f) :
    Function.Bijective (RatTate.map f) := by
  obtain ⟨a, b, ha, hb, hk, hc⟩ := h
  obtain ⟨g, hgf, hfg⟩ := exists_scaled_inverse f a b hk hc
  exact (ratTateEquivOfScaledInverse f g (a * b) (Nat.mul_ne_zero ha hb) hgf hfg).bijective

/-- The rationalized equivalence is induced by the original additive map,
not chosen by a dimension count. -/
def ratTateEquivOfBoundedDefects (f : M →+ N) (h : BoundedDefects f) :
    RatTate M ≃ₗ[ℚ_[2]] RatTate N :=
  LinearEquiv.ofBijective (RatTate.map f) (ratTate_map_bijective_of_boundedDefects f h)

/-- Sum-and-difference maps that compose in both directions to a nonzero
integer multiplication have bounded defects. -/
theorem boundedDefects_of_scaledInverse (f : M →+ N) (g : N →+ M) (n : ℕ)
    (hn : n ≠ 0) (hgf : ∀ x : M, g (f x) = n • x)
    (hfg : ∀ y : N, f (g y) = n • y) : BoundedDefects f := by
  refine ⟨n, n, hn, hn, fun x hx => ?_, fun y => ⟨g y, hfg y⟩⟩
  rw [← hgf, hx, map_zero]

/-- A finite kernel and a finite cokernel are a sufficient special case. -/
theorem boundedDefects_of_finite (f : M →+ N) [Finite f.ker] [Finite (N ⧸ f.range)] :
    BoundedDefects f := by
  refine ⟨Nat.card f.ker, Nat.card (N ⧸ f.range), Nat.card_pos.ne', Nat.card_pos.ne',
    fun x hx => ?_, fun y => ?_⟩
  · let x' : f.ker := ⟨x, hx⟩
    have hx' : Nat.card f.ker • x' = 0 := card_nsmul_eq_zero'
    exact congrArg Subtype.val hx'
  · have h : (Nat.card (N ⧸ f.range)) • (QuotientAddGroup.mk y : N ⧸ f.range) = 0 :=
      card_nsmul_eq_zero'
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h
    exact h

end Rationalization

section UniversalCoefficients

variable {V S : Type*} [AddCommGroup V] [Module ℚ_[2] V] [AddCommGroup S]

/-- The algebraic universal-coefficient step. A basis of the rational
cohomology, together with the actual map from its divisible lattice quotient
to full Selmer having bounded defects, determines the rational comparison.
Existence and arithmetic compatibility of that map remain separate inputs. -/
def universalCoefficientsRatTateEquiv {r : ℕ}
    (e : V ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    (j : (Fin r → Q2Z2) →+ S) (hj : BoundedDefects j) : V ≃ₗ[ℚ_[2]] RatTate S :=
  e.trans <| ((RatTate.piEquiv (M := Q2Z2) r).trans
    (LinearEquiv.piCongrRight fun _ => ratTateQ2Z2Equiv)).symm.trans
      (ratTateEquivOfBoundedDefects j hj)

end UniversalCoefficients

section QuadraticDecomposition

variable {S : Type*} [AddCommGroup S]

/-- The positive eigensubgroup of an additive involution. -/
def positivePart (τ : S →+ S) : AddSubgroup S := (τ - AddMonoidHom.id S).ker

/-- The negative eigensubgroup of an additive involution. At two these
subgroups need not give an integral direct-sum decomposition. -/
def negativePart (τ : S →+ S) : AddSubgroup S := (τ + AddMonoidHom.id S).ker

private def sumDifference (τ : S →+ S) (hτ : ∀ x, τ (τ x) = x) :
    S →+ positivePart τ × negativePart τ where
  toFun x :=
    (⟨x + τ x, by
      change τ (x + τ x) - (x + τ x) = 0
      rw [map_add, hτ]
      abel⟩,
      ⟨x - τ x, by
        change τ (x - τ x) + (x - τ x) = 0
        rw [map_sub, hτ]
        abel⟩)
  map_zero' := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · change (x + y) + τ (x + y) = (x + τ x) + (y + τ y)
      rw [map_add]
      abel
    · change (x + y) - τ (x + y) = (x - τ x) + (y - τ y)
      rw [map_add]
      abel

private def eigenspaceSum (τ : S →+ S) : positivePart τ × negativePart τ →+ S :=
  ((positivePart τ).subtype.comp (AddMonoidHom.fst _ _)) +
    ((negativePart τ).subtype.comp (AddMonoidHom.snd _ _))

private theorem sumDifference_defects (τ : S →+ S) (hτ : ∀ x, τ (τ x) = x) :
    BoundedDefects (sumDifference τ hτ) := by
  apply boundedDefects_of_scaledInverse (sumDifference τ hτ) (eigenspaceSum τ) 2 (by decide)
  · intro x
    change (x + τ x) + (x - τ x) = 2 • x
    rw [two_nsmul]
    abel
  · rintro ⟨p, n⟩
    have hp : τ (p : S) = (p : S) := by
      have h : τ (p : S) - (p : S) = 0 := p.2
      exact sub_eq_zero.mp h
    have hn : τ (n : S) = -(n : S) := by
      have h : τ (n : S) + (n : S) = 0 := n.2
      exact eq_neg_of_add_eq_zero_left h
    apply Prod.ext <;> apply Subtype.ext
    · change (p : S) + (n : S) + τ ((p : S) + (n : S)) = 2 • (p : S)
      rw [map_add, hp, hn, two_nsmul]
      abel
    · change (p : S) + (n : S) - τ ((p : S) + (n : S)) = 2 • (n : S)
      rw [map_add, hp, hn, two_nsmul]
      abel

/-- The sum-and-difference map gives the rational eigenspace splitting of
any additive involution. Both integral defects are killed by two; no integral
splitting and no finiteness of a Shafarevich--Tate group is assumed. -/
def ratTateEigenspaceEquiv (τ : S →+ S) (hτ : ∀ x, τ (τ x) = x) :
    RatTate S ≃ₗ[ℚ_[2]] RatTate (positivePart τ) × RatTate (negativePart τ) :=
  (ratTateEquivOfBoundedDefects (sumDifference τ hτ) (sumDifference_defects τ hτ)).trans
    RatTate.prodEquiv

end QuadraticDecomposition

section Products

variable (G : Type*) [Monoid G] [TopologicalSpace G]
  (M N : Type*) [AddCommGroup M] [AddCommGroup N]
  [TopologicalSpace M] [TopologicalSpace N]
  [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]
  [DistribMulAction G M] [DistribMulAction G N]
  [ContinuousSMul G M] [ContinuousSMul G N]

private def h1Fst : H1 G (M × N) →+ H1 G M :=
  explicitMap1 G (M × N) G M (ContinuousMonoidHom.id G)
    (AddMonoidHom.fst M N) continuous_fst (fun _ _ => rfl)

private def h1Snd : H1 G (M × N) →+ H1 G N :=
  explicitMap1 G (M × N) G N (ContinuousMonoidHom.id G)
    (AddMonoidHom.snd M N) continuous_snd (fun _ _ => rfl)

private def pairedCocycle (c : Z1 G M) (d : Z1 G N) : Z1 G (M × N) :=
  ⟨fun g => ((c : G → M) g, (d : G → N) g),
    mem_Z1_iff.mpr ⟨(mem_Z1_iff.mp c.2).1.prodMk (mem_Z1_iff.mp d.2).1,
      fun g h => Prod.ext ((mem_Z1_iff.mp c.2).2 g h) ((mem_Z1_iff.mp d.2).2 g h)⟩⟩

private theorem h1Product_bijective :
    Function.Bijective ((h1Fst G M N).prod (h1Snd G M N)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      have hf := congrArg Prod.fst hx
      have hs := congrArg Prod.snd hx
      change h1Fst G M N (c : H1 G (M × N)) = 0 at hf
      change h1Snd G M N (c : H1 G (M × N)) = 0 at hs
      erw [h1Fst, explicitMap1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hf
      erw [h1Snd, explicitMap1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hs
      obtain ⟨m, hm⟩ := hf
      obtain ⟨n, hn⟩ := hs
      apply H1pi_eq_zero_iff.mpr
      exact mem_B1_iff.mpr ⟨(m, n), fun g => Prod.ext (hm g) (hn g)⟩
  · rintro ⟨x, y⟩
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      induction y using QuotientAddGroup.induction_on with
      | H d =>
        exact ⟨(pairedCocycle G M N c d : H1 G (M × N)), rfl⟩

/-- First continuous cohomology commutes with a product of topological
coefficient modules. The forward map consists of the two coefficient projections. -/
def h1ProdAddEquiv : H1 G (M × N) ≃+ H1 G M × H1 G N :=
  AddEquiv.ofBijective ((h1Fst G M N).prod (h1Snd G M N)) (h1Product_bijective G M N)

variable {G M N}

/-- The product equivalence commutes with every compatible-pair pullback,
so it preserves the actual localization maps, not only dimensions. -/
theorem h1ProdAddEquiv_naturality
    {H : Type*} [Monoid H] [TopologicalSpace H]
    {M' N' : Type*} [AddCommGroup M'] [AddCommGroup N']
    [TopologicalSpace M'] [TopologicalSpace N']
    [IsTopologicalAddGroup M'] [IsTopologicalAddGroup N']
    [DistribMulAction H M'] [DistribMulAction H N']
    [ContinuousSMul H M'] [ContinuousSMul H N']
    (φ : H →ₜ* G) (f : M →+ M') (g : N →+ N')
    (hf : Continuous f) (hg : Continuous g)
    (hfe : ∀ h m, f (φ h • m) = h • f m)
    (hge : ∀ h n, g (φ h • n) = h • g n) (x : H1 G (M × N)) :
    h1ProdAddEquiv H M' N'
      (explicitMap1 G (M × N) H (M' × N') φ (f.prodMap g)
        ((hf.comp continuous_fst).prodMk (hg.comp continuous_snd))
        (fun h mn => Prod.ext (hfe h mn.1) (hge h mn.2)) x) =
      (explicitMap1 G M H M' φ f hf hfe (h1ProdAddEquiv G M N x).1,
        explicitMap1 G N H N' φ g hg hge (h1ProdAddEquiv G M N x).2) := by
  induction x using QuotientAddGroup.induction_on with
  | H c => rfl

end Products

section GenuineSelmerProducts

variable (E E' : WeierstrassCurve ℚ)

/-- Local triviality in the point-coefficient product: both point-cohomology
components are in the genuine Shafarevich--Tate groups. -/
def productSha : AddSubgroup
    (H1 (AbsoluteGaloisGroup ℚ) (E.PointCoeff × E'.PointCoeff)) :=
  ((sha E).prod (sha E')).comap
    (h1ProdAddEquiv (AbsoluteGaloisGroup ℚ) E.PointCoeff E'.PointCoeff).toAddMonoidHom

/-- The full Selmer group for the product of the two genuine two-primary
coefficient modules, defined by local triviality of its image in point cohomology. -/
def fullSelmerProduct : AddSubgroup
    (H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E × TwoPowerCoeff E')) :=
  (productSha E E').comap
    (explicitMap1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E × TwoPowerCoeff E')
      (AbsoluteGaloisGroup ℚ) (E.PointCoeff × E'.PointCoeff)
      (ContinuousMonoidHom.id (AbsoluteGaloisGroup ℚ))
      ((twoPowerCoeffIncl E).toAddMonoidHom.prodMap (twoPowerCoeffIncl E').toAddMonoidHom)
      continuous_of_discreteTopology
      (fun σ PP => Prod.ext ((twoPowerCoeffIncl E).map_smul σ PP.1)
        ((twoPowerCoeffIncl E').map_smul σ PP.2)))

/-- The product local conditions are exactly the two original full Selmer
conditions, by naturality of the continuous cohomology projections. -/
theorem mem_fullSelmerProduct
    {c : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E × TwoPowerCoeff E')} :
    c ∈ fullSelmerProduct E E' ↔
      (h1ProdAddEquiv (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (TwoPowerCoeff E') c).1 ∈
        selmerTwoPower E ∧
      (h1ProdAddEquiv (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (TwoPowerCoeff E') c).2 ∈
        selmerTwoPower E' := by
  unfold fullSelmerProduct productSha
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap]
  erw [h1ProdAddEquiv_naturality]
  rfl

/-- An explicit product decomposition of the full Selmer local conditions.
It does not assume finiteness of the Shafarevich--Tate groups. -/
def fullSelmerProductAddEquiv :
    fullSelmerProduct E E' ≃+ selmerTwoPower E × selmerTwoPower E' := by
  let e := h1ProdAddEquiv (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (TwoPowerCoeff E')
  refine
    { toFun := fun c =>
        (⟨(e c).1, ((mem_fullSelmerProduct E E').mp c.2).1⟩,
          ⟨(e c).2, ((mem_fullSelmerProduct E E').mp c.2).2⟩)
      invFun := fun c => ⟨e.symm ((c.1 : H1 _ _), (c.2 : H1 _ _)), ?_⟩
      left_inv := fun c => Subtype.ext (e.symm_apply_apply (c : H1 _ _))
      right_inv := fun c =>
        Prod.ext (Subtype.ext (congrArg Prod.fst (e.apply_symm_apply _)))
          (Subtype.ext (congrArg Prod.snd (e.apply_symm_apply _)))
      map_add' := fun c d =>
        Prod.ext (Subtype.ext (congrArg Prod.fst (e.map_add _ _)))
          (Subtype.ext (congrArg Prod.snd (e.map_add _ _))) }
  apply (mem_fullSelmerProduct E E').mpr
  change (e (e.symm ((c.1 : H1 _ _), (c.2 : H1 _ _)))).1 ∈ selmerTwoPower E ∧
    (e (e.symm ((c.1 : H1 _ _), (c.2 : H1 _ _)))).2 ∈ selmerTwoPower E'
  rw [e.apply_symm_apply]
  exact ⟨c.1.2, c.2.2⟩

/-- Rationalization of the actual product Selmer group gives exactly the
right-hand side of `CentralSelmerComparison`. -/
def fullSelmerProductRatTateEquiv :
    RatTate (fullSelmerProduct E E') ≃ₗ[ℚ_[2]]
      RatTate (selmerTwoPower E) × RatTate (selmerTwoPower E') :=
  (RatTate.congr (fullSelmerProductAddEquiv E E')).trans RatTate.prodEquiv

end GenuineSelmerProducts

section ModelCohomology

variable {R : Type} [CommRing R]

private def homologyOneEquivKer (C : CochainComplex (ModuleCat.{0} R) ℤ)
    (hzero : C.d 0 1 = 0) : C.homology 1 ≃ₗ[R] LinearMap.ker (C.d 1 2).hom := by
  let S := C.sc' 0 1 2
  have hcycles : S.moduleCatToCycles = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (C.d 0 1).hom x = 0
    rw [hzero]
    rfl
  have hrange : LinearMap.range S.moduleCatToCycles = ⊥ := LinearMap.range_eq_bot.mpr hcycles
  exact ((C.homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv.trans
    S.moduleCatHomologyIso.toLinearEquiv).trans (Submodule.quotEquivOfEqBot _ hrange)

/-- The degree-one cohomology of a two-term matrix model is its matrix
kernel. The zero incoming differential is explicit: coordinates in degrees
one and two alone would not imply it. -/
def modelHomologyOneEquiv {m : ℕ} (C : CochainComplex (ModuleCat.{0} R) ℤ)
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (e1 : C.X 1 ≃ₗ[R] (Fin (m + 1) → R))
    (e2 : C.X 2 ≃ₗ[R] (Fin (m + 1) → R))
    (hzero : C.d 0 1 = 0) (hd : ∀ x, e2 ((C.d 1 2).hom x) = D *ᵥ e1 x) :
    C.homology 1 ≃ₗ[R] LinearMap.ker D.mulVecLin := by
  refine (homologyOneEquivKer C hzero).trans
    { toFun := fun x => ⟨e1 x, ?_⟩
      invFun := fun x => ⟨e1.symm x, ?_⟩
      left_inv := fun x => Subtype.ext (e1.symm_apply_apply (x : C.X 1))
      right_inv := fun x => Subtype.ext (e1.apply_symm_apply (x : Fin (m + 1) → R))
      map_add' := fun x y => Subtype.ext (e1.map_add _ _)
      map_smul' := fun c x => Subtype.ext (e1.map_smul c _) }
  · change D *ᵥ e1 (x : C.X 1) = 0
    rw [← hd, x.2, map_zero]
  · apply e2.injective
    rw [hd, e1.apply_symm_apply, map_zero]
    exact x.2

/-- A retained central quasi-isomorphism identifies the matrix kernel with
the first cohomology of the rational Kummer complex. -/
def matrixKerEquivOfQuasiIso {m : ℕ}
    (C K : CochainComplex (ModuleCat.{0} R) ℤ) (i : K ⟶ C) [QuasiIsoAt i 1]
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (e1 : C.X 1 ≃ₗ[R] (Fin (m + 1) → R))
    (e2 : C.X 2 ≃ₗ[R] (Fin (m + 1) → R))
    (hzero : C.d 0 1 = 0) (hd : ∀ x, e2 ((C.d 1 2).hom x) = D *ᵥ e1 x) :
    LinearMap.ker D.mulVecLin ≃ₗ[R] K.homology 1 :=
  (modelHomologyOneEquiv C D e1 e2 hzero hd).symm.trans
    (asIso (HomologicalComplex.homologyMap i 1)).toLinearEquiv.symm

end ModelCohomology

section ScalarChange

variable {A B : Type} [CommRing A] [CommRing B]

/-- Coefficient extension of a cochain complex along a ring homomorphism. -/
abbrev scalarChangedComplex (ρ : A →+* B) (C : CochainComplex (ModuleCat.{0} A) ℤ) :
    CochainComplex (ModuleCat.{0} B) ℤ :=
  ((ModuleCat.extendScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

private def extendedCoordinates {r : ℕ} (ρ : A →+* B) (M : ModuleCat.{0} A)
    (e : M ≃ₗ[A] (Fin r → A)) : (ModuleCat.extendScalars ρ).obj M ≃ₗ[B] (Fin r → B) := by
  letI : Algebra A B := ρ.toAlgebra
  exact (LinearEquiv.baseChange A B M (Fin r → A) e).trans
    (TensorProduct.piScalarRight A B B (Fin r))

set_option backward.isDefEq.respectTransparency false in
private theorem extendedDifferential {r : ℕ} (ρ : A →+* B) (M N : ModuleCat.{0} A)
    (d : M ⟶ N) (D : Matrix (Fin r) (Fin r) A)
    (e1 : M ≃ₗ[A] (Fin r → A)) (e2 : N ≃ₗ[A] (Fin r → A))
    (hd : ∀ x, e2 (d.hom x) = D *ᵥ e1 x) (x : (ModuleCat.extendScalars ρ).obj M) :
    extendedCoordinates ρ N e2 (((ModuleCat.extendScalars ρ).map d).hom x) =
      (D.map ρ).mulVecLin (extendedCoordinates ρ M e1 x) := by
  let : Algebra A B := ρ.toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
    change B at b
    ext j
    change ρ (e2 (d.hom x) j) * b =
      ((D.map ρ) *ᵥ (fun l => ρ (e1 x l) * b)) j
    rw [hd]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- Specializing a two-term matrix model maps its entries through the
coefficient homomorphism and identifies its degree-one cohomology with the
specialized matrix kernel. No flatness assumption or cohomology base-change
assertion is used: this is coefficient change of the actual complex. -/
def specializedModelHomologyOneEquiv {m : ℕ} (ρ : A →+* B)
    (C : CochainComplex (ModuleCat.{0} A) ℤ)
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (e1 : C.X 1 ≃ₗ[A] (Fin (m + 1) → A))
    (e2 : C.X 2 ≃ₗ[A] (Fin (m + 1) → A))
    (hzero : C.d 0 1 = 0) (hd : ∀ x, e2 ((C.d 1 2).hom x) = D *ᵥ e1 x) :
    (scalarChangedComplex ρ C).homology 1 ≃ₗ[B] LinearMap.ker (D.map ρ).mulVecLin := by
  refine modelHomologyOneEquiv (scalarChangedComplex ρ C) (D.map ρ)
    (extendedCoordinates ρ (C.X 1) e1) (extendedCoordinates ρ (C.X 2) e2) ?_ ?_
  · change (ModuleCat.extendScalars ρ).map (C.d 0 1) = 0
    rw [hzero, CategoryTheory.Functor.map_zero]
  · intro x
    exact extendedDifferential ρ (C.X 1) (C.X 2) (C.d 1 2) D e1 e2 hd x

end ScalarChange

section Integration

open ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53

variable {ℓ : ℕ} {k : ℤ} {m : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (C K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ) (i : K ⟶ C) [QuasiIsoAt i 1]
    (e1 : C.X 1 ≃ₗ[ℚ_[2]] (Fin (m + 1) → ℚ_[2]))
    (e2 : C.X 2 ≃ₗ[ℚ_[2]] (Fin (m + 1) → ℚ_[2]))
    (hzero : C.d 0 1 = 0)
    (hd : ∀ x, e2 ((C.d 1 2).hom x) = (Dm.map Rings.rhoT) *ᵥ e1 x)
    {S : Type} [AddCommGroup S]
    (hK : K.homology 1 ≃ₗ[ℚ_[2]] RatTate S)
    (f : S →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f)

/-- The requested comparison from precise cohomological inputs: the central
matrix model, the retained rational Kummer quasi-isomorphism, universal
coefficients for the full Selmer group, and bounded-defect quadratic descent.
None of those arithmetic inputs is asserted for an arbitrary matrix. -/
def centralSelmerComparisonOfKummerModel :
    CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm where
  cmp := (matrixKerEquivOfQuasiIso C K i (Dm.map Rings.rhoT) e1 e2 hzero hd).trans <|
    hK.trans <| (ratTateEquivOfBoundedDefects f hf).trans <|
      fullSelmerProductRatTateEquiv (Ecurve ℓ) (Etw ℓ k)

include C K i e1 e2 hzero hd hK f hf in
/-- The constructor supplies the exact `hcentral` field and both central
dimensions under the original full Selmer corank-one hypothesis. -/
theorem central_dimensions_of_KummerModel (hSel : SelmerCorankOneOverK ℓ k) :
    (Dm.map Rings.rhoT).rank = m ∧
      Module.finrank ℚ_[2] (LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) = 1 ∧
      Module.finrank ℚ_[2]
        ((Fin (m + 1) → ℚ_[2]) ⧸ LinearMap.range (Dm.map Rings.rhoT).mulVecLin) = 1 := by
  let cmp := centralSelmerComparisonOfKummerModel Dm C K i e1 e2 hzero hd hK f hf
  exact ⟨cmp.hcentral hSel.1 hSel.2, cmp.finrank_ker hSel.1 hSel.2,
    cmp.finrank_coker hSel.1 hSel.2⟩

/-- The comparison with the universal-coefficient input expressed as an
actual additive map with bounded defects, instead of an entire equivalence. -/
def centralSelmerComparisonOfUniversalCoefficients {r : ℕ}
    (eK : K.homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    (j : (Fin r → Q2Z2) →+ S) (hj : BoundedDefects j) :
    CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm :=
  centralSelmerComparisonOfKummerModel Dm C K i e1 e2 hzero hd
    (universalCoefficientsRatTateEquiv eK j hj) f hf

end Integration

section SpecializedIntegration

open ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53

/-- The comparison constructor for the integral base-model fields themselves.
Specialization, matrix cohomology, rationalization, and product Selmer local
conditions are all supplied by proved algebra. The remaining inputs are the
retained arithmetic quasi-isomorphism, the universal-coefficient map, and
the bounded-defect quadratic Selmer descent map. -/
def centralSelmerComparisonOfSpecializedModel {ℓ : ℕ} {k : ℤ} {m r : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ)
    (i : K ⟶ scalarChangedComplex Rings.rhoT CU) [QuasiIsoAt i 1]
    (eK : K.homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {S : Type} [AddCommGroup S] (j : (Fin r → Q2Z2) →+ S) (hj : BoundedDefects j)
    (f : S →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f) :
    CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm where
  cmp := (specializedModelHomologyOneEquiv Rings.rhoT CU Dm e1 e2 hzero hd).symm.trans <|
    (asIso (HomologicalComplex.homologyMap i 1)).toLinearEquiv.symm.trans <|
      (universalCoefficientsRatTateEquiv eK j hj).trans <|
        (ratTateEquivOfBoundedDefects f hf).trans <|
          fullSelmerProductRatTateEquiv (Ecurve ℓ) (Etw ℓ k)

variable {ℓ : ℕ} {k : ℤ} {m r : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ)
    (i : K ⟶ scalarChangedComplex Rings.rhoT CU) [QuasiIsoAt i 1]
    (eK : K.homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {S : Type} [AddCommGroup S] (j : (Fin r → Q2Z2) →+ S) (hj : BoundedDefects j)
    (f : S →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f)

include CU e1 e2 hzero hd K i eK j hj f hf in
/-- The existing base-zero `hcentral` field is supplied without alteration
once the specified arithmetic comparison maps and their bounded defects
have been constructed. -/
theorem hcentral_of_specializedModel (hSel : SelmerCorankOneOverK ℓ k) :
    (Dm.map Rings.rhoT).rank = m :=
  hcentral_of_selmer hSel
    (centralSelmerComparisonOfSpecializedModel Dm CU e1 e2 hzero hd K i eK j hj f hf)

end SpecializedIntegration

/-- Coranks alone cannot supply a comparison for an unconstrained matrix:
the identity has zero kernel, even when the full Selmer coranks are one and zero. -/
theorem no_comparison_identity {S₁ S₂ : Type*} [AddCommGroup S₁] [AddCommGroup S₂]
    (h₁ : Z2Corank S₁ 1) (h₂ : Z2Corank S₂ 0) (m : ℕ) :
    ¬ Nonempty (CentralSelmerComparison S₁ S₂
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ZInQ.Manuscript.RC.Rings.LambdaT)) := by
  rintro ⟨cmp⟩
  have h := cmp.hcentral h₁ h₂
  have hmap : (1 : Matrix (Fin (m + 1)) (Fin (m + 1))
      ZInQ.Manuscript.RC.Rings.LambdaT).map ZInQ.Manuscript.RC.Rings.rhoT = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hmap, Matrix.rank_one, Fintype.card_fin] at h
  omega

end ZInQ.Manuscript.RC53Assist.CentralSelmer
