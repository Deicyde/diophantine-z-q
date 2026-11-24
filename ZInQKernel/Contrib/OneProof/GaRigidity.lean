import ZInQKernel.Contrib.OneProof.H.TailY

/-!
# ga-rigidity: rigidity for `𝔾_a` over an algebraically closed field

Over an algebraically closed field `k`, in the functor-of-points language of `ZInQ.HeightSplit` (`algPt k R = Spec R`
as a `k`-scheme; a homomorphism `𝔾_a → G` of group schemes is a morphism `g : Spec k[X] → G` with
`g(x + y) = g(x) g(y)`, `IsGaHom`):

1. **Step (1)** `gaHom_torus_trivial` (and `unit_additive_eq_one`): every homomorphism `𝔾_a → 𝔾_m^r` is trivial
   (`k[X]ˣ = kˣ`; holds over any field).
2. **Step (2)** `gaHom_proper_trivial`, `gaHom_abVar_trivial`: every homomorphism `𝔾_a → B` to a proper group scheme
   (an abelian variety `PkgI3.AbVar k`) is trivial. The proof is the valuative criterion at the point `∞` of `ℙ¹`:
   with `R = k[s]_(s)`, `s = 1/x`, the `K`-point `g(1/s)` of `B` extends to `Q : Spec R → B` (properness); the
   translation `τ_c : s ↦ s/(1 + cs)` of `R` (`x ↦ x + c`) shows that `Q ∘ τ_c` and `Q · g(c)` both extend
   `g(1/s + c)`, so they agree (separatedness); at the closed point (`τ_c ≡ id`) this gives `g(c) = 1`
   (`gaHom_proper_point`, any field). Morphisms out of `𝔸¹` are determined by `k`-points (`ext_of_points`).
3. **Step (3)** `gaHom_trivial_of_semiAbelian`, `noGaSubgroup_of_semiAbelian`: if the identity component of `G` is an
   extension of an abelian variety by a split torus (`HasSemiAbelianIdentityComponent`, the kernel's semistability),
   every homomorphism `𝔾_a → G` is trivial, so `G` has no subgroup scheme isomorphic to `𝔾_a` (`NoGaSubgroup`). A
   homomorphism `𝔾_a → G` lands in every open subgroup (`gaHom_factors_open`: the `c` with `g(c) ∈ U` form a cofinite
   subgroup of the infinite `k`, and `𝔸¹` is Jacobson).

No `sorry`, no `axiom`; only Mathlib and the kernel definitions (`ZInQ.HeightSplit.algPt`, `PkgI3.AbVar`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit

namespace GaRigidity

variable {k : Type} [Field k]

/-! ## §0. `𝔾_a` and its homomorphisms, in the functor of points -/

/-- `k[X] → k[X, Y]`, `X ↦ X + Y`: the comultiplication of `𝔾_a = Spec k[X]`. -/
def addMap (k : Type) [Field k] : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k :=
  Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.X 1)

/-- `X ↦ X` (first projection `𝔾_a × 𝔾_a → 𝔾_a`). -/
def pr1 (k : Type) [Field k] : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k := Polynomial.aeval (MvPolynomial.X 0)

/-- `X ↦ Y` (second projection `𝔾_a × 𝔾_a → 𝔾_a`). -/
def pr2 (k : Type) [Field k] : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k := Polynomial.aeval (MvPolynomial.X 1)

/-- A morphism `g : 𝔾_a = Spec k[X] → G` of `k`-schemes is a **homomorphism of group schemes**: `g(x + y) = g(x) g(y)`,
i.e. `g ∘ add = (g ∘ pr₁) · (g ∘ pr₂)` as morphisms `Spec k[X, Y] → G` (product in the group `Hom(Spec k[X,Y], G)`). -/
def IsGaHom (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (g : algPt k (Polynomial k) ⟶ G) : Prop :=
  algPtMap (addMap k) ≫ g = (algPtMap (pr1 k) ≫ g) * (algPtMap (pr2 k) ≫ g)

/-- **`G` contains no subgroup scheme isomorphic to `𝔾_a`**: no homomorphism `𝔾_a → G` of `k`-group schemes is a closed
immersion. (The condition of SGA 7 I Exp. IX Déf. 3.4 / 2.1.5 on the identity component of the geometric special fibre,
per the queue11 reviewer verdict; locators UNVERIFIED.) -/
def NoGaSubgroup (G : Over (Spec (CommRingCat.of k))) [GrpObj G] : Prop :=
  ∀ g : algPt k (Polynomial k) ⟶ G, IsGaHom G g → IsClosedImmersion g.left → False

/-! ## §1. `algPt` calculus -/

theorem algPtMap_comp {R S T : Type} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] [CommRing T]
    [Algebra k T] (f : R →ₐ[k] S) (g : S →ₐ[k] T) :
    algPtMap (g.comp f) = algPtMap g ≫ algPtMap f := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem algPtMap_id {R : Type} [CommRing R] [Algebra k R] : algPtMap (AlgHom.id k R) = 𝟙 (algPt k R) := by
  ext1
  change Spec.map _ = 𝟙 _
  exact Spec.map_id _

theorem algPtMap_left {R S : Type} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S) :
    (algPtMap f).left = Spec.map (CommRingCat.ofHom (f : R →+* S)) := rfl

instance (R : Type) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] : LocallyOfFiniteType (algPt k R).hom :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

/-! ## §2. Step (1): every homomorphism `𝔾_a → 𝔾_m^r` is trivial -/

/-- **Step (1), ring form**: a unit `u ∈ k[X]ˣ = 𝔾_m(k[X])` with `u(X + Y) = u(X) u(Y)` (a homomorphism `𝔾_a → 𝔾_m`,
by Yoneda) is `1`. Over a field `k[X]ˣ = kˣ`, and `c = c²` with `c` a unit forces `c = 1`. -/
theorem unit_additive_eq_one (u : (Polynomial k)ˣ)
    (h : Units.map (addMap k : Polynomial k →* MvPolynomial (Fin 2) k) u =
      Units.map (pr1 k : Polynomial k →* MvPolynomial (Fin 2) k) u *
        Units.map (pr2 k : Polynomial k →* MvPolynomial (Fin 2) k) u) : u = 1 := by
  obtain ⟨r, hr, hC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have h' := congrArg Units.val h
  simp only [Units.coe_map, Units.val_mul, MonoidHom.coe_ofClass] at h'
  rw [← hC] at h'
  simp only [addMap, pr1, pr2, Polynomial.aeval_C] at h'
  rw [← map_mul] at h'
  have hrr : r = r * r := (algebraMap k (MvPolynomial (Fin 2) k)).injective h'
  have hr1 : r = 1 := by
    have h0 : r ≠ 0 := hr.ne_zero
    have := mul_left_cancel₀ h0 (hrr.symm.trans (mul_one r).symm)
    exact this
  apply Units.ext
  rw [← hC, hr1, Polynomial.C_1, Units.val_one]

/-- **Step (1), group-scheme form**: let `e` identify `𝔾_m^r` with a subgroup functor of `U` (injective, multiplicative,
natural in the `k`-algebra, as in `HasSemiAbelianIdentityComponent`). A homomorphism `𝔾_a → U` of the form `e(t)` is
trivial. -/
theorem gaHom_torus_trivial (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U))
    (hinj : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hnat : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (t : Fin r → (Polynomial k)ˣ) (h : IsGaHom U (e _ t)) : e _ t = 1 := by
  unfold IsGaHom at h
  rw [← hnat, ← hnat, ← hnat, ← map_mul] at h
  have ht := hinj _ h
  have : t = 1 := by
    funext i
    exact unit_additive_eq_one (t i) (congrFun ht i)
  rw [this, map_one]

/-! ## §3. The local ring of `ℙ¹` at `∞`: `R = k[s]_(s)` with `s = 1/x`, its translations and its residue map -/

/-- The prime `(s) ⊆ k[s]`. -/
abbrev P0 (k : Type) [Field k] : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

instance P0.isPrime : (P0 k).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- `K = k(s) = Frac k[s]`. -/
abbrev Kl (k : Type) [Field k] : Type := FractionRing (Polynomial k)

theorem P0_le : (P0 k).primeCompl ≤ nonZeroDivisors (Polynomial k) :=
  le_nonZeroDivisors_of_noZeroDivisors (fun h0 => h0 (Ideal.zero_mem _))

/-- `R = k[s]_(s) ⊆ K`, a discrete valuation ring (the local ring of `ℙ¹` at `∞`, with `s = 1/x`). -/
abbrev Rl (k : Type) [Field k] : Type :=
  ↥(Localization.subalgebra.ofField (Kl k) (P0 k).primeCompl P0_le)

instance : IsLocalization.AtPrime (Rl k) (P0 k) :=
  Localization.subalgebra.isLocalization_ofField (Kl k) (P0 k).primeCompl P0_le

instance : IsDiscreteValuationRing (Rl k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k)
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_ne_zero) (Rl k)

example : IsFractionRing (Rl k) (Kl k) := inferInstance
example : IsScalarTower k (Rl k) (Kl k) := inferInstance
example : IsScalarTower k (Polynomial k) (Rl k) := inferInstance

/-- The uniformizer `s ∈ R`. -/
abbrev sR (k : Type) [Field k] : Rl k := algebraMap (Polynomial k) (Rl k) Polynomial.X

theorem not_mem_P0 {y : Polynomial k} (hy : y ∈ (P0 k).primeCompl) : y.eval 0 ≠ 0 := by
  intro h
  apply hy
  show y ∈ P0 k
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, h]

/-- The residue map `ρ : R → k`, `f ↦ f(0)` (value at `∞`). -/
def rho (k : Type) [Field k] : Rl k →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := (P0 k).primeCompl) (f := Polynomial.aeval (0 : k)) (fun y => by
    rw [isUnit_iff_ne_zero, Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using not_mem_P0 y.2)

theorem rho_algebraMap (p : Polynomial k) : rho k (algebraMap (Polynomial k) (Rl k) p) = p.eval 0 := by
  rw [rho, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]

theorem rho_s : rho k (sR k) = 0 := by
  rw [rho_algebraMap]; simp

theorem rho_surjective : Function.Surjective (rho k) := fun c => ⟨algebraMap k _ c, by simp⟩

/-- An element of the local ring `R` with nonzero residue is a unit. -/
theorem isUnit_of_rho_ne_zero {x : Rl k} (hx : rho k x ≠ 0) : IsUnit x := by
  by_contra hu
  have hm : x ∈ IsLocalRing.maximalIdeal (Rl k) := (IsLocalRing.mem_maximalIdeal x).mpr hu
  rw [← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (rho k) rho_surjective)] at hm
  exact hx (RingHom.mem_ker.mp hm)

/-- `1 + c s` is a unit of `R`. -/
theorem isUnit_u (c : k) : IsUnit (1 + algebraMap k (Rl k) c * sR k) :=
  isUnit_of_rho_ne_zero (by simp [rho_s])

/-- `s/(1 + c s)`. -/
def sT (c : k) : Rl k := sR k * ↑(isUnit_u c).unit⁻¹

theorem rho_sT (c : k) : rho k (sT c) = 0 := by
  rw [sT, map_mul, rho_s, zero_mul]

/-- **The translation `x ↦ x + c` at `∞`**: `τ_c : R → R`, `s ↦ s/(1 + c s)`. -/
def tau (c : k) : Rl k →ₐ[k] Rl k :=
  IsLocalization.liftAlgHom (M := (P0 k).primeCompl) (f := Polynomial.aeval (sT c)) (fun y => by
    apply isUnit_of_rho_ne_zero
    rw [← Polynomial.aeval_algHom_apply, rho_sT, Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using not_mem_P0 y.2)

theorem tau_algebraMap (c : k) (p : Polynomial k) :
    tau c (algebraMap (Polynomial k) (Rl k) p) = Polynomial.aeval (sT c) p := by
  rw [tau, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem tau_s (c : k) : tau c (sR k) = sT c := by
  rw [tau_algebraMap, Polynomial.aeval_X]

/-- `ρ ∘ τ_c = ρ`: the translation fixes the point at `∞`. -/
theorem rho_comp_tau (c : k) : (rho k).comp (tau c) = rho k := by
  apply IsLocalization.algHom_ext (P0 k).primeCompl
  apply Polynomial.algHom_ext
  change rho k (tau c (algebraMap _ _ Polynomial.X)) = rho k (algebraMap _ _ Polynomial.X)
  rw [tau_algebraMap, Polynomial.aeval_X, rho_sT, rho_algebraMap]
  simp

/-- `τ_{-c} ∘ τ_c = id`. -/
theorem tau_neg_comp_tau (c : k) : (tau (-c)).comp (tau c) = AlgHom.id k (Rl k) := by
  apply IsLocalization.algHom_ext (P0 k).primeCompl
  apply Polynomial.algHom_ext
  change tau (-c) (tau c (algebraMap _ _ Polynomial.X)) = algebraMap _ _ Polynomial.X
  rw [tau_algebraMap, Polynomial.aeval_X, sT, map_mul, tau_s]
  set a : Rl k := ↑(isUnit_u c).unit⁻¹
  set b : Rl k := ↑(isUnit_u (-c)).unit⁻¹
  have ha : a * (1 + algebraMap k (Rl k) c * sR k) = 1 := IsUnit.val_inv_mul (isUnit_u c)
  have hb : b * (1 + algebraMap k (Rl k) (-c) * sR k) = 1 := IsUnit.val_inv_mul (isUnit_u (-c))
  have h1 := congrArg (tau (-c)) ha
  rw [map_mul, map_one, map_add, map_one, map_mul, AlgHom.commutes, tau_s, sT] at h1
  change sR k * b * tau (-c) a = sR k
  rw [map_neg] at hb
  linear_combination (sR k * tau (-c) a) * hb + sR k * h1

theorem tau_injective (c : k) : Function.Injective (tau c) := by
  intro x y h
  have := congrArg (tau (-c)) h
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, tau_neg_comp_tau] at this

theorem sR_ne_zero : sR k ≠ 0 := by
  intro h
  have hinj : Function.Injective (algebraMap (Polynomial k) (Rl k)) :=
    IsLocalization.injective (Rl k) P0_le
  exact Polynomial.X_ne_zero (hinj (h.trans (map_zero _).symm))

/-- `j : R → K`. -/
abbrev jR (k : Type) [Field k] : Rl k →ₐ[k] Kl k := IsScalarTower.toAlgHom k (Rl k) (Kl k)

/-- `τ_c` on `K`. -/
theorem jtau_injective (c : k) : Function.Injective ((jR k).comp (tau c)) :=
  (IsFractionRing.injective (Rl k) (Kl k)).comp (tau_injective c)

def tauK (c : k) : Kl k →ₐ[k] Kl k :=
  IsFractionRing.liftAlgHom (g := (jR k).comp (tau c)) (jtau_injective c)

theorem tauK_comp_jR (c : k) : (tauK c).comp (jR k) = (jR k).comp (tau c) := by
  apply AlgHom.ext; intro x
  show tauK c (algebraMap (Rl k) (Kl k) x) = algebraMap (Rl k) (Kl k) (tau c x)
  rw [tauK, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]; rfl

/-- `x = 1/s ∈ K`. -/
abbrev xK (k : Type) [Field k] : Kl k := (algebraMap (Rl k) (Kl k) (sR k))⁻¹

/-- `τ_c(1/s) = 1/s + c`. -/
theorem tauK_xK (c : k) : tauK c (xK k) = xK k + algebraMap k (Kl k) c := by
  have h1 : tauK c (algebraMap (Rl k) (Kl k) (sR k)) = algebraMap (Rl k) (Kl k) (sT c) := by
    have := congrArg (fun f => f (sR k)) (tauK_comp_jR c)
    simpa [tau_s] using this
  rw [map_inv₀, h1, sT, RingHom.map_mul]
  have hs : algebraMap (Rl k) (Kl k) (sR k) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Rl k) (Kl k))).mpr sR_ne_zero
  have ha : (↑(isUnit_u c).unit⁻¹ : Rl k) * (1 + algebraMap k (Rl k) c * sR k) = 1 := IsUnit.val_inv_mul (isUnit_u c)
  have ha' := congrArg (algebraMap (Rl k) (Kl k)) ha
  rw [RingHom.map_mul, RingHom.map_one, RingHom.map_add, RingHom.map_one, RingHom.map_mul,
    ← IsScalarTower.algebraMap_apply] at ha'
  set A := algebraMap (Rl k) (Kl k) ↑(isUnit_u c).unit⁻¹
  set S := algebraMap (Rl k) (Kl k) (sR k)
  have hA : A = (1 + algebraMap k (Kl k) c * S)⁻¹ := eq_inv_of_mul_eq_one_left ha'
  have hu : 1 + algebraMap k (Kl k) c * S ≠ 0 := by
    intro h0; rw [h0, mul_zero] at ha'; exact zero_ne_one ha'
  rw [hA, xK]
  field_simp
  ring


/-! ## §4. Step (2), the valuative argument: a homomorphism `𝔾_a → B` to a proper group scheme kills `k`-points

For `g : 𝔾_a → B` and the `K`-point `x = 1/s` of `𝔾_a`, the `K`-point `g(x)` of the proper `B` extends to an
`R`-point `Q` (valuative criterion, existence). The translation `τ_c` of `R` (`x ↦ x + c`) gives the extension
`Q ∘ τ_c` of `g(x + c) = g(x) g(c)`; so does `Q · g(c)`; by uniqueness (separatedness) they agree. At the closed point
(`ρ ∘ τ_c = ρ`) this reads `Q(∞) = Q(∞) g(c)`, so `g(c) = 1`. -/

section Valuative

variable (B : Over (Spec (CommRingCat.of k))) [IsProper B.hom]

/-- The valuative square of a `K`-point of `B` over `Spec R → Spec k`. -/
def vsq (T : algPt k (Kl k) ⟶ B) : ValuativeCommSq B.hom where
  R := Rl k
  K := Kl k
  i₁ := T.left
  i₂ := (algPt k (Rl k)).hom
  commSq := ⟨(Over.w T).trans (by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])⟩

/-- Existence of the extension of a `K`-point to an `R`-point (properness). -/
theorem lift_exists (T : algPt k (Kl k) ⟶ B) : ∃ Q : algPt k (Rl k) ⟶ B, algPtMap (jR k) ≫ Q = T := by
  have hE : (ValuativeCriterion.Existence ⊓ @QuasiCompact) B.hom := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨l⟩ := (hE.1 (vsq B T)).exists_lift
  refine ⟨Over.homMk l.l l.fac_right, ?_⟩
  ext1
  exact l.fac_left

/-- Uniqueness of the extension (separatedness). -/
theorem lift_unique (Q Q' : algPt k (Rl k) ⟶ B) (h : algPtMap (jR k) ≫ Q = algPtMap (jR k) ≫ Q') : Q = Q' := by
  have hU := IsSeparated.valuativeCriterion B.hom (vsq B (algPtMap (jR k) ≫ Q))
  have := hU.elim ⟨Q.left, rfl, Over.w Q⟩ ⟨Q'.left, by rw [h]; rfl, Over.w Q'⟩
  ext1
  exact congrArg CategoryTheory.CommSq.LiftStruct.l this

variable [GrpObj B]

/-- **Step (2), pointwise**: a homomorphism `g : 𝔾_a → B` to a proper group scheme over a field `k` sends every
`k`-point `c` of `𝔾_a` to the unit. -/
theorem gaHom_proper_point (g : algPt k (Polynomial k) ⟶ B) (h : IsGaHom B g) (c : k) :
    algPtMap (Polynomial.aeval c) ≫ g = 1 := by
  set xc := algPtMap (Polynomial.aeval c) ≫ g
  let P : Polynomial k →ₐ[k] Kl k := Polynomial.aeval (xK k)
  let φ : MvPolynomial (Fin 2) k →ₐ[k] Kl k := MvPolynomial.aeval ![xK k, algebraMap k (Kl k) c]
  have hadd : φ.comp (addMap k) = (tauK c).comp P := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, addMap, Polynomial.aeval_X, map_add, MvPolynomial.aeval_X, φ, P]
    rw [tauK_xK]
    simp
  have hp1 : φ.comp (pr1 k) = P := by
    apply Polynomial.algHom_ext
    simp [pr1, φ, P]
  have hp2 : φ.comp (pr2 k) = (Algebra.ofId k (Kl k)).comp (Polynomial.aeval c) := by
    apply Polynomial.algHom_ext
    simp [pr2, φ]
  have hhom : algPtMap ((tauK c).comp P) ≫ g =
      (algPtMap P ≫ g) * (algPtMap (Algebra.ofId k (Kl k)) ≫ xc) := by
    have := congrArg (algPtMap φ ≫ ·) h
    simp only [comp_mul, ← Category.assoc, ← algPtMap_comp, hadd, hp1, hp2] at this
    rw [this, algPtMap_comp, Category.assoc]
  obtain ⟨Q, hQ⟩ := lift_exists B (algPtMap P ≫ g)
  have hjo : (jR k).comp (Algebra.ofId k (Rl k)) = Algebra.ofId k (Kl k) := Subsingleton.elim _ _
  have key : algPtMap (tau c) ≫ Q = Q * (algPtMap (Algebra.ofId k (Rl k)) ≫ xc) := by
    apply lift_unique B
    rw [comp_mul, ← Category.assoc, ← algPtMap_comp, ← tauK_comp_jR, algPtMap_comp, Category.assoc, hQ,
      ← Category.assoc, ← algPtMap_comp, ← Category.assoc (algPtMap (jR k)), ← algPtMap_comp, hjo]
    exact hhom
  have hro : (rho k).comp (Algebra.ofId k (Rl k)) = AlgHom.id k k := Subsingleton.elim _ _
  have key2 := congrArg (algPtMap (rho k) ≫ ·) key
  simp only [comp_mul, ← Category.assoc, ← algPtMap_comp, rho_comp_tau, hro, algPtMap_id, Category.id_comp] at key2
  exact left_eq_mul.mp key2

end Valuative


/-! ## §5. Morphisms out of `𝔸¹` are determined by their values at `k`-points (`k` algebraically closed) -/

section Ext

variable [IsAlgClosed k]

/-- Every closed point of `𝔸¹ = Spec k[X]` is the image of a `k`-point `X ↦ c`. -/
theorem closedPoint_eq_ev (x : (algPt k (Polynomial k)).left) (hx : IsClosed {x}) :
    ∃ c : k, ∀ a, (algPtMap (Polynomial.aeval c)).left a = x := by
  let p := pointOfClosedPoint (algPt k (Polynomial k)).hom x hx
  have hp : p ≫ (algPt k (Polynomial k)).hom = 𝟙 _ := pointOfClosedPoint_comp _ x hx
  let φ := Spec.preimage p
  have hφ : Spec.map φ = p := Spec.map_preimage p
  have hφ1 : CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_id]
    exact hp
  refine ⟨φ.hom Polynomial.X, fun a => ?_⟩
  have hφe : φ = CommRingCat.ofHom ((Polynomial.aeval (φ.hom Polynomial.X) : Polynomial k →ₐ[k] k) :
      Polynomial k →+* k) := by
    ext1
    apply Polynomial.ringHom_ext
    · intro r
      have := congrArg (fun f => f.hom r) hφ1
      simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, CommRingCat.hom_ofHom,
        RingHom.id_apply] at this
      change φ.hom (Polynomial.C r) = Polynomial.aeval _ (Polynomial.C r)
      rw [Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply, ← Polynomial.algebraMap_eq]
      exact this
    · simp
  rw [algPtMap_left, ← hφe, hφ]
  exact pointOfClosedPoint_apply _ x hx a

/-- **Extensionality from `k`-points**: two morphisms `𝔸¹ → Y` to a separated `k`-scheme of finite type that agree at
every `k`-point are equal. -/
theorem ext_of_points {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (f f' : algPt k (Polynomial k) ⟶ Y)
    (h : ∀ c : k, algPtMap (Polynomial.aeval c) ≫ f = algPtMap (Polynomial.aeval c) ≫ f') : f = f' := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : IsReduced (algPt k (Polynomial k)).left := by
    change IsReduced (Spec (CommRingCat.of (Polynomial k))); infer_instance
  ext1
  refine ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_)
    ((Over.w f).trans (Over.w f').symm)
  obtain ⟨c, hc⟩ := closedPoint_eq_ev x hx
  let a : (algPt k k).left := (algPt k (Polynomial k)).hom x
  rw [← hc a]
  change (algPtMap (Polynomial.aeval c) ≫ f).left a = (algPtMap (Polynomial.aeval c) ≫ f').left a
  rw [h c]

end Ext

/-! ## §6. Step (2): every homomorphism `𝔾_a → B` to a proper group scheme (an abelian variety) is trivial -/

/-- **Step (2)**: over an algebraically closed field, every homomorphism of group schemes from `𝔾_a` to a proper group
scheme is trivial. -/
theorem gaHom_proper_trivial [IsAlgClosed k] (B : Over (Spec (CommRingCat.of k))) [IsProper B.hom] [GrpObj B]
    (g : algPt k (Polynomial k) ⟶ B) (h : IsGaHom B g) : g = 1 :=
  ext_of_points g 1 fun c => by rw [gaHom_proper_point B g h c, comp_one]

/-- **Step (2) for abelian varieties**: every homomorphism `𝔾_a → A` to an abelian variety over an algebraically closed
field is trivial. -/
theorem gaHom_abVar_trivial [IsAlgClosed k] (A : PkgI3.AbVar k) (g : algPt k (Polynomial k) ⟶ A.X)
    (h : IsGaHom A.X g) : g = 1 :=
  gaHom_proper_trivial A.X g h


/-! ## §7. A homomorphism `𝔾_a → G` lands in every open subgroup `U ⊆ G` (`k` algebraically closed)

`V = g⁻¹(U)` is open and contains `0`, so it contains every `k`-point `c` off the finite zero set of some `h ≠ 0`. The
`c` with `g(c) ∈ U` form a subgroup of `k` (`U` is a subgroup); a cofinite subgroup of the infinite `k` is `k`. So `V`
contains every closed point, hence (Jacobson) is everything. -/

section OpenSubgroup

/-- Factorization through an open immersion of `k`-schemes, from containment of the image. -/
theorem factor_openImm {W G U : Over (Spec (CommRingCat.of k))} (inc : U ⟶ G) [IsOpenImmersion inc.left]
    (y : W ⟶ G) (hy : Set.range y.left ⊆ Set.range inc.left) : ∃ y' : W ⟶ U, y' ≫ inc = y := by
  refine ⟨Over.homMk (IsOpenImmersion.lift inc.left y.left hy) ?_, ?_⟩
  · rw [← Over.w inc, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w y]
  · ext1
    exact IsOpenImmersion.lift_fac _ _ _

theorem subsingleton_specField (a b : (algPt k k).left) : a = b := by
  change PrimeSpectrum k at a b
  exact Subsingleton.elim a b

theorem ev_mem_basicOpen (c : k) (a : (algPt k k).left) (h : Polynomial k) :
    (algPtMap (Polynomial.aeval c)).left a ∈ (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum (Polynomial k))) ↔
      h.eval c ≠ 0 := by
  let a' : PrimeSpectrum k := a
  change PrimeSpectrum.comap ((Polynomial.aeval c : Polynomial k →ₐ[k] k) : Polynomial k →+* k) a' ∈
    PrimeSpectrum.basicOpen h ↔ _
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime a'.asIdeal,
    Ideal.mem_comap, Ideal.mem_bot]
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- `g(a + b) = g(a) g(b)` on `k`-points. -/
theorem gaHom_add {G : Over (Spec (CommRingCat.of k))} [GrpObj G] (g : algPt k (Polynomial k) ⟶ G)
    (h : IsGaHom G g) (a b : k) :
    algPtMap (Polynomial.aeval (a + b)) ≫ g =
      (algPtMap (Polynomial.aeval a) ≫ g) * (algPtMap (Polynomial.aeval b) ≫ g) := by
  let φ : MvPolynomial (Fin 2) k →ₐ[k] k := MvPolynomial.aeval ![a, b]
  have hadd : φ.comp (addMap k) = Polynomial.aeval (a + b) := by
    apply Polynomial.algHom_ext; simp [addMap, φ]
  have hp1 : φ.comp (pr1 k) = Polynomial.aeval a := by
    apply Polynomial.algHom_ext; simp [pr1, φ]
  have hp2 : φ.comp (pr2 k) = Polynomial.aeval b := by
    apply Polynomial.algHom_ext; simp [pr2, φ]
  have := congrArg (algPtMap φ ≫ ·) h
  simpa only [comp_mul, ← Category.assoc, ← algPtMap_comp, hadd, hp1, hp2] using this

/-- **A homomorphism `𝔾_a → G` factors through every open subgroup `U ⊆ G`.** -/
theorem gaHom_factors_open {G U : Over (Spec (CommRingCat.of k))} [GrpObj G] [GrpObj U] (inc : U ⟶ G)
    [IsOpenImmersion inc.left] [IsMonHom inc] (g : algPt k (Polynomial k) ⟶ G) (h : IsGaHom G g) :
    ∃ g' : algPt k (Polynomial k) ⟶ U, g' ≫ inc = g := by
  -- `k`-points in `U`
  let InU : k → Prop := fun c => ∃ y : algPt k k ⟶ U, y ≫ inc = algPtMap (Polynomial.aeval c) ≫ g
  have hsub : ∀ c b, InU b → InU (b - c) → InU c := by
    rintro c b ⟨y1, hy1⟩ ⟨y2, hy2⟩
    refine ⟨y1 * y2⁻¹, ?_⟩
    have hb := gaHom_add g h c (b - c)
    rw [add_sub_cancel] at hb
    rw [mul_comp, GrpObj.inv_comp, hy1, hy2, hb, mul_inv_cancel_right]
  let V : Set (algPt k (Polynomial k)).left := g.left ⁻¹' Set.range inc.left
  have hVopen : IsOpen V := inc.left.isOpenEmbedding.isOpen_range.preimage g.left.continuous
  have hInU : ∀ c, (∃ a, (algPtMap (Polynomial.aeval c)).left a ∈ V) → InU c := by
    rintro c ⟨a, ha⟩
    refine factor_openImm inc _ ?_
    rintro _ ⟨b, rfl⟩
    rw [subsingleton_specField b a]
    exact ha
  have hV : ∀ c, InU c → ∀ a, (algPtMap (Polynomial.aeval c)).left a ∈ V := by
    rintro c ⟨y, hy⟩ a
    refine ⟨y.left a, ?_⟩
    change (y ≫ inc).left a = (algPtMap (Polynomial.aeval c) ≫ g).left a
    rw [hy]
  -- `0 ∈ U`
  have h0 : InU 0 := by
    have h00 := gaHom_add g h 0 0
    rw [add_zero] at h00
    have h1 : algPtMap (Polynomial.aeval (0 : k)) ≫ g = 1 := left_eq_mul.mp h00
    exact ⟨1, by rw [one_comp, h1]⟩
  obtain ⟨a0⟩ : Nonempty (algPt k k).left := by
    change Nonempty (PrimeSpectrum k); infer_instance
  -- a basic open around `0` inside `V`
  obtain ⟨_, ⟨f, rfl⟩, hf0, hfV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (hV 0 h0 a0) hVopen
  have hf0' : f.eval 0 ≠ 0 := (ev_mem_basicOpen 0 a0 f).mp hf0
  have hfne : f ≠ 0 := by rintro rfl; simp at hf0'
  have hgood : ∀ c, f.eval c ≠ 0 → InU c := fun c hc =>
    hInU c ⟨a0, hfV ((ev_mem_basicOpen c a0 f).mpr hc)⟩
  -- every `k`-point lies in `U`
  have hall : ∀ c, InU c := by
    intro c
    have hfin : ({b | f.IsRoot b} ∪ {b | f.IsRoot (b - c)}).Finite := by
      refine (Polynomial.finite_setOf_isRoot hfne).union ?_
      have : {b | f.IsRoot (b - c)} = (fun x => x + c) '' {b | f.IsRoot b} := by
        ext b
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · intro hb; exact ⟨b - c, hb, sub_add_cancel b c⟩
        · rintro ⟨x, hx, rfl⟩; simpa using hx
      rw [this]; exact (Polynomial.finite_setOf_isRoot hfne).image _
    obtain ⟨b, hb⟩ := hfin.exists_notMem
    simp only [Set.mem_union, Set.mem_setOf_eq, Polynomial.IsRoot.def, not_or] at hb
    exact hsub c b (hgood b hb.1) (hgood (b - c) hb.2)
  -- hence `V` is everything
  have hJ : JacobsonSpace (algPt k (Polynomial k)).left :=
    LocallyOfFiniteType.jacobsonSpace (algPt k (Polynomial k)).hom
  have hVc : Vᶜ = ∅ := by
    have hcl : IsClosed Vᶜ := hVopen.isClosed_compl
    have hemp : Vᶜ ∩ closedPoints _ = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx hxc
      obtain ⟨c, hc⟩ := closedPoint_eq_ev x hxc
      exact hx (hc a0 ▸ hV c (hall c) a0)
    rw [← hcl.closure_eq, ← JacobsonSpace.closure_inter_closedPoints_eq_closure hcl.isLocallyClosed, hemp,
      closure_empty]
  refine factor_openImm inc g ?_
  rintro _ ⟨x, rfl⟩
  have : x ∈ V := by
    by_contra hx
    have : x ∈ Vᶜ := hx
    rw [hVc] at this
    exact this
  exact this

end OpenSubgroup


/-! ## §8. Step (3): a semi-abelian identity component contains no `𝔾_a` -/

section SemiAbelian

variable [IsAlgClosed k]

/-- **Step (3), homomorphism form**: if the identity component of `G` is an extension of an abelian variety by a split
torus (`HasSemiAbelianIdentityComponent`), every homomorphism `𝔾_a → G` is trivial. Proof: it factors through the open
subgroup `U` (§7); its image in the abelian variety `B` is trivial (Step (2)), so it lands in `ker(U → B) = 𝔾_m^r`, where
it is trivial (Step (1)). -/
theorem gaHom_trivial_of_semiAbelian (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    (hG : HasSemiAbelianIdentityComponent G) (g : algPt k (Polynomial k) ⟶ G) (h : IsGaHom G g) : g = 1 := by
  obtain ⟨U, iU, inc, hopen, hmon, -, B, π, hπ, -, -, r, e, hinj, hker, hnat⟩ := hG
  have : IsOpenImmersion inc.left := hopen
  obtain ⟨g', hg'⟩ := gaHom_factors_open inc g h
  have hmono : Mono inc := Over.mono_of_mono_left inc
  have h' : IsGaHom U g' := by
    unfold IsGaHom
    apply (cancel_mono inc).mp
    rw [mul_comp, Category.assoc, Category.assoc, Category.assoc, hg']
    exact h
  have hπg : g' ≫ π = 1 := by
    apply gaHom_abVar_trivial B
    unfold IsGaHom
    rw [← Category.assoc, h', mul_comp, Category.assoc, Category.assoc]
  obtain ⟨t, ht⟩ := (hker _ g').mp hπg
  rw [← ht] at h'
  rw [← hg', ← ht, gaHom_torus_trivial U r e hinj hnat t h', one_comp]

/-- **Step (3)**: if the identity component of `G` (over an algebraically closed field) is an extension of an abelian
variety by a split torus, `G` contains no subgroup scheme isomorphic to `𝔾_a`. -/
theorem noGaSubgroup_of_semiAbelian (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    (hG : HasSemiAbelianIdentityComponent G) : NoGaSubgroup G := by
  intro g h hci
  have h1 := gaHom_trivial_of_semiAbelian G hG g h
  have hm : Mono g.left := inferInstance
  have e0 : (algPtMap (Polynomial.aeval (0 : k))).left ≫ g.left =
      (algPtMap (Polynomial.aeval (1 : k))).left ≫ g.left := by
    rw [← Over.comp_left, ← Over.comp_left, h1, comp_one, comp_one]
  have e1' := (cancel_mono g.left).mp e0
  have e1 : Spec.map (CommRingCat.ofHom ((Polynomial.aeval (0 : k) : Polynomial k →ₐ[k] k) : Polynomial k →+* k)) =
      Spec.map (CommRingCat.ofHom ((Polynomial.aeval (1 : k) : Polynomial k →ₐ[k] k) : Polynomial k →+* k)) := e1'
  rw [Spec.map_inj] at e1
  have e2 := congrArg (fun φ => φ.hom Polynomial.X) e1
  simp at e2

end SemiAbelian

end GaRigidity
