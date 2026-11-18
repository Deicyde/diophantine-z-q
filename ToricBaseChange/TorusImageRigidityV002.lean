import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# A torus maps into the toric part: rigidity for `𝔾_m` and the toric rank inequality

Let `k` be a field and `B` a proper group scheme over `k` (for example an abelian variety).

* `gmHom_proper_point`: every homomorphism `𝔾_m → B`, given in the functor of points
  (`Φ_R : Rˣ →* B(R)`, natural in `k`-algebras `R`), kills every `k`-point. Proof by the valuative
  criterion at the point `0` of `𝔸¹`: with `R = k[Y]_(Y)` and `K = k(Y)`, the `K`-point `Φ(Y)` extends
  to `Q ∈ B(R)` (properness); for `c ∈ kˣ` the scaling `τ_c : Y ↦ cY` of `R` gives the extension
  `Q ∘ τ_c` of `Φ(cY) = Φ(Y)·Φ(c)`, and so does `Q·Φ(c)`; by separatedness they agree; at the closed
  point (`ρ ∘ τ_c = ρ`) this reads `Q(0) = Q(0)·Φ(c)`, so `Φ(c) = 1`. No algebraic closure, no
  splitting field and no tameness is used.
* `torusHom_proper_point`: the same for `𝔾_m^r`.
* `card_torsion_pi`, `rank_le_of_torsion_injective`: over an algebraically closed field `K` with
  `m` invertible, `{t : (Kˣ)^r // t^m = 1}` has `m^r` elements; an injection of these sets for
  `m ≥ 2` gives `r ≤ r'`.
* `toricRank_le_of_torusMap`: a homomorphism `ψ : X → G'` of group schemes over an algebraically
  closed field, a torus `e : 𝔾_m^r → X`, and a semi-abelian identity component `U' ⊆ G'`
  (`π' : U' → B'` with `B'` proper and `ker π' = e'(𝔾_m^{r'})`) give `r ≤ r'`, provided the image of
  the torus lies in `U'` and `ψ ∘ e` has no nontrivial `m`-torsion in its kernel on `K`-points for
  some `m ≥ 2` invertible in `K`. The torus image lands in `ker π'` by `torusHom_proper_point`;
  this is proved, not assumed.

`SpecPt k R` and `SpecPtMap` have literally the bodies of the functor-of-points objects used for
semi-abelian identity components (`Spec R` as a `k`-scheme, and `Spec` of a `k`-algebra map).
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ToricBaseChange

/-! ## §1. Points over `k`-algebras -/

section Points

variable (k : Type) [Field k]

/-- `Spec R` as a `k`-scheme, for a `k`-algebra `R` (its morphisms to `G` are the `R`-points). -/
def SpecPt (R : Type) [CommRing R] [Algebra k R] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))

variable {k}

/-- `Spec S → Spec R` over `k` for a `k`-algebra map `f : R → S`. -/
def SpecPtMap {R S : Type} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    (f : R →ₐ[k] S) : SpecPt k S ⟶ SpecPt k R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (f : R →+* S))) (by
    simp only [SpecPt, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

theorem SpecPtMap_comp {R S T : Type} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    [CommRing T] [Algebra k T] (f : R →ₐ[k] S) (g : S →ₐ[k] T) :
    SpecPtMap (g.comp f) = SpecPtMap g ≫ SpecPtMap f := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem SpecPtMap_id {R : Type} [CommRing R] [Algebra k R] :
    SpecPtMap (AlgHom.id k R) = 𝟙 (SpecPt k R) := by
  ext1
  change Spec.map _ = 𝟙 _
  exact Spec.map_id _

end Points

/-! ## §2. The local ring `R = k[Y]_(Y)` of `𝔸¹` at `0`, its residue map and its scalings -/

section LocalRing

variable {k : Type} [Field k]

/-- The prime `(Y) ⊆ k[Y]`. -/
abbrev P0 (k : Type) [Field k] : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

instance P0.isPrime : (P0 k).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- `K = k(Y)`. -/
abbrev Kl (k : Type) [Field k] : Type := FractionRing (Polynomial k)

theorem P0_le : (P0 k).primeCompl ≤ nonZeroDivisors (Polynomial k) :=
  le_nonZeroDivisors_of_noZeroDivisors (fun h0 => h0 (Ideal.zero_mem _))

/-- `R = k[Y]_(Y) ⊆ K`, a discrete valuation ring. -/
abbrev Rl (k : Type) [Field k] : Type :=
  ↥(Localization.subalgebra.ofField (Kl k) (P0 k).primeCompl P0_le)

instance : IsLocalization.AtPrime (Rl k) (P0 k) :=
  Localization.subalgebra.isLocalization_ofField (Kl k) (P0 k).primeCompl P0_le

instance : IsDiscreteValuationRing (Rl k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k)
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_ne_zero) (Rl k)

/-- The uniformizer `Y ∈ R`. -/
abbrev sR (k : Type) [Field k] : Rl k := algebraMap (Polynomial k) (Rl k) Polynomial.X

theorem not_mem_P0 {y : Polynomial k} (hy : y ∈ (P0 k).primeCompl) : y.eval 0 ≠ 0 := by
  intro h
  apply hy
  show y ∈ P0 k
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, h]

/-- The residue map `ρ : R → k`, `f ↦ f(0)`. -/
def rho (k : Type) [Field k] : Rl k →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := (P0 k).primeCompl) (f := Polynomial.aeval (0 : k)) (fun y => by
    rw [isUnit_iff_ne_zero, Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using not_mem_P0 y.2)

theorem rho_algebraMap (p : Polynomial k) :
    rho k (algebraMap (Polynomial k) (Rl k) p) = p.eval 0 := by
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

/-- `c Y`, for `c ∈ kˣ`. -/
def sT (c : kˣ) : Rl k := algebraMap k (Rl k) (c : k) * sR k

theorem rho_sT (c : kˣ) : rho k (sT c) = 0 := by
  rw [sT, map_mul, rho_s, mul_zero]

/-- **The scaling `Y ↦ cY` at `0`**: `τ_c : R → R`. -/
def tau (c : kˣ) : Rl k →ₐ[k] Rl k :=
  IsLocalization.liftAlgHom (M := (P0 k).primeCompl) (f := Polynomial.aeval (sT c)) (fun y => by
    apply isUnit_of_rho_ne_zero
    rw [← Polynomial.aeval_algHom_apply, rho_sT, Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using not_mem_P0 y.2)

theorem tau_algebraMap (c : kˣ) (p : Polynomial k) :
    tau c (algebraMap (Polynomial k) (Rl k) p) = Polynomial.aeval (sT c) p := by
  rw [tau, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem tau_s (c : kˣ) : tau c (sR k) = sT c := by
  rw [tau_algebraMap, Polynomial.aeval_X]

/-- `ρ ∘ τ_c = ρ`: the scaling fixes the point `0`. -/
theorem rho_comp_tau (c : kˣ) : (rho k).comp (tau c) = rho k := by
  apply IsLocalization.algHom_ext (P0 k).primeCompl
  apply Polynomial.algHom_ext
  change rho k (tau c (algebraMap _ _ Polynomial.X)) = rho k (algebraMap _ _ Polynomial.X)
  rw [tau_algebraMap, Polynomial.aeval_X, rho_sT, rho_algebraMap]
  simp

/-- `τ_{c⁻¹} ∘ τ_c = id`. -/
theorem tau_inv_comp_tau (c : kˣ) : (tau c⁻¹).comp (tau c) = AlgHom.id k (Rl k) := by
  apply IsLocalization.algHom_ext (P0 k).primeCompl
  apply Polynomial.algHom_ext
  change tau c⁻¹ (tau c (algebraMap _ _ Polynomial.X)) = algebraMap _ _ Polynomial.X
  rw [tau_algebraMap, Polynomial.aeval_X, sT, map_mul, AlgHom.commutes, tau_s, sT, ← _root_.mul_assoc,
    ← map_mul, Units.mul_inv, map_one, _root_.one_mul]

theorem tau_injective (c : kˣ) : Function.Injective (tau c) := by
  intro x y h
  have := congrArg (tau c⁻¹) h
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, tau_inv_comp_tau] at this

theorem sR_ne_zero : sR k ≠ 0 := by
  intro h
  have hinj : Function.Injective (algebraMap (Polynomial k) (Rl k)) :=
    IsLocalization.injective (Rl k) P0_le
  exact Polynomial.X_ne_zero (hinj (h.trans (map_zero _).symm))

/-- `j : R → K`. -/
abbrev jR (k : Type) [Field k] : Rl k →ₐ[k] Kl k := IsScalarTower.toAlgHom k (Rl k) (Kl k)

theorem jtau_injective (c : kˣ) : Function.Injective ((jR k).comp (tau c)) :=
  (IsFractionRing.injective (Rl k) (Kl k)).comp (tau_injective c)

/-- `τ_c` on `K`. -/
def tauK (c : kˣ) : Kl k →ₐ[k] Kl k :=
  IsFractionRing.liftAlgHom (g := (jR k).comp (tau c)) (jtau_injective c)

theorem tauK_comp_jR (c : kˣ) : (tauK c).comp (jR k) = (jR k).comp (tau c) := by
  apply AlgHom.ext; intro x
  show tauK c (algebraMap (Rl k) (Kl k) x) = algebraMap (Rl k) (Kl k) (tau c x)
  rw [tauK, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]; rfl

/-- `Y ∈ K`. -/
abbrev yK (k : Type) [Field k] : Kl k := algebraMap (Rl k) (Kl k) (sR k)

theorem yK_ne_zero : yK k ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Rl k) (Kl k))).mpr sR_ne_zero

/-- `Y` as a unit of `K`. -/
def yU (k : Type) [Field k] : (Kl k)ˣ := Units.mk0 (yK k) yK_ne_zero

/-- `τ_c(Y) = cY` in `K`. -/
theorem tauK_yK (c : kˣ) : tauK c (yK k) = algebraMap k (Kl k) (c : k) * yK k := by
  have h1 := congrArg (fun f => f (sR k)) (tauK_comp_jR c)
  simp only [AlgHom.comp_apply] at h1
  change tauK c (jR k (sR k)) = _
  rw [h1, tau_s, sT, map_mul, AlgHom.commutes]
  rfl

end LocalRing

/-! ## §3. The valuative criterion for `R ⊆ K` -/

section Valuative

variable {k : Type} [Field k] (B : Over (Spec (CommRingCat.of k)))

/-- The valuative square of a `K`-point of `B` over `Spec R → Spec k`. -/
def vsq (T : SpecPt k (Kl k) ⟶ B) : ValuativeCommSq B.hom where
  R := Rl k
  K := Kl k
  i₁ := T.left
  i₂ := (SpecPt k (Rl k)).hom
  commSq := ⟨(Over.w T).trans (by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])⟩

/-- Existence of the extension of a `K`-point to an `R`-point (properness). -/
theorem lift_exists [IsProper B.hom] (T : SpecPt k (Kl k) ⟶ B) :
    ∃ Q : SpecPt k (Rl k) ⟶ B, SpecPtMap (jR k) ≫ Q = T := by
  have hE : (ValuativeCriterion.Existence ⊓ @QuasiCompact) B.hom := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨l⟩ := (hE.1 (vsq B T)).exists_lift
  refine ⟨Over.homMk l.l l.fac_right, ?_⟩
  ext1
  exact l.fac_left

/-- Uniqueness of the extension (separatedness). -/
theorem lift_unique [IsSeparated B.hom] (Q Q' : SpecPt k (Rl k) ⟶ B)
    (h : SpecPtMap (jR k) ≫ Q = SpecPtMap (jR k) ≫ Q') : Q = Q' := by
  have hU := IsSeparated.valuativeCriterion B.hom (vsq B (SpecPtMap (jR k) ≫ Q))
  have := hU.elim ⟨Q.left, rfl, Over.w Q⟩ ⟨Q'.left, by rw [h]; rfl, Over.w Q'⟩
  ext1
  exact congrArg CategoryTheory.CommSq.LiftStruct.l this

end Valuative

/-! ## §4. Rigidity: a homomorphism `𝔾_m^r → B` to a proper group scheme kills `k`-points -/

section Rigidity

variable {k : Type} [Field k] (B : Over (Spec (CommRingCat.of k))) [IsProper B.hom] [GrpObj B]

/-- **Rigidity for `𝔾_m`, pointwise**: a homomorphism `𝔾_m → B` to a proper group scheme over a
field `k` (in the functor of points, natural in `k`-algebras) sends every `k`-point to the unit. -/
theorem gmHom_proper_point
    (Φ : ∀ (R : Type) [CommRing R] [Algebra k R], Rˣ →* (SpecPt k R ⟶ B))
    (hnat : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
      (t : Rˣ), Φ S (Units.map (f : R →* S) t) = SpecPtMap f ≫ Φ R t) (c : kˣ) :
    Φ k c = 1 := by
  have hunit : Units.map ((tauK c : Kl k →ₐ[k] Kl k) : Kl k →* Kl k) (yU k) =
      yU k * Units.map ((Algebra.ofId k (Kl k) : k →ₐ[k] Kl k) : k →* Kl k) c := by
    apply Units.ext
    simp only [Units.coe_map, Units.val_mul, MonoidHom.coe_ofClass, yU, Units.val_mk0]
    rw [tauK_yK, Algebra.ofId_apply, mul_comm]
  have hhom : SpecPtMap (tauK c) ≫ Φ (Kl k) (yU k) =
      Φ (Kl k) (yU k) * (SpecPtMap (Algebra.ofId k (Kl k)) ≫ Φ k c) := by
    rw [← hnat, hunit, map_mul, hnat]
  obtain ⟨Q, hQ⟩ := lift_exists B (Φ (Kl k) (yU k))
  have hjo : (jR k).comp (Algebra.ofId k (Rl k)) = Algebra.ofId k (Kl k) := Subsingleton.elim _ _
  have key : SpecPtMap (tau c) ≫ Q = Q * (SpecPtMap (Algebra.ofId k (Rl k)) ≫ Φ k c) := by
    apply lift_unique B
    rw [comp_mul, ← Category.assoc, ← SpecPtMap_comp, ← tauK_comp_jR, SpecPtMap_comp,
      Category.assoc, hQ, ← Category.assoc, ← SpecPtMap_comp, hjo]
    exact hhom
  have hro : (rho k).comp (Algebra.ofId k (Rl k)) = AlgHom.id k k := Subsingleton.elim _ _
  have key2 := congrArg (SpecPtMap (rho k) ≫ ·) key
  simp only [comp_mul, ← Category.assoc, ← SpecPtMap_comp, rho_comp_tau, hro, SpecPtMap_id,
    Category.id_comp] at key2
  exact left_eq_mul.mp key2

/-- **Rigidity for `𝔾_m^r`, pointwise**: a homomorphism `𝔾_m^r → B` to a proper group scheme over a
field `k` sends every `k`-point to the unit. -/
theorem torusHom_proper_point (r : ℕ)
    (Φ : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (SpecPt k R ⟶ B))
    (hnat : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
      (t : Fin r → Rˣ), Φ S (fun i => Units.map (f : R →* S) (t i)) = SpecPtMap f ≫ Φ R t)
    (t : Fin r → kˣ) : Φ k t = 1 := by
  have h1 : ∀ i : Fin r, Φ k (Pi.mulSingle i (t i)) = 1 := by
    intro i
    exact gmHom_proper_point B (fun R _ _ => (Φ R).comp (MonoidHom.mulSingle (fun _ => Rˣ) i))
      (fun R S _ _ _ _ f u => by
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply]
        rw [← hnat]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.mulSingle_eq_of_ne hj]) (t i)
  have hall : ∀ s : Finset (Fin r), Φ k (∏ i ∈ s, Pi.mulSingle i (t i)) = 1 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, map_one]
    · intro a s ha ih
      rw [Finset.prod_insert ha, map_mul, h1 a, ih, _root_.mul_one]
  have h2 := hall Finset.univ
  rwa [Finset.univ_prod_mulSingle] at h2

end Rigidity

/-! ## §5. Counting `m`-torsion of `(Kˣ)^r` -/

section Counting

variable (K : Type) [Field K] [IsAlgClosed K]

/-- `#{t ∈ (Kˣ)^r : t^m = 1} = m^r` for `m` invertible in the algebraically closed field `K`. -/
theorem card_torsion_pi (m : ℕ) [NeZero (m : K)] (r : ℕ) :
    Nat.card {t : Fin r → Kˣ // t ^ m = 1} = m ^ r := by
  have e : {t : Fin r → Kˣ // t ^ m = 1} ≃ (Fin r → rootsOfUnity m K) :=
    { toFun := fun t i => ⟨t.1 i, (mem_rootsOfUnity m (t.1 i)).mpr (by simpa using congrFun t.2 i)⟩
      invFun := fun s => ⟨fun i => (s i).1, funext fun i => by
        simpa using (mem_rootsOfUnity m _).mp (s i).2⟩
      left_inv := fun t => rfl
      right_inv := fun s => rfl }
  have : NeZero m := NeZero.of_neZero_natCast K
  rw [Nat.card_congr e, Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_fin]

/-- **Rank from torsion**: an injection of `m`-torsion sets (`m ≥ 2` invertible in `K`) from
`(Kˣ)^r` to `(Kˣ)^{r'}` gives `r ≤ r'`. -/
theorem rank_le_of_torsion_injective (m : ℕ) (hm : 2 ≤ m) [NeZero (m : K)] (r r' : ℕ)
    (θ : {t : Fin r → Kˣ // t ^ m = 1} → {t : Fin r' → Kˣ // t ^ m = 1})
    (hθ : Function.Injective θ) : r ≤ r' := by
  haveI : Finite {t : Fin r' → Kˣ // t ^ m = 1} := Nat.finite_of_card_ne_zero (by
    rw [card_torsion_pi K m r']; exact pow_ne_zero _ (by omega))
  have h1 := Nat.card_le_card_of_injective θ hθ
  rw [card_torsion_pi K m r, card_torsion_pi K m r'] at h1
  exact (Nat.pow_le_pow_iff_right (by omega)).mp h1

end Counting

/-! ## §6. The toric rank inequality for a homomorphism into a semi-abelian identity component -/

section Assembly

variable {K : Type} [Field K] [IsAlgClosed K]

/-- **Toric rank cannot drop along a homomorphism that is injective on the prime-to-`p` torsion of
a torus.** Over an algebraically closed field `K`: `X` a group scheme with a torus
`e : 𝔾_m^r → X` (functor of points, natural); `G'` a group scheme with an open subgroup `U'`
(`inc`), a homomorphism `π : U' → B'` to a proper group scheme with kernel `e'(𝔾_m^{r'})`
(`e'` injective); `ψ : X → G'` a homomorphism. If the image of the torus lies in `U'` (`hfac`) and
`ψ ∘ e` kills no nontrivial `m`-torsion `K`-point (`hker`, some `m ≥ 2` invertible in `K`), then
`r ≤ r'`. That the torus image lies in `ker π` is proved here (rigidity, §4). -/
theorem toricRank_le_of_torusMap
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
    (hfac : ∀ (R : Type) [CommRing R] [Algebra K R] (t : Fin r → Rˣ),
      ∃ y : SpecPt K R ⟶ U', y ≫ inc = e R t ≫ ψ)
    (m : ℕ) (hm : 2 ≤ m) [NeZero (m : K)]
    (hker : ∀ t : Fin r → Kˣ, t ^ m = 1 → e K t ≫ ψ = 1 → t = 1) :
    r ≤ r' := by
  haveI : Mono inc := Over.mono_of_mono_left inc
  -- the factorization through `U'`, as a natural homomorphism
  let y : ∀ (R : Type) [CommRing R] [Algebra K R], (Fin r → Rˣ) → (SpecPt K R ⟶ U') :=
    fun R _ _ t => (hfac R t).choose
  have hy : ∀ (R : Type) [CommRing R] [Algebra K R] (t : Fin r → Rˣ), y R t ≫ inc = e R t ≫ ψ :=
    fun R _ _ t => (hfac R t).choose_spec
  have hy_one : ∀ (R : Type) [CommRing R] [Algebra K R], y R 1 = 1 := by
    intro R _ _
    apply (cancel_mono inc).mp
    rw [hy, map_one, one_comp, one_comp]
  have hy_mul : ∀ (R : Type) [CommRing R] [Algebra K R] (s t : Fin r → Rˣ),
      y R (s * t) = y R s * y R t := by
    intro R _ _ s t
    apply (cancel_mono inc).mp
    rw [hy, map_mul, mul_comp, mul_comp, hy, hy]
  have hy_nat : ∀ (R S : Type) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
      (f : R →ₐ[K] S) (t : Fin r → Rˣ),
      y S (fun i => Units.map (f : R →* S) (t i)) = SpecPtMap f ≫ y R t := by
    intro R S _ _ _ _ f t
    apply (cancel_mono inc).mp
    rw [hy, Category.assoc, hy, hnat, Category.assoc]
  let yH : ∀ (R : Type) [CommRing R] [Algebra K R], (Fin r → Rˣ) →* (SpecPt K R ⟶ U') :=
    fun R _ _ => { toFun := y R, map_one' := hy_one R, map_mul' := hy_mul R }
  -- the torus image in `B'` is trivial on `K`-points (rigidity)
  let Φ : ∀ (R : Type) [CommRing R] [Algebra K R], (Fin r → Rˣ) →* (SpecPt K R ⟶ B') :=
    fun R _ _ => { toFun := fun t => y R t ≫ π
                   map_one' := by rw [hy_one, one_comp]
                   map_mul' := fun s t => by rw [hy_mul, mul_comp] }
  have hΦnat : ∀ (R S : Type) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
      (f : R →ₐ[K] S) (t : Fin r → Rˣ),
      Φ S (fun i => Units.map (f : R →* S) (t i)) = SpecPtMap f ≫ Φ R t := by
    intro R S _ _ _ _ f t
    change y S _ ≫ π = SpecPtMap f ≫ y R t ≫ π
    rw [hy_nat, Category.assoc]
  have hπ : ∀ t : Fin r → Kˣ, y K t ≫ π = 1 := fun t =>
    torusHom_proper_point B' r Φ hΦnat t
  have hrange : ∀ t : Fin r → Kˣ, ∃ t' : Fin r' → Kˣ, e' K t' = y K t := fun t =>
    (he'_ker K (y K t)).mp (hπ t)
  -- the induced map on `m`-torsion
  let θ : {t : Fin r → Kˣ // t ^ m = 1} → {t : Fin r' → Kˣ // t ^ m = 1} := fun t =>
    ⟨(hrange t.1).choose, by
      apply he'_inj K
      rw [map_pow, (hrange t.1).choose_spec, map_one]
      change (yH K t.1) ^ m = 1
      rw [← map_pow, t.2, map_one]⟩
  have hθ : Function.Injective θ := by
    intro s t hst
    have h1 : y K s.1 = y K t.1 := by
      rw [← (hrange s.1).choose_spec, ← (hrange t.1).choose_spec]
      exact congrArg (fun z => e' K z.1) hst
    have h2 : yH K (s.1 * t.1⁻¹) = 1 := by
      rw [map_mul, map_inv]
      change y K s.1 * (y K t.1)⁻¹ = 1
      rw [h1, mul_inv_cancel]
    have h3 : e K (s.1 * t.1⁻¹) ≫ ψ = 1 := by
      rw [← hy]
      change yH K (s.1 * t.1⁻¹) ≫ inc = 1
      rw [h2, one_comp]
    have h4 : (s.1 * t.1⁻¹) ^ m = 1 := by
      rw [mul_pow, inv_pow, s.2, t.2, inv_one, _root_.mul_one]
    have h5 := hker _ h4 h3
    exact Subtype.ext (mul_inv_eq_one.mp h5)
  exact rank_le_of_torsion_injective K m hm r r' θ hθ

end Assembly

end ToricBaseChange
