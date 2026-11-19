import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.InnerLimit
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.NonVacuity
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericWiring
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchAdjunction
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.TameComplex

/-!
# Inner-limit local switching objects

The coefficient-stage limit is taken before the characteristic-zero fibre.
The sources are the retained inner-limit lemma, the derivative-condition lemma,
and the height-one switching argument in the manuscript, lines 4391–4451,
4834–4907, and 4976–5135. Finite tame coordinates are those of (4.4).
-/

set_option maxHeartbeats 500000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InnerLimit

open CategoryTheory Filter Topology Matrix Module
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.SelmerComplex
open scoped PowerSeries.WithPiTopology

/-- The rank-two coefficient coordinates. -/
abbrev Vec2 (R : Type) := Fin 2 → R

/-- Finite and singular coordinates, in this order. -/
abbrev Coords (R : Type) := Vec2 R × Vec2 R

section Completed

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R]

/-- The linear coordinate limit on lifted finite-coefficient sequences. -/
def coordLimit (U : Ultrafilter ℕ) : (ℕ → Coords R) →ₗ[R] Coords R where
  toFun x := (ulimVec U (fun i => (x i).1), ulimVec U (fun i => (x i).2))
  map_add' x y := by
    apply Prod.ext
    · exact ulimVec_add U (fun i => (x i).1) (fun i => (y i).1)
    · exact ulimVec_add U (fun i => (x i).2) (fun i => (y i).2)
  map_smul' r x := by
    apply Prod.ext <;> funext a
    · change ulim U (fun i => r * (x i).1 a) = r * ulim U (fun i => (x i).1 a)
      rw [ulim_mul, ulim_const]
    · change ulim U (fun i => r * (x i).2 a) = r * ulim U (fun i => (x i).2 a)
      rw [ulim_mul, ulim_const]

/-- Constant coordinate lifts have the prescribed limit. -/
theorem coordLimit_const (U : Ultrafilter ℕ) (x : Coords R) :
    coordLimit U (fun _ => x) = x := by
  apply Prod.ext <;> funext a <;> exact ulim_const U _

/-- Every limiting coordinate tuple is represented by a lifted sequence. -/
theorem coordLimit_surjective (U : Ultrafilter ℕ) : Function.Surjective (coordLimit (R := R) U) :=
  fun x => ⟨fun _ => x, coordLimit_const U x⟩

/-- The separated completed coordinate product; its kernel kills infinitesimal sequences. -/
abbrev CompletedH1 (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] (U : Ultrafilter ℕ) :=
  (ℕ → Coords R) ⧸ (coordLimit (R := R) U).ker

/-- The completed local coordinate product is a rank-four module over the coefficient ring. -/
def completedEquiv (U : Ultrafilter ℕ) : CompletedH1 R U ≃ₗ[R] Coords R :=
  LinearMap.quotKerEquivOfSurjective (coordLimit (R := R) U)
    (coordLimit_surjective (R := R) U)

/-- The equivalence is induced by the coordinate limit, not by a choice of representatives. -/
theorem completedEquiv_mk (U : Ultrafilter ℕ) (x : ℕ → Coords R) :
    completedEquiv (R := R) U (Submodule.Quotient.mk x) = coordLimit U x := rfl

/-- Kernel membership means vanishing at every retained coefficient precision. -/
theorem coordLimit_eq_zero_iff (I : ℕ → Ideal R) (hI : IdealsTendToZero I)
    (hopen : ∀ n, IsOpen (I n : Set R)) (U : Ultrafilter ℕ) (x : ℕ → Coords R) :
    coordLimit U x = 0 ↔ ∀ n, ∀ᶠ i in (U : Filter ℕ),
      (∀ a, (x i).1 a ∈ I n) ∧ (∀ a, (x i).2 a ∈ I n) := by
  constructor
  · intro hx n
    have hf : ∀ a, ∀ᶠ i in (U : Filter ℕ), (x i).1 a ∈ I n := by
      intro a
      have ha : ulim U (fun i => (x i).1 a) = 0 := congrFun (congrArg Prod.fst hx) a
      simpa only [sub_zero] using
        (ulim_eq_iff_forall_eventually_sub_mem hI hopen U (fun i => (x i).1 a) 0).mp ha n
    have hs : ∀ a, ∀ᶠ i in (U : Filter ℕ), (x i).2 a ∈ I n := by
      intro a
      have ha : ulim U (fun i => (x i).2 a) = 0 := congrFun (congrArg Prod.snd hx) a
      simpa only [sub_zero] using
        (ulim_eq_iff_forall_eventually_sub_mem hI hopen U (fun i => (x i).2 a) 0).mp ha n
    exact (Filter.eventually_all.mpr hf).and (Filter.eventually_all.mpr hs)
  · intro hx
    apply Prod.ext <;> funext a
    · change ulim U (fun i => (x i).1 a) = 0
      apply (ulim_eq_iff_forall_eventually_sub_mem hI hopen U _ 0).mpr
      intro n
      exact (hx n).mono fun i hi => by simpa only [sub_zero] using hi.1 a
    · change ulim U (fun i => (x i).2 a) = 0
      apply (ulim_eq_iff_forall_eventually_sub_mem hI hopen U _ 0).mpr
      intro n
      exact (hx n).mono fun i hi => by simpa only [sub_zero] using hi.2 a

/-- Changing coefficient-stage lifts does not change the completed local class. -/
theorem completed_mk_eq_of_stage_congruence (I : ℕ → Ideal R) (hI : IdealsTendToZero I)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) {x y : ℕ → Coords R}
    (h : ∀ᶠ i in (U : Filter ℕ),
      (∀ a, (x i).1 a - (y i).1 a ∈ I i) ∧ (∀ a, (x i).2 a - (y i).2 a ∈ I i)) :
    (Submodule.Quotient.mk x : CompletedH1 R U) = Submodule.Quotient.mk y := by
  apply (completedEquiv (R := R) U).injective
  rw [completedEquiv_mk, completedEquiv_mk]
  exact Prod.ext
    (ulimVec_eq_of_sub_mem hI hU (h.mono fun _ hi => hi.1))
    (ulimVec_eq_of_sub_mem hI hU (h.mono fun _ hi => hi.2))

/-- The limiting tuple recovers the retained tuple at every fixed precision. -/
theorem coordLimit_precision (I : ℕ → Ideal R) (hopen : ∀ n, IsOpen (I n : Set R))
    (U : Ultrafilter ℕ) (x : ℕ → Coords R) (n : ℕ) :
    ∀ᶠ i in (U : Filter ℕ),
      (∀ a, (x i).1 a - (coordLimit U x).1 a ∈ I n) ∧
      (∀ a, (x i).2 a - (coordLimit U x).2 a ∈ I n) := by
  exact (Filter.eventually_all.mpr fun a => eventually_sub_ulim_mem (hopen n) U _).and
    (Filter.eventually_all.mpr fun a => eventually_sub_ulim_mem (hopen n) U _)

end Completed

section Axes

variable {R : Type} [CommRing R]

/-- The finite axis over the integral coefficient ring. -/
def finiteAxis (R : Type) [CommRing R] : Submodule R (Coords R) :=
  (⊤ : Submodule R (Vec2 R)).prod ⊥

/-- The singular axis over the integral coefficient ring. -/
def singularAxis (R : Type) [CommRing R] : Submodule R (Coords R) :=
  (⊥ : Submodule R (Vec2 R)).prod ⊤

theorem mem_finiteAxis {x : Coords R} : x ∈ finiteAxis R ↔ x.2 = 0 := by
  simp [finiteAxis, Submodule.mem_prod]

theorem mem_singularAxis {x : Coords R} : x ∈ singularAxis R ↔ x.1 = 0 := by
  simp [singularAxis, Submodule.mem_prod]

/-- The axes have zero intersection, over the integral ring as well as over a field. -/
theorem axes_inf : finiteAxis R ⊓ singularAxis R = ⊥ := by
  ext x
  simp only [Submodule.mem_inf, mem_finiteAxis, mem_singularAxis, Submodule.mem_bot]
  exact ⟨fun h => Prod.ext h.2 h.1, fun h => by rw [h]; exact ⟨rfl, rfl⟩⟩

/-- The two axes span the entire limiting local coordinate module. -/
theorem axes_sup : finiteAxis R ⊔ singularAxis R = ⊤ := by
  apply top_unique
  intro x _
  have hf : (x.1, 0) ∈ finiteAxis R := mem_finiteAxis.mpr rfl
  have hs : (0, x.2) ∈ singularAxis R := mem_singularAxis.mpr rfl
  have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
  rw [hx]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hf) (Submodule.mem_sup_right hs)

/-- The finite plane is a free rank-two coordinate module. -/
def finiteAxisEquiv : finiteAxis R ≃ₗ[R] Vec2 R where
  toFun x := x.1.1
  invFun x := ⟨(x, 0), mem_finiteAxis.mpr rfl⟩
  left_inv x := Subtype.ext (Prod.ext rfl (mem_finiteAxis.mp x.2).symm)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The singular plane is a free rank-two coordinate module. -/
def singularAxisEquiv : singularAxis R ≃ₗ[R] Vec2 R where
  toFun x := x.1.2
  invFun x := ⟨(0, x), mem_singularAxis.mpr rfl⟩
  left_inv x := Subtype.ext (Prod.ext (mem_singularAxis.mp x.2).symm rfl)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Axes

section Derivative

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R]

/-- Retained local matrices. Arithmetic prime selection and cochain comparison are separate inputs. -/
structure DerivativeMatrices (I : ℕ → Ideal R) (U : Ultrafilter ℕ) where
  ell : ℕ → R
  ellInv : ℕ → R
  phi : ℕ → Matrix (Fin 2) (Fin 2) R
  rationalFrob : ℕ → Matrix (Fin 2) (Fin 2) R
  J : Matrix (Fin 2) (Fin 2) R
  ell_congr : ∀ᶠ i in (U : Filter ℕ), ell i + 1 ∈ I i
  inv_congr : ∀ᶠ i in (U : Filter ℕ), ell i * ellInv i - 1 ∈ I i
  phi_congr : ∀ᶠ i in (U : Filter ℕ), ∀ a b, (phi i - 1) a b ∈ I i
  rational_congr : ∀ᶠ i in (U : Filter ℕ), ∀ a b, (rationalFrob i - J) a b ∈ I i
  J_square : J * J = 1

variable {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite) (D : DerivativeMatrices I U)

include hI hU

/-- The rational residue characteristic tends to minus one in the retained coefficient topology. -/
theorem ell_limit : ulim U D.ell = -1 := by
  rw [← ulim_const U (-1 : R)]
  exact ulim_eq_ulim_of_sub_mem hI hU (D.ell_congr.mono fun i hi => by simpa using hi)

/-- The squared residue size equals one only after taking the coefficient-stage limit. -/
theorem residueSize_limit : ulim U (fun i => D.ell i ^ 2) = 1 := by
  simp only [pow_two, ulim_mul, ell_limit hI hU D, neg_one_mul, neg_neg]

/-- Retained integral inverses preserve the negative sign on tame inertia. -/
theorem ellInv_limit : ulim U D.ellInv = -1 := by
  have h : ulim U (fun i => D.ell i * D.ellInv i) = 1 := by
    rw [← ulim_const U (1 : R)]
    exact ulim_eq_ulim_of_sub_mem hI hU D.inv_congr
  rw [ulim_mul, ell_limit hI hU D, neg_one_mul] at h
  simpa using congrArg (fun x : R => -x) h

/-- The square Frobenius acts trivially on the limiting coefficient module. -/
theorem phi_limit : ulimMat U D.phi = 1 := by
  rw [← ulimMat_const U (1 : Matrix (Fin 2) (Fin 2) R)]
  exact ulimMat_eq_of_sub_mem hI hU D.phi_congr

/-- Rational Frobenius has the retained conjugation matrix as its exact limit. -/
theorem rationalFrob_limit : ulimMat U D.rationalFrob = D.J := by
  rw [← ulimMat_const U D.J]
  exact ulimMat_eq_of_sub_mem hI hU D.rational_congr

/-- Tame pullback contributes minus one, so its limiting coordinate action is minus J. -/
theorem singularAction_limit :
    ulimMat U (fun i => D.ellInv i • D.rationalFrob i) = -D.J := by
  ext a b
  change ulim U (fun i => D.ellInv i * D.rationalFrob i a b) = -D.J a b
  rw [ulim_mul, ellInv_limit hI hU D]
  have hj := congrFun (congrFun (rationalFrob_limit hI hU D) a) b
  change ulim U (fun i => D.rationalFrob i a b) = D.J a b at hj
  rw [hj, neg_one_mul]

end Derivative

section CompletedPlanes

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R]

/-- The finite switch plane in the completed coordinate product. -/
def completedFinite (U : Ultrafilter ℕ) : Submodule R (CompletedH1 R U) :=
  (finiteAxis R).comap (completedEquiv (R := R) U).toLinearMap

/-- The singular switch plane in the completed coordinate product. -/
def completedSingular (U : Ultrafilter ℕ) : Submodule R (CompletedH1 R U) :=
  (singularAxis R).comap (completedEquiv (R := R) U).toLinearMap

/-- Transport by the actual coordinate limit identifies the finite plane with its axis. -/
theorem completedFinite_map (U : Ultrafilter ℕ) :
    (completedFinite (R := R) U).map (completedEquiv (R := R) U).toLinearMap = finiteAxis R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨(completedEquiv (R := R) U).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
    change completedEquiv (R := R) U ((completedEquiv (R := R) U).symm y) ∈ finiteAxis R
    simpa using hy

/-- Transport by the actual coordinate limit identifies the singular plane with its axis. -/
theorem completedSingular_map (U : Ultrafilter ℕ) :
    (completedSingular (R := R) U).map (completedEquiv (R := R) U).toLinearMap = singularAxis R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨(completedEquiv (R := R) U).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
    change completedEquiv (R := R) U ((completedEquiv (R := R) U).symm y) ∈ singularAxis R
    simpa using hy

/-- A finite-coordinate sequence determines a class in the finite switch plane. -/
theorem completed_mk_finite (U : Ultrafilter ℕ) (f : ℕ → Vec2 R) :
    (Submodule.Quotient.mk (fun i => (f i, 0)) : CompletedH1 R U) ∈ completedFinite (R := R) U := by
  change completedEquiv (R := R) U (Submodule.Quotient.mk (fun i => (f i, 0))) ∈ finiteAxis R
  rw [completedEquiv_mk, mem_finiteAxis]
  exact ulimVec_zero U

/-- A singular-coordinate sequence determines a class in the singular switch plane. -/
theorem completed_mk_singular (U : Ultrafilter ℕ) (s : ℕ → Vec2 R) :
    (Submodule.Quotient.mk (fun i => (0, s i)) : CompletedH1 R U) ∈ completedSingular (R := R) U := by
  change completedEquiv (R := R) U (Submodule.Quotient.mk (fun i => (0, s i))) ∈ singularAxis R
  rw [completedEquiv_mk, mem_singularAxis]
  exact ulimVec_zero U

end CompletedPlanes

section ComplexLimit

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R]

/-- Finite free coefficient-stage complexes after the ranks have been fixed on a large set. -/
structure ComplexStages (I : ℕ → Ideal R) (U : Ultrafilter ℕ) where
  rank : ℤ → ℕ
  low : ℤ
  high : ℤ
  bounded : ∀ n, n < low ∨ high < n → rank n = 0
  d : ∀ _i a b, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) R
  square : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c),
    ∀ᶠ i in (U : Filter ℕ), ∀ x y, (d i b c hbc * d i a b hab) x y ∈ I i

variable {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)

include hI hU

/-- Every limiting consecutive differential product vanishes over the integral ring. -/
theorem differential_product_limit (C : ComplexStages I U) (a b c : ℤ)
    (hab : a + 1 = b) (hbc : b + 1 = c) :
    ulimMat U (fun i => C.d i b c hbc) * ulimMat U (fun i => C.d i a b hab) = 0 := by
  rw [← ulimMat_mul]
  exact ulimMat_eq_zero_of_mem hI hU (C.square a b c hab hbc)

/-- The genuine cochain complex of limiting differential matrices over the coefficient ring. -/
def limitComplex (C : ComplexStages I U) : GCx R where
  X n := ModuleCat.of R (Fin (C.rank n) → R)
  d a b hab := Matrix.toLin' (ulimMat U (fun i => C.d i a b hab))
  d_d a b c hab hbc x := by
    change Matrix.toLin' (ulimMat U (fun i => C.d i b c hbc))
      (Matrix.toLin' (ulimMat U (fun i => C.d i a b hab)) x) = 0
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, differential_product_limit hI hU C a b c hab hbc]
    simp

/-- A retained finite-coefficient map with a commutation identity at the same precision. -/
structure MapStages (C D : ComplexStages I U) where
  f : ∀ _i a b, a = b → Matrix (Fin (D.rank b)) (Fin (C.rank a)) R
  comm : ∀ a a' b b' (hab : a = b) (ha : a + 1 = a') (hb : b + 1 = b') (ha'b' : a' = b'),
    ∀ᶠ i in (U : Filter ℕ), ∀ x y,
      (f i a' b' ha'b' * C.d i a a' ha - D.d i b b' hb * f i a b hab) x y ∈ I i

/-- Taking the same inner limit preserves a retained chain map, not just its cohomology ranks. -/
def limitMap {C D : ComplexStages I U} (F : MapStages C D) :
    GHom (limitComplex hI hU C) (limitComplex hI hU D) where
  f a b hab := Matrix.toLin' (ulimMat U (fun i => F.f i a b hab))
  comm a a' b b' hab ha hb ha'b' x := by
    change (Fin (C.rank a) → R) at x
    have he : ulimMat U (fun i => F.f i a' b' ha'b') * ulimMat U (fun i => C.d i a a' ha) =
        ulimMat U (fun i => D.d i b b' hb) * ulimMat U (fun i => F.f i a b hab) := by
      rw [← ulimMat_mul, ← ulimMat_mul]
      exact ulimMat_eq_of_sub_mem hI hU (F.comm a a' b b' hab ha hb ha'b')
    change Matrix.toLin' (ulimMat U (fun i => F.f i a' b' ha'b'))
      (Matrix.toLin' (ulimMat U (fun i => C.d i a a' ha)) x) =
        Matrix.toLin' (ulimMat U (fun i => D.d i b b' hb))
          (Matrix.toLin' (ulimMat U (fun i => F.f i a b hab)) x)
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, he, Matrix.toLin'_mul, LinearMap.comp_apply]

variable {k : Type} [Field k]

/-- The field complex is obtained by mapping the integral limiting matrices, in that order. -/
def specializeComplex (ρ : R →+* k) (C : ComplexStages I U) : GCx k where
  X n := ModuleCat.of k (Fin (C.rank n) → k)
  d a b hab := Matrix.toLin' ((ulimMat U (fun i => C.d i a b hab)).map ρ)
  d_d a b c hab hbc x := by
    have he : (ulimMat U (fun i => C.d i b c hbc)).map ρ *
        (ulimMat U (fun i => C.d i a b hab)).map ρ = 0 := by
      rw [← Matrix.map_mul, differential_product_limit hI hU C a b c hab hbc]
      ext x y
      exact map_zero ρ
    change Matrix.toLin' ((ulimMat U (fun i => C.d i b c hbc)).map ρ)
      (Matrix.toLin' ((ulimMat U (fun i => C.d i a b hab)).map ρ) x) = 0
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, he]
    simp

/-- The inner-limit fibre cohomology is the homology of the specialized complex. -/
abbrev innerH1 (ρ : R →+* k) (C : ComplexStages I U) :=
  (specializeComplex hI hU ρ C).toCC.homology 1

end ComplexLimit

section SplitLocal

variable {R : Type} [CommRing R]

/-- The full limit local terms retain both degree zero and degree two. -/
def splitLocalTerms (R : Type) [CommRing R] : ℤ → ModuleCat R
  | .ofNat 0 => ModuleCat.of R (Vec2 R)
  | .ofNat 1 => ModuleCat.of R (Coords R)
  | .ofNat 2 => ModuleCat.of R (Vec2 R)
  | _ => ModuleCat.of R PUnit

/-- The split limit local complex; its zero differentials are justified by the retained limits. -/
def splitLocalComplex (R : Type) [CommRing R] : GCx R where
  X := splitLocalTerms R
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- All differentials in the split limit local complex vanish. -/
theorem splitLocalComplex_d_zero (a b : ℤ) : (splitLocalComplex R).toCC.d a b = 0 := by
  dsimp [GCx.toCC, splitLocalComplex]
  split_ifs <;> rfl

/-- Its actual degree-one homology is the direct sum of the finite and singular planes. -/
def splitLocalH1Equiv (R : Type) [CommRing R] :
    (splitLocalComplex R).toCC.homology 1 ≃ₗ[R] Coords R :=
  (((splitLocalComplex R).toCC.isoHomologyπ 0 1 (by simp) (splitLocalComplex_d_zero 0 1)).symm ≪≫
    (splitLocalComplex R).toCC.iCyclesIso 1 2 (by simp) (splitLocalComplex_d_zero 1 2)).toLinearEquiv

end SplitLocal

section LimitLocalOperators

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}

/-- Frobenius minus one on the limiting finite coordinates. -/
def innerFiniteOp (D : DerivativeMatrices I U) : Module.End R (Vec2 R) :=
  Matrix.toLin' (ulimMat U D.phi) - LinearMap.id

/-- Frobenius minus the limiting residue size on the singular coordinates. -/
def innerSingularOp (D : DerivativeMatrices I U) : Module.End R (Vec2 R) :=
  Matrix.toLin' (ulimMat U D.phi) - ulim U (fun i => D.ell i ^ 2) • LinearMap.id

variable (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)

include hI hU

/-- The finite-coordinate boundary vanishes in the inner limit. -/
theorem innerFiniteOp_zero (D : DerivativeMatrices I U) : innerFiniteOp D = 0 := by
  rw [innerFiniteOp, phi_limit hI hU D, Matrix.toLin'_one, sub_self]

/-- The singular-coordinate differential vanishes in the inner limit. -/
theorem innerSingularOp_zero (D : DerivativeMatrices I U) : innerSingularOp D = 0 := by
  rw [innerSingularOp, phi_limit hI hU D, residueSize_limit hI hU D,
    Matrix.toLin'_one, one_smul, sub_self]

/-- The coker/kernel coordinates of the retained limit, not of a fixed arithmetic fibre. -/
abbrev InnerCokerKer (D : DerivativeMatrices I U) :=
  (Vec2 R ⧸ LinearMap.range (innerFiniteOp D)) × LinearMap.ker (innerSingularOp D)

/-- Both limiting summands have full rank two. -/
def innerCokerKerEquiv (D : DerivativeMatrices I U) : InnerCokerKer D ≃ₗ[R] Coords R :=
  ((LinearMap.range (innerFiniteOp D)).quotEquivOfEqBot
    (by rw [innerFiniteOp_zero hI hU D, LinearMap.range_zero])).prodCongr
    ((LinearEquiv.ofEq (LinearMap.ker (innerSingularOp D)) ⊤
      (by rw [innerSingularOp_zero hI hU D, LinearMap.ker_zero])).trans Submodule.topEquiv)

/-- The coker/kernel limit is identified with actual homology of the split local complex. -/
def innerLocalHomologyEquiv (D : DerivativeMatrices I U) :
    InnerCokerKer D ≃ₗ[R] (splitLocalComplex R).toCC.homology 1 :=
  (innerCokerKerEquiv hI hU D).trans (splitLocalH1Equiv R).symm

/-- The completed coordinate product and the homology construction agree. -/
def completedLocalHomologyEquiv :
    CompletedH1 R U ≃ₗ[R] (splitLocalComplex R).toCC.homology 1 :=
  (completedEquiv (R := R) U).trans (splitLocalH1Equiv R).symm

end LimitLocalOperators

section TateSpecialization

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}
  {α : GKS K S →* Lambdaˣ} [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- The integral completed local limit uses the genuine Tate coefficient module. -/
def completedTateEquiv (U : Ultrafilter ℕ) :
    CompletedH1 Lambda U ≃ₗ[Lambda] TLam K S W α × TLam K S W α :=
  (completedEquiv (R := Lambda) U).trans
    ((tlamBasis (K := K) (S := S) (W := W) (α := α)).equivFun.symm.prodCongr
      (tlamBasis (K := K) (S := S) (W := W) (α := α)).equivFun.symm)

/-- The inner-limit local fibre has two copies of the actual fibre coefficient module. -/
abbrev InnerFibreH1 (P : Ideal Lambda) [P.IsPrime] :=
  VP K S W P α × VP K S W P α

/-- Scalar extension is performed on the completed integral limit, before fibre cohomology. -/
def completedFibreEquiv (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime] :
    TensorProduct Lambda (ResAt P) (CompletedH1 Lambda U) ≃ₗ[ResAt P] InnerFibreH1 (K := K) (S := S) (W := W) (α := α) P :=
  (LinearEquiv.baseChange Lambda (ResAt P) _ _
    (completedTateEquiv (K := K) (S := S) (W := W) (α := α) U)).trans
    ((TensorProduct.prodRight Lambda (ResAt P) (ResAt P) (TLam K S W α) (TLam K S W α)).trans
      ((fibreEquiv (K := K) (S := S) (W := W) (α := α) (P := P)).prodCongr
        (fibreEquiv (K := K) (S := S) (W := W) (α := α) (P := P))))

/-- Coordinates of the genuine rank-two fibre coefficient module on both planes. -/
def fibreCoordsEquiv (P : Ideal Lambda) [P.IsPrime] :
    InnerFibreH1 (K := K) (S := S) (W := W) (α := α) P ≃ₗ[ResAt P] Coords (ResAt P) :=
  (vpBasis (K := K) (S := S) (W := W) (α := α) P).equivFun.prodCongr
    (vpBasis (K := K) (S := S) (W := W) (α := α) P).equivFun

/-- Non-vacuity of the local limit fibre: its dimension is four. -/
theorem innerFibreH1_finrank (P : Ideal Lambda) [P.IsPrime] :
    finrank (ResAt P) (InnerFibreH1 (K := K) (S := S) (W := W) (α := α) P) = 4 := by
  rw [(fibreCoordsEquiv (K := K) (S := S) (W := W) (α := α) P).finrank_eq]
  simp [Coords, Vec2]

/-- The curve E_1 and the prime (t) instantiate the limiting rank-four fibre. -/
theorem innerFibreH1_E1 :
    finrank (ResAt Pt0)
      (InnerFibreH1 (K := ℚ) (S := Set.univ) (W := curveE1) (α := alphaLam ℚ Set.univ) Pt0) = 4 :=
  innerFibreH1_finrank Pt0

end TateSpecialization

section SplitConditions

variable {k : Type} [Field k]

/-- A coefficient module placed in degree one, with zero differentials. -/
abbrev oneTerms (k M : Type) [Field k] [AddCommGroup M] [Module k M] : ℤ → ModuleCat k
  | .ofNat 1 => ModuleCat.of k M
  | _ => ModuleCat.of k PUnit

abbrev oneComplex (k M : Type) [Field k] [AddCommGroup M] [Module k M] : GCx k where
  X := oneTerms k M
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- Every such quotient is concentrated in degree one. -/
theorem oneComplex_concentrated (M : Type) [AddCommGroup M] [Module k M] :
    ConcDegOne (oneComplex k M) := by
  intro n hn
  rcases n with (_ | _ | n) | n
  · change Subsingleton PUnit
    infer_instance
  · exact (hn rfl).elim
  · change Subsingleton PUnit
    infer_instance
  · change Subsingleton PUnit
    infer_instance

/-- Local conditions retain the full degree-zero term and omit degree two. -/
abbrev conditionTerms (P : Submodule k (Coords k)) : ℤ → ModuleCat k
  | .ofNat 0 => ModuleCat.of k (Vec2 k)
  | .ofNat 1 => ModuleCat.of k P
  | _ => ModuleCat.of k PUnit

abbrev conditionComplex (P : Submodule k (Coords k)) : GCx k where
  X := conditionTerms P
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- Components of the inclusion of one limit local condition into another. -/
def conditionInclAt {P Q : Submodule k (Coords k)} (h : P ≤ Q) :
    ∀ n, conditionTerms P n →ₗ[k] conditionTerms Q n
  | .ofNat 0 => LinearMap.id
  | .ofNat 1 => Submodule.inclusion h
  | _ => 0

/-- Inclusions keep the same degree-zero term; they are actual chain maps. -/
def conditionIncl {P Q : Submodule k (Coords k)} (h : P ≤ Q) :
    GHom (conditionComplex P) (conditionComplex Q) where
  f a b hab := by subst hab; exact conditionInclAt h a
  comm a a' b b' hab ha hb ha'b' x := by
    subst hab ha'b'
    change conditionInclAt h a' 0 = 0
    exact map_zero _

/-- All condition inclusions are injective in every degree. -/
theorem conditionIncl_injective {P Q : Submodule k (Coords k)} (h : P ≤ Q) (n : ℤ) :
    Function.Injective ((conditionIncl h).f n n rfl) := by
  rcases n with (_ | _ | n) | n
  · exact Function.injective_id
  · exact Submodule.inclusion_injective h
  · exact fun _ _ _ => Subsingleton.elim (α := PUnit) _ _
  · exact fun _ _ _ => Subsingleton.elim (α := PUnit) _ _

/-- The condition inclusion into the full local complex, including degree zero. -/
def conditionToLocalAt (P : Submodule k (Coords k)) :
    ∀ n, conditionTerms P n →ₗ[k] splitLocalTerms k n
  | .ofNat 0 => LinearMap.id
  | .ofNat 1 => P.subtype
  | _ => 0

def conditionToLocal (P : Submodule k (Coords k)) :
    GHom (conditionComplex P) (splitLocalComplex k) where
  f a b hab := by subst hab; exact conditionToLocalAt P a
  comm a a' b b' hab ha hb ha'b' x := by
    subst hab ha'b'
    change conditionToLocalAt P a' 0 = 0
    exact map_zero _

/-- Projection from a local condition to its degree-one coordinate quotient. -/
def conditionProjAt {P : Submodule k (Coords k)} {M : Type} [AddCommGroup M] [Module k M]
    (f : P →ₗ[k] M) : ∀ n, conditionTerms P n →ₗ[k] oneTerms k M n
  | .ofNat 1 => f
  | _ => 0

def conditionProj {P : Submodule k (Coords k)} {M : Type} [AddCommGroup M] [Module k M]
    (f : P →ₗ[k] M) : GHom (conditionComplex P) (oneComplex k M) where
  f a b hab := by subst hab; exact conditionProjAt f a
  comm a a' b b' hab ha hb ha'b' x := by
    subst hab ha'b'
    change conditionProjAt f a' 0 = 0
    exact map_zero _

/-- The degree-one map between coordinate quotients. -/
def oneMapAt {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) : ∀ n, oneTerms k M n →ₗ[k] oneTerms k N n
  | .ofNat 1 => f
  | _ => 0

def oneMap {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) : GHom (oneComplex k M) (oneComplex k N) where
  f a b hab := by subst hab; exact oneMapAt f a
  comm a a' b b' hab ha hb ha'b' x := by
    subst hab ha'b'
    change oneMapAt f a' 0 = 0
    exact map_zero _

variable (G : GCx k) (res : GHom G (splitLocalComplex k))

/-- Selmer data with the relaxed derivative condition, which is not the full local complex. -/
abbrev limitRelaxedData : SelData k :=
  ⟨G, conditionComplex ⊤, splitLocalComplex k, res, conditionToLocal ⊤⟩

/-- The local quotient and its coordinates are constructed from the split limit. -/
abbrev literalLimitRelaxed : RelaxedLocalization k where
  D := limitRelaxedData G res
  Wrel := oneComplex k (Coords k)
  gR := conditionProj (⊤ : Submodule k (Coords k)).subtype
  eR := LinearEquiv.refl k (Coords k)
  hWrel := oneComplex_concentrated _

/-- The strict condition retains exactly the same degree-zero term as all other conditions. -/
def limitStrictData : SelData k :=
  ⟨G, conditionComplex ⊥, splitLocalComplex k, res, conditionToLocal ⊥⟩

/-- Both switch sides, with all exactness fields proved, for a split coordinate projection. -/
def literalLimitSide (P : Submodule k (Coords k)) (T : Type) [AddCommGroup T] [Module k T]
    (π : Coords k →ₗ[k] T) (hπ : Function.Surjective π) (hker : ∀ x, π x = 0 ↔ x ∈ P) :
    SwitchSide (literalLimitRelaxed G res) P where
  U₁ := conditionComplex P
  Ustr := conditionComplex ⊥
  W₁ := oneComplex k P
  W₂ := oneComplex k T
  f₁ := conditionIncl le_top
  g₂ := conditionProj (π ∘ₗ (⊤ : Submodule k (Coords k)).subtype)
  fs := conditionIncl bot_le
  g₁ := conditionProj (LinearMap.id : P →ₗ[k] P)
  i := oneMap P.subtype
  p := oneMap π
  hfg₂ n u := by
    rcases n with (_ | _ | n) | n
    · rfl
    · change P at u
      change π (u : Coords k) = 0
      exact (hker u).mpr u.2
    · rfl
    · rfl
  f₁_inj := conditionIncl_injective le_top
  g₂_surj n := by
    rcases n with (_ | _ | n) | n
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · intro y
      obtain ⟨x, hx⟩ := hπ y
      exact ⟨⟨x, Submodule.mem_top⟩, hx⟩
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  ex₂ n u hu := by
    rcases n with (_ | _ | n) | n
    · exact ⟨u, rfl⟩
    · change ↥(⊤ : Submodule k (Coords k)) at u
      change π (u : Coords k) = 0 at hu
      exact ⟨⟨u, (hker u).mp hu⟩, Subtype.ext rfl⟩
    · exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  hfg₁ n u := by
    rcases n with (_ | _ | n) | n
    · rfl
    · apply Subtype.ext
      exact (Submodule.mem_bot k).mp u.2
    · rfl
    · rfl
  fs_inj := conditionIncl_injective bot_le
  g₁_surj n := by
    rcases n with (_ | _ | n) | n
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · exact Function.surjective_id
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  ex₁ n u hu := by
    rcases n with (_ | _ | n) | n
    · exact ⟨u, rfl⟩
    · change u = 0 at hu
      subst hu
      exact ⟨0, rfl⟩
    · exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  hRF n u := by
    rcases n with (_ | _ | n) | n <;> rfl
  hpR n u := by
    rcases n with (_ | _ | n) | n <;> rfl
  hW₁ := oneComplex_concentrated _
  hW₂ := oneComplex_concentrated _
  i_inj := P.injective_subtype
  ip_exact y := by
    change π y = 0 ↔ ∃ x : P, (x : Coords k) = y
    rw [hker]
    exact ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩
  hP := by
    change LinearMap.range P.subtype = P
    exact Submodule.range_subtype P

/-- The finite side is constructed with singular-coordinate projection. -/
def finiteLiteralLimitSide :
    SwitchSide (literalLimitRelaxed G res) (finPlane k (Vec2 k) (Vec2 k)) :=
  literalLimitSide G res (finPlane k (Vec2 k) (Vec2 k)) (Vec2 k) (LinearMap.snd k _ _)
    LinearMap.snd_surjective (fun _ => mem_finPlane.symm)

/-- The singular side is constructed with finite-coordinate projection. -/
def singularLiteralLimitSide :
    SwitchSide (literalLimitRelaxed G res) (singPlane k (Vec2 k) (Vec2 k)) :=
  literalLimitSide G res (singPlane k (Vec2 k) (Vec2 k)) (Vec2 k) (LinearMap.fst k _ _)
    LinearMap.fst_surjective (fun _ => mem_singPlane.symm)

/-- The homology-level relaxed object required by the existing switch engine. -/
def limitRelaxed : QuasiRelaxedLocalization k := (literalLimitRelaxed G res).toQuasi

/-- The finite quasi side needs no duality assumption. -/
def finiteLimitSide : QuasiSwitchSide (limitRelaxed G res) (finPlane k (Vec2 k) (Vec2 k)) :=
  (finiteLiteralLimitSide G res).toQuasi

/-- The singular quasi side needs no duality assumption. -/
def singularLimitSide : QuasiSwitchSide (limitRelaxed G res) (singPlane k (Vec2 k) (Vec2 k)) :=
  (singularLiteralLimitSide G res).toQuasi

end SplitConditions

section StrictAndDuality

variable {k : Type} [Field k] (G : GCx k) (res : GHom G (splitLocalComplex k))

/-- The strict condition of each side is the same actual Selmer datum. -/
theorem literalLimitSide_Dstr (P : Submodule k (Coords k)) (T : Type) [AddCommGroup T] [Module k T]
    (π : Coords k →ₗ[k] T) (hπ : Function.Surjective π) (hker : ∀ x, π x = 0 ↔ x ∈ P) :
    (literalLimitSide G res P T π hπ hker).Dstr = limitStrictData G res := by
  change (⟨G, conditionComplex ⊥, splitLocalComplex k, res,
    ghomComp (conditionIncl (bot_le : (⊥ : Submodule k (Coords k)) ≤ P))
      (ghomComp (conditionIncl (le_top : P ≤ ⊤)) (conditionToLocal ⊤))⟩ : SelData k) = _
  unfold limitStrictData
  congr 1
  apply ghom_ext
  intro n u
  rcases n with (_ | _ | n) | n <;> rfl

/-- The two quasi sides share their strict Selmer data, not merely its dimension. -/
theorem limitSides_Dstr : (finiteLimitSide G res).Dstr = (singularLimitSide G res).Dstr := by
  change (finiteLiteralLimitSide G res).Dstr = (singularLiteralLimitSide G res).Dstr
  exact (literalLimitSide_Dstr G res (finPlane k (Vec2 k) (Vec2 k)) (Vec2 k)
    (LinearMap.snd k _ _) LinearMap.snd_surjective (fun _ => mem_finPlane.symm)).trans
    (literalLimitSide_Dstr G res (singPlane k (Vec2 k) (Vec2 k)) (Vec2 k)
      (LinearMap.fst k _ _) LinearMap.fst_surjective (fun _ => mem_singPlane.symm)).symm

/-- The strict inclusion into the relaxed condition of this very limit diagram. -/
def strictLimitMap : GHom (conditionComplex (⊥ : Submodule k (Coords k))) (limitRelaxed G res).D.U :=
  conditionIncl bot_le

/-- The strict inclusion is annihilated by the actual quotient map. -/
theorem strictLimitMap_zero (n : ℤ) (u : (conditionComplex (⊥ : Submodule k (Coords k))).X n) :
    (limitRelaxed G res).gR.f n n rfl ((strictLimitMap G res).f n n rfl u) = 0 := by
  rcases n with (_ | _ | n) | n
  · rfl
  · change ↥(⊥ : Submodule k (Coords k)) at u
    change (u : Coords k) = 0
    exact (Submodule.mem_bot k).mp u.2
  · rfl
  · rfl

/-- Degreewise injectivity of the strict inclusion. -/
theorem strictLimitMap_injective (n : ℤ) : Function.Injective ((strictLimitMap G res).f n n rfl) :=
  conditionIncl_injective bot_le n

/-- Degreewise surjectivity of the actual relaxed/strict quotient. -/
theorem strictLimitQuot_surjective (n : ℤ) :
    Function.Surjective ((limitRelaxed G res).gR.f n n rfl) := by
  rcases n with (_ | _ | n) | n
  · exact fun x => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  · exact fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩
  · exact fun x => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  · exact fun x => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩

/-- Degreewise exactness of the actual strict/relaxed quotient sequence. -/
theorem strictLimitQuot_exact (n : ℤ) (u : (limitRelaxed G res).D.U.X n)
    (hu : (limitRelaxed G res).gR.f n n rfl u = 0) :
    ∃ u', (strictLimitMap G res).f n n rfl u' = u := by
  rcases n with (_ | _ | n) | n
  · exact ⟨u, rfl⟩
  · change ↥(⊤ : Submodule k (Coords k)) at u
    change (u : Coords k) = 0 at hu
    exact ⟨0, Subtype.ext hu.symm⟩
  · exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  · exact ⟨0, Subsingleton.elim (α := PUnit) _ _⟩

/-- Restriction along the strict inclusion gives the stated strict Selmer datum. -/
theorem strictLimitMap_Data :
    restrictData (limitRelaxed G res).D (strictLimitMap G res) = limitStrictData G res := by
  change (⟨G, conditionComplex ⊥, splitLocalComplex k, res,
    ghomComp (conditionIncl (bot_le : (⊥ : Submodule k (Coords k)) ≤ ⊤))
      (conditionToLocal ⊤)⟩ : SelData k) = _
  unfold limitStrictData
  congr 1
  apply ghom_ext
  intro n u
  rcases n with (_ | _ | n) | n <;> rfl

/-- The connecting map is that of the actual strict/relaxed change-of-condition sequence. -/
def limitDelta : (limitRelaxed G res).Wrel.toCC.homology 1 →ₗ[k]
    (selCx (restrictData (limitRelaxed G res).D (strictLimitMap G res))).toCC.homology 2 :=
  switchDelta (limitRelaxed G res) (strictLimitMap G res) (strictLimitMap_zero G res)
    (strictLimitMap_injective G res) (strictLimitQuot_surjective G res) (strictLimitQuot_exact G res)

/-- Localization and the connecting map are exact in the actual limit diagram. -/
theorem limitDelta_exact : LinearMap.range (H1 (quotMap (limitRelaxed G res).D (limitRelaxed G res).gR)) =
    LinearMap.ker (limitDelta G res) :=
  switchDelta_exact (limitRelaxed G res) (strictLimitMap G res) (strictLimitMap_zero G res)
    (strictLimitMap_injective G res) (strictLimitQuot_surjective G res) (strictLimitQuot_exact G res)

/-- The precise missing duality is a separating pairing adjoint to this connecting map. -/
def LimitSwitchDuality (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1) : Prop :=
  SwitchDualityAdjunction (limitRelaxed G res)
    (restrictData (limitRelaxed G res).D (strictLimitMap G res)) ε σ J hε hσ hJ
    (limitDelta G res) (limitDelta_exact G res)

/-- Exact self-annihilation follows from the missing duality; it is not assumed as a new axiom. -/
theorem limitLocalizationDuality (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (h : LimitSwitchDuality G res ε σ J hε hσ hJ) :
    LocalizationDualityInput ε σ J hε hσ hJ (limitRelaxed G res).U :=
  localizationDualityInput_of_adjunction (limitRelaxed G res)
    (restrictData (limitRelaxed G res).D (strictLimitMap G res)) ε σ J hε hσ hJ
    (limitDelta G res) (limitDelta_exact G res) h

variable {A F : Type} [CommRing A] [Field F] {ι : A →+* F}

/-- Existing nonquadratic consumer data, constructed from the limit objects and explicitly named inputs. -/
def limitNonquadStep (ρ : A →+* k) (S₀ S₁ : TwoTermStage ι)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (hdual : LimitSwitchDuality G res ε σ J hε hσ hJ)
    (hdet : finPlane k (Vec2 k) (Vec2 k) ≤ (limitRelaxed G res).U)
    (φ : (selCx (finiteLimitSide G res).Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S₀)
    (φ' : (selCx (singularLimitSide G res).Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S₁) :
    QuasiNonquadStep ρ S₀ S₁ where
  R := limitRelaxed G res
  SF := finiteLimitSide G res
  SS := singularLimitSide G res
  hk0 := by rw [limitSides_Dstr]
  ε := ε
  σ := σ
  J := J
  hε := hε
  hσ := hσ
  hJ2 := hJ
  hdual := limitLocalizationDuality G res ε σ J hε hσ hJ hdual
  hdet := hdet
  φ := φ
  φ' := φ'

end StrictAndDuality

section PerfectDualityContract

variable {k : Type} [Field k] (G : GCx k) (res : GHom G (splitLocalComplex k))

/-- A precise complex-level contract for fixed-field duality and the retained local residue formula. -/
def LimitPairingCertificate (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) : Prop :=
  ∃ (Q : SelPairData (restrictData (limitRelaxed G res).D (strictLimitMap G res)) (limitRelaxed G res).D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0),
    QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)) ∧
    ∀ (t u : (limitRelaxed G res).D.U.X 1) (s : (conditionComplex (⊥ : Submodule k (Coords k))).X 2)
      (_ht : (limitRelaxed G res).D.U.d 1 2 rfl t = 0)
      (_hu : (limitRelaxed G res).D.U.d 1 2 rfl u = (strictLimitMap G res).f 2 2 rfl s)
      (ct cu : LinearMap.ker ((limitRelaxed G res).Wrel.d 1 2 rfl))
      (_hct : ct.1 = (limitRelaxed G res).gR.f 1 1 rfl t)
      (_hcu : cu.1 = (limitRelaxed G res).gR.f 1 1 rfl u),
      tr (selCupFun Q 2 1 3 rfl
          ((0 : (limitRelaxed G res).D.G.X 2), s,
            -((limitRelaxed G res).D.ι.f 1 (2 - 1) (by omega) u))
          ((0 : (limitRelaxed G res).D.G.X 1), t, (0 : (limitRelaxed G res).D.L.X (1 - 1)))) =
        switchPairing ε σ J ((limitRelaxed G res).eR (cls1 (limitRelaxed G res).Wrel ct))
          ((limitRelaxed G res).eR (cls1 (limitRelaxed G res).Wrel cu))

/-- The fixed-field complex duality contract supplies exactly the required limit adjunction. -/
theorem limitDuality_of_pairingCertificate (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (H : LimitPairingCertificate G res ε σ J) : LimitSwitchDuality G res ε σ J hε hσ hJ := by
  obtain ⟨Q, tr, htr, hqi, hres⟩ := H
  exact switchAdjunctionFromDuality_proof k (limitRelaxed G res)
    (conditionComplex (⊥ : Submodule k (Coords k))) (strictLimitMap G res)
    (strictLimitMap_zero G res) (strictLimitMap_injective G res)
    (strictLimitQuot_surjective G res) (strictLimitQuot_exact G res) Q tr htr ε σ J hε hσ hJ hqi hres

end PerfectDualityContract

section CoefficientStageCoordinates

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}

/-- Coordinate modules at the finite coefficient stages, before any characteristic-zero fibre. -/
abbrev StageCoordinates (I : ℕ → Ideal R) := ∀ i, Coords (R ⧸ I i)

/-- A coordinate lift at each coefficient stage; only its class will matter. -/
def stageLift (x : StageCoordinates I) : ℕ → Coords R := fun i =>
  (fun a => Classical.choose (Ideal.Quotient.mk_surjective ((x i).1 a)),
    fun a => Classical.choose (Ideal.Quotient.mk_surjective ((x i).2 a)))

omit [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R] in
@[simp] theorem stageLift_fst (x : StageCoordinates I) (i : ℕ) (a : Fin 2) :
    Ideal.Quotient.mk (I i) ((stageLift x i).1 a) = (x i).1 a :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective ((x i).1 a))

omit [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R] in
@[simp] theorem stageLift_snd (x : StageCoordinates I) (i : ℕ) (a : Fin 2) :
    Ideal.Quotient.mk (I i) ((stageLift x i).2 a) = (x i).2 a :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective ((x i).2 a))

variable (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)

include hI hU

/-- Equality of coefficient-stage projections implies equality of limiting coordinates. -/
theorem coordLimit_eq_of_stage_projection {x y : ℕ → Coords R}
    (h : ∀ᶠ i in (U : Filter ℕ),
      (∀ a, Ideal.Quotient.mk (I i) ((x i).1 a) = Ideal.Quotient.mk (I i) ((y i).1 a)) ∧
      (∀ a, Ideal.Quotient.mk (I i) ((x i).2 a) = Ideal.Quotient.mk (I i) ((y i).2 a))) :
    coordLimit U x = coordLimit U y :=
  Prod.ext (ulimVec_eq_of_stages hI hU (h.mono fun _ hi => hi.1))
    (ulimVec_eq_of_stages hI hU (h.mono fun _ hi => hi.2))

/-- The limit map on the actual coefficient-stage coordinate product is linear over R. -/
def stageLimit : StageCoordinates I →ₗ[R] Coords R where
  toFun x := coordLimit U (stageLift x)
  map_add' x y := by
    change coordLimit U (stageLift (x + y)) = coordLimit U (stageLift x) + coordLimit U (stageLift y)
    rw [← map_add]
    apply coordLimit_eq_of_stage_projection hI hU
    exact Eventually.of_forall fun i => ⟨fun a => by simp, fun a => by simp⟩
  map_smul' r x := by
    change coordLimit U (stageLift (r • x)) = r • coordLimit U (stageLift x)
    rw [← map_smul]
    apply coordLimit_eq_of_stage_projection hI hU
    refine Eventually.of_forall fun i => ⟨?_, ?_⟩
    · intro a
      change Ideal.Quotient.mk (I i) ((stageLift (r • x) i).1 a) =
        Ideal.Quotient.mk (I i) (r * (stageLift x i).1 a)
      rw [stageLift_fst, map_mul, stageLift_fst]
      rfl
    · intro a
      change Ideal.Quotient.mk (I i) ((stageLift (r • x) i).2 a) =
        Ideal.Quotient.mk (I i) (r * (stageLift x i).2 a)
      rw [stageLift_snd, map_mul, stageLift_snd]
      rfl

/-- The coefficient-stage limit is onto; constant integral tuples provide representatives. -/
theorem stageLimit_surjective : Function.Surjective (stageLimit hI hU) := by
  intro x
  let s : StageCoordinates I := fun i =>
    (fun a => Ideal.Quotient.mk (I i) (x.1 a), fun a => Ideal.Quotient.mk (I i) (x.2 a))
  have he : coordLimit U (stageLift s) = coordLimit U (fun _ => x) := by
    apply coordLimit_eq_of_stage_projection hI hU
    exact Eventually.of_forall fun i => ⟨fun a => by simp [s], fun a => by simp [s]⟩
  exact ⟨s, he.trans (coordLimit_const U x)⟩

/-- The separated limit of the finite-coefficient coordinate groups. -/
abbrev CompletedStageH1 := StageCoordinates I ⧸ (stageLimit hI hU).ker

/-- The actual coefficient-stage product has the same limiting rank-four coordinate module. -/
def completedStageEquiv : CompletedStageH1 hI hU ≃ₗ[R] Coords R :=
  LinearMap.quotKerEquivOfSurjective (stageLimit hI hU) (stageLimit_surjective hI hU)

/-- The lift-based and coefficient-stage definitions of the inner limit agree. -/
def stageToLiftEquiv : CompletedStageH1 hI hU ≃ₗ[R] CompletedH1 R U :=
  (completedStageEquiv hI hU).trans (completedEquiv (R := R) U).symm

omit [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R] hI hU in
/-- Both local differential operators are already zero at the retained coefficient precision. -/
theorem derivative_stage_operators (D : DerivativeMatrices I U) :
    ∀ᶠ i in (U : Filter ℕ),
      Matrix.toLin' ((D.phi i).map (Ideal.Quotient.mk (I i))) - LinearMap.id = 0 ∧
      Matrix.toLin' ((D.phi i).map (Ideal.Quotient.mk (I i))) -
        Ideal.Quotient.mk (I i) (D.ell i ^ 2) • LinearMap.id = 0 := by
  filter_upwards [D.phi_congr, D.ell_congr] with i hi he
  have hphi : (D.phi i).map (Ideal.Quotient.mk (I i)) = 1 := by
    have hc : (D.phi i).map (Ideal.Quotient.mk (I i)) =
        (1 : Matrix (Fin 2) (Fin 2) R).map (Ideal.Quotient.mk (I i)) := by
      ext a b
      exact Ideal.Quotient.eq.mpr (hi a b)
    simpa only [Matrix.map_one _ (map_zero _) (map_one _)] using hc
  have hell : Ideal.Quotient.mk (I i) (D.ell i) = -1 := by
    have hc : Ideal.Quotient.mk (I i) (D.ell i) = Ideal.Quotient.mk (I i) (-1) :=
      Ideal.Quotient.eq.mpr (by simpa using he)
    simpa using hc
  have hq : Ideal.Quotient.mk (I i) (D.ell i ^ 2) = 1 := by rw [map_pow, hell]; simp
  rw [hphi, hq, Matrix.toLin'_one, one_smul, sub_self]
  exact ⟨rfl, rfl⟩

end CoefficientStageCoordinates

section RankAndFibrePlanes

variable {R : Type} [CommRing R]

/-- The finite integral plane is free, independently of the limit duality. -/
instance finiteAxis_free : Module.Free R (finiteAxis R) :=
  Module.Free.of_basis (Basis.ofEquivFun (finiteAxisEquiv (R := R)))

instance finiteAxis_finite : Module.Finite R (finiteAxis R) :=
  Module.Finite.of_basis (Basis.ofEquivFun (finiteAxisEquiv (R := R)))

instance singularAxis_free : Module.Free R (singularAxis R) :=
  Module.Free.of_basis (Basis.ofEquivFun (singularAxisEquiv (R := R)))

instance singularAxis_finite : Module.Finite R (singularAxis R) :=
  Module.Finite.of_basis (Basis.ofEquivFun (singularAxisEquiv (R := R)))

theorem finiteAxis_finrank [StrongRankCondition R] : finrank R (finiteAxis R) = 2 := by
  rw [(finiteAxisEquiv (R := R)).finrank_eq, Module.finrank_fin_fun]

theorem singularAxis_finrank [StrongRankCondition R] : finrank R (singularAxis R) = 2 := by
  rw [(singularAxisEquiv (R := R)).finrank_eq, Module.finrank_fin_fun]

variable [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]

/-- The completed finite plane is identified with the rank-two integral coordinate module. -/
def completedFiniteEquiv (U : Ultrafilter ℕ) : completedFinite (R := R) U ≃ₗ[R] Vec2 R :=
  (Submodule.equivMapOfInjective (completedEquiv (R := R) U).toLinearMap
    (completedEquiv (R := R) U).injective (completedFinite (R := R) U)).trans
    ((LinearEquiv.ofEq _ _ (completedFinite_map (R := R) U)).trans (finiteAxisEquiv (R := R)))

/-- The completed singular plane is identified with the rank-two integral coordinate module. -/
def completedSingularEquiv (U : Ultrafilter ℕ) : completedSingular (R := R) U ≃ₗ[R] Vec2 R :=
  (Submodule.equivMapOfInjective (completedEquiv (R := R) U).toLinearMap
    (completedEquiv (R := R) U).injective (completedSingular (R := R) U)).trans
    ((LinearEquiv.ofEq _ _ (completedSingular_map (R := R) U)).trans (singularAxisEquiv (R := R)))

instance completedFinite_free (U : Ultrafilter ℕ) : Module.Free R (completedFinite (R := R) U) :=
  Module.Free.of_basis (Basis.ofEquivFun (completedFiniteEquiv (R := R) U))

instance completedSingular_free (U : Ultrafilter ℕ) : Module.Free R (completedSingular (R := R) U) :=
  Module.Free.of_basis (Basis.ofEquivFun (completedSingularEquiv (R := R) U))

/-- The completed local module has integral rank four. -/
theorem completedH1_finrank [StrongRankCondition R] (U : Ultrafilter ℕ) :
    finrank R (CompletedH1 R U) = 4 := by
  rw [(completedEquiv (R := R) U).finrank_eq]
  simp [Coords, Vec2]

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}
  {α : GKS K S →* Lambdaˣ} [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- The completed finite-coefficient product specializes to two genuine copies of V_P. -/
def completedStageFibreEquiv (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] :
    TensorProduct Lambda (ResAt P) (CompletedStageH1 (R := Lambda) stageIdeal_tendsToZero hU) ≃ₗ[ResAt P]
      InnerFibreH1 (K := K) (S := S) (W := W) (α := α) P :=
  (LinearEquiv.baseChange Lambda (ResAt P) _ _
    (stageToLiftEquiv (R := Lambda) stageIdeal_tendsToZero hU)).trans
    (completedFibreEquiv (K := K) (S := S) (W := W) (α := α) U P)

/-- The finite plane inside the genuine limit fibre coefficient module. -/
def fibreFinitePlane (P : Ideal Lambda) [P.IsPrime] :
    Submodule (ResAt P) (InnerFibreH1 (K := K) (S := S) (W := W) (α := α) P) :=
  (finiteAxis (ResAt P)).comap (fibreCoordsEquiv (K := K) (S := S) (W := W) (α := α) P).toLinearMap

/-- The singular plane inside the genuine limit fibre coefficient module. -/
def fibreSingularPlane (P : Ideal Lambda) [P.IsPrime] :
    Submodule (ResAt P) (InnerFibreH1 (K := K) (S := S) (W := W) (α := α) P) :=
  (singularAxis (ResAt P)).comap (fibreCoordsEquiv (K := K) (S := S) (W := W) (α := α) P).toLinearMap

/-- The finite fibre plane has exactly the consumer's finite-plane coordinates. -/
theorem fibreFinitePlane_map (P : Ideal Lambda) [P.IsPrime] :
    (fibreFinitePlane (K := K) (S := S) (W := W) (α := α) P).map
      (fibreCoordsEquiv (K := K) (S := S) (W := W) (α := α) P).toLinearMap = finiteAxis (ResAt P) := by
  rw [fibreFinitePlane, Submodule.map_comap_eq,
    LinearMap.range_eq_top.mpr (fibreCoordsEquiv (K := K) (S := S) (W := W) (α := α) P).surjective,
    top_inf_eq]

/-- The singular fibre plane has exactly the consumer's singular-plane coordinates. -/
theorem fibreSingularPlane_map (P : Ideal Lambda) [P.IsPrime] :
    (fibreSingularPlane (K := K) (S := S) (W := W) (α := α) P).map
      (fibreCoordsEquiv (K := K) (S := S) (W := W) (α := α) P).toLinearMap = singularAxis (ResAt P) := by
  rw [fibreSingularPlane, Submodule.map_comap_eq,
    LinearMap.range_eq_top.mpr (fibreCoordsEquiv (K := K) (S := S) (W := W) (α := α) P).surjective,
    top_inf_eq]

/-- The finite plane remains two-dimensional after the fixed-P specialization. -/
theorem fibreFinitePlane_finrank (P : Ideal Lambda) [P.IsPrime] :
    finrank (ResAt P) (fibreFinitePlane (K := K) (S := S) (W := W) (α := α) P) = 2 := by
  rw [← (fibreCoordsEquiv (K := K) (S := S) (W := W) (α := α) P).finrank_map_eq,
    fibreFinitePlane_map]
  exact finiteAxis_finrank

/-- The singular plane remains two-dimensional after the fixed-P specialization. -/
theorem fibreSingularPlane_finrank (P : Ideal Lambda) [P.IsPrime] :
    finrank (ResAt P) (fibreSingularPlane (K := K) (S := S) (W := W) (α := α) P) = 2 := by
  rw [← (fibreCoordsEquiv (K := K) (S := S) (W := W) (α := α) P).finrank_map_eq,
    fibreSingularPlane_map]
  exact singularAxis_finrank

/-- Both switch planes are non-vacuous at E_1 and P = (t). -/
theorem fibrePlanes_E1 :
    finrank (ResAt Pt0)
      (fibreFinitePlane (K := ℚ) (S := Set.univ) (W := curveE1) (α := alphaLam ℚ Set.univ) Pt0) = 2 ∧
    finrank (ResAt Pt0)
      (fibreSingularPlane (K := ℚ) (S := Set.univ) (W := curveE1) (α := alphaLam ℚ Set.univ) Pt0) = 2 :=
  ⟨fibreFinitePlane_finrank Pt0, fibreSingularPlane_finrank Pt0⟩

end RankAndFibrePlanes

section RetainedInverseCertificates

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)

include hI hU

/-- A retained inverse identity, rather than stagewise nonzero values, certifies a unit limit. -/
theorem scalar_limit_isUnit (a b : ℕ → R)
    (hab : ∀ᶠ i in (U : Filter ℕ), a i * b i - 1 ∈ I i) : IsUnit (ulim U a) := by
  have he : ulim U a * ulim U b = 1 := by
    rw [← ulim_mul, ← ulim_const U (1 : R)]
    exact ulim_eq_ulim_of_sub_mem hI hU hab
  refine ⟨⟨ulim U a, ulim U b, he, ?_⟩, rfl⟩
  rwa [mul_comm]

/-- Matrix inverse identities may be cleared by one fixed scalar for the retained diagram. -/
structure InverseMatrixStages (n : ℕ) where
  forward : ℕ → Matrix (Fin n) (Fin n) R
  inverse : ℕ → Matrix (Fin n) (Fin n) R
  scale : R
  right : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
    (forward i * inverse i - scale • 1) a b ∈ I i
  left : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
    (inverse i * forward i - scale • 1) a b ∈ I i

/-- The right inverse identity survives the coefficient-stage limit with the same scalar. -/
theorem inverseMatrices_right {n : ℕ} (D : InverseMatrixStages (I := I) (U := U) n) :
    ulimMat U D.forward * ulimMat U D.inverse = D.scale • 1 := by
  rw [← ulimMat_const U (D.scale • (1 : Matrix (Fin n) (Fin n) R))]
  exact matrix_identity_survives hI hU D.forward D.inverse (fun _ => D.scale • 1) D.right

/-- The left inverse identity survives as well. -/
theorem inverseMatrices_left {n : ℕ} (D : InverseMatrixStages (I := I) (U := U) n) :
    ulimMat U D.inverse * ulimMat U D.forward = D.scale • 1 := by
  rw [← ulimMat_const U (D.scale • (1 : Matrix (Fin n) (Fin n) R))]
  exact matrix_identity_survives hI hU D.inverse D.forward (fun _ => D.scale • 1) D.left

variable {k : Type} [Field k]

/-- A fixed cleared inverse scalar stays fixed after specializing the limit matrices. -/
theorem inverseMatrices_specialized {n : ℕ} (ρ : R →+* k)
    (D : InverseMatrixStages (I := I) (U := U) n) :
    (ulimMat U D.forward).map ρ * (ulimMat U D.inverse).map ρ = ρ D.scale • 1 := by
  rw [← Matrix.map_mul, inverseMatrices_right hI hU D]
  ext a b
  change ρ (D.scale * (if a = b then 1 else 0)) = ρ D.scale * (if a = b then 1 else 0)
  by_cases h : a = b <;> simp [h]

/-- Nondegeneracy cannot be lost in the limit when a fixed inverse certificate is retained. -/
theorem inverseMatrices_pairing_separates {n : ℕ} (ρ : R →+* k)
    (D : InverseMatrixStages (I := I) (U := U) n) (hscale : ρ D.scale ≠ 0) :
    ∀ x : Fin n → k, (∀ y, Matrix.toBilin' ((ulimMat U D.forward).map ρ) x y = 0) → x = 0 := by
  let P := (ulimMat U D.forward).map ρ
  let Q := (ρ D.scale)⁻¹ • (ulimMat U D.inverse).map ρ
  have hPQ : P * Q = 1 := by
    dsimp [P, Q]
    rw [Matrix.mul_smul, inverseMatrices_specialized hI hU ρ D, smul_smul,
      inv_mul_cancel₀ hscale, one_smul]
  intro x hx
  funext a
  have hz := hx (Q *ᵥ Pi.single a 1)
  change Matrix.toBilin' P x (Q *ᵥ Pi.single a 1) = 0 at hz
  rw [Matrix.toBilin'_apply', Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec,
    dotProduct_single_one] at hz
  exact hz

end RetainedInverseCertificates

section LimitConjugation

variable {R : Type} [CommRing R]

/-- The local limit action has J on the finite plane and minus J on the singular plane. -/
def localLimitAction (J : Matrix (Fin 2) (Fin 2) R) : Coords R →ₗ[R] Coords R :=
  (Matrix.toLin' J).prodMap (-Matrix.toLin' J)

/-- The action is an involution over the integral ring. -/
theorem localLimitAction_square (J : Matrix (Fin 2) (Fin 2) R) (hJ : J * J = 1) :
    localLimitAction J ∘ₗ localLimitAction J = LinearMap.id := by
  have hj : Matrix.toLin' J ∘ₗ Matrix.toLin' J = LinearMap.id := by
    rw [← Matrix.toLin'_mul, hJ, Matrix.toLin'_one]
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact LinearMap.congr_fun hj x.1
  · change -(Matrix.toLin' J (-(Matrix.toLin' J x.2))) = x.2
    rw [map_neg, neg_neg]
    exact LinearMap.congr_fun hj x.2

/-- The limiting involution preserves the finite plane. -/
theorem localLimitAction_finite (J : Matrix (Fin 2) (Fin 2) R) :
    finiteAxis R ≤ (finiteAxis R).comap (localLimitAction J) := by
  intro x hx
  rw [Submodule.mem_comap, mem_finiteAxis]
  rw [mem_finiteAxis] at hx
  change (-Matrix.toLin' J) x.2 = 0
  rw [hx, map_zero]

/-- The limiting involution preserves the singular plane. -/
theorem localLimitAction_singular (J : Matrix (Fin 2) (Fin 2) R) :
    singularAxis R ≤ (singularAxis R).comap (localLimitAction J) := by
  intro x hx
  rw [Submodule.mem_comap, mem_singularAxis]
  rw [mem_singularAxis] at hx
  change Matrix.toLin' J x.1 = 0
  rw [hx, map_zero]

variable [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
  {I : ℕ → Ideal R} {U : Ultrafilter ℕ} (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)

include hI hU

/-- Both limiting coordinate actions are obtained from the retained moving-prime matrices. -/
theorem localLimitAction_from_stages (D : DerivativeMatrices I U) :
    (Matrix.toLin' (ulimMat U D.rationalFrob)).prodMap
      (Matrix.toLin' (ulimMat U (fun i => D.ellInv i • D.rationalFrob i))) = localLimitAction D.J := by
  rw [rationalFrob_limit hI hU D, singularAction_limit hI hU D]
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · simp [localLimitAction]

/-- The orientation of J follows from retained rational Frobenius determinants. -/
theorem limitJ_det (D : DerivativeMatrices I U)
    (hdet : ∀ᶠ i in (U : Filter ℕ), (D.rationalFrob i).det - D.ell i ∈ I i) : D.J.det = -1 := by
  have he : ulim U (fun i => (D.rationalFrob i).det) = ulim U D.ell :=
    ulim_eq_ulim_of_sub_mem hI hU hdet
  have hj : ∀ a b, ulim U (fun i => D.rationalFrob i a b) = D.J a b := fun a b =>
    congrFun (congrFun (rationalFrob_limit hI hU D) a) b
  have hd : ulim U (fun i => (D.rationalFrob i).det) = D.J.det := by
    simp only [Matrix.det_fin_two, ulim_sub, ulim_mul, hj]
  rw [hd, ell_limit hI hU D] at he
  exact he

end LimitConjugation

section RetainedHomotopyInverses

variable {R : Type} [CommRing R]

/-- Assemble an actual cochain homotopy from relation-indexed linear identities. -/
def homotopyOfLinearIdentities {C D : CochainComplex (ModuleCat R) ℤ} (f g : C ⟶ D)
    (h : ∀ a b, b + 1 = a → C.X a →ₗ[R] D.X b)
    (heq : ∀ a, (f.f a).hom = h (a + 1) a rfl ∘ₗ (C.d a (a + 1)).hom +
      (D.d (a - 1) a).hom ∘ₗ h a (a - 1) (by omega) + (g.f a).hom) : Homotopy f g where
  hom a b := if hab : b + 1 = a then ModuleCat.ofHom (h a b hab) else 0
  zero a b hab := dite_eq_right hab
  comm a := by
    have hprev : (a - 1) + 1 = a := by omega
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (a - 1) a from hprev)]
    simp only [dite_eq_left hprev]
    apply ModuleCat.hom_ext
    exact heq a

/-- Relation-indexed and ordinary differential linear maps agree exactly. -/
theorem toCC_d_linear (C : GCx R) (a b : ℤ) (hab : a + 1 = b) :
    (C.toCC.d a b).hom = C.d a b hab := by
  apply LinearMap.ext
  intro x
  exact GCx.toCC_d_hom C a b hab x

/-- A coefficient ring homomorphism preserves addition of rectangular matrices. -/
theorem matrixMap_add {S m n : Type} [CommRing S] (ρ : R →+* S) (M N : Matrix m n R) :
    (M + N).map ρ = M.map ρ + N.map ρ := by
  ext a b
  exact map_add ρ (M a b) (N a b)

variable [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
  {I : ℕ → Ideal R} {U : Ultrafilter ℕ}

/-- The reverse maps and both homotopies are retained at the coefficient stages. -/
structure HomotopyEquivStages (C D : ComplexStages I U) where
  forward : MapStages C D
  inverse : MapStages D C
  sourceHom : ∀ (_i : ℕ) (a b : ℤ), b + 1 = a → Matrix (Fin (C.rank b)) (Fin (C.rank a)) R
  targetHom : ∀ (_i : ℕ) (a b : ℤ), b + 1 = a → Matrix (Fin (D.rank b)) (Fin (D.rank a)) R
  sourceIdentity : ∀ a : ℤ, ∀ᶠ i in (U : Filter ℕ), ∀ x y : Fin (C.rank a),
    (inverse.f i a a rfl * forward.f i a a rfl - 1 -
      sourceHom i (a + 1) a rfl * C.d i a (a + 1) rfl -
      C.d i (a - 1) a (by omega) * sourceHom i a (a - 1) (by omega) :
        Matrix (Fin (C.rank a)) (Fin (C.rank a)) R) x y ∈ I i
  targetIdentity : ∀ a : ℤ, ∀ᶠ i in (U : Filter ℕ), ∀ x y : Fin (D.rank a),
    (forward.f i a a rfl * inverse.f i a a rfl - 1 -
      targetHom i (a + 1) a rfl * D.d i a (a + 1) rfl -
      D.d i (a - 1) a (by omega) * targetHom i a (a - 1) (by omega) :
        Matrix (Fin (D.rank a)) (Fin (D.rank a)) R) x y ∈ I i

variable (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)

include hI hU

/-- The first inverse homotopy identity survives as an exact matrix equality. -/
theorem sourceHomotopy_identity {C D : ComplexStages I U} (E : HomotopyEquivStages C D) (a : ℤ) :
    ulimMat U (fun i => E.inverse.f i a a rfl) * ulimMat U (fun i => E.forward.f i a a rfl) =
      ulimMat U (fun i => E.sourceHom i (a + 1) a rfl) * ulimMat U (fun i => C.d i a (a + 1) rfl) +
      ulimMat U (fun i => C.d i (a - 1) a (by omega)) *
        ulimMat U (fun i => E.sourceHom i a (a - 1) (by omega)) + 1 := by
  have hz := ulimMat_eq_zero_of_mem hI hU (E.sourceIdentity a)
  rw [ulimMat_sub, ulimMat_sub, ulimMat_sub, ulimMat_mul, ulimMat_one,
    ulimMat_mul, ulimMat_mul] at hz
  apply eq_of_sub_eq_zero
  convert hz using 1; abel

/-- The second inverse homotopy identity survives on the same ultrafilter. -/
theorem targetHomotopy_identity {C D : ComplexStages I U} (E : HomotopyEquivStages C D) (a : ℤ) :
    ulimMat U (fun i => E.forward.f i a a rfl) * ulimMat U (fun i => E.inverse.f i a a rfl) =
      ulimMat U (fun i => E.targetHom i (a + 1) a rfl) * ulimMat U (fun i => D.d i a (a + 1) rfl) +
      ulimMat U (fun i => D.d i (a - 1) a (by omega)) *
        ulimMat U (fun i => E.targetHom i a (a - 1) (by omega)) + 1 := by
  have hz := ulimMat_eq_zero_of_mem hI hU (E.targetIdentity a)
  rw [ulimMat_sub, ulimMat_sub, ulimMat_sub, ulimMat_mul, ulimMat_one,
    ulimMat_mul, ulimMat_mul] at hz
  apply eq_of_sub_eq_zero
  convert hz using 1; abel

/-- Retained reverse maps and homotopies give an actual homotopy equivalence of the inner complexes. -/
def retainedHomotopyEquiv {C D : ComplexStages I U} (E : HomotopyEquivStages C D) :
    HomotopyEquiv (limitComplex hI hU C).toCC (limitComplex hI hU D).toCC where
  hom := GHom.toCC (limitMap hI hU E.forward)
  inv := GHom.toCC (limitMap hI hU E.inverse)
  homotopyHomInvId := homotopyOfLinearIdentities _ _
    (fun a b hab => Matrix.toLin' (ulimMat U (fun i => E.sourceHom i a b hab))) (by
      intro a
      erw [toCC_d_linear (limitComplex hI hU C) a (a + 1) rfl,
        toCC_d_linear (limitComplex hI hU C) (a - 1) a (by omega)]
      apply LinearMap.ext
      intro x
      change (Fin (C.rank a) → R) at x
      change (ulimMat U (fun i => E.inverse.f i a a rfl)) *ᵥ
          ((ulimMat U (fun i => E.forward.f i a a rfl)) *ᵥ x) =
        (ulimMat U (fun i => E.sourceHom i (a + 1) a rfl)) *ᵥ
          ((ulimMat U (fun i => C.d i a (a + 1) rfl)) *ᵥ x) +
        (ulimMat U (fun i => C.d i (a - 1) a (by omega))) *ᵥ
          ((ulimMat U (fun i => E.sourceHom i a (a - 1) (by omega))) *ᵥ x) + x
      have he := congrArg (fun M : Matrix (Fin (C.rank a)) (Fin (C.rank a)) R => M *ᵥ x)
        (sourceHomotopy_identity hI hU E a)
      simpa only [Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] using he)
  homotopyInvHomId := homotopyOfLinearIdentities _ _
    (fun a b hab => Matrix.toLin' (ulimMat U (fun i => E.targetHom i a b hab))) (by
      intro a
      erw [toCC_d_linear (limitComplex hI hU D) a (a + 1) rfl,
        toCC_d_linear (limitComplex hI hU D) (a - 1) a (by omega)]
      apply LinearMap.ext
      intro x
      change (Fin (D.rank a) → R) at x
      change (ulimMat U (fun i => E.forward.f i a a rfl)) *ᵥ
          ((ulimMat U (fun i => E.inverse.f i a a rfl)) *ᵥ x) =
        (ulimMat U (fun i => E.targetHom i (a + 1) a rfl)) *ᵥ
          ((ulimMat U (fun i => D.d i a (a + 1) rfl)) *ᵥ x) +
        (ulimMat U (fun i => D.d i (a - 1) a (by omega))) *ᵥ
          ((ulimMat U (fun i => E.targetHom i a (a - 1) (by omega))) *ᵥ x) + x
      have he := congrArg (fun M : Matrix (Fin (D.rank a)) (Fin (D.rank a)) R => M *ᵥ x)
        (targetHomotopy_identity hI hU E a)
      simpa only [Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] using he)

variable {k : Type} [Field k]

/-- Retained localization maps specialize after taking their integral coefficient limits. -/
def specializeMap {C D : ComplexStages I U} (ρ : R →+* k) (F : MapStages C D) :
    GHom (specializeComplex hI hU ρ C) (specializeComplex hI hU ρ D) where
  f a b hab := Matrix.toLin' ((ulimMat U (fun i => F.f i a b hab)).map ρ)
  comm a a' b b' hab ha hb ha'b' x := by
    change (Fin (C.rank a) → k) at x
    have he : ulimMat U (fun i => F.f i a' b' ha'b') * ulimMat U (fun i => C.d i a a' ha) =
        ulimMat U (fun i => D.d i b b' hb) * ulimMat U (fun i => F.f i a b hab) := by
      rw [← ulimMat_mul, ← ulimMat_mul]
      exact ulimMat_eq_of_sub_mem hI hU (F.comm a a' b b' hab ha hb ha'b')
    have hs := congrArg (fun M : Matrix (Fin (D.rank b')) (Fin (C.rank a)) R => M.map ρ) he
    rw [Matrix.map_mul, Matrix.map_mul] at hs
    change Matrix.toLin' ((ulimMat U (fun i => F.f i a' b' ha'b')).map ρ)
      (Matrix.toLin' ((ulimMat U (fun i => C.d i a a' ha)).map ρ) x) =
        Matrix.toLin' ((ulimMat U (fun i => D.d i b b' hb)).map ρ)
          (Matrix.toLin' ((ulimMat U (fun i => F.f i a b hab)).map ρ) x)
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hs, Matrix.toLin'_mul, LinearMap.comp_apply]

/-- Retained homotopy inverses survive every fixed-field specialization after the inner limit. -/
def retainedSpecializedHomotopyEquiv {C D : ComplexStages I U} (ρ : R →+* k)
    (E : HomotopyEquivStages C D) :
    HomotopyEquiv (specializeComplex hI hU ρ C).toCC (specializeComplex hI hU ρ D).toCC where
  hom := GHom.toCC (specializeMap hI hU ρ E.forward)
  inv := GHom.toCC (specializeMap hI hU ρ E.inverse)
  homotopyHomInvId := homotopyOfLinearIdentities _ _
    (fun a b hab => Matrix.toLin' ((ulimMat U (fun i => E.sourceHom i a b hab)).map ρ)) (by
      intro a
      erw [toCC_d_linear (specializeComplex hI hU ρ C) a (a + 1) rfl,
        toCC_d_linear (specializeComplex hI hU ρ C) (a - 1) a (by omega)]
      apply LinearMap.ext
      intro x
      change (Fin (C.rank a) → k) at x
      change ((ulimMat U (fun i => E.inverse.f i a a rfl)).map ρ) *ᵥ
          (((ulimMat U (fun i => E.forward.f i a a rfl)).map ρ) *ᵥ x) =
        ((ulimMat U (fun i => E.sourceHom i (a + 1) a rfl)).map ρ) *ᵥ
          (((ulimMat U (fun i => C.d i a (a + 1) rfl)).map ρ) *ᵥ x) +
        ((ulimMat U (fun i => C.d i (a - 1) a (by omega))).map ρ) *ᵥ
          (((ulimMat U (fun i => E.sourceHom i a (a - 1) (by omega))).map ρ) *ᵥ x) + x
      have hs := congrArg (fun M : Matrix (Fin (C.rank a)) (Fin (C.rank a)) R => M.map ρ)
        (sourceHomotopy_identity hI hU E a)
      simp only [Matrix.map_mul, matrixMap_add, Matrix.map_one _ (map_zero ρ) (map_one ρ)] at hs
      have he := congrArg (fun M : Matrix (Fin (C.rank a)) (Fin (C.rank a)) k => M *ᵥ x) hs
      simpa only [Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] using he)
  homotopyInvHomId := homotopyOfLinearIdentities _ _
    (fun a b hab => Matrix.toLin' ((ulimMat U (fun i => E.targetHom i a b hab)).map ρ)) (by
      intro a
      erw [toCC_d_linear (specializeComplex hI hU ρ D) a (a + 1) rfl,
        toCC_d_linear (specializeComplex hI hU ρ D) (a - 1) a (by omega)]
      apply LinearMap.ext
      intro x
      change (Fin (D.rank a) → k) at x
      change ((ulimMat U (fun i => E.forward.f i a a rfl)).map ρ) *ᵥ
          (((ulimMat U (fun i => E.inverse.f i a a rfl)).map ρ) *ᵥ x) =
        ((ulimMat U (fun i => E.targetHom i (a + 1) a rfl)).map ρ) *ᵥ
          (((ulimMat U (fun i => D.d i a (a + 1) rfl)).map ρ) *ᵥ x) +
        ((ulimMat U (fun i => D.d i (a - 1) a (by omega))).map ρ) *ᵥ
          (((ulimMat U (fun i => E.targetHom i a (a - 1) (by omega))).map ρ) *ᵥ x) + x
      have hs := congrArg (fun M : Matrix (Fin (D.rank a)) (Fin (D.rank a)) R => M.map ρ)
        (targetHomotopy_identity hI hU E a)
      simp only [Matrix.map_mul, matrixMap_add, Matrix.map_one _ (map_zero ρ) (map_one ρ)] at hs
      have he := congrArg (fun M : Matrix (Fin (D.rank a)) (Fin (D.rank a)) k => M *ᵥ x) hs
      simpa only [Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] using he)

/-- The retained integral homotopy inverse certifies a quasi-isomorphism of the limit complex. -/
theorem retainedLimit_quasiIso {C D : ComplexStages I U} (E : HomotopyEquivStages C D) :
    QuasiIso (GHom.toCC (limitMap hI hU E.forward)) :=
  (retainedHomotopyEquiv hI hU E).quasiIso_hom

/-- The same certificate gives the fixed-field duality map after specializing the limit. -/
theorem retainedSpecialized_quasiIso {C D : ComplexStages I U} (ρ : R →+* k)
    (E : HomotopyEquivStages C D) : QuasiIso (GHom.toCC (specializeMap hI hU ρ E.forward)) :=
  (retainedSpecializedHomotopyEquiv hI hU ρ E).quasiIso_hom

end RetainedHomotopyInverses

section CoefficientPrecisionTopology

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R]

/-- The inner local cohomology with its coefficient-precision topology, not the product quotient topology. -/
def InnerLimitH1 (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] (U : Ultrafilter ℕ) : Type := CompletedH1 R U

instance innerLimitH1_addCommGroup (U : Ultrafilter ℕ) : AddCommGroup (InnerLimitH1 R U) :=
  inferInstanceAs (AddCommGroup (CompletedH1 R U))

instance innerLimitH1_module (U : Ultrafilter ℕ) : Module R (InnerLimitH1 R U) :=
  inferInstanceAs (Module R (CompletedH1 R U))

/-- Coordinates determine the canonical separated topology on the inner limit. -/
def innerLimitCoords (U : Ultrafilter ℕ) : InnerLimitH1 R U ≃ₗ[R] Coords R :=
  completedEquiv (R := R) U

instance innerLimitH1_topology (U : Ultrafilter ℕ) : TopologicalSpace (InnerLimitH1 R U) :=
  TopologicalSpace.induced (innerLimitCoords (R := R) U) inferInstance

/-- The topological limit is exactly the complete rank-four coefficient module. -/
def innerLimitHomeomorph (U : Ultrafilter ℕ) : InnerLimitH1 R U ≃ₜ Coords R where
  toEquiv := (innerLimitCoords (R := R) U).toEquiv
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    change Continuous fun x : Coords R =>
      innerLimitCoords (R := R) U ((innerLimitCoords (R := R) U).symm x)
    exact (continuous_id : Continuous (@id (Coords R))).congr fun x =>
      (LinearEquiv.apply_symm_apply (innerLimitCoords (R := R) U) x).symm

instance innerLimitH1_compact (U : Ultrafilter ℕ) : CompactSpace (InnerLimitH1 R U) :=
  (innerLimitHomeomorph (R := R) U).symm.compactSpace

instance innerLimitH1_t2 (U : Ultrafilter ℕ) : T2Space (InnerLimitH1 R U) :=
  (innerLimitHomeomorph (R := R) U).symm.t2Space

/-- Addition is continuous for the coefficient-precision topology. -/
instance innerLimitH1_continuousAdd (U : Ultrafilter ℕ) : ContinuousAdd (InnerLimitH1 R U) := by
  refine ⟨?_⟩
  apply continuous_induced_rng.mpr
  change Continuous fun x : InnerLimitH1 R U × InnerLimitH1 R U =>
    innerLimitCoords (R := R) U (x.1 + x.2)
  have h := ((innerLimitHomeomorph (R := R) U).continuous.comp continuous_fst).add
    ((innerLimitHomeomorph (R := R) U).continuous.comp continuous_snd)
  exact h.congr fun x => (map_add (innerLimitCoords (R := R) U) x.1 x.2).symm

instance innerLimitH1_continuousNeg (U : Ultrafilter ℕ) : ContinuousNeg (InnerLimitH1 R U) := by
  refine ⟨?_⟩
  apply continuous_induced_rng.mpr
  change Continuous fun x : InnerLimitH1 R U => innerLimitCoords (R := R) U (-x)
  exact (innerLimitHomeomorph (R := R) U).continuous.neg.congr fun x =>
    (map_neg (innerLimitCoords (R := R) U) x).symm

/-- The coefficient-ring module action is continuous on the topological inner limit. -/
instance innerLimitH1_continuousSMul (U : Ultrafilter ℕ) : ContinuousSMul R (InnerLimitH1 R U) := by
  refine ⟨?_⟩
  apply continuous_induced_rng.mpr
  change Continuous fun x : R × InnerLimitH1 R U => innerLimitCoords (R := R) U (x.1 • x.2)
  have h : Continuous (fun x : R × InnerLimitH1 R U => x.1 • innerLimitCoords (R := R) U x.2) :=
    (continuous_fst : Continuous fun x : R × InnerLimitH1 R U => x.1).smul
      ((innerLimitHomeomorph (R := R) U).continuous.comp continuous_snd)
  exact h.congr fun x => (map_smul (innerLimitCoords (R := R) U) x.1 x.2).symm

/-- The coefficient-stage quotient feeds the separated topological inner-limit object. -/
def stageToInnerLimitEquiv {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
    (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite) :
    CompletedStageH1 hI hU ≃ₗ[R] InnerLimitH1 R U :=
  (completedStageEquiv hI hU).trans (innerLimitCoords (R := R) U).symm

/-- The finite plane in the separated topological inner-limit object. -/
def innerFinitePlane (U : Ultrafilter ℕ) : Submodule R (InnerLimitH1 R U) :=
  (finiteAxis R).comap (innerLimitCoords (R := R) U).toLinearMap

/-- The singular plane in the separated topological inner-limit object. -/
def innerSingularPlane (U : Ultrafilter ℕ) : Submodule R (InnerLimitH1 R U) :=
  (singularAxis R).comap (innerLimitCoords (R := R) U).toLinearMap

/-- The topological finite plane has the same rank-two integral coordinates. -/
def innerFiniteEquiv (U : Ultrafilter ℕ) : innerFinitePlane (R := R) U ≃ₗ[R] Vec2 R :=
  completedFiniteEquiv (R := R) U

/-- The topological singular plane has the same rank-two integral coordinates. -/
def innerSingularEquiv (U : Ultrafilter ℕ) : innerSingularPlane (R := R) U ≃ₗ[R] Vec2 R :=
  completedSingularEquiv (R := R) U

/-- The inner-limit planes have zero intersection. -/
theorem innerPlanes_inf (U : Ultrafilter ℕ) :
    innerFinitePlane (R := R) U ⊓ innerSingularPlane (R := R) U = ⊥ := by
  ext x
  constructor
  · rintro ⟨hf, hs⟩
    rw [Submodule.mem_bot]
    apply (innerLimitCoords (R := R) U).injective
    rw [map_zero]
    exact Prod.ext (mem_singularAxis.mp hs) (mem_finiteAxis.mp hf)
  · intro hx
    rw [Submodule.mem_bot] at hx
    rw [hx]
    exact Submodule.zero_mem _

/-- The inner-limit planes span the entire object. -/
theorem innerPlanes_sup (U : Ultrafilter ℕ) :
    innerFinitePlane (R := R) U ⊔ innerSingularPlane (R := R) U = ⊤ := by
  apply top_unique
  intro x _
  let e := innerLimitCoords (R := R) U
  have hf : e.symm ((e x).1, 0) ∈ innerFinitePlane U := by
    change e (e.symm ((e x).1, 0)) ∈ finiteAxis R
    rw [LinearEquiv.apply_symm_apply, mem_finiteAxis]
  have hs : e.symm (0, (e x).2) ∈ innerSingularPlane U := by
    change e (e.symm (0, (e x).2)) ∈ singularAxis R
    rw [LinearEquiv.apply_symm_apply, mem_singularAxis]
  have he : x = e.symm ((e x).1, 0) + e.symm (0, (e x).2) := by
    apply e.injective
    rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    ext <;> simp
  rw [he]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hf) (Submodule.mem_sup_right hs)

/-- The finite plane is closed for the coefficient-precision topology. -/
theorem innerFinitePlane_closed (U : Ultrafilter ℕ) : IsClosed (innerFinitePlane (R := R) U : Set (InnerLimitH1 R U)) := by
  have h := (isClosed_singleton : IsClosed ({0} : Set (Vec2 R))).preimage
    (innerLimitHomeomorph (R := R) U).continuous.snd
  convert h using 1
  ext x
  exact mem_finiteAxis

/-- The singular plane is closed for the coefficient-precision topology. -/
theorem innerSingularPlane_closed (U : Ultrafilter ℕ) : IsClosed (innerSingularPlane (R := R) U : Set (InnerLimitH1 R U)) := by
  have h := (isClosed_singleton : IsClosed ({0} : Set (Vec2 R))).preimage
    (innerLimitHomeomorph (R := R) U).continuous.fst
  convert h using 1
  ext x
  exact mem_singularAxis

omit [T2Space R] in
/-- Membership at one open coefficient precision is exactly eventual membership along U. -/
theorem ulim_mem_iff (J : Ideal R) (hJ : IsOpen (J : Set R)) (U : Ultrafilter ℕ) (x : ℕ → R) :
    ulim U x ∈ J ↔ ∀ᶠ i in (U : Filter ℕ), x i ∈ J := by
  have he := eventually_sub_ulim_mem hJ U x
  constructor
  · intro hx
    filter_upwards [he] with i hi
    simpa using J.add_mem hi hx
  · intro hx
    obtain ⟨i, hi, hsub⟩ := (hx.and he).exists
    have hmem := J.sub_mem hi hsub
    simpa using hmem

/-- The coordinate topology records the retained coefficient precision on both planes. -/
theorem coordLimit_mem_precision (J : Ideal R) (hJ : IsOpen (J : Set R))
    (U : Ultrafilter ℕ) (x : ℕ → Coords R) :
    ((∀ a, (coordLimit U x).1 a ∈ J) ∧ (∀ a, (coordLimit U x).2 a ∈ J)) ↔
      ∀ᶠ i in (U : Filter ℕ), (∀ a, (x i).1 a ∈ J) ∧ (∀ a, (x i).2 a ∈ J) := by
  constructor
  · rintro ⟨hf, hs⟩
    exact (Filter.eventually_all.mpr fun a => (ulim_mem_iff J hJ U _).mp (hf a)).and
      (Filter.eventually_all.mpr fun a => (ulim_mem_iff J hJ U _).mp (hs a))
  · intro h
    exact ⟨fun a => (ulim_mem_iff J hJ U _).mpr (h.mono fun _ hi => hi.1 a),
      fun a => (ulim_mem_iff J hJ U _).mpr (h.mono fun _ hi => hi.2 a)⟩

end CoefficientPrecisionTopology

section TopologicalTateBridge

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}
  {α : GKS K S →* Lambdaˣ} [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- The separated inner local limit has exactly the Tate coefficient topology on both planes. -/
def innerLimitTateHomeomorph (U : Ultrafilter ℕ) :
    InnerLimitH1 Lambda U ≃ₜ TLam K S W α × TLam K S W α :=
  (innerLimitHomeomorph (R := Lambda) U).trans
    ((tlamHomeomorph (K := K) (S := S) (W := W) (α := α)).symm.prodCongr
      (tlamHomeomorph (K := K) (S := S) (W := W) (α := α)).symm)

/-- Fixed-P scalar extension of the separated topological object has the genuine fibre coefficients. -/
def innerLimitFibreEquiv (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime] :
    TensorProduct Lambda (ResAt P) (InnerLimitH1 Lambda U) ≃ₗ[ResAt P]
      InnerFibreH1 (K := K) (S := S) (W := W) (α := α) P :=
  (LinearEquiv.baseChange Lambda (ResAt P) _ _
    ((innerLimitCoords (R := Lambda) U).trans (completedEquiv (R := Lambda) U).symm)).trans
    (completedFibreEquiv (K := K) (S := S) (W := W) (α := α) U P)

end TopologicalTateBridge

section FixedFibreLimitContract

open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
  (P : Ideal Lambda) [P.IsPrime] (C : ComplexStages (R := Lambda) stageIdeal U)

/-- The fixed-P global object is obtained from the integral coefficient-stage limit, in that order. -/
abbrev fibreLimitGlobal : GCx (ResAt P) :=
  specializeComplex stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) C

variable (res : GHom (fibreLimitGlobal U hU P C) (splitLocalComplex (ResAt P)))

/-- Producer contract: fixed-P perfect-complex duality and residue compatibility for the retained limit diagram. -/
def FibreInnerLimitPairingCertificate (ε σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P)) : Prop :=
  LimitPairingCertificate (fibreLimitGlobal U hU P C) res ε σ J

/-- The precise fixed-P inner-limit duality statement needed by switching. -/
def FibreInnerLimitDuality (ε σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P))
    (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1) : Prop :=
  LimitSwitchDuality (fibreLimitGlobal U hU P C) res ε σ J hε hσ hJ

/-- The complex-level producer contract yields the exact connecting-map adjunction. -/
theorem fibreInnerLimitDuality_of_certificate (ε σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P))
    (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (H : FibreInnerLimitPairingCertificate U hU P C res ε σ J) :
    FibreInnerLimitDuality U hU P C res ε σ J hε hσ hJ :=
  limitDuality_of_pairingCertificate (fibreLimitGlobal U hU P C) res ε σ J hε hσ hJ H

variable {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}

/-- The existing nonquadratic step at the fixed height-one residue map, using the inner-limit sides. -/
def fibreLimitNonquadStep (S₀ S₁ : TwoTermStage ι) (ε σ : ResAt P)
    (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (hdual : FibreInnerLimitDuality U hU P C res ε σ J hε hσ hJ)
    (hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
      (limitRelaxed (fibreLimitGlobal U hU P C) res).U)
    (φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) res).Dside).toCC.homology 1 ≃ₗ[ResAt P]
      fiberH1 (resAt P) S₀)
    (φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C) res).Dside).toCC.homology 1 ≃ₗ[ResAt P]
      fiberH1 (resAt P) S₁) : QuasiNonquadStep (resAt P) S₀ S₁ :=
  limitNonquadStep (fibreLimitGlobal U hU P C) res (resAt P) S₀ S₁ ε σ J hε hσ hJ hdual hdet φ φ'

end FixedFibreLimitContract

section ActualLimitingTameComplex

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}

/-- The limiting unramified tame complex uses the limiting Frobenius and residue-size operators. -/
def limitTameComplex (D : DerivativeMatrices I U) : CochainComplex (ModuleCat R) ℤ :=
  tameComplex (innerFiniteOp D) 0 (innerSingularOp D) (by simp)

variable (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)

include hI hU

/-- The finite-coordinate boundary of the limiting tame cochain complex is zero. -/
theorem limitTame_d01_zero (D : DerivativeMatrices I U) : (limitTameComplex D).d 0 1 = 0 := by
  change ModuleCat.ofHom (tameD0 (innerFiniteOp D) (0 : Module.End R (Vec2 R))) = 0
  rw [innerFiniteOp_zero hI hU D]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The singular-coordinate differential of that same complex is zero. -/
theorem limitTame_d12_zero (D : DerivativeMatrices I U) : (limitTameComplex D).d 1 2 = 0 := by
  change ModuleCat.ofHom (tameD1 (0 : Module.End R (Vec2 R)) (innerSingularOp D)) = 0
  rw [innerSingularOp_zero hI hU D]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Coords R at x
  change tameD1 (0 : Module.End R (Vec2 R)) 0 x = 0
  simp only [tameD1_apply, LinearMap.zero_apply, neg_zero, zero_add]

/-- The rank-four coordinates are the actual first homology of the limiting tame complex. -/
def limitTameH1Equiv (D : DerivativeMatrices I U) :
    (limitTameComplex D).homology 1 ≃ₗ[R] Coords R :=
  (((limitTameComplex D).isoHomologyπ 0 1 (by simp) (limitTame_d01_zero hI hU D)).symm ≪≫
    (limitTameComplex D).iCyclesIso 1 2 (by simp) (limitTame_d12_zero hI hU D)).toLinearEquiv

/-- The limit coker/kernel model is canonically identified with that actual cochain homology. -/
def innerCokerKerTameEquiv (D : DerivativeMatrices I U) :
    InnerCokerKer D ≃ₗ[R] (limitTameComplex D).homology 1 :=
  (innerCokerKerEquiv hI hU D).trans (limitTameH1Equiv hI hU D).symm

/-- The coefficient-stage quotient construction and the limiting tame cochain construction agree. -/
def coefficientStageTameH1Equiv (D : DerivativeMatrices I U) :
    CompletedStageH1 hI hU ≃ₗ[R] (limitTameComplex D).homology 1 :=
  (completedStageEquiv hI hU).trans (limitTameH1Equiv hI hU D).symm

/-- The separated coefficient-topological object is the same local first cohomology. -/
def topologicalLimitTameH1Equiv (D : DerivativeMatrices I U) :
    InnerLimitH1 R U ≃ₗ[R] (limitTameComplex D).homology 1 :=
  (innerLimitCoords (R := R) U).trans (limitTameH1Equiv hI hU D).symm

end ActualLimitingTameComplex

/-! ## Checked declaration types and axiom footprints -/

set_option pp.universes true
set_option pp.fullNames true

end ZInQ.Contrib.RC53Assist.InnerLimit
