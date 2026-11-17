import Research.DerivativeSwitch.ConjugateLocalTransport
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The local transport identity on Mathlib's actual first group cohomology

These maps descend through `groupCohomology.H1`, the cohomology of the
inhomogeneous cochain complex. The conjugate carrier uses the pulled-back
representation, which need not equal the original representation.
For the finite arithmetic application, continuity and passage to a common
finite quotient are justified separately in the source application note.
-/

namespace Research.DerivativeSwitch.ConjugateLocalTransport

open groupCohomology

universe u
variable {R G V : Type u} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V]

noncomputable section

/-- Surjectivity of the actual cochain-complex cohomology projection. -/
theorem h1_projection_surjective (rho : G →* Module.End R V) :
    Function.Surjective (H1π (Rep.of rho)).hom := by
  intro z
  exact H1_induction_on z (fun p => ⟨p, rfl⟩)

def cocycleEvaluation (rho : G →* Module.End R V) (x : G) :
    cocycles₁ (Rep.of rho) →ₗ[R] V where
  toFun p := p x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cocycleEvaluation_kills_kernel (rho : G →* Module.End R V)
    (x : G) (hx : rho x = 1) :
    LinearMap.ker (H1π (Rep.of rho)).hom ≤ LinearMap.ker (cocycleEvaluation rho x) := by
  intro p hp
  have hb := (H1π_eq_zero_iff p).mp (LinearMap.mem_ker.mp hp)
  obtain ⟨v, hv⟩ := hb
  have h := congrFun hv x
  change rho x v - v = p x at h
  change p x = 0
  simpa [hx] using h.symm

/-- Evaluation at a trivially acting element descends to genuine H¹. -/
def h1Evaluation (rho : G →* Module.End R V) (x : G) (hx : rho x = 1) :
    H1 (Rep.of rho) →ₗ[R] V :=
  (H1π (Rep.of rho)).hom.liftOfSurjective (h1_projection_surjective rho)
    ⟨cocycleEvaluation rho x, cocycleEvaluation_kills_kernel rho x hx⟩

@[simp]
theorem h1Evaluation_projection (rho : G →* Module.End R V) (x : G)
    (hx : rho x = 1) (p : cocycles₁ (Rep.of rho)) :
    h1Evaluation rho x hx (H1π (Rep.of rho) p) = p x := by
  exact LinearMap.equivOfSurjective_apply _ _

/-- Pullback of cocycles changes the coefficient representation. -/
def cocyclePullback (rho : G →* Module.End R V) (gamma : G →* G) :
    cocycles₁ (Rep.of rho) →ₗ[R] cocycles₁ (Rep.of (rho.comp gamma)) where
  toFun p := ⟨fun x => p (gamma x), (mem_cocycles₁_iff _).mpr (by
    intro g h
    simpa using (mem_cocycles₁_iff _).mp p.2 (gamma g) (gamma h))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cocyclePullback_kills_kernel (rho : G →* Module.End R V) (gamma : G →* G) :
    LinearMap.ker (H1π (Rep.of rho)).hom ≤
      LinearMap.ker ((H1π (Rep.of (rho.comp gamma))).hom.comp (cocyclePullback rho gamma)) := by
  intro p hp
  have hb := (H1π_eq_zero_iff p).mp (LinearMap.mem_ker.mp hp)
  obtain ⟨v, hv⟩ := hb
  apply (H1π_eq_zero_iff _).mpr
  refine ⟨v, ?_⟩
  funext x
  exact congrFun hv (gamma x)

/-- Pullback on the actual H¹ groups, with the two coefficient systems explicit. -/
def h1Pullback (rho : G →* Module.End R V) (gamma : G →* G) :
    H1 (Rep.of rho) →ₗ[R] H1 (Rep.of (rho.comp gamma)) :=
  (H1π (Rep.of rho)).hom.liftOfSurjective (h1_projection_surjective rho)
    ⟨(H1π (Rep.of (rho.comp gamma))).hom.comp (cocyclePullback rho gamma),
      cocyclePullback_kills_kernel rho gamma⟩

@[simp]
theorem h1Pullback_projection (rho : G →* Module.End R V) (gamma : G →* G)
    (p : cocycles₁ (Rep.of rho)) :
    h1Pullback rho gamma (H1π (Rep.of rho) p) =
      H1π (Rep.of (rho.comp gamma)) (cocyclePullback rho gamma p) := by
  exact LinearMap.equivOfSurjective_apply _ _

namespace LocalData

variable {H : Subgroup G} {T : G →* Module.End R V} {alpha : H →* Rˣ}
  (D : LocalData H T alpha)

/-- Finite and singular coordinates of the actual first cohomology class. -/
def h1Coordinates : H1 (Rep.of (twist H T alpha)) →ₗ[R] V × V :=
  (h1Evaluation _ D.finiteGenerator D.twist_finite).prod
    (h1Evaluation _ D.inertia D.twist_inertia)

@[simp]
theorem h1Coordinates_projection (p : cocycles₁ (Rep.of (twist H T alpha))) :
    D.h1Coordinates (H1π (Rep.of (twist H T alpha)) p) = D.coordinates p := by
  exact Prod.ext (h1Evaluation_projection _ _ _ p) (h1Evaluation_projection _ _ _ p)

variable [H.Normal]

/-- Coordinates on conjugate H¹. No identification of coefficient systems is assumed. -/
def conjugateH1Coordinates :
    H1 (Rep.of ((twist H T alpha).comp (conjugation H D.tau))) →ₗ[R] V × V :=
  (h1Evaluation _ D.finiteGenerator D.twist_conjugation_finite).prod
    (h1Evaluation _ D.inertia D.twist_conjugation_inertia)

@[simp]
theorem conjugateH1Coordinates_projection
    (p : cocycles₁ (Rep.of ((twist H T alpha).comp (conjugation H D.tau)))) :
    D.conjugateH1Coordinates
        (H1π (Rep.of ((twist H T alpha).comp (conjugation H D.tau))) p) =
      D.coordinates p := by
  exact Prod.ext (h1Evaluation_projection _ _ _ p) (h1Evaluation_projection _ _ _ p)

/-- An actual source-to-interface map: the derived shared-unit transport holds
on Mathlib's H¹, not merely on a chosen representative or abstract class carrier. -/
theorem h1_local_transport (hEll : (D.ell : R) = -1)
    (z : H1 (Rep.of (twist H T alpha))) :
    D.conjugateH1Coordinates
        (h1Pullback (twist H T alpha) (conjugation H D.tau) z) =
      ((D.transportUnit : R) • (D.h1Coordinates z).1,
       -((D.transportUnit : R) • (D.h1Coordinates z).2)) := by
  induction z using H1_induction_on with
  | h p =>
    rw [h1Pullback_projection, D.conjugateH1Coordinates_projection,
      D.h1Coordinates_projection]
    apply D.coordinates_rawConjugate_of_neg_one hEll p
    intro g h
    have hp := (mem_cocycles₁_iff _).mp p.2 g h
    change p.1 (g * h) = (twist H T alpha) g (p.1 h) + p.1 g at hp
    change p.1 (g * h) = p.1 g + (twist H T alpha) g (p.1 h)
    exact hp.trans (add_comm _ _)

end LocalData

end

end Research.DerivativeSwitch.ConjugateLocalTransport
