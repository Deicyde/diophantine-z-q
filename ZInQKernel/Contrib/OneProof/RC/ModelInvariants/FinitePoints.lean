module

public import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.FiniteGroup
public import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.IntegralPoints

/-! # Geometric points of an affine finite-group quotient -/

@[expose] public section

namespace RC.ModelInvariants

open scoped Pointwise TensorProduct

variable {R S G k : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [Field k] [Algebra R k]

/-- Every geometric point of the finite-group invariant algebra lifts to the original algebra. -/
theorem fixedPoints_restrict_surjective [Finite G] [IsAlgClosed k] :
    Function.Surjective (fun f : S →ₐ[R] k =>
      f.comp (FixedPoints.subalgebra R S G).val) := by
  let := fixedPoints_isIntegral (R := R) (S := S) (G := G)
  exact liftIntegralPoint Subtype.val_injective

/-- The action on points is by precomposition with the inverse algebra automorphism. -/
instance pointAction : MulAction G (S →ₐ[R] k) where
  smul g f := f.comp (MulSemiringAction.toAlgHom R S g⁻¹)
  one_smul f := AlgHom.ext fun x => by
    change f ((1 : G)⁻¹ • x) = f x
    rw [inv_one, one_smul]
  mul_smul g t f := AlgHom.ext fun x => by
    change f ((g * t)⁻¹ • x) = f (t⁻¹ • g⁻¹ • x)
    rw [mul_inv_rev, mul_smul]

theorem pointAction_apply (g : G) (f : S →ₐ[R] k) (x : S) :
    (g • f) x = f (g⁻¹ • x) := rfl

private theorem fieldPoint_eq_of_ker_eq {T : Type*} [CommRing T] [Algebra k T]
    {f g : T →ₐ[k] k} (h : RingHom.ker f.toRingHom = RingHom.ker g.toRingHom) : f = g := by
  ext x
  have he : x - algebraMap k T (f x) ∈ RingHom.ker f.toRingHom := by
    simp
  rw [h, RingHom.mem_ker] at he
  change g (x - algebraMap k T (f x)) = 0 at he
  rw [map_sub, g.commutes] at he
  exact (sub_eq_zero.mp he).symm

private theorem fieldPoint_ker_smul {T : Type*} [CommRing T] [Algebra k T]
    [MulSemiringAction G T] [SMulCommClass G k T] (g : G) (f : T →ₐ[k] k) :
    RingHom.ker (g • f : T →ₐ[k] k).toRingHom = g • RingHom.ker f.toRingHom := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, RingHom.mem_ker, RingHom.mem_ker]
  rfl

/-- Two points with the same restriction to the invariant algebra differ by a group element. -/
theorem fixedPoints_restrict_eq_iff [Fintype G] (h : IsUnit (Fintype.card G : R))
    (f g : S →ₐ[R] k) :
    f.comp (FixedPoints.subalgebra R S G).val = g.comp (FixedPoints.subalgebra R S G).val ↔
      ∃ a : G, a • f = g := by
  constructor
  · intro he
    let lift := Algebra.TensorProduct.liftEquivRight R k S k
    let F := lift f
    let H := lift g
    let V := FixedPoints.subalgebra k (k ⊗[R] S) G
    have hres : F.comp V.val = H.comp V.val := by
      let e := fixedPointsBaseChange (S := S) k h
      have hall : (F.comp V.val).comp e.toAlgHom = (H.comp V.val).comp e.toAlgHom := by
        apply Algebra.TensorProduct.ext'
        intro a x
        change a * f x = a * g x
        rw [show f x = g x from AlgHom.congr_fun he x]
      ext x : 1
      obtain ⟨y, rfl⟩ := e.surjective x
      exact AlgHom.congr_fun hall y
    let p := RingHom.ker F.toRingHom
    let q := RingHom.ker H.toRingHom
    let : p.IsPrime := RingHom.ker_isPrime _
    let : q.IsPrime := RingHom.ker_isPrime _
    have hpq : p.under V = q.under V := by
      change Ideal.comap V.val.toRingHom p = Ideal.comap V.val.toRingHom q
      rw [RingHom.comap_ker, RingHom.comap_ker]
      exact congrArg (fun u : V →ₐ[k] k => RingHom.ker u.toRingHom) hres
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.exists_smul_of_under_eq V (k ⊗[R] S) G p q hpq
    have hag : (a • F : (k ⊗[R] S) →ₐ[k] k) = H :=
      fieldPoint_eq_of_ker_eq ((fieldPoint_ker_smul a F).trans ha.symm)
    refine ⟨a, AlgHom.ext fun x => ?_⟩
    have hx := AlgHom.congr_fun hag (1 ⊗ₜ[R] x)
    simpa [pointAction_apply, scalarExtension_smul_tmul, F, H, lift] using hx
  · rintro ⟨a, rfl⟩
    exact AlgHom.ext fun x => by
      change f x = f (a⁻¹ • (x : S))
      rw [x.property a⁻¹]

/-- Restriction identifies the orbit quotient of geometric points with the points of the
invariant algebra. -/
noncomputable def fixedPointsOrbitEquiv [Fintype G] [IsAlgClosed k]
    (h : IsUnit (Fintype.card G : R)) :
    MulAction.orbitRel.Quotient G (S →ₐ[R] k) ≃ (FixedPoints.subalgebra R S G →ₐ[R] k) := by
  let restrict : MulAction.orbitRel.Quotient G (S →ₐ[R] k) →
      (FixedPoints.subalgebra R S G →ₐ[R] k) := Quotient.lift
    (fun f : S →ₐ[R] k => f.comp (FixedPoints.subalgebra R S G).val)
    (fun f g hfg => ((fixedPoints_restrict_eq_iff h g f).2 (MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hfg))).symm)
  refine Equiv.ofBijective restrict ⟨?_, ?_⟩
  · intro x y
    induction x using Quotient.inductionOn with
    | _ f =>
        induction y using Quotient.inductionOn with
        | _ g =>
            intro he
            exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2
              ((fixedPoints_restrict_eq_iff h g f).1 he.symm)))
  · intro z
    obtain ⟨f, hf⟩ := fixedPoints_restrict_surjective z
    exact ⟨Quotient.mk _ f, hf⟩

theorem fixedPointsOrbitEquiv_mk [Fintype G] [IsAlgClosed k]
    (h : IsUnit (Fintype.card G : R)) (f : S →ₐ[R] k) :
    fixedPointsOrbitEquiv h (Quotient.mk _ f) = f.comp (FixedPoints.subalgebra R S G).val := rfl

#print axioms fixedPoints_restrict_surjective
#print axioms pointAction
#print axioms pointAction_apply
#print axioms fieldPoint_eq_of_ker_eq
#print axioms fieldPoint_ker_smul
#print axioms fixedPoints_restrict_eq_iff
#print axioms fixedPointsOrbitEquiv
#print axioms fixedPointsOrbitEquiv_mk

end RC.ModelInvariants
