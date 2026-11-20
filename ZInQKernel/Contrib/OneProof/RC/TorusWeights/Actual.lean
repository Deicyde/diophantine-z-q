import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Norm
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Family
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-! The weights on individual orbits of the actual (O.7) stage. -/

noncomputable section

open scoped Quaternion NumberField nonZeroDivisors
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.TorusWeights

open Eichler Visibility Visibility.ThetaStage O7Actual

section Adelic

variable {O : Type} [CommRing O] {a b : ℚ} {R : Order a b} {hstar : ℤ}

/-- Read the local Schwartz factors at a finite set of primes containing
the ramified character primes. Nonzero local values are fixed character
values or signs (tex 8495–8578, 9325–9327). -/
structure SchwartzFactors (O : Type) [CommRing O] (C : NormFactors R hstar) where
  primes : Finset Adelic.Prime
  ramified : ∀ p : Adelic.Prime, p.val ∣ hstar.natAbs → p ∈ primes
  value : (p : Adelic.Prime) → Bp p.val a b → O
  covariance : ∀ p ∈ primes, ∀ (u : Adelic.localUnits R p) (x : Bp p.val a b),
    value p ((↑u.val⁻¹ : Bp p.val a b) * x * (u.val : Bp p.val a b)) =
      value p x * (((C.atPrime p (localNrd p u.val))⁻¹ : ℤˣ) : ℤ)
  local_order : ∀ p ∈ primes, ∀ x, value p x ≠ 0 →
    ∃ j : ℕ, value p x ^ (2 ^ j : ℕ) = 1

/-- Compute a local vector in the right frame z, including its rational
input x. This is the argument of the Schwartz factor in (O.4). -/
def inFrame (z : Adelic.FiniteUnits R) (x : B a b) (p : Adelic.Prime) : Bp p.val a b :=
  (↑(z.val p)⁻¹ : Bp p.val a b) * toLocal p.val x * (z.val p : Bp p.val a b)

def SchwartzFactors.eval {C : NormFactors R hstar} (W : SchwartzFactors O C)
    (z : Adelic.FiniteUnits R) (x : B a b) : O :=
  ∏ p ∈ W.primes, W.value p (inFrame z x p)

/-- The global character of an order unit uses exactly the local factors
in the Schwartz covariance (tex 8571–8578). -/
theorem NormFactors.rightProduct (C : NormFactors R hstar) (W : SchwartzFactors O C)
    (r : Adelic.integralUnits R) :
    C.character r.val = ∏ p ∈ W.primes, C.atPrime p (localNrd p (r.val.val p)) := by
  classical
  let f : ℕ → ℤˣ := fun p => if hp : p.Prime then
    C.atPrime ⟨p, hp⟩ (localNrd ⟨p, hp⟩ (r.val.val ⟨p, hp⟩)) else 1
  have hs : Function.mulSupport f ⊆ ↑(W.primes.image Subtype.val) := by
    intro p hp
    by_contra hm
    apply hp
    by_cases hP : p.Prime
    · let _ : Fact p.Prime := ⟨hP⟩
      have hw : (⟨p, hP⟩ : Adelic.Prime) ∉ W.primes :=
        fun h => hm (Finset.mem_image.mpr ⟨⟨p, hP⟩, h, rfl⟩)
      have hu := C.unitValuation ⟨p, hP⟩ ⟨r.val.val ⟨p, hP⟩, r.prop ⟨p, hP⟩⟩
      change Padic.valuation (localNrd ⟨p, hP⟩ (r.val.val ⟨p, hP⟩) : ℚ_[p]) = 0 at hu
      have hh := C.unramified ⟨p, hP⟩ (fun h => hw (W.ramified _ h))
        _ (by rw [hu])
      dsimp [f]
      rw [dite_eq_left hP]
      apply Units.ext
      simpa only [hu, Int.toNat_zero, pow_zero, Units.val_one] using hh
    · simp [f, hP]
  calc
    C.character r.val = ∏ᶠ p, f p := C.product _
    _ = ∏ p ∈ W.primes.image Subtype.val, f p := finprod_eq_prod_of_mulSupport_subset _ hs
    _ = _ := by
      rw [Finset.prod_image (fun _ _ _ _ h => Subtype.ext h)]
      apply Finset.prod_congr rfl
      intro p _
      simp only [f, dite_eq_left p.prop]

/-- The product of nonzero local Schwartz values has two-power order. -/
theorem SchwartzFactors.eval_order {C : NormFactors R hstar} (W : SchwartzFactors O C)
    (z : Adelic.FiniteUnits R) (x : B a b) (h : W.eval z x ≠ 0) :
    ∃ j : ℕ, W.eval z x ^ (2 ^ j : ℕ) = 1 := by
  classical
  let f := fun p => W.value p (inFrame z x p)
  have hlocal : ∀ p ∈ W.primes, ∃ j : ℕ, f p ^ (2 ^ j : ℕ) = 1 := by
    intro p hp
    exact W.local_order p hp _ (fun hz => h (Finset.prod_eq_zero hp hz))
  have hprod (S : Finset Adelic.Prime)
      (hS : ∀ p ∈ S, ∃ j : ℕ, f p ^ (2 ^ j : ℕ) = 1) :
      ∃ j : ℕ, (∏ p ∈ S, f p) ^ (2 ^ j : ℕ) = 1 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert p T hp ih =>
      rw [Finset.prod_insert hp]
      exact twoPower_mul (hS p (Finset.mem_insert_self _ _))
        (ih (fun q hq => hS q (Finset.mem_insert_of_mem hq)))
  exact hprod W.primes hlocal

/-- The order assertion for the norm base uses that the character is
quadratic (tex 9325–9327). -/
theorem sign_square (v : ℤˣ) : ((v : ℤ) : O) ^ 2 = 1 := by
  rcases Int.isUnit_iff.mp v.isUnit with h | h <;> simp [h]

set_option maxHeartbeats 800000 in
/-- If the torus component centralizes x and the actual frame is
q * a * z * r, the Schwartz argument differs by conjugation by r only.
The same r remains on the right in the norm computation. -/
theorem frame_transport (z a₀ : Adelic.FiniteUnits R) (q : (B a b)ˣ)
    (r : Adelic.integralUnits R) (x : B a b)
    (h : ∀ p : Adelic.Prime, Commute (a₀.val p : Bp p.val a b) (toLocal p.val x))
    (p : Adelic.Prime) :
    inFrame (Adelic.diagonal R q * (a₀ * z) * r.val)
        ((q : B a b) * x * (↑q⁻¹ : B a b)) p =
      (↑(r.val.val p)⁻¹ : Bp p.val a b) * inFrame z x p * (r.val.val p : Bp p.val a b) := by
  let q' := Units.map (toLocal p.val).toMonoidHom q
  let a' := a₀.val p
  let z' := z.val p
  let r' := r.val.val p
  change (↑(q' * (a' * z') * r')⁻¹ : Bp p.val a b) *
    toLocal p.val ((q : B a b) * x * (↑q⁻¹ : B a b)) * (↑(q' * (a' * z') * r') : Bp p.val a b) =
    (↑r'⁻¹ : Bp p.val a b) * ((↑z'⁻¹ : Bp p.val a b) * toLocal p.val x * (z' : Bp p.val a b)) * (r' : Bp p.val a b)
  have hq : toLocal p.val (↑q⁻¹ : B a b) = (↑q'⁻¹ : Bp p.val a b) := by
    rw [← map_inv]
    rfl
  simp only [map_mul, hq, mul_inv_rev, Units.val_mul]
  have ha : (↑a'⁻¹ : Bp p.val a b) * toLocal p.val x * (a' : Bp p.val a b) = toLocal p.val x := by
    rw [mul_assoc, ← (h p).eq, ← mul_assoc, Units.inv_mul, one_mul]
  calc
    _ = (↑r'⁻¹ : Bp p.val a b) *
        ((↑z'⁻¹ : Bp p.val a b) * ((↑a'⁻¹ : Bp p.val a b) * toLocal p.val x * (a' : Bp p.val a b)) *
          (z' : Bp p.val a b)) * (r' : Bp p.val a b) := by
      have hq' : toLocal p.val (q : B a b) = (q' : Bp p.val a b) := rfl
      simp only [hq', mul_assoc, Units.inv_mul_cancel_left]
    _ = _ := by rw [ha]

end Adelic

section Actual

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}
variable {F : Type} [Field F] [NumberField F]

abbrev ActualOrder (s : StageAt O N M hN m) := Adelic.levelOrder s.ell s.mod_four N hN

abbrev actualIndex (s : StageAt O N M hN m) (D : ℤ) : ℚ :=
  (((s.weights.m : ℤ) * D : ℤ) : ℚ)

/-- The unweighted adelic realization of the given orientation fibers:
a rational embedding, a frame for each tuple, and a finite idele for
each class. The presentation concerns the orbit, so it does not prescribe
the chosen quotient representative. -/
structure TorusParametrization (s : StageAt O N M hN m) (D : ℤ)
    (Q : QuadraticBasis F (D * -(s.weights.m : ℤ)))
    (A : OrbitFibers s.visibility (actualIndex s D) N.primeFactors.card (ClassGroup (𝓞 F))) where
  embedding : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))
  embedIdeles : (FiniteAdeleRing (𝓞 F) F)ˣ →* Adelic.FiniteUnits (ActualOrder s)
  base : Orientations N.primeFactors.card → Adelic.FiniteUnits (ActualOrder s)
  idele : ClassGroup (𝓞 F) → (FiniteAdeleRing (𝓞 F) F)ˣ
  idele_class : ∀ c, toClassGroup (𝓞 F) F (idele c) = c
  centralizes : ∀ (a₀ : (FiniteAdeleRing (𝓞 F) F)ˣ) (p : Adelic.Prime),
    Commute ((embedIdeles a₀).val p : Bp p.val (-1) (-(s.ell : ℚ)))
      (toLocal p.val (embedding (Q.model QuadraticAlgebra.omega)))
  presents : ∀ t c, ∃ q : (B (-1) (-(s.ell : ℚ)))ˣ,
    (Eichler.representative (zc A.param (t, c))).val =
      (Adelic.fromAdelic (embedIdeles (idele c) * base t)).val.translate q ∧
    ∃ x : s.visibility.supp (zc A.param (t, c)) (actualIndex s D),
      (x : B (-1) (-(s.ell : ℚ))) = (q : B (-1) (-(s.ell : ℚ))) *
        embedding (Q.model QuadraticAlgebra.omega) * (↑q⁻¹ : B (-1) (-(s.ell : ℚ))) ∧
      Quotient.mk _ x = (A.param (t, c)).2

variable {s : StageAt O N M hN m} {D : ℤ}
variable {Q : QuadraticBasis F (D * -(s.weights.m : ℤ))}
variable {A : OrbitFibers s.visibility (actualIndex s D) N.primeFactors.card (ClassGroup (𝓞 F))}

/-- The independent ideal and local norm dictionary for the normalized
idèles used in the fibers (tex 9161–9166, 9180–9194). -/
structure TorusIdealRead (T : TorusParametrization s D Q A) where
  ideal : ClassGroup (𝓞 F) → integralIdealsPrimeTo (conductorOrder F 1).conductorModulus
  coprime : ∀ c, (Ideal.absNorm (ideal c).val).Coprime s.weights.m
  fractional : ∀ c, toFractionalIdeal (T.idele c) =
    FractionalIdeal.mk0 F ⟨(ideal c).val, mem_nonZeroDivisors_iff_ne_zero.mpr
      (((conductorOrder F 1).mem_integralIdealsPrimeTo_conductorModulus_iff.mp (ideal c).prop).1)⟩
  pic : ClassGroup (𝓞 F) ≃* Pic (conductorOrder F 1)
  pic_eq : ∀ c, (conductorOrder F 1).picClass (ideal c) = pic c
  valuation : ∀ c (p : Adelic.Prime),
    Padic.valuation (localNrd p ((T.embedIdeles (T.idele c)).val p) : ℚ_[p.val]) =
      ((Ideal.absNorm (ideal c).val).factorization p.val : ℤ)
  ramified_one : ∀ c (p : Adelic.Prime), p.val ∣ s.weights.m →
    localNrd p ((T.embedIdeles (T.idele c)).val p) = 1

/-- The class labels on the actual stage are read at the same chosen
adelic representatives in both factors. Only values on the given sphere's
nonzero support are needed in the second field. -/
structure StageRead (s : StageAt O N M hN m) (D : ℤ)
    (C : NormFactors (ActualOrder s) (-(s.weights.m : ℤ))) (W : SchwartzFactors O C) : Prop where
  norm_eq : ∀ z, s.weights.χN z = ((C.character (Adelic.classRepresentative z) : ℤ) : O)
  schwartz_eq : ∀ z (x : s.visibility.supp z (actualIndex s D)),
    s.weights.f z x = W.eval (Adelic.classRepresentative z) x

/-- The torus norm character equals the descended ideal character on each
class, using the prime valuations of its own normalized idele. -/
theorem torus_character (T : TorusParametrization s D Q A) (J : TorusIdealRead T)
    (C : NormFactors (ActualOrder s) (-(s.weights.m : ℤ)))
    (hχ : NormCharacterDescent F (-(s.weights.m : ℤ))) (c : ClassGroup (𝓞 F)) :
    (C.character (T.embedIdeles (T.idele c)) : ℤ) =
      (hχ.choose (J.pic c) : ℤ) := by
  have hcop : (Ideal.absNorm (J.ideal c).val).Coprime (-(s.weights.m : ℤ)).natAbs := by
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using J.coprime c
  have hn : Ideal.absNorm (J.ideal c).val ≠ 0 :=
    fun hz => (((conductorOrder F 1).mem_integralIdealsPrimeTo_conductorModulus_iff.mp
      (J.ideal c).prop).1) (Ideal.absNorm_eq_zero_iff.mp hz)
  rw [C.onIntegralNorm _ _ hn (J.valuation c)]
  · rw [← J.pic_eq c, hχ.choose_spec _ hcop]
  · intro p hp
    apply J.ramified_one c p
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hp


/-- Tex 8571–8578 and 9171–9179: the same integral unit supplies the
right character in the norm factor and its inverse in the Schwartz factor. -/
theorem orbit_transport (T : TorusParametrization s D Q A)
    (C : NormFactors (ActualOrder s) (-(s.weights.m : ℤ))) (W : SchwartzFactors O C)
    (H : StageRead s D C W) (t : Orientations N.primeFactors.card) (c : ClassGroup (𝓞 F)) :
    ∃ r : Adelic.integralUnits (ActualOrder s),
      s.visibility.χN (zc A.param (t, c)) =
        ((C.character (T.base t) : ℤ) : O) *
        ((C.character (T.embedIdeles (T.idele c)) : ℤ) : O) *
        ((C.character r.val : ℤ) : O) ∧
      s.visibility.f (zc A.param (t, c)) (rep A.param (t, c)) =
        W.eval (T.base t) (T.embedding (Q.model QuadraticAlgebra.omega)) *
        ((((C.character r.val)⁻¹ : ℤˣ) : ℤ) : O) := by
  obtain ⟨q, hideal, x, hx, horbit⟩ := T.presents t c
  obtain ⟨r, hframe⟩ := (Adelic.fromAdelic_translate_iff
    (T.embedIdeles (T.idele c) * T.base t)
    (Adelic.classRepresentative (zc A.param (t, c))) q).mp
      ((congrArg (fun I : LPIdeal (ActualOrder s) => I.val)
        (Adelic.fromAdelic_classRepresentative (zc A.param (t, c)))).trans hideal)
  refine ⟨r, ?_, ?_⟩
  · have hread : s.visibility.χN (zc A.param (t, c)) =
        ((C.character (Adelic.classRepresentative (zc A.param (t, c))) : ℤ) : O) :=
      H.norm_eq _
    rw [hread, hframe]
    simp only [map_mul, C.rational, one_mul, Units.val_mul, Int.cast_mul]
    ring
  · let z := zc A.param (t, c)
    let y : s.visibility.supp z (actualIndex s D) := (A.param (t, c)).2.out
    have he : Quotient.mk _ y = Quotient.mk _ x :=
      (Quotient.out_eq' (A.param (t, c)).2).trans horbit.symm
    have hy : y ∈ MulAction.orbit (s.visibility.G z) x :=
      MulAction.orbitRel_apply.mp (Quotient.exact he)
    have hh := f_eq_of_mem_orbit s.visibility z (actualIndex s D) x y hy
    change s.weights.f z y = _
    change s.weights.f z y = s.weights.f z x at hh
    rw [hh, H.schwartz_eq, hframe]
    unfold SchwartzFactors.eval
    have hprod : ∀ p ∈ W.primes,
        W.value p (inFrame (Adelic.diagonal _ q * (T.embedIdeles (T.idele c) * T.base t) * r.val)
          x p) =
        W.value p (inFrame (T.base t) (T.embedding (Q.model QuadraticAlgebra.omega)) p) *
          (((C.atPrime p (localNrd p (r.val.val p)))⁻¹ : ℤˣ) : ℤ) := by
      intro p hp
      rw [hx, frame_transport _ _ _ _ _ (T.centralizes _) p]
      exact W.covariance p hp ⟨_, r.prop p⟩ _
    rw [Finset.prod_congr rfl hprod, Finset.prod_mul_distrib, C.rightProduct W r,
      ← Finset.prod_inv_distrib, Units.coe_prod]
    push_cast
    rfl

/-- Fill the actual TorusWeights, using the class character supplied by
norm descent. The base orders come from the signs and the nonzero local
Schwartz factors at the base frame. -/
def actualWeights (T : TorusParametrization s D Q A) (J : TorusIdealRead T)
    (C : NormFactors (ActualOrder s) (-(s.weights.m : ℤ))) (W : SchwartzFactors O C)
    (H : StageRead s D C W) (hχ : NormCharacterDescent F (-(s.weights.m : ℤ))) :
    O7Actual.TorusWeights s.visibility A where
  normBase t := ((C.character (T.base t) : ℤ) : O)
  schwartzBase t := W.eval (T.base t) (T.embedding (Q.model QuadraticAlgebra.omega))
  character c := ((hχ.choose (J.pic c) : ℤ) : O)
  transport t c := Units.map (Int.castRingHom O).toMonoidHom
    (C.character (orbit_transport T C W H t c).choose.val)
  norm_transport t c := by
    have h := (orbit_transport T C W H t c).choose_spec.1
    refine h.trans ?_
    exact congrArg (fun v : ℤ => ((C.character (T.base t) : ℤ) : O) * (v : O) *
      ((C.character (orbit_transport T C W H t c).choose.val : ℤ) : O))
      (torus_character T J C hχ c)
  schwartz_transport t c := by
    have h := (orbit_transport T C W H t c).choose_spec.2
    rw [← map_inv]
    exact h
  norm_order t := ⟨1, by simpa using (sign_square (O := O) (C.character (T.base t)))⟩
  schwartz_order t := by
    apply W.eval_order
    intro hz
    obtain ⟨r, -, h⟩ := orbit_transport T C W H t (1 : ClassGroup (𝓞 F))
    rw [hz, zero_mul] at h
    exact ((A.param (t, (1 : ClassGroup (𝓞 F)))).2.out.prop.2.2) h

/-- The exact type of DatumAt.weights with the full odd filter and the
quadratic basis from the supplied matching IntegralSupport. -/
def datumWeights (I : IntegralSupport s D)
    (A₀ : OrbitFibers s.visibility (actualIndex s D) N.primeFactors.card I.classGroup)
    (filter : OddFilter N s.ell D (-(s.weights.m : ℤ)))
    (T : letI := I.field; letI := I.numberField; TorusParametrization s D I.basis A₀)
    (J : letI := I.field; letI := I.numberField; TorusIdealRead T)
    (C : NormFactors (ActualOrder s) (-(s.weights.m : ℤ))) (W : SchwartzFactors O C)
    (H : StageRead s D C W)
    (disc_eq : letI := I.field; letI := I.numberField; discr I.Fq = D * -(s.weights.m : ℤ))
    (descent : letI := I.field; letI := I.numberField;
      1 < D → NormCharacterDescent I.Fq (-(s.weights.m : ℤ))) :
    O7Actual.TorusWeights s.visibility A₀ := by
  letI := I.field
  letI := I.numberField
  have degree : Module.finrank ℚ I.Fq = 2 := by
    rw [← I.basis.model.toLinearEquiv.finrank_eq]
    exact QuadraticAlgebra.finrank_eq_two _ _
  exact actualWeights T J C W H (descent_of_filter filter degree disc_eq descent)


end Actual

end ZInQ.Manuscript.RC.TorusWeights
