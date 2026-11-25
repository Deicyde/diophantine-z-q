import ZInQKernel.Contrib.OneProof.RC.Eichler.Indexed
import ZInQKernel.Contrib.OneProof.RC.Stages.ReducedCurve

/-!
# The supersingular function at one stage (tex 8462–8494)

The arithmetic identities for the specialized parametrization are geometric inputs. The
identification with supersingular pairs is GLUE: the manuscript cites it to Jetchev–Kane,
§§1.1–1.2 and 2.5 (arXiv v1; journal version unread); Ribet 1990 Prop. 3.3 reports it without
proof, and a Lean proof is in progress. The operator compatibilities are ELLIOT. The class set, ideal neighbours and Kummer map are
the existing constructions. No printed-form leaf is introduced.
-/

noncomputable section

open scoped WeierstrassCurve

namespace ZInQ.Manuscript.RC.PM

open Eichler Stages

set_option maxHeartbeats 800000

variable {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
variable {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]

/-- The points over the quadratic residue field, in the existing fixed-point model. -/
abbrev ReducedPoints (Ebar : WeierstrassCurve (ZMod ell)) :=
  FixedSq (curveFrob (K := K) Ebar)

/-- The geometric input at good reduction. `Ebar` is the reduction of the elliptic quotient,
and `ap` gives its characteristic-zero Hecke eigenvalues. -/
structure Geometry (K : Type*) [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    (R : Order a b) (N : ℕ) (Ebar : WeierstrassCurve (ZMod ell))
    (ap : ℕ → ℤ) where
  /-- Voight Main Thm. 14.6.1, as already stated in AppF.Prints (tex 8462–8463). -/
  ram : AppF.RamifiedExactlyAtEll0Infty ell a b
  /-- ELLIOT (tex 8464, 8469, 8477): the Eichler order, with level prime to the detecting prime. -/
  eichler : IsEichler ell N R
  /-- GLUE (tex 8465–8474): coarse supersingular pairs, as in the class-set comparison cited to
  Jetchev–Kane (arXiv v1; journal version unread); a Lean proof is in progress. -/
  SS : Type
  /-- GLUE (tex 8465–8474): the class description, cited to Jetchev–Kane §§1.1–1.2 and 2.5
  (arXiv v1; journal version unread); Ribet 1990 Prop. 3.3 reports it without proof; a Lean
  proof is in progress. -/
  classes : ClassSet R ≃ SS
  /-- ELLIOT (tex 8476–8479): the specialization of the parametrization based at infinity. -/
  specialize : SS → ReducedPoints (K := K) Ebar
  /-- ELLIOT (tex 8480–8487): the quotient intertwines Hecke and `T_p(∞)=(p+1)∞`.
  The sum uses the actual ideal neighbours, with multiplicity, via the given line indexing. -/
  hecke : ∀ p (hp : p.Prime), ¬ p ∣ N * ell → ∀ lines : LineIndex R p hp.ne_zero,
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ z, ∑ i, specialize (classes (nbAt lines z i)) = ap p • specialize (classes z)
  /-- ELLIOT (tex 8487–8489, 9331–9338): the action of `W_{p^e}` for `e=v_p(N)>0`. -/
  atkin : ∀ p : ℕ, p.Prime → 0 < N.factorization p → ClassSet R → ClassSet R
  /-- ELLIOT (tex 8487–8489): `W_{p^e}` is an involution. -/
  atkin_involutive : ∀ p hp he, Function.Involutive (atkin p hp he)
  /-- ELLIOT (tex 8488, 9334–9339): the eigenvalue `w_{p^e}`. -/
  atkinSign : ℕ → ℤ
  /-- ELLIOT (tex 9334–9339): the eigenvalue is a sign. -/
  atkinSign_eq : ∀ p : ℕ, p.Prime → 0 < N.factorization p → atkinSign p = 1 ∨ atkinSign p = -1
  /-- ELLIOT (tex 8282–8285, 8488–8489): the reduction of `π(W_{p^e}∞)`. -/
  cusp : ℕ → ReducedPoints (K := K) Ebar
  /-- ELLIOT (tex 8487–8489): the affine Atkin–Lehner identity before scaling by `L`. -/
  atkin_affine : ∀ p hp he z, specialize (classes (atkin p hp he z)) =
    atkinSign p • specialize (classes z) + cusp p
  /-- ELLIOT (tex 8469–8473):
  the arithmetic Frobenius on supersingular pairs over the quadratic field. -/
  frobSS : SS → SS
  /-- ELLIOT (tex 8489–8490, 9343–9358): the right operation of a division uniformizer. -/
  uniformizer : Equiv.Perm (ClassSet R)
  /-- ELLIOT (tex 8489–8490, 9347–9355): the uniformizer induces Frobenius on pairs. -/
  uniformizer_spec : ∀ z, classes (uniformizer z) = frobSS (classes z)
  /-- ELLIOT (tex 9347–9355): the rational parametrization specializes equivariantly. -/
  specialize_frob : ∀ x, specialize (frobSS x) = fixedFrob (curveFrob (K := K) Ebar) (specialize x)

variable {Ebar : WeierstrassCurve (ZMod ell)} {ap : ℕ → ℤ}
  (G : Geometry (K := K) R N Ebar ap)

namespace Geometry

/-- `π_ℓ₀` on the quotient of locally principal right ideals (tex 8476–8479). -/
def pi : ClassSet R → ReducedPoints (K := K) Ebar := G.specialize ∘ G.classes

/-- On-the-spot (c): equivalent ideal representatives give the same specialized point. -/
theorem pi_eq_of_rel {I J : LPIdeal R} (h : (idealRel R).r I J) :
    G.pi (Quotient.mk _ I) = G.pi (Quotient.mk _ J) :=
  congrArg G.pi (Quotient.sound h)

end Geometry

/-- The finite detector data from (O.2), on the reduced curve. The row is on the finite
torsion subgroup: it is the specialization of `Stages.finiteRow`, with its Frobenius
invariance (tex 8378–8390, 8439–8456). -/
structure Evaluation (K : Type*) [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    (Ebar : WeierstrassCurve (ZMod ell)) (M : ℕ) where
  ell_ne_two : ell ≠ 2
  square_trivial : ∀ t : (Ebar⁄K).toAffine.Point, (2 ^ M : ℕ) • t = 0 →
    curveFrob (K := K) Ebar (curveFrob (K := K) Ebar t) = t
  row : AddSubgroup.torsionBy (Ebar⁄K).toAffine.Point (2 ^ M : ℕ) →+ ZMod (2 ^ M)
  row_fixed : ∀ t, row (torsionFrob (curveFrob (K := K) Ebar) (2 ^ M) t) = row t

variable [IsSepClosed K] [Ebar.IsElliptic]
variable {M : ℕ} (d : Evaluation K Ebar M) (L : ℕ)

/-- The actual finite-field stage map `λ_M = b_M ∘ κ_M`. Its composition with reduction
is the map used by `Visibility.StageKummer` (tex 8378–8390, 8452–8456, 9288–9291). -/
def lam : ReducedPoints (K := K) Ebar →+ ZMod (2 ^ M) :=
  d.row.comp (reducedKappa (K := K) Ebar d.ell_ne_two M d.square_trivial)

/-- The Frobenius sign of the detector is inherited from the fixed row. -/
theorem lam_frob (x : ReducedPoints (K := K) Ebar) :
    (lam d) (fixedFrob (curveFrob (K := K) Ebar) x) = lam d x := by
  unfold lam reducedKappa
  exact lambda_frobenius_plus (curveFrob (K := K) Ebar) (2 ^ M) _ _ d.row d.row_fixed x

/-- `λ_M ∘ [L]` is additive on `E(𝔽_{ℓ₀²})` (tex 9290–9291), as an additive homomorphism. -/
def scaled : ReducedPoints (K := K) Ebar →+ ZMod (2 ^ M) where
  toFun x := lam d (L • x)
  map_zero' := by simp
  map_add' x y := by rw [nsmul_add, map_add]

/-- The finite class function `P_M(z)=λ_M(Lπ_ℓ₀(z))` (tex 8476). -/
def P : ClassSet R → ZMod (2 ^ M) := scaled d L ∘ G.pi

/-- On-the-spot (c): the function descends to classes. -/
theorem P_eq_of_rel {I J : LPIdeal R} (h : (idealRel R).r I J) :
    P G d L (Quotient.mk _ I) = P G d L (Quotient.mk _ J) :=
  congrArg (scaled d L) (G.pi_eq_of_rel h)

/-- Good Hecke eigenrelation, as a sum over all lines (tex 8481–8487, 8491–8492). -/
theorem P_hecke_at (p : ℕ) (hp : p.Prime) (hgood : ¬ p ∣ N * ell)
    (lines : LineIndex R p hp.ne_zero) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ z, ∑ i, P G d L (nbAt lines z i) = (ap p : ZMod (2 ^ M)) * P G d L z := by
  let : NeZero p := ⟨hp.ne_zero⟩
  intro z
  change ∑ i, scaled d L (G.pi (nbAt lines z i)) = (ap p : ZMod (2 ^ M)) * scaled d L (G.pi z)
  rw [← map_sum, show ∑ i, G.pi (nbAt lines z i) = ap p • G.pi z from
    G.hecke p hp hgood lines z, map_zsmul, zsmul_eq_mul]

/-- The exact type of `AppF.ThetaStage.hecke` for the total neighbour map `Eichler.nb`. -/
theorem P_hecke {Good : ℕ → Prop} (prime : ∀ p, Good p → p.Prime)
    (away : ∀ p, Good p → ¬ p ∣ N * ell)
    (lines : ∀ p (hp : Good p), LineIndex R p (prime p hp).ne_zero) :
    ∀ p (hp : Good p), letI : NeZero p := ⟨(prime p hp).ne_zero⟩
      ∀ z, ∑ i, P G d L (nb prime lines p z i) = (ap p : ZMod (2 ^ M)) * P G d L z := by
  classical
  intro p hp z
  simpa only [nb, dite_eq_left hp] using P_hecke_at G d L p (prime p hp) (away p hp) (lines p hp) z

/-- The Atkin–Lehner eigenrelation after the multiplier kills the reduced cuspidal translation
(tex 8282–8285, 8295–8297, 8487–8492, 9336–9339). -/
theorem P_atkin (p : ℕ) (hp : p.Prime) (he : 0 < N.factorization p)
    (hL : L • G.cusp p = 0) (z : ClassSet R) :
    P G d L (G.atkin p hp he z) = (G.atkinSign p : ZMod (2 ^ M)) * P G d L z := by
  change lam d (L • G.pi (G.atkin p hp he z)) =
    (G.atkinSign p : ZMod (2 ^ M)) * lam d (L • G.pi z)
  rw [show G.pi (G.atkin p hp he z) = G.atkinSign p • G.pi z + G.cusp p from G.atkin_affine p hp he z,
    nsmul_add, hL, add_zero, smul_comm, map_zsmul, zsmul_eq_mul]

/-- The right division-uniformizer eigenvalue is `+1` (tex 8490–8492, 9347–9355). -/
theorem P_uniformizer (z : ClassSet R) : P G d L (G.uniformizer z) = P G d L z := by
  change lam d (L • G.specialize (G.classes (G.uniformizer z))) =
    lam d (L • G.specialize (G.classes z))
  rw [G.uniformizer_spec, G.specialize_frob, ← map_nsmul, lam_frob]

#print axioms Geometry.pi_eq_of_rel
#print axioms lam_frob
#print axioms scaled
#print axioms P
#print axioms P_eq_of_rel
#print axioms P_hecke_at
#print axioms P_hecke
#print axioms P_atkin
#print axioms P_uniformizer

end ZInQ.Manuscript.RC.PM
