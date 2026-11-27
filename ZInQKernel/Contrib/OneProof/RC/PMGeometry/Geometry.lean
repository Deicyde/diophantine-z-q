import ZInQKernel.Contrib.OneProof.RC.PM.Stage

/-!
# Modular special fibre for the supersingular function (tex 8462–8492)

The modular curve and Jacobian are used through their point and divisor interfaces.
The class-set comparison is GLUE: cited as Jetchev–Kane §§1.1–1.2 and 2.5 (arXiv v1;
journal version unread); Ribet 1990 Prop. 3.3 reports it without proof, and a Lean proof is
in progress. The comparison of the operators used in Appendix F is ELLIOT: asserted in the
manuscript; to be proved in Lean.
-/

noncomputable section

open scoped WeierstrassCurve
open FreeAbelianGroup (of)

namespace ZInQ.Manuscript.RC.PMGeometry

open Eichler Stages

/-- Adelic outputs. `ram` is the instance of the existing `AppF.VoightMainThm1461`;
the level and the right operations are supplied by the adelic construction. -/
structure Adelic {ell N : ℕ} {a b : ℚ} (R : Order a b) where
  ram : AppF.RamifiedExactlyAtEll0Infty ell a b
  eichler : IsEichler ell N R
  atkin : ∀ p : ℕ, p.Prime → 0 < N.factorization p → ClassSet R → ClassSet R
  atkin_involutive : ∀ p hp he, Function.Involutive (atkin p hp he)
  uniformizer : Equiv.Perm (ClassSet R)

private def degree (X : Type) : FreeAbelianGroup X →+ ℤ :=
  FreeAbelianGroup.lift (fun _ => 1)

/-- Degree-zero integral divisors on the coarse points of the modular special fibre. -/
abbrev DivZero (X : Type) := (degree X).ker

/-- Subtract the degree times the chosen cusp. This is the identity on degree-zero
divisors, and sends a point to its difference with the cusp (tex 8480–8487). -/
def center {X : Type} (infinity : X) : FreeAbelianGroup X →+ DivZero X :=
  (show FreeAbelianGroup X →+ FreeAbelianGroup X from {
    toFun := fun D => D - degree X D • of infinity
    map_zero' := by simp
    map_add' := by
      intro D E
      simp only [map_add, add_zsmul]
      abel }).codRestrict _ (fun D => by
        change degree X (D - degree X D • of infinity) = 0
        simp [degree])

/-- ELLIOT's special-fibre parametrization, the class-set comparison with supersingular
pairs (GLUE) and the operator comparisons (ELLIOT).
`Point` is the coarse point set of the good special fibre of `X₀(N)` over
the quadratic residue field; `ss` is its supersingular locus (tex 8465–8479).
`J` is the group of points of the specialized Jacobian. Only the divisor
class map and its composite with the elliptic quotient are used. -/
structure GeometricInput {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
    (A : Adelic (ell := ell) (N := N) R)
    (K : Type*) [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    (Ebar : WeierstrassCurve (ZMod ell)) (ap : ℕ → ℤ) where
  Point : Type
  ss : Set Point
  infinity : Point
  /-- GLUE (tex 8465–8474): class set versus coarse supersingular pairs. Cited as
  Jetchev–Kane §§1.1–1.2 and 2.5 (arXiv v1; journal version unread); Ribet 1990 Prop. 3.3
  reports it without proof; a Lean proof is in progress. -/
  classes : ClassSet R ≃ ss
  /-- The geometric good Hecke correspondence, as a divisor with multiplicities. -/
  T : ℕ → Point → FreeAbelianGroup Point
  W : ℕ → Point → Point
  /-- Arithmetic Frobenius of the special fibre over the prime field. -/
  frobenius : Point → Point
  /-- All points in this model are over the quadratic residue field. -/
  frobenius_sq : Function.Involutive frobenius
  frobenius_ss : ∀ x ∈ ss, frobenius x ∈ ss
  /-- ELLIOT: geometric / adelic comparison for the good Hecke correspondence
  (tex 8480–8487, 9042, 9067–9078); asserted in the manuscript; to be proved in Lean. -/
  hecke_compare : ∀ p (hp : p.Prime), ¬ p ∣ N * ell → ∀ lines : LineIndex R p hp.ne_zero,
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ z, T p (classes z).val = ∑ i, of (classes (nbAt lines z i)).val
  /-- ELLIOT: geometric / adelic comparison for Atkin–Lehner (tex 8487–8489, 9331–9341);
  asserted in the manuscript; to be proved in Lean. -/
  atkin_compare : ∀ p hp he z, W p (classes z).val = (classes (A.atkin p hp he z)).val
  /-- ELLIOT: geometric / adelic comparison for Frobenius (tex 8489–8490, 9347–9355). -/
  frobenius_compare : ∀ z, frobenius (classes z).val = (classes (A.uniformizer z)).val
  /-- ELLIOT: `T_p[∞]=(p+1)[∞]` on the special fibre (tex 8477–8487). -/
  T_infinity : ∀ p, p.Prime → ¬ p ∣ N * ell → T p infinity = (p + 1) • of infinity
  /-- The rational cusp remains rational on the special fibre. -/
  frobenius_infinity : frobenius infinity = infinity
  J : Type
  [jacobianGroup : AddCommGroup J]
  divisorClass : DivZero Point →+ J
  /-- ELLIOT: the elliptic quotient extends to this good special fibre (tex 8476–8481). -/
  quotient : J →+ PM.ReducedPoints (K := K) Ebar
  /-- ELLIOT: the specialized quotient intertwines the good Hecke action on
  the degree-zero classes `[x]-[∞]` with multiplication by `a_p` (tex 8481–8487). -/
  hecke_quotient : ∀ p, p.Prime → ¬ p ∣ N * ell → ∀ x ∈ ss,
    quotient (divisorClass (center infinity (T p x - T p infinity))) =
      ap p • quotient (divisorClass (center infinity (of x)))
  atkinSign : ℕ → ℤ
  atkinSign_eq : ∀ p : ℕ, p.Prime → 0 < N.factorization p →
    atkinSign p = 1 ∨ atkinSign p = -1
  /-- ELLIOT: the quotient has Atkin–Lehner eigenvalue `w_{p^e}` on the
  degree-zero classes. The affine translation does not occur on divisors
  of degree zero (tex 8487–8489, 9336–9339). -/
  atkin_quotient : ∀ p : ℕ, p.Prime → 0 < N.factorization p → ∀ x ∈ ss,
    quotient (divisorClass (center infinity (of (W p x) - of (W p infinity)))) =
      atkinSign p • quotient (divisorClass (center infinity (of x)))
  /-- ELLIOT: on the special fibre, the rational quotient on divisor classes
  commutes with arithmetic Frobenius (tex 9347–9355). -/
  frobenius_quotient : ∀ x ∈ ss,
    quotient (divisorClass (center infinity (of (frobenius x) - of (frobenius infinity)))) =
      fixedFrob (curveFrob (K := K) Ebar) (quotient (divisorClass (center infinity (of x))))

attribute [instance] GeometricInput.jacobianGroup

namespace GeometricInput

variable {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
  {A : Adelic (ell := ell) (N := N) R}
  {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
  {Ebar : WeierstrassCurve (ZMod ell)} {ap : ℕ → ℤ}
  (G : GeometricInput A K Ebar ap)

/-- Linear extension of the specialized parametrization based at infinity. -/
def onDivisor : FreeAbelianGroup G.Point →+ PM.ReducedPoints (K := K) Ebar :=
  G.quotient.comp (G.divisorClass.comp (center G.infinity))

/-- `π_ℓ₀(x)` is the elliptic quotient of the class of `[x]-[∞]`. -/
def specialize (x : G.Point) : PM.ReducedPoints (K := K) Ebar := G.onDivisor (of x)

/-- The based Abel–Jacobi map sends the base cusp to zero. -/
theorem specialize_infinity : G.specialize G.infinity = 0 := by
  have h : center G.infinity (of G.infinity) = 0 := by
    apply Subtype.ext
    change of G.infinity - degree G.Point (of G.infinity) • of G.infinity = 0
    simp [degree]
  simp [specialize, onDivisor, h]

/-- The induced Frobenius on the supersingular locus. -/
def frobSS (x : G.ss) : G.ss := ⟨G.frobenius x.val, G.frobenius_ss x.val x.property⟩

/-- Arithmetic and inverse Frobenius have the same action on coarse pairs
over the quadratic field (tex 9353–9355). -/
theorem frobSS_involutive : Function.Involutive G.frobSS :=
  fun x => Subtype.ext (G.frobenius_sq x.val)

/-- The reduction of `π(W_{p^e}∞)` (tex 8488–8489). -/
def cusp (p : ℕ) := G.specialize (G.W p G.infinity)

/-- The good Hecke eigenrelation: `AJ(T_p∞)=0` and the quotient intertwines
the correspondence on `[z]-[∞]` (tex 8480–8487). -/
theorem hecke (p : ℕ) (hp : p.Prime) (hgood : ¬ p ∣ N * ell)
    (lines : LineIndex R p hp.ne_zero) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ z, ∑ i, G.specialize (G.classes (nbAt lines z i)).val =
      ap p • G.specialize (G.classes z).val := by
  let : NeZero p := ⟨hp.ne_zero⟩
  intro z
  have h := G.hecke_quotient p hp hgood (G.classes z).val (G.classes z).property
  change G.onDivisor (G.T p (G.classes z).val - G.T p G.infinity) = _ at h
  rw [map_sub, G.T_infinity p hp hgood, map_nsmul,
    show G.onDivisor (of G.infinity) = 0 from G.specialize_infinity, smul_zero, sub_zero,
    G.hecke_compare p hp hgood lines z, map_sum] at h
  exact h

/-- Moving the base cusp accounts for the affine translation (tex 8487–8489). -/
theorem atkin_affine (p : ℕ) (hp : p.Prime) (he : 0 < N.factorization p) (z : ClassSet R) :
    G.specialize (G.classes (A.atkin p hp he z)).val =
      G.atkinSign p • G.specialize (G.classes z).val + G.cusp p := by
  have h := G.atkin_quotient p hp he (G.classes z).val (G.classes z).property
  change G.onDivisor (of (G.W p (G.classes z).val) - of (G.W p G.infinity)) = _ at h
  rw [map_sub, G.atkin_compare p hp he z] at h
  exact eq_add_of_sub_eq h

/-- Arithmetic Frobenius fixes the base cusp, so no translation occurs (tex 9347–9355). -/
theorem specialize_frob (x : G.ss) :
    G.specialize (G.frobSS x).val =
      fixedFrob (curveFrob (K := K) Ebar) (G.specialize x.val) := by
  have h := G.frobenius_quotient x.val x.property
  change G.onDivisor (of (G.frobenius x.val) - of (G.frobenius G.infinity)) = _ at h
  rw [G.frobenius_infinity, map_sub,
    show G.onDivisor (of G.infinity) = 0 from G.specialize_infinity, sub_zero] at h
  exact h

/-- The adelic right uniformizer induces the Frobenius of coarse pairs (tex 8489–8490). -/
theorem uniformizer_spec (z : ClassSet R) :
    G.classes (A.uniformizer z) = G.frobSS (G.classes z) :=
  Subtype.ext (G.frobenius_compare z).symm

/-- The geometry consumed by the existing class-function and theta constructions. -/
def geometry : PM.Geometry K R N Ebar ap where
  ram := A.ram
  eichler := A.eichler
  SS := G.ss
  classes := G.classes
  specialize := fun x => G.specialize x.val
  hecke := G.hecke
  atkin := A.atkin
  atkin_involutive := A.atkin_involutive
  atkinSign := G.atkinSign
  atkinSign_eq := G.atkinSign_eq
  cusp := G.cusp
  atkin_affine := G.atkin_affine
  frobSS := G.frobSS
  uniformizer := A.uniformizer
  uniformizer_spec := G.uniformizer_spec
  specialize_frob := G.specialize_frob

#print axioms center
#print axioms specialize_infinity
#print axioms frobSS_involutive
#print axioms hecke
#print axioms atkin_affine
#print axioms specialize_frob
#print axioms uniformizer_spec
#print axioms geometry

end GeometricInput
end ZInQ.Manuscript.RC.PMGeometry
