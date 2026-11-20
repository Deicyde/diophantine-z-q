import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Model

/-! The signed and good-Hecke identities for the same extended map.
Specializing relations of morphisms and cancelling the cusp terms are
on-the-spot glue (c), tex 8480–8492 and 9331–9355. -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve
open CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve
open FreeAbelianGroup (of)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 350000
set_option maxHeartbeats 1100000

namespace ZInQ.Manuscript.RC.PMQuotient.GoodRow

open GoodReduction (generic)
open PMGeometry (DivZero center)

private theorem toAdd_ofFn_prod {A : Type} [AddCommGroup A] {n : ℕ}
    (f : Fin n → Multiplicative A) :
    (List.ofFn f).prod.toAdd = ∑ i, (f i).toAdd := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    change (f 0).toAdd + (List.ofFn fun j => f j.succ).prod.toAdd = _
    rw [ih]

variable {R : Type} [CommRing R] [Algebra R ℚ]
    {ell N : ℕ} [Fact ell.Prime] {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    {Ebar : WeierstrassCurve (ZMod ell)} {X : PMAdelic.CoarseFibre}
    {XQ EQ : Over (Spec (.of ℚ))} {π : XQ ⟶ EQ}
    (G : GoodRow R ell N K Ebar X π)

/-- Restrict a morphism and read its value at one section, preserving the group law. -/
def readAt {B : Over (Spec (.of R))} (b : residueSource ell K ⟶ G.special.obj B) :
    (B ⟶ G.E) →* Multiplicative (Ebar.baseChange K).toAffine.Point :=
  G.read.toMonoidHom.comp
    (({ toFun := fun f => b ≫ f
        map_one' := MonObj.comp_one b
        map_mul' := fun f g => MonObj.comp_mul b f g } :
      (G.special.obj B ⟶ G.special.obj G.E) →* _).comp
      (G.special.homMonoidHom (X := B) (M := G.E)))

/-- The fixed generic map vanishes at the rational cusp (tex 1786–1787). -/
def Based : Prop :=
  (generic R ℚ).map (G.cusp ≫ G.πInt) = 1

/-- Specialize the normalization at the base cusp. -/
theorem value_infinity (h : G.Based) : G.value G.infinity = 0 := by
  let : Smooth (𝟙_ (Over (Spec (.of R)))).hom := by
    change Smooth (𝟙 (Spec (.of R)))
    infer_instance
  have hint : G.cusp ≫ G.πInt = 1 := by
    apply (G.neron.2.2.2.2 _).injective
    change (generic R ℚ).homMonoidHom (G.cusp ≫ G.πInt) =
      (generic R ℚ).homMonoidHom (1 : _ ⟶ G.E)
    rw [map_one]
    exact h
  apply Subtype.ext
  change G.evaluate (G.point G.infinity) = 0
  rw [G.point_infinity, evaluate, Category.assoc, ← Functor.map_comp]
  change (G.readAt (residueUnit G.closed) (G.cusp ≫ G.πInt)).toAdd = 0
  rw [hint]
  exact congrArg Multiplicative.toAdd (map_one (G.readAt (residueUnit G.closed)))

/-- The actual moving-cusp translation, integrally. Both its generic and
residue values use this section and the same extended map. -/
def movedCusp {q : ℕ} (hq : q.Prime) (he : 0 < N.factorization q) :
    𝟙_ (Over (Spec (.of R))) ⟶ G.E :=
  G.cusp ≫ G.W q hq he ≫ G.πInt

/-- The generic form of the signed affine identity, with the constant
`π(W∞)`. This is the morphism version of `translatedAtkinAtInfinity`,
transported to the identified generic fibres. -/
def AtkinIdentity (w : ℕ → ℤˣ) : Prop :=
  ∀ q hq he, (generic R ℚ).map (G.W q hq he) ≫ (generic R ℚ).map G.πInt =
    ((generic R ℚ).map G.πInt) ^ (w q : ℤ) *
      (generic R ℚ).map (toUnit G.M ≫ G.movedCusp hq he)

/-- Specialize the pinned signed identity by the integral affine relation. -/
theorem atkin_quotient {w : ℕ → ℤˣ} (hb : G.Based) (ha : G.AtkinIdentity w)
    (q : ℕ) (hq : q.Prime) (he : 0 < N.factorization q) (x : X.Point) :
    G.quotient (center G.infinity (of (X.W q x) - of (X.W q G.infinity))) =
      (w q : ℤ) • G.quotient (center G.infinity (of x)) := by
  let v := (PM.ReducedPoints (K := K) Ebar).subtype.comp G.quotient
  apply Subtype.ext
  exact GoodReduction.atkinQuotient_of_integralRelation G.neron G.πInt
    (G.W q hq he) (G.movedCusp hq he) (w q : ℤ) (ha q hq he)
    (Spec.map (CommRingCat.ofHom G.closed)) G.point G.read.toMonoidHom G.infinity
    (AddMonoidHom.id (DivZero X.Point)) v q (G.point_W q hq he)
    (fun y => by
      change (G.quotient (center G.infinity (of y))).val = G.evaluate (G.point y)
      rw [G.quotient_center, G.value_infinity hb, sub_zero]
      rfl) x

/-- The part of the integral good-Hecke correspondence used at one
supersingular point. A smooth chart with ordered cyclic subgroups records
every branch with its multiplicity, even when two quotient points coincide.
Tex 8479–8487; Deligne–Rapoport VI.6 (UNVERIFIED) and chart glue (c). -/
structure HeckePacket (q : ℕ) (x : X.Point) where
  /-- A smooth local chart of the moduli of pairs with the good correspondence split. -/
  B : Over (Spec (.of R))
  /-- Smoothness of the chart; the prime-to-ell torsion is finite étale. -/
  [smoothB : Smooth B.hom]
  /-- The forgetful map and the cyclic quotients, from the integral correspondence. -/
  source : B ⟶ G.M
  /-- Cyclic quotients indexed by all cyclic subgroups of order q. -/
  target : Fin (q + 1) → (B ⟶ G.M)
  /-- A geometric point of the chart above the indicated coarse point. -/
  lift : residueSource ell K ⟶ G.special.obj B
  /-- Comparison of the forgetful map with the coarse source section (c). -/
  source_eq : lift ≫ G.special.map source = G.point x
  /-- The coarse images of the geometric cyclic quotients. -/
  neighbour : Fin (q + 1) → X.Point
  /-- The coarse divisor counts the quotients with multiplicities (c). -/
  divisor_eq : X.T q x = ∑ j, of (neighbour j)
  /-- The quotient sections are the same neighbours used by the coarse operator (c). -/
  target_eq : ∀ j, lift ≫ G.special.map (target j) = G.point (neighbour j)

attribute [instance] HeckePacket.smoothB

/-- Generic good-Hecke equivariance evaluated on the chart, using the
parametrization based at infinity and `T_q∞ = (q+1)∞` (tex 1788, 8480–8487).
The inherited Milne locator does not supply this hypothesis. An ordered
product avoids imposing commutativity instances on scheme morphisms. -/
def HeckeIdentity {q : ℕ} {x : X.Point} (T : G.HeckePacket q x) (a : ℤ) : Prop :=
  (List.ofFn fun j => (generic R ℚ).map (T.target j ≫ G.πInt)).prod =
    (generic R ℚ).map (T.source ≫ G.πInt) ^ a

/-- The Hecke relation on the degree-zero divisor follows by Néron
uniqueness on the smooth chart and addition of its reduced branch values. -/
theorem hecke_quotient (hb : G.Based) {q : ℕ} (hq : q.Prime) (hgood : ¬ q ∣ N * ell)
    {x : X.Point} (T : G.HeckePacket q x) {a : ℤ} (ha : G.HeckeIdentity T a) :
    G.quotient (center G.infinity (X.T q x - X.T q G.infinity)) =
      a • G.quotient (center G.infinity (of x)) := by
  let gen := (generic R ℚ).homMonoidHom (X := T.B) (M := G.E)
  let l := List.ofFn fun j => T.target j ≫ G.πInt
  have hint : l.prod = (T.source ≫ G.πInt) ^ a := by
    apply (G.neron.2.2.2.2 T.B).injective
    change gen l.prod = gen ((T.source ≫ G.πInt) ^ a)
    rw [map_list_prod, map_zpow, List.map_ofFn]
    exact ha
  let ev := G.readAt T.lift
  have hv := congrArg (fun f => (ev f).toAdd) hint
  change (ev l.prod).toAdd = (ev ((T.source ≫ G.πInt) ^ a)).toAdd at hv
  rw [map_list_prod, map_zpow, List.map_ofFn, toAdd_ofFn_prod] at hv
  rw [T.divisor_eq, G.T_infinity q hq hgood]
  simp only [map_sub, map_sum, map_nsmul, G.quotient_center, G.value_infinity hb, sub_zero, smul_zero]
  apply Subtype.ext
  change (PM.ReducedPoints (K := K) Ebar).subtype (∑ j, G.value (T.neighbour j)) =
    (PM.ReducedPoints (K := K) Ebar).subtype (a • G.value x)
  rw [map_sum, map_zsmul]
  convert hv using 1
  · apply Finset.sum_congr rfl
    intro j _
    change G.evaluate (G.point (T.neighbour j)) =
      (G.read (T.lift ≫ G.special.map (T.target j ≫ G.πInt))).toAdd
    rw [Functor.map_comp, ← Category.assoc, T.target_eq]
    rfl
  · change a • G.evaluate (G.point x) =
      a • (G.read (T.lift ≫ G.special.map (T.source ≫ G.πInt))).toAdd
    rw [Functor.map_comp, ← Category.assoc, T.source_eq]
    rfl

/-- The good-model inputs and the actual generic identities. -/
structure Relations (ap : ℕ → ℤ) (w : ℕ → ℤˣ) where
  /-- The Abel–Jacobi base cusp normalizes the fixed parametrization. -/
  based : G.Based
  /-- The generic signed identity for the pinned newform. -/
  atkin : G.AtkinIdentity w
  /-- The integral correspondence at the points used in the row. -/
  hecke : ∀ q, q.Prime → ¬ q ∣ N * ell → ∀ x ∈ X.ss, G.HeckePacket q x
  /-- Hecke equivariance for (only) those branches of the fixed map. -/
  eigen : ∀ q hq hg x hx, G.HeckeIdentity (hecke q hq hg x hx) (ap q)

/-- The old interface uses degree-zero divisors as its intermediate group.
Both the identity divisor map and the quotient are now fixed definitions. -/
def specialFibre {ap : ℕ → ℤ} {w : ℕ → ℤˣ} (H : G.Relations ap w) :
    AtkinSign.SpecialFibreAtSigns ell N K Ebar ap X w where
  infinity := G.infinity
  frobenius_sq := G.frobenius_sq
  T_infinity := G.T_infinity
  frobenius_infinity := G.frobenius_infinity
  J := DivZero X.Point
  divisorClass := AddMonoidHom.id _
  quotient := G.quotient
  hecke_quotient q hq hg x hx :=
    G.hecke_quotient H.based hq hg (H.hecke q hq hg x hx) (H.eigen q hq hg x hx)
  atkin_quotient q hq he x _ := G.atkin_quotient H.based H.atkin q hq he x
  frobenius_quotient x _ := G.frobenius_quotient x

/-- The PM specialization is the residue reading of the extension, since
the cusp subtraction vanishes by the generic normalization. -/
theorem specialize_eq_value {ap : ℕ → ℤ} {w : ℕ → ℤˣ} (H : G.Relations ap w)
    {hell : ell % 4 = 3} {hN : 0 < N} {hcop : N.Coprime ell}
    (J : PMAdelic.JetchevKane ell hell N hN hcop X) (x : X.Point) :
    (PMAdelic.geometricInput J (G.specialFibre H).toSpecialFibre).specialize x = G.value x := by
  change G.quotient (center G.infinity (of x)) = _
  rw [G.quotient_center, G.value_infinity H.based, sub_zero]


end ZInQ.Manuscript.RC.PMQuotient.GoodRow
