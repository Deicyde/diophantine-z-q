import ZInQKernel.Contrib.OneProof.RC.PMWire.Model

/-! Tex 8480–8492, 9331–9355. Specialization of the pinned affine relation
and of the generic Hecke identity; on-the-spot glue (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve CartesianMonoidalCategory Limits
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj TauCeti.ExactDivisor
open FreeAbelianGroup (of)
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option synthInstance.maxHeartbeats 350000

namespace ZInQ.Manuscript.RC.PMWire

open GoodReduction (generic)
open PMQuotient (residueSource residueUnit)
open PreparedParam

/-- The existing analytic normalization of the fixed rational map, using
the same scale and the same normalized newform. In particular the value
at infinity is rational zero. The normalized map is supplied by
`AtkinRational.algebraicParametrizationAtScale_atInfinity`; this record
does not infer scale rationality. -/
structure FixedAtScale {N : ℕ} [NeZero N] {E₀ : WeierstrassCurve ℚ}
    [E₀.IsElliptic] (π : rationalSource N ⟶ ellipticTarget E₀)
    (f : HeckeRing.GL2.Newform N 2) (χ : f.χ = 1) (Lat : PeriodPair) (κ : ℂ) : Prop where
  lattice : IsLatticeOf E₀ Lat
  chart : ∀ τ : UpperHalfPlane,
    projectiveValue (((X0Branch.model N).complexPoint τ).val ≫ π.left) =
      phiAn E₀ (f.toCuspFormGamma0 χ) Lat κ τ
  zero : projectiveValue ((AtkinPin.infinityPoint N).val ≫ π.left) = 0

namespace GoodRow

variable {R : Type} [CommRing R] [Algebra R ℚ]
  {ell N : ℕ} [Fact ell.Prime] [NeZero N] {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
  {Ebar : WeierstrassCurve (ZMod ell)} {X : PMAdelic.CoarseFibre}
  {E₀ : WeierstrassCurve ℚ} [E₀.IsElliptic] {π : rationalSource N ⟶ ellipticTarget E₀}
  (G : GoodRow R ell N K Ebar X π)

/-- The Atkin–Lehner equation on the rational compact curve. Its sign is
the actual eigenvalue, by the translated point identity at the fixed scale. -/
theorem rationalAffine
    {f : HeckeRing.GL2.Newform N 2} {χ : f.χ = 1} {Lat : PeriodPair} {κ : ℂ}
    (P : FixedAtScale π f χ Lat κ) (q : ℕ) :
    rationalW N q ≫ G.φ = G.φ ^ (AtkinPin.wNew f χ q : ℤ) *
      (toUnit _ ≫ G.translationQ q) := by
  have : IsSeparated G.genericE.hom := inferInstance
  have : Mono G.jE.hom.left := inferInstance
  refine AtkinRational.overRelationAtScale f χ
    (TauCeti.Nat.isExactDivisor_primePow (N := N) (p := q))
    Lat κ P.lattice π.left (Over.w π) P.chart P.zero G.jE.hom.left
    G.φ (toUnit _ ≫ G.translationQ q) ?_ ?_ G.readComplex G.readComplex_eq
  · change (π.left ≫ G.jE.inv.left) ≫ G.jE.hom.left = π.left
    simp
  · have ht : (toUnit (rationalSource N) ≫ G.translationQ q) ≫ G.jE.hom =
        toUnit (rationalSource N) ≫ J0Cusps.infinity N ≫ rationalW N q ≫ π := by
      have hφ : G.φ ≫ G.jE.hom = π := by simp [φ]
      calc
        _ = toUnit (rationalSource N) ≫
            (J0Cusps.infinity N ≫ rationalW N q ≫ G.φ) ≫ G.jE.hom :=
          Category.assoc _ _ _
        _ = toUnit (rationalSource N) ≫ J0Cusps.infinity N ≫
            (rationalW N q ≫ G.φ) ≫ G.jE.hom :=
          congrArg (fun z => toUnit (rationalSource N) ≫ z) (Category.assoc _ _ _)
        _ = toUnit (rationalSource N) ≫ J0Cusps.infinity N ≫ rationalW N q ≫
            (G.φ ≫ G.jE.hom) :=
          congrArg (fun z => toUnit (rationalSource N) ≫ J0Cusps.infinity N ≫ z)
            (Category.assoc _ _ _)
        _ = _ := by rw [hφ]
    exact congrArg CommaMorphism.left ht

/-- The signed relation specializes on the actual Néron extension because
its source operator is tied to the rational involution. -/
theorem integralAffine
    {f : HeckeRing.GL2.Newform N 2} {χ : f.χ = 1} {Lat : PeriodPair} {κ : ℂ}
    (P : FixedAtScale π f χ Lat κ) (q : ℕ) (hq : q.Prime) (he : 0 < N.factorization q) :
    G.W q hq he ≫ G.πInt = G.πInt ^ (AtkinPin.wNew f χ q : ℤ) *
      (toUnit _ ≫ G.translationInt q) := by
  let gen := (generic R ℚ).homMonoidHom (X := G.M) (M := G.E)
  apply (G.neron.2.2.2.2 G.M).injective
  change gen (G.W q hq he ≫ G.πInt) =
    gen (G.πInt ^ (AtkinPin.wNew f χ q : ℤ) * (toUnit _ ≫ G.translationInt q))
  simp only [map_mul, map_zpow, gen, Functor.homMonoidHom_apply, Functor.map_comp,
    G.hInt, G.translationInt_generic]
  rw [← Category.assoc ((generic R ℚ).map (G.W q hq he)), G.W_generic, Category.assoc,
    G.rationalAffine P q, MonObj.comp_mul, GrpObj.comp_zpow]
  have hu : (generic R ℚ).map (toUnit G.M) ≫
        toUnit ((generic R ℚ).obj (𝟙_ (Over (Spec (.of R))))) =
        toUnit ((generic R ℚ).obj G.M) := comp_toUnit _
  rw [← Category.assoc ((generic R ℚ).map (toUnit G.M)), hu,
    ← Category.assoc G.jX, comp_toUnit]

/-- Affine Atkin–Lehner equation on the same residue values used in (O.7). -/
theorem atkin_value
    {f : HeckeRing.GL2.Newform N 2} {χ : f.χ = 1} {Lat : PeriodPair} {κ : ℂ}
    (P : FixedAtScale π f χ Lat κ) (q : ℕ) (hq : q.Prime) (he : 0 < N.factorization q) (x : X.Point) :
    G.value (X.W q x) = (AtkinPin.wNew f χ q : ℤ) • G.value x + G.translation q := by
  apply Subtype.ext
  have hs := AtkinRational.overRelation_baseChange (Spec.map (CommRingCat.ofHom G.closed))
    (G.W q hq he) G.πInt (toUnit G.M ≫ G.translationInt q) (AtkinPin.wNew f χ q : ℤ)
    (G.integralAffine P q hq he)
  have h := congrArg (fun t => (G.read (G.point x ≫ t)).toAdd) hs
  change (G.read (G.point x ≫ G.special.map (G.W q hq he) ≫ G.special.map G.πInt)).toAdd =
    (G.read (G.point x ≫ ((G.special.map G.πInt) ^ (AtkinPin.wNew f χ q : ℤ) *
      G.special.map (toUnit G.M ≫ G.translationInt q)))).toAdd at h
  rw [MonObj.comp_mul, GrpObj.comp_zpow, map_mul, map_zpow] at h
  have hW : G.point (X.W q x) = G.point x ≫ G.special.map (G.W q hq he) :=
    G.point_W q hq he x
  rw [← Category.assoc, ← hW, Functor.map_comp, ← Category.assoc (G.point x)] at h
  have hunit : G.point x ≫ G.special.map (toUnit G.M) = residueUnit G.closed :=
    (IsTerminal.isTerminalObj _ _ isTerminalTensorUnit).hom_ext _ _
  rw [hunit] at h
  exact h

/-- The part of the good Hecke correspondence at a supersingular point.
The indexed targets list every cyclic subgroup, retaining multiplicities. -/
structure HeckePacket (q : ℕ) (x : X.Point) where
  B : Over (Spec (.of R))
  [smoothB : Smooth B.hom]
  source : B ⟶ G.M
  target : Fin (q + 1) → (B ⟶ G.M)
  lift : residueSource ell K ⟶ G.special.obj B
  source_eq : lift ≫ G.special.map source = G.point x
  neighbour : Fin (q + 1) → X.Point
  divisor_eq : X.T q x = ∑ j, of (neighbour j)
  target_eq : ∀ j, lift ≫ G.special.map (target j) = G.point (neighbour j)

attribute [instance] HeckePacket.smoothB

/-- Good Hecke equivariance of the rational map, restricted to the
correspondence chart. Its basedness and the usual generic identity
(T_q∞=(q+1)∞) are used upstream to supply this input. -/
def HeckeIdentity {q : ℕ} {x : X.Point} (T : G.HeckePacket q x) (a : ℤ) : Prop :=
  (List.ofFn fun j => (generic R ℚ).map (T.target j ≫ G.πInt)).prod =
    (generic R ℚ).map (T.source ≫ G.πInt) ^ a

/-- The remaining operator inputs concern only the good Hecke correspondence. -/
structure Relations (ap : ℕ → ℤ) where
  hecke : ∀ q, q.Prime → ¬ q ∣ N * ell → ∀ x ∈ X.ss, G.HeckePacket q x
  eigen : ∀ q hq hg x hx, G.HeckeIdentity (hecke q hq hg x hx) (ap q)

private theorem toAdd_ofFn_prod {A : Type} [AddCommGroup A] {n : ℕ} (f : Fin n → Multiplicative A) :
    (List.ofFn f).prod.toAdd = ∑ i, (f i).toAdd := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    change (f 0).toAdd + (List.ofFn fun j => f j.succ).prod.toAdd = _
    rw [ih]

/-- Néron uniqueness on the smooth Hecke chart gives the relation on the
list of reduced values, with no reduction at a cusp. -/
theorem hecke_values {q : ℕ} {x : X.Point} (T : G.HeckePacket q x) {a : ℤ}
    (ha : G.HeckeIdentity T a) : (∑ j, G.value (T.neighbour j)) = a • G.value x := by
  let gen := (generic R ℚ).homMonoidHom (X := T.B) (M := G.E)
  let l := List.ofFn fun j => T.target j ≫ G.πInt
  have hint : l.prod = (T.source ≫ G.πInt) ^ a := by
    apply (G.neron.2.2.2.2 T.B).injective
    change gen l.prod = gen ((T.source ≫ G.πInt) ^ a)
    rw [map_list_prod, map_zpow, List.map_ofFn]
    exact ha
  let ev := G.readAt T.lift
  have hv := congrArg (fun t => (ev t).toAdd) hint
  change (ev l.prod).toAdd = (ev ((T.source ≫ G.πInt) ^ a)).toAdd at hv
  rw [map_list_prod, map_zpow, List.map_ofFn, toAdd_ofFn_prod] at hv
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


end GoodRow
end ZInQ.Manuscript.RC.PMWire
