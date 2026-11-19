import ZInQKernel.Contrib.CloudB3RC53.Duality.DerivedKummerTrunc
import ZInQKernel.Contrib.CloudB3RC53.Duality.DerivedReduction
import ZInQKernel.Contrib.CloudB3RC53.Duality.KummerTruncIsotropy
import ZInQKernel.Contrib.CloudB3RC53.Torsion.ConeRing
import ZInQKernel.Contrib.TauCeti.Algebra.AddCircle

/-!
# Local Tate duality and the actual finite Kummer condition

The only arithmetic input below is the local duality printed by Milne. The
annihilator assertion and the quotient comparison are conclusions, not fields
of the printed input. The field has characteristic zero, so the argument applies
to every nonarchimedean place, including places above two. No good-reduction or
odd-residue-characteristic assumption occurs.

The elliptic curve is identified with its dual by its canonical principal
polarization. We record the underlying additive isomorphisms of Milne I.3.4.
On the point side the dual consists of finite-order characters. These characters
are continuous: their kernels contain nB(F), which is open by I.3.3.
- pairing data are not postulated by an axiom;
- the printed statement is a Prop parameter;
- its source compatibility is the commuting diagram in the proof of I.3.2.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.DerivedKummer

open TauCeti TauCeti.ContCohomology

abbrev RationalCircle := AddCircle (1 : ℚ)

/-- The finite-order characters of an additive group, the point-side dual in
Milne I.3.4. The topology is forgotten, not replaced by a claim about arbitrary
infinite-order algebraic characters. -/
def finiteCharacters (P : Type*) [AddCommGroup P] : AddSubgroup (P →+ RationalCircle) where
  carrier := {χ | ∃ n : ℕ, 0 < n ∧ ∀ p, n • χ p = 0}
  zero_mem' := ⟨1, Nat.one_pos, by intro p; simp⟩
  add_mem' := by
    rintro χ ψ ⟨n, hn, hχ⟩ ⟨m, hm, hψ⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun p => ?_⟩
    change (n * m) • (χ p + ψ p) = 0
    rw [nsmul_add]
    have h₁ : (n * m) • χ p = 0 := by
      rw [mul_nsmul, hχ, nsmul_zero]
    have h₂ : (n * m) • ψ p = 0 := by
      rw [Nat.mul_comm, mul_nsmul, hψ, nsmul_zero]
    rw [h₁, h₂, add_zero]
  neg_mem' := by
    rintro χ ⟨n, hn, hχ⟩
    exact ⟨n, hn, fun p => by simpa using hχ p⟩

/-- The two isomorphisms of Milne I.3.4, with the compact and discrete topologies
forgotten. `P` denotes B(F), `C` denotes H¹(F,B). -/
structure TateDualityData (P C : Type*) [AddCommGroup P] [AddCommGroup C] where
  pairing : P →+ C →+ RationalCircle
  perfect_left : Function.Bijective pairing
  finite_right : ∀ c, pairing.flip c ∈ finiteCharacters P
  perfect_right : Function.Bijective (pairing.flip.codRestrict (finiteCharacters P) finite_right)

namespace TateDualityData

variable {P C : Type*} [AddCommGroup P] [AddCommGroup C] (D : TateDualityData P C)

/-- Right nondegeneracy is a consequence of the printed isomorphism, not an
extra arithmetic hypothesis. -/
theorem right_injective : Function.Injective D.pairing.flip := by
  intro c c' h
  exact D.perfect_right.1 (Subtype.ext h)

/-- The local Tate pairing detects every Weil--Châtelet class. -/
theorem nondegenerate_right (c : C) (hc : ∀ p, D.pairing p c = 0) : c = 0 := by
  apply D.right_injective
  ext p
  simpa using hc p

abbrev pointMod (n : ℕ) := P ⧸ (nsmulAddMonoidHom (α := P) n).range

/-- Multiplication by n vanishes on P/nP, including when P has finite torsion. -/
theorem pointMod_nsmul_mk (n : ℕ) (p : P) :
    n • (QuotientAddGroup.mk p : pointMod (P := P) n) = 0 := by
  change (QuotientAddGroup.mk (n • p) : pointMod (P := P) n) = 0
  exact (QuotientAddGroup.eq_zero_iff _).2 ⟨p, rfl⟩

/-- The finite pairing H¹(F,B)[n] → Hom(B(F)/nB(F), Q/Z), induced by the
printed full pairing. This definition does not discard any n-torsion. -/
def modPair (n : ℕ) : AddSubgroup.torsionBy C n →+ (pointMod (P := P) n →+ RationalCircle) where
  toFun c := QuotientAddGroup.lift _ (D.pairing.flip c) (by
    rintro _ ⟨p, rfl⟩
    change D.pairing (n • p) c = 0
    rw [map_nsmul, AddMonoidHom.nsmul_apply, ← map_nsmul,
      AddSubgroup.torsionBy.nsmul_iff.mp c.2, map_zero])
  map_zero' := by
    apply AddMonoidHom.ext
    intro q
    induction q using QuotientAddGroup.induction_on with
    | _ p =>
      change D.pairing p 0 = 0
      exact map_zero _
  map_add' c c' := by
    apply AddMonoidHom.ext
    intro q
    induction q using QuotientAddGroup.induction_on with
    | _ p =>
      change D.pairing p ((c : C) + c') = D.pairing p c + D.pairing p c'
      exact map_add _ _ _

/-- The finite comparison is the original local Tate pairing on representatives. -/
theorem modPair_mk (n : ℕ) (c : AddSubgroup.torsionBy C n) (p : P) :
    D.modPair n c (QuotientAddGroup.mk p) = D.pairing p c := rfl

/-- Restricting the printed full duality to n-torsion gives a perfect finite
quotient-to-dual pairing. Surjectivity is proved from the full duality and does
not assume that every isotropic subgroup of a perfect pairing is maximal. -/
theorem modPair_bijective (n : ℕ) (hn : 0 < n) : Function.Bijective (D.modPair n) := by
  constructor
  · intro c c' h
    apply Subtype.ext
    apply D.right_injective
    ext p
    exact congrArg (fun φ => φ (QuotientAddGroup.mk p)) h
  · intro ψ
    let χ : P →+ RationalCircle := ψ.comp (QuotientAddGroup.mk' _)
    have hχn : ∀ p, n • χ p = 0 := by
      intro p
      change n • ψ (QuotientAddGroup.mk p) = 0
      rw [← map_nsmul, pointMod_nsmul_mk, map_zero]
    have hχ : χ ∈ finiteCharacters P := ⟨n, hn, hχn⟩
    obtain ⟨c, hc⟩ := D.perfect_right.2 ⟨χ, hχ⟩
    have hcP : ∀ p, D.pairing p c = χ p := fun p =>
      congrArg (fun f : finiteCharacters P => f.val p) hc
    have hnc : n • c = 0 := D.nondegenerate_right _ (fun p => by
      rw [map_nsmul, hcP]
      exact hχn p)
    refine ⟨⟨c, AddSubgroup.torsionBy.nsmul_iff.mpr hnc⟩, ?_⟩
    apply AddMonoidHom.ext
    intro q
    induction q using QuotientAddGroup.induction_on with
    | _ p => exact hcP p

end TateDualityData

section Arithmetic

variable {F : Type} [Field F] [DecidableEq F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]

/-- The printed local pairings and their printed compatibility, specialized to
an elliptic curve with its canonical principal polarization. This is data, not
an assertion that such data have already been constructed in the library. -/
structure MilneCompatiblePairings where
  duality : TateDualityData B.toAffine.Point (H1 (AbsoluteGaloisGroup F) B.PointCoeff)
  adjoint : ∀ (n : ℕ) (hn : IsUnit (n : F)) (p : B.toAffine.Point)
    (y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff n)),
    ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn (B.kummerMap n hn p) y =
      duality.pairing p (ZInQ.Contrib.CloudB3RC53.Duality.kummerProj B n y)

/-- The existing finite local-duality interface follows from the full printed
pairings. Its nondegeneracy field is discharged by the printed isomorphism. -/
theorem MilneCompatiblePairings.toRC53 (D : MilneCompatiblePairings B) (n : ℕ)
    (hn : IsUnit (n : F)) : ZInQ.Contrib.CloudB3RC53.Duality.MilneLocalTateDualityKummer B n hn :=
  ⟨⟨D.duality.pairing, D.adjoint n hn, fun y _ h => D.duality.nondegenerate_right y h⟩⟩

/-- The actual Kummer image is its exact annihilator for the actual Weil-cup
pairing. No dimension count and no presumed maximal-isotropy field is used. -/
theorem kummer_exact_annihilator (D : MilneCompatiblePairings B) (n : ℕ)
    (hn : IsUnit (n : F)) (y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff n)) :
    y ∈ (B.kummerMap n hn).range ↔
      ∀ x ∈ (B.kummerMap n hn).range,
        ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn x y = 0 :=
  ZInQ.Contrib.CloudB3RC53.Duality.kummerAnnihilatorNode_proof F B n hn (D.toRC53 B n hn) y

/-- The finite local cup product vanishes on two actual Kummer classes. -/
theorem kummer_finite_isotropy (D : MilneCompatiblePairings B) (n : ℕ)
    (hn : IsUnit (n : F)) (p q : B.toAffine.Point) :
    ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn
      (B.kummerMap n hn p) (B.kummerMap n hn q) = 0 :=
  (kummer_exact_annihilator B D n hn _).1 ⟨q, rfl⟩ _ ⟨p, rfl⟩

/-- Exactness of the genuine Kummer sequence, with target H¹(F,B)[n]. -/
theorem ker_torsion_projection (n : ℕ) (hn : IsUnit (n : F)) :
    (B.torsionCoeffInclH1 n).ker = (B.kummerMap n hn).range := by
  rw [WeierstrassCurve.torsionCoeffInclH1, AddMonoidHom.ker_codRestrict]
  exact (B.range_kummerMap n hn).symm

/-- The genuine quotient by the Kummer image is H¹(F,B)[n]. This is proved by
Kummer exactness before any local-duality input is used. -/
def kummerQuotientProjection (n : ℕ) (hn : IsUnit (n : F)) :
    (H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff n) ⧸ (B.kummerMap n hn).range) ≃+
      AddSubgroup.torsionBy (H1 (AbsoluteGaloisGroup F) B.PointCoeff) n :=
  QuotientAddGroup.liftEquiv _ (B.torsionCoeffInclH1_surjective n hn)
    (ker_torsion_projection B n hn).symm

/-- The actual quotient-to-dual comparison. It uses the full local duality,
not an independently chosen abstract isomorphism of groups. -/
def kummerQuotientComparison (D : MilneCompatiblePairings B) (n : ℕ)
    (hn : IsUnit (n : F)) :
    (H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff n) ⧸ (B.kummerMap n hn).range) →+
      (TateDualityData.pointMod (P := B.toAffine.Point) n →+ RationalCircle) :=
  (D.duality.modPair n).comp (kummerQuotientProjection B n hn).toAddMonoidHom

/-- The comparison on representatives is induced by the actual Weil pairing
and local invariant. This equality fixes the map, not just its abstract type. -/
theorem kummerQuotientComparison_mk (D : MilneCompatiblePairings B) (n : ℕ)
    (hn : IsUnit (n : F)) (y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff n))
    (p : B.toAffine.Point) :
    kummerQuotientComparison B D n hn (QuotientAddGroup.mk y) (QuotientAddGroup.mk p) =
      ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn (B.kummerMap n hn p) y := by
  exact (D.adjoint n hn p y).symm

/-- The actual finite quotient-to-dual comparison is perfect, at all finite
levels, including level two. -/
theorem kummerQuotientComparison_bijective (D : MilneCompatiblePairings B) (n : ℕ)
    (hn : IsUnit (n : F)) : Function.Bijective (kummerQuotientComparison B D n hn) := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (by
    intro h
    apply hn.ne_zero
    simp [h])
  exact (D.duality.modPair_bijective n hpos).comp (kummerQuotientProjection B n hn).bijective

end Arithmetic

/-- **PRINTED INPUT**, Milne, *Arithmetic Duality Theorems*, second edition
(2006), Chapter I, Corollary 3.4, printed p. 43 (PDF p. 51):

> "If K has characteristic zero, then there is a canonical pairing
> H^r(K,A^t) × H^{1-r}(K,A) → Q/Z, which induces an isomorphism of compact
> groups A^t(K) → H^1(K,A)^* (case r = 0) and an isomorphism of discrete
> groups of cofinite-type H^1(K,A^t) → A(K)^* (case r = 1)."

Compatibility is part of the printed commuting diagram in the proof of
Theorem 3.2, printed p. 42 (PDF p. 50):

> "if we take α^r(G,A_n) to be the map α^r(G,A_n(K^s)) of §2, then it is clear
> that the diagram commutes."

Remark 3.5, printed p. 44 (PDF p. 52), identifies these maps with the Weil-cup
maps:

> "It is possible to show that these pairings agree with those in (3.4)
> (up to sign) by checking that each is compatible with the pairings
> H^r(K,A^t_n) × H^{2-r}(K,A_n) → H^2(K,G_m) defined by the e_n-pairing."

We choose the common sign convention in the Tate pairing. This is the
underlying additive form of those printed isomorphisms and their compatibility,
specialized by the canonical principal polarization of an elliptic curve. The
open-subgroup assertion in Lemma 3.3, printed p. 41, identifies the continuous
finite-order point characters with `finiteCharacters`. The source is bibliography
item `milne`: https://www.jmilne.org/math/Books/ADTnot.pdf.

This Prop is not given an unconditional inhabitant. -/
def MilneLocalDualityPrint : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic],
    Nonempty (MilneCompatiblePairings B)

/-- The exact annihilator assertion follows from the cited print in its
characteristic-zero scope, for every finite level invertible in the field. -/
theorem kummer_exact_annihilator_of_print (hM : MilneLocalDualityPrint)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
    (n : ℕ) (hn : IsUnit (n : F)) (y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff n)) :
    y ∈ (B.kummerMap n hn).range ↔
      ∀ x ∈ (B.kummerMap n hn).range,
        ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn x y = 0 := by
  obtain ⟨D⟩ := hM F B
  exact kummer_exact_annihilator B D n hn y

/-- **The actual mod-two quotient-to-dual comparison**, with its exact
Weil-cup evaluation rule. The degree-zero torsion is not removed from B(F). -/
theorem kummer_modTwo_comparison_of_print (hM : MilneLocalDualityPrint)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
    (h2 : IsUnit (2 : F)) :
    ∃ e : (H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) ⧸ (B.kummerMap 2 h2).range) ≃+
        (TateDualityData.pointMod (P := B.toAffine.Point) 2 →+ RationalCircle),
      ∀ (y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2)) (p : B.toAffine.Point),
        e (QuotientAddGroup.mk y) (QuotientAddGroup.mk p) =
          ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 h2 (B.kummerMap 2 h2 p) y := by
  obtain ⟨D⟩ := hM F B
  exact ⟨AddEquiv.ofBijective (kummerQuotientComparison B D 2 h2)
    (kummerQuotientComparison_bijective B D 2 h2), kummerQuotientComparison_mk B D 2 h2⟩

section ResidueAlgebra

variable (n : ℕ) [NeZero n]

/-- The canonical embedding k mod n ↦ k/n mod Z, with its exact torsion target. -/
def zmodToCircleTorsion : ZMod n →+ AddSubgroup.torsionBy RationalCircle n :=
  (ZMod.toRatAddCircle n).codRestrict _ (by
    intro k
    rw [← ZMod.toRatAddCircle_range]
    exact ⟨k, rfl⟩)

/-- Q/Z[n] is canonically Z/nZ, without choosing a primitive root or a
noncanonical top-coefficient functional. -/
def circleTorsionEquiv : AddSubgroup.torsionBy RationalCircle n ≃+ ZMod n :=
  (AddEquiv.ofBijective (zmodToCircleTorsion n) ⟨
    fun a b h => ZMod.toRatAddCircle_injective n (congrArg Subtype.val h),
    fun z => by
      obtain ⟨a, ha⟩ := ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero n
        (AddSubgroup.torsionBy.nsmul_iff.mp z.2)
      exact ⟨a, Subtype.ext ha⟩⟩).symm

/-- The value dictionary preserves the actual invariant normalization. -/
theorem circleTorsionEquiv_toRat (z : AddSubgroup.torsionBy RationalCircle n) :
    ZMod.toRatAddCircle n (circleTorsionEquiv n z) = z.val :=
  congrArg Subtype.val ((AddEquiv.ofBijective (zmodToCircleTorsion n) ⟨
    fun a b h => ZMod.toRatAddCircle_injective n (congrArg Subtype.val h),
    fun z => by
      obtain ⟨a, ha⟩ := ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero n
        (AddSubgroup.torsionBy.nsmul_iff.mp z.2)
      exact ⟨a, Subtype.ext ha⟩⟩).apply_symm_apply z)

variable {V : Type*} [AddCommGroup V] (hV : ∀ v : V, n • v = 0)

/-- A character of an n-torsion group has values in Q/Z[n]. -/
def charactersIntoTorsion : (V →+ RationalCircle) ≃+
    (V →+ AddSubgroup.torsionBy RationalCircle n) where
  toFun ψ := ψ.codRestrict _ (fun v => AddSubgroup.torsionBy.nsmul_iff.mpr
    (by rw [← map_nsmul, hV, map_zero]))
  invFun ψ := (AddSubgroup.torsionBy RationalCircle n).subtype.comp ψ
  left_inv ψ := by ext v; rfl
  right_inv ψ := by ext v; rfl
  map_add' ψ χ := by ext v; rfl

/-- Characters into Q/Z and into Z/nZ agree for an n-torsion group. -/
def charactersToZMod : (V →+ RationalCircle) ≃+ (V →+ ZMod n) :=
  (charactersIntoTorsion n hV).trans (AddEquiv.addMonoidHomCongrRight (circleTorsionEquiv n))

/-- The dictionary reads a residue value as its canonical local invariant. -/
theorem charactersToZMod_apply (ψ : V →+ RationalCircle) (v : V) :
    ZMod.toRatAddCircle n (charactersToZMod n hV ψ v) = ψ v :=
  circleTorsionEquiv_toRat n _

end ResidueAlgebra

/-- The canonical F₂-module structure on B(F)/2B(F), without removing torsion. -/
instance pointModTwoModule (P : Type*) [AddCommGroup P] :
    Module (ZMod 2) (TateDualityData.pointMod (P := P) 2) :=
  AddCommGroup.zmodModule (fun q => by
    induction q using QuotientAddGroup.induction_on with
    | _ p => exact TateDualityData.pointMod_nsmul_mk 2 p)

/-- The point quotient is killed by two, a fact independent of local duality. -/
theorem pointModTwo_nsmul (P : Type*) [AddCommGroup P]
    (q : TateDualityData.pointMod (P := P) 2) : 2 • q = 0 := by
  induction q using QuotientAddGroup.induction_on with
  | _ p => exact TateDualityData.pointMod_nsmul_mk 2 p

section ModTwo

variable {F : Type} [Field F] [DecidableEq F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]

/-- The actual cohomology H¹(F,B[2]) is an F₂-module because its coefficients
are killed by two. -/
instance actualH1TwoModule : Module (ZMod 2) (H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2)) :=
  AddCommGroup.zmodModule (nsmul_H1_eq_zero (fun p =>
    Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp p.2)))

/-- The actual quotient by the Kummer image has the induced F₂ structure. -/
instance kummerQuotientTwoModule (h2 : IsUnit (2 : F)) :
    Module (ZMod 2)
      (H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) ⧸ (B.kummerMap 2 h2).range) :=
  QuotientAddGroup.zmodModule (fun y => by
    rw [nsmul_H1_eq_zero (fun p => Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp p.2)) y]
    exact (B.kummerMap 2 h2).range.zero_mem)

/-- The coefficient-valued mod-two comparison, as an F₂-linear map to the
F₂-linear dual of the actual point quotient. -/
def kummerModTwoLinearComparison (D : MilneCompatiblePairings B) (h2 : IsUnit (2 : F)) :
    (H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) ⧸ (B.kummerMap 2 h2).range) →ₗ[ZMod 2]
      (TateDualityData.pointMod (P := B.toAffine.Point) 2 →ₗ[ZMod 2] ZMod 2) :=
  (((AddMonoidHom.toZModLinearMapEquiv 2).toAddMonoidHom).comp
    ((charactersToZMod 2 (pointModTwo_nsmul B.toAffine.Point)).toAddMonoidHom.comp
      (kummerQuotientComparison B D 2 h2))).toZModLinearMap 2

/-- The actual residue comparison is bijective as a coefficient-valued linear
map, not merely as a group comparison tested by a scalar functional. -/
theorem kummerModTwoLinearComparison_bijective (D : MilneCompatiblePairings B)
    (h2 : IsUnit (2 : F)) : Function.Bijective (kummerModTwoLinearComparison B D h2) :=
  (AddMonoidHom.toZModLinearMapEquiv 2).bijective.comp
    ((charactersToZMod 2 (pointModTwo_nsmul B.toAffine.Point)).bijective.comp
      (kummerQuotientComparison_bijective B D 2 h2))

/-- The linear comparison has exactly the Weil-cup invariant normalization. -/
theorem kummerModTwoLinearComparison_mk (D : MilneCompatiblePairings B)
    (h2 : IsUnit (2 : F)) (y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2))
    (p : B.toAffine.Point) :
    ZMod.toRatAddCircle 2
      (kummerModTwoLinearComparison B D h2 (QuotientAddGroup.mk y) (QuotientAddGroup.mk p)) =
      ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 h2 (B.kummerMap 2 h2 p) y := by
  change ZMod.toRatAddCircle 2
    (charactersToZMod 2 (pointModTwo_nsmul B.toAffine.Point)
      (kummerQuotientComparison B D 2 h2 (QuotientAddGroup.mk y)) (QuotientAddGroup.mk p)) = _
  rw [charactersToZMod_apply, kummerQuotientComparison_mk]

/-- The degree-two local Weil-cup invariant paired with a rational n-torsion
point. This is the r = 2 comparison in Milne I.2.3 under elliptic self-duality. -/
def localH2TorsionValue (n : ℕ) (hn : IsUnit (n : F))
    (y : H2 (AbsoluteGaloisGroup F) (B.TorsionCoeff n))
    (t : AddSubgroup.torsionBy B.toAffine.Point n) : RationalCircle :=
  TauCeti.ClassFieldTheory.invMap F
    (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n
      (explicitCoeff2 (AbsoluteGaloisGroup F) (B.TorsionCoeff n)
        (B.weilPairingCoeff n hn t) continuous_of_discreteTopology y))

/-- The finite torsion in degree zero is an F₂-module. -/
instance actualTwoTorsionModule : Module (ZMod 2) (AddSubgroup.torsionBy B.toAffine.Point 2) :=
  AddCommGroup.zmodModule (fun t => Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp t.2))

/-- The actual degree-two cohomology is an F₂-module. -/
instance actualH2TwoModule : Module (ZMod 2) (H2 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2)) :=
  AddCommGroup.zmodModule (nsmul_H2_eq_zero (fun p =>
    Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp p.2)))

end ModTwo

/-- **PRINTED INPUT**, Milne, *Arithmetic Duality Theorems*, second edition
(2006), Chapter I, Corollary 2.3, printed p. 28 (PDF p. 36):

> "Let M be a finitely generated G-module whose torsion subgroup has order
> prime to char(K). Then cup-product defines isomorphisms
> H^r(G,M^D) → H^{2-r}(G,M)^* for all r ≥ 1, and an isomorphism (of compact
> groups) H^0(G,M^D)^∧ → H^2(G,M)^*. The groups H^1(G,M) and H^1(G,M^D)
> are finite."

Here M is the actual finite coefficient module B[n], and M^D is identified
with B[n] by the perfect Weil pairing. This records the degree-one perfect
pairing and the degree-two isomorphism to the dual of the actual rational
torsion. Finiteness of the coefficient module makes completion in degree zero
unnecessary. Characteristic zero, not odd residue characteristic, is the scope.
The source is bibliography item `milne`:
https://www.jmilne.org/math/Books/ADTnot.pdf.

No claim about the Kummer annihilator or a comparison cone is included in this
printed leaf. The two adjoints at degree one are the finite cup-product duality
under the two Weil identifications. This Prop has no unconditional inhabitant. -/
def MilneFiniteLocalDualityPrint : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
    (n : ℕ) (hn : IsUnit (n : F)),
    Finite (H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff n)) ∧
      Function.Bijective (ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn) ∧
      Function.Bijective (ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn).flip ∧
      ∃ e : H2 (AbsoluteGaloisGroup F) (B.TorsionCoeff n) ≃+
          (AddSubgroup.torsionBy B.toAffine.Point n →+ RationalCircle),
        ∀ y t, e y t = localH2TorsionValue B n hn y t

/-- The coefficient-valued mod-two quotient comparison follows from the full
printed duality and its commuting Kummer diagram. -/
theorem kummer_modTwo_linear_comparison_of_print (hM : MilneLocalDualityPrint)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
    (h2 : IsUnit (2 : F)) :
    ∃ e : (H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) ⧸ (B.kummerMap 2 h2).range) ≃ₗ[ZMod 2]
        (TateDualityData.pointMod (P := B.toAffine.Point) 2 →ₗ[ZMod 2] ZMod 2),
      ∀ (y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2)) (p : B.toAffine.Point),
        ZMod.toRatAddCircle 2 (e (QuotientAddGroup.mk y) (QuotientAddGroup.mk p)) =
          ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 h2 (B.kummerMap 2 h2 p) y := by
  obtain ⟨D⟩ := hM F B
  exact ⟨LinearEquiv.ofBijective (kummerModTwoLinearComparison B D h2)
    (kummerModTwoLinearComparison_bijective B D h2), kummerModTwoLinearComparison_mk B D h2⟩

/-- The second component of the actual mod-two comparison retains the entire
degree-zero torsion B(F)[2]. Omitting this component would not prove derived
local orthogonality. -/
theorem kummer_modTwo_torsion_comparison_of_print (hM : MilneFiniteLocalDualityPrint)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
    (h2 : IsUnit (2 : F)) :
    ∃ e : H2 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) ≃ₗ[ZMod 2]
        (AddSubgroup.torsionBy B.toAffine.Point 2 →ₗ[ZMod 2] ZMod 2),
      ∀ (y : H2 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2))
        (t : AddSubgroup.torsionBy B.toAffine.Point 2),
        ZMod.toRatAddCircle 2 (e y t) = localH2TorsionValue B 2 h2 y t := by
  obtain ⟨_, _, _, e, he⟩ := hM F B 2 h2
  let χ := charactersToZMod 2 (fun t : AddSubgroup.torsionBy B.toAffine.Point 2 =>
    Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp t.2))
  let f := ((AddMonoidHom.toZModLinearMapEquiv 2).toAddMonoidHom.comp
    (χ.toAddMonoidHom.comp e.toAddMonoidHom)).toZModLinearMap 2
  have hf : Function.Bijective f :=
    (AddMonoidHom.toZModLinearMapEquiv 2).bijective.comp (χ.bijective.comp e.bijective)
  refine ⟨LinearEquiv.ofBijective f hf, fun y t => ?_⟩
  change ZMod.toRatAddCircle 2 (charactersToZMod 2 _ (e y) t) = _
  rw [charactersToZMod_apply, he]

section IntegralIsotropy

open ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

/-- The canonical finite local-invariant normalization of a two-adic trace. -/
def padicInvariant (a : ℕ) : ℤ_[2] →+ RationalCircle :=
  (ZMod.toRatAddCircle (2 ^ a)).comp (PadicInt.toZModPow a).toAddMonoidHom

/-- The finite invariant vanishes precisely on multiples of 2^a. -/
theorem padicInvariant_eq_zero_iff (a : ℕ) (z : ℤ_[2]) :
    padicInvariant a z = 0 ↔ (2 : ℤ_[2]) ^ a ∣ z := by
  have : NeZero (2 ^ a) := ⟨pow_ne_zero a (by decide)⟩
  change ZMod.toRatAddCircle (2 ^ a) (PadicInt.toZModPow a z) = 0 ↔ _
  rw [ZMod.toRatAddCircle_eq_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]
  norm_num

/-- Every power of two is invertible in a characteristic-zero field, including
when the residue characteristic is two. -/
theorem twoPower_isUnit (F : Type) [Field F] [CharZero F] (a : ℕ) :
    IsUnit (((2 ^ a : ℕ) : F)) :=
  isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (pow_ne_zero a (by decide)))

/-- Finite isotropy for the actual Kummer classes discharges the divisibility
hypothesis in the integral truncation theorem. `hred` is the precise remaining
identification of the integral trace with the actual finite cup products. -/
theorem actualCup_divisible_of_print (hM : MilneLocalDualityPrint)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
    {X Y : Type*} (β : X → Y → ℤ_[2])
    (hred : ∀ (a : ℕ) (x : X) (y : Y), ∃ p q : B.toAffine.Point,
      padicInvariant a (β x y) =
        ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B (2 ^ a) (twoPower_isUnit F a)
          (B.kummerMap (2 ^ a) (twoPower_isUnit F a) p)
          (B.kummerMap (2 ^ a) (twoPower_isUnit F a) q)) :
    ∀ (a : ℕ) (x : X) (y : Y), (2 : ℤ_[2]) ^ a ∣ β x y := by
  obtain ⟨D⟩ := hM F B
  intro a x y
  obtain ⟨p, q, hpq⟩ := hred a x y
  exact (padicInvariant_eq_zero_iff a _).1
    (hpq.trans (kummer_finite_isotropy B D (2 ^ a) (twoPower_isUnit F a) p q))

/-- The zero integral truncated isotropy homotopy, constructed from the printed
local duality and explicit integral-to-finite trace compatibility. The trace
kernel and the two-term bounds are exactly the existing truncation interface;
no untruncated homotopy is claimed. -/
def kummerTruncIsotropy_from_print (hM : MilneLocalDualityPrint)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
    {U U' L L' E : GCx ℤ_[2]} (ι : GHom U L) (ι' : GHom U' L') (P : GPair L L' E)
    (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside U' (fun i => i = 0 ∨ i = 1))
    (trv : E.X 2 →ₗ[ℤ_[2]] ℤ_[2]) (htrv : ∀ y, trv (E.d 1 2 rfl y) = 0)
    (hker : ∀ z : E.X 2, E.d 2 3 rfl z = 0 → trv z = 0 → ∃ y, E.d 1 2 rfl y = z)
    (hred : ∀ (a : ℕ) (u : U.X 1) (v : U'.X 1), ∃ p q : B.toAffine.Point,
      padicInvariant a (trv (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι'.f 1 1 rfl v))) =
        ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B (2 ^ a) (twoPower_isUnit F a)
          (B.kummerMap (2 ^ a) (twoPower_isUnit F a) p)
          (B.kummerMap (2 ^ a) (twoPower_isUnit F a) q)) :
    ZInQ.Contrib.CloudB3RC53.Duality.LocalTruncIsotropy ι ι' P :=
  ZInQ.Contrib.CloudB3RC53.Duality.kummerTruncIsotropy_two hU hU' trv htrv hker
    (actualCup_divisible_of_print hM F B
      (fun u v => trv (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι'.f 1 1 rfl v))) hred)

end IntegralIsotropy

section ActualDerivedReduction

open ZInQ.Contrib.CloudB3RC53.Duality

/-- Pullback of characters along an explicit additive equivalence. -/
def pullCharacterEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    (B →+ RationalCircle) ≃+ (A →+ RationalCircle) where
  toFun χ := χ.comp e.toAddMonoidHom
  invFun χ := χ.comp e.symm.toAddMonoidHom
  left_inv χ := by
    ext b
    change χ (e (e.symm b)) = χ b
    rw [e.apply_symm_apply]
  right_inv χ := by
    ext a
    change χ (e.symm (e a)) = χ a
    rw [e.symm_apply_apply]
  map_add' χ ψ := by ext a; rfl

variable {F : Type} [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  {P₁ P₀ M : Type*} [AddCommGroup P₁] [Module ℤ_[2] P₁]
  [AddCommGroup P₀] [Module ℤ_[2] P₀] [AddCommGroup M] [Module ℤ_[2] M]
  (f : P₁ →ₗ[ℤ_[2]] P₀) (g : P₀ →ₗ[ℤ_[2]] M)

/-- Degree zero of the actual derived reduction, in the supplied presentation. -/
abbrev reductionH0 := LinearMap.ker (reduction (2 : ℤ_[2]) f)

/-- Degree one of the actual derived reduction, in the supplied presentation. -/
abbrev reductionH1 :=
  ((P₀ ⧸ nSub (2 : ℤ_[2]) P₀) ⧸ LinearMap.range (reduction (2 : ℤ_[2]) f))

/-- The algebraic degree-zero identification, followed by the explicit
identification of the completion's torsion with actual rational torsion. -/
def derivedH0Identification (hfg : g.comp f = 0) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : ∀ y, g y = 0 → ∃ x, f x = y)
    (hreg : IsSMulRegular P₀ (2 : ℤ_[2]))
    (η₀ : torsionN (2 : ℤ_[2]) M ≃+ AddSubgroup.torsionBy B.toAffine.Point 2) :
    reductionH0 f ≃+ AddSubgroup.torsionBy B.toAffine.Point 2 :=
  (kerReduction_equiv hfg hf hg hex hreg).toAddEquiv.trans η₀

/-- The algebraic degree-one identification, followed by the explicit
identification of the completion modulo two with the actual point quotient. -/
def derivedH1Identification (hfg : g.comp f = 0) (hg : Function.Surjective g)
    (hex : ∀ y, g y = 0 → ∃ x, f x = y)
    (η₁ : (M ⧸ nSub (2 : ℤ_[2]) M) ≃+ TateDualityData.pointMod (P := B.toAffine.Point) 2) :
    reductionH1 f ≃+ TateDualityData.pointMod (P := B.toAffine.Point) 2 :=
  (cokerReduction_equiv hfg hg hex).toAddEquiv.trans η₁

/-- The two components of the actual derived mod-two quotient-to-dual
comparison. Degree zero is retained through `kerReduction_equiv`, not set to
zero. The point-quotient and torsion identifications of the actual completion
are displayed as η₁ and η₀; their construction is not silently replaced by an
abstract isomorphism of unrelated finite models. Both evaluation rules fix the
actual local cup maps. -/
theorem derived_modTwo_comparisons_of_print
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (h2 : IsUnit (2 : F)) (hfg : g.comp f = 0) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : ∀ y, g y = 0 → ∃ x, f x = y)
    (hreg : IsSMulRegular P₀ (2 : ℤ_[2]))
    (η₀ : torsionN (2 : ℤ_[2]) M ≃+ AddSubgroup.torsionBy B.toAffine.Point 2)
    (η₁ : (M ⧸ nSub (2 : ℤ_[2]) M) ≃+ TateDualityData.pointMod (P := B.toAffine.Point) 2) :
    (∃ e : (H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) ⧸ (B.kummerMap 2 h2).range) ≃+
        (reductionH1 f →+ RationalCircle),
      ∀ (y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2)) (r : reductionH1 f)
        (p : B.toAffine.Point),
        derivedH1Identification B f g hfg hg hex η₁ r = QuotientAddGroup.mk p →
        e (QuotientAddGroup.mk y) r = localTatePairing B 2 h2 (B.kummerMap 2 h2 p) y) ∧
      (∃ e : H2 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) ≃+ (reductionH0 f →+ RationalCircle),
        ∀ (y : H2 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2)) (r : reductionH0 f),
          e y r = localH2TorsionValue B 2 h2 y
            (derivedH0Identification B f g hfg hf hg hex hreg η₀ r)) := by
  obtain ⟨e₁, h₁⟩ := kummer_modTwo_comparison_of_print hM F B h2
  obtain ⟨_, _, _, e₀, h₀⟩ := hF F B 2 h2
  let q := derivedH1Identification B f g hfg hg hex η₁
  let t := derivedH0Identification B f g hfg hf hg hex hreg η₀
  constructor
  · refine ⟨e₁.trans (pullCharacterEquiv q), fun y r p hp => ?_⟩
    change e₁ (QuotientAddGroup.mk y) (q r) = _
    rw [show q r = QuotientAddGroup.mk p from hp]
    exact h₁ y p
  · refine ⟨e₀.trans (pullCharacterEquiv t), fun y r => ?_⟩
    exact h₀ y (t r)

end ActualDerivedReduction

end ZInQ.Contrib.RC53Assist.DerivedKummer
