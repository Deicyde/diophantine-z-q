import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.FrobeniusTrace
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Bilinear
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
import ZInQKernel.Contrib.TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Determinants and degrees of endomorphisms

The determinant on the Tate module is recovered from the alternating,
nondegenerate Weil pairing at each prime-power torsion level. No pairing
on an inverse limit of roots of unity is needed.

The zero endomorphism, separable endomorphisms, and multiplication by
any integer satisfy the determinant--degree identity without any new
geometric input. The full proposition `DetEqDegree` reduces to the named
PRINT `InseparableWeilPairingCompatibility`, stated only for nonzero
inseparable endomorphisms of the reduced curve.

The Frobenius determinant-form slice `det(1 - n π) = 1 - a n + p n²`
is proved without that PRINT: `n π - 1` is separable. Consequently the
good-reduction Frobenius trace dictionary requires only the reduction
comparison, not the full determinant--degree proposition.

References: Silverman, The Arithmetic of Elliptic Curves, III.4,
III.6, III.7, III.8.1, III.8.2, III.8.6, V.2.3, VII.3.1, and VII.7.1.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.DetDegree

open Module TauCeti TauCeti.Isogeny
open scoped Classical

/-- **PROVED theorem** (Silverman III.7 and III.8.1): if an additive
endomorphism scales every prime-power Weil pairing by the natural number
`d`, its determinant on the Tate module is `d`. -/
theorem det_tate_eq_of_weilPairing_compatibility
    {K : Type*} [Field K] [IsSepClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (α : E.toAffine.Point →+ E.toAffine.Point) (d : ℕ)
    (h : ∀ (n : ℕ) (S T : TateModuleLevel ℓ E.toAffine.Point n),
      weilPairing E (ℓ ^ n) (by simpa using pow_ne_zero n hℓ)
          (TateModule.levelMap (p := ℓ) α n S)
          (TateModule.levelMap (p := ℓ) α n T) =
        d • weilPairing E (ℓ ^ n) (by simpa using pow_ne_zero n hℓ) S T) :
    LinearMap.det (TateModule.mapLinearMap (p := ℓ) α) = (d : ℤ_[ℓ]) := by
  classical
  have hprime : ℓ.Prime := Fact.out
  let : NeZero ℓ := ⟨hprime.ne_zero⟩
  obtain ⟨e⟩ := E.nonempty_linearEquiv_tateModule hℓ
  let b : Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) :=
    (Pi.basisFun ℤ_[ℓ] (Fin 2)).map e.symm
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  let : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hprime.ne_zero⟩
  have hN : ((ℓ ^ n : ℕ) : K) ≠ 0 := by simpa using pow_ne_zero n hℓ
  let : Module ℤ_[ℓ] (Additive (rootsOfUnity (ℓ ^ n) K)) :=
    Module.compHom (Additive (rootsOfUnity (ℓ ^ n) K)) (PadicInt.toZModPow n)
  let B : TateModule ℓ E.toAffine.Point →ₗ[ℤ_[ℓ]]
      TateModule ℓ E.toAffine.Point →ₗ[ℤ_[ℓ]] Additive (rootsOfUnity (ℓ ^ n) K) :=
    LinearMap.mk₂ ℤ_[ℓ]
      (fun X Y => weilPairing E (ℓ ^ n) hN (TateModule.proj n X) (TateModule.proj n Y))
      (fun X Y Z => by simp only [map_add, AddMonoidHom.add_apply])
      (fun c X Y => by
        change weilPairing E (ℓ ^ n) hN (TateModule.proj n (c • X)) (TateModule.proj n Y) =
          PadicInt.toZModPow n c •
            weilPairing E (ℓ ^ n) hN (TateModule.proj n X) (TateModule.proj n Y)
        rw [TateModule.proj_smul, weilPairing_zmod_smul_left])
      (fun X Y Z => by simp only [map_add])
      (fun c X Y => by
        change weilPairing E (ℓ ^ n) hN (TateModule.proj n X) (TateModule.proj n (c • Y)) =
          PadicInt.toZModPow n c •
            weilPairing E (ℓ ^ n) hN (TateModule.proj n X) (TateModule.proj n Y)
        rw [TateModule.proj_smul, weilPairing_zmod_smul_right])
  have hB : B.IsAlt := fun X => weilPairing_self E (ℓ ^ n) hN (TateModule.proj n X)
  have hscale := hB.compl₁₂_self_eq_det_smul b (TateModule.mapLinearMap (p := ℓ) α)
  have heq (X Y : TateModule ℓ E.toAffine.Point) :
      PadicInt.toZModPow n (LinearMap.det (TateModule.mapLinearMap (p := ℓ) α)) •
          weilPairing E (ℓ ^ n) hN (TateModule.proj n X) (TateModule.proj n Y) =
        (d : ZMod (ℓ ^ n)) •
          weilPairing E (ℓ ^ n) hN (TateModule.proj n X) (TateModule.proj n Y) := by
    have hs := congrArg (fun C => C X Y) hscale
    change weilPairing E (ℓ ^ n) hN
        (TateModule.proj n (TateModule.mapLinearMap (p := ℓ) α X))
        (TateModule.proj n (TateModule.mapLinearMap (p := ℓ) α Y)) =
      PadicInt.toZModPow n (LinearMap.det (TateModule.mapLinearMap (p := ℓ) α)) •
        weilPairing E (ℓ ^ n) hN (TateModule.proj n X) (TateModule.proj n Y) at hs
    rw [TateModule.mapLinearMap_apply, TateModule.mapLinearMap_apply,
      TateModule.proj_map, TateModule.proj_map,
      h n (TateModule.proj n X) (TateModule.proj n Y)] at hs
    simpa only [Nat.cast_smul_eq_nsmul] using hs.symm
  have hproj : Function.Surjective
      (TateModule.proj (p := ℓ) (A := E.toAffine.Point) n) :=
    TateModule.proj_surjective
      (TateModule.tateModuleTransition_surjective_of_natCard hprime.ne_zero
        (E.natCard_tateModuleLevel hℓ)) n
  obtain ⟨bn⟩ := WeierstrassCurve.nonempty_basis_torsionBy E (ℓ ^ n) hN
  have hzero : PadicInt.toZModPow n (LinearMap.det (TateModule.mapLinearMap (p := ℓ) α)) -
      (d : ZMod (ℓ ^ n)) = 0 := by
    apply (isAlt_weilPairingBilin E (ℓ ^ n) hN).eq_zero_of_smul_apply_basis_eq_zero bn
      (separatingLeft_weilPairingBilin E (ℓ ^ n) hN)
    rw [sub_smul, sub_eq_zero, weilPairingBilin_apply]
    obtain ⟨X, hX⟩ := hproj (bn 0)
    obtain ⟨Y, hY⟩ := hproj (bn 1)
    simpa only [hX, hY] using heq X Y
  simpa only [map_natCast] using sub_eq_zero.mp hzero

/-- **PROVED theorem** (Silverman III.8.2 and III.8.6): the determinant
is the degree for a separable endomorphism, using its given additive
point map. -/
theorem detEqDegree_separable
    {K : Type*} [Field K] [IsSepClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (φ : TauCeti.Isogeny E.toAffine E.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange E.toAffine.FunctionField]
    (α : E.toAffine.Point →+ E.toAffine.Point)
    (hα : ∀ P, (Hom.ofIsogeny φ).pointMap P = α P) :
    LinearMap.det (TateModule.mapLinearMap (p := ℓ) α) = (φ.degree : ℤ_[ℓ]) := by
  apply det_tate_eq_of_weilPairing_compatibility E ℓ hℓ α φ.degree
  intro n S T
  have hmap (U : TateModuleLevel ℓ E.toAffine.Point n) :
      TateModule.levelMap (p := ℓ) α n U =
        ZInQ.Contrib.CloudB3RC53.WeilIsogeny.torsionMap φ (ℓ ^ n) U :=
    Subtype.ext (hα U).symm
  rw [hmap S, hmap T]
  exact ZInQ.Contrib.CloudB3RC53.WeilIsogeny.weilPairing_torsionMap φ (ℓ ^ n)
    (by simpa using pow_ne_zero n hℓ) S T

/-- **PROVED theorem** (Silverman III.7 and III.8.6): the zero
endomorphism has determinant and degree zero when the Tate prime is
invertible in the field. -/
theorem detEqDegree_zero
    {K : Type*} [Field K] [IsSepClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (α : E.toAffine.Point →+ E.toAffine.Point)
    (hα : ∀ P, (0 : Hom E.toAffine E.toAffine).pointMap P = α P) :
    LinearMap.det (TateModule.mapLinearMap (p := ℓ) α) =
      ((0 : Hom E.toAffine E.toAffine).degree : ℤ_[ℓ]) := by
  rw [Hom.degree_zero]
  apply det_tate_eq_of_weilPairing_compatibility E ℓ hℓ α 0
  intro n S T
  have hz (U : TateModuleLevel ℓ E.toAffine.Point n) :
      TateModule.levelMap (p := ℓ) α n U = 0 := by
    apply Subtype.ext
    change α U = 0
    exact (hα (U : E.toAffine.Point)).symm.trans
      (Hom.zero_pointMap (W₁ := E.toAffine) (W₂ := E.toAffine) (U : E.toAffine.Point))
  simp only [hz S, hz T, map_zero, zero_smul]

/-- **PROVED theorem** (Silverman III.4, III.6, and III.8.6): the
endomorphism multiplication by any integer has determinant equal to its
degree, including inseparable multiplication maps. -/
theorem detEqDegree_integer_multiplication
    {K : Type*} [Field K] [IsSepClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) (k : ℤ)
    (α : E.toAffine.Point →+ E.toAffine.Point)
    (hα : ∀ P, (k • Hom.id E.toAffine).pointMap P = α P) :
    LinearMap.det (TateModule.mapLinearMap (p := ℓ) α) =
      ((k • Hom.id E.toAffine).degree : ℤ_[ℓ]) := by
  let : Module.Free ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) := E.free_tateModule hℓ
  let : Module.Finite ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) := E.finite_tateModule hℓ
  have ha : α = k • AddMonoidHom.id E.toAffine.Point := by
    apply AddMonoidHom.ext
    intro P
    change α P = k • P
    exact (hα P).symm.trans (by rw [Hom.zsmul_pointMap, Hom.id_pointMap])
  rw [ha, ZInQ.Contrib.CloudB3RC53.ModularWeil.mapLinearMap_zsmul,
    ZInQ.Contrib.CloudB3RC53.ModularWeil.mapLinearMap_id, LinearMap.det_smul,
    E.finrank_tateModule hℓ, map_one, mul_one,
    Hom.degree_zsmul, Hom.degree_id, mul_one]
  have hsq : (k.natAbs : ℤ) ^ 2 = k ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
  simpa only [Int.cast_pow, Nat.cast_pow, Int.cast_natCast] using
    congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hsq.symm

open ZInQ.Contrib.CloudB3RC53.ModularWeil

/-- **PROVED theorem** (Silverman V.2.3 and III.8.6): the determinant
form `det(1 - n π) = 1 - a n + p n²` requires only the separable
endomorphisms `n π - 1`. Thus no inseparable-pairing input is needed for
this slice of the Frobenius determinant form. -/
theorem frobeniusTateDetFormOne_proved : FrobeniusTateDetFormOne := by
  intro p _ Et hEt ℓ _ hℓ n
  have : Et.IsElliptic := hEt
  have hℓK : (ℓ : AlgebraicClosure (ZMod p)) ≠ 0 := by
    intro h0
    have h0' : (ℓ : ZMod p) = 0 := by
      apply (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
      simpa only [map_natCast, map_zero] using h0
    have hdiv : p ∣ ℓ := (CharP.cast_eq_zero_iff (ZMod p) p ℓ).mp h0'
    have heq : p = ℓ := ((Nat.dvd_prime (Fact.out : ℓ.Prime)).mp hdiv).resolve_left
      (Fact.out : p.Prime).ne_one
    exact hℓ heq.symm
  let E := Et.baseChange (AlgebraicClosure (ZMod p))
  let : Module.Free ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) := E.free_tateModule hℓK
  let : Module.Finite ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) := E.finite_tateModule hℓK
  have h1 : ((1 : ℤ) : AlgebraicClosure (ZMod p)) ≠ 0 := by simp
  let fr : E.toAffine.Point →+ E.toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := Et)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
  have hfr (P : E.toAffine.Point) :
      Multiplicative.toAdd (Et.pointGaloisAction
        (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (AlgebraicClosure (ZMod p)))) P =
        fr P := by
    rw [WeierstrassCurve.pointGaloisAction_apply]
    congr 1
  have hα (P : E.toAffine.Point) :
      (Hom.ofIsogeny (ZInQ.Contrib.CloudB3RC53.WeilIsogeny.psi Et
        (K := AlgebraicClosure (ZMod p)) n h1)).pointMap P =
        (n • fr - AddMonoidHom.id E.toAffine.Point) P := by
    rw [ZInQ.Contrib.CloudB3RC53.WeilIsogeny.pointMap_psi, hfr P, one_zsmul]
    rfl
  have hd := detEqDegree_separable E ℓ hℓK
    (ZInQ.Contrib.CloudB3RC53.WeilIsogeny.psi Et (K := AlgebraicClosure (ZMod p)) n h1)
    (n • fr - AddMonoidHom.id E.toAffine.Point) hα
  have hT : TateModule.mapLinearMap (p := ℓ)
      (n • fr - AddMonoidHom.id E.toAffine.Point) =
        (n : ℤ_[ℓ]) • frobTate p Et ℓ - (1 : Module.End ℤ_[ℓ] (redTate p Et ℓ)) := by
    rw [mapLinearMap_sub, mapLinearMap_zsmul, mapLinearMap_id]
    rfl
  rw [hT] at hd
  have hsign : LinearMap.det
      ((1 : Module.End ℤ_[ℓ] (redTate p Et ℓ)) - (n : ℤ_[ℓ]) • frobTate p Et ℓ) =
      LinearMap.det
        ((n : ℤ_[ℓ]) • frobTate p Et ℓ - (1 : Module.End ℤ_[ℓ] (redTate p Et ℓ))) := by
    rw [show (1 : Module.End ℤ_[ℓ] (redTate p Et ℓ)) - (n : ℤ_[ℓ]) • frobTate p Et ℓ =
        (-1 : ℤ_[ℓ]) • ((n : ℤ_[ℓ]) • frobTate p Et ℓ - 1) by
          rw [neg_one_smul, neg_sub],
      LinearMap.det_smul, E.finrank_tateModule hℓK]
    simp
  rw [hsign, hd]
  have hdegree := ZInQ.Contrib.CloudB3RC53.WeilIsogeny.degree_psi Et
    (K := AlgebraicClosure (ZMod p)) n h1
  rw [ZInQ.Contrib.CloudB3RC53.WeilIsogeny.traceFrob, ZMod.card] at hdegree
  have hcast : ((ZInQ.Contrib.CloudB3RC53.WeilIsogeny.psi Et
      (K := AlgebraicClosure (ZMod p)) n h1).degree : ℤ_[ℓ]) =
      (((ZInQ.Contrib.CloudB3RC53.WeilIsogeny.psi Et
        (K := AlgebraicClosure (ZMod p)) n h1).degree : ℤ) : ℤ_[ℓ]) := by norm_cast
  rw [hcast, hdegree]
  push_cast
  ring

/-- **PROVED theorem from the reduction comparison** (Silverman
VII.3.1, VII.7.1, and V.2.3): the good-reduction Frobenius trace dictionary
needs only the reduction comparison, since its determinant-form slice
has been proved without the inseparable-pairing PRINT. -/
theorem goodReductionFrobeniusTraceDictionaryQ_of_reductionComparison
    (hR : TateReductionComparison) :
    ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionFrobeniusTraceDictionaryQ :=
  goodReductionFrobeniusTraceDictionaryQ_of_one hR frobeniusTateDetFormOne_proved

/-- **PRINT definition of an unproved geometric input** (Silverman
III.8.2, III.8.6, and V.2.3): for a nonzero inseparable endomorphism of
the reduced curve, the prime-power Weil pairing is scaled by its degree.
The pairing and the induced torsion maps are the existing ones. There
is no determinant or Tate-module conclusion in this input. -/
def InseparableWeilPairingCompatibility : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Et : WeierstrassCurve (ZMod p)) [Et.IsElliptic],
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
      ∀ (f : Hom (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine
          (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine) (hf : f ≠ 0),
        ¬ Algebra.IsSeparable (Hom.toIsogeny hf).fieldPullback.fieldRange
          (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine.FunctionField →
        ∀ (α : (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point →+
            (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point),
          (∀ P, f.pointMap P = α P) →
          ∀ (n : ℕ) (hN : ((ℓ ^ n : ℕ) : AlgebraicClosure (ZMod p)) ≠ 0)
            (S T : TateModuleLevel ℓ
              (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point n),
            weilPairing (Et.baseChange (AlgebraicClosure (ZMod p))) (ℓ ^ n) hN
                (TateModule.levelMap (p := ℓ) α n S)
                (TateModule.levelMap (p := ℓ) α n T) =
              f.degree •
                weilPairing (Et.baseChange (AlgebraicClosure (ZMod p))) (ℓ ^ n) hN S T

/-- **PROVED theorem from the named PRINT** (Silverman III.8.6 and
V.2.3): the full determinant--degree proposition reduces only to
prime-power Weil-pairing compatibility for nonzero inseparable
endomorphisms. The zero and separable cases require no additional
geometric input. -/
theorem detEqDegree_of_inseparableWeilPairingCompatibility
    (hP : InseparableWeilPairingCompatibility) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.DetEqDegree := by
  intro p _ Et _ ℓ _ hℓ f α hα
  have hℓK : (ℓ : AlgebraicClosure (ZMod p)) ≠ 0 := by
    intro h0
    have h0' : (ℓ : ZMod p) = 0 := by
      apply (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
      simpa only [map_natCast, map_zero] using h0
    have hdiv : p ∣ ℓ := (CharP.cast_eq_zero_iff (ZMod p) p ℓ).mp h0'
    have heq : p = ℓ := ((Nat.dvd_prime (Fact.out : ℓ.Prime)).mp hdiv).resolve_left
      (Fact.out : p.Prime).ne_one
    exact hℓ heq.symm
  by_cases hf : f = 0
  · subst f
    exact detEqDegree_zero (Et.baseChange (AlgebraicClosure (ZMod p))) ℓ hℓK α hα
  · by_cases hs : Algebra.IsSeparable (Hom.toIsogeny hf).fieldPullback.fieldRange
        (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine.FunctionField
    · let : Algebra.IsSeparable (Hom.toIsogeny hf).fieldPullback.fieldRange
          (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine.FunctionField := hs
      have hd := detEqDegree_separable (Et.baseChange (AlgebraicClosure (ZMod p))) ℓ hℓK
        (Hom.toIsogeny hf) α (by simpa only [Hom.ofIsogeny_toIsogeny] using hα)
      rw [← Hom.degree_ofIsogeny, Hom.ofIsogeny_toIsogeny] at hd
      exact hd
    · apply det_tate_eq_of_weilPairing_compatibility
        (Et.baseChange (AlgebraicClosure (ZMod p))) ℓ hℓK α f.degree
      intro n S T
      exact hP p Et ℓ hℓ f hf hs α hα n (by simpa using pow_ne_zero n hℓK) S T

end ZInQ.Contrib.RC53Assist.DetDegree
