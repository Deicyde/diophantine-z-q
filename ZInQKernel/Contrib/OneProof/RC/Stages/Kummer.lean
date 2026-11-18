import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Serre
import ZInQKernel.Contrib.OneProof.RC.Odd.Detector
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective

/-! The division cocycle on the actual absolute Galois group (tex 8308–8316). -/

noncomputable section

open scoped WeierstrassCurve
open TauCeti WeierstrassCurve
open ZInQ.Manuscript.RC.PrintsArith

namespace ZInQ.Manuscript.RC.Stages

variable (A : WeierstrassCurve ℚ)

abbrev GeomPoint := (A⁄Qbar).toAffine.Point

/-- The points above Q, with the compatibility needed for a Tate-valued cocycle. -/
structure DivisionTower (Q : GeomPoint A) where
  point : ℕ → GeomPoint A
  base : point 0 = Q
  step : ∀ n, 2 • point (n + 1) = point n

variable {A}

/-- Algebraically closed division provides one compatible tower, in all precisions. -/
def divisionTower [A.IsElliptic] (Q : GeomPoint A) : DivisionTower A Q := by
  have h := (A⁄Qbar).toAffine.nsmul_surjective (n := 2) (by norm_num)
  exact ⟨Nat.rec Q (fun _ x => (h x).choose), rfl, fun n => (h _).choose_spec⟩

variable {Q : GeomPoint A}

/-- Each member of the tower divides Q by the expected power of two. -/
theorem DivisionTower.divides (d : DivisionTower A Q) (n : ℕ) : (2 ^ n : ℕ) • d.point n = Q := by
  induction n with
  | zero => simpa using d.base
  | succ n ih => rw [pow_succ', mul_nsmul, d.step, ih]

/-- The finite component of the cocycle: g Q_n - Q_n. -/
def DivisionTower.translation (d : DivisionTower A Q)
    (hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q)
    (g : GalQ) (n : ℕ) : TateModuleLevel 2 (GeomPoint A) n :=
  ⟨Affine.Point.map g.toAlgHom (d.point n) - d.point n, by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    rw [nsmul_sub, ← map_nsmul, d.divides, hQ, sub_self]⟩

/-- The genuine elliptic Kummer cocycle in the integral Tate module. -/
def DivisionTower.cocycle (d : DivisionTower A Q)
    (hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q) (g : GalQ) :
    TateMod A 2 :=
  TateModule.mk (d.translation hQ g) (fun n => Subtype.ext (by
    change 2 • (Affine.Point.map g.toAlgHom (d.point (n + 1)) - d.point (n + 1)) =
      Affine.Point.map g.toAlgHom (d.point n) - d.point n
    rw [nsmul_sub, ← map_nsmul, d.step]))

/-- The finite projections are exactly the original differences of division points. -/
theorem DivisionTower.coe_proj_cocycle (d : DivisionTower A Q) (hQ) (g : GalQ) (n : ℕ) :
    (TateModule.proj n (d.cocycle hQ g) : GeomPoint A) =
      Affine.Point.map g.toAlgHom (d.point n) - d.point n := rfl

/-- The representation in the additive endomorphisms used by Odd.Detector. -/
def additiveRep (A : WeierstrassCurve ℚ) : GalQ →* AddMonoid.End (TateMod A 2) where
  toFun g := (tateRep A 2 g).toAddMonoidHom
  map_one' := AddMonoidHom.ext fun x => by
    change (tateRep A 2 1) x = x
    rw [map_one]
    rfl
  map_mul' g h := AddMonoidHom.ext fun x => by
    change (tateRep A 2 (g * h)) x = (tateRep A 2 g * tateRep A 2 h) x
    rw [map_mul]

/-- Tex 8311–8316: the genuine cocycle law. -/
theorem DivisionTower.isCocycle (d : DivisionTower A Q) (hQ) :
    Odd.IsCocycle (additiveRep A) (d.cocycle hQ) := by
  intro g h
  apply TateModule.ext
  intro n
  apply Subtype.ext
  rw [d.coe_proj_cocycle, map_add, AddSubgroup.coe_add, d.coe_proj_cocycle]
  change Affine.Point.map (g * h).toAlgHom (d.point n) - d.point n =
    _ + (TateModule.proj n (tateRep A 2 g (d.cocycle hQ h)) : GeomPoint A)
  rw [coe_proj_tateRep, d.coe_proj_cocycle, map_sub, Affine.Point.map_map]
  change Affine.Point.map (g.toAlgHom.comp h.toAlgHom) (d.point n) - d.point n = _
  abel

/-- The restriction to the common kernel of the Tate action and the auxiliary field is a
homomorphism. This works over any subgroup of the Tate kernel. -/
def DivisionTower.restriction (d : DivisionTower A Q)
    (hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q)
    (H : Subgroup GalQ) (hH : H ≤ (additiveRep A).ker) :
    H →* Multiplicative (TateMod A 2) where
  toFun g := Multiplicative.ofAdd (d.cocycle hQ g)
  map_one' := congrArg Multiplicative.ofAdd (d.isCocycle hQ).map_one
  map_mul' g h := congrArg Multiplicative.ofAdd (by
    change d.cocycle hQ ((g : GalQ) * (h : GalQ)) = d.cocycle hQ g + d.cocycle hQ h
    rw [(d.isCocycle hQ) (g : GalQ) h, MonoidHom.mem_ker.mp (hH g.property)]
    rfl)

/-- Tex 8349–8355: once the translation lands on the required vector, the very same
Galois element detects it at every precision. -/
theorem DivisionTower.detectingElement (d : DivisionTower A Q) (hQ)
    {h τ : GalQ} (hh : additiveRep A h = 1) (hτ : τ * τ = 1)
    (b : TateMod A 2 →+ ℤ_[2]) (hb : ∀ x, b (additiveRep A τ x) = b x)
    (t₀ : TateMod A 2) (ht₀ : b t₀ = 1) (a : ℕ)
    (hv : d.cocycle hQ h = (2 ^ a : ℕ) • t₀) :
    additiveRep A (h * τ) = additiveRep A τ ∧
      b (d.cocycle hQ ((h * τ) * (h * τ))) = 2 ^ (a + 1) := by
  obtain ⟨hrep, hs⟩ := (d.isCocycle hQ).sigma_sq hh hτ
  refine ⟨hrep, ?_⟩
  rw [hs, hv]
  exact Odd.row_value (additiveRep A τ) b hb t₀ ht₀ a

/-- Reduce an integral row modulo 2^M. The kernel of finite projection is
2^M times the Tate module, so the reduced row is well defined on finite torsion. -/
def finiteRow [A.IsElliptic] (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2]) (M : ℕ) :
    TateModuleLevel 2 (GeomPoint A) M →+ ZMod (2 ^ M) :=
  let h := TateModule.proj_surjective
    (TateModule.tateModuleTransition_surjective_of_natCard (p := 2) (by decide)
      ((A⁄Qbar).natCard_tateModuleLevel (by norm_num : (2 : Qbar) ≠ 0))) M
  (TateModule.proj M).liftOfSurjective h
    ⟨(PadicInt.toZModPow M).toAddMonoidHom.comp b.toAddMonoidHom, by
      intro x hx
      obtain ⟨y, hy⟩ := TateModule.proj_eq_zero_iff.mp (AddMonoidHom.mem_ker.mp hx)
      apply AddMonoidHom.mem_ker.mpr
      change PadicInt.toZModPow M (b x) = 0
      rw [hy, map_nsmul, map_nsmul, nsmul_eq_mul]
      have hz : ((2 ^ M : ℕ) : ZMod (2 ^ M)) = 0 := ZMod.natCast_self _
      rw [hz, zero_mul]⟩

/-- The finite row evaluated on a projected Tate vector is its original value
reduced modulo the precision. -/
theorem finiteRow_proj [A.IsElliptic] (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2])
    (M : ℕ) (t : TateMod A 2) :
    finiteRow b M (TateModule.proj M t) = PadicInt.toZModPow M (b t) := by
  simp [finiteRow]

#print axioms finiteRow
#print axioms finiteRow_proj
#print axioms divisionTower
#print axioms DivisionTower.divides
#print axioms DivisionTower.coe_proj_cocycle
#print axioms DivisionTower.isCocycle
#print axioms DivisionTower.restriction
#print axioms DivisionTower.detectingElement

end ZInQ.Manuscript.RC.Stages
