import ZInQKernel.HDecomp.ModCurves.X1Belyi
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure

/-!
# rleaf-elliptic: the textbook leaf T36 (`E[N] ≅ (ℤ/N)²`) proved

`X1Belyi.TorsionStructure` (leaf T36 of docs/research/h-decomposition.md §2.2, field `x1.torsion`
of the textbook bundle): for an elliptic curve `W` over an algebraically closed field `K` of
characteristic 0 and `N ≥ 1`, the `N`-torsion `W[N]` of Mathlib's Weierstrass points is
isomorphic to `ZMod N × ZMod N`.

Proof: Tau Ceti's `WeierstrassCurve.torsion_addEquiv_prod` (vendored from commit 5a01f5fe,
`TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure`; Silverman, AEC
III.6.4(b)) gives `AddSubgroup.torsionBy W.toAffine.Point N ≃+ ZMod N × ZMod N` over a separably
closed field in which `N` is invertible. The project's `nTors W N` has the same carrier
(`N • P = 0` versus `(N : ℤ) • P = 0`), and the decidable-equality instances are reconciled by
`convert`.
-/

namespace ZInQ.RLeaf

open WeierstrassCurve

/-- `nTors W N` and Mathlib's `torsionBy W.toAffine.Point N` are the same subgroup. -/
theorem nTors_eq_torsionBy {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (N : ℕ) :
    X1Belyi.nTors W N = AddSubgroup.torsionBy W.toAffine.Point (N : ℤ) := by
  ext P
  change N • P = 0 ↔ (N : ℤ) • P = 0
  rw [natCast_zsmul]

/-- **Leaf T36 (`X1Belyi.TorsionStructure`), proved.** -/
theorem t36_torsionStructure : X1Belyi.TorsionStructure := by
  intro K _ _ _ _ W _ N hN
  have : NeZero N := ⟨hN.ne'⟩
  have hNK : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨e⟩ : Nonempty (AddSubgroup.torsionBy W.toAffine.Point (N : ℤ) ≃+ ZMod N × ZMod N) := by
    convert W.torsion_addEquiv_prod N hNK
  exact ⟨(AddEquiv.addSubgroupCongr (nTors_eq_torsionBy W N)).trans e⟩

end ZInQ.RLeaf

#print axioms ZInQ.RLeaf.nTors_eq_torsionBy
#print axioms ZInQ.RLeaf.t36_torsionStructure
