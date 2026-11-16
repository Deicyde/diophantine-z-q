import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_nonempty_modularPolynomialData

/-!
# `X₀(N)`-transitivity for the generic elliptic curve from the cyclic-quotient bijection

**A reduction, not a proof of the target.** The statement of `ZInQ.RLeaf.X0Transitive`
(`ZInQKernel/Contrib/RLeaf/IgusaX0.lean:69`), with `galPt σ` unfolded to its definition
`WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom` (`ZInQKernel/Contrib/RLeaf/IgusaSL2.lean:91`),
over the objects of `ZInQKernel/HDecomp/ModCurves/Defs.lean` (`Qj = ℚ(j)`, `Kbar`, `Ej`, `EjBar`;
nothing is redefined here), is derived from `CyclicQuotientJBijOn`: the exact statement (at
universe `0`) of Anthropic FLT's
`WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`. That
theorem's 661-module proof cone is not ported (see the worker report); everything else used here
is proved (Mathlib, and the ported FLT theorems imported below). `Reduction.lean` states the
reduction against the original constant `ZInQ.RLeaf.X0Transitive`.

For points `P, P'` of exact order `N > 0` on `E_j` over `\overline{ℚ(j)}` (all `N`, `N = 1`
included):

* `H = ⟨P⟩` and `H' = ⟨P'⟩` are cyclic of order `N`, so (`CyclicQuotientJBijOn`, with
  `K = ℚ`: `j = RatFunc.X` is transcendental over `ℚ`) the quotient `j`-invariants
  `y = j(E_j/H)` and `y' = j(E_j/H')` are roots of `Φ_N(X, j)`, and `C ↦ j(E_j/C)` is injective
  on cyclic subgroups of order `N`;
* `Φ_N(X, j)` is irreducible over `ℚ(j) = RatFunc ℚ` (Anthropic FLT,
  `ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero`) and monic, so it
  is the minimal polynomial of `y` and of `y'` over `ℚ(j)`; as `\overline{ℚ(j)}/ℚ(j)` is normal,
  some `σ ∈ Aut(\overline{ℚ(j)}/ℚ(j))` sends `y` to `y'` (`Normal.minpoly_eq_iff_mem_orbit`);
* `σ(j(E_j/H)) = j(E_j/σH)` (Anthropic FLT,
  `WeierstrassCurve.cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed`, with
  `E_j^σ = E_j` because the coefficients of `E_j` lie in `ℚ(j)`), so `j(E_j/σH) = j(E_j/H')`,
  hence `σH = H'` by injectivity, and `σ P ∈ σH = ⟨P'⟩`.

Sources (vendored under `Vendor/AnthropicFLT/`, see its `SOURCE_MANIFEST.json`, `LICENSE`,
`NOTICE.upstream`, `ATTRIBUTION.upstream.md`): anthropics/fermats-last-theorem, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, Apache-2.0; local import paths relocated, bodies
unchanged. The mathematics: Lang, *Elliptic functions*, Ch. 5, §2, Thm 3; Cox, *Primes of the form
x² + ny²*, Thm 11.18.

No `sorry`, no `axiom`, no `native_decide`; the one unproved input is the hypothesis
`CyclicQuotientJBijOn`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2X0Transitive

open LeafModCurves WeierstrassCurve Polynomial

/-- **The cyclic-quotient bijection** (the statement of Anthropic FLT's
`WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`,
`Theorems/Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.lean`
at commit `6e837e75`, with its universes `u, v` set to `0`): for `E` over an algebraically closed
`L` with `j(E)` transcendental over `K` and `N ≠ 0` in `L`, `C ↦ j(E/C)` (iterated Vélu,
`WeierstrassCurve.cyclicQuotientJ`) is a bijection from the cyclic subgroups of order `N` onto the
roots of `Φ_N(X, j(E))`. Not proved in this module. -/
def CyclicQuotientJBijOn : Prop :=
  ∀ (K : Type) [Field K] (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (L : Type) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra K L]
    (_ : (N : L) ≠ 0) (E : WeierstrassCurve L) [E.IsElliptic] (_ : Transcendental K E.j),
    Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H N)
      {H | IsAddCyclic H ∧ Nat.card H = N}
      {y | (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) E.j)).IsRoot y}

/-- `E_j` over `\overline{ℚ(j)}` is elliptic (as `X1Belyi`'s instance, here a definition so that
nothing global is added). -/
abbrev ejBarIsElliptic : EjBar.IsElliptic :=
  inferInstanceAs ((Ej.map (algebraMap Qj Kbar)).IsElliptic)

/-- `\overline{ℚ(j)}` has characteristic zero. -/
theorem charZero_Kbar : CharZero Kbar :=
  charZero_of_injective_algebraMap (algebraMap Qj Kbar).injective

/-- `j(E_j) = j` in `\overline{ℚ(j)}`. -/
theorem ejBar_j : (letI := ejBarIsElliptic; EjBar.j) = algebraMap Qj Kbar RatFunc.X := by
  let _ : EjBar.IsElliptic := ejBarIsElliptic
  show (Ej.map (algebraMap Qj Kbar)).j = _
  rw [WeierstrassCurve.map_j, Ej_j]

/-- An automorphism of `\overline{ℚ(j)}` over `ℚ(j)` fixes `E_j`. -/
theorem ejBar_map_algEquiv (σ : Kbar ≃ₐ[Qj] Kbar) : EjBar.map (σ : Kbar →+* Kbar) = EjBar := by
  show (Ej.map (algebraMap Qj Kbar)).map (σ : Kbar →+* Kbar) = Ej.map (algebraMap Qj Kbar)
  rw [WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext fun a => σ.commutes a

/-- Equal curves and two point maps acting by `σ` on coordinates give the same quotient
`j`-invariants (the argument of Anthropic FLT's `CycQJMapAux.cyclicQuotientJ_map_congr`). -/
theorem cyclicQuotientJ_congr {L L' : Type*} [Field L] [Field L'] [DecidableEq L] [DecidableEq L']
    (σ : L →+* L') {V : WeierstrassCurve L} {W₁ W₂ : WeierstrassCurve L'} (hW : W₁ = W₂)
    (φ₁ : V.toAffine.Point →+ W₁.toAffine.Point) (φ₂ : V.toAffine.Point →+ W₂.toAffine.Point)
    (hφ₁ : ∀ (x y : L) (h : V.toAffine.Nonsingular x y),
      ∃ h', φ₁ (.some x y h) = .some (σ x) (σ y) h')
    (hφ₂ : ∀ (x y : L) (h : V.toAffine.Nonsingular x y),
      ∃ h', φ₂ (.some x y h) = .some (σ x) (σ y) h')
    (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    W₁.cyclicQuotientJ (H.map φ₁) N = W₂.cyclicQuotientJ (H.map φ₂) N := by
  subst hW
  have hφ : φ₁ = φ₂ := by
    ext P
    rcases P with _ | ⟨x, y, h⟩
    · exact (map_zero φ₁).trans (map_zero φ₂).symm
    · obtain ⟨h₁, e₁⟩ := hφ₁ x y h
      obtain ⟨h₂, e₂⟩ := hφ₂ x y h
      rw [e₁, e₂]
  rw [hφ]

/-- **`X₀(N)`-transitivity, unfolded, from the cyclic-quotient bijection**
(`ZInQ.RLeaf.X0Transitive` with `galPt` unfolded; the `DecidableEq` instance of `Kbar` is a
unification argument, so that the statement matches the original one whatever instance it was
elaborated with). -/
theorem x0Transitive_unfolded_of_bijOn (hB : CyclicQuotientJBijOn) {inst : DecidableEq Kbar} :
    ∀ (N : ℕ) (P P' : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → addOrderOf P' = N →
      ∃ σ : Kbar ≃ₐ[Qj] Kbar,
        WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom P ∈
          AddSubgroup.zmultiples P' := by
  intro N P P' hN hP hP'
  have : NeZero N := ⟨hN.ne'⟩
  let _ : EjBar.IsElliptic := ejBarIsElliptic
  have _ : CharZero Kbar := charZero_Kbar
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  -- `j` is transcendental over `ℚ`, and `N ≠ 0` in `\overline{ℚ(j)}`
  have hT : Transcendental ℚ EjBar.j := by
    rw [ejBar_j, transcendental_algebraMap_iff (algebraMap Qj Kbar).injective]
    -- `Algebra ℚ Qj` instances form a subsingleton
    convert RatFunc.transcendental_X (K := ℚ)
    exact Subsingleton.elim _ _
  have hNK : (N : Kbar) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hbij := hB ℚ N data Kbar hNK EjBar hT
  -- `Φ_N(X, j)` over `ℚ(j)`: irreducible, monic, and its image over `\overline{ℚ(j)}`
  set p : Polynomial Qj := (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom ℚ))).map
    (algebraMap (Polynomial ℚ) (RatFunc ℚ)) with hp
  have hirr : Irreducible p :=
    ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero ℚ N data
      (Nat.cast_ne_zero.mpr hN.ne')
  have hmon : p.Monic := (data.monic.map _).map _
  have hpmap : p.map (algebraMap Qj Kbar) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar) EjBar.j) := by
    rw [hp, Polynomial.map_map, Polynomial.map_map, ejBar_j]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_X, RatFunc.algebraMap_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hmin : ∀ z : Kbar,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar) EjBar.j)).IsRoot z →
        minpoly Qj z = p := by
    intro z hz
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ hmon).symm
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hpmap]
    exact hz
  -- the two cyclic subgroups of order `N`
  have hcyc : ∀ Q : EjBar.toAffine.Point, addOrderOf Q = N →
      AddSubgroup.zmultiples Q ∈
        {H : AddSubgroup EjBar.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N} :=
    fun Q hQ => ⟨inferInstance, by rw [Nat.card_zmultiples, hQ]⟩
  have hy := hbij.mapsTo (hcyc P hP)
  have hy' := hbij.mapsTo (hcyc P' hP')
  -- an automorphism sending `j(E_j/⟨P⟩)` to `j(E_j/⟨P'⟩)`
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp
    ((Normal.minpoly_eq_iff_mem_orbit Kbar).mp ((hmin _ hy').trans (hmin _ hy).symm))
  rw [AlgEquiv.smul_def] at hσ
  refine ⟨σ, ?_⟩
  set g := WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom with hg
  -- equivariance: `σ(j(E_j/⟨P⟩)) = j(E_j/σ⟨P⟩)`
  have heq := WeierstrassCurve.cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
    (σ : Kbar →+* Kbar) EjBar (AddSubgroup.zmultiples P) N
  have hcongr : (EjBar.map (σ : Kbar →+* Kbar)).cyclicQuotientJ
        ((AddSubgroup.zmultiples P).map (WeierstrassCurve.mapPointHom (σ : Kbar →+* Kbar))) N =
      EjBar.cyclicQuotientJ ((AddSubgroup.zmultiples P).map g) N :=
    cyclicQuotientJ_congr (σ : Kbar →+* Kbar) (ejBar_map_algEquiv σ) _ g
      (fun x y h => ⟨_, rfl⟩)
      (fun x y h => ⟨_, WeierstrassCurve.Affine.Point.map_some (W' := Ej) σ.toAlgHom h⟩) _ N
  have hjeq : EjBar.cyclicQuotientJ ((AddSubgroup.zmultiples P).map g) N =
      EjBar.cyclicQuotientJ (AddSubgroup.zmultiples P') N := by
    rw [← hcongr, heq]
    exact hσ
  -- `σ⟨P⟩ = ⟨σ P⟩` is cyclic of order `N`, so by injectivity it is `⟨P'⟩`
  have hginj : Function.Injective g := WeierstrassCurve.Affine.Point.map_injective _
  have hmz : (AddSubgroup.zmultiples P).map g = AddSubgroup.zmultiples (g P) :=
    AddMonoidHom.map_zmultiples g P
  have hHg : (AddSubgroup.zmultiples P).map g ∈
      {H : AddSubgroup EjBar.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N} := by
    rw [hmz]
    exact hcyc _ ((addOrderOf_injective g hginj P).trans hP)
  have hsub := hbij.injOn hHg (hcyc P' hP') hjeq
  rw [← hsub]
  exact AddSubgroup.mem_map_of_mem g (AddSubgroup.mem_zmultiples P)

end ZInQ.Contrib.CloudB2X0Transitive
