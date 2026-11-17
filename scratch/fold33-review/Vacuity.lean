import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.TYZGenus.ShimuraField

/-!
# fold33-review: vacuity and use checks for the three new leaves of wip/leaf-fold33b

* §1 `HCMDict.ShimuraThm54`: its hypotheses hold together at `m = 1`, `σ = id`, `s = 1`, `𝔞 = κ⁻¹⟨1, i⟩`,
  `E = E_{⟨1,i⟩}`, `ξ = ξ_{⟨1,i⟩}` (the same `s = 1` instance the TYZ chain uses in `RingClassLattice.lean`).
* §2 `GroupLawNeron.NeronSchemeExtensionDedekind`: its hypotheses are inhabited at a non-field Dedekind domain
  (`ℤ`, `ℚ`, the zero abelian variety) and at a DVR (`ℤ_[p]`, `ℚ_[p]`), the case the chain reads.
* §3 `GZAlg.GrossZagierAlgOptCd`: the hypotheses added by gzopt-dict (`φ^*`, `ord_q φ^*(x) < 0`, meromorphy,
  `q`-expansions) are produced by a Lean proof from gz-optimal's (`grossZagierModuliOptAt_of_alg`).
* §4 Use sites: the theorems through which `frozenTarget` reads each leaf are in its constant closure.
-/

open Complex

namespace Fold33Review

open ZInQ.Contrib.HCMDict ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise T5Glue

/-! ## §1 ShimuraThm54 -/

/-- The lattice `⟨1, i⟩`. -/
noncomputable def Li : PeriodPair := pp UpperHalfPlane.I

/-- `⟨1, i⟩ ⊂ κ(ℚ(i))`. -/
theorem Li_sub_range : (Li.lattice : Set ℂ) ⊆ Set.range (kappa 1) := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hx
  refine ⟨⟨(a : ℚ), (b : ℚ)⟩, ?_⟩
  simp [kappa, Li, pp, Real.sqrt_one]

/-- `𝔞 = κ⁻¹⟨1, i⟩`. -/
def ai : Set (QNeg 1) := kappa 1 ⁻¹' (Li.lattice : Set ℂ)

theorem Li_eq : (Li.lattice : Set ℂ) = kappa 1 '' ai := by
  rw [ai, Set.image_preimage_eq_of_subset Li_sub_range]

theorem artinCond_one (e : SeparableClosure (QNeg 1) →ₐ[ℚ] Qbar) :
    ArtinCond 1 e (RingEquiv.refl ℂ) 1 := by
  intro F _ _ _ x
  rw [show icl (1 : IdeleGroup (𝓞 (QNeg 1)) (QNeg 1)) = 1 from QuotientGroup.mk_one _, map_one,
    AlgEquiv.one_apply]
  rfl

/-- **Every hypothesis of `ShimuraThm54` holds at one instance** (`m = 1`, `σ = id`, `s = 1`). -/
theorem shimuraThm54_hyps_satisfiable :
    ∃ e : SeparableClosure (QNeg 1) →ₐ[ℚ] Qbar,
      ιC (e (algebraMap (QNeg 1) (SeparableClosure (QNeg 1)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt 1 : ℂ) ∧
      ArtinCond 1 e (RingEquiv.refl ℂ) 1 ∧
      (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa 1 '' ai) ∧
      ∃ (E : WeierstrassCurve ℂ) (_ : E.IsElliptic), E.a₁ = 0 ∧ E.a₂ = 0 ∧ E.a₃ = 0 ∧
        ∃ ξ : ℂ → E.toAffine.Point, IsAnalyticUnif E (kappa 1 '' ai) ξ := by
  obtain ⟨e, he⟩ := exists_normalized_embed_any 1
  haveI hE : Li.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr Li.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩
  refine ⟨e, by exact_mod_cast he, artinCond_one e, ⟨Li, Li_eq⟩, Li.weierstrassCurve, hE,
    by simp, by simp, by simp, Li.toPoint Li.discriminant_ne_zero, ?_⟩
  have h := toPoint_isAnalyticUnif Li
  rwa [Li_eq] at h

theorem squarefree_one' : Squarefree (1 : ℕ) := squarefree_one

/-! ## §2 NeronSchemeExtensionDedekind -/

open ZInQ.Contrib.GroupLawNeron in
/-- The hypotheses of the leaf (a Dedekind domain that is not a field, its fraction field, an abelian variety)
are inhabited. Mathlib v4.35 has no nonzero `AbVar` over `ℚ` built from first principles; the zero one is
`PkgI3.AbVar.zero`. -/
example : ∃ (A : PkgI3.AbVar ℚ), True := ⟨PkgI3.AbVar.zero ℚ, trivial⟩

example : IsDedekindDomain ℤ := inferInstance
example : IsFractionRing ℤ ℚ := inferInstance
example : ¬ IsField ℤ := Int.not_isField

/-- The DVR case (`NeronSchemeExtensionDVR`, the form `mumfordGroupLawDVR_of_neron` reads): instances exist. -/
example (p : ℕ) [Fact p.Prime] : IsDiscreteValuationRing ℤ_[p] := inferInstance
example (p : ℕ) [Fact p.Prime] : IsFractionRing ℤ_[p] ℚ_[p] := inferInstance

/-- The Dedekind leaf gives its DVR case and the removed textbook field (both by instantiation, Lean). -/
example : ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind →
    ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDVR ∧ ZInQ.Contrib.NeronC.NeronSchemeExtensionExists :=
  fun h => ⟨ZInQ.Contrib.GroupLawNeron.dvr_of_dedekind h,
    ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind h⟩

/-! ## §3 GrossZagierAlgOptCd -/

/-- gzopt-dict's bridge: every instance of gz-optimal's hypotheses yields an instance of the algebraic leaf's
(`φ^* := phiOf x' y'`), given the `q`-expansion principle (proved: gamma0-qexp). -/
example : ZInQ.GZAlg.GrossZagierAlgOptCd → ZInQ.GZOptimal.GrossZagierModuliOptCd :=
  ZInQ.GZAlg.grossZagierModuliOptCd_of_alg ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof

end Fold33Review

/-! ## §4 Use sites in the closure of `frozenTarget` -/

open Lean Elab Command in
partial def closureOf' (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots.toList
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let mut cs := ci.type.getUsedConstants
      match ci with
      | .defnInfo d => cs := cs ++ d.value.getUsedConstants
      | .thmInfo t => cs := cs ++ t.value.getUsedConstants
      | .opaqueInfo o => cs := cs ++ o.value.getUsedConstants
      | .inductInfo i => cs := cs ++ i.ctors.toArray
      | .ctorInfo c => cs := cs.push c.induct
      | _ => pure ()
      for c in cs do
        unless seen.contains c do stack := c :: stack
  return seen

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let cl := closureOf' env #[`ZInQ.OneProof.frozenTarget]
  let uses : List Name := [
    `ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed,
    `ZInQ.Contrib.HCMDict.eq_scaled_of_isAnalyticUnif,
    `ZInQ.GZAlg.grossZagierFormulaCd_of_alg,
    `ZInQ.GZAlg.grossZagierModuliOptAt_of_alg,
    `ZInQ.GZOptimal.core_selfOptimal,
    `ZInQ.PeriodOdd.core_isog,
    `ZInQ.PeriodOdd.grossZagierFormulaCd_of_etaW32,
    `ZInQ.Contrib.GroupLawNeron.mumfordGroupLawDVR_of_neron,
    `ZInQ.Contrib.GroupLawNeron.dvr_of_dedekind,
    `ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind,
    `ZInQ.Contrib.GroupLawNeron.NeronGoodModelIso]
  for u in uses do
    logInfo m!"USE {u}: in closure = {cl.contains u}, exists = {(env.find? u).isSome}"
  -- the good-model glue: which theorems in the closure have type `NeronGoodModelIso`?
  for n in cl.toList do
    if let some (.thmInfo t) := env.find? n then
      if t.type.isConstOf `ZInQ.Contrib.GroupLawNeron.NeronGoodModelIso then
        logInfo m!"PROOF of NeronGoodModelIso in closure: {n}"
      if t.type.isConstOf `ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR then
        logInfo m!"PROOF of MumfordGroupLawDVR in closure: {n}"

#print axioms Fold33Review.shimuraThm54_hyps_satisfiable
