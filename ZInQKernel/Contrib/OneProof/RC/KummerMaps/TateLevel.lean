import ZInQKernel.Contrib.OneProof.RC.CoefModules.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.TateWiring.Image

/-!
# Lane RC29 (Kummer maps), item 3: `E(K_S)[2^i] ≃ T₂E/2^i T₂E`, equivariantly

Manuscript `diophantine_zq.tex` (11/5 version).

* tex 2723–2726: "The actual finite coefficients are `A_i=(ℤ/2^iℤ)[t]/t^i`,
  `M_i=(T_2E⊗A_i)(χ_hΨ_i)`."
* tex 2836–2837: "Fix the non-CM elliptic curve `E/ℚ`, its conductor `N`, its Tate module
  `T=T_2E`".
* tex 2778–2788: "Fix an actual complex conjugation `τ ∈ G_ℚ` … `Ψ_i(τgτ⁻¹)=Ψ_i(g)⁻¹` (`g ∈ G_K`)":
  the text reads `G_K` inside `G_ℚ`, i.e. `K ⊂ ℚ̄` and `K̄ = ℚ̄`.
* tex 2798–2805: the pairing `(v,w) ↦ e_2(v,ρ_T(τ)w)` on `M_i`, with `ρ_T` the Galois action on
  `T = T₂E`.

Lane RC28 realized `M_i` as `Mcoef K S W i α = CoefMod (Acoef i) α (TorsS K S W (2^i))`, i.e.
`(A_i ⊗_ℤ E(K_S)[2^i])(α)`, and recorded as its DEPARTURE 1 that the identification
`T₂E/2^i T₂E ≅ E[2^i]` with lane RC17's Tate module was not formalized. This file builds that
identification, equivariantly, for `E : WeierstrassCurve ℚ` elliptic, `K` a number field and
`W = E_K = E⁄K`; the coefficient statement `A_i ⊗_ℤ E(K_S)[2^i] ≅ A_i ⊗_{ℤ₂} T₂E` is in
`TateCoef.lean`.

## (a) `K̄ ≅ ℚ̄` and `Gal(K̄/K) → G_ℚ`

* `tateAlgEquiv K : K̄ ≃ₐ[ℚ] ℚ̄` (`K/ℚ` is algebraic, so `K̄` is an algebraic closure of `ℚ`).
* For any `e : K̄ ≃ₐ[ℚ] ℚ̄`, `tateGalToQ e : Gal(K̄/K) →ₜ* G_ℚ`, `σ ↦ e σ e⁻¹`: a continuous
  homomorphism for the Krull topologies (Mathlib's `Field.absoluteGaloisGroup.mapOfAlgebra`),
  injective (`tateGalToQ_injective`), with `tateGalToQ_apply_e : (e σ e⁻¹)(e x) = e (σ x)`.

## (b) `T₂E/2^i T₂E ≃ E(ℚ̄)[2^i]`

* `TateLevel E i = E(ℚ̄)[2^i]` (Tau Ceti's level `i` of `T₂E`), `tateProj E i = proj i`.
* `tatePowSub E i = 2^i T₂E` (as `(2^i) • ⊤`), `tateProj_eq_zero_iff` (kernel),
  `tateProj_surjective`, `tateProj_reduction` (tex 3163–3164).
* `tateQuotEquiv E i : T₂E ⧸ 2^i T₂E ≃+ E(ℚ̄)[2^i]`, `tateQuotEquiv_mk`, semilinear along
  `ℤ₂ → ℤ/2^i` (`tateQuotEquiv_smul`), and compatible with `tateRep`:
  `tateQuotEquiv_tateRepMod` (`tateRepMod E i g` is `ρ_T(g)` reduced mod `2^i`).

## (c) `E(K_S)[2^i] ≃ E(ℚ̄)[2^i] ≃ T₂E/2^i T₂E`, equivariantly

* `tateTorsMap S E e i : E(K_S)[2^i] →+ E(ℚ̄)[2^i]` (coordinates along `K_S ⊂ K̄ ≅ ℚ̄`): injective
  without hypotheses, and **equivariant** (`tateTorsMap_smul`): for `σ ∈ G_{K,S}` and **any**
  lift `σ' ∈ Gal(K̄/K)` of `σ`, `σP ↦ (e σ' e⁻¹)(image of P)`.
* Under `FullTorsion K S (E⁄K) (2^i)` (lane RC28's GLUE, Néron–Ogg–Shafarevich):
  `tateTorsEquiv` and `tateTorsQuotEquiv : E(K_S)[2^i] ≃+ T₂E/2^i T₂E`, with
  `tateTorsQuotEquiv_smul`: `σ` corresponds to the reduction mod `2^i` of `tateRep E 2` at
  `tateGalToQ e σ'`; `tateRepMod_factor`: that reduction depends only on `σ'|_{K_S}`.
* `tateTorsMap_eq_bar`: `tateTorsMap` is lane RC28's `inclTors` followed by `K̄ ≅ ℚ̄`.

## (d) The matrix form

* `tateLevelBasis E i`: the `ℤ/2^i`-basis of `E(ℚ̄)[2^i]` reducing lane RC9's `tateBasis E`;
  `tateTorsBasis`: its transport to `E(K_S)[2^i]`.
* `tateTorsBasis_smul`, `toMatrix_tateTorsAct`: the matrix of `σ` is `tateMatrix E (e σ' e⁻¹)`
  (lane RC17) reduced mod `2^i`; `tateRhoTors : G_{K,S} →* GL₂(ℤ/2^i)` and `tateRhoTors_eq`:
  `tateRhoTors σ = GL₂(red_{2^i}) (rhoGL E (tateGalToQ e σ'))`.

## (f) The actual complex conjugation

* `tateConjQ e C = e τ e⁻¹ ∈ G_ℚ` for lane RC28's `ActualConj` `C` (tex 2778: `τ ∈ G_ℚ`, `τ² = 1`,
  `tateConjQ_mul_self`; complex conjugation for `ι ∘ e⁻¹`, `tateConjQ_complex`).
* `tateTorsMap_conjTors`, `tateTorsQuotEquiv_conjTors`: lane RC28's `conjTors` (its `ρ_T(τ)` on
  `E(K_S)[N]`, tex 2801) is the reduction mod `2^i` of `tateRep E 2 (tateConjQ e C)`
  (`tate_baseChange_map_kappa`: RC28's hypothesis `W.map κ = W` holds for `W = E⁄K`).

## Non-vacuity

`tate_exists_lift` (every `σ` has a lift), `tateAlgEquiv` (an `e` exists), `tate_fullTorsion_zero`
(`i = 0`), `tate_fullTorsion_ecurve` (`i = 1`, the curves `E_ℓ` of the manuscript).

## Kinds and departures

All declarations are definitions or PROVED. The only hypothesis beyond the data is
`FullTorsion K S (E⁄K) (2^i)` (GLUE, lane RC28: Néron–Ogg–Shafarevich, Silverman, *The Arithmetic
of Elliptic Curves*, 2nd ed., VII.7.1; Serre–Tate, Ann. of Math. 88 (1968), Thm. 1). It gives
(`tateRepMod_factor`) that the action of `Gal(K̄/K)` on `T₂E/2^i T₂E` factors through `G_{K,S}`,
as the text's use of `RΓ(G_{K,S}, M_i)` (tex 3455–3463) presupposes (conversely, by Galois
theory, such a factorization forces `E[2^i] ⊂ E(K_S)`; this converse is not formalized).

* DEPARTURE (choice of embedding): the text works with `K ⊂ ℚ̄`, `G_K ⊂ G_ℚ` (tex 2788). In Lean
  `K` is an abstract number field with its own algebraic closure, and `K̄ ≅ ℚ̄` is a chosen
  `ℚ`-isomorphism `e` (a parameter of every statement; one exists, `tateAlgEquiv`). All results
  hold for every `e`.
* DEPARTURE (form): `2^i T₂E` is the submodule `(2^i) • ⊤` (`= 2^i T₂E` by
  `mem_tatePowSub_iff`); the identification with `E(ℚ̄)[2^i]` is an additive equivalence,
  semilinear along `ℤ₂ → ℤ/2^i`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex (GKS resAbsCont)
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Manuscript.RC.TateWiring (tateMatrix rhoGL coe_rhoGL)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside resAbs resAbs_apply_coe)
open scoped WeierstrassCurve

/-! ### (a) `K̄ ≅ ℚ̄` and the induced map `Gal(K̄/K) → G_ℚ` -/

section GalQ

variable (K : Type) [Field K] [NumberField K]

/-- `K̄` is an algebraic closure of `ℚ` (`K/ℚ` is finite, hence algebraic). Kind: PROVED. -/
theorem tate_isAlgClosure : IsAlgClosure ℚ (AlgebraicClosure K) :=
  IsAlgClosure.ofAlgebraic ℚ K (AlgebraicClosure K)

/-- **A `ℚ`-algebra isomorphism `K̄ ≃ ℚ̄`** (two algebraic closures of `ℚ`). It realizes the text's
convention `K ⊂ ℚ̄`, `G_K ⊂ G_ℚ` (tex 2788). DEPARTURE (choice): the isomorphism is not canonical;
every statement below takes an arbitrary `e : K̄ ≃ₐ[ℚ] ℚ̄`, and this one shows that such `e`
exist. -/
def tateAlgEquiv : AlgebraicClosure K ≃ₐ[ℚ] Qbar :=
  haveI := tate_isAlgClosure K
  IsAlgClosure.equiv ℚ (AlgebraicClosure K) Qbar

variable {K}

/-- `ℚ̄ → K̄` along `e⁻¹`, as an algebra structure (used only to build `tateGalToQ`). -/
abbrev tateQbarAlgebra (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) : Algebra Qbar (AlgebraicClosure K) :=
  (e.symm : Qbar →+* AlgebraicClosure K).toAlgebra

/-- **The map `Gal(K̄/K) → G_ℚ = Gal(ℚ̄/ℚ)`, `σ ↦ e σ e⁻¹`**, a continuous homomorphism for the
Krull topologies (Mathlib's `Field.absoluteGaloisGroup.mapOfAlgebra`, for the tower `ℚ → ℚ̄ → K̄`
given by `e⁻¹`). Its domain `K̄ ≃ₐ[K] K̄` is Mathlib's `Field.absoluteGaloisGroup K` by
definition. It is the inclusion `G_K ⊂ G_ℚ` of the text (tex 2788) for the embedding `e`.
Kind: definition (continuity PROVED in Mathlib). -/
def tateGalToQ (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* GalQ :=
  letI := tateQbarAlgebra e
  Field.absoluteGaloisGroup.mapOfAlgebra ℚ K

theorem tateGalToQ_symm_apply (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (y : Qbar) :
    e.symm (tateGalToQ e σ y) = σ (e.symm y) := by
  let _ := tateQbarAlgebra e
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) Qbar y

/-- `tateGalToQ e σ = e ∘ σ ∘ e⁻¹`. Kind: PROVED. -/
theorem tateGalToQ_apply (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (y : Qbar) :
    tateGalToQ e σ y = e (σ (e.symm y)) := by
  rw [← tateGalToQ_symm_apply, AlgEquiv.apply_symm_apply]

/-- `(e σ e⁻¹)(e x) = e (σ x)`. Kind: PROVED. -/
theorem tateGalToQ_apply_e (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K) :
    tateGalToQ e σ (e x) = e (σ x) := by
  rw [tateGalToQ_apply, AlgEquiv.symm_apply_apply]

/-- **`Gal(K̄/K) → G_ℚ` is injective.** Kind: PROVED. -/
theorem tateGalToQ_injective (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) :
    Function.Injective (tateGalToQ e) := by
  intro σ τ h
  ext x
  have := congrArg (fun g : GalQ => g (e x)) h
  simp only [tateGalToQ_apply_e] at this
  exact e.injective this

/-- **`Gal(K̄/K) → G_ℚ` is continuous** (Krull topologies). Kind: PROVED. -/
theorem tateGalToQ_continuous (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) :
    Continuous (tateGalToQ e) :=
  (tateGalToQ e).continuous

end GalQ

/-! ### (b) `T₂E/2^i T₂E ≃ E(ℚ̄)[2^i]`, compatibly with `ρ_T` -/

section Level

variable (E : WeierstrassCurve ℚ) (i : ℕ)

/-- **`E(ℚ̄)[2^i]`**, the level `i` of the Tate module `T₂E = lim E(ℚ̄)[2^n]` (vendored Tau Ceti
`TateModuleLevel`). -/
abbrev TateLevel : Type := TauCeti.TateModuleLevel 2 (E⁄Qbar).toAffine.Point i

/-- The projection `T₂E → E(ℚ̄)[2^i]` (Tau Ceti `proj i`). -/
abbrev tateProj : TateMod E 2 →+ TateLevel E i := TauCeti.TateModule.proj i

/-- `|E(ℚ̄)[2^i]| = (2^i)²` (vendored Tau Ceti; `ℚ̄` is separably closed, `2 ≠ 0`). Kind: PROVED. -/
theorem natCard_tateLevel [E.IsElliptic] : Nat.card (TateLevel E i) = (2 ^ i) ^ 2 :=
  (E⁄Qbar).natCard_tateModuleLevel two_ne_zero_qbar i

/-- **`T₂E → E(ℚ̄)[2^i]` is surjective** (Tau Ceti `proj_surjective`, the transitions being onto by
the count). Kind: PROVED. -/
theorem tateProj_surjective [E.IsElliptic] : Function.Surjective (tateProj E i) :=
  TauCeti.TateModule.proj_surjective
    (TauCeti.TateModule.tateModuleTransition_surjective_of_natCard two_ne_zero
      (fun n => natCard_tateLevel E n)) i

/-- **`2^i T₂E`**, as the `ℤ₂`-submodule `(2^i) • T₂E`. -/
def tatePowSub : Submodule ℤ_[2] (TateMod E 2) := Ideal.span {(2 : ℤ_[2]) ^ i} • ⊤

theorem mem_tatePowSub_iff {x : TateMod E 2} :
    x ∈ tatePowSub E i ↔ ∃ y : TateMod E 2, x = (2 : ℤ_[2]) ^ i • y := by
  rw [tatePowSub, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, Submodule.mem_top, rfl⟩

theorem tate_two_pow_smul (y : TateMod E 2) : (2 : ℤ_[2]) ^ i • y = (2 ^ i : ℕ) • y := by
  rw [← Nat.cast_smul_eq_nsmul ℤ_[2]]
  push_cast
  rfl

/-- **The kernel of `T₂E → E(ℚ̄)[2^i]` is `2^i T₂E`** (Tau Ceti `proj_eq_zero_iff`).
Kind: PROVED. -/
theorem tateProj_eq_zero_iff {x : TateMod E 2} : tateProj E i x = 0 ↔ x ∈ tatePowSub E i := by
  rw [mem_tatePowSub_iff, tateProj, TauCeti.TateModule.proj_eq_zero_iff]
  simp only [tate_two_pow_smul]

theorem tatePowSub_le_ker :
    (tatePowSub E i).restrictScalars ℤ ≤ LinearMap.ker (tateProj E i).toIntLinearMap := by
  intro x hx
  rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap]
  exact (tateProj_eq_zero_iff E i).2 hx

/-- The map `T₂E/2^i T₂E → E(ℚ̄)[2^i]` induced by `proj i`. -/
def tateQuotLin : (TateMod E 2 ⧸ tatePowSub E i) →ₗ[ℤ] TateLevel E i :=
  ((tatePowSub E i).restrictScalars ℤ).liftQ (tateProj E i).toIntLinearMap (tatePowSub_le_ker E i)
    ∘ₗ (Submodule.Quotient.restrictScalarsEquiv ℤ (tatePowSub E i)).symm.toLinearMap

theorem tateQuotLin_mk (x : TateMod E 2) :
    tateQuotLin E i (Submodule.Quotient.mk x) = tateProj E i x := rfl

theorem tateQuotLin_bijective [E.IsElliptic] : Function.Bijective (tateQuotLin E i) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [tateQuotLin_mk, tateProj_eq_zero_iff] at hq
      exact (Submodule.Quotient.mk_eq_zero _).2 hq
  · intro y
    obtain ⟨x, rfl⟩ := tateProj_surjective E i y
    exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- **(b) `T₂E/2^i T₂E ≃ E(ℚ̄)[2^i]`**, `x mod 2^i ↦ proj i x`. Since `2^i A_i = 0`, the text's
`T₂E ⊗ A_i` (tex 2726) only sees `T₂E/2^i T₂E`, and the text itself passes between the two forms:
tex 3163–3164 ("Reduction `T/2^aT → T/2^mT` is multiplication by `2^{a−m}` on geometric torsion
points", see `tateProj_reduction`) and tex 3207–3208 (the coefficient module written
`(E[2^m] ⊗ A)(θ)`). Kind: definition, bijectivity PROVED from Tau Ceti's `proj_surjective` and
`proj_eq_zero_iff`. -/
def tateQuotEquiv [E.IsElliptic] : (TateMod E 2 ⧸ tatePowSub E i) ≃+ TateLevel E i :=
  (LinearEquiv.ofBijective (tateQuotLin E i) (tateQuotLin_bijective E i)).toAddEquiv

theorem tateQuotEquiv_mk [E.IsElliptic] (x : TateMod E 2) :
    tateQuotEquiv E i (Submodule.Quotient.mk x) = tateProj E i x := rfl

/-- `tateQuotEquiv` is semilinear along the reduction `ℤ₂ → ℤ/2^i`. Kind: PROVED. -/
theorem tateQuotEquiv_smul [E.IsElliptic] (a : ℤ_[2]) (q : TateMod E 2 ⧸ tatePowSub E i) :
    tateQuotEquiv E i (a • q) = PadicInt.toZModPow i a • tateQuotEquiv E i q := by
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, tateQuotEquiv_mk, tateQuotEquiv_mk]
    exact TauCeti.TateModule.proj_smul a x i

/-- **Reduction `T/2^aT → T/2^mT` is multiplication by `2^{a−m}` on geometric torsion points**
(tex 3163–3164): `proj_m x = 2^{a−m} · proj_a x` in `E(ℚ̄)` for `m ≤ a` (Tau Ceti
`coe_proj_eq_pow_sub_nsmul`). Kind: PROVED. -/
theorem tateProj_reduction {m a : ℕ} (h : m ≤ a) (x : TateMod E 2) :
    ((tateProj E m x : TateLevel E m) : (E⁄Qbar).toAffine.Point) =
      2 ^ (a - m) • ((tateProj E a x : TateLevel E a) : (E⁄Qbar).toAffine.Point) :=
  TauCeti.TateModule.coe_proj_eq_pow_sub_nsmul x h

/-- The action of `g ∈ G_ℚ` on `E(ℚ̄)[2^i]` (on the coordinates of points). -/
def tateLevelAct (g : GalQ) : TateLevel E i →+ TateLevel E i :=
  TauCeti.TateModule.levelMap (Affine.Point.map (W' := E) g.toAlgHom) i

theorem coe_tateLevelAct (g : GalQ) (P : TateLevel E i) :
    ((tateLevelAct E i g P : TateLevel E i) : (E⁄Qbar).toAffine.Point) =
      Affine.Point.map (W' := E) g.toAlgHom (P : (E⁄Qbar).toAffine.Point) := rfl

/-- `proj i (ρ_T(g) x) = g (proj i x)` (lane RC9's `coe_proj_tateRep`). Kind: PROVED. -/
theorem tateProj_tateRep (g : GalQ) (x : TateMod E 2) :
    tateProj E i (tateRep E 2 g x) = tateLevelAct E i g (tateProj E i x) :=
  Subtype.ext (coe_proj_tateRep E 2 g x i)

theorem tatePowSub_le_comap (g : GalQ) :
    tatePowSub E i ≤ (tatePowSub E i).comap (tateRep E 2 g) := by
  intro x hx
  rw [Submodule.mem_comap]
  obtain ⟨y, rfl⟩ := (mem_tatePowSub_iff E i).1 hx
  rw [map_smul]
  exact (mem_tatePowSub_iff E i).2 ⟨_, rfl⟩

/-- **`ρ_T(g)` reduced mod `2^i`**: the map induced by `tateRep E 2 g` on `T₂E/2^i T₂E`. -/
def tateRepMod (g : GalQ) :
    (TateMod E 2 ⧸ tatePowSub E i) →ₗ[ℤ_[2]] (TateMod E 2 ⧸ tatePowSub E i) :=
  (tatePowSub E i).mapQ (tatePowSub E i) (tateRep E 2 g) (tatePowSub_le_comap E i g)

theorem tateRepMod_mk (g : GalQ) (x : TateMod E 2) :
    tateRepMod E i g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (tateRep E 2 g x) := rfl

/-- The reduction mod `2^i` of `ρ_T` is a representation of `G_ℚ` on `T₂E/2^i T₂E`. -/
def tateRepModHom : Representation ℤ_[2] GalQ (TateMod E 2 ⧸ tatePowSub E i) where
  toFun g := tateRepMod E i g
  map_one' := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H x => rw [tateRepMod_mk, map_one, Module.End.one_apply, Module.End.one_apply]
  map_mul' g h := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H x => rw [tateRepMod_mk, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        tateRepMod_mk, tateRepMod_mk]

/-- **(b) compatibility with `tateRep`**: `T₂E/2^i T₂E ≃ E(ℚ̄)[2^i]` intertwines the reduction of
`ρ_T(g)` with the coordinatewise action of `g`. Kind: PROVED. -/
theorem tateQuotEquiv_tateRepMod [E.IsElliptic] (g : GalQ) (q : TateMod E 2 ⧸ tatePowSub E i) :
    tateQuotEquiv E i (tateRepMod E i g q) = tateLevelAct E i g (tateQuotEquiv E i q) := by
  induction q using Submodule.Quotient.induction_on with
  | H x => rw [tateRepMod_mk, tateQuotEquiv_mk, tateQuotEquiv_mk, tateProj_tateRep]

end Level

/-! ### (c) `E(K_S)[2^i] ≃ E(ℚ̄)[2^i]`, equivariantly -/

section Tors

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (E : WeierstrassCurve ℚ)

/-- `(E_K)_{K_S} = E_{K_S}` (both are `E` with coefficients pushed along `ℚ → K_S`). -/
theorem tateCurveEqS : (E⁄K)⁄(KS K S) = E⁄(KS K S) :=
  (congrArg E.map (IsScalarTower.algebraMap_eq ℚ K (KS K S))).symm

/-- The points of two equal Weierstrass curves (transport along the equality). -/
def tatePointCongr {F : Type} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    (h : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

theorem tatePointCongr_some {F : Type} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    (h : W₁ = W₂) {x y : F} (hxy : W₁.toAffine.Nonsingular x y) :
    tatePointCongr h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst h
  rfl

variable {K} (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)

/-- The `ℚ`-embedding `K_S ⊂ K̄ ≅ ℚ̄` (along `e`). -/
def tateEmbS : KS K S →ₐ[ℚ] Qbar :=
  e.toAlgHom.comp ((inclS K S).restrictScalars ℚ)

theorem tateEmbS_apply (x : KS K S) : tateEmbS S e x = e (inclS K S x) := rfl

/-- The point map `E_K(K_S) → E(ℚ̄)` along `K_S ⊂ K̄ ≅ ℚ̄` (on coordinates). -/
def tatePointMap : ((E⁄K)⁄(KS K S)).toAffine.Point →+ (E⁄Qbar).toAffine.Point :=
  (Affine.Point.map (W' := E) (tateEmbS S e)).comp
    (tatePointCongr (tateCurveEqS K S E)).toAddMonoidHom

theorem tatePointMap_some {x y : KS K S} (h : ((E⁄K)⁄(KS K S)).toAffine.Nonsingular x y) :
    ∃ h', tatePointMap S E e (.some x y h) = .some (tateEmbS S e x) (tateEmbS S e y) h' :=
  ⟨_, (congrArg (Affine.Point.map (W' := E) (tateEmbS S e))
    (tatePointCongr_some (tateCurveEqS K S E) h)).trans (Affine.Point.map_some _ _)⟩

theorem tatePointMap_injective : Function.Injective (tatePointMap S E e) :=
  (Affine.Point.map_injective _).comp (tatePointCongr _).injective

variable (i : ℕ)

/-- **`E(K_S)[2^i] → E(ℚ̄)[2^i]`**, the coordinate map along `K_S ⊂ K̄ ≅ ℚ̄`, on lane RC28's
`TorsS K S (E⁄K) (2^i)`. -/
def tateTorsMap : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ) →+ TateLevel E i :=
  TauCeti.TateModule.levelMap (p := 2) (tatePointMap S E e) i

theorem coe_tateTorsMap (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    ((tateTorsMap S E e i P : TateLevel E i) : (E⁄Qbar).toAffine.Point) =
      tatePointMap S E e (P : ((E⁄K)⁄(KS K S)).toAffine.Point) := rfl

/-- `E(K_S)[2^i] → E(ℚ̄)[2^i]` is injective (no hypothesis). Kind: PROVED. -/
theorem tateTorsMap_injective : Function.Injective (tateTorsMap S E e i) := fun _ _ h =>
  Subtype.ext (tatePointMap_injective S E e (congrArg Subtype.val h))

/-- **Under `FullTorsion`, `E(K_S)[2^i] → E(ℚ̄)[2^i]` is bijective** (injective, and both sides
have `(2^i)²` elements). `FullTorsion` is lane RC28's GLUE (Néron–Ogg–Shafarevich). Kind:
PROVED. -/
theorem tateTorsMap_bijective [E.IsElliptic] (hW : FullTorsion K S (E⁄K) (2 ^ i)) :
    Function.Bijective (tateTorsMap S E e i) := by
  have : Finite (TateLevel E i) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_tateLevel]; positivity)
  refine (tateTorsMap_injective S E e i).bijective_of_nat_card_le ?_
  rw [natCard_tateLevel]
  exact hW.ge

/-- The lift condition: `σ' ∈ Gal(K̄/K)` restricts to `σ ∈ G_{K,S}` on `K_S`. -/
theorem tateEmbS_galS (σ : GKS K S) (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x)) (x : KS K S) :
    tateEmbS S e (galS K S σ x) = tateGalToQ e σ' (tateEmbS S e x) := by
  rw [tateEmbS_apply, tateEmbS_apply, tateGalToQ_apply_e, hσ']

/-- **(c) Equivariance of `E(K_S)[2^i] → E(ℚ̄)[2^i]`**: for `σ ∈ G_{K,S}` and **any** lift
`σ' ∈ Gal(K̄/K)` of `σ` (`σ'` agrees with `σ` on `K_S`), the image of `σP` is
`(e σ' e⁻¹)(image of P)`. Kind: PROVED. -/
theorem tateTorsMap_smul (σ : GKS K S) (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x))
    (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    tateTorsMap S E e i (σ • P) = tateLevelAct E i (tateGalToQ e σ') (tateTorsMap S E e i P) := by
  apply Subtype.ext
  rw [coe_tateLevelAct, coe_tateTorsMap, coe_tateTorsMap, coe_smul_torsS]
  obtain ⟨P, -⟩ := P
  change tatePointMap S E e (Affine.Point.map (galS K S σ).toAlgHom P) =
    Affine.Point.map (W' := E) (tateGalToQ e σ').toAlgHom (tatePointMap S E e P)
  rcases P with _ | ⟨x, y, h⟩
  · have h0 : (Affine.Point.zero : ((E⁄K)⁄(KS K S)).toAffine.Point) = 0 := rfl
    rw [h0, map_zero, map_zero, map_zero]
  · simp only [tatePointMap, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, Affine.Point.map_some, tatePointCongr_some,
      Affine.Point.some.injEq]
    exact ⟨tateEmbS_galS S e σ σ' hσ' x, tateEmbS_galS S e σ σ' hσ' y⟩

/-- **(c) `E(K_S)[2^i] ≃+ E(ℚ̄)[2^i]`** under `FullTorsion K S (E⁄K) (2^i)` (GLUE). -/
def tateTorsEquiv [E.IsElliptic] (hW : FullTorsion K S (E⁄K) (2 ^ i)) :
    TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ) ≃+ TateLevel E i :=
  AddEquiv.ofBijective (tateTorsMap S E e i) (tateTorsMap_bijective S E e i hW)

theorem tateTorsEquiv_apply [E.IsElliptic] (hW : FullTorsion K S (E⁄K) (2 ^ i))
    (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    tateTorsEquiv S E e i hW P = tateTorsMap S E e i P :=
  rfl

/-- **(c) `E(K_S)[2^i] ≃+ E(ℚ̄)[2^i] ≃+ T₂E/2^i T₂E`** under `FullTorsion K S (E⁄K) (2^i)`
(GLUE). -/
def tateTorsQuotEquiv [E.IsElliptic] (hW : FullTorsion K S (E⁄K) (2 ^ i)) :
    TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ) ≃+ (TateMod E 2 ⧸ tatePowSub E i) :=
  (tateTorsEquiv S E e i hW).trans (tateQuotEquiv E i).symm

theorem tateQuotEquiv_tateTorsQuotEquiv [E.IsElliptic] (hW : FullTorsion K S (E⁄K) (2 ^ i))
    (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    tateQuotEquiv E i (tateTorsQuotEquiv S E e i hW P) = tateTorsMap S E e i P :=
  (tateQuotEquiv E i).apply_symm_apply _

/-- **(c) The identification `E(K_S)[2^i] ≃ T₂E/2^i T₂E` is `G_{K,S}`-equivariant**: for
`σ ∈ G_{K,S}` and **any** lift `σ' ∈ Gal(K̄/K)` of `σ`, it carries `σ` on `E(K_S)[2^i]` to the
reduction mod `2^i` of `ρ_T = tateRep E 2` (lanes RC9/RC17) at `tateGalToQ e σ' ∈ G_ℚ`.
In particular the right side does not depend on the lift. Kind: PROVED (from the GLUE
`FullTorsion`, used only for bijectivity). -/
theorem tateTorsQuotEquiv_smul [E.IsElliptic] (hW : FullTorsion K S (E⁄K) (2 ^ i))
    (σ : GKS K S) (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x))
    (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    tateTorsQuotEquiv S E e i hW (σ • P) =
      tateRepMod E i (tateGalToQ e σ') (tateTorsQuotEquiv S E e i hW P) := by
  apply (tateQuotEquiv E i).injective
  rw [tateQuotEquiv_tateRepMod, tateQuotEquiv_tateTorsQuotEquiv,
    tateQuotEquiv_tateTorsQuotEquiv, tateTorsMap_smul S E e i σ σ' hσ']

/-! #### Compatibility with lane RC28's `inclTors : E(K_S)[N] → E(K̄)[N]` -/

/-- `(E_K)_{K̄} = E_{K̄}`. -/
theorem tateCurveEqBar : (E⁄K)⁄(AlgebraicClosure K) = E⁄(AlgebraicClosure K) :=
  (congrArg E.map (IsScalarTower.algebraMap_eq ℚ K (AlgebraicClosure K))).symm

/-- The point map `E_K(K̄) → E(ℚ̄)` along `e`. -/
def tateBarPointMap :
    ((E⁄K)⁄(AlgebraicClosure K)).toAffine.Point →+ (E⁄Qbar).toAffine.Point :=
  (Affine.Point.map (W' := E) e.toAlgHom).comp
    (tatePointCongr (tateCurveEqBar (K := K) E)).toAddMonoidHom

/-- **`E_K(K̄)[2^i] → E(ℚ̄)[2^i]`** along `e`, on lane RC28's `TorsBar (E⁄K) (2^i)`. -/
def tateBarMap : TorsBar (E⁄K) (2 ^ i) →+ TateLevel E i :=
  TauCeti.TateModule.levelMap (p := 2) (tateBarPointMap E e) i

/-- **`tateTorsMap` is lane RC28's `inclTors` followed by `K̄ ≅ ℚ̄`**: `E(K_S)[2^i] → E(K̄)[2^i] →
E(ℚ̄)[2^i]`. So lane RC28's Weil pairing `weilS` (defined through `inclTors`) is read on the same
points. Kind: PROVED. -/
theorem tateTorsMap_eq_bar (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    tateTorsMap S E e i P = tateBarMap E e i (inclTors (S := S) (E⁄K) (2 ^ i) P) := by
  apply Subtype.ext
  obtain ⟨P, -⟩ := P
  change tatePointMap S E e P = tateBarPointMap E e (Affine.Point.map (inclS K S) P)
  rcases P with _ | ⟨x, y, h⟩
  · have h0 : (Affine.Point.zero : ((E⁄K)⁄(KS K S)).toAffine.Point) = 0 := rfl
    rw [h0, map_zero, map_zero, map_zero]
  · simp only [tatePointMap, tateBarPointMap, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, Affine.Point.map_some, tatePointCongr_some,
      Affine.Point.some.injEq]
    exact ⟨rfl, rfl⟩

/-- **Under `FullTorsion`, the action of `Gal(K̄/K)` on `T₂E/2^i T₂E` factors through `G_{K,S}`**:
two elements of `Gal(K̄/K)` with the same restriction to `K_S` act in the same way (through
`tateGalToQ e`). This is the formal content of the text's use of `M_i` as a `G_{K,S}`-module
(`RΓ(G_{K,S}, M_i)`, tex 3455–3463). Kind: PROVED (GLUE `FullTorsion`). -/
theorem tateRepMod_factor [E.IsElliptic] (hW : FullTorsion K S (E⁄K) (2 ^ i))
    (σ₁ σ₂ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x : KS K S, σ₁ (inclS K S x) = σ₂ (inclS K S x)) :
    tateRepMod E i (tateGalToQ e σ₁) = tateRepMod E i (tateGalToQ e σ₂) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : GKS K S, ∀ x : KS K S, σ₂ (inclS K S x) = inclS K S (galS K S σ x) :=
    ⟨resAbsCont K S σ₂, fun x => (resAbs_apply_coe K S σ₂ x).symm⟩
  refine LinearMap.ext fun q => ?_
  obtain ⟨P, rfl⟩ := (tateTorsQuotEquiv S E e i hW).surjective q
  rw [← tateTorsQuotEquiv_smul S E e i hW σ σ₁ (fun x => (h x).trans (hσ x)),
    ← tateTorsQuotEquiv_smul S E e i hW σ σ₂ hσ]

end Tors

/-! ### Lifts of `σ ∈ G_{K,S}` to `Gal(K̄/K)` -/

section Lift

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **Every `σ ∈ G_{K,S}` has a lift to `Gal(K̄/K)`** (lane RC28's `liftGal`; non-vacuity of the
lift hypothesis of `tateTorsMap_smul`). Kind: PROVED. -/
theorem tate_exists_lift (σ : GKS K S) :
    ∃ σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x) :=
  ⟨liftGal σ, liftGal_spec σ⟩

omit [NumberField K] in
/-- The lift condition is exactly "`σ'` restricts to `σ`" (lane RC26's `resAbsCont`).
Kind: PROVED. -/
theorem tate_isLift_iff (σ : GKS K S) (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x)) ↔ resAbsCont K S σ' = σ := by
  constructor
  · intro h
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    exact (resAbs_apply_coe K S σ' x).trans (h x)
  · intro h x
    rw [← h]
    exact (resAbs_apply_coe K S σ' x).symm

end Lift

/-! ### (d) The matrix form -/

section Matrix

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (i : ℕ)

/-- `c ↦ ∑ c_j · proj i (b_j)` for lane RC9's basis `b = tateBasis E` of `T₂E`. -/
def tateLevelLin : (Fin 2 → ZMod (2 ^ i)) →ₗ[ZMod (2 ^ i)] TateLevel E i :=
  Fintype.linearCombination (ZMod (2 ^ i)) (fun j => tateProj E i (tateBasis E j))

theorem tateProj_eq_sum (x : TateMod E 2) :
    tateProj E i x =
      ∑ j, PadicInt.toZModPow i ((tateBasis E).repr x j) • tateProj E i (tateBasis E j) := by
  conv_lhs => rw [← (tateBasis E).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact TauCeti.TateModule.proj_smul _ _ i

theorem tateLevelLin_bijective : Function.Bijective (tateLevelLin E i) := by
  have hsurj : Function.Surjective (tateLevelLin E i) := by
    intro y
    obtain ⟨x, rfl⟩ := tateProj_surjective E i y
    refine ⟨fun j => PadicInt.toZModPow i ((tateBasis E).repr x j), ?_⟩
    rw [tateLevelLin, Fintype.linearCombination_apply, tateProj_eq_sum]
  refine hsurj.bijective_of_nat_card_le ?_
  rw [natCard_tateLevel, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The `ℤ/2^i`-basis of `E(ℚ̄)[2^i]` reducing lane RC9's `tateBasis E`**:
`tateLevelBasis E i j = proj i (tateBasis E j)` (`tateLevelBasis_apply`). -/
def tateLevelBasis : Module.Basis (Fin 2) (ZMod (2 ^ i)) (TateLevel E i) :=
  Module.Basis.ofEquivFun
    (LinearEquiv.ofBijective (tateLevelLin E i) (tateLevelLin_bijective E i)).symm

theorem tateLevelBasis_apply (j : Fin 2) :
    tateLevelBasis E i j = tateProj E i (tateBasis E j) := by
  simp only [tateLevelBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm,
    LinearEquiv.ofBijective_apply, tateLevelLin, Fintype.linearCombination_apply_single, one_smul]

/-- `ρ_T(g) b_j = ∑_k M_{kj} b_k` for `M = tateMatrix E g` (lane RC17). Kind: PROVED. -/
theorem tateRep_tateBasis (g : GalQ) (j : Fin 2) :
    tateRep E 2 g (tateBasis E j) = ∑ k, tateMatrix E g k j • tateBasis E k := by
  conv_lhs => rw [← (tateBasis E).sum_repr (tateRep E 2 g (tateBasis E j))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tateMatrix, LinearMap.toMatrix_apply]

/-- In the basis `tateLevelBasis E i`, `g ∈ G_ℚ` acts on `E(ℚ̄)[2^i]` by `tateMatrix E g` reduced
mod `2^i`. Kind: PROVED. -/
theorem tateLevelAct_basis (g : GalQ) (j : Fin 2) :
    tateLevelAct E i g (tateLevelBasis E i j) =
      ∑ k, PadicInt.toZModPow i (tateMatrix E g k j) • tateLevelBasis E i k := by
  rw [tateLevelBasis_apply, ← tateProj_tateRep, tateRep_tateBasis, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tateLevelBasis_apply]
  exact TauCeti.TateModule.proj_smul _ _ i

end Matrix

section MatrixAct

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (E : WeierstrassCurve ℚ) (i : ℕ)

/-- The action of `σ ∈ G_{K,S}` on `E(K_S)[2^i]`, as a `ℤ/2^i`-linear map. -/
def tateTorsAct (σ : GKS K S) :
    TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ) →ₗ[ZMod (2 ^ i)] TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ) :=
  AddMonoidHom.toZModLinearMap (2 ^ i)
    { toFun := fun P => σ • P
      map_zero' := smul_zero σ
      map_add' := smul_add σ }

theorem tateTorsAct_apply (σ : GKS K S) (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    tateTorsAct S E i σ P = σ • P := rfl

/-- `σ ↦ (action of σ on E(K_S)[2^i])`, a homomorphism `G_{K,S} → End_{ℤ/2^i}(E(K_S)[2^i])`. -/
def tateTorsActHom :
    GKS K S →* Module.End (ZMod (2 ^ i)) (TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) where
  toFun σ := tateTorsAct S E i σ
  map_one' := LinearMap.ext fun P => one_smul _ P
  map_mul' σ τ := LinearMap.ext fun P => mul_smul σ τ P

end MatrixAct

section MatrixS

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)

/-- `E(K_S)[2^i] ≃ E(ℚ̄)[2^i]` as `ℤ/2^i`-modules (under `FullTorsion`, GLUE). -/
def tateTorsLinEquiv (hW : FullTorsion K S (E⁄K) (2 ^ i)) :
    TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ) ≃ₗ[ZMod (2 ^ i)] TateLevel E i :=
  (tateTorsEquiv S E e i hW).toLinearEquiv fun c P => ZMod.map_smul (tateTorsEquiv S E e i hW) c P

/-- **(d) The basis of `E(K_S)[2^i]` transported from the reduction of `tateBasis E`** (under
`FullTorsion`, GLUE). -/
def tateTorsBasis (hW : FullTorsion K S (E⁄K) (2 ^ i)) :
    Module.Basis (Fin 2) (ZMod (2 ^ i)) (TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :=
  (tateLevelBasis E i).map (tateTorsLinEquiv S E e i hW).symm

theorem tateTorsMap_tateTorsBasis (hW : FullTorsion K S (E⁄K) (2 ^ i)) (j : Fin 2) :
    tateTorsMap S E e i (tateTorsBasis S E e i hW j) = tateProj E i (tateBasis E j) := by
  rw [← tateLevelBasis_apply, tateTorsBasis, Module.Basis.map_apply]
  exact (tateTorsLinEquiv S E e i hW).apply_symm_apply _

/-- **(d) The matrix of `σ ∈ G_{K,S}` on `E(K_S)[2^i]`** in `tateTorsBasis`: for any lift `σ'` of
`σ`, `σ b_j = ∑_k (tateMatrix E (e σ' e⁻¹))_{kj} mod 2^i · b_k`. Kind: PROVED (GLUE
`FullTorsion` for the basis). -/
theorem tateTorsBasis_smul (hW : FullTorsion K S (E⁄K) (2 ^ i)) (σ : GKS K S)
    (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x)) (j : Fin 2) :
    σ • tateTorsBasis S E e i hW j =
      ∑ k, PadicInt.toZModPow i (tateMatrix E (tateGalToQ e σ') k j) •
        tateTorsBasis S E e i hW k := by
  apply tateTorsMap_injective S E e i
  rw [tateTorsMap_smul S E e i σ σ' hσ', tateTorsMap_tateTorsBasis, ← tateLevelBasis_apply,
    tateLevelAct_basis, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ZMod.map_smul, tateTorsMap_tateTorsBasis, tateLevelBasis_apply]

/-- **(d) `Mat(σ) = tateMatrix E (tateGalToQ e σ') mod 2^i`** (lane RC17's `tateMatrix`).
Kind: PROVED. -/
theorem toMatrix_tateTorsAct (hW : FullTorsion K S (E⁄K) (2 ^ i)) (σ : GKS K S)
    (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x)) :
    LinearMap.toMatrix (tateTorsBasis S E e i hW) (tateTorsBasis S E e i hW)
        (tateTorsAct S E i σ) =
      (tateMatrix E (tateGalToQ e σ')).map (PadicInt.toZModPow i) := by
  ext k j
  rw [LinearMap.toMatrix_apply, tateTorsAct_apply, tateTorsBasis_smul S E e i hW σ σ' hσ',
    Module.Basis.repr_sum_self, Matrix.map_apply]

/-- **(d) The representation `G_{K,S} → GL₂(ℤ/2^i)` on `E(K_S)[2^i]`** in `tateTorsBasis`
(under `FullTorsion`, GLUE). -/
def tateRhoTors (hW : FullTorsion K S (E⁄K) (2 ^ i)) : GKS K S →* GL (Fin 2) (ZMod (2 ^ i)) :=
  (Units.map (LinearMap.toMatrixAlgEquiv (tateTorsBasis S E e i hW)).toRingEquiv.toMonoidHom).comp
    (tateTorsActHom S E i).toHomUnits

theorem coe_tateRhoTors (hW : FullTorsion K S (E⁄K) (2 ^ i)) (σ : GKS K S) :
    ((tateRhoTors S E e i hW σ : GL (Fin 2) (ZMod (2 ^ i))) :
        Matrix (Fin 2) (Fin 2) (ZMod (2 ^ i))) =
      LinearMap.toMatrix (tateTorsBasis S E e i hW) (tateTorsBasis S E e i hW)
        (tateTorsAct S E i σ) :=
  rfl

/-- **(d) `tateRhoTors σ` is lane RC17's `rhoGL E` at `tateGalToQ e σ'` reduced mod `2^i`**, for
any lift `σ'` of `σ`. Kind: PROVED. -/
theorem tateRhoTors_eq (hW : FullTorsion K S (E⁄K) (2 ^ i)) (σ : GKS K S)
    (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x)) :
    tateRhoTors S E e i hW σ =
      Matrix.GeneralLinearGroup.map (PadicInt.toZModPow i) (rhoGL E (tateGalToQ e σ')) := by
  ext k j
  rw [coe_tateRhoTors, toMatrix_tateTorsAct S E e i hW σ σ' hσ']
  rfl

end MatrixS

/-! ### (f) The actual complex conjugation `ρ_T(τ)` (tex 2778, 2798–2805) -/

section Conj

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (E : WeierstrassCurve ℚ) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (C : ActualConj K S)

/-- Lane RC28's conjugation `τ` of `K̄` as a `ℚ`-algebra automorphism (every ring automorphism
fixes `ℚ`). -/
def tateTauAlg : AlgebraicClosure K ≃ₐ[ℚ] AlgebraicClosure K :=
  AlgEquiv.ofRingEquiv (f := C.τ) fun q =>
    congrArg (fun f : ℚ →+* AlgebraicClosure K => f q)
      (Subsingleton.elim ((C.τ : AlgebraicClosure K →+* AlgebraicClosure K).comp
        (algebraMap ℚ (AlgebraicClosure K))) (algebraMap ℚ (AlgebraicClosure K)))

/-- **The text's actual complex conjugation `τ ∈ G_ℚ`** (tex 2778) for lane RC28's `ActualConj`:
`e τ e⁻¹`. -/
def tateConjQ : GalQ :=
  (e.symm.trans (tateTauAlg C)).trans e

theorem tateConjQ_apply_e (x : AlgebraicClosure K) : tateConjQ e C (e x) = e (C.τ x) := by
  change e (C.τ (e.symm (e x))) = e (C.τ x)
  rw [AlgEquiv.symm_apply_apply]

/-- `τ² = 1` (tex 2778). Kind: PROVED. -/
theorem tateConjQ_mul_self : tateConjQ e C * tateConjQ e C = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [AlgEquiv.mul_apply, tateConjQ_apply_e, tateConjQ_apply_e, C.hinv, AlgEquiv.one_apply]

/-- `e τ e⁻¹` is the complex conjugation of `ℚ̄` for the complex embedding `ι ∘ e⁻¹`.
Kind: PROVED. -/
theorem tateConjQ_complex (y : Qbar) :
    C.ι (e.symm (tateConjQ e C y)) = starRingEnd ℂ (C.ι (e.symm y)) := by
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [tateConjQ_apply_e, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, C.hι]

/-- `E_K` is fixed by `κ` (its coefficients are rational): lane RC28's hypothesis of `conjTors`
holds for `W = E⁄K`. Kind: PROVED. -/
theorem tate_baseChange_map_kappa : (E⁄K).map (C.κ : K →+* K) = E⁄K := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  exact congrArg E.map (Subsingleton.elim _ _)

variable (i : ℕ)

/-- **`ρ_T(τ)` on `E(K_S)[2^i]` is `ρ_T(e τ e⁻¹)` on `E(ℚ̄)[2^i]`**: lane RC28's `conjTors`
(the coordinate action of `τ`, its `ρ_T(τ)` of tex 2801) corresponds to the coordinate action of
`tateConjQ e C ∈ G_ℚ`. Kind: PROVED. -/
theorem tateTorsMap_conjTors (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    tateTorsMap S E e i (conjTors C (E⁄K) (tate_baseChange_map_kappa E C) _ P) =
      tateLevelAct E i (tateConjQ e C) (tateTorsMap S E e i P) := by
  apply Subtype.ext
  rw [coe_tateLevelAct, coe_tateTorsMap, coe_tateTorsMap, coe_conjTors]
  obtain ⟨P, -⟩ := P
  change tatePointMap S E e (conjPt C (E⁄K) (tate_baseChange_map_kappa E C) P) =
    Affine.Point.map (W' := E) (tateConjQ e C).toAlgHom (tatePointMap S E e P)
  rcases P with _ | ⟨x, y, h⟩
  · have h0 : (Affine.Point.zero : ((E⁄K)⁄(KS K S)).toAffine.Point) = 0 := rfl
    rw [h0, conjPt_zero, map_zero, map_zero]
  · rw [conjPt_some]
    simp only [tatePointMap, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, Affine.Point.map_some, tatePointCongr_some,
      Affine.Point.some.injEq]
    refine ⟨?_, ?_⟩
    · change e (inclS K S (C.tau x)) = tateConjQ e C (e (inclS K S x))
      rw [tateConjQ_apply_e]
      exact congrArg e (C.coe_tau x)
    · change e (inclS K S (C.tau y)) = tateConjQ e C (e (inclS K S y))
      rw [tateConjQ_apply_e]
      exact congrArg e (C.coe_tau y)

/-- **(f) `ρ_T(τ)` under `E(K_S)[2^i] ≃ T₂E/2^i T₂E`**: lane RC28's `conjTors` is the reduction
mod `2^i` of `tateRep E 2` at the actual complex conjugation `tateConjQ e C` (tex 2798–2805).
Kind: PROVED (GLUE `FullTorsion`). -/
theorem tateTorsQuotEquiv_conjTors [E.IsElliptic] (hW : FullTorsion K S (E⁄K) (2 ^ i))
    (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    tateTorsQuotEquiv S E e i hW (conjTors C (E⁄K) (tate_baseChange_map_kappa E C) _ P) =
      tateRepMod E i (tateConjQ e C) (tateTorsQuotEquiv S E e i hW P) := by
  apply (tateQuotEquiv E i).injective
  rw [tateQuotEquiv_tateRepMod, tateQuotEquiv_tateTorsQuotEquiv,
    tateQuotEquiv_tateTorsQuotEquiv, tateTorsMap_conjTors]

/-- Non-vacuity of lane RC28's `ActualConj` (its `actualConj_nonempty_gaussian`): an actual complex
conjugation exists for `K = ℚ(i)` and `S` the places above `2`, nontrivial on `K`. -/
example : ∃ C : ActualConj (CyclotomicField 4 ℚ)
      {v : HeightOneSpectrum (𝓞 (CyclotomicField 4 ℚ)) |
        v.asIdeal.comap (algebraMap ℤ (𝓞 (CyclotomicField 4 ℚ))) ∈
          ({Ideal.span {(2 : ℤ)}} : Set (Ideal ℤ))}, C.κ ≠ RingEquiv.refl _ :=
  actualConj_nonempty_gaussian

end Conj

/-! ### Non-vacuity of `FullTorsion K S (E⁄K) (2^i)` -/

section NonVacuity

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- `FullTorsion K S (E⁄K) (2^0)` for every `E` (lane RC28's `fullTorsion_one`). Kind: PROVED. -/
theorem tate_fullTorsion_zero (E : WeierstrassCurve ℚ) : FullTorsion K S (E⁄K) (2 ^ 0) := by
  rw [pow_zero]
  exact fullTorsion_one _

/-- The base change of the manuscript's `E_ℓ = Ecurve ℓ` to `K` is lane RC28's `curveEll ℓ`. -/
theorem tate_ecurve_baseChange (ℓ : ℕ) :
    (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)⁄K = curveEll (ℓ : K) := by
  rw [curveEll_coeffs]
  simp only [ZInQ.Contrib.CloudB3RC53.Ecurve, ZInQ.Manuscript.curve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, map_zero, map_mul, map_pow, map_neg, map_ofNat, map_natCast]

/-- **`FullTorsion K S (E_ℓ⁄K) (2^1)` for the manuscript's curves `E_ℓ : y² = x(x−ℓ)(x+3ℓ)`**
(tex 1760–1830; full rational `2`-torsion), every `K` and every `S` (lane RC28's
`fullTorsion_two_curveEll`). Kind: PROVED. -/
theorem tate_fullTorsion_ecurve {ℓ : ℕ} (hℓ : 0 < ℓ) :
    FullTorsion K S ((ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)⁄K) (2 ^ 1) := by
  rw [pow_one, tate_ecurve_baseChange]
  exact fullTorsion_two_curveEll (by exact_mod_cast hℓ.ne')

/-- Non-vacuity of the whole chain: for `E_ℓ` at `i = 1`, the equivariant identification
`E(K_S)[2] ≃ T₂E/2T₂E` exists for every `K`, `S` (with `e = tateAlgEquiv K`). -/
example {ℓ : ℕ} (hℓ : 0 < ℓ) :
    haveI := ecurve_isElliptic hℓ
    Nonempty (TorsS K S ((ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)⁄K) ((2 ^ 1 : ℕ) : ℤ) ≃+
      (TateMod (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) 2 ⧸
        tatePowSub (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) 1)) :=
  haveI := ecurve_isElliptic hℓ
  ⟨tateTorsQuotEquiv S _ (tateAlgEquiv K) 1 (tate_fullTorsion_ecurve hℓ)⟩

end NonVacuity

end ZInQ.Manuscript.RC.KummerMaps
