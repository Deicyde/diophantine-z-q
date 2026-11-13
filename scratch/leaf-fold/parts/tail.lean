
/-! ## leaf-fold (2026-11-13): the closed leaves folded in, three statement repairs, the open bundles

Since leaf-fold the whole file lives in `namespace HDec`, so that it can import the closed proofs of
`ZInQKernel/Contrib/`. Those proofs are stated over `ZInQKernel/HDecomp/`, the kernel port of this
file, which declares the same names at the root (`PkgI6.LocalH2CardC`, …). Inside `HDec` every
name of this file resolves to this file's copy (innermost namespace first), and a Contrib theorem
about the root copy is converted to this file's copy by `exact` (definitional unfolding). In
addition, `#hdec_same HDec.X` checks *syntactically* that `HDec.X` and the root `X`, and every
`HDec` constant they mention, have the same type and the same body after deleting the prefix
`HDec.` (theorems: same type). -/

section LeafFoldCheckSec

open Lean Elab Command

/-- `#hdec_same HDec.X`: compare `HDec.X` with the root `X`, recursively through every `HDec.`
constant that the types and (for definitions) the bodies mention. Reports the number of constants
compared and every difference. -/
elab "#hdec_same " id:ident : command => do
  let env ← getEnv
  let n := id.getId
  let strip : Name → Name := fun c =>
    if (`HDec).isPrefixOf c then c.replacePrefix `HDec .anonymous else c
  let mapE : Expr → Expr := fun e => e.replace fun
    | .const c us => some (.const (strip c) us)
    | _ => none
  let mut todo : Array Name := #[n]
  let mut seen : NameSet := {}
  let mut bad : Array String := #[]
  let mut count := 0
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    count := count + 1
    match env.find? c, env.find? (strip c) with
    | none, _ => bad := bad.push s!"{c}: not found"
    | some _, none => bad := bad.push s!"{c}: no root counterpart"
    | some ci, some ri =>
      if mapE ci.type != ri.type then bad := bad.push s!"{c}: types differ"
      let isThm := match ci with | .thmInfo _ => true | _ => false
      let mut used := ci.type.getUsedConstants
      if !isThm then
        match ci.value?, ri.value? with
        | some v, some w =>
          if mapE v != w then bad := bad.push s!"{c}: bodies differ"
          used := used ++ v.getUsedConstants
        | none, none => pure ()
        | _, _ => bad := bad.push s!"{c}: kinds differ"
      match ci with
      | .inductInfo v => used := used ++ v.ctors.toArray
      | _ => pure ()
      for u in used do
        if (`HDec).isPrefixOf u && !seen.contains u then todo := todo.push u
  if bad.isEmpty then
    logInfo m!"{n}: {count} HDec constants compared; each is its root counterpart verbatim (up to the prefix)"
  else
    logInfo m!"{n}: {count} HDec constants compared; differences:\n{String.intercalate "\n" bad.toList}"

end LeafFoldCheckSec

noncomputable section

/-! ### Statement repair: R14 with its published determinant clause (g0-mod-galois)

Copied verbatim from `scratch/g0-mod-galois/part_det.lean` (`toRingEquivQ`, `cycQ`, `R14Det`). -/

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- `σ ↦ σ` as ring automorphisms of `ℚ̄`. -/
def toRingEquivQ : PkgI4.GQ →* (PkgI4.Qbar ≃+* PkgI4.Qbar) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The `ℓ`-adic cyclotomic character `χ_ℓ : G_ℚ → ℤ_ℓ^× ⊆ ℚ̄_ℓ^×` (Mathlib's
`cyclotomicCharacter` on `ℚ̄`, as `PkgI4.cyc` on `G_{ℚ_p}`). -/
def cycQ (ℓ : ℕ) [Fact ℓ.Prime] : PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
  (Units.map ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter PkgI4.Qbar ℓ).comp toRingEquivQ)

/-- **R14 with its published determinant clause (leaf; Shimura 1971 Thm 7.14 for `k = 2`,
Deligne 1971 for `k ≥ 2`, Deligne–Serre 1974 for `k = 1`; locators UNVERIFIED).** For a normalized
eigenform `g` of weight `k ≥ 1` with nebentypus, there is a semisimple `ρ_g` attached to `g` with
`det ρ_g = ε · χ_ℓ^{k−1}`, `ε` of finite image (the nebentypus as a Galois character). This is
`HSyn.EigenformRepExists` plus the determinant, which the published statements contain. -/
def R14Det : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k),
    0 < N → 1 ≤ k → PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧
      ∃ ε : PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
        ∀ σ, (ρ.mat σ).det = ((ε σ * cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

/-! ### Statement repair: G10 with concrete hypotheses (g10-odd)

g0-mod-galois's glue Prop `G10Glue` (oddness of `r_ℓ`, inside the glue piece
`GluePieces.modularConstituent`) assumed the `opaque` placeholders `HSyn.T11_RiemannGAGA`,
`HSyn.T12_ArtinComparison` (inert: nothing follows from them). g10-odd's corrected statement
`G10GlueConcrete` assumes the concrete leaves T11(a), T11(b), T35, T5, T26 and R9(b) instead, and
g10-odd proves `G10GlueConcrete` from the smaller glue Prop `ConjTwistNontrivial` (a statement
about `A` alone). The objects `resQ`, `Vb`, `tate`, `Intertwines` are copied verbatim from
g0-mod-galois (`ZInQKernel/Contrib/G9/Statement.lean` has the same copies), `G10Out`,
`G10GlueConcrete`, `ConjTwistNontrivial` verbatim from `scratch/g10-odd/G10Odd.lean` (with the
namespace `ZInQ.LeafPush2` written out). Neither is a hypothesis of `sixContactMin_of_open`: both
are parts of the glue piece `modularConstituent`. -/

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- `e` intertwines the operators `f g` on `V` with `r(g) ⊕ r(g)` on `ℚ̄_ℓ² × ℚ̄_ℓ²`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-- Output of G10: `r` is odd. -/
def G10Out {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) : Prop := r.IsOdd

/-- **G10, corrected statement (GLUE; g10-odd).** `G10Glue` with the inert placeholders replaced
by the concrete leaves its proof uses: T11(a) `T11a_RiemannEnd`, T11(b) `T11b_Rigidity`, T35
`UniformizationExists`, T5 `PkgI2.TorsionStructure`, T26 `PkgI3.TateModuleFree`, R9(b)
`PkgI3.FaltingsTate`. Conclusion unchanged. -/
def G10GlueConcrete : Prop :=
  ZInQ.LeafPush2.T11a_RiemannEnd → ZInQ.LeafPush2.T11b_Rigidity →
  ZInQ.LeafPush2.UniformizationExists → PkgI2.TorsionStructure.{0} →
  PkgI3.TateModuleFree → PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Module.finrank ℤ (PkgI3.AbVar.End A) = 4 → PkgI3.EndDivision A →
    (∃ x y : PkgI3.AbVar.End A, x * y ≠ y * x) →
    Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G10Out r

/-- **The core of G10 (GLUE; g10-odd, which proves `ConjTwistNontrivial → G10Glue` and
`ConjTwistFromLeaves → G10GlueConcrete`).** Complex conjugation does not act trivially by
conjugation on the image of `G_K` in `GL(V_ℓ(A))`. -/
def ConjTwistNontrivial : Prop :=
  PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime], A.dim = 2 → ∀ c : PkgI4.GQ, PkgI4.IsComplexConj c →
    ¬ ∀ σ τ : Field.absoluteGaloisGroup K, resQ K τ = c * resQ K σ * c⁻¹ →
      A.galRep ℓ τ = A.galRep ℓ σ

end G0Galois

/-! ### Statement repair: R10 with its multiplicity-0 clause (g9-derham, finding F1)

`PkgI4.DeRhamComparison` (field `r10`) gives the Hodge–Tate multiplicities `g` at `0` and `−1`
but not `0` at every other weight, which G9's output `HasHTWeights p ρ {0, −1}` needs (g9-derham
F1). The published theorem contains it: the Hodge–Tate decomposition
`ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g` (Tate 1967 for good reduction, Faltings 1988 in general;
UNVERIFIED locators) with Tate's `ℂ_p(j)^{G_F} = 0` for `j ≠ 0`. `R10Weights` is g9-derham's
`G9Bridge.R10Weights` (verbatim; `ZInQKernel/Contrib/G9/Reduction.lean`); the corrected leaf is
`DeRhamComparisonHT`, R10 with the clause, used as the field `r10` of `OpenResearchLeaves`. -/

namespace PkgI4

/-- g9-derham's missing clause of R10: every Hodge–Tate weight other than `0`, `−1` of `V_p(A)`
has multiplicity `0`. -/
def R10Weights : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (w : ℤ), w ≠ 0 → w ≠ -1 → PkgI4.htMultOver p (A.galRep p) w = 0

/-- **I4-L0 corrected (R10 with the multiplicity-0 clause; leaf).** For an abelian variety `A`
of dimension `g` over a finite extension `F` of `ℚ_p`, `V_p(A)` is de Rham, with Hodge–Tate
weights `0` and `−1` each of multiplicity `g`, and multiplicity `0` at every other weight
(`DeRhamComparison` and `R10Weights` in one statement; references as for `DeRhamComparison`, plus
the Hodge–Tate decomposition, Tate 1967, Faltings 1988, UNVERIFIED locators). -/
def DeRhamComparisonHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F),
    (∀ g : ℕ, A.dim = (g : WithBot ℕ∞) →
      IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
        htMultOver p (A.galRep p) (-1) = g) ∧
    ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0

theorem deRhamComparison_of_HT (h : DeRhamComparisonHT) : DeRhamComparison := by
  intro p _ F _ _ _ A g hg
  exact (h p F A).1 g hg

theorem r10Weights_of_HT (h : DeRhamComparisonHT) : R10Weights := by
  intro p _ F _ _ _ A w h0 h1
  exact (h p F A).2 w h0 h1

/-- The corrected R10 is the conjunction of the old field and the missing clause. -/
theorem deRhamComparisonHT_iff : DeRhamComparisonHT ↔ DeRhamComparison ∧ R10Weights := by
  refine ⟨fun h => ⟨deRhamComparison_of_HT h, r10Weights_of_HT h⟩, fun ⟨h, hw⟩ => ?_⟩
  intro p _ F _ _ _ A
  exact ⟨fun g hg => h p F A g hg, fun w h0 h1 => hw p F A w h0 h1⟩

end PkgI4

namespace HSyn

/-! ### The closed leaves (leaf-fold)

Each bundle field below is now a theorem, from a closed proof in `ZInQKernel/Contrib/` (or, for
T2, t-brauer-purity's proof copied above). The `#hdec_same` lines after the bundles check that
the field's Prop is the Contrib theorem's Prop verbatim. -/

/-- T2, Abhyankar's lemma, DVR form (t-brauer-purity; proof copied above). -/
theorem t2_proved : PkgI2.AbhyankarDVR.{0} := TBrauerPurity.abhyankarDVR

/-- T15, `#H²(G_{ℚ_p}, ℤ/2) = #H²(G_ℝ, ℤ/2) = 2` on cochains (t1415-tc, from Tau Ceti). -/
theorem t15_proved : PkgI6.LocalH2CardC := ZInQ.Contrib.BrauerT14T15.localH2CardC

/-- T16(a), local Kronecker–Weber for `ℚ_p` (lkw, from Tau Ceti's local class field theory). -/
theorem t16a_proved : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p :=
  ZInQ.Contrib.localKroneckerWeber

/-- T17, Kronecker–Weber for cyclic `L/ℚ` (kw-new, from Tau Ceti's `kroneckerWeber`). -/
theorem t17_proved : TSkolemKW.KW.KroneckerWeberCyclic :=
  ZInQ.Contrib.KroneckerWeber.kroneckerWeberCyclic

/-- T17 in its original (pre-leaf-adopt3) form `HSyn.KroneckerWeber` (kw-new restates it
verbatim as `ZInQ.Contrib.KroneckerWeber.HSynKroneckerWeber`). -/
theorem kroneckerWeber_proved : KroneckerWeber := ZInQ.Contrib.KroneckerWeber.hSynKroneckerWeber

/-- T18, Chebotarev, existence form (cheb-bridge, from Tau Ceti's Chebotarev density theorem). -/
theorem t18_proved : PkgI6.ChebotarevExists := ZInQ.Contrib.chebotarevExists

/-- T18 in its density form `HSyn.FrobeniusDense` (cheb-bridge restates it verbatim, with the
`HSyn` definitions it uses, as `ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense`). -/
theorem frobeniusDense_proved : FrobeniusDense := ZInQ.Contrib.frobeniusDense

/-- T20, Hilbert's different formula, global form (diff-bridge, from Tau Ceti). -/
theorem t20_proved : GlueConductor.HilbertDifferentFormula :=
  ZInQ.Contrib.Different.hilbertDifferentFormula

/-- T21, Serre's different bound, global form (diff-bridge, from Tau Ceti's wild bound). -/
theorem t21_proved : GlueConductor.SerreDifferentBound := ZInQ.Contrib.Different.serreDifferentBound

/-- T25, a normalized eigenform has the eigenvalues of a newform (t25-newform, from Tau Ceti). -/
theorem t25_proved : PkgI4.NewformOfEigenform := T25.newformOfEigenform_leaf

/-- T30, the local square-root criterion (lkw: from T16(a); the file's own derivation
`T30.leafSqrtCrit_of_t16a` gives the same). -/
theorem t30_proved : GlueDescent.B2Q.LeafSqrtCrit := ZInQ.Contrib.leafSqrtCrit

/-- T30 by this file's own derivation from T16(a). -/
theorem t30_proved' : GlueDescent.B2Q.LeafSqrtCrit := T30.leafSqrtCrit_of_t16a t16a_proved

/-- T31, unramified outside the primes of a finite set (t31-unram, from Tau Ceti). -/
theorem t31_proved : GlueDescent.B2Q.LeafUnramified := ZInQ.Contrib.T31.leafUnramified

/-- T14(a′), T14(b′) from the Kummer case of the second inequality of global class field theory
(t1415-tc: `KummerIndexBound`, over Tau Ceti's idele class groups; Milne, *Class Field Theory*,
VII §6). Not used below: T14(a′), T14(b′) stay open leaves; this is the reduction t1415-tc found. -/
theorem t14_of_kummerIndexBound (h : ZInQ.Contrib.BrauerT14T15.KummerIndexBound) :
    PkgI6.BrauerHasse2C ∧ PkgI6.BrauerReciprocity2C :=
  ⟨ZInQ.Contrib.BrauerT14T15.brauerHasse2C_of_kummerIndexBound h,
    ZInQ.Contrib.BrauerT14T15.brauerReciprocity2C_of_kummerIndexBound h⟩

/-- R14 from its corrected form `G0Galois.R14Det` (drop the determinant clause). -/
theorem eigenformRepExists_of_r14Det (h : G0Galois.R14Det) : EigenformRepExists := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hss, hatt, -⟩ := h ℓ ιC ιL N k χ g hN hk hg
  exact ⟨⟨ρ.toHom, ρ.continuous_toHom⟩, hss, hatt⟩

/-- **The research-level leaves still open** (leaf-fold, 2026-11-13): the 26 fields of
`ResearchLeaves` (the note's 23 research-level leaves; none is proved), with two fields replaced by the published, corrected statements:
* `r10 : PkgI4.DeRhamComparisonHT`: R10 with the multiplicity-0 clause (g9-derham F1);
* `r14 : G0Galois.R14Det`: R14 with the determinant `det ρ_g = ε χ_ℓ^{k−1}` (g0-mod-galois).
Both imply the old fields (`PkgI4.deRhamComparison_of_HT`, `eigenformRepExists_of_r14Det`).
Still `opaque` placeholders: `r1an` (R1(b)) and `r17` (R17). -/
structure OpenResearchLeaves : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  r1an : R01b_ComplexUniformization
  r1rec : LeafQM.AV.R1rec
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  /-- R10 corrected: with multiplicity `0` at every weight other than `0`, `−1` (g9-derham). -/
  r10 : PkgI4.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  /-- R14 corrected: with the determinant clause (g0-mod-galois's `R14Det`). -/
  r14 : G0Galois.R14Det
  r15 : DeligneSerreConseq
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  r17 : R17_Carayol
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  h5 : LeafAdopt.H5

/-- **The textbook leaves still open** (leaf-fold, 2026-11-13): `TextbookLeaves` without the nine
fields now proved (`t2`, `t15`, `t16a`, `t17`, `t18`, `t20`, `t21`, `t25`, `t31`). -/
structure OpenTextbookLeaves : Prop where
  t1 : PkgI2.PurityBranchLocus.{0}
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10Etale.T10_TateDuality
  t11a : ZInQ.LeafPush2.T11a_RiemannEnd
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t14a : PkgI6.BrauerHasse2C
  t14b : PkgI6.BrauerReciprocity2C
  t16b : PkgI6.LocalReciprocityUpper
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t28 : PkgI1.IgusaClebschSeparation
  t29a : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29a_DivisionNormalizer p
  t29b : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29b_SplitNormalizer p
  t33 : LeafModCurves.JacobianExists ℚ
  t34 : LeafModCurves.DimJ1Genus
  t35 : ZInQ.LeafPush2.UniformizationExists
  x1 : X1Belyi.X1Leaves
  t41 : ZInQ.H5Neron.NeronModelExists

theorem researchLeaves_of_open (r : OpenResearchLeaves) : ResearchLeaves where
  r1r2 := r.r1r2
  r1an := r.r1an
  r1rec := r.r1rec
  r3 := r.r3
  r4 := r.r4
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r7b := r.r7b
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  r10 := PkgI4.deRhamComparison_of_HT r.r10
  r11r12 := r.r11r12
  r13 := r.r13
  r14 := eigenformRepExists_of_r14Det r.r14
  r15 := r.r15
  r16 := r.r16
  r17 := r.r17
  r18 := r.r18
  r19 := r.r19
  r20 := r.r20
  r21 := r.r21
  r22 := r.r22
  h5 := r.h5

theorem textbookLeaves_of_open (t : OpenTextbookLeaves) : TextbookLeaves where
  t1 := t.t1
  t2 := t2_proved
  t3 := t.t3
  t4 := t.t4
  t5 := t.t5
  t6 := t.t6
  t7 := t.t7
  t8 := t.t8
  t9 := t.t9
  t10 := t.t10
  t11a := t.t11a
  t11b := t.t11b
  t14a := t.t14a
  t14b := t.t14b
  t15 := t15_proved
  t16a := t16a_proved
  t16b := t.t16b
  t17 := t17_proved
  t18 := t18_proved
  t20 := t20_proved
  t21 := t21_proved
  t23 := t.t23
  t24 := t.t24
  t25 := t25_proved
  t26 := t.t26
  t27 := t.t27
  t28 := t.t28
  t29a := t.t29a
  t29b := t.t29b
  t31 := t31_proved
  t33 := t.t33
  t34 := t.t34
  t35 := t.t35
  x1 := t.x1
  t41 := t.t41

/-- **G0 with only the open leaves** (leaf-fold, 2026-11-13; no `sorry`, standard axioms).
`SixContactMin` follows from the open leaves and the ten glue pieces.

Open research-level leaves (all 23 of the note's R1-R22 and H5, in 26 fields; none is proved):
R1(a,c,d)+R2+R5-on-`X₆` (`r1r2`), R1(b) (`r1an`, opaque), R1(d) reciprocity (`r1rec`), R3, R4,
R5(ii) (`r5`), R5(i) (`r5count`), R6, R7(a), R7(b), R8, R9(a), R9(b), **R10 corrected**
(`PkgI4.DeRhamComparisonHT`), R11+R12 (`r11r12`), R13, **R14 corrected** (`G0Galois.R14Det`), R15,
R16, R17 (opaque), R18, R19, R20, R21, R22, H5.

Open textbook leaves (26 fields; `x1` bundles T36-T40): T1, T3, T4, T5, T6, T7, T8,
T9, T10, T11(a), T11(b), T14(a′), T14(b′), T16(b), T23, T24, T26, T27, T28, T29(a), T29(b), T33,
T34, T35, T36-T40 (`x1`), T41.

Proved (no longer hypotheses): T2 (`t2_proved`), T13, T15 (`t15_proved`), T16(a)
(`t16a_proved`), T17 (`t17_proved`), T18 (`t18_proved`), T19, T20 and T21 in global form
(`t20_proved`, `t21_proved`), T22, T25 (`t25_proved`), T30, T31 (`t31_proved`). -/
theorem sixContactMin_of_open (r : OpenResearchLeaves) (t : OpenTextbookLeaves)
    (gp : GluePieces) : ZInQ.SixContactMin :=
  sixContactMin_of_leaves (researchLeaves_of_open r) (textbookLeaves_of_open t) gp

end HSyn

end

/-! ### Verbatim checks: each closed field against its Contrib Prop (leaf-fold)

`HDec.X` is this file's statement, `X` the one the Contrib theorem proves (in
`ZInQKernel/HDecomp/`). -/

#hdec_same HDec.PkgI6.LocalH2CardC
#hdec_same HDec.PkgI6.LocalKroneckerWeber
#hdec_same HDec.TSkolemKW.KW.KroneckerWeberCyclic
#hdec_same HDec.PkgI6.ChebotarevExists
#hdec_same HDec.GlueConductor.HilbertDifferentFormula
#hdec_same HDec.GlueConductor.SerreDifferentBound
#hdec_same HDec.PkgI4.NewformOfEigenform
#hdec_same HDec.GlueDescent.B2Q.LeafSqrtCrit
#hdec_same HDec.GlueDescent.B2Q.LeafUnramified
#hdec_same HDec.PkgI6.BrauerHasse2C
#hdec_same HDec.PkgI6.BrauerReciprocity2C
