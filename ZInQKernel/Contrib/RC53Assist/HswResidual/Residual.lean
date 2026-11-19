import ZInQKernel.Contrib.CloudB3RC53.Hsw.ShapeDerivTie
import ZInQKernel.Contrib.CloudB3RC53.Duality.LocalKummer
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison

/-!
# Residual nondegeneracy of the derivative switch

The coefficient field throughout this file is `ZMod 2`. The ground local field in
`MilneCor23Residual` has characteristic zero; this is not a characteristic-zero
coefficient statement.

Source: J. S. Milne, Arithmetic Duality Theorems, second edition (2006),
Chapter I, Section 2, Corollary 2.3, printed page 28 (PDF page 36),
https://www.jmilne.org/math/Books/ADTnot.pdf.
The source says: "Let M be a finitely generated G-module whose torsion
subgroup has order prime to char(K). Then cup-product defines isomorphisms"
`H^r(G, M^D) -> H^(2-r)(G, M)^*` for `r >= 1`, where
`M^D = Hom(M, (K^s)^*)`. It also states that `H^1(G, M)` and
`H^1(G, M^D)` are finite. In this edition the result is Corollary 2.3,
not Theorem 2.3. The finite, exponent-two, degree-one specialization is
recorded below as an explicit proposition, not as an added axiom.

The manuscript cites this source at lines 3442-3444. Its transported derivative
pairing occurs at lines 2816-2820 and 4854-4890. The existing Kummer print
concerns adjointness of the Kummer map and is not the finite-module
nondegeneracy statement. The cup product used below is the existing `cupH`.

The restriction of the cone trace to the switch-place summand must induce
an isomorphism on local degree-two cohomology. Killing coboundaries alone
is not sufficient: the zero trace kills coboundaries and has a zero residue
form. This arithmetic trace condition is kept separate from the printed
finite local duality and from the proved cochain identification.

Source reading: AI-READ. The printed proposition remains an explicit input.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HswResidual

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.CloudB3RC53.GenuineInst
open ZInQ.Contrib.CloudB3RC53.Hsw

section TraceCup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M N T : Type}
  [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]
  [AddCommGroup N] [Module (ZMod 2) N] [DistribMulAction G N]
  [SMulCommClass G (ZMod 2) N] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul G N]
  [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction G T]
  [SMulCommClass G (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul G T]

/-- The biadditive map underlying a bilinear coefficient pairing. -/
abbrev biadditive (β : M →ₗ[ZMod 2] N →ₗ[ZMod 2] T) : M →+ N →+ T where
  toFun x := (β x).toAddMonoidHom
  map_zero' := by ext y; simp
  map_add' x x' := by ext y; simp

/-- A local degree-two trace on continuous two-cocycles. -/
def traceZ2 (tr2 : (contCochains (ZMod 2) G T).X 2 →ₗ[ZMod 2] ZMod 2) :
    TauCeti.ContCohomology.Z2 G T →+ ZMod 2 where
  toFun z := tr2 (mkCochain2 (z : G × G → T)
    (TauCeti.ContCohomology.mem_Z2_iff.mp z.2).1)
  map_zero' := by
    change tr2 0 = 0
    exact map_zero tr2
  map_add' z z' := by
    have hadd : mkCochain2 (k := ZMod 2) ((z + z' : TauCeti.ContCohomology.Z2 G T) : G × G → T)
        (TauCeti.ContCohomology.mem_Z2_iff.mp (z + z').2).1 =
        mkCochain2 (k := ZMod 2) (z : G × G → T) (TauCeti.ContCohomology.mem_Z2_iff.mp z.2).1 +
          mkCochain2 (k := ZMod 2) (z' : G × G → T) (TauCeti.ContCohomology.mem_Z2_iff.mp z'.2).1 := by
      apply contCochains_ext
      intro v
      rfl
    rw [hadd, map_add]

/-- The induced trace on explicit continuous degree-two cohomology. -/
def traceH2 (tr2 : (contCochains (ZMod 2) G T).X 2 →ₗ[ZMod 2] ZMod 2)
    (htr2 : ∀ c, tr2 (((contCochains (ZMod 2) G T).d 1 2).hom c) = 0) :
    TauCeti.ContCohomology.H2 G T →+ ZMod 2 :=
  QuotientAddGroup.lift _ (traceZ2 tr2) (by
    intro z hz
    rw [AddSubgroup.mem_addSubgroupOf] at hz
    obtain ⟨c, hc, hcz⟩ := TauCeti.ContCohomology.mem_B2_iff.mp hz
    have hd : mkCochain2 (z : G × G → T)
        (TauCeti.ContCohomology.mem_Z2_iff.mp z.2).1 =
        ((contCochains (ZMod 2) G T).d 1 2).hom (mkCochain1 c hc) := by
      apply contCochains_ext
      intro v
      have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
      rw [hv, contFun_mkCochain2, contFun_d12]
      change (z : G × G → T) (v 0, v 1) =
        v 0 • c (v 1) - c (v 0 * v 1) + c (v 0)
      exact (congrFun hcz (v 0, v 1)).symm
    change tr2 (mkCochain2 (z : G × G → T) _) = 0
    rw [hd]
    exact htr2 _)

/-- The induced trace evaluated on a cocycle class. -/
theorem traceH2_mk
    (tr2 : (contCochains (ZMod 2) G T).X 2 →ₗ[ZMod 2] ZMod 2)
    (htr2 : ∀ c, tr2 (((contCochains (ZMod 2) G T).d 1 2).hom c) = 0)
    (z : TauCeti.ContCohomology.Z2 G T) :
    traceH2 tr2 htr2 (TauCeti.ContCohomology.H2pi G T z) =
      tr2 (mkCochain2 (z : G × G → T)
        (TauCeti.ContCohomology.mem_Z2_iff.mp z.2).1) :=
  rfl

/-- Cup product followed by the induced local trace, on genuine continuous `H^1`. -/
def localCupTrace (β : M →ₗ[ZMod 2] N →ₗ[ZMod 2] T)
    (hβ : ∀ (g : G) x y, β (g • x) (g • y) = g • β x y)
    (tr2 : (contCochains (ZMod 2) G T).X 2 →ₗ[ZMod 2] ZMod 2)
    (htr2 : ∀ c, tr2 (((contCochains (ZMod 2) G T).d 1 2).hom c) = 0) :
    TauCeti.ContCohomology.H1 G M →+
      TauCeti.ContCohomology.H1 G N →+ ZMod 2 :=
  (AddMonoidHom.compHom (traceH2 tr2 htr2)).comp
    (ZInQ.Contrib.CloudB3RC53.Duality.cupH (biadditive β) hβ)

/-- Identification of the two continuous cup products on cocycle representatives. -/
theorem localCupTrace_cocycles (β : M →ₗ[ZMod 2] N →ₗ[ZMod 2] T)
    (hβ : ∀ (g : G) x y, β (g • x) (g • y) = g • β x y)
    (tr2 : (contCochains (ZMod 2) G T).X 2 →ₗ[ZMod 2] ZMod 2)
    (htr2 : ∀ c, tr2 (((contCochains (ZMod 2) G T).d 1 2).hom c) = 0)
    (z : LinearMap.ker ((contCochains (ZMod 2) G M).d 1 2).hom)
    (w : LinearMap.ker ((contCochains (ZMod 2) G N).d 1 2).hom) :
    localCupTrace β hβ tr2 htr2 (kerToH1 z) (kerToH1 w) =
      tr2 (contCup β (continuous_pairing β) 1 1 2 rfl z.1 w.1) := by
  let z' : TauCeti.ContCohomology.Z1 G M :=
    ⟨fun g => contFun z.1 (fun _ => g), mem_Z1_of_d_eq_zero z.1 z.2⟩
  let w' : TauCeti.ContCohomology.Z1 G N :=
    ⟨fun g => contFun w.1 (fun _ => g), mem_Z1_of_d_eq_zero w.1 w.2⟩
  change traceH2 tr2 htr2
    (ZInQ.Contrib.CloudB3RC53.Duality.cupH (biadditive β) hβ
      (TauCeti.ContCohomology.H1pi G M z') (TauCeti.ContCohomology.H1pi G N w')) = _
  calc
    _ = traceH2 tr2 htr2 (TauCeti.ContCohomology.H2pi G T
        (ZInQ.Contrib.CloudB3RC53.Duality.cupZ (biadditive β) hβ z' w')) :=
      congrArg (traceH2 tr2 htr2)
        (ZInQ.Contrib.CloudB3RC53.Duality.cupH_mk (biadditive β) hβ z' w')
    _ = tr2 (mkCochain2
        ((ZInQ.Contrib.CloudB3RC53.Duality.cupZ (biadditive β) hβ z' w') : G × G → T)
        (TauCeti.ContCohomology.mem_Z2_iff.mp
          (ZInQ.Contrib.CloudB3RC53.Duality.cupZ (biadditive β) hβ z' w').2).1) :=
      traceH2_mk tr2 htr2 _
    _ = _ := by
      congr 1
      apply contCochains_ext
      intro v
      change β (contFun z.1 (fun _ => v 0)) (v 0 • contFun w.1 (fun _ => v 1)) =
        cupFun β 1 1 2 rfl (cFun z.1) (cFun w.1) v
      rw [cupFun_apply]
      have h1 : (fun i : Fin 1 => v (Fin.castLE (by omega) i)) = fun _ => v 0 := by
        funext i
        rw [Subsingleton.elim i 0]
        rfl
      have h2 : (fun j : Fin 1 => v ⟨1 + j, by omega⟩) = fun _ => v 1 := by
        funext j
        rw [Subsingleton.elim j 0]
        rfl
      have h3 : headProd 1 2 (by omega) v = v 0 := by
        change Fin.partialProd v (Fin.succ 0) = v 0
        rw [Fin.partialProd_succ, Fin.castSucc_zero, Fin.partialProd_zero, one_mul]
      rw [h1, h2, h3]

end TraceCup

/-- **PRINT: finite residual specialization of Milne I, Corollary 2.3.**
For finite exponent-two modules over a nonarchimedean local field of characteristic
zero, a perfect equivariant coefficient pairing into a trivial rank-one module
identifies either module with the Tate dual of the other. A local trace inducing
`H^2(G_L,T) = F_2` identifies the finite, two-torsion Pontryagin dual with its
`F_2`-valued additive dual. Hence both degree-one cup adjoints are bijective.
Locator: second edition, I Section 2, Corollary 2.3, printed p. 28, PDF p. 36.
This definition records the proposition and does not assert a proof of it. -/
def MilneCor23Residual : Prop :=
  ∀ (L : Type) [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (M N T : Type)
    [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (Field.absoluteGaloisGroup L) M]
    [SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup L) M]
    [Finite M]
    [AddCommGroup N] [Module (ZMod 2) N] [DistribMulAction (Field.absoluteGaloisGroup L) N]
    [SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) N]
    [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul (Field.absoluteGaloisGroup L) N]
    [Finite N]
    [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (Field.absoluteGaloisGroup L) T]
    [SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) T]
    [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (Field.absoluteGaloisGroup L) T]
    (_eT : T ≃ₗ[ZMod 2] ZMod 2)
    (_hT : ∀ (g : Field.absoluteGaloisGroup L) (t : T), g • t = t)
    (β : M →ₗ[ZMod 2] N →ₗ[ZMod 2] T)
    (hβ : ∀ (g : Field.absoluteGaloisGroup L) x y, β (g • x) (g • y) = g • β x y),
    Function.Bijective β → Function.Bijective β.flip →
    ∀ (tr2 : (contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).X 2 →ₗ[ZMod 2] ZMod 2)
      (htr2 : ∀ c, tr2 (((contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).d 1 2).hom c) = 0),
      InducesIsoH2 (C := natCx (contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T)) tr2 →
      Finite (TauCeti.ContCohomology.H1 (Field.absoluteGaloisGroup L) M) ∧
      Finite (TauCeti.ContCohomology.H1 (Field.absoluteGaloisGroup L) N) ∧
      Function.Bijective (localCupTrace β hβ tr2 htr2) ∧
      Function.Bijective (localCupTrace β hβ tr2 htr2).flip

section WeilCoefficients

variable {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- **Perfectness of a residual Weil coefficient pairing**, allowing distinct
coordinate identifications in its two slots, as in conjugate duality. -/
theorem coefficient_perfect_of_weil
    (e1 e2 : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) (eW : W ≃ₗ[ZMod 2] ZMod 2)
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hβ : ∀ x y, eW (β x y) = weil (e1 x) (e2 y)) :
    Function.Bijective β ∧ Function.Bijective β.flip := by
  have : FiniteDimensional (ZMod 2) V := e1.symm.finiteDimensional
  have key (a b : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
      (hB : ∀ x y, eW (B x y) = weil (a x) (b y)) : Function.Bijective B := by
    let P : LinearMap.BilinForm (ZMod 2) V := B.compr₂ eW.toLinearMap
    have hinj : Function.Injective P := by
      refine (injective_iff_map_eq_zero P).mpr fun x hx => ?_
      apply a.injective
      rw [map_zero]
      funext i
      fin_cases i
      · have he := hB x (b.symm (Pi.single 1 1))
        rw [b.apply_symm_apply] at he
        have h0 : weil (a x) (Pi.single 1 1) = 0 :=
          he.symm.trans (LinearMap.congr_fun hx (b.symm (Pi.single 1 1)))
        simpa [weil_apply] using h0
      · have he := hB x (b.symm (Pi.single 0 1))
        rw [b.apply_symm_apply] at he
        have h0 : weil (a x) (Pi.single 0 1) = 0 :=
          he.symm.trans (LinearMap.congr_fun hx (b.symm (Pi.single 0 1)))
        have hn : -(a x 1) = 0 := by simpa [weil_apply] using h0
        exact neg_eq_zero.mp hn
    have hdim : Module.finrank (ZMod 2) V =
        Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V) := Subspace.dual_finrank_eq.symm
    have hsurj : Function.Surjective P :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
    constructor
    · intro x y hxy
      apply hinj
      ext z
      exact congrArg eW (LinearMap.congr_fun hxy z)
    · intro f
      obtain ⟨x, hx⟩ := hsurj (eW.toLinearMap ∘ₗ f)
      refine ⟨x, LinearMap.ext fun y => eW.injective ?_⟩
      exact LinearMap.congr_fun hx y
  have hneg : ∀ c : ZMod 2, -c = c := CharTwo.neg_eq
  refine ⟨key e1 e2 β hβ, key e2 e1 β.flip ?_⟩
  intro x y
  change eW (β y x) = weil (e2 x) (e1 y)
  rw [hβ, weil_swap, hneg]

end WeilCoefficients

section KummerBrauer

/-- The inclusion of `F_2` into `Q/Z`, normalized by `1 |-> 1/2`. -/
def f2ToQmodZ : ZMod 2 →+ AddCircle (1 : ℚ) :=
  ZMod.lift 2 ⟨AddMonoidHom.mk' (fun j : ℤ => (↑((j : ℚ) / (2 : ℚ)) : AddCircle (1 : ℚ)))
    (by intro i j; simp [add_div]), by norm_num⟩

/-- The standard inclusion of `F_2` into `Q/Z` is injective. -/
theorem f2ToQmodZ_injective : Function.Injective f2ToQmodZ := by
  have hcast (i : ℤ) : f2ToQmodZ (i : ZMod 2) =
      (↑((i : ℚ) / (2 : ℚ)) : AddCircle (1 : ℚ)) := by
    simp [f2ToQmodZ]
  have hval (j : ZMod 2) : f2ToQmodZ j = (↑((j.val : ℚ) / (2 : ℚ)) : AddCircle (1 : ℚ)) := by
    have hnat : f2ToQmodZ (j.val : ZMod 2) = (↑((j.val : ℚ) / (2 : ℚ)) : AddCircle (1 : ℚ)) := by
      simpa only [Int.cast_natCast] using hcast (j.val : ℤ)
    simpa only [ZMod.natCast_zmod_val] using hnat
  intro x y hxy
  rw [hval x, hval y] at hxy
  have hx : (x.val : ℚ) / 2 ∈ Set.Ico 0 (0 + (1 : ℚ)) :=
    ⟨by positivity, by
      rw [zero_add, div_lt_one (by norm_num : (0 : ℚ) < 2)]
      exact_mod_cast x.val_lt⟩
  have hy : (y.val : ℚ) / 2 ∈ Set.Ico 0 (0 + (1 : ℚ)) :=
    ⟨by positivity, by
      rw [zero_add, div_lt_one (by norm_num : (0 : ℚ) < 2)]
      exact_mod_cast y.val_lt⟩
  have hq := (AddCircle.coe_eq_coe_iff_of_mem_Ico hx hy).mp hxy
  apply ZMod.val_injective 2
  exact_mod_cast (div_left_inj' (by norm_num : (2 : ℚ) ≠ 0)).mp hq

/-- **A23 comparison input**, stated for the existing natural Kummer-to-Brauer map.
The map `H^2(G_L,mu_2) -> Br(L)` is injective and its image is exactly `Br(L)[2]`.
This is a named proposition, not a proof of the comparison. -/
def KummerBrauerComparisonF2 (L : Type) [Field L] [CharZero L] : Prop :=
  Function.Injective (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := L) 2) ∧
    (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := L) 2).range =
      AddSubgroup.torsionBy (TauCeti.ClassFieldTheory.Br L) 2

variable {L : Type} [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
  [DistribMulAction (Field.absoluteGaloisGroup L) T]
  [SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (Field.absoluteGaloisGroup L) T]
  (eμ : T ≃+ TauCeti.KummerCoeff L 2)
  (heμ : ∀ (g : TauCeti.AbsoluteGaloisGroup L) (t : T),
    eμ ((TauCeti.absoluteGaloisGroupRestrictEquiv L).symm g • t) = g • eμ t)

/-- The proved continuous cohomology transport for the coefficient identification `T = mu_2`.
It uses the existing restriction isomorphism between algebraic and separable closures. -/
def kummerH2Transport :
    TauCeti.ContCohomology.H2 (Field.absoluteGaloisGroup L) T ≃+
      TauCeti.ContCohomology.H2 (TauCeti.AbsoluteGaloisGroup L) (TauCeti.KummerCoeff L 2) :=
  TauCeti.ContCohomology.explicitMap2Equiv (Field.absoluteGaloisGroup L) T
    (TauCeti.AbsoluteGaloisGroup L) (TauCeti.KummerCoeff L 2)
    (TauCeti.absoluteGaloisGroupRestrictEquiv L).symm eμ
    continuous_of_discreteTopology continuous_of_discreteTopology heμ

/-- The local cochain trace agrees with the genuine Brauer invariant on two-cocycles. -/
def LocalTraceMatchesInvariant
    (tr2 : (contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).X 2 →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ c : LinearMap.ker ((contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).d 2 3).hom,
    f2ToQmodZ (tr2 c.1) = TauCeti.ClassFieldTheory.invMap L
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := L) 2
        (kummerH2Transport eμ heμ (kerToH2 c)))

/-- **The trace isomorphism from the A23 comparison and invariant identification.**
This proves only the transport and normalization consequence. It does not prove
`KummerBrauerComparisonF2`, which stays an explicit input. -/
theorem inducesIsoH2_of_KummerBrauer (hKB : KummerBrauerComparisonF2 L)
    (tr2 : (contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).X 2 →ₗ[ZMod 2] ZMod 2)
    (hmatch : LocalTraceMatchesInvariant eμ heμ tr2) :
    InducesIsoH2 (C := natCx (contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T)) tr2 := by
  let E := kummerH2Transport eμ heμ
  constructor
  · intro c hc htc
    let cc : LinearMap.ker ((contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).d 2 3).hom :=
      ⟨c, hc⟩
    have hzero : kerToH2 cc = 0 := by
      apply E.injective
      apply hKB.1
      apply (TauCeti.ClassFieldTheory.invMap L).injective
      have h := hmatch cc
      have htc' : tr2 cc.1 = 0 := htc
      rw [htc', map_zero] at h
      simpa only [map_zero] using h.symm
    exact (kerToH2_eq_zero_iff cc).mp hzero
  · let b := (TauCeti.ClassFieldTheory.invMap L).symm (f2ToQmodZ 1)
    have hb0 : (2 : ℕ) • b = 0 := by
      apply (TauCeti.ClassFieldTheory.invMap L).injective
      change TauCeti.ClassFieldTheory.invMap L ((2 : ℕ) •
        (TauCeti.ClassFieldTheory.invMap L).symm (f2ToQmodZ 1)) =
        TauCeti.ClassFieldTheory.invMap L 0
      rw [map_nsmul, AddEquiv.apply_symm_apply, ← map_nsmul,
        show (2 : ℕ) • (1 : ZMod 2) = 0 from by decide, map_zero, map_zero]
    have hb : b ∈ (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := L) 2).range := by
      rw [hKB.2]
      exact AddSubgroup.torsionBy.nsmul_iff.mpr hb0
    obtain ⟨a, ha⟩ := hb
    obtain ⟨c, hc⟩ := kerToH2_surjective (k := ZMod 2)
      (G := Field.absoluteGaloisGroup L) (M := T) (E.symm a)
    have hm := hmatch c
    change f2ToQmodZ (tr2 c.1) =
      TauCeti.ClassFieldTheory.invMap L
        (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := L) 2 (E (kerToH2 c))) at hm
    rw [hc, E.apply_symm_apply, ha] at hm
    have hn : tr2 c.1 = 1 := f2ToQmodZ_injective
      (hm.trans ((TauCeti.ClassFieldTheory.invMap L).apply_symm_apply (f2ToQmodZ 1)))
    exact ⟨c.1, c.2, hn⟩

end KummerBrauer

section Switch

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] [DecidableEq (Places K S)]
  {T : Type} [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

/-- Restriction of the cone trace to the local degree-two summand at `q`. -/
def residualTraceAt (X : GenuineSwitch K S (ZMod 2) M)
    (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) x y, β (g • x) (g • y) = g • β x y)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (q : Places K S) :
    (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).X 2 →ₗ[ZMod 2] ZMod 2 :=
  tr ∘ₗ locT (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso) ∘ₗ
    LinearMap.single (ZMod 2)
      (fun v : Places K S => (localCx (ZMod 2) (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T v).X 2) q

/-- The restricted trace kills local coboundaries. -/
theorem residualTraceAt_d (X : GenuineSwitch K S (ZMod 2) M)
    (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) x y, β (g • x) (g • y) = g • β x y)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).d 2 3 rfl c) = 0)
    (q : Places K S)
    (c : (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).X 1) :
    residualTraceAt X β hβ Iso tr q
      (((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).d 1 2).hom c) = 0 := by
  have h := tr_locT_d (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso) tr htr (Pi.single q c)
  change tr (locT _ ((piCx (fun v : Places K S =>
    localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v)).d 1 2 rfl (Pi.single q c))) = 0 at h
  erw [piCx_d_single] at h
  exact h

variable (F : DerivFamily (galLv (k := ZMod 2) K S M)) {q : Places K S}
  (hR : RelAt (Gv := fun v : Places K S => Gloc K v.1)
    (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) F.str F.rel q)

/-- The genuine local cocycle read at the switch place. -/
def localCocycle (t : F.Urel.X 1) :
    LinearMap.ker ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) M)).d 1 2).hom :=
  ⟨(t q).1, (hR.rel1 _).mp (t q).2⟩

/-- The coordinate class of a relaxed cocycle is read by its local tame coordinates. -/
theorem gClass_eq_coordAt (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)} (Tc : TameCoordinates (M := ResMod (locMap K S q.1) M) I φ σ)
    (t : F.Urel.X 1) (ht : F.Urel.d 1 2 rfl t = 0) :
    gClass (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi t ht =
      coordAt (Gv := fun v : Places K S => Gloc K v.1)
        (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) q φ σ eM (t q).1 := by
  change descH1 F.Wrel (psi0 (derivHsr F) hR φ σ eM)
    (psi0_d (derivHsr F) hR φ σ eM Tc.hφ Tc.hσ) (cls1 F.Wrel _) = _
  erw [descH1_cls1]
  rfl

/-- A zero local cohomology class gives a zero switch-coordinate class. -/
theorem gClass_eq_zero_of_localClass (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)} (Tc : TameCoordinates (M := ResMod (locMap K S q.1) M) I φ σ)
    (t : F.Urel.X 1) (ht : F.Urel.d 1 2 rfl t = 0)
    (hz : kerToH1 (localCocycle F hR t) = 0) :
    gClass (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi t ht = 0 := by
  obtain ⟨a, ha⟩ := (kerToH1_eq_zero_iff (localCocycle F hR t)).mp hz
  rw [gClass_eq_coordAt F hR φ σ eM Tc t ht]
  change ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) M)).d 0 1).hom a =
    (t q).1 at ha
  rw [← ha]
  exact coordAt_relaxedD (Gv := fun v : Places K S => Gloc K v.1)
    (Mv := fun v : Places K S => ResMod (locMap K S v.1) M) φ σ eM Tc.hφ Tc.hσ a

/-- **Identification of the residue form with the local cup-product pairing.**
Testing the first relaxed cochain against a cocycle supported at `q` leaves only
the `q`-summand of the local cup product. The order of the two arguments is
reversed and there is a minus sign, exactly as in the cone residue formula. -/
theorem resForm_eq_localCupTrace
    (eR : F.Wrel.toCC.homology 1 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))
    (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) x y, β (g • x) (g • y) = g • β x y)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ
      (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) β hβ
      (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR Iso).resE).d 2 3 rfl c) = 0)
    (t : F.Urel.X 1)
    (z : LinearMap.ker
      ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) M)).d 1 2).hom) :
    resForm (derivSwitch F eR).toQuasi (piCx (derivSwitch F eR).US)
      (piMap (derivSwitch F eR).φ)
      (galoisPairData K S (ZMod 2) β hβ (derivSwitch F eR).ΔS (derivSwitch F eR).ΔR Iso)
      tr t (relSingle F q (hrelq_of_relAt F hR) z.1 z.2) =
    -localCupTrace (resPairing (ZMod 2) (GKS K S) β (locMap K S q.1))
      (fun g x y => hβ (locMap K S q.1 g) x y)
      (residualTraceAt (derivSwitch F eR) β hβ Iso tr q)
      (residualTraceAt_d (derivSwitch F eR) β hβ Iso tr htr q)
      (kerToH1 z) (kerToH1 (localCocycle F hR t)) := by
  let X := derivSwitch F eR
  let Q := galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso
  let βq := resPairing (ZMod 2) (GKS K S) β (locMap K S q.1)
  let u := relSingle F q (hrelq_of_relAt F hR) z.1 z.2
  let C := contCup βq (continuous_pairing βq) 1 1 2 rfl z.1 (t q).1
  have hcup : Q.cupL.P 1 1 2 rfl (X.toQuasi.D.ι.f 1 1 rfl u)
      (X.toQuasi.D.ι.f 1 1 rfl t) = Pi.single q C := by
    funext v
    by_cases hv : v = q
    · subst v
      have hself : (relSingle F q (hrelq_of_relAt F hR) z.1 z.2 q).1 = z.1 :=
        relSingle_apply_self F q (hrelq_of_relAt F hR) z.1 z.2
      have hsingle : (Pi.single q C : Q.EL.X 2) q = C :=
        Pi.single_eq_same (M := fun v : Places K S =>
          (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) T v).X 2) q C
      change contCup βq (continuous_pairing βq) 1 1 2 rfl
        (relSingle F q (hrelq_of_relAt F hR) z.1 z.2 q).1 (t q).1 =
          (Pi.single q C : Q.EL.X 2) q
      exact (congrArg (fun a => contCup βq (continuous_pairing βq) 1 1 2 rfl a (t q).1)
        hself).trans hsingle.symm
    · have hne : (relSingle F q (hrelq_of_relAt F hR) z.1 z.2 v).1 =
          (0 : (galLv (k := ZMod 2) K S M v).X 1) :=
        congrArg (fun a : ((F.rel v).S 1 : Type) => a.1)
          (relSingle_apply_ne F q (hrelq_of_relAt F hR) z.1 z.2 v hv)
      change (localPair (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl
          (relSingle F q (hrelq_of_relAt F hR) z.1 z.2 v).1 (t v).1 =
          (Pi.single q C : Q.EL.X 2) v
      calc
        _ = (localPair (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl
            0 (t v).1 := congrArg (fun a =>
              (localPair (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
                (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl a (t v).1) hne
        _ = 0 := LinearMap.map_zero₂ _ _
        _ = _ := (Pi.single_eq_of_ne (M := fun v : Places K S =>
          (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) T v).X 2) hv C).symm
  have hres : resForm X.toQuasi (piCx X.US) (piMap X.φ) Q tr t u =
      -residualTraceAt X β hβ Iso tr q C := by
    unfold resForm
    have hl := lhs_eq X.toQuasi.D (piCx X.US) (piMap X.φ) Q tr t u 0
    have h0 : Q.hU 2 1 2 rfl 0 t = 0 := LinearMap.map_zero₂ _ _
    erw [hl, h0, zero_sub, hcup, map_neg, map_neg]
    rfl
  have hp := localCupTrace_cocycles βq
    (fun g x y => hβ (locMap K S q.1 g) x y)
    (residualTraceAt X β hβ Iso tr q)
    (residualTraceAt_d X β hβ Iso tr htr q) z (localCocycle F hR t)
  exact hres.trans (congrArg Neg.neg hp).symm

/-- **Residual nondegeneracy: the exact `hnd` of the tame switch consumer.**
The inputs are finite local Tate duality in its printed degree-one form,
perfectness of the local coefficient pairing, and the local trace isomorphism.
No nondegeneracy of the switch or its residue form is assumed. -/
theorem derivSwitch_hnd_of_Milne (hMilne : MilneCor23Residual)
    (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)} (Tc : TameCoordinates (M := ResMod (locMap K S q.1) M) I φ σ)
    (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) x y, β (g • x) (g • y) = g • β x y)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) β hβ
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl c) = 0)
    (eT : ResMod (locMap K S q.1) T ≃ₗ[ZMod 2] ZMod 2)
    (htrivT : ∀ (g : Gloc K q.1) (m : T), locMap K S q.1 g • m = m)
    (hb : Function.Bijective (resPairing (ZMod 2) (GKS K S) β (locMap K S q.1)))
    (hb' : Function.Bijective (resPairing (ZMod 2) (GKS K S) β (locMap K S q.1)).flip)
    (htrace : InducesIsoH2
      (C := natCx (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)))
      (residualTraceAt (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)) β hβ Iso tr q)) :
    ∀ t (ht : (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi.D.U.d 1 2 rfl u = 0),
        resForm (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi
          (piCx (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).US)
          (piMap (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).φ)
          (galoisPairData K S (ZMod 2) β hβ
            (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
            (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso) tr t u = 0) →
      gClass (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).toQuasi t ht = 0 := by
  intro t ht hortho
  let X := derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)
  let βq := resPairing (ZMod 2) (GKS K S) β (locMap K S q.1)
  let trq := residualTraceAt X β hβ Iso tr q
  have hβq : ∀ (g : Gloc K q.1) x y, βq (g • x) (g • y) = g • βq x y :=
    fun g x y => hβ (locMap K S q.1 g) x y
  have htrq : ∀ c, trq
      (((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S q.1) T)).d 1 2).hom c) = 0 :=
    residualTraceAt_d X β hβ Iso tr htr q
  have : Finite (ResMod (locMap K S q.1) M) := Finite.of_injective eM eM.injective
  have hlocal := hMilne (q.1.adicCompletion K)
    (ResMod (locMap K S q.1) M) (ResMod (locMap K S q.1) M)
    (ResMod (locMap K S q.1) T) eT (fun g m => htrivT g m) βq hβq hb hb' trq htrq htrace
  have hz : kerToH1 (localCocycle F hR t) = 0 := by
    apply hlocal.2.2.2.1
    apply AddMonoidHom.ext
    intro y
    have hy : localCupTrace βq hβq trq htrq y (kerToH1 (localCocycle F hR t)) = 0 := by
      obtain ⟨z, rfl⟩ := kerToH1_surjective (k := ZMod 2) (G := Gloc K q.1)
        (M := ResMod (locMap K S q.1) M) y
      have ho := hortho (relSingle F q (hrelq_of_relAt F hR) z.1 z.2)
        (relSingle_d F q (hrelq_of_relAt F hR) z.1 z.2)
      have he := resForm_eq_localCupTrace F hR (eRAt (derivHsr F) hR φ σ eM Tc)
        β hβ Iso tr htr t z
      exact neg_eq_zero.mp (he.symm.trans ho)
    simpa only [AddMonoidHom.flip_apply, map_zero, AddMonoidHom.zero_apply] using hy
  exact gClass_eq_zero_of_localClass F hR φ σ eM Tc t ht hz

/-- **The tame switch consumer with residual nondegeneracy supplied.**
Coefficient perfectness is proved from the transported residual Weil pairing.
The local trace isomorphism is proved from the explicit A23 comparison and
its agreement with the genuine Brauer invariant. The sole local-duality print
is `MilneCor23Residual`; there is no switch nondegeneracy input. -/
theorem derivSwitch_switchCoordinates_tame_of_Milne (hMilne : MilneCor23Residual)
    (φ σ : Gloc K q.1)
    (eM : ResMod (locMap K S q.1) M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    {I : Subgroup (Gloc K q.1)} (Tc : TameCoordinates (M := ResMod (locMap K S q.1) M) I φ σ)
    (hIur : ∀ g, urRes K q.1 g = 1 → g ∈ I)
    (β γ : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
    (hβ : ∀ (g : GKS K S) x y, β (g • x) (g • y) = g • β x y)
    (hγ : ∀ (g : GKS K S) x y, γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x)
    (Iso : GaloisIsotropyData K S (ZMod 2) β hβ
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR)
    (tr : (coneCx (galoisPairData K S (ZMod 2) β hβ
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ c, tr ((coneCx (galoisPairData K S (ZMod 2) β hβ
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔS
      (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)).ΔR Iso).resE).d 2 3 rfl c) = 0)
    (hUS2 : ∀ v (x : (F.str v).cx.X 2), x = 0)
    {ε : ZMod 2} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hJ2 : J * J = 1)
    (htriv : ∀ (g : Gloc K q.1) (m : M), locMap K S q.1 g • m = m)
    (htrivT : ∀ (g : Gloc K q.1) (m : T), locMap K S q.1 g • m = m)
    (eT : ResMod (locMap K S q.1) T ≃ₗ[ZMod 2] ZMod 2)
    (eM₂ : ResMod (locMap K S q.1) M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hWeil : ∀ x y, eT (resPairing (ZMod 2) (GKS K S) β (locMap K S q.1) x y) =
      weil (eM x) (eM₂ y))
    (hKB : KummerBrauerComparisonF2 (q.1.adicCompletion K))
    (eμ : ResMod (locMap K S q.1) T ≃+ TauCeti.KummerCoeff (q.1.adicCompletion K) 2)
    (heμ : ∀ (g : TauCeti.AbsoluteGaloisGroup (q.1.adicCompletion K))
      (t : ResMod (locMap K S q.1) T),
      eμ ((TauCeti.absoluteGaloisGroupRestrictEquiv (q.1.adicCompletion K)).symm g • t) = g • eμ t)
    (hmatch : LocalTraceMatchesInvariant eμ heμ
      (residualTraceAt (derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)) β hβ Iso tr q)) :
    let X := derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)
    ∃ Φ : ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) ≃ₗ[ZMod 2]
        ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)),
      (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)).map Φ.toLinearMap =
        finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
      ({ X with eR := X.eR.trans Φ } : GenuineSwitch K S (ZMod 2) M).SwitchCoordinates
        (galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso) tr ε (-(-1)) J := by
  have : Finite T := Finite.of_injective eT eT.injective
  let X := derivSwitch F (eRAt (derivHsr F) hR φ σ eM Tc)
  obtain ⟨hb, hb'⟩ := coefficient_perfect_of_weil eM eM₂ eT
    (resPairing (ZMod 2) (GKS K S) β (locMap K S q.1)) hWeil
  have htrace := inducesIsoH2_of_KummerBrauer eμ heμ hKB
    (residualTraceAt X β hβ Iso tr q) hmatch
  have hnd := derivSwitch_hnd_of_Milne F hR hMilne φ σ eM Tc β hβ Iso tr htr
    eT htrivT hb hb' htrace
  exact derivSwitch_switchCoordinates_tame F hR φ σ eM Tc hIur β γ hβ hγ hpol Iso tr htr
    hUS2 hε hJ2 htriv htrivT hnd

end Switch

end ZInQ.Contrib.RC53Assist.HswResidual
