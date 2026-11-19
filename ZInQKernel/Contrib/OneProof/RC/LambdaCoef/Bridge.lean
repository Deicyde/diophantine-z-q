import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Fibre
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Collapse
import ZInQKernel.Contrib.OneProof.RC.CoefModules.CocycleCondition
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.DerivativeTransport
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GaloisWiringQuad

/-!
# Lane RC28 round 2, part 6: the fibres `V_𝔭` in the genuine Selmer and switching interfaces

Manuscript `diophantine_zq.tex` (11/5), (4.3) at tex 3455–3463 and the switching argument at
tex 4976–5200 ("use the actual primitive scalar Selmer complex over `R = Λ_𝔭`", `k = Frac(Λ/𝔭)` of
characteristic zero).

For `𝔭` a height-one prime `≠ (2)` (`IsHeightOneOdd`) and a continuous `α` (`IsContChar`), the
field `k = ResAt 𝔭` and the module `V_𝔭 = VP K S W 𝔭 α` carry every instance the interfaces need:

* `fibreSelData Δ = galoisSelData K S k V_𝔭 Δ` (lane RC26) for any genuine local conditions `Δ`;
  `fibreRelaxed`, `fibreStrict` (full / zero conditions), and **`fibreUr`**: the unramified
  condition at every place, the cocycle subcomplex `U⁰ = C⁰`, `U¹ = Z_ur + B¹`, `Uⁿ = 0` with
  `Z_ur` the continuous `1`-cocycles constant on inertia cosets (`urZ`), injective
  (`fibreUr_injective`);
* `fibreLv = galLv (k := k) K S V_𝔭`: the genuine local complexes `C^•_cont(G_{K_v}, V_𝔭)` at the
  decomposition groups, the input of the other group's `DerivFamily` / `toQuasiSide`;
  `fibreDerivFamily` (non-vacuity);
* `fibreFamily Δ`: a configuration family over `ResAt 𝔭`, `Λ_𝔭` whose actual fibre is
  `galoisSelData K S k V_𝔭 Δ` (the slot of the switching data), **genuine at `𝔭`**
  (`isGenuineFamilyAt_fibreFamily`);
* **the round-1 obstruction disappears**: `2` is a unit of `k` (`isUnit_two_resAt`), `k` has
  characteristic zero (`charZero_resAt`), and `V_𝔭` is not killed by any power of `2` as soon as it
  is nonzero (`not_two_pow_torsion`); the genuine fibre complex has a nonzero degree-zero term
  (`nontrivial_selCx_zero`), so `collapse_refuted_actual` does not apply.

Kinds: definitions and PROVED.
-/

/-!
This is a conditional construction for one supplied continuous Λ-valued character on a fixed
G_{K,S}. Its finite levels are the compatible reductions of that character. The manuscript's
moving characters have conductor primes varying with precision and need not be reductions of
one character (tex 2737–2741, 4269–4277). No identification with the retained inner-limit Selmer
diagrams is proved here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LambdaCoef

open NumberField IsDedekindDomain CategoryTheory Filter Topology
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Wiring (ResAt resAt IsGaloisSelData IsGenuineFamilyAt)
open ZInQ.Manuscript.RC.CoefModules (CondAt ofCondAt ofCondAt_injective contD cfun
  cocycleCondition cocycleConditionι cocycleConditionι_injective)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx GCx)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily DerivFamily SubFam galLv)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (resUr)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (α : GKS K S →* Lambdaˣ) [IsContChar α]

/-! ### Genuine Selmer data with coefficients `V_𝔭` -/

/-- **The genuine Selmer data (4.3) with coefficients the fibre `V_𝔭`**, over `k = k(𝔭)`. -/
abbrev fibreSelData (Δ : GaloisLocalConditions K S (ResAt P) (VP K S W P α)) : SelData (ResAt P) :=
  galoisSelData K S (ResAt P) (VP K S W P α) Δ

/-- The full conditions at every place. -/
abbrev fibreRelaxed : SelData (ResAt P) :=
  fibreSelData W P α (relaxedConditions (ResAt P) _ _ _ _)

/-- The zero conditions at every place (compactly supported cochains). -/
abbrev fibreStrict : SelData (ResAt P) :=
  fibreSelData W P α (strictConditions (ResAt P) _ _ _ _)

/-- **The genuine local complexes of `V_𝔭` at the decomposition groups** (the input of the other
group's derivative families). -/
abbrev fibreLv : Places K S → GCx (ResAt P) := galLv (k := ResAt P) K S (VP K S W P α)

/-- Non-vacuity of the derivative families over `V_𝔭` (the old conditions everywhere). -/
def fibreDerivFamily : DerivFamily (fibreLv W P α) :=
  DerivFamily.const _ fun v => SubFam.top _

/-! ### The unramified condition for `V_𝔭` -/

variable (K S) in
/-- **The unramified `1`-cocycles** at `v`: continuous cocycles constant on the cosets of the
inertia group (the kernel of `G_{K_v} → Gal(K_v^{ur}/K_v)`), i.e. inflated from
`Gal(K_v^{ur}/K_v)` with values in the inertia invariants. -/
def urZ (v : Places K S) :
    Submodule (ResAt P) (contCochain (ResAt P) (Gloc K v.1) (ResMod (locMap K S v.1)
      (VP K S W P α)) 1) where
  carrier := {z | contD _ _ _ 1 z = 0 ∧ ∀ g g' : Fin 1 → Gloc K v.1,
    resUr K v.1 (g 0) = resUr K v.1 (g' 0) → cfun z g = cfun z g'}
  add_mem' {a b} ha hb := ⟨by rw [map_add, ha.1, hb.1, add_zero], fun g g' h => by
    change cfun a g + cfun b g = cfun a g' + cfun b g'
    rw [ha.2 g g' h, hb.2 g g' h]⟩
  zero_mem' := ⟨map_zero _, fun _ _ _ => rfl⟩
  smul_mem' c z hz := ⟨by rw [map_smul, hz.1, smul_zero], fun g g' h => by
    change c • cfun z g = c • cfun z g'
    rw [hz.2 g g' h]⟩

/-- **The unramified condition at `v`** (tex 3479–3498): `U⁰ = C⁰`, `U¹ = Z_ur + B¹`, `Uⁿ = 0`,
as a subcomplex of `C^•_cont(G_{K_v}, V_𝔭)` (the generic cocycle condition of lane RC28 round 1). -/
def urCocycleAt (v : Places K S) : CondAt K S (ResAt P) (VP K S W P α) v :=
  ⟨cocycleCondition (urZ K S W P α v) (fun z hz => hz.1),
    cocycleConditionι (urZ K S W P α v) (fun z hz => hz.1)⟩

/-- **The unramified local conditions for `V_𝔭` at every place.** -/
def fibreUrConditions : GaloisLocalConditions K S (ResAt P) (VP K S W P α) :=
  ofCondAt K S _ _ (fun v => urCocycleAt W P α v)

/-- The unramified conditions are subcomplexes of the local cochains. Kind: PROVED. -/
theorem fibreUr_injective (v : Places K S) (n : ℤ) :
    Function.Injective (((fibreUrConditions W P α).i v).f n n rfl) :=
  ofCondAt_injective K S _ _ _ (fun v n => cocycleConditionι_injective (urZ K S W P α v)
    (fun z hz => hz.1) n) v n

/-- The genuine Selmer data of `V_𝔭` with the unramified conditions. -/
abbrev fibreUr : SelData (ResAt P) := fibreSelData W P α (fibreUrConditions W P α)

/-- **The fibre Selmer data are genuine Galois Selmer data** (`IsGaloisSelData`) for finite `S`
and injective conditions. Kind: PROVED. -/
theorem isGaloisSelData_fibre (hS : S.Finite) (Δ : GaloisLocalConditions K S (ResAt P)
    (VP K S W P α)) (hΔ : ∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl)) :
    IsGaloisSelData (fibreSelData W P α Δ) :=
  ⟨K, inferInstance, inferInstance, S, VP K S W P α, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Δ, hS, hΔ, rfl⟩

theorem isGaloisSelData_fibreRelaxed (hS : S.Finite) :
    IsGaloisSelData (fibreRelaxed W P α) :=
  isGaloisSelData_fibre W P α hS _ fun _ _ _ _ h => h

theorem isGaloisSelData_fibreStrict (hS : S.Finite) :
    IsGaloisSelData (fibreStrict W P α) :=
  isGaloisSelData_fibre W P α hS _ fun _ _ x y _ => Subsingleton.elim (α := PUnit) x y

theorem isGaloisSelData_fibreUr (hS : S.Finite) : IsGaloisSelData (fibreUr W P α) :=
  isGaloisSelData_fibre W P α hS _ (fibreUr_injective W P α)

/-! ### The slot of the switching data -/

/-- **A configuration family over `k(𝔭)`, `Λ_𝔭` whose actual fibre is the genuine Selmer data
of `V_𝔭`** (one configuration; the actual class and functional `0`): the slot the switching
data fill. -/
def fibreFamily (Δ : GaloisLocalConditions K S (ResAt P) (VP K S W P α)) :
    SwitchFamily (ResAt P) (Localization.AtPrime P) where
  Config := Unit
  Prime := Empty
  actual := ()
  next c _ := c
  fibre _ := fibreSelData W P α Δ
  t := algebraMap Lambda (Localization.AtPrime P) PowerSeries.X
  zAct := 0
  hzAct := map_zero _
  lamAct := 0
  hlamAct _ := rfl

/-- **The fibre family is genuine at `𝔭`** (lane RC0's `IsGenuineFamilyAt`). Kind: PROVED. -/
theorem isGenuineFamilyAt_fibreFamily (hS : S.Finite)
    (Δ : GaloisLocalConditions K S (ResAt P) (VP K S W P α))
    (hΔ : ∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl)) :
    IsGenuineFamilyAt P (fibreFamily W P α Δ) :=
  ⟨fun _ => isGaloisSelData_fibre W P α hS Δ hΔ, rfl⟩

/-! ### The round-1 obstruction disappears -/

/-- `2` is a unit of `k(𝔭)`. Kind: PROVED. -/
theorem isUnit_two_fibreField : IsUnit (2 : ResAt P) :=
  isUnit_two_resAt (IsHeightOneOdd.height_eq (P := P)) (IsHeightOneOdd.ne_two (P := P))

/-- `k(𝔭)` has characteristic zero. Kind: PROVED. -/
theorem charZero_fibreField : CharZero (ResAt P) :=
  charZero_resAt (IsHeightOneOdd.height_eq (P := P)) (IsHeightOneOdd.ne_two (P := P))

/-- **A nonzero `V_𝔭` is not `2`-power torsion** (contrast with round 1's
`collapse_refuted_actual`, whose hypothesis is `2`-power torsion). Kind: PROVED. -/
theorem not_two_pow_torsion [Nontrivial (VP K S W P α)] :
    ¬ ∃ n : ℕ, ∀ v : VP K S W P α, (2 ^ n : ℕ) • v = 0 := by
  rintro ⟨n, hn⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : VP K S W P α)
  have hu : IsUnit ((2 : ResAt P) ^ n) := (isUnit_two_fibreField P).pow n
  have h := hn v
  rw [← Nat.cast_smul_eq_nsmul (ResAt P), Nat.cast_pow, Nat.cast_ofNat] at h
  exact hv ((hu.smul_eq_zero).mp h)

/-- The constant `0`-cochain map `V_𝔭 → C⁰_cont(G_{K,S}, V_𝔭)` is injective. -/
theorem constCochain_injective :
    Function.Injective fun v : VP K S W P α =>
      (ZInQ.Manuscript.RC.CoefModules.constCochain (k := ResAt P) (G := GKS K S) v) := by
  intro v w h
  have := congrArg (fun c => cfun c default) h
  simpa using this

end ZInQ.Manuscript.RC.LambdaCoef
