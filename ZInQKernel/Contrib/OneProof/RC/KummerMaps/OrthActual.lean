import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthUnramified
import ZInQKernel.Contrib.OneProof.RC.CoefModules.KummerAt
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Selmer

/-!
# Lane RC29 (item 2 (b)(ii), (c)): Kummer against Kummer, and the assembled orthogonality

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3463: "Its Kummer image
is its exact local annihilator, and the comparison has integral isotropy homotopies … These are the
local maps used in the Selmer-cone duality above"), the support comparisons (tex 3466–3499) and
Lemma `ex:arith-conjugate-duality` (tex 2761–2830).

* `OrthConcentratedAt`, `OrthIsotropicAt`: the per-place shape used here — a local condition
  concentrated in degrees `0, 1`, and the `(1, 1)` products of two conditions being coboundaries.
  For such conditions the zero homotopy is a `τ≥2` isotropy homotopy (`orthZeroIsotropy`) and the
  per-place local duality map does not depend on the homotopy (`orthLocalMap_indep`).
* (b)(ii) Kummer: `orth_kummerAt_concentrated` (PROVED: lane RC28's `kummerAt` lives in degrees
  `0, 1`); the two remaining Kummer inputs are hypotheses of kind ELLIOT in the assembled
  theorems — the isotropy of the Kummer conditions (`OrthIsotropicAt`, tex 3423, 3439–3448:
  "finite isotropy") and the per-place quasi-isomorphy of the local duality map for
  (Kummer, Kummer) (tex 3423, 3439–3450, 3456: exact annihilator, "Reduction modulo two … gives
  the perfect quotient-to-dual comparison; derived Nakayama lifts it"). The coefficient maps `ι`
  stay abstract.
* (c) `orthogonalComplementsT_urOutside`: **`OrthogonalComplementsT` for local conditions given
  at the coefficient support `S₀` and lane RC28's unramified conditions at `S − S₀`**, on the
  inflations of `G_{K,S₀}`-modules `M₀, M₀'` with a perfect pairing into `T₀ ≅ R(1)`, from (a)
  (`orthogonalComplementsT_ofCondAt`), the PRINT `NekovarProp756` at `S − S₀` and per-place
  hypotheses at `S₀`; `orthSelmerDuality_urOutside`: finite Selmer duality through lane RC26's
  `genuineSelmerDualityT`. The given conditions at `S₀` are required to be concentrated in degrees
  `0, 1` (`hc`, `hc'`), which excludes a genuine full condition with nonzero coefficients: these
  theorems do not cover the full active and moving conditions of the text (tex 2865–2867,
  5055–5061). Lane RC29's round-3 `actualLocalComplements` (`ActualComplements.lean`) does, through
  the arbitrary-condition assembly `orthogonalComplementsT_ofCondAt` and the full/zero comparison
  `orthLocalMap_full_zero_quasiIso`.
* The actual data: `orthogonalComplementsT_actualKummer` and `orthSelmerDuality_actualKummer` —
  RC28's `actualConditions` with the Kummer condition `kummerAt` at `S₀` on `M_i` and on
  `M_i(α⁻¹) ≅ M_i^*(1)` against each other through the inflated Weil pairing `weilPairingM`.

Kinds: definitions and PROVED from the hypotheses named in each statement.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-! ### Per-place predicates -/

section Predicates

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]

/-- A local condition at `v` **concentrated in degrees `0, 1`** (as the unramified and the Kummer
conditions are). -/
abbrev OrthConcentratedAt {v : Places K S} (c : CondAt K S R M v) : Prop :=
  ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (c.U.X i)

variable (β : M →ₗ[R] M' →ₗ[R] T)
  (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- **Isotropy of two local conditions at `v`**: the cup product of two degree-one elements is a
coboundary in `C²_cont(G_{K_v}, T)` (with the conditions in degrees `0, 1`, this is exactly what a
`τ≥2` isotropy homotopy with `h = 0` needs, `orthZeroIsotropy`). -/
abbrev OrthIsotropicAt {v : Places K S} (c : CondAt K S R M v) (c' : CondAt K S R M' v) : Prop :=
  ∀ (u : c.U.X 1) (y : c'.U.X 1),
    (orthGaloisPair K β hβ v).P 1 1 2 rfl (c.i.f 1 1 rfl u) (c'.i.f 1 1 rfl y) ∈
      LinearMap.range ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T v).d 1 2 rfl)

/-- **Transport of per-place quasi-isomorphy along equalities of conditions**, for conditions
concentrated in degrees `0, 1` (the isotropy homotopy does not matter, `orthLocalMap_indep`).
PROVED. -/
theorem orthQuasiIso_congr {v : Places K S} {A A₀ : CondAt K S R M v} {B B₀ : CondAt K S R M' v}
    (hA : A = A₀) (hB : B = B₀) (J : LocalTruncIsotropy A.i B.i (orthGaloisPair K β hβ v))
    (J₀ : LocalTruncIsotropy A₀.i B₀.i (orthGaloisPair K β hβ v))
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (hA₀ : OrthConcentratedAt A₀) (hB₀ : OrthConcentratedAt B₀)
    (h : QuasiIso (GHom.toCC (orthLocalMap A₀.i B₀.i (orthGaloisPair K β hβ v) J₀ trv htrv))) :
    QuasiIso (GHom.toCC (orthLocalMap A.i B.i (orthGaloisPair K β hβ v) J trv htrv)) := by
  subst hA hB
  rwa [orthLocalMap_indep J J₀ trv htrv hA₀ hB₀]

end Predicates

/-! ### Non-vacuity of the per-place predicates -/

section NonVacuity

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]

/-- Non-vacuity of `OrthConcentratedAt`: the zero condition. -/
theorem orth_zeroAt_concentrated (v : Places K S) : OrthConcentratedAt (zeroAt K S R M v) :=
  fun _ _ _ => inferInstanceAs (Subsingleton PUnit)

end NonVacuity

/-! ### (b)(ii) The Kummer condition lives in degrees `0, 1` -/

section KummerShape

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]

/-- **Lane RC28's Kummer condition is concentrated in degrees `0, 1`**
(`[C⁰ --d⁰--> Kummer span ⊔ B¹]`). PROVED. -/
theorem orth_kummerAt_concentrated (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (B : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t) :
    OrthConcentratedAt (kummerAt (k := R) v B m ι hι) := by
  intro i h0 h1
  match i, h0, h1 with
  | Int.ofNat 0, h0, _ => exact absurd rfl h0
  | Int.ofNat 1, _, h1 => exact absurd rfl h1
  | Int.ofNat (n + 2), _, _ =>
      change Subsingleton ↥(⊥ : Submodule R
        ↥(contCochain R (Gloc K v.1) (ResMod (locMap K S v.1) M) (n + 2)))
      infer_instance
  | Int.negSucc n, _, _ => exact inferInstanceAs (Subsingleton PUnit)

end KummerShape

/-! ### (c) Conditions at `S₀`, unramified conditions at `S − S₀` -/

section Assembly

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (R : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {M₀ M₀' T₀ : Type}
  [AddCommGroup M₀] [Module R M₀] [DistribMulAction (GKS K S₀) M₀] [SMulCommClass (GKS K S₀) R M₀]
  [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  [AddCommGroup M₀'] [Module R M₀'] [DistribMulAction (GKS K S₀) M₀']
  [SMulCommClass (GKS K S₀) R M₀'] [TopologicalSpace M₀'] [DiscreteTopology M₀']
  [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀']
  [AddCommGroup T₀] [Module R T₀] [DistribMulAction (GKS K S₀) T₀] [SMulCommClass (GKS K S₀) R T₀]
  [TopologicalSpace T₀] [DiscreteTopology T₀] [ContinuousSMul (GKS K S₀) T₀]
  (β₀ : M₀ →ₗ[R] M₀' →ₗ[R] T₀)
  (hβ₀ : ∀ (g : GKS K S₀) (a : M₀) (b : M₀'), β₀ (g • a) (g • b) = g • β₀ a b)

/-- The unramified-outside conditions are concentrated in degrees `0, 1` when the given ones at
`S₀` are. PROVED. -/
theorem orth_urOutside_concentrated (M₁ : Type) [AddCommGroup M₁] [Module R M₁]
    [DistribMulAction (GKS K S₀) M₁] [SMulCommClass (GKS K S₀) R M₁] [TopologicalSpace M₁]
    [DiscreteTopology M₁] [ContinuousSMul (GKS K S₀) M₁] [Finite M₁]
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S R (InflMod hS M₁) v)
    (hc : ∀ v h, OrthConcentratedAt (c v h)) (v : Places K S) :
    OrthConcentratedAt (urOutside hS R M₁ c v) := by
  unfold urOutside
  split_ifs with h
  · exact hc v h
  · exact orth_urAt_vanishes hS R M₁ v h

/-- Non-vacuity of `OrthIsotropicAt`: lane RC28's unramified conditions at `w ∈ S − S₀` are
isotropic (Lemma 7.5.2, PROVED in `OrthUnramified`). -/
theorem orth_urAt_isotropic (w : Places K S) (hw : w.1 ∉ S₀) :
    OrthIsotropicAt (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (urAt hS R M₀ w hw) (urAt hS R M₀' w hw) :=
  orthUr_cup_mem_range hS R β₀ hβ₀ w hw

variable (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S R (InflMod hS M₀) v)
  (c' : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S R (InflMod hS M₀') v)
  (hc : ∀ v h, OrthConcentratedAt (c v h)) (hc' : ∀ v h, OrthConcentratedAt (c' v h))
  (hiso : ∀ v h, OrthIsotropicAt (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
    (c v h) (c' v h))

include hiso in
/-- The unramified-outside conditions are isotropic when the given ones at `S₀` are: at
`S − S₀` by the PROVED Lemma 7.5.2 (`orthUr_cup_mem_range`). PROVED. -/
theorem orth_urOutside_isotropic (v : Places K S) :
    OrthIsotropicAt (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (urOutside hS R M₀ c v) (urOutside hS R M₀' c' v) := by
  unfold urOutside
  split_ifs with h
  · exact hiso v h
  · exact orthUr_cup_mem_range hS R β₀ hβ₀ v h

/-- **The isotropy homotopies of the actual-shape conditions**: the zero homotopy at every place
(a `τ≥2` isotropy homotopy by the isotropy at `S₀` and Lemma 7.5.2 at `S − S₀`). It needs the given
conditions at `S₀` concentrated in degrees `0, 1`, so it does not apply to a genuine full condition;
for full/zero places see round 3's `ActLTZ` and `actLIso` (`ActualComplements.lean`). -/
def orthOutsideIsotropy (v : Places K S) :
    LocalTruncIsotropy (urOutside hS R M₀ c v).i (urOutside hS R M₀' c' v).i
      (orthUrPair hS R β₀ hβ₀ v) :=
  orthZeroIsotropy (orth_urOutside_concentrated hS R M₀ c hc v)
    (orth_urOutside_concentrated hS R M₀' c' hc' v) (orth_urOutside_isotropic hS R β₀ hβ₀ c c' hiso v)

/-- The `τ≥2` isotropy data of the actual-shape conditions (lane RC26's
`TruncIsotropyData.ofLocal` of `orthOutsideIsotropy`), for given conditions at `S₀` concentrated in
degrees `0, 1` (not a genuine full condition; see round 3's `actLTrunc`). -/
abbrev orthOutsideTrunc :
    GaloisTruncIsotropyData K S R (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c')) :=
  TruncIsotropyData.ofLocal (ΔA := ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
    (ΔB := ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
    (orthOutsideIsotropy hS R β₀ hβ₀ c c' hc hc' hiso)

variable (trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS T₀) v).X 2 →ₗ[R] R)
  (htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS T₀) v).d 1 2 rfl z) = 0)

/-- **The per-place quasi-isomorphisms**: at `v ∈ S₀` from the hypothesis `hperf` (the given
conditions are exact orthogonal complements with the zero homotopy), at `v ∈ S − S₀` from the
PRINT `NekovarProp756`. PROVED (from these). -/
theorem orth_urOutside_quasiIso (h756 : NekovarProp756 K) (p : ℕ) [IsLocalRing R]
    (hset₀ : NekovarFiniteSetting K S₀ p R) (hb : Function.Bijective β₀)
    (hb' : Function.Bijective β₀.flip) (hT₀ : IsCyclotomicTwist K S₀ R T₀)
    (htrv2 : ∀ v : Places K S, v.1 ∉ S₀ → InducesIsoH2 (trv v))
    (hperf : ∀ (v : Places K S) (h : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap (c v h).i
      (c' v h).i (orthUrPair hS R β₀ hβ₀ v) (orthZeroIsotropy (hc v h) (hc' v h) (hiso v h))
      (trv v) (htrv v))))
    (v : Places K S) :
    QuasiIso (GHom.toCC (orthLocalMap (urOutside hS R M₀ c v).i (urOutside hS R M₀' c' v).i
      (orthUrPair hS R β₀ hβ₀ v) (orthOutsideIsotropy hS R β₀ hβ₀ c c' hc hc' hiso v)
      (trv v) (htrv v))) := by
  by_cases h : v.1 ∈ S₀
  · exact orthQuasiIso_congr (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (show urOutside hS R M₀ c v = c v h from dif_pos h)
      (show urOutside hS R M₀' c' v = c' v h from dif_pos h) _ _ (trv v) (htrv v)
      (hc v h) (hc' v h) (hperf v h)
  · exact orthQuasiIso_congr (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (show urOutside hS R M₀ c v = urAt hS R M₀ v h from dif_neg h)
      (show urOutside hS R M₀' c' v = urAt hS R M₀' v h from dif_neg h) _ _ (trv v) (htrv v)
      (orth_urAt_vanishes hS R M₀ v h) (orth_urAt_vanishes hS R M₀' v h)
      (orthUr_quasiIso_of_print h756 hS p hset₀ β₀ hβ₀ hb hb' hT₀ v h
        (orthUrIsotropy hS R β₀ hβ₀ v h) (trv v) (htrv v) (htrv2 v h))

/-- **(c) `OrthogonalComplementsT` for conditions given at `S₀` and the unramified conditions at
`S − S₀`** (Nekovář 6.2.7 with 7.5.6; tex 2813–2816, 3423, 3483–3498): with finitely many places,
the zero isotropy homotopies, local traces `tr_v` killing coboundaries (inducing `H² ≅ R` at
`S − S₀`), a global trace whose local part is `∑_v tr_v` (`hsum`, GLUE as in lane RC26: Nekovář's
trace construction 5.4.1 is not formalized), and the per-place orthogonality at `S₀` (`hperf`).
PROVED (from `NekovarProp756` and the hypotheses). -/
theorem orthogonalComplementsT_urOutside [Fintype (Places K S)] (h756 : NekovarProp756 K)
    (p : ℕ) [IsLocalRing R] (hset₀ : NekovarFiniteSetting K S₀ p R) (hb : Function.Bijective β₀)
    (hb' : Function.Bijective β₀.flip) (hT₀ : IsCyclotomicTwist K S₀ R T₀)
    (htrv2 : ∀ v : Places K S, v.1 ∉ S₀ → InducesIsoH2 (trv v))
    (hperf : ∀ (v : Places K S) (h : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap (c v h).i
      (c' v h).i (orthUrPair hS R β₀ hβ₀ v) (orthZeroIsotropy (hc v h) (hc' v h) (hiso v h))
      (trv v) (htrv v))))
    (tr : (galoisCompactTT K S R (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
      (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso)).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
      (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso)).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS T₀)).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) (InflMod hS T₀)).X 3), (truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) (InflMod hS T₀)) (3 - 1)).mkQ
          z) = ∑ v, trv v (z v)) :
    OrthogonalComplementsT K (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
      (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso) tr htr :=
  orthogonalComplementsT_ofCondAt K (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
    (urOutside hS R M₀ c) (urOutside hS R M₀' c') (orthOutsideIsotropy hS R β₀ hβ₀ c c' hc hc' hiso)
    trv htrv tr htr hsum
    (orth_urOutside_quasiIso hS R β₀ hβ₀ c c' hc hc' hiso trv htrv h756 p hset₀ hb hb' hT₀ htrv2
      hperf)

/-- **(c) Finite Selmer duality for conditions given at `S₀` and the unramified conditions at
`S − S₀`** (Lemma `ex:arith-conjugate-duality`, tex 2761–2830, with tex 3456; Nekovář 6.3.4 via
lane RC26's `genuineSelmerDualityT`): the genuine Selmer duality map of the `τ≥2` data is a
quasi-isomorphism. Hypotheses: the PRINTs `NekovarProp543T` (Nekovář 5.4.3) and `NekovarProp756`
(Nekovář 7.5.6), the standing settings for `S₀` and `S`, a perfect pairing into a cyclotomic twist
over `S₀` whose inflation is a cyclotomic twist over `S` (`hT`, GLUE: `K_{S₀} ⊆ K_S` and the
`N`-th roots of unity of `K_S` lie in `K_{S₀}`; not formalized here), the traces as in
`orthogonalComplementsT_urOutside` with `InducesIsoH3 tr`, and the per-place orthogonality at
`S₀`. PROVED (from these). -/
theorem orthSelmerDuality_urOutside [Fintype (Places K S)] (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K) (p : ℕ) [IsLocalRing R] (hset₀ : NekovarFiniteSetting K S₀ p R)
    (hset : NekovarFiniteSetting K S p R) (hb : Function.Bijective β₀)
    (hb' : Function.Bijective β₀.flip) (hT₀ : IsCyclotomicTwist K S₀ R T₀)
    (hT : IsCyclotomicTwist K S R (InflMod hS T₀))
    (htrv2 : ∀ v : Places K S, v.1 ∉ S₀ → InducesIsoH2 (trv v))
    (hperf : ∀ (v : Places K S) (h : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap (c v h).i
      (c' v h).i (orthUrPair hS R β₀ hβ₀ v) (orthZeroIsotropy (hc v h) (hc' v h) (hiso v h))
      (trv v) (htrv v))))
    (tr : (galoisCompactTT K S R (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
      (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso)).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
      (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso)).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS T₀)).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) (InflMod hS T₀)).X 3), (truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) (InflMod hS T₀)) (3 - 1)).mkQ
          z) = ∑ v, trv v (z v))
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S R (orthInflPair hS R β₀)
      (orthInflPair_smul hS R β₀ hβ₀) (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
      (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso)) tr htr)) :=
  haveI : Finite (InflMod hS M₀) := inferInstanceAs (Finite M₀)
  haveI : Finite (InflMod hS M₀') := inferInstanceAs (Finite M₀')
  genuineSelmerDualityT K (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
    (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
    (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
    (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso) tr htr h543 p hset hb hb' hT htr3
    (orthogonalComplementsT_urOutside hS R β₀ hβ₀ c c' hc hc' hiso trv htrv h756 p hset₀ hb hb'
      hT₀ htrv2 hperf tr htr hsum)

end Assembly


/-! ### The actual data: Kummer at `S₀`, unramified at `S − S₀`, on `M_i` and `M_i(α⁻¹)` -/

section Actual

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (α : GKS K S₀ →* (Acoef i)ˣ)
  [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
  (B B' : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
  [∀ v, (B' v).IsElliptic]
  (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) (2 ^ i) →+
    ResMod (locMap K S v.1) (MinS hS W i α))
  (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) (2 ^ i)),
    ι v (σ • t) = σ • ι v t)
  (ι' : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B' v) (2 ^ i) →+
    ResMod (locMap K S v.1) (MinS hS W i (charInv α)))
  (hι' : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B' v) (2 ^ i)),
    ι' v (σ • t) = σ • ι' v t)

/-- The Kummer conditions at `S₀` on `M_i` (lane RC28's `kummerAt`, `ι` abstract). -/
abbrev orthKummerC : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v :=
  fun v _ => kummerAt v (B v) (2 ^ i) (ι v) (hι v)

/-- The Kummer conditions at `S₀` on the dual module `M_i(α⁻¹) ≅ M_i^*(1)`. -/
abbrev orthKummerC' : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i (charInv α)) v :=
  fun v _ => kummerAt v (B' v) (2 ^ i) (ι' v) (hι' v)

/-- The conditions of `orthogonalComplementsT_actualKummer` are lane RC28's `actualConditions`
with the Kummer condition at `S₀`. -/
theorem orth_actualConditions_eq :
    actualConditions hS W i α (orthKummerC hS W i α B ι hι) =
      ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)) :=
  rfl

/-- **(c) for the actual data**: `OrthogonalComplementsT` for lane RC28's actual conditions (the
Kummer condition `kummerAt` at the coefficient support `S₀`, the unramified condition at `S − S₀`)
on `M_i` against the same shape on `M_i(α⁻¹) ≅ M_i^*(1)` through the inflated Weil pairing
(tex 2798–2804), with the zero isotropy homotopies. Hypotheses: the PRINT `NekovarProp756`
(Nekovář 7.5.6) at `S − S₀`; the standing hypotheses for `S₀` (`K` totally complex, `S₀` finite
containing the primes above `2`) and `E[2^i]` defined over `K_{S₀}` (`FullTorsion`, GLUE of lane
RC28); **ELLIOT** `hisoK` (tex 3423, 3439–3448: the Kummer conditions are isotropic, "finite
isotropy"; its cohomological content is the isotropy half of the other group's
`KummerAnnihilatorNode`, PROVED from the PRINT `MilneLocalTateDualityKummer`, UNVERIFIED, in a
different cohomology model — the comparison and the coefficient extension along `ι, ι'` are not
formalized); **ELLIOT** `hperfK` (tex 3423, 3439–3450, 3456: the Kummer condition is the exact
local annihilator and the comparison is perfect, "Reduction modulo two … gives the perfect
quotient-to-dual comparison; derived Nakayama lifts it"); the traces as in
`orthogonalComplementsT_urOutside`. PROVED (from these). -/
theorem orthogonalComplementsT_actualKummer [Fintype (Places K S)] (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hW : FullTorsion K S₀ W (2 ^ i))
    (hisoK : ∀ v h, OrthIsotropicAt (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (orthKummerC hS W i α B ι hι v h) (orthKummerC' hS W i α B' ι' hι' v h))
    (trv : ∀ v : Places K S, (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v : Places K S, v.1 ∉ S₀ → InducesIsoH2 (trv v))
    (hperfK : ∀ (v : Places K S) (h : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap
      (kummerAt v (B v) (2 ^ i) (ι v) (hι v)).i (kummerAt v (B' v) (2 ^ i) (ι' v) (hι' v)).i
      (orthUrPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
        (weilPairingM_smul W hμ₀ (Acoef i) α) v)
      (orthZeroIsotropy (orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) (hisoK v h))
      (trv v) (htrv v))))
    (tr : (galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)).X 3 →ₗ[Acoef i]
        Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)).d 2 3 rfl
          z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    OrthogonalComplementsT K (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK) tr htr :=
  orthogonalComplementsT_urOutside hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
    (weilPairingM_smul W hμ₀ (Acoef i) α) (orthKummerC hS W i α B ι hι)
    (orthKummerC' hS W i α B' ι' hι')
    (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
    (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK trv htrv h756 2
    (nekovarFiniteSetting_acoef K hK S₀ hS₀fin h2₀ i)
    (weilPairingM_bijective W hμ₀ (Acoef i) α hW) (weilPairingM_flip_bijective W hμ₀ (Acoef i) α hW)
    (isCyclotomicTwist_tate1 (Acoef i) hμ₀) htrv2 hperfK tr htr hsum

/-- **(c) Finite Selmer duality for the actual data** (Lemma `ex:arith-conjugate-duality`, tex
2761–2830, with the Kummer-type conditions of (4.3), tex 3455–3463; Nekovář 6.3.4 via lane RC26's
`genuineSelmerDualityT`): the genuine Selmer duality map of lane RC28's actual conditions (Kummer
at `S₀`, unramified at `S − S₀`) on `M_i` against `M_i(α⁻¹) ≅ M_i^*(1)` is a quasi-isomorphism.
Hypotheses: those of `orthogonalComplementsT_actualKummer`, the PRINT `NekovarProp543T`
(Nekovář 5.4.3), `S` finite, `InducesIsoH3 tr`, and `hT` (GLUE, not formalized here: the
inflation of the cyclotomic twist `A_i(1)` from `G_{K,S₀}` to `G_{K,S}` is a cyclotomic twist —
`K_{S₀} ⊆ K_S`, and the `2^i`-th roots of unity of `K_S` are those of `K_{S₀}`). PROVED (from
these). -/
theorem orthSelmerDuality_actualKummer [Fintype (Places K S)] (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K) (hSfin : S.Finite)
    (hT : IsCyclotomicTwist K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (hK : IsTotallyComplex K) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hW : FullTorsion K S₀ W (2 ^ i))
    (hisoK : ∀ v h, OrthIsotropicAt (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (orthKummerC hS W i α B ι hι v h) (orthKummerC' hS W i α B' ι' hι' v h))
    (trv : ∀ v : Places K S, (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v : Places K S, v.1 ∉ S₀ → InducesIsoH2 (trv v))
    (hperfK : ∀ (v : Places K S) (h : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap
      (kummerAt v (B v) (2 ^ i) (ι v) (hι v)).i (kummerAt v (B' v) (2 ^ i) (ι' v) (hι' v)).i
      (orthUrPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
        (weilPairingM_smul W hμ₀ (Acoef i) α) v)
      (orthZeroIsotropy (orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) (hisoK v h))
      (trv v) (htrv v))))
    (tr : (galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)).X 3 →ₗ[Acoef i]
        Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)).d 2 3 rfl
          z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)) tr htr)) :=
  orthSelmerDuality_urOutside hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
    (weilPairingM_smul W hμ₀ (Acoef i) α) (orthKummerC hS W i α B ι hι)
    (orthKummerC' hS W i α B' ι' hι')
    (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
    (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK trv htrv h543
    h756 2 (nekovarFiniteSetting_acoef K hK S₀ hS₀fin h2₀ i)
    (nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i)
    (weilPairingM_bijective W hμ₀ (Acoef i) α hW) (weilPairingM_flip_bijective W hμ₀ (Acoef i) α hW)
    (isCyclotomicTwist_tate1 (Acoef i) hμ₀) hT htrv2 hperfK tr htr hsum htr3

end Actual

end ZInQ.Manuscript.RC.KummerMaps
