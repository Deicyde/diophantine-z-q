import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerTraces

/-!
# Lane RC29 (round 3): the local complement criterion for the actual Selmer data at every place

Manuscript `diophantine_zq.tex`, Definition `ex:arith-data` (tex 2748–2760: "The primitive and
relaxed complexes use the actual derived Kummer, unramified, full and orthogonal local conditions
specified below"), Lemma `ex:arith-conjugate-duality` (tex 2761–2830; tex 2813–2814: "A full
condition is paired with the zero condition"), the descent paragraph (tex 3080–3085: "Then `b_{I,a}`
is Kummer at `2N` … at good odd places the finite Kummer image equals the unramified image. At active
and moving primes the required condition is full"), Lemma `ex:arith-local-kummer` (tex 3413–3468)
and the support change (tex 3483–3498: the unramified condition at the new places).

**The actual local conditions** on `M_i = (E[2^i] ⊗ A_i)(α)` (built over `G_{K,S₀}`, inflated to the
Selmer support `S ⊇ S₀`), with the derivative primes excluded (they belong to the inner-limit
switching, Lemma `ex:limits-derivative-switch`):

| place | condition on `M_i(α)` | orthogonal condition on `M_i(α⁻¹) ≅ M_i^*(1)` |
|---|---|---|
| `v ∈ P` (the places above `2N`) | Kummer (`actualKummerAtS α`) | Kummer (`actualKummerAtS α⁻¹`) |
| `v ∈ S₀ − P` (active and moving primes) | full (`fullAt`) | zero (`zeroAt`) |
| `v ∈ S − S₀` (new places) | unramified (`urAt`) | unramified (`urAt`) |

Results:

* `actLCondA`, `actLCondB`: these two families (`ofCondAt` of them are lane RC26's
  `GaloisLocalConditions`).
* `ActLTZ` and `actLIso`: at every place the restricted cup product vanishes after the truncation
  `τ≥2` (Kummer: finite isotropy, from the Milne print; full/zero: the dual inclusion is zero;
  unramified: Nekovář's Lemma 7.5.2, PROVED in round 1), so the zero family is a `τ≥2` isotropy
  homotopy at every place; `actLTrunc` is the glued `τ≥2` isotropy data.
* `actLPerf`: **the per-place local duality maps are quasi-isomorphisms at every place**: at `P`
  from the PRINTs `MilneLocalTateDualityKummerCharZero` and `NekovarProp524` (round 2's
  `kummerPerPlace_perf_of_milne`), at `S₀ − P` for every coefficient system (full against zero,
  round 1's `orthLocalMap_full_zero_quasiIso`), at `S − S₀` from the PRINT `NekovarProp756`.
* **`actualLocalComplements`**: lane RC26's `OrthogonalComplementsT` — exactly the hypothesis
  `horth` of RC26's consumer `genuineSelmerDualityT` — for the actual conditions, with no per-place
  input left (only PRINTs, the standing setting and the traces).
* **`actualSelmerDuality`** (given traces), **`actualSelmerDuality_packet`** (a global trace
  normalized by a packet of local traces), **`actualSelmerDuality_of_prints`** (the traces from the
  print `NekovarFiniteTraces`): the finite Selmer duality `C_U(M_i) ≃ RHom(C_{U⊥}(M_i^*(1)),
  A_i)[−3]` for the actual data, packaged with the orthogonal complements as `ActLDuality`.

Companion files: `ActualBridge.lean` (the shape of lane RC31's consumers,
`actualLocalComplements_iff_fibre`, and non-vacuity, `actL_nonvacuous`), `ConjComplements.lean`
(the same criterion with the text's transported dual conditions on `τ^*M_i` and the pairing
`(v, w) ↦ e(v, ρ_T(τ)w)`, `conjActualLocalComplements`) and `ActualConj.lean` (its global form with
the traces of the packet, `conjActualSelmerDuality_of_prints`).

Kinds: definitions and PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero` (Milne,
*Arithmetic Duality Theorems*, 2nd ed., I.2.3, I.3.2, I.3.4, I.3.5), `NekovarProp524` (Nekovář 5.2.4),
`NekovarProp756` (Nekovář 7.5.6 with 7.5.5), for the global duality also `NekovarProp543T` (5.4.3)
and `NekovarFiniteTraces` (5.1.3, 5.1.5, 5.2.1, 5.4.1); GLUE `FullTorsion` (lane RC28); ELLIOT
`hα` (the moving character is trivial on the decomposition groups at `2N`: tex 2729, 3431,
Proposition `ex:arith-moving-character`, tex 3500–3506; for `α_i = χ_hΨ_i` this is round 1's
`isLocallyQuadAt_alphaChar`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero LocalTruncIsotropy
  pullPair ofTruncZero)
open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-! ### Vanishing after `τ≥2` and the zero isotropy homotopy -/

section TruncZero

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- Predicate (Nekovář 6.2.1.3, 6.2.1.5: `prod_v = 0` after `τ≥2`). **The restricted local cup
product of two conditions at `v` vanishes in `τ≥2 C(G_{K_v}, T)`**: then the zero family is a `τ≥2`
isotropy homotopy (`actLIsoOf`). -/
def ActLTZ {v : Places K S} (A : CondAt K S R M v) (B : CondAt K S R M' v) : Prop :=
  ∀ (a b c : ℤ) (h : a + b = c) (u : A.U.X a) (w : B.U.X b),
    (truncPair (pullPair (orthGaloisPair K β hβ v) A.i B.i)).P a b c h u w = 0

/-- Definition. The zero `τ≥2` isotropy homotopy of a pair satisfying `ActLTZ`. -/
def actLIsoOf {v : Places K S} {A : CondAt K S R M v} {B : CondAt K S R M' v}
    (hz : ActLTZ β hβ A B) : LocalTruncIsotropy A.i B.i (orthGaloisPair K β hβ v) :=
  ofTruncZero hz

/-- PROVED. `ActLTZ` is transported along equalities of conditions. -/
theorem actLTZ_congr {v : Places K S} {A A₀ : CondAt K S R M v} {B B₀ : CondAt K S R M' v}
    (hA : A = A₀) (hB : B = B₀) (h : ActLTZ β hβ A₀ B₀) : ActLTZ β hβ A B := by
  subst hA hB
  exact h

/-- PROVED (Nekovář 6.2.1.5). **Two conditions concentrated in degrees `0, 1` whose `(1, 1)`
products are coboundaries satisfy `ActLTZ`.** -/
theorem actLTZ_of_conc {v : Places K S} {A : CondAt K S R M v} {B : CondAt K S R M' v}
    (hA : OrthConcentratedAt A) (hB : OrthConcentratedAt B) (h11 : OrthIsotropicAt β hβ A B) :
    ActLTZ β hβ A B := by
  intro a b c h u w
  change (truncSub _ c).mkQ ((orthGaloisPair K β hβ v).P a b c h (A.i.f a a rfl u)
    (B.i.f b b rfl w)) = 0
  by_cases ha : a = 0 ∨ a = 1
  · by_cases hb : b = 0 ∨ b = 1
    · by_cases hc : c ≤ 1
      · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_le _ hc]
        trivial
      · obtain rfl : a = 1 := by omega
        obtain rfl : b = 1 := by omega
        obtain rfl : c = 2 := by omega
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_eq _ rfl]
        exact h11 u w
    · have : Subsingleton (B.U.X b) := hB b (by omega) (by omega)
      rw [Subsingleton.elim w 0]
      simp
  · have : Subsingleton (A.U.X a) := hA a (by omega) (by omega)
    rw [Subsingleton.elim u 0]
    simp

/-- PROVED (tex 2813–2814: "A full condition is paired with the zero condition"). **Any condition
against the zero condition satisfies `ActLTZ`** (the dual inclusion is zero). -/
theorem actLTZ_zero {v : Places K S} (A : CondAt K S R M v) :
    ActLTZ β hβ A (zeroAt K S R M' v) := by
  intro a b c h u w
  change (truncSub _ c).mkQ ((orthGaloisPair K β hβ v).P a b c h (A.i.f a a rfl u)
    ((0 : _ →ₗ[R] _) w)) = 0
  rw [LinearMap.zero_apply, map_zero, map_zero]

variable {L E : GCx R}

/-- PROVED. **Per-place quasi-isomorphy for every isotropy homotopy is transported along
equalities of conditions** (no concentration needed). -/
theorem actLPerf_congr {v : Places K S} {A A₀ : CondAt K S R M v} {B B₀ : CondAt K S R M' v}
    (hA : A = A₀) (hB : B = B₀)
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (h : ∀ J₀ : LocalTruncIsotropy A₀.i B₀.i (orthGaloisPair K β hβ v),
      QuasiIso (GHom.toCC (orthLocalMap A₀.i B₀.i (orthGaloisPair K β hβ v) J₀ trv htrv)))
    (J : LocalTruncIsotropy A.i B.i (orthGaloisPair K β hβ v)) :
    QuasiIso (GHom.toCC (orthLocalMap A.i B.i (orthGaloisPair K β hβ v) J trv htrv)) := by
  subst hA hB
  exact h J

/-- PROVED (tex 2813–2814; round 1's `orthLocalMap_full_zero_quasiIso`). **The full condition is
the orthogonal complement of the zero condition at every place**, for every isotropy homotopy and
every trace: both sides of the per-place local duality map are acyclic. -/
theorem actLPerf_full_zero (v : Places K S)
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (J : LocalTruncIsotropy (fullAt K S R M v).i (zeroAt K S R M' v).i (orthGaloisPair K β hβ v)) :
    QuasiIso (GHom.toCC (orthLocalMap (fullAt K S R M v).i (zeroAt K S R M' v).i
      (orthGaloisPair K β hβ v) J trv htrv)) :=
  orthLocalMap_full_zero_quasiIso (orthGaloisPair K β hβ v) J trv htrv

end TruncZero

/-! ### The actual conditions -/

section Actual

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (P : Set (HeightOneSpectrum (𝓞 K)))
  [NeZero i] [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)

/-- Definition (tex 2754–2756, 3080–3085, 3483–3498). **The actual local conditions on `M_i(α)`**:
the Kummer condition at the places of `P` (above `2N`), the full condition at the other places of
`S₀` (the active and the moving primes), the unramified condition at `S − S₀`. -/
abbrev actLCondA : ∀ v : Places K S, CondAt K S (Acoef i) (MinS hS W i α) v :=
  urOutside hS (Acoef i) (Mcoef K S₀ W i α)
    (kummerCondA hS W i s hs hs0 hFull P α hα fun v _ _ => fullAt K S (Acoef i) (MinS hS W i α) v)

/-- Definition (tex 2810–2816). **The orthogonal local conditions on `M_i(α⁻¹) ≅ M_i^*(1)`**: the
Kummer condition at `P`, the zero condition at the other places of `S₀` (paired with the full
condition), the unramified condition at `S − S₀`. -/
abbrev actLCondB : ∀ v : Places K S, CondAt K S (Acoef i) (MinS hS W i (charInv α)) v :=
  urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
    (kummerCondB hS W i s hs hs0 hFull P α hα fun v _ _ =>
      zeroAt K S (Acoef i) (MinS hS W i (charInv α)) v)

/-- The coefficient pairing: lane RC28's Weil pairing `M_i(α) × M_i(α⁻¹) → A_i(1)`, inflated. -/
abbrev actLBeta := orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)

theorem actLBeta_smul (g : GKS K S) (a : MinS hS W i α) (b : MinS hS W i (charInv α)) :
    actLBeta hS W i α hμ₀ (g • a) (g • b) = g • actLBeta hS W i α hμ₀ a b :=
  orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) g a b

open scoped Classical in
/-- PROVED. At a place of `P`, the condition is the actual Kummer condition. -/
theorem actLCondA_of_P {v : Places K S} (hv : v.1 ∈ S₀) (hP : v.1 ∈ P) :
    actLCondA hS W i s hs hs0 hFull P α hα v = actualKummerAtS hS W i s hs hs0 α hFull v (hα v.1 hP) :=
  (dite_eq_left hv).trans (kummerCondA_of_mem hS W i s hs hs0 hFull P α hα _ hv hP)

open scoped Classical in
/-- PROVED. At a place of `P`, the orthogonal condition is the actual Kummer condition. -/
theorem actLCondB_of_P {v : Places K S} (hv : v.1 ∈ S₀) (hP : v.1 ∈ P) :
    actLCondB hS W i s hs hs0 hFull P α hα v =
      actualKummerAtS hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv (hα v.1 hP)) :=
  (dite_eq_left hv).trans (kummerCondB_of_mem hS W i s hs hs0 hFull P α hα _ hv hP)

/-- PROVED. At the other places of `S₀`, the condition is the full condition. -/
theorem actLCondA_of_notP {v : Places K S} (hv : v.1 ∈ S₀) (hP : v.1 ∉ P) :
    actLCondA hS W i s hs hs0 hFull P α hα v = fullAt K S (Acoef i) (MinS hS W i α) v :=
  (dite_eq_left hv).trans (kummerCondA_of_not_mem hS W i s hs hs0 hFull P α hα _ hv hP)

/-- PROVED. At the other places of `S₀`, the orthogonal condition is the zero condition. -/
theorem actLCondB_of_notP {v : Places K S} (hv : v.1 ∈ S₀) (hP : v.1 ∉ P) :
    actLCondB hS W i s hs hs0 hFull P α hα v = zeroAt K S (Acoef i) (MinS hS W i (charInv α)) v :=
  (dite_eq_left hv).trans (kummerCondB_of_not_mem hS W i s hs hs0 hFull P α hα _ hv hP)

/-- PROVED. Outside `S₀`, the condition is the unramified condition. -/
theorem actLCondA_of_notS0 {v : Places K S} (hv : v.1 ∉ S₀) :
    actLCondA hS W i s hs hs0 hFull P α hα v = urAt hS (Acoef i) (Mcoef K S₀ W i α) v hv :=
  dite_eq_right hv

/-- PROVED. Outside `S₀`, the orthogonal condition is the unramified condition. -/
theorem actLCondB_of_notS0 {v : Places K S} (hv : v.1 ∉ S₀) :
    actLCondB hS W i s hs hs0 hFull P α hα v =
      urAt hS (Acoef i) (Mcoef K S₀ W i (charInv α)) v hv :=
  dite_eq_right hv

/-- Definition. The actual local conditions on `M_i(α)` as lane RC26's Galois local conditions. -/
def actLDeltaA : GaloisLocalConditions K S (Acoef i) (MinS hS W i α) :=
  ofCondAt K S (Acoef i) (MinS hS W i α) (actLCondA hS W i s hs hs0 hFull P α hα)

/-- Definition. The orthogonal local conditions on `M_i(α⁻¹)` as lane RC26's Galois local
conditions. -/
def actLDeltaB : GaloisLocalConditions K S (Acoef i) (MinS hS W i (charInv α)) :=
  ofCondAt K S (Acoef i) (MinS hS W i (charInv α)) (actLCondB hS W i s hs hs0 hFull P α hα)

variable (trv : ∀ v : Places K S, (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
  (htrv : ∀ v z, trv v ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)

open scoped Classical in
include htrv in
/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` at the Kummer places (tex
3418–3419, 3439–3448), trivially at the full/zero places (tex 2813–2814), and from Nekovář's
Lemma 7.5.2 at the unramified places (PROVED in round 1). **At every place the restricted cup
product of the actual conditions vanishes after `τ≥2`.** -/
theorem actLTZ_actual (hM : MilneLocalTateDualityKummerCharZero)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v)) (v : Places K S) :
    ActLTZ (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
      (actLCondA hS W i s hs hs0 hFull P α hα v) (actLCondB hS W i s hs hs0 hFull P α hα v) := by
  by_cases hv : v.1 ∈ S₀
  · by_cases hP : v.1 ∈ P
    · refine actLTZ_congr _ _ (actLCondA_of_P hS W i s hs hs0 hFull P α hα hv hP)
        (actLCondB_of_P hS W i s hs hs0 hFull P α hα hv hP) (actLTZ_of_conc _ _ ?_ ?_ ?_)
      · have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        exact orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v (hα v.1 hP))
      · have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        exact orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
          (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv (hα v.1 hP)))
      · exact kummerPerPlace_isotropic_of_milne hS W i s hs hs0 hFull v hμ₀ α hM (hα v.1 hP) (trv v)
          (htrv v) (htrv2 v)
    · rw [actLCondB_of_notP hS W i s hs hs0 hFull P α hα hv hP]
      exact actLTZ_zero _ _ _
  · refine actLTZ_congr _ _ (actLCondA_of_notS0 hS W i s hs hs0 hFull P α hα hv)
      (actLCondB_of_notS0 hS W i s hs hs0 hFull P α hα hv) (actLTZ_of_conc _ _
        (orth_urAt_vanishes hS (Acoef i) (Mcoef K S₀ W i α) v hv)
        (orth_urAt_vanishes hS (Acoef i) (Mcoef K S₀ W i (charInv α)) v hv)
        (orthUr_cup_mem_range hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
          (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v hv))

include htrv in
/-- Definition. **The isotropy homotopies of the actual conditions**: the zero homotopy at every
place (`actLTZ_actual`). -/
def actLIso (hM : MilneLocalTateDualityKummerCharZero)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v)) (v : Places K S) :
    LocalTruncIsotropy (actLCondA hS W i s hs hs0 hFull P α hα v).i
      (actLCondB hS W i s hs hs0 hFull P α hα v).i
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v) :=
  actLIsoOf _ _ (actLTZ_actual hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2 v)

include htrv in
/-- Definition. The `τ≥2` isotropy data of the actual conditions (lane RC26's
`TruncIsotropyData.ofLocal` of `actLIso`). -/
def actLTrunc (hM : MilneLocalTateDualityKummerCharZero)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v)) :
    GaloisTruncIsotropyData K S (Acoef i) (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
      (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα) :=
  TruncIsotropyData.ofLocal
    (ΔA := ofCondAt K S (Acoef i) (MinS hS W i α) (actLCondA hS W i s hs hs0 hFull P α hα))
    (ΔB := ofCondAt K S (Acoef i) (MinS hS W i (charInv α)) (actLCondB hS W i s hs hs0 hFull P α hα))
    (actLIso hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2)

open scoped Classical in
/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524` (at the Kummer
places) and `NekovarProp756` (at the unramified places), the GLUE `FullTorsion` and `hT` (PROVED,
`cycloInfl_isCyclotomicTwist_tate1`). **The per-place local duality map of the actual conditions is
a quasi-isomorphism at every place of `S`**, for every isotropy homotopy. -/
theorem actLPerf (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K)
    (h756 : NekovarProp756 K) (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v)) (v : Places K S)
    (J : LocalTruncIsotropy (actLCondA hS W i s hs hs0 hFull P α hα v).i
      (actLCondB hS W i s hs hs0 hFull P α hα v).i
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v)) :
    QuasiIso (GHom.toCC (orthLocalMap (actLCondA hS W i s hs hs0 hFull P α hα v).i
      (actLCondB hS W i s hs hs0 hFull P α hα v).i
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v) J (trv v)
      (htrv v))) := by
  by_cases hv : v.1 ∈ S₀
  · by_cases hP : v.1 ∈ P
    · exact actLPerf_congr _ _ (actLCondA_of_P hS W i s hs hs0 hFull P α hα hv hP)
        (actLCondB_of_P hS W i s hs hs0 hFull P α hα hv hP) (trv v) (htrv v)
        (fun J₀ => kummerPerPlace_perf_of_milne hS W i s hs hs0 hFull v hμ₀ α hM h524 hK hSfin h2₀
          (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀) (hα v.1 hP) (trv v) (htrv v) (htrv2 v) J₀) J
    · exact actLPerf_congr _ _ (actLCondA_of_notP hS W i s hs hs0 hFull P α hα hv hP)
        (actLCondB_of_notP hS W i s hs hs0 hFull P α hα hv hP) (trv v) (htrv v)
        (actLPerf_full_zero _ _ v (trv v) (htrv v)) J
  · exact actLPerf_congr _ _ (actLCondA_of_notS0 hS W i s hs hs0 hFull P α hα hv)
      (actLCondB_of_notS0 hS W i s hs hs0 hFull P α hα hv) (trv v) (htrv v)
      (fun J₀ => orthUr_quasiIso_of_print h756 hS 2 (nekovarFiniteSetting_acoef K hK S₀ hS₀fin h2₀ i)
        (weilPairingM (S := S₀) W hμ₀ (Acoef i) α) (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α)
        (weilPairingM_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
        (weilPairingM_flip_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
        (isCyclotomicTwist_tate1 (Acoef i) hμ₀) v hv J₀ (trv v) (htrv v) (htrv2 v)) J

/-- Definition. The truncated compact cone of the actual data, the domain of the global trace. -/
abbrev actLTT (hM : MilneLocalTateDualityKummerCharZero)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v)) : GCx (Acoef i) :=
  galoisCompactTT K S (Acoef i) (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
    (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα)
    (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2)

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero` (Milne, *ADT* 2nd ed., I.2.3,
I.3.2, I.3.4, I.3.5), `NekovarProp524` (Nekovář 5.2.4) and `NekovarProp756` (Nekovář 7.5.6 with
7.5.5), the GLUE `FullTorsion` (lane RC28), the ELLIOT `hα` (tex 2729, 3431, 3500–3506) and the
traces of lane RC26 (`InducesIsoH2` at every place, `hsum`; Nekovář 5.4.1) (tex 2754–2756,
2810–2816, 3080–3085, 3413–3468, 3483–3498). **The local complement criterion for the actual
Selmer data at every place of `S`**: the actual conditions (Kummer at the places above `2N`, full
at the active and moving primes, unramified at `S − S₀`) and their orthogonal conditions (Kummer,
zero, unramified) are orthogonal complements — lane RC26's `OrthogonalComplementsT`, the hypothesis
`horth` of `genuineSelmerDualityT` — with no per-place input left. -/
theorem actualLocalComplements [Fintype (Places K S)] (hM : MilneLocalTateDualityKummerCharZero)
    (h524 : NekovarProp524 K) (h756 : NekovarProp756 K) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (hS₀fin : S₀.Finite) (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v))
    (tr : (actLTT hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((actLTT hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    OrthogonalComplementsT K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
      (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα)
      (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2) tr htr :=
  orthogonalComplementsT_ofCondAt K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
    (actLCondA hS W i s hs hs0 hFull P α hα) (actLCondB hS W i s hs hs0 hFull P α hα)
    (actLIso hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2) trv htrv tr htr hsum
    (fun v => actLPerf hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM h524 h756 hK hSfin hS₀fin h2₀
      htrv2 v _)

/-- PROVED from the PRINTs of `actualLocalComplements` and `NekovarProp543T` (Nekovář 5.4.3 with
6.3–6.4), with `InducesIsoH3 tr` (tex 2761–2830, 3454–3463). **The finite Selmer duality for the
actual data**, `C_U(M_i) ≃ RHom(C_{U⊥}(M_i^*(1)), A_i)[−3]`: lane RC26's Selmer duality map of the
actual conditions and their orthogonal conditions is a quasi-isomorphism (RC26's consumer
`genuineSelmerDualityT` fed with `actualLocalComplements`). -/
theorem actualSelmerDuality [Fintype (Places K S)] (hM : MilneLocalTateDualityKummerCharZero)
    (h524 : NekovarProp524 K) (h543 : NekovarProp543T K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v))
    (tr : (actLTT hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((actLTT hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i) (actLBeta hS W i α hμ₀)
      (actLBeta_smul hS W i α hμ₀) (actLDeltaA hS W i s hs hs0 hFull P α hα)
      (actLDeltaB hS W i s hs hs0 hFull P α hα)
      (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2)) tr htr)) :=
  haveI : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  haveI : Finite (MinS hS W i (charInv α)) := inferInstanceAs (Finite (Mcoef K S₀ W i (charInv α)))
  genuineSelmerDualityT K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
    (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα)
    (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2) tr htr h543 2
    (nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i)
    (weilPairingM_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
    (weilPairingM_flip_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
    (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀) htr3
    (actualLocalComplements hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM h524 h756 hK hSfin hS₀fin
      h2₀ htrv2 tr htr hsum)

/-- Definition. **The conclusion for a packet `L` and a global trace `tr`**: the actual conditions
and their orthogonal conditions are orthogonal complements (`OrthogonalComplementsT`, RC26's `horth`)
and lane RC26's Selmer duality map is a quasi-isomorphism. -/
def ActLDuality (hM : MilneLocalTateDualityKummerCharZero)
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (tr : (actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).d 2 3 rfl
      z) = 0) : Prop :=
  OrthogonalComplementsT K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
      (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα)
      (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso) tr htr ∧
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
      (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα)
      (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso)) tr htr))

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524`,
`NekovarProp543T`, `NekovarProp756`, the GLUE `FullTorsion` and the ELLIOT `hα`. **The actual
local complements and the finite Selmer duality for a packet of local traces** and a global trace
normalized by it, inducing `H³_c ≅ A_i`. -/
theorem actualSelmerDuality_packet [Fintype (Places K S)]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K) (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (tr : (actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).d 2 3 rfl
      z) = 0)
    (hN : L.Normalizes tr) (h3 : InducesIsoH3 tr) :
    ActLDuality hS W i s hs hs0 hFull P α hμ₀ hα hM L tr htr :=
  ⟨actualLocalComplements hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM h524 h756 hK hSfin
      hS₀fin h2₀ L.iso tr htr hN,
    actualSelmerDuality hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM h524 h543 h756 hK hSfin
      hS₀fin h2₀ L.iso tr htr hN h3⟩

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524`,
`NekovarProp543T`, `NekovarProp756` and `NekovarFiniteTraces` (Nekovář 5.1.3, 5.1.5, 5.2.1, 5.4.1),
the GLUE `FullTorsion` and the ELLIOT `hα` (tex 2761–2830, 3413–3468, 3483–3498). **The actual
local complements and the finite Selmer duality, with the traces of the packet**: there are local
traces `L` (one family for `A_i(1)` over `G_{K,S}`) and a global trace `tr` killing coboundaries,
inducing `H³_c(G_{K,S}, A_i(1)) ≅ A_i` and normalized by `L`, for which the actual conditions and
their orthogonal conditions are orthogonal complements (`OrthogonalComplementsT`) and lane RC26's
Selmer duality map is a quasi-isomorphism (`ActLDuality`). No per-place input is left. -/
theorem actualSelmerDuality_of_prints [Fintype (Places K S)]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K) (hTr : NekovarFiniteTraces K) (hK : IsTotallyComplex K)
    (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∃ (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
      (tr : (actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).X 3 →ₗ[Acoef i]
        Acoef i)
      (htr : ∀ z, tr ((actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).d 2 3 rfl
        z) = 0),
      InducesIsoH3 tr ∧ L.Normalizes tr ∧ ActLDuality hS W i s hs hs0 hFull P α hμ₀ hα hM L tr htr := by
  have hset := nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i
  have hT := cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀
  obtain ⟨L, hL⟩ := @hTr S 2 (Acoef i) _ _ hset _ (InflMod hS (Tate1 (Acoef i) hμ₀)) _ _ _ _ _ _ _ hT
  refine ⟨L, ?_⟩
  have h1 := hL (MinS hS W i α) (MinS hS W i (charInv α))
    (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
    (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα)
    (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso)
  exact h1.imp fun tr => Exists.imp fun htr hP => ⟨hP.1, hP.2,
    actualSelmerDuality_packet hS W i s hs hs0 hFull P α hμ₀ hα hM h524 h543 h756 hK hSfin hS₀fin
      h2₀ L tr htr hP.2 hP.1⟩

end Actual

end ZInQ.Manuscript.RC.KummerMaps
