import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerSelmer
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ConjInfl

/-!
# Lane RC29, round 3 (D4): the transported dual conditions are the orthogonal complements

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830), tex
2798–2816:

> The Weil pairing gives the following `R_i`-linear perfect pairing:
> `M_i ⊗ τ^*M_i → R_i(1)`, `(v, w) ↦ e₂(v, ρ_T(τ)w)`. […] At a split place `v`, the dual local
> condition is transported from the conjugate place `τv`. At a fixed place it is transported by
> the actual local representative of conjugation. Kummer conditions at `2N` are preserved by this
> transport. A full condition is paired with the zero condition; […]

with the actual conditions of tex 2754–2756 and 3084–3085 ("At active and moving primes the
required condition is full") and the unramified conditions at the new places (tex 3483–3498).
Round 2 left open (gap D4) that the transported dual conditions are the orthogonal complements.
This file proves it, in lane RC26's consumer shape `OrthogonalComplementsT`:

* **The model.** The dual family lives on `Infl(τ₀^*M_{i,0})`, which is `τ^*MinS` through round 2's
  `conjInflPullEquiv` (the identity map), with **the text's pairing** `(v, w) ↦ e(v, ρ_T(τ)w)`
  (lane RC28's `conjPairing` over `S₀`, inflated: `conjCPair`, `conjCβ`). The transport of a
  condition at `τv` to `v` is round 1's `conjTransport` with the inner element `conjCElt` adapted
  to lane RC29's decomposition embeddings `decompEmb` (`conjCTransport`).
* **(a) Coefficient change** (`conjC_cup_coef`, `conjCCoefIsotropy`, `conjC_orthLocalMap_coef`,
  `conjC_quasiIso_coef_iff`, `conjC_isotropic_coef_iff`): pushing the dual condition along an
  equivariant `φ` with `β''(a, φ b) = β'(a, b)` does not change the per-place local duality map.
* **(b) Iso invariance** (`conjC_orthLocalMap_iso`, `conjC_quasiIso_of_condIso`,
  `conjC_isotropic_of_condIso`): for conditions concentrated in degrees `0, 1`, per-place
  orthogonality transfers along round 2's isomorphisms of local conditions `ConjKCondIso`.
* **(c) Unit scaling** (`conjC_kummerAt_smul`): the Kummer condition through `u • ι` is the one
  through `ι`; with the inflated comparison `conjC_iota_eq` (`conjToInv ∘ ι^τ = α(h̄₀)⁻¹ ε • ι_v`)
  the transported Kummer condition becomes the actual Kummer condition of `M_i(α⁻¹)`
  (`conjCKummerIso`).
* **(d) Per place**: Kummer places `conjC_kummer_quasiIso` (from lane RC29's
  `kummerPerPlace_perf_of_milne`), full/zero places (the transported zero condition is the zero
  condition, `conjCTransport_zeroAt`; lane RC29's `orthLocalMap_fullAt_zeroAt_quasiIso`),
  unramified places (PRINT `NekovarProp756` through `orthUr_quasiIso_of_print`); all for every
  isotropy homotopy (`conjC_perPlace`).
* **The theorem** `conjActualLocalComplements`: for `ΔA` = Kummer at `P`, full at `S₀ − P`,
  unramified at `S − S₀` on `M_i = MinS`, and `ΔB` = the transported dual family (`conjCFamB`),
  with the zero isotropy homotopies (`conjCTrunc`, built by `ofTruncZero` — at the full/zero
  places all restricted products vanish because the dual inclusion is zero),
  `OrthogonalComplementsT`. Corollary `conjActualSelmerDuality`: the finite Selmer duality
  `C_U(M_i) ≃ RHom(C_{U⊥}(τ^*M_i), A_i)[−3]` (tex 2825–2829) through lane RC26's
  `genuineSelmerDualityT`.

Kinds: DEF and PROVED; the PRINTs used are `MilneLocalTateDualityKummerCharZero` (Milne),
`NekovarProp524`, `NekovarProp756`, `NekovarProp543T` (Nekovář), all existing. Hypotheses, with
kinds and tex lines, are listed at `conjActualLocalComplements`; non-vacuity of the new ones:
`conjC_stable_nonvacuous` (`κ`-stability of `S₀` and `P`), `conjC_hα₀_nonvacuous`,
`conjC_hμ₀_of_fullTorsion`. No new structure or predicate is introduced.

DEPARTURES (form): (1) the dual module is `Infl(τ₀^*M_{i,0})` (the inflation of `τ^*` over `S₀`;
equal to `τ^*MinS` by round 2's `conjInflPullEquiv`) so that the unramified conditions at `S − S₀`
are lane RC28's `urAt`; (2) the inner element of the transport is `conjCElt`, adapted to lane
RC29's decomposition embeddings (round 1's DEPARTURE D1: the text has no inner element; with
round 1's canonical element the transported coefficient map would differ from a unit multiple of
`ι_v` by a non-scalar centralizing element); (3) the transport is used at every place of `S₀`
through the conjugate place `τv = locConjPlaceS C v`, which at a fixed place is `v` itself
(round 1's `conjTransport_eq_rep`: the transport by the local representative of conjugation).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs resUnr_comp)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom GPair sgn coneCx coneT)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (ghomComp idGHom zeroGHom GHom.toCC GHom.toCC_f_apply
  GHom.toCC_comp GHom.toCC_ext dualCx dualCx_ext asDual dualHom selmerDualityMap)
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy MilneLocalTateDualityKummerCharZero
  pullPair ofTruncZero)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (truncSub truncPair truncSub_of_le truncSub_of_eq)

/-! ### (a) Change of coefficients of the dual condition -/

section CoefChange

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M M' M'' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup M''] [Module R M''] [DistribMulAction (GKS K S) M'']
  [SMulCommClass (GKS K S) R M''] [TopologicalSpace M''] [DiscreteTopology M'']
  [ContinuousSMul (GKS K S) M'']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β' : M →ₗ[R] M' →ₗ[R] T)
  (hβ' : ∀ (g : GKS K S) (a : M) (b : M'), β' (g • a) (g • b) = g • β' a b)
  (β'' : M →ₗ[R] M'' →ₗ[R] T)
  (hβ'' : ∀ (g : GKS K S) (a : M) (b : M''), β'' (g • a) (g • b) = g • β'' a b)
  (φ : M' ≃ₗ[R] M'') (hφ : ∀ (σ : GKS K S) (m : M'), φ (σ • m) = σ • φ m)
  (hcomp : ∀ a b, β'' a (φ b) = β' a b)

include hφ hcomp in
/-- PROVED. **The cup product is compatible with a change of coefficients of the second factor**
(degrees in `ℕ`): for an equivariant `φ : M' ≃ M''` and pairings with `β''(a, φ b) = β'(a, b)`
(hypothesis `hcomp`), `x ∪_{β''} φ_*(y) = x ∪_{β'} y` on the continuous cochains of `G_{K_v}`. -/
theorem conjC_cup_coef_nat (v : Places K S) (p q n : ℕ) (h : p + q = n)
    (x : (contCochains R (Gloc K v.1) (ResMod (locMap K S v.1) M)).X p)
    (y : (contCochains R (Gloc K v.1) (ResMod (locMap K S v.1) M')).X q) :
    contCup (resPairing R (GKS K S) β'' (locMap K S v.1))
        (resPairing_continuous R (GKS K S) β'' (continuous_pairing β'') (locMap K S v.1)) p q n h x
        (((conjTransportCoefIso φ hφ v.1).hom.f q).hom y) =
      contCup (resPairing R (GKS K S) β' (locMap K S v.1))
        (resPairing_continuous R (GKS K S) β' (continuous_pairing β') (locMap K S v.1)) p q n h x
        y := by
  have key : ∀ (hh : Gloc K v.1) (a : ResMod (locMap K S v.1) M)
      (m : ResMod (locMap K S v.1) M'),
      resPairing R (GKS K S) β'' (locMap K S v.1) a (hh • conjTransportCoefEquiv φ v.1 m) =
        resPairing R (GKS K S) β' (locMap K S v.1) a (hh • m) := fun hh a m => by
    change β'' (show M from a) (locMap K S v.1 hh • φ (show M' from m)) =
      β' (show M from a) (locMap K S v.1 hh • (show M' from m))
    rw [← hφ]
    exact hcomp _ _
  apply Subtype.ext
  change cupFun (resPairing R (GKS K S) β'' (locMap K S v.1)) p q n h (cFun x)
      (cFun (((conjTransportCoefIso φ hφ v.1).hom.f q).hom y)) =
    cupFun (resPairing R (GKS K S) β' (locMap K S v.1)) p q n h (cFun x) (cFun y)
  funext g
  rw [cupFun_apply, cupFun_apply]
  exact key _ _ _

include hφ hcomp in
/-- PROVED. `conjC_cup_coef_nat` for the `ℤ`-indexed local cup products (zero outside nonnegative
degrees). -/
theorem conjC_cup_coef (v : Places K S) :
    ∀ (i j l : ℤ) (h : i + j = l) (x : (locAt K S R M v).X i) (y : (locAt K S R M' v).X j),
      (orthGaloisPair K β'' hβ'' v).P i j l h x
          ((natHom (conjTransportCoefIso φ hφ v.1).hom).f j j rfl y) =
        (orthGaloisPair K β' hβ' v).P i j l h x y
  | Int.ofNat p, Int.ofNat q, Int.ofNat n, h, x, y =>
      conjC_cup_coef_nat β' β'' φ hφ hcomp v p q n (by simp only [Int.ofNat_eq_natCast] at h; omega)
        x y
  | Int.ofNat _, Int.ofNat _, Int.negSucc _, _, _, _ => rfl
  | Int.ofNat _, Int.negSucc _, _, _, _, _ => rfl
  | Int.negSucc _, _, _, _, _, _ => rfl

variable {v : Places K S} (c : CondAt K S R M v) (c' : CondAt K S R M' v)

/-- DEF. **An isotropy homotopy for `(c, c')` and `β'` is one for `(c, φ_* c')` and `β''`** (the
same homotopy; the isotropy identities transfer by `conjC_cup_coef`). -/
def conjCCoefIsotropy (J : LocalTruncIsotropy c.i c'.i (orthGaloisPair K β' hβ' v)) :
    LocalTruncIsotropy c.i (conjTransportCoef φ hφ c').i (orthGaloisPair K β'' hβ'' v) where
  h := J.h
  isotropy₂ i i₁ j j₁ hh hi hj u y := by
    have e := conjC_cup_coef β' hβ' β'' hβ'' φ hφ hcomp v i j 2 hh (c.i.f i i rfl u)
      (c'.i.f j j rfl y)
    change J.h i₁ j 2 _ (c.U.d i i₁ hi u) y + sgn i • J.h i j₁ 2 _ u (c'.U.d j j₁ hj y) -
      (orthGaloisPair K β'' hβ'' v).P i j 2 hh (c.i.f i i rfl u)
        ((natHom (conjTransportCoefIso φ hφ v.1).hom).f j j rfl (c'.i.f j j rfl y)) ∈ _
    rw [e]
    exact J.isotropy₂ i i₁ j j₁ hh hi hj u y
  isotropy₃ i i₁ j j₁ k k₁ hh hi hj hk h3 u y := by
    have e := conjC_cup_coef β' hβ' β'' hβ'' φ hφ hcomp v i j k₁ (by omega) (c.i.f i i rfl u)
      (c'.i.f j j rfl y)
    change _ = (orthGaloisPair K β'' hβ'' v).P i j k₁ _ (c.i.f i i rfl u)
        ((natHom (conjTransportCoefIso φ hφ v.1).hom).f j j rfl (c'.i.f j j rfl y))
    rw [e]
    exact J.isotropy₃ i i₁ j j₁ k k₁ hh hi hj hk h3 u y

/-- PROVED. **(a) Coefficient change** (tex 2798–2805: `τ^*M_i ≃ M_i^*(1)` through `conjToInv`): the
per-place local duality maps of `(c, φ_* c')` for `β''` and of `(c, c')` for `β'` are equal. -/
theorem conjC_orthLocalMap_coef (J : LocalTruncIsotropy c.i c'.i (orthGaloisPair K β' hβ' v))
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T
      v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0) :
    GHom.toCC (orthLocalMap c.i (conjTransportCoef φ hφ c').i (orthGaloisPair K β'' hβ'' v)
        (conjCCoefIsotropy β' hβ' β'' hβ'' φ hφ hcomp c c' J) trv htrv) =
      GHom.toCC (orthLocalMap c.i c'.i (orthGaloisPair K β' hβ' v) J trv htrv) := by
  refine GHom.toCC_ext fun i z => dualCx_ext fun y => ?_
  obtain ⟨u, x⟩ := z
  have e1 := orthLocalMap_apply c.i (conjTransportCoef φ hφ c').i (orthGaloisPair K β'' hβ'' v)
    (conjCCoefIsotropy β' hβ' β'' hβ'' φ hφ hcomp c c' J) trv htrv i i rfl u x y
  have e2 := orthLocalMap_apply c.i c'.i (orthGaloisPair K β' hβ' v) J trv htrv i i rfl u x y
  refine e1.trans (Eq.trans ?_ e2.symm)
  have e := conjC_cup_coef β' hβ' β'' hβ'' φ hφ hcomp v (i - 1) (3 - i) 2 (by omega) x
    (c'.i.f (3 - i) (3 - i) rfl y)
  change trv ((orthGaloisPair K β'' hβ'' v).P (i - 1) (3 - i) 2 _ x
      ((natHom (conjTransportCoefIso φ hφ v.1).hom).f (3 - i) (3 - i) rfl
        (c'.i.f (3 - i) (3 - i) rfl y)) + J.h i (3 - i) 2 _ u y) = _
  rw [e]

/-- PROVED. **(a)** The per-place quasi-isomorphy of `(c, φ_* c')` for `β''` is that of `(c, c')`
for `β'`. -/
theorem conjC_quasiIso_coef_iff (J : LocalTruncIsotropy c.i c'.i (orthGaloisPair K β' hβ' v))
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T
      v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0) :
    QuasiIso (GHom.toCC (orthLocalMap c.i (conjTransportCoef φ hφ c').i
        (orthGaloisPair K β'' hβ'' v) (conjCCoefIsotropy β' hβ' β'' hβ'' φ hφ hcomp c c' J) trv
          htrv)) ↔
      QuasiIso (GHom.toCC (orthLocalMap c.i c'.i (orthGaloisPair K β' hβ' v) J trv htrv)) :=
  ⟨fun h => by rwa [conjC_orthLocalMap_coef] at h, fun h => by rwa [conjC_orthLocalMap_coef]⟩

include hcomp in
/-- PROVED. **(a)** `OrthIsotropicAt` transfers along the coefficient change. -/
theorem conjC_isotropic_coef_iff :
    OrthIsotropicAt β'' hβ'' c (conjTransportCoef φ hφ c') ↔ OrthIsotropicAt β' hβ' c c' := by
  refine forall_congr' fun u => forall_congr' fun y => ?_
  have e := conjC_cup_coef β' hβ' β'' hβ'' φ hφ hcomp v 1 1 2 rfl (c.i.f 1 1 rfl u)
    (c'.i.f 1 1 rfl y)
  change (orthGaloisPair K β'' hβ'' v).P 1 1 2 rfl (c.i.f 1 1 rfl u)
      ((natHom (conjTransportCoefIso φ hφ v.1).hom).f 1 1 rfl (c'.i.f 1 1 rfl y)) ∈ _ ↔ _
  rw [e]

end CoefChange

/-! ### (b) Invariance under isomorphisms of the dual condition -/

section IsoInvariance

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
  {v : Places K S} (c : CondAt K S R M v) {c₁ c₂ : CondAt K S R M' v}

omit [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T] in
/-- PROVED. The dual `Hom(U₂, R)[−m] → Hom(U₁, R)[−m]` of an isomorphism of local conditions `U₁ ≅
U₂` (`ConjKCondIso`, round 2) is an isomorphism of complexes. -/
theorem conjC_dualHom_isIso (I : ConjKCondIso c₁ c₂) (m : ℤ) :
    IsIso (GHom.toCC (dualHom I.hom m)) := by
  refine ⟨⟨GHom.toCC (dualHom I.inv m), ?_, ?_⟩⟩
  · ext n f
    refine dualCx_ext fun y => ?_
    change asDual f (I.hom.f (m - n) (m - n) rfl (I.inv.f (m - n) (m - n) rfl y)) = asDual f y
    rw [I.hom_inv]
  · ext n f
    refine dualCx_ext fun y => ?_
    change asDual f (I.inv.f (m - n) (m - n) rfl (I.hom.f (m - n) (m - n) rfl y)) = asDual f y
    rw [I.inv_hom]

/-- PROVED. **(b) Iso invariance**: for conditions concentrated in degrees `0, 1` and `c₁ ≅ c₂`
(`ConjKCondIso`), the per-place local duality map of `(c, c₁)` is that of `(c, c₂)` followed by the
dual of `c₁ ≅ c₂`, for any two isotropy homotopies (they only enter in total degree `3`, where one
factor vanishes). -/
theorem conjC_orthLocalMap_iso (I : ConjKCondIso c₁ c₂) (hc : OrthConcentratedAt c)
    (hc₁ : OrthConcentratedAt c₁)
    (J₁ : LocalTruncIsotropy c.i c₁.i (orthGaloisPair K β hβ v))
    (J₂ : LocalTruncIsotropy c.i c₂.i (orthGaloisPair K β hβ v))
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T
      v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0) :
    GHom.toCC (orthLocalMap c.i c₁.i (orthGaloisPair K β hβ v) J₁ trv htrv) =
      GHom.toCC (orthLocalMap c.i c₂.i (orthGaloisPair K β hβ v) J₂ trv htrv) ≫
        GHom.toCC (dualHom I.hom 3) := by
  rw [GHom.toCC_comp]
  refine GHom.toCC_ext fun i z => dualCx_ext fun y => ?_
  obtain ⟨u, x⟩ := z
  have e1 := orthLocalMap_apply c.i c₁.i (orthGaloisPair K β hβ v) J₁ trv htrv i i rfl u x y
  have e2 := orthLocalMap_apply c.i c₂.i (orthGaloisPair K β hβ v) J₂ trv htrv i i rfl u x
    (I.hom.f (3 - i) (3 - i) rfl y)
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [I.comm]
  congr 2
  by_cases hi : i = 0 ∨ i = 1
  · have : Subsingleton (c₁.U.X (3 - i)) := hc₁ (3 - i) (by omega) (by omega)
    rw [Subsingleton.elim y 0, map_zero, map_zero, map_zero]
  · have : Subsingleton (c.U.X i) := hc i (by omega) (by omega)
    rw [Subsingleton.elim u 0, map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

/-- PROVED. **(b)** Per-place quasi-isomorphy transfers from `(c, c₂)` to `(c, c₁)` along `c₁ ≅ c₂`
(concentrated conditions, any isotropy homotopies). -/
theorem conjC_quasiIso_of_condIso (I : ConjKCondIso c₁ c₂) (hc : OrthConcentratedAt c)
    (hc₁ : OrthConcentratedAt c₁)
    (J₁ : LocalTruncIsotropy c.i c₁.i (orthGaloisPair K β hβ v))
    (J₂ : LocalTruncIsotropy c.i c₂.i (orthGaloisPair K β hβ v))
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T
      v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (h : QuasiIso (GHom.toCC (orthLocalMap c.i c₂.i (orthGaloisPair K β hβ v) J₂ trv htrv))) :
    QuasiIso (GHom.toCC (orthLocalMap c.i c₁.i (orthGaloisPair K β hβ v) J₁ trv htrv)) := by
  rw [conjC_orthLocalMap_iso β hβ c I hc hc₁ J₁ J₂ trv htrv]
  have := conjC_dualHom_isIso I 3
  infer_instance

/-- PROVED. **(b)** `OrthIsotropicAt` transfers along `c₁ ≅ c₂`. -/
theorem conjC_isotropic_of_condIso (I : ConjKCondIso c₁ c₂)
    (h : OrthIsotropicAt β hβ c c₂) : OrthIsotropicAt β hβ c c₁ := by
  intro u y
  rw [← I.comm 1 y]
  exact h u (I.hom.f 1 1 rfl y)

end IsoInvariance

/-! ### (c) Scaling the Kummer coefficient map by a unit -/

section UnitScaling

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  {v : Places K S} [DecidableEq (v.1.adicCompletion K)]
  (B : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] (m : ℕ) [NeZero m]

omit [ContinuousSMul (GKS K S) M] in
/-- PROVED. A Kummer cocycle through `ι' = r • ι` is a Kummer cocycle through `ι` with coefficient
multiplied by `r`. -/
theorem conjC_kummerCocycle_smul
    (ι ι' : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M) (r : R)
    (hr : ∀ t, ι' t = r • ι t) (a : R) (P : B.toAffine.Point) :
    kummerCocycleIn ι' a P = kummerCocycleIn ι (a * r) P := by
  apply Subtype.ext
  funext g
  change a • ι' (kummerFun _ B m P (g 0)) = (a * r) • ι (kummerFun _ B m P (g 0))
  rw [hr, smul_smul]

omit [ContinuousSMul (GKS K S) M] in
/-- PROVED. **(c) Unit scaling**: the Kummer cocycle span through `u • ι` (`u` a unit of the
coefficient ring) is the one through `ι` (`kummerZ'` is an `A`-span). -/
theorem conjC_kummerZ_smul (ι ι' : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)
    (u : Rˣ) (hu : ∀ t, ι' t = (u : R) • ι t) : kummerZ' R ι' = kummerZ' R ι := by
  have hu' : ∀ t, ι t = ((u⁻¹ : Rˣ) : R) • ι' t := fun t => by
    rw [hu, smul_smul, Units.inv_mul, one_smul]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, P⟩, rfl⟩
    change kummerCocycleIn ι' a P ∈ _
    rw [conjC_kummerCocycle_smul B m ι ι' (u : R) hu a P]
    exact Submodule.subset_span ⟨(a * u, P), rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, P⟩, rfl⟩
    change kummerCocycleIn ι a P ∈ _
    rw [conjC_kummerCocycle_smul B m ι' ι ((u⁻¹ : Rˣ) : R) hu' a P]
    exact Submodule.subset_span ⟨(a * ((u⁻¹ : Rˣ) : R), P), rfl⟩

/-- PROVED. **(c)** The Kummer condition through `u • ι` EQUALS the Kummer condition through `ι`
(lane RC28's `kummerAt`). -/
theorem conjC_kummerAt_smul (ι ι' : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t)
    (hι' : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι' (σ • t) = σ • ι' t)
    (u : Rˣ) (hu : ∀ t, ι' t = (u : R) • ι t) :
    kummerAt (k := R) v B m ι' hι' = kummerAt (k := R) v B m ι hι := by
  have hZ := conjC_kummerZ_smul B m ι ι' u hu
  unfold kummerAt kummerConditionIn kummerConditionInι
  generalize kummerZ'_cocycle R ι hι = h₁
  generalize kummerZ'_cocycle R ι' hι' = h₂
  revert h₂
  rw [hZ]
  intro h₂
  rfl

end UnitScaling

/-! ### The inner element adapted to the decomposition embeddings -/

section AdaptedElt

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (v : Places K S)

/-- DEF. **The comparison element `h₀ ∈ Gal(K̄/K)` of the decomposition embeddings** at `v` and
`τv`: `j_v ∘ h₀ = J ∘ j_{τv} ∘ τ` for lane RC29's `decompEmb` (a choice; `conjK_exists_comp_of`,
round 2). -/
def conjCCompElt : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  Classical.choose (conjK_exists_comp_of C.κ C.τ C.hτ (locConjPlaceS_asIdeal C v)
    (decompEmb K v.1) (decompEmb K (locConjPlaceS C v).1))

/-- PROVED. The defining property of `conjCCompElt`. -/
theorem conjCCompElt_spec (x : AlgebraicClosure K) :
    decompEmb K v.1 (conjCCompElt C v x) =
      locConjLift C.κ (locConjPlaceS_asIdeal C v) (decompEmb K (locConjPlaceS C v).1 (C.τ x)) :=
  Classical.choose_spec (conjK_exists_comp_of C.κ C.τ C.hτ (locConjPlaceS_asIdeal C v)
    (decompEmb K v.1) (decompEmb K (locConjPlaceS C v).1)) x

/-- DEF. **The inner element adapted to the decomposition embeddings**, `g = c(h̄₀)⁻¹` (DEPARTURE D1
of round 1: the text does not mention an inner element; with Mathlib's arbitrary embeddings one is
needed, and this one makes the transported Kummer map a unit multiple of the Kummer map at `v`,
`conjC_iota_eq`). -/
def conjCElt : GKS K S :=
  (C.conj (@id (GKS K S) (resAbs K S (conjCCompElt C v))))⁻¹

/-- PROVED (round 2's `conjK_locMap_of_decompMap`). `conjCElt` satisfies the hypothesis `hg` of the
transport. -/
theorem conjCElt_spec (σ : Gloc K v.1) :
    locMap K S (locConjPlaceS C v).1 (locConjGal C.κ (locConjPlaceS_asIdeal C v) σ) =
      conjCElt C v * C.conj (locMap K S v.1 σ) * (conjCElt C v)⁻¹ :=
  conjK_locMap_of_decompMap C (locConjPlaceS_asIdeal C v) (conjCCompElt C v)
    (conjK_decompMap_of C.κ C.τ C.hτ (locConjPlaceS_asIdeal C v) (decompEmb K v.1)
      (decompEmb K (locConjPlaceS C v).1) (fun σ y => decompEmb_decompMap K v.1 σ y)
      (fun σ y => decompEmb_decompMap K (locConjPlaceS C v).1 σ y) (conjCCompElt C v)
      (conjCCompElt_spec C v)) σ

/-- PROVED. `Ē(j_v y) = j_{τv}(τ(h₀⁻¹ y))`. -/
theorem conjCCompElt_bar (y : AlgebraicClosure K) :
    locConjBar C.κ (locConjPlaceS_asIdeal C v) (decompEmb K v.1 y) =
      decompEmb K (locConjPlaceS C v).1 (C.τ ((conjCCompElt C v).symm y)) :=
  conjK_bar_of C.κ C.τ (locConjPlaceS_asIdeal C v) (decompEmb K v.1)
    (decompEmb K (locConjPlaceS C v).1) (conjCCompElt C v) (conjCCompElt_spec C v) y

end AdaptedElt

/-! ### The transported dual conditions -/

section Transported

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (hS : S₀ ⊆ S)
  (hS₀ : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ S₀ ↔ w ∈ S₀))
  (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.map (C.κ : K →+* K) = W) (i : ℕ)
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]

/-- DEF (tex 2810–2812: "At a split place v, the dual local condition is transported from the
conjugate place τv. At a fixed place it is transported by the actual local representative of
conjugation"). **The transport to `v` of a condition at `τv = locConjPlaceS C v`** on `M_i = MinS`,
as a condition on `Infl(τ₀^*M_{i,0})` (`τ^*MinS` through round 2's `conjInflPullEquiv`, the identity
map): round 1's `conjTransport` with the adapted inner element `conjCElt`. At a fixed place (`τv =
v`) this is the transport by the local representative of conjugation (round 1's
`conjTransport_eq_rep`). -/
def conjCTransport (v : Places K S)
    (c : CondAt K S (Acoef i) (MinS hS W i α) (locConjPlaceS C v)) :
    CondAt K S (Acoef i) (InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α))) v :=
  conjTransportCoef (conjInflPullEquiv C hS hS₀ (Acoef i) (Mcoef K S₀ W i α))
    (conjInflPullEquiv_smul C hS hS₀ (Acoef i) (Mcoef K S₀ W i α))
    (conjTransport C (conjCElt C v) (locConjPlaceS_asIdeal C v) (conjCElt_spec C v) c)

omit [W.IsElliptic] in
/-- PROVED. **The transport of the zero condition is the zero condition** (an equality; tex
2813–2814). -/
theorem conjCTransport_zeroAt (v : Places K S) :
    conjCTransport C hS hS₀ W i α v (zeroAt K S (Acoef i) _ (locConjPlaceS C v)) =
      zeroAt K S (Acoef i) _ v := by
  unfold conjCTransport
  rw [conjTransport_zeroAt, conjTransportCoef_zeroAt]

/-- DEF (tex 2798–2805). **`Infl(τ₀^*M_{i,0}) ≃ Infl(M_{i,0}(α⁻¹))`**, the inflation of lane RC28's
`conjToInv` (`w ↦ (id ⊗ ρ_T(τ)) w`) over `S₀`. -/
def conjCInvEquiv :
    InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α)) ≃ₗ[Acoef i]
      MinS hS W i (charInv α) :=
  conjInflMapEquiv hS _ _ (LinearEquiv.ofBijective
    (conjToInv (conjInflConj C hS₀) W hW (Acoef i) α)
    (conjToInv_bijective (conjInflConj C hS₀) W hW (Acoef i) α))

omit [IsOpenKer α] in
/-- PROVED. `conjCInvEquiv` is `G_{K,S}`-equivariant when `α∘c₀ = α⁻¹` (hypothesis `hα₀`: ELLIOT tex
2786–2795, PROVED by lane RC28 for the actual `α_i`, `alphaChar_conj`). -/
theorem conjCInvEquiv_smul (hα₀ : ∀ σ, α ((conjInflConj C hS₀).conj σ) = (α σ)⁻¹) (σ : GKS K S)
    (m : InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α))) :
    conjCInvEquiv C hS hS₀ W hW i α (σ • m) = σ • conjCInvEquiv C hS hS₀ W hW i α m :=
  conjInflMapEquiv_smul hS _ _ _ (conjToInv_smul (conjInflConj C hS₀) W hW (Acoef i) α hα₀) σ m

variable (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hκh : C.κ h = h) (hFull₀ : FullTorsion K S₀ W (2 ^ i))

/-- PROVED. The inflation of the adapted inner element: `infl(g⁻¹) = c₀(h̄₀)` (lane RC28's
`inflMap_conjGKS`, `resUnr_comp`). -/
theorem conjC_inflMap_elt (v : Places K S) :
    inflMap K hS (conjCElt C v)⁻¹ =
      (conjInflConj C hS₀).conj (@id (GKS K S₀) (resAbs K S₀ (conjCCompElt C v))) := by
  unfold conjCElt
  rw [inv_inv, conjInfl_inflMap_conj C hS hS₀]
  congr 1
  exact resUnr_comp K hS (conjCCompElt C v)

omit [IsOpenKer α] in
/-- PROVED (tex 2812–2813, inflated `M_i`). **The transported Kummer coefficient map is a unit
multiple of the Kummer coefficient map at `v`**: `conjToInv ∘ ι^τ = u • ι_v` in `M_{i,0}(α⁻¹)`, with
`u = α(h̄₀)⁻¹ ε`, `ε = ±1` the square-root sign of round 2 (`conjK_compTorsEquiv_sign` over `S₀`).
Hypotheses `hW` (definition/GLUE: `W.map κ = W` for a rational curve; lane RC28's DEPARTURE 3),
`hκh` (definition/GLUE: `κ h = h` for a rational twist, tex 2798–2802), `hFull₀` (GLUE, lane
RC28), `hα₀` (ELLIOT tex 2786–2795: the anticyclotomic moving-character relation). -/
theorem conjC_iota_eq (hα₀ : ∀ σ, α ((conjInflConj C hS₀).conj σ) = (α σ)⁻¹) (v : Places K S) :
    ∃ u : (Acoef i)ˣ, ∀ t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i),
      conjTransportCoefEquiv (S := S) (conjCInvEquiv C hS hS₀ W hW i α) v.1
        (conjTransportCoefEquiv (S := S) (conjInflPullEquiv C hS hS₀ (Acoef i) (Mcoef K S₀ W i α))
          v.1 (conjKIotaAt C (Acoef i) (conjCElt C v) (locConjPlaceS_asIdeal C v)
            (localTwist W h v.1) (localTwist W h (locConjPlaceS C v).1)
            (conjK_localTwist_map C.κ (locConjPlaceS_asIdeal C v) W hW hκh) (2 ^ i)
            (kummerIotaS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v)) t)) =
        (u : Acoef i) • kummerIotaS hS W i s hs hs0 (charInv α) hFull₀ v t := by
  set h₀ := conjCCompElt C v with hh₀
  obtain ⟨ε, hε⟩ := conjK_compTorsEquiv_sign (conjInflConj C hS₀) W hW s hs hs0 hκh
    (locConjPlaceS_asIdeal C v) h₀ (conjCCompElt_bar C v) (2 ^ i) hFull₀
  refine ⟨(α (@id (GKS K S₀) (resAbs K S₀ h₀)))⁻¹ *
    Units.map (Int.castRingHom (Acoef i)).toMonoidHom ε, fun t => ?_⟩
  have hinv : @id (GKS K S₀) (resAbs K S₀ h₀⁻¹) = (@id (GKS K S₀) (resAbs K S₀ h₀))⁻¹ :=
    map_inv (resAbs K S₀) h₀
  set P := (compTorsEquiv W (2 ^ i) hFull₀ v.1).symm
    (twistTors (W.baseChange (v.1.adicCompletion K)) (algebraMap K (v.1.adicCompletion K) h)
      two_ne_zero (localSqrt_ne_zero s hs0 v.1) (localSqrt_sq s hs v.1) (2 ^ i) t) with hP
  have e1 : (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from
      kummerIotaS hS W i s hs hs0 (charInv α) hFull₀ v t) = (1 : Acoef i) ⊗ₜ P := rfl
  have e2 : (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from
      conjKIotaAt C (Acoef i) (conjCElt C v) (locConjPlaceS_asIdeal C v)
        (localTwist W h v.1) (localTwist W h (locConjPlaceS C v).1)
        (conjK_localTwist_map C.κ (locConjPlaceS_asIdeal C v) W hW hκh) (2 ^ i)
        (kummerIotaS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v)) t) =
      (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from
        inflMap K hS (conjCElt C v)⁻¹ •
          oneTmul (Acoef i) α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))
            ((ε : ℤ) • conjTors (conjInflConj C hS₀) W hW ((2 ^ i : ℕ) : ℤ)
              (@id (GKS K S₀) (resAbs K S₀ h₀⁻¹) • P))) := by
    rw [← hε t]
    rfl
  have e3 : (conjInflConj C hS₀).conj (@id (GKS K S₀) (resAbs K S₀ h₀)) •
      oneTmul (Acoef i) α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))
        ((ε : ℤ) • conjTors (conjInflConj C hS₀) W hW ((2 ^ i : ℕ) : ℤ)
          (@id (GKS K S₀) (resAbs K S₀ h₀⁻¹) • P)) =
      CoefMod.equiv (Acoef i) α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))
        ((ε : ℤ) • (((((α (@id (GKS K S₀) (resAbs K S₀ h₀)))⁻¹ : (Acoef i)ˣ) : Acoef i) * 1) ⊗ₜ
          conjTors (conjInflConj C hS₀) W hW ((2 ^ i : ℕ) : ℤ) P)) := by
    rw [map_zsmul, smul_comm, oneTmul_apply, CoefMod.smul_tmul, hα₀,
      ← conjTors_smul (conjInflConj C hS₀) W hW ((2 ^ i : ℕ) : ℤ), hinv, smul_inv_smul, map_zsmul]
  change conjBC (conjInflConj C hS₀) W hW (Acoef i)
      (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from
        conjKIotaAt C (Acoef i) (conjCElt C v) (locConjPlaceS_asIdeal C v)
          (localTwist W h v.1) (localTwist W h (locConjPlaceS C v).1)
          (conjK_localTwist_map C.κ (locConjPlaceS_asIdeal C v) W hW hκh) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v)) t) =
    (((α (@id (GKS K S₀) (resAbs K S₀ h₀)))⁻¹ *
      Units.map (Int.castRingHom (Acoef i)).toMonoidHom ε : (Acoef i)ˣ) : Acoef i) •
      (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from
        kummerIotaS hS W i s hs hs0 (charInv α) hFull₀ v t)
  rw [e2, conjC_inflMap_elt C hS hS₀ v, e3, e1]
  change conjBC (conjInflConj C hS₀) W hW (Acoef i)
      ((ε : ℤ) • (((((α (@id (GKS K S₀) (resAbs K S₀ h₀)))⁻¹ : (Acoef i)ˣ) : Acoef i) * 1) ⊗ₜ
        conjTors (conjInflConj C hS₀) W hW ((2 ^ i : ℕ) : ℤ) P)) = _
  rw [map_zsmul, conjBC_tmul (conjInflConj C hS₀) W hW (Acoef i),
    conjTors_conjTors (conjInflConj C hS₀) W hW ((2 ^ i : ℕ) : ℤ) P, mul_one, Units.val_mul,
    Units.coe_map, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  congr 1
  simp [zsmul_eq_mul, mul_comm]

end Transported

/-! ### The transported Kummer place -/

section KummerPlace

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (hS : S₀ ⊆ S)
  (hS₀ : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ S₀ ↔ w ∈ S₀))
  (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.map (C.κ : K →+* K) = W) (i : ℕ)
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hκh : C.κ h = h) (hFull₀ : FullTorsion K S₀ W (2 ^ i))
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα₀ : ∀ σ, α ((conjInflConj C hS₀).conj σ) = (α σ)⁻¹)

/-- DEF (tex 2798–2802: "The Weil pairing gives the following R_i-linear perfect pairing: M_i ⊗
τ^*M_i → R_i(1), (v,w) ↦ e₂(v, ρ_T(τ)w)"). **The text's pairing**, lane RC28's `conjPairing` over
`S₀`. -/
abbrev conjCPair :
    Mcoef K S₀ W i α →ₗ[Acoef i] PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α) →ₗ[Acoef i]
      Tate1 (Acoef i) hμ₀ :=
  conjPairing (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α

omit [IsOpenKer α] in
include hα₀ in
/-- PROVED (lane RC28's `conjPairing_smul`; hypothesis `hα₀`, ELLIOT tex 2786–2795). The text's
pairing is `G_{K,S₀}`-equivariant. -/
theorem conjCPair_smul (g : GKS K S₀) (a : Mcoef K S₀ W i α)
    (b : PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α)) :
    conjCPair C hS₀ W hW i α hμ₀ (g • a) (g • b) = g • conjCPair C hS₀ W hW i α hμ₀ a b :=
  conjPairing_smul (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α hα₀ g a b

open scoped Classical in
/-- PROVED. The actual Kummer condition (lane RC29's `actualKummerAtS`) is concentrated in degrees
`0, 1`. -/
theorem conjC_actualKummerAtS_concentrated (α' : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α']
    (v : Places K S) (hα : IsLocallyQuadAt (S := S₀) i α' (quadChar s hs hs0) v.1) :
    OrthConcentratedAt (actualKummerAtS hS W i s hs hs0 α' hFull₀ v hα) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
    (kummerIotaS hS W i s hs hs0 α' hFull₀ v) (kummerIotaS_smul hS W i s hs hs0 α' hFull₀ v hα)

open scoped Classical in
/-- PROVED (tex 2812–2813: "Kummer conditions at 2N are preserved by this transport"). **The
transported actual Kummer condition from `τv`, pushed along `conjCInvEquiv`, is isomorphic to the
actual Kummer condition at `v` of `M_i(α⁻¹)`**: round 2's `conjKTransportKummerIso`,
`conjKCoefKummerIso` (twice), and the unit scaling `conjC_kummerAt_smul` with `conjC_iota_eq`.
Hypotheses `hαv`, `hαw`: lane RC29's local triviality of the moving character at `v` and at `τv`
(tex 2751–2753). -/
def conjCKummerIso (v : Places K S)
    (hαv : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (hαw : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) (locConjPlaceS C v).1) :
    ConjKCondIso (conjTransportCoef (conjCInvEquiv C hS hS₀ W hW i α)
        (conjCInvEquiv_smul C hS hS₀ W hW i α hα₀)
        (conjCTransport C hS hS₀ W i α v
          (actualKummerAtS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v) hαw)))
      (actualKummerAtS hS W i s hs hs0 (charInv α) hFull₀ v (isLocallyQuadAt_charInv hαv)) :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) (locConjPlaceS C v).1
  ((((conjKTransportKummerIso C (Acoef i) (conjCElt C v) (locConjPlaceS_asIdeal C v)
      (conjCElt_spec C v) (localTwist W h v.1) (localTwist W h (locConjPlaceS C v).1)
      (conjK_localTwist_map C.κ (locConjPlaceS_asIdeal C v) W hW hκh) (2 ^ i)
      (kummerIotaS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v))
      (kummerIotaS_smul hS W i s hs hs0 α hFull₀ (locConjPlaceS C v) hαw)).coef
    (conjInflPullEquiv C hS hS₀ (Acoef i) (Mcoef K S₀ W i α))
    (conjInflPullEquiv_smul C hS hS₀ (Acoef i) (Mcoef K S₀ W i α))).trans
    (conjKCoefKummerIso (conjInflPullEquiv C hS hS₀ (Acoef i) (Mcoef K S₀ W i α))
      (conjInflPullEquiv_smul C hS hS₀ (Acoef i) (Mcoef K S₀ W i α)) (localTwist W h v.1) (2 ^ i)
      _ (conjKIotaAt_smul C (Acoef i) (conjCElt C v) (locConjPlaceS_asIdeal C v)
        (conjCElt_spec C v) (localTwist W h v.1) (localTwist W h (locConjPlaceS C v).1)
        (conjK_localTwist_map C.κ (locConjPlaceS_asIdeal C v) W hW hκh) (2 ^ i)
        (kummerIotaS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v))
        (kummerIotaS_smul hS W i s hs hs0 α hFull₀ (locConjPlaceS C v) hαw)))).coef
    (conjCInvEquiv C hS hS₀ W hW i α) (conjCInvEquiv_smul C hS hS₀ W hW i α hα₀)).trans
    ((conjKCoefKummerIso (conjCInvEquiv C hS hS₀ W hW i α)
      (conjCInvEquiv_smul C hS hS₀ W hW i α hα₀) (localTwist W h v.1) (2 ^ i) _
      (conjKCoefIota_smul _ (conjInflPullEquiv_smul C hS hS₀ (Acoef i) (Mcoef K S₀ W i α)) _ _ _
        (conjKIotaAt_smul C (Acoef i) (conjCElt C v) (locConjPlaceS_asIdeal C v)
          (conjCElt_spec C v) (localTwist W h v.1) (localTwist W h (locConjPlaceS C v).1)
          (conjK_localTwist_map C.κ (locConjPlaceS_asIdeal C v) W hW hκh) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v))
          (kummerIotaS_smul hS W i s hs hs0 α hFull₀ (locConjPlaceS C v) hαw)))).trans
      (ConjKCondIso.ofEq (conjC_kummerAt_smul (localTwist W h v.1) (2 ^ i)
        (kummerIotaS hS W i s hs hs0 (charInv α) hFull₀ v) _
        (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull₀ v (isLocallyQuadAt_charInv hαv)) _
        (Classical.choose (conjC_iota_eq C hS hS₀ W hW i α s hs hs0 hκh hFull₀ hα₀ v))
        (Classical.choose_spec (conjC_iota_eq C hS hS₀ W hW i α s hs hs0 hκh hFull₀ hα₀ v)))))

variable [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]

include hκh in
open scoped Classical in
/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` (Milne, *Arithmetic Duality
Theorems*, 2nd ed., Ch. I, Cor. 2.3, Thm. 3.2, Cor. 3.4, Rem. 3.5; through lane RC29's
`kummerPerPlace_isotropic_of_milne`, tex 3418–3419, 3439–3448). **The Kummer condition at `v` and
the transported Kummer condition from `τv` are isotropic for the text's pairing**, for a local trace
inducing `H² ≅ A_i` (`h2`). -/
theorem conjC_kummer_isotropic (hM : MilneLocalTateDualityKummerCharZero) (v : Places K S)
    (hαv : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (hαw : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) (locConjPlaceS C v).1)
    (trv : (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ z, trv ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (h2 : InducesIsoH2 trv) :
    OrthIsotropicAt (orthInflPair hS (Acoef i) (conjCPair C hS₀ W hW i α hμ₀))
      (orthInflPair_smul hS (Acoef i) _ (conjCPair_smul C hS₀ W hW i α hμ₀ hα₀))
      (actualKummerAtS hS W i s hs hs0 α hFull₀ v hαv)
      (conjCTransport C hS hS₀ W i α v
        (actualKummerAtS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v) hαw)) := by
  refine (conjC_isotropic_coef_iff (orthInflPair hS (Acoef i) (conjCPair C hS₀ W hW i α hμ₀))
    (orthInflPair_smul hS (Acoef i) _ (conjCPair_smul C hS₀ W hW i α hμ₀ hα₀))
    (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
    (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
    (conjCInvEquiv C hS hS₀ W hW i α) (conjCInvEquiv_smul C hS hS₀ W hW i α hα₀)
    (fun _ _ => rfl) _ _).1 ?_
  exact conjC_isotropic_of_condIso _ _ _
    (conjCKummerIso C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hα₀ v hαv hαw)
    (kummerPerPlace_isotropic_of_milne hS W i s hs hs0 hFull₀ v hμ₀ α hM hαv trv htrv h2)

include hκh in
open scoped Classical in
/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero` and `NekovarProp524` (Nekovář,
*Selmer complexes*, Prop. 5.2.4; lane RC26) through lane RC29's `kummerPerPlace_perf_of_milne` (tex
3418–3419, 3439–3450). **The per-place orthogonality at a Kummer place** (tex 2810–2813): the
per-place local duality map of (Kummer condition at `v` on `M_i`, transported Kummer condition from
`τv` on `τ^*M_i`) for the text's pairing is a quasi-isomorphism, for EVERY `τ≥2` isotropy homotopy.
Hypotheses: `hK`, `hSfin`, `h2₀` (the standing setting, tex 2750–2753: `K` imaginary quadratic,
finitely many places, `S₀ ⊇ {v | 2}`), `h2` (lane RC26's trace hypothesis, Nekovář 5.2.1), and those
of `conjCKummerIso`. -/
theorem conjC_kummer_quasiIso [NeZero i] (hM : MilneLocalTateDualityKummerCharZero)
    (h524 : NekovarProp524 K) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) (v : Places K S)
    (hαv : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (hαw : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) (locConjPlaceS C v).1)
    (trv : (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ z, trv ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (h2 : InducesIsoH2 trv)
    (J : LocalTruncIsotropy (actualKummerAtS hS W i s hs hs0 α hFull₀ v hαv).i
      (conjCTransport C hS hS₀ W i α v
        (actualKummerAtS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v) hαw)).i
      (orthUrPair hS (Acoef i) (conjCPair C hS₀ W hW i α hμ₀)
        (conjCPair_smul C hS₀ W hW i α hμ₀ hα₀) v)) :
    QuasiIso (GHom.toCC (orthLocalMap (actualKummerAtS hS W i s hs hs0 α hFull₀ v hαv).i
      (conjCTransport C hS hS₀ W i α v
        (actualKummerAtS hS W i s hs hs0 α hFull₀ (locConjPlaceS C v) hαw)).i
      (orthUrPair hS (Acoef i) (conjCPair C hS₀ W hW i α hμ₀)
        (conjCPair_smul C hS₀ W hW i α hμ₀ hα₀) v) J trv htrv)) := by
  refine (conjC_quasiIso_coef_iff (orthInflPair hS (Acoef i) (conjCPair C hS₀ W hW i α hμ₀))
    (orthInflPair_smul hS (Acoef i) _ (conjCPair_smul C hS₀ W hW i α hμ₀ hα₀))
    (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
    (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
    (conjCInvEquiv C hS hS₀ W hW i α) (conjCInvEquiv_smul C hS hS₀ W hW i α hα₀)
    (fun _ _ => rfl) _ _ J trv htrv).1 ?_
  have hc := conjC_actualKummerAtS_concentrated hS W i s hs hs0 hFull₀ α v hαv
  have hc₁ := conjC_actualKummerAtS_concentrated hS W i s hs hs0 hFull₀ α (locConjPlaceS C v) hαw
  have hc₂ := conjC_actualKummerAtS_concentrated hS W i s hs hs0 hFull₀ (charInv α) v
    (isLocallyQuadAt_charInv hαv)
  have hi := kummerPerPlace_isotropic_of_milne hS W i s hs hs0 hFull₀ v hμ₀ α hM hαv trv htrv h2
  exact conjC_quasiIso_of_condIso _ _ _
    (conjCKummerIso C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hα₀ v hαv hαw) hc hc₁ _
    (orthZeroIsotropy hc hc₂ hi) trv htrv
    (kummerPerPlace_perf_of_milne hS W i s hs hs0 hFull₀ v hμ₀ α hM h524 hK hSfin h2₀
      (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀) hαv trv htrv h2 _)

end KummerPlace

/-! ### Per-place lemmas: vanishing truncated products, transport along equalities -/

section PlaceHelpers

variable {k : Type} [CommRing k] {U U' L L' E : GCx k} {iU : GHom U L} {iU' : GHom U' L'}
  {P : GPair L L' E}

/-- PROVED (as lane RC29's `orthZeroIsotropy`). For conditions concentrated in degrees `0, 1` with
isotropic `(1, 1)` products, the restricted products vanish in `τ≥2`. -/
theorem conjC_truncZero_of_concentrated (hU : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U.X i))
    (hU' : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U'.X i))
    (h11 : ∀ (u : U.X 1) (v : U'.X 1),
      P.P 1 1 2 rfl (iU.f 1 1 rfl u) (iU'.f 1 1 rfl v) ∈ LinearMap.range (E.d 1 2 rfl)) :
    ∀ (i j l : ℤ) (h : i + j = l) (u : U.X i) (v : U'.X j),
      (truncPair (pullPair P iU iU')).P i j l h u v = 0 := fun i j l h u v => by
  change (truncSub E l).mkQ (P.P i j l h (iU.f i i rfl u) (iU'.f j j rfl v)) = 0
  by_cases hi : i = 0 ∨ i = 1
  · by_cases hj : j = 0 ∨ j = 1
    · by_cases hl : l ≤ 1
      · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_le E hl]
        trivial
      · obtain rfl : i = 1 := by omega
        obtain rfl : j = 1 := by omega
        obtain rfl : l = 2 := by omega
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_eq E rfl]
        exact h11 u v
    · have : Subsingleton (U'.X j) := hU' j (by omega) (by omega)
      rw [Subsingleton.elim v 0]
      simp
  · have : Subsingleton (U.X i) := hU i (by omega) (by omega)
    rw [Subsingleton.elim u 0]
    simp

/-- PROVED. If the dual condition vanishes, the restricted products vanish (tex 2813–2814: the full
condition against the zero condition). -/
theorem conjC_truncZero_of_zero (hU' : ∀ j : ℤ, Subsingleton (U'.X j)) :
    ∀ (i j l : ℤ) (h : i + j = l) (u : U.X i) (v : U'.X j),
      (truncPair (pullPair P iU iU')).P i j l h u v = 0 := fun i j l h u v => by
  have := hU' j
  rw [Subsingleton.elim v 0, map_zero]

end PlaceHelpers

section PlaceCongr

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
  {v : Places K S}

/-- PROVED. Transport of the vanishing of the restricted products along equalities of conditions. -/
theorem conjC_truncZero_congr {A A₀ : CondAt K S R M v} {B B₀ : CondAt K S R M' v}
    (hA : A = A₀) (hB : B = B₀)
    (h : ∀ (i j l : ℤ) (hh : i + j = l) (u : A₀.U.X i) (y : B₀.U.X j),
      (truncPair (pullPair (orthGaloisPair K β hβ v) A₀.i B₀.i)).P i j l hh u y = 0) :
    ∀ (i j l : ℤ) (hh : i + j = l) (u : A.U.X i) (y : B.U.X j),
      (truncPair (pullPair (orthGaloisPair K β hβ v) A.i B.i)).P i j l hh u y = 0 := by
  subst hA hB
  exact h

/-- PROVED. Transport of per-place quasi-isomorphy for every isotropy homotopy along equalities of
conditions. -/
theorem conjC_quasiIso_congr {A A₀ : CondAt K S R M v} {B B₀ : CondAt K S R M' v}
    (hA : A = A₀) (hB : B = B₀)
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T
      v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (h : ∀ J₀ : LocalTruncIsotropy A₀.i B₀.i (orthGaloisPair K β hβ v),
      QuasiIso (GHom.toCC (orthLocalMap A₀.i B₀.i (orthGaloisPair K β hβ v) J₀ trv htrv)))
    (J : LocalTruncIsotropy A.i B.i (orthGaloisPair K β hβ v)) :
    QuasiIso (GHom.toCC (orthLocalMap A.i B.i (orthGaloisPair K β hβ v) J trv htrv)) := by
  subst hA hB
  exact h J

end PlaceCongr

/-! ### The actual conditions and their transported duals -/

section ActualConditions

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (hS : S₀ ⊆ S)
  (hS₀ : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ S₀ ↔ w ∈ S₀))
  (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.map (C.κ : K →+* K) = W) (i : ℕ)
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hκh : C.κ h = h) (hFull₀ : FullTorsion K S₀ W (2 ^ i))
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα₀ : ∀ σ, α ((conjInflConj C hS₀).conj σ) = (α σ)⁻¹)
  (P : Set (HeightOneSpectrum (𝓞 K)))
  (hP : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ P ↔ w ∈ P))
  (hαP : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)

open Classical in
/-- DEF (tex 2754–2756, 3084–3085: "At active and moving primes the required condition is full").
**The actual conditions on `M_i` at `S₀`**: the actual Kummer condition at the places of `P` (the
places above `2N`), the full condition at the other places of `S₀` (the active and moving primes).
-/
def conjCCondA : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v :=
  fun v _ => if hv : v.1 ∈ P then actualKummerAtS hS W i s hs hs0 α hFull₀ v (hαP v.1 hv)
    else fullAt K S (Acoef i) _ v

open Classical in
/-- DEF (tex 2810–2814: "A full condition is paired with the zero condition"). **The condition at
`τv` whose transport is the dual condition at `v`**: Kummer at `τv ∈ P`, zero otherwise. -/
def conjCDualType (w : Places K S) : CondAt K S (Acoef i) (MinS hS W i α) w :=
  if hw : w.1 ∈ P then actualKummerAtS hS W i s hs hs0 α hFull₀ w (hαP w.1 hw)
    else zeroAt K S (Acoef i) _ w

/-- DEF (tex 2810–2814). **The transported dual conditions at `S₀`**: at `v ∈ S₀` the transport
(`conjCTransport`) of `conjCDualType` at `τv`. -/
def conjCCondB : ∀ v : Places K S, v.1 ∈ S₀ →
    CondAt K S (Acoef i) (InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α))) v :=
  fun v _ => conjCTransport C hS hS₀ W i α v (conjCDualType hS W i s hs hs0 hFull₀ α P hαP
    (locConjPlaceS C v))

include hP in
/-- PROVED. `τv ∈ P ↔ v ∈ P` (hypothesis `hP`: `κ`-stability of `P`, definition/GLUE, tex
2750–2753: `P` is the set of places above `2N`, a set of places above rational primes, so this is
rational-prime support stability, not an independent ELLIOT step; non-vacuous
`conjC_stable_nonvacuous`). -/
theorem conjC_mem_conjPlace_iff (v : Places K S) : (locConjPlaceS C v).1 ∈ P ↔ v.1 ∈ P :=
  (hP v.1 (conjPlace C.κ v.1) rfl).symm

/-- PROVED. At a place of `P`, `conjCCondA` is the actual Kummer condition. -/
theorem conjCCondA_of_mem {v : Places K S} (hv : v.1 ∈ S₀) (hvP : v.1 ∈ P) :
    conjCCondA hS W i s hs hs0 hFull₀ α P hαP v hv =
      actualKummerAtS hS W i s hs hs0 α hFull₀ v (hαP v.1 hvP) := by
  unfold conjCCondA
  exact dite_eq_left hvP

/-- PROVED. Outside `P`, `conjCCondA` is the full condition. -/
theorem conjCCondA_of_not_mem {v : Places K S} (hv : v.1 ∈ S₀) (hvP : v.1 ∉ P) :
    conjCCondA hS W i s hs hs0 hFull₀ α P hαP v hv = fullAt K S (Acoef i) _ v := by
  unfold conjCCondA
  exact dite_eq_right hvP

include hP in
/-- PROVED. At a place of `P`, `conjCCondB` is the transported Kummer condition from `τv`. -/
theorem conjCCondB_of_mem {v : Places K S} (hv : v.1 ∈ S₀) (hvP : v.1 ∈ P) :
    conjCCondB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v hv =
      conjCTransport C hS hS₀ W i α v (actualKummerAtS hS W i s hs hs0 α hFull₀
        (locConjPlaceS C v) (hαP _ ((conjC_mem_conjPlace_iff C P hP v).2 hvP))) := by
  unfold conjCCondB conjCDualType
  rw [dite_eq_left ((conjC_mem_conjPlace_iff C P hP v).2 hvP)]

include hP in
/-- PROVED. Outside `P`, `conjCCondB` is the zero condition (an equality, `conjCTransport_zeroAt`).
-/
theorem conjCCondB_of_not_mem {v : Places K S} (hv : v.1 ∈ S₀) (hvP : v.1 ∉ P) :
    conjCCondB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v hv = zeroAt K S (Acoef i) _ v := by
  unfold conjCCondB conjCDualType
  rw [dite_eq_right (fun h' => hvP ((conjC_mem_conjPlace_iff C P hP v).1 h')),
    conjCTransport_zeroAt]

end ActualConditions

/-! ### The assembly: the transported duals are the orthogonal complements -/

section Assembly

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (hS : S₀ ⊆ S)
  (hS₀ : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ S₀ ↔ w ∈ S₀))
  (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.map (C.κ : K →+* K) = W) (i : ℕ)
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hκh : C.κ h = h) (hFull₀ : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα₀ : ∀ σ, α ((conjInflConj C hS₀).conj σ) = (α σ)⁻¹)
  (P : Set (HeightOneSpectrum (𝓞 K)))
  (hP : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ P ↔ w ∈ P))
  (hαP : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)

/-- DEF. The text's pairing (`conjCPair`) inflated to `G_{K,S}`: `MinS × Infl(τ₀^*M_{i,0}) →
Infl(A_i(1))`. -/
abbrev conjCβ :
    MinS hS W i α →ₗ[Acoef i] InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α))
      →ₗ[Acoef i] InflMod hS (Tate1 (Acoef i) hμ₀) :=
  orthInflPair hS (Acoef i) (conjCPair C hS₀ W hW i α hμ₀)

include hα₀ in
/-- PROVED. The inflated pairing is `G_{K,S}`-equivariant (hypothesis `hα₀`). -/
theorem conjCβ_smul (g : GKS K S) (a : MinS hS W i α)
    (b : InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α))) :
    conjCβ C hS hS₀ W hW i α hμ₀ (g • a) (g • b) = g • conjCβ C hS hS₀ W hW i α hμ₀ a b :=
  orthInflPair_smul hS (Acoef i) _ (conjCPair_smul C hS₀ W hW i α hμ₀ hα₀) g a b

/-- DEF (tex 2754–2756, 3084–3085, 3483–3498). **`ΔA`**: Kummer at `P`, full at `S₀ − P`, lane
RC28's unramified condition at `S − S₀`, on `M_i = MinS`. -/
abbrev conjCFamA : ∀ v : Places K S, CondAt K S (Acoef i) (MinS hS W i α) v :=
  urOutside hS (Acoef i) (Mcoef K S₀ W i α) (conjCCondA hS W i s hs hs0 hFull₀ α P hαP)

/-- DEF (tex 2810–2816, 3483–3498). **`ΔB`, the transported dual family**: at `v ∈ S₀` the transport
from `τv` of Kummer (`τv ∈ P`) or zero (`τv ∈ S₀ − P`), the unramified condition at `S − S₀`, on
`Infl(τ₀^*M_{i,0}) = τ^*MinS`. -/
abbrev conjCFamB : ∀ v : Places K S,
    CondAt K S (Acoef i) (InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α))) v :=
  urOutside hS (Acoef i) (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α))
    (conjCCondB C hS hS₀ W i s hs hs0 hFull₀ α P hαP)

variable (trv : ∀ v : Places K S, (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
  (htrv : ∀ v z, trv v ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
  (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v))

include hκh hP htrv htrv2 in
open scoped Classical in
/-- PROVED (from the PRINT `MilneLocalTateDualityKummerCharZero` at the Kummer places, Lemma 7.5.2
of Nekovář at `S − S₀` through lane RC29's `orthUr_cup_mem_range`, and the vanishing of the zero
condition at `S₀ − P`). **At every place the restricted products of `ΔA` and `ΔB` vanish in `τ≥2`.**
-/
theorem conjC_truncZero (hM : MilneLocalTateDualityKummerCharZero) (v : Places K S) :
    ∀ (j₁ j₂ l : ℤ) (hh : j₁ + j₂ = l)
      (u : (conjCFamA hS W i s hs hs0 hFull₀ α P hαP v).U.X j₁)
      (y : (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v).U.X j₂),
      (truncPair (pullPair (orthGaloisPair K (conjCβ C hS hS₀ W hW i α hμ₀)
        (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀) v)
        (conjCFamA hS W i s hs hs0 hFull₀ α P hαP v).i
        (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v).i)).P j₁ j₂ l hh u y = 0 := by
  by_cases hv : v.1 ∈ S₀
  · have hA : conjCFamA hS W i s hs hs0 hFull₀ α P hαP v =
        conjCCondA hS W i s hs hs0 hFull₀ α P hαP v hv := dite_eq_left hv
    have hB : conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v =
        conjCCondB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v hv := dite_eq_left hv
    by_cases hvP : v.1 ∈ P
    · have hw : (locConjPlaceS C v).1 ∈ P := (conjC_mem_conjPlace_iff C P hP v).2 hvP
      exact conjC_truncZero_congr _ _
        (hA.trans (conjCCondA_of_mem hS W i s hs hs0 hFull₀ α P hαP hv hvP))
        (hB.trans (conjCCondB_of_mem C hS hS₀ W i s hs hs0 hFull₀ α P hP hαP hv hvP))
        (conjC_truncZero_of_concentrated
          (conjC_actualKummerAtS_concentrated hS W i s hs hs0 hFull₀ α v (hαP v.1 hvP))
          (conjC_actualKummerAtS_concentrated hS W i s hs hs0 hFull₀ α (locConjPlaceS C v)
            (hαP _ hw))
          (conjC_kummer_isotropic C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ hM v
            (hαP v.1 hvP) (hαP _ hw) (trv v) (htrv v) (htrv2 v)))
    · exact conjC_truncZero_congr _ _
        (hA.trans (conjCCondA_of_not_mem hS W i s hs hs0 hFull₀ α P hαP hv hvP))
        (hB.trans (conjCCondB_of_not_mem C hS hS₀ W i s hs hs0 hFull₀ α P hP hαP hv hvP))
        (conjC_truncZero_of_zero fun _ => ⟨fun a b => Subsingleton.elim (α := PUnit) a b⟩)
  · have hA : conjCFamA hS W i s hs hs0 hFull₀ α P hαP v =
        urAt hS (Acoef i) (Mcoef K S₀ W i α) v hv := dite_eq_right hv
    have hB : conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v =
        urAt hS (Acoef i) (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α)) v hv :=
      dite_eq_right hv
    exact conjC_truncZero_congr _ _ hA hB
      (conjC_truncZero_of_concentrated (orth_urAt_vanishes hS (Acoef i) _ v hv)
        (orth_urAt_vanishes hS (Acoef i) _ v hv)
        (orthUr_cup_mem_range hS (Acoef i) (conjCPair C hS₀ W hW i α hμ₀)
          (conjCPair_smul C hS₀ W hW i α hμ₀ hα₀) v hv))

include hκh hP htrv htrv2 in
/-- DEF. **The per-place `τ≥2` isotropy homotopies** of `(ΔA, ΔB)`: the zero homotopies
(`ofTruncZero` of `conjC_truncZero`; Nekovář 6.2.1.5, `h_v = 0`). -/
def conjCIsotropy (hM : MilneLocalTateDualityKummerCharZero) (v : Places K S) :
    LocalTruncIsotropy (conjCFamA hS W i s hs hs0 hFull₀ α P hαP v).i
      (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v).i
      (orthGaloisPair K (conjCβ C hS hS₀ W hW i α hμ₀) (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀) v) :=
  ofTruncZero (conjC_truncZero C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv
    htrv2 hM v)

include hκh hP htrv htrv2 in
/-- DEF. The `τ≥2` isotropy data of `(ΔA, ΔB)` (lane RC26's `TruncIsotropyData.ofLocal` of
`conjCIsotropy`). -/
abbrev conjCTrunc (hM : MilneLocalTateDualityKummerCharZero) :
    GaloisTruncIsotropyData K S (Acoef i) (conjCβ C hS hS₀ W hW i α hμ₀)
      (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
      (ofCondAt K S (Acoef i) (MinS hS W i α) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP))
      (ofCondAt K S (Acoef i) _ (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP)) :=
  TruncIsotropyData.ofLocal
    (ΔA := ofCondAt K S (Acoef i) (MinS hS W i α) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP))
    (ΔB := ofCondAt K S (Acoef i) _ (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP))
    (conjCIsotropy C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv htrv2 hM)

include hκh hP htrv2 in
open scoped Classical in
/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524`, `NekovarProp756`
(Nekovář 7.5.6 with 7.5.5, lane RC29's `orthUr_quasiIso_of_print`). **The per-place orthogonality of
`ΔA` and `ΔB` at every place of `S`, for every isotropy homotopy**: Kummer places by
`conjC_kummer_quasiIso`, full/zero places by lane RC29's `orthLocalMap_fullAt_zeroAt_quasiIso` (tex
2813–2814), unramified places by the PRINT `NekovarProp756`. -/
theorem conjC_perPlace [NeZero i] (hM : MilneLocalTateDualityKummerCharZero)
    (h524 : NekovarProp524 K) (h756 : NekovarProp756 K) (hK : IsTotallyComplex K)
    (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) (v : Places K S)
    (J : LocalTruncIsotropy (conjCFamA hS W i s hs hs0 hFull₀ α P hαP v).i
      (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v).i
      (orthGaloisPair K (conjCβ C hS hS₀ W hW i α hμ₀) (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
        v)) :
    QuasiIso (GHom.toCC (orthLocalMap (conjCFamA hS W i s hs hs0 hFull₀ α P hαP v).i
      (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v).i
      (orthGaloisPair K (conjCβ C hS hS₀ W hW i α hμ₀) (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀) v)
      J (trv v) (htrv v))) := by
  by_cases hv : v.1 ∈ S₀
  · have hA : conjCFamA hS W i s hs hs0 hFull₀ α P hαP v =
        conjCCondA hS W i s hs hs0 hFull₀ α P hαP v hv := dite_eq_left hv
    have hB : conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v =
        conjCCondB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v hv := dite_eq_left hv
    by_cases hvP : v.1 ∈ P
    · have hw : (locConjPlaceS C v).1 ∈ P := (conjC_mem_conjPlace_iff C P hP v).2 hvP
      exact conjC_quasiIso_congr _ _
        (hA.trans (conjCCondA_of_mem hS W i s hs hs0 hFull₀ α P hαP hv hvP))
        (hB.trans (conjCCondB_of_mem C hS hS₀ W i s hs hs0 hFull₀ α P hP hαP hv hvP)) (trv v)
        (htrv v) (fun J₀ => conjC_kummer_quasiIso C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀
          hM h524 hK hSfin h2₀ v (hαP v.1 hvP) (hαP _ hw) (trv v) (htrv v) (htrv2 v) J₀) J
    · exact conjC_quasiIso_congr _ _
        (hA.trans (conjCCondA_of_not_mem hS W i s hs hs0 hFull₀ α P hαP hv hvP))
        (hB.trans (conjCCondB_of_not_mem C hS hS₀ W i s hs hs0 hFull₀ α P hP hαP hv hvP)) (trv v)
        (htrv v) (fun J₀ => orthLocalMap_fullAt_zeroAt_quasiIso K _ _ v J₀ (trv v) (htrv v)) J
  · have hA : conjCFamA hS W i s hs hs0 hFull₀ α P hαP v =
        urAt hS (Acoef i) (Mcoef K S₀ W i α) v hv := dite_eq_right hv
    have hB : conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP v =
        urAt hS (Acoef i) (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α)) v hv :=
      dite_eq_right hv
    exact conjC_quasiIso_congr _ _ hA hB (trv v) (htrv v)
      (fun J₀ => orthUr_quasiIso_of_print h756 hS 2
        (nekovarFiniteSetting_acoef K hK S₀ hS₀fin h2₀ i)
        (conjCPair C hS₀ W hW i α hμ₀) (conjCPair_smul C hS₀ W hW i α hμ₀ hα₀)
        (conjPairing_bijective (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α hFull₀)
        (conjPairing_flip_bijective (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α hFull₀)
        (isCyclotomicTwist_tate1 (Acoef i) hμ₀) v hv J₀ (trv v) (htrv v) (htrv2 v)) J

open scoped Classical in
/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524`, `NekovarProp756`
(tex 2810–2816 with 2754–2756, 3084–3085, 3413–3450, 3483–3498). **D4: the transported dual
conditions ARE the orthogonal complements of the actual conditions**, in lane RC26's consumer shape
`OrthogonalComplementsT K β hβ ΔA ΔB I tr htr`: `ΔA` = Kummer at `P`, full at `S₀ − P`, unramified
at `S − S₀` on `M_i`; `ΔB` = the transport from `τv` of Kummer/zero at `S₀`, unramified at `S − S₀`
on `τ^*M_i`; `β` the text's pairing `(v, w) ↦ e(v, ρ_T(τ)w)`; `I` the zero isotropy homotopies.
Hypotheses: the standing setting (`hK`, `hSfin`, `hS₀fin`, `h2₀`, tex 2750–2753; `hS₀`, `hP`
`κ`-stability, i.e. rational-prime support stability, definition/GLUE, tex 2750–2753, 3479–3498;
`hκh`, i.e. `κ h = h` for a rational twist, definition/GLUE, tex 2798–2802; `hW`, i.e.
`W.map κ = W` for a rational curve, definition/GLUE, lane RC28 DEPARTURE 3 (not independent
ELLIOT steps for the genuine objects); `hα₀` ELLIOT tex 2786–2795, the anticyclotomic
moving-character relation; `hFull₀` GLUE lane RC28; `hαP` lane RC29's local triviality at `P`,
tex 2751–2753; `IsOpenKer α`), local traces inducing `H² ≅ A_i` at every place (`htrv2`, Nekovář
5.2.1, lane RC26) and a global trace whose local part is `∑_v tr_v` (`hsum`, Nekovář 5.4.1, lane
RC26). -/
theorem conjActualLocalComplements [Fintype (Places K S)] [NeZero i]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K)
    (h756 : NekovarProp756 K) (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (tr : (galoisCompactTT K S (Acoef i) (conjCβ C hS hS₀ W hW i α hμ₀)
      (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
      (ofCondAt K S (Acoef i) (MinS hS W i α) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP))
      (ofCondAt K S (Acoef i) _ (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP))
      (conjCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv htrv2 hM)).X 3
        →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i) (conjCβ C hS hS₀ W hW i α hμ₀)
      (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
      (ofCondAt K S (Acoef i) (MinS hS W i α) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP))
      (ofCondAt K S (Acoef i) _ (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP))
      (conjCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv htrv2 hM)).d
        2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    OrthogonalComplementsT K (conjCβ C hS hS₀ W hW i α hμ₀)
      (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
      (ofCondAt K S (Acoef i) (MinS hS W i α) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP))
      (ofCondAt K S (Acoef i) _ (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP))
      (conjCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv htrv2 hM) tr
      htr :=
  orthogonalComplementsT_ofCondAt K (conjCβ C hS hS₀ W hW i α hμ₀)
    (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP)
    (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP)
    (conjCIsotropy C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv htrv2 hM)
    trv htrv tr htr hsum
    (fun v => conjC_perPlace C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv htrv2
      hM h524 h756 hK hSfin hS₀fin h2₀ v _)

open scoped Classical in
/-- PROVED from the PRINTs of `conjActualLocalComplements` and `NekovarProp543T` (Nekovář 5.4.3 with
6.3.4, lane RC26's `genuineSelmerDualityT`; tex 2825–2829). **The finite Selmer duality `C_U(M_i) ≃
RHom(C_{U⊥}(τ^*M_i), A_i)[−3]` for the actual conditions and their transported duals**, with the
text's pairing: lane RC26's Selmer duality map is a quasi-isomorphism. Additional hypothesis: the
global trace induces `H³_c ≅ A_i` (`htr3`, Nekovář 5.4.1, lane RC26). -/
theorem conjActualSelmerDuality [Fintype (Places K S)] [NeZero i]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K)
    (h756 : NekovarProp756 K) (h543 : NekovarProp543T K) (hK : IsTotallyComplex K)
    (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (tr : (galoisCompactTT K S (Acoef i) (conjCβ C hS hS₀ W hW i α hμ₀)
      (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
      (ofCondAt K S (Acoef i) (MinS hS W i α) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP))
      (ofCondAt K S (Acoef i) _ (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP))
      (conjCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv htrv2 hM)).X 3
        →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i) (conjCβ C hS hS₀ W hW i α hμ₀)
      (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
      (ofCondAt K S (Acoef i) (MinS hS W i α) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP))
      (ofCondAt K S (Acoef i) _ (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP))
      (conjCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv htrv2 hM)).d
        2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (conjCβ C hS hS₀ W hW i α hμ₀) (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
      (ofCondAt K S (Acoef i) (MinS hS W i α) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP))
      (ofCondAt K S (Acoef i) _ (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP))
      (conjCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv htrv2 hM))
      tr htr)) := by
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  have : Finite (InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α))) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i α))
  exact genuineSelmerDualityT K (conjCβ C hS hS₀ W hW i α hμ₀)
    (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀) _ _ _ tr htr h543 2
    (nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i)
    (conjPairing_bijective (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α hFull₀)
    (conjPairing_flip_bijective (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α hFull₀)
    (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀) htr3
    (conjActualLocalComplements C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP trv htrv
      htrv2 hM h524 h756 hK hSfin hS₀fin h2₀ tr htr hsum)

end Assembly

/-! ### Non-vacuity of the new hypotheses -/

section NonVacuity

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}

/-- PROVED (lane RC28's `isStable_comap_int`). **Non-vacuity of the `κ`-stability hypotheses `hS₀`,
`hP`**: every set of places described through the rational primes below them (for instance the
places above `2N`) is stable. -/
theorem conjC_stable_nonvacuous (C : ActualConj K S) (T : Set (Ideal ℤ)) :
    ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) →
      (v ∈ {u : HeightOneSpectrum (𝓞 K) | u.asIdeal.comap (algebraMap ℤ (𝓞 K)) ∈ T} ↔
        w ∈ {u : HeightOneSpectrum (𝓞 K) | u.asIdeal.comap (algebraMap ℤ (𝓞 K)) ∈ T}) :=
  isStable_comap_int T C.κ

/-- PROVED. Non-vacuity of `hα₀` (`α = 1`; for the actual `α_i` it is lane RC28's
`alphaChar_conj`). -/
theorem conjC_hα₀_nonvacuous (C₀ : ActualConj K S₀) (i : ℕ) :
    ∀ σ, (1 : GKS K S₀ →* (Acoef i)ˣ) (C₀.conj σ) = ((1 : GKS K S₀ →* (Acoef i)ˣ) σ)⁻¹ :=
  fun _ => by simp

/-- PROVED (lane RC28's `hasRootsOfUnity_of_fullTorsion`). The hypothesis `hμ₀` follows from
`hFull₀`. -/
theorem conjC_hμ₀_of_fullTorsion (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
    (hFull₀ : FullTorsion K S₀ W (2 ^ i)) : HasRootsOfUnity K S₀ (2 ^ i) :=
  hasRootsOfUnity_of_fullTorsion K S₀ W (2 ^ i) hFull₀

end NonVacuity

end ZInQ.Manuscript.RC.KummerMaps
