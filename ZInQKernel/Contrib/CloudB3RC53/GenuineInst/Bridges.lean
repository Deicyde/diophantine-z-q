import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Instances
import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.NaturalStep

/-!
# Genuine instantiations, part 1: CommonCoordinate and Torsion over the genuine Selmer data

The other team's genuine Selmer complexes (`RC/SelmerComplex/`: `galoisSelData K S R M Δ`, the
genuine cup products `globalPair`, `localSumPair`, the genuine restriction `resS`, and
`genuineRetainedPairing`) meet two interfaces of this area:

* **CommonCoordinate** (tex L4159–4177). `GenuineRetention` is the place-by-place retention datum
  of `CommonCoordinate.PlaceRetention` for the genuine relaxed and orthogonal Selmer data, with the
  targets and cup products the genuine ones (only the per-place homotopies, the projections and
  the retention equalities remain as data). `GenuineRetention.toPlaceRetention` gives the
  `PlaceRetention`, and `GenuineRetention.toRetainedPairing_eq` identifies its retained pairing
  with the other team's `genuineRetainedPairing` (the retention equality being PROVED by
  `PlaceRetention.retained`). `selmerFunctionals_of_genuine` feeds the genuine data into
  `CommonCoordinate.SelmerFunctionals`, hence into `NaturalStep` and RC0's `h47`.
* **Torsion** (tex L4051–4064). `KummerModelIdentification` over the genuine data is the other
  team's `GenuineKummerModelIdentification`; `hK_of_genuine_identification` and
  `hvprim_of_genuine_identification` are Torsion's valuation outputs for it.

**Classification.** PROVED (packaging; the identification inputs remain those of the interfaces).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open NumberField IsDedekindDomain CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.CommonCoordinate
  ZInQ.Manuscript.RC.SelmerComplex

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

section Retention

variable {R : Type} [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

variable (R T) in
/-- The genuine local target `⊕_{v ∈ S} C^•_cont(G_{K_v}, T)`. -/
abbrev genEL : GCx R :=
  localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T

/-- The genuine local cup product `⊕_v C(G_v, M) × ⊕_v C(G_v, M') → ⊕_v C(G_v, T)`. -/
abbrev genCupL :=
  localSumPair R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
    (continuous_pairing β)

/-- **Place-by-place retention for the genuine Selmer data** (tex L4159–4166): the fields of
`PlaceRetention` other than the targets and cup products, which are the genuine ones. -/
structure GenuineRetention (ΔR : GaloisLocalConditions K S R M')
    (ΔPp : GaloisLocalConditions K S R M) {UP US : GCx R}
    (fP : GHom UP (galoisSelData K S R M' ΔR).U) (fS : GHom US (galoisSelData K S R M ΔPp).U) where
  /-- The index type of places. -/
  ι : Type
  /-- The old places. -/
  old : Finset ι
  /-- The old local condition at `v` (primitive/relaxed side). -/
  Uo : ι → GCx R
  /-- The old orthogonal local condition at `v`. -/
  Uo' : ι → GCx R
  /-- The old isotropy homotopy at `v`. -/
  hv : ∀ (v : ι) (i j l : ℤ), i + j = l + 1 →
    (Uo' v).X i →ₗ[R] (Uo v).X j →ₗ[R] (genEL K S R T).X l
  /-- The new place `q`. -/
  NP : UnramifiedNewPlace R
  /-- The orthogonal of the unramified condition at `q`. -/
  Uq' : GCx R
  /-- The isotropy homotopy at `q`. -/
  hq : ∀ i j l : ℤ, i + j = l + 1 → Uq'.X i →ₗ[R] NP.Uq.X j →ₗ[R] (genEL K S R T).X l
  pR : ∀ (v : ι) (j : ℤ), (galoisSelData K S R M' ΔR).U.X j →ₗ[R] (Uo v).X j
  pP : ∀ (v : ι) (j : ℤ), UP.X j →ₗ[R] (Uo v).X j
  pS : ∀ (v : ι) (i : ℤ), US.X i →ₗ[R] (Uo' v).X i
  pPp : ∀ (v : ι) (i : ℤ), (galoisSelData K S R M ΔPp).U.X i →ₗ[R] (Uo' v).X i
  qR : ∀ j : ℤ, (galoisSelData K S R M' ΔR).U.X j →ₗ[R] NP.Lq.X j
  qP : ∀ j : ℤ, UP.X j →ₗ[R] NP.Uq.X j
  qPp : ∀ i : ℤ, (galoisSelData K S R M ΔPp).U.X i →ₗ[R] Uq'.X i
  hR : ∀ i j l : ℤ, i + j = l + 1 →
    US.X i →ₗ[R] (galoisSelData K S R M' ΔR).U.X j →ₗ[R] (genEL K S R T).X l
  hR_eq : ∀ (i j l : ℤ) (h : i + j = l + 1) (x : US.X i) (y : (galoisSelData K S R M' ΔR).U.X j),
    hR i j l h x y = ∑ v ∈ old, hv v i j l h (pS v i x) (pR v j y)
  isoR : ∀ (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hl : l + 1 = l₁) (u : US.X i) (v : (galoisSelData K S R M' ΔR).U.X j),
    (genEL K S R T).d l l₁ hl (hR i j l h u v) + hR i₁ j l₁ (by omega) (US.d i i₁ hi u) v +
        ZInQ.Contrib.CloudB3RC53.PairedFunctional.sgn i • hR i j₁ l₁ (by omega) u ((galoisSelData K S R M' ΔR).U.d j j₁ hj v) =
      (genCupL K S β hβ).P i j l₁ (by omega)
        ((ghomComp fS (galoisSelData K S R M ΔPp).ι).f i i rfl u)
        ((galoisSelData K S R M' ΔR).ι.f j j rfl v)
  hP : ∀ i j l : ℤ, i + j = l + 1 →
    (galoisSelData K S R M ΔPp).U.X i →ₗ[R] UP.X j →ₗ[R] (genEL K S R T).X l
  hP_eq : ∀ (i j l : ℤ) (h : i + j = l + 1) (x : (galoisSelData K S R M ΔPp).U.X i) (y : UP.X j),
    hP i j l h x y = ∑ v ∈ old, hv v i j l h (pPp v i x) (pP v j y) + hq i j l h (qPp i x) (qP j y)
  isoP : ∀ (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hl : l + 1 = l₁) (u : (galoisSelData K S R M ΔPp).U.X i) (v : UP.X j),
    (genEL K S R T).d l l₁ hl (hP i j l h u v) +
        hP i₁ j l₁ (by omega) ((galoisSelData K S R M ΔPp).U.d i i₁ hi u) v +
        ZInQ.Contrib.CloudB3RC53.PairedFunctional.sgn i • hP i j₁ l₁ (by omega) u (UP.d j j₁ hj v) =
      (genCupL K S β hβ).P i j l₁ (by omega) ((galoisSelData K S R M ΔPp).ι.f i i rfl u)
        ((ghomComp fP (galoisSelData K S R M' ΔR).ι).f j j rfl v)
  ret_P : ∀ (v : ι) (j : ℤ) (y : UP.X j), pR v j (fP.f j j rfl y) = pP v j y
  ret_S : ∀ (v : ι) (i : ℤ) (x : US.X i), pPp v i (fS.f i i rfl x) = pS v i x
  q_P : ∀ (j : ℤ) (y : UP.X j), qR j (fP.f j j rfl y) = NP.ιq.f j j rfl (qP j y)
  q_S : ∀ (i : ℤ) (x : US.X i), qPp i (fS.f i i rfl x) = 0

variable {K S β hβ} {ΔR : GaloisLocalConditions K S R M'} {ΔPp : GaloisLocalConditions K S R M}
  {UP US : GCx R} {fP : GHom UP (galoisSelData K S R M' ΔR).U}
  {fS : GHom US (galoisSelData K S R M ΔPp).U}

/-- The `PlaceRetention` of the genuine retention datum: genuine targets
`C^•_cont(G_{K,S}, T)`, `⊕_v C^•_cont(G_{K_v}, T)`, the genuine restriction and cup products, and the
genuine compatibility `res(a ∪ b) = res a ∪ res b` (the other team's, PROVED). -/
def GenuineRetention.toPlaceRetention (G : GenuineRetention K S β hβ ΔR ΔPp fP fS) :
    PlaceRetention (galoisSelData K S R M' ΔR) (galoisSelData K S R M ΔPp) fP fS where
  E := (genuineRetainedPairing K S β hβ ΔR ΔPp fP fS G.hR G.isoR G.hP G.isoP
    (fun i j l h u v => by
      rw [G.hR_eq, G.hP_eq, G.q_S, map_zero, LinearMap.zero_apply, add_zero]
      exact Finset.sum_congr rfl fun w _ => by rw [G.ret_P, G.ret_S])).E
  EL := genEL K S R T
  resE := resS R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T
  cupG := globalPair R (GKS K S) β hβ (continuous_pairing β)
  cupL := genCupL K S β hβ
  compat := (genuineRetainedPairing K S β hβ ΔR ΔPp fP fS G.hR G.isoR G.hP G.isoP
    (fun i j l h u v => by
      rw [G.hR_eq, G.hP_eq, G.q_S, map_zero, LinearMap.zero_apply, add_zero]
      exact Finset.sum_congr rfl fun w _ => by rw [G.ret_P, G.ret_S])).compat
  ι := G.ι
  old := G.old
  Uo := G.Uo
  Uo' := G.Uo'
  hv := G.hv
  NP := G.NP
  Uq' := G.Uq'
  hq := G.hq
  pR := G.pR
  pP := G.pP
  pS := G.pS
  pPp := G.pPp
  qR := G.qR
  qP := G.qP
  qPp := G.qPp
  hR := G.hR
  hR_eq := G.hR_eq
  isoR := G.isoR
  hP := G.hP
  hP_eq := G.hP_eq
  isoP := G.isoP
  ret_P := G.ret_P
  ret_S := G.ret_S
  q_P := G.q_P
  q_S := G.q_S

/-- **The bridge to the other team's `genuineRetainedPairing`**: the retained pairing of the
genuine place-by-place retention datum is `genuineRetainedPairing` with the retention equality
supplied by `PlaceRetention.retained` (PROVED, definitional). -/
theorem GenuineRetention.toRetainedPairing_eq (G : GenuineRetention K S β hβ ΔR ΔPp fP fS) :
    G.toPlaceRetention.toRetainedPairing =
      genuineRetainedPairing K S β hβ ΔR ΔPp fP fS G.hR G.isoR G.hP G.isoP
        G.toPlaceRetention.retained :=
  rfl

/-- **`SelmerFunctionals` from the genuine data** (tex L4159–4177): the triangular-basis
functionals are the paired functionals of the genuine retained pairing, read into the coordinate
ring `KC` through `ψ`. Feeds `NaturalStep` and hence RC0's `h47`. PROVED. -/
theorem selmerFunctionals_of_genuine {KC : Type} [CommRing KC] {n : ℕ} {κ : Type}
    {wR : Fin n ⊕ κ → KC} {wP : Fin n → KC} {eK : KC}
    (G : GenuineRetention K S β hβ ΔR ΔPp fP fS)
    (tr : (coneCx G.toPlaceRetention.toRetainedPairing.QP.resE).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((coneCx G.toPlaceRetention.toRetainedPairing.QP.resE).d 2 3 rfl z) = 0)
    (zS : (selCx (restrictData (galoisSelData K S R M ΔPp) fS)).X 1)
    (zP : (selCx (galoisSelData K S R M ΔPp)).X 1) (e : R)
    (b : (selCx (galoisSelData K S R M ΔPp)).X 0)
    (hlift : (changeMap (galoisSelData K S R M ΔPp) fS).f 1 1 rfl zS =
      e • zP + (selCx (galoisSelData K S R M ΔPp)).d 0 1 rfl b)
    (φP : Fin n → (selCx (restrictData (galoisSelData K S R M' ΔR) fP)).X 2)
    (hφP : ∀ i, (selCx (restrictData (galoisSelData K S R M' ΔR) fP)).d 2 3 rfl (φP i) = 0)
    (φR : Fin n ⊕ κ → (selCx (galoisSelData K S R M' ΔR)).X 2)
    (hφR : ∀ i, φR (Sum.inl i) = (changeMap (galoisSelData K S R M' ΔR) fP).f 2 2 rfl (φP i))
    (ψ : R →+* KC) (he : ψ e = eK)
    (hwR : ∀ j, wR j = ψ (pairedFun G.toPlaceRetention.toRetainedPairing.QR
      (tr : (coneCx G.toPlaceRetention.toRetainedPairing.QR.resE).X 3 →ₗ[R] R) zS (φR j)))
    (hwP : ∀ i, wP i = ψ (pairedFun G.toPlaceRetention.toRetainedPairing.QP tr zP (φP i))) :
    SelmerFunctionals wR wP eK :=
  ⟨CommRingCat.of R, galoisSelData K S R M' ΔR, galoisSelData K S R M ΔPp, UP, US, fP, fS,
    G.toPlaceRetention, tr, htr, zS, zP, e, b, hlift, φP, hφP, φR, hφR, ψ, he, hwR, hwP⟩

end Retention

section Kummer

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
  ZInQ.Contrib.CloudB3RC53.Calibration ZInQ.Contrib.CloudB3RC53.Torsion

variable {M : Type} [AddCommGroup M] [Module (PowerSeries ℚ_[2]) M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) (PowerSeries ℚ_[2]) M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul (PowerSeries ℚ_[2]) M]
  [ContinuousSMul (GKS K S) M] {Δ : GaloisLocalConditions K S (PowerSeries ℚ_[2]) M}

/-- **Torsion's `hK` for the genuine Kummer identification** (tex L4051–4064). PROVED. -/
theorem hK_of_genuine_identification
    (I : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ) (j vL vm gA sA : ℤ)
    (hu₀v : v2 (central I.u₀) = 0)
    (ha : v2 (central I.a) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (hb : v2 (central I.b) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (h₁ : v2 (central I.δ₁) = gA) (h₂ : v2 (central I.δ₂) = sA) (h₃ : v2 (central I.δ₃) = gA) :
    v2 (central I.coord) = (((j + vL + vm) + (j + vL + vm) +
      (Central.diskContribution 1 gA + Central.diskContribution 2 sA +
        Central.diskContribution 3 gA) : ℤ) : WithTop ℤ) :=
  hK_of_identification I j vL vm gA sA hu₀v ha hb h₁ h₂ h₃

/-- **RC0's `hvprim` for the genuine Kummer identification** (tex L4051–4080). PROVED. -/
theorem hvprim_of_genuine_identification
    (I : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ) (j vL vm gA sA vN ω : ℤ)
    (hu₀v : v2 (central I.u₀) = 0)
    (ha : v2 (central I.a) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (hb : v2 (central I.b) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (h₁ : v2 (central I.δ₁) = gA) (h₂ : v2 (central I.δ₂) = sA) (h₃ : v2 (central I.δ₃) = gA)
    {uprim δW : PowerSeries ℚ_[2]} (htri : δW * uprim = I.coord)
    (hδ : v2 (central δW) = ((2 * vN + 4 * ω : ℤ) : WithTop ℤ)) :
    v2 (central uprim) = ((primValuation j vL vm gA sA vN ω : ℤ) : WithTop ℤ) :=
  hvprim_of_identification I j vL vm gA sA vN ω hu₀v ha hb h₁ h₂ h₃ htri hδ

end Kummer

end ZInQ.Contrib.CloudB3RC53.GenuineInst
