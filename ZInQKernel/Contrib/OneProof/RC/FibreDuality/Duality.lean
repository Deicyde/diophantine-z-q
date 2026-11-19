import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Print

/-!
# Lane RC31, part 5: Selmer duality for the characteristic-zero fibres (consumer corollaries)

Manuscript `diophantine_zq.tex`: the height-one regularity step (tex 4976–5200), its derivative
switch (tex 4878–4897: "The transported duality and localization identities identify the relaxed
localization image with the kernel of its dual localization map, hence with its exact annihilator
[Nekovář 6.3.3–6.3.4]"), "Exact duality makes the relaxed localization image equal to the finite
plane" (tex 5000–5001), and "localization's connecting map is its dual under the strict/relaxed
duality, so its kernel is both `U` and `U^⊥`; this is the exactness in [Nekovář 6.3.3–6.3.4]"
(tex 5065–5070); for the finite modules the same statement is Lemma `ex:arith-conjugate-duality`
(tex 2761–2830).

Nekovář, *Selmer complexes*, Astérisque 310 (2006), 6.8.1 (p. 154): the localized version of the
duality Theorem 6.3.4 (p. 143) "by the same proof as in 5.6.3". Here, as in lane RC26, that proof
is the cochain-level five lemma on the two short exact sequences of 6.3.3 (`sesHom`,
`finiteSelmerDualityNode_proof`): the global duality map (the PRINT `NekovarFibreGlobalDuality`,
Nekovář 5.6.3(ii)) and the local duality map (orthogonal complements, Nekovář 6.2.7) are
quasi-isomorphisms, hence so is the Selmer duality map
`C_{U}(X) → Hom_{k(𝔭)}(C_{U⊥}(X'), k(𝔭))[−3]`. Over the field `k(𝔭)` the termwise dual computes
`RHom` (a field is self-injective).

* `FibreOrthogonalComplementsT`: Nekovář's orthogonal complements (6.2.7) for local conditions
  with truncated isotropy data on the fibres (the hypothesis the switching data must supply for
  their derivative conditions; tex 4855–4875).
* **`fibreSelmerDualityT`** (PROVED from the PRINT): the shape of lane RC26's
  `genuineSelmerDualityT`, for non-discrete coefficients over `k(𝔭)`.
* `fibreOrthogonal_relaxed_strictT` (PROVED): full against zero ("A full condition is paired with
  the zero condition", tex 2813–2814), for any truncated isotropy data and any trace.
* `fibreOrthogonal_strict_relaxedT` (PROVED from local duality and the trace normalization `hsum`)
  and `fibreOrthogonal_strict_relaxedT_of_print` (from the PRINT `NekovarFibreLocalDuality`).
* **`fibreSelmerDuality_relaxed_strict`, `fibreSelmerDuality_strict_relaxed`** (PROVED from the
  PRINTs): the duality between the full-condition and the zero-condition fibre Selmer complexes,
  both ways (not the derivative-prime strict/relaxed pair of tex 5059–5070).
* `exists_fibreSelmerDuality_strict_relaxed` (PROVED from the three PRINTs): with the canonical
  trace packet (`NekovarFibreTraces`: ONE packet of local traces `FibreLocalTraces`, and global
  traces normalized by it, `FibreLocalTraces.Normalizes`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain CategoryTheory Filter Topology
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.LambdaCoef (IsHeightOneOdd)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (truncSub SelPairDataTrunc selCupFun_toSelPairData)

/-- **A field is self-injective**, so the termwise dual of a complex over `k(𝔭)` computes `RHom`
(`TermwiseDualComputesRHom`). Kind: PROVED (Mathlib: modules over a semisimple ring are
injective). -/
theorem field_selfInjective (k : Type) [Field k] : Module.Injective k k :=
  Module.injective_of_isSemisimpleRing k k

section Generic

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k]
  {X X' T : Type}
  [AddCommGroup X] [Module k X] [DistribMulAction (GKS K S) X] [SMulCommClass (GKS K S) k X]
  [TopologicalSpace X] [ContinuousAdd X] [ContinuousConstSMul k X] [ContinuousSMul (GKS K S) X]
  [AddCommGroup X'] [Module k X'] [DistribMulAction (GKS K S) X'] [SMulCommClass (GKS K S) k X']
  [TopologicalSpace X'] [ContinuousAdd X'] [ContinuousConstSMul k X']
  [ContinuousSMul (GKS K S) X']
  [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul (GKS K S) T]
  (β : X →ₗ[k] X' →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a : X) (b : X'), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : X × X' => β x.1 x.2)

/-- **Orthogonal complements for the fibre data** (Nekovář 6.2.7, p. 140, with local products
into `τ≥2` as in 6.2.1.3 and 6.3.1): the local duality map
`(u, x) ↦ (v ↦ tr(0, x ∪ i' v + h(u, v) mod d(C¹)))` of the genuine truncated pairing data is a
quasi-isomorphism. Kind: hypothesis (definition), the input the actual local conditions must
supply. -/
def FibreOrthogonalComplementsT (ΔA : GaloisLocalConditions K S k X)
    (ΔB : GaloisLocalConditions K S k X') (I : GalTruncIsotropyData S k β hβ hβc ΔA ΔB)
    (tr : (galCompactTT S k β hβ hβc ΔA ΔB I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc ΔA ΔB I).d 2 3 rfl z) = 0) : Prop :=
  QuasiIso (GHom.toCC (localDualityMap (galPairDataT S k β hβ hβc ΔA ΔB I) tr htr))

/-- `LocalOrthogonalityInput` of the abstract duality node is `FibreOrthogonalComplementsT` for
the genuine fibre data (definitional). Kind: PROVED. -/
theorem localOrthogonalityInput_fibre_iff (ΔA : GaloisLocalConditions K S k X)
    (ΔB : GaloisLocalConditions K S k X') (I : GalTruncIsotropyData S k β hβ hβc ΔA ΔB)
    (tr : (galCompactTT S k β hβ hβc ΔA ΔB I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc ΔA ΔB I).d 2 3 rfl z) = 0)
    (Pc : PerfectCoefficientPairing k) :
    LocalOrthogonalityInput (galPairDataT S k β hβ hβc ΔA ΔB I) tr htr Pc ↔
      FibreOrthogonalComplementsT β hβ hβc ΔA ΔB I tr htr :=
  Iff.rfl

/-- **The Selmer duality map is a quasi-isomorphism once the global and the local duality maps are**
(Nekovář 6.3.4 via 6.3.3, p. 142–143; localized, 6.8.1): the cochain-level five lemma
(`finiteSelmerDualityNode_proof`) over the field `k`. Kind: PROVED. -/
theorem selmerDuality_of_global_local (ΔA : GaloisLocalConditions K S k X)
    (ΔB : GaloisLocalConditions K S k X') (I : GalTruncIsotropyData S k β hβ hβc ΔA ΔB)
    (tr : (galCompactTT S k β hβ hβc ΔA ΔB I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc ΔA ΔB I).d 2 3 rfl z) = 0)
    (hG : QuasiIso (GHom.toCC (globalDualityMap (galPairDataT S k β hβ hβc ΔA ΔB I) tr htr)))
    (hL : FibreOrthogonalComplementsT β hβ hβc ΔA ΔB I tr htr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galPairDataT S k β hβ hβc ΔA ΔB I) tr htr)) :=
  finiteSelmerDualityNode_proof k _ _ (galPairDataT S k β hβ hβc ΔA ΔB I) tr htr
    ⟨ModuleCat.of k k, ModuleCat.of k k, LinearMap.mul k k,
      ⟨fun a b h => by simpa using LinearMap.congr_fun h 1, fun f => ⟨f 1, LinearMap.ext fun x => by
        rw [LinearMap.mul_apply', mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]⟩⟩,
      ⟨fun a b h => by simpa using LinearMap.congr_fun h 1, fun f => ⟨f 1, LinearMap.ext fun x => by
        rw [LinearMap.flip_apply, LinearMap.mul_apply', ← smul_eq_mul, ← map_smul, smul_eq_mul,
          mul_one]⟩⟩⟩
    (Or.inl (field_selfInjective k)) hG hL

/-- **Truncated isotropy data for (full on `X`, zero on `X'`)**: the zero homotopies (the strict
side has no cochains, so the local product vanishes; lane RC26's `TruncIsotropyData.ofLowDegree`).
Kind: definition (non-vacuity of the hypothesis `I` of `fibreSelmerDuality_relaxed_strict`). -/
def relaxedStrictTruncIsotropy :
    GalTruncIsotropyData S k β hβ hβc (relaxedConditions k _ _ _ X) (strictConditions k _ _ _ X') :=
  TruncIsotropyData.ofLowDegree fun _ _ _ _ => Or.inr (show Subsingleton PUnit from inferInstance)

/-- **Truncated isotropy data for (zero on `X`, full on `X'`)**: the zero homotopies. Kind:
definition (non-vacuity of the hypothesis `I` of `fibreSelmerDuality_strict_relaxed`). -/
def strictRelaxedTruncIsotropy :
    GalTruncIsotropyData S k β hβ hβc (strictConditions k _ _ _ X) (relaxedConditions k _ _ _ X') :=
  TruncIsotropyData.ofLowDegree fun _ _ _ _ => Or.inl (show Subsingleton PUnit from inferInstance)

/-- **The dual identification `X' ≃ Hom_k(X, T)` of a perfect pairing** (`X' ≅ X^*(1)` for
`T ≅ k(1)`; manuscript tex 2805 "Thus `τ^*M_i ≃ M_i^*(1)`", at the fibres): the adjoint of
`β.flip`. Kind: definition. -/
def dualEquivOfPerfect (hb' : Function.Bijective β.flip) : X' ≃ₗ[k] (X →ₗ[k] T) :=
  LinearEquiv.ofBijective β.flip hb'

omit [NumberField K] [SMulCommClass (GKS K S) k X] [SMulCommClass (GKS K S) k X']
  [SMulCommClass (GKS K S) k T]
  [TopologicalSpace X] [ContinuousAdd X] [ContinuousConstSMul k X] [ContinuousSMul (GKS K S) X]
  [TopologicalSpace X'] [ContinuousAdd X'] [ContinuousConstSMul k X'] [ContinuousSMul (GKS K S) X']
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul (GKS K S) T] in
include hβ in
/-- **The dual identification is Galois-equivariant** for the contragredient action
`(σ f)(x) = σ • f(σ⁻¹ • x)` on `Hom_k(X, T)`. Kind: PROVED. -/
theorem dualEquivOfPerfect_smul (hb' : Function.Bijective β.flip) (σ : GKS K S) (y : X')
    (x : X) : dualEquivOfPerfect β hb' (σ • y) x = σ • dualEquivOfPerfect β hb' y (σ⁻¹ • x) := by
  change β x (σ • y) = σ • β (σ⁻¹ • x) y
  rw [← hβ σ (σ⁻¹ • x) y, smul_inv_smul]

/-- **The full condition is the orthogonal complement of the zero condition on the fibres**
(tex 2813–2814: "A full condition is paired with the zero condition"): for any truncated isotropy
data and any trace on the truncated cone, the local duality map of (full on `X`, zero on `X'`) is a
quasi-isomorphism — both sides are acyclic. Kind: PROVED. -/
theorem fibreOrthogonal_relaxed_strictT
    (I : GalTruncIsotropyData S k β hβ hβc (relaxedConditions k _ _ _ X)
      (strictConditions k _ _ _ X'))
    (tr : (galCompactTT S k β hβ hβc _ _ I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc _ _ I).d 2 3 rfl z) = 0) :
    FibreOrthogonalComplementsT β hβ hβc _ _ I tr htr := by
  unfold FibreOrthogonalComplementsT
  apply quasiIso_of_acyclic
  · rw [acyclic_toCC_iff]
    exact relaxed_locCx_acyclic (k := k) (GS := GKS K S) (Gv := fun v : Places K S => Gloc K v.1)
      (loc := fun v => locMap K S v.1) (M := X)
  · rw [acyclic_toCC_iff]
    intro i j l hij hjl φ _
    refine ⟨0, dualCx_ext fun x => ?_⟩
    have hx : x = 0 := funext fun _ => rfl
    rw [hx, map_zero, map_zero]

/-- **The zero condition is the orthogonal complement of the full condition on the fibres**
(Nekovář 6.2.7 via local duality): for finitely many places, local traces `tr_v` killing
coboundaries with every local duality map
`C^•_cont(G_{K_v}, X) → Hom_k(C^•_cont(G_{K_v}, X'), k)[−2]` a quasi-isomorphism, any truncated
isotropy data, and a trace on the truncated cone whose local part is `∑_v tr_v`, the zero
condition on `X` and the full condition on `X'` are orthogonal complements. Kind: PROVED (the
local duality map of the truncated data is that of the full-target data for the pulled-back trace,
and lane RC26's generic `quasiIso_localDualityMap_strict_relaxed`). -/
theorem fibreOrthogonal_strict_relaxedT [Fintype (Places K S)]
    (trv : ∀ v : Places K S, (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d (2 - 1) 2 (by omega) z) = 0)
    (hqi : ∀ v, QuasiIso (GHom.toCC (adjHom (localPair k (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc v) 2 (trv v)
        (htrv v))))
    (I : GalTruncIsotropyData S k β hβ hβc (strictConditions k _ _ _ X)
      (relaxedConditions k _ _ _ X'))
    (tr : (galCompactTT S k β hβ hβc _ _ I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc _ _ I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx k (GKS K S) T).X 3), (truncSub (localSumCx k (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    FibreOrthogonalComplementsT β hβ hβc _ _ I tr htr := by
  have hQ : galPairDataT S k β hβ hβc (strictConditions k _ _ _ X)
      (relaxedConditions k _ _ _ X') I =
      (genuinePairDataTrunc k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) β hβ hβc _ _ I).toSelPairData := rfl
  have h0 := quasiIso_localDualityMap_strict_relaxed k (GKS K S)
    (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc trv htrv hqi
    (trOfTrunc (genuinePairDataTrunc k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) β hβ hβc _ _ I) tr)
    (trOfTrunc_kills (genuinePairDataTrunc k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) β hβ hβc _ _ I) tr htr)
    (fun z => (trOfTrunc_apply (genuinePairDataTrunc k (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc _ _ I) tr _).trans
        (hsum z))
  unfold FibreOrthogonalComplementsT
  have e : GHom.toCC (localDualityMap (galPairDataT S k β hβ hβc _ _ I) tr htr) =
      GHom.toCC (localDualityMap (genuinePairData k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) β hβ hβc _ _ (strictRelaxedIsotropyGen k (GKS K S)
          (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc))
        (trOfTrunc (genuinePairDataTrunc k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) β hβ hβc _ _ I) tr)
        (trOfTrunc_kills (genuinePairDataTrunc k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) β hβ hβc _ _ I) tr htr)) := by
    refine (dualityMaps_eq_of_trace_eq _ _ _ _ _ _ fun i c c' => ?_).2.1
    obtain ⟨a, u, x⟩ := c
    have hu : u = 0 := funext fun _ => rfl
    subst hu
    refine (congrArg tr (selCupFun_toSelPairData (genuinePairDataTrunc k (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc _ _ I) i (3 - i) 3
      (by omega) (a, 0, x) c')).trans
      (Eq.trans ?_ (trOfTrunc_apply (genuinePairDataTrunc k (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc _ _ I) tr _).symm)
    congr 1
    refine Prod.ext rfl ?_
    change (truncSub _ (3 - 1)).mkQ _ = (truncSub _ (3 - 1)).mkQ _
    congr 1
    simp [ZInQ.Contrib.CloudB3RC53.SwitchInputs.selCupFunT, selCupFun]
    rfl
  rw [e]
  exact h0

end Generic

/-! ### At `k(𝔭)`, from the PRINTs -/

section Fibre

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {P : Ideal Lambda} [P.IsPrime] [IsHeightOneOdd P]
  {X X' T : Type}
  [AddCommGroup X] [Module (ResAt P) X] [Module Lambda X] [IsScalarTower Lambda (ResAt P) X]
  [DistribMulAction (GKS K S) X] [SMulCommClass (GKS K S) (ResAt P) X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousConstSMul (ResAt P) X] [ContinuousSMul (GKS K S) X]
  [AddCommGroup X'] [Module (ResAt P) X'] [Module Lambda X']
  [IsScalarTower Lambda (ResAt P) X'] [DistribMulAction (GKS K S) X']
  [SMulCommClass (GKS K S) (ResAt P) X'] [TopologicalSpace X'] [IsTopologicalAddGroup X']
  [ContinuousConstSMul (ResAt P) X'] [ContinuousSMul (GKS K S) X']
  [AddCommGroup T] [Module (ResAt P) T] [Module Lambda T] [IsScalarTower Lambda (ResAt P) T]
  [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) (ResAt P) T] [TopologicalSpace T]
  [IsTopologicalAddGroup T] [ContinuousConstSMul (ResAt P) T] [ContinuousSMul (GKS K S) T]
  (β : X →ₗ[ResAt P] X' →ₗ[ResAt P] T)
  (hβ : ∀ (g : GKS K S) (a : X) (b : X'), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : X × X' => β x.1 x.2)

/-- **Selmer duality for the characteristic-zero fibres** (Nekovář, *Selmer complexes*, 6.8.1,
p. 154: the localized 6.3.4; manuscript tex 4878–4897, 5000–5001, 5065–5070), in the shape of lane
RC26's `genuineSelmerDualityT`: under the fibre standing hypotheses, for coefficients with
Nekovář's topology, `T ≅ k(𝔭)(1)`, a perfect continuous equivariant pairing `β : X × X' → T`,
local conditions `ΔA`, `ΔB` with truncated isotropy data `I`, a trace inducing
`H³_c ≅ k(𝔭)`, and the orthogonality of the local conditions, the genuine Selmer duality map
`C_{ΔA}(X) → Hom_{k(𝔭)}(C_{ΔB}(X'), k(𝔭))[−3]` is a quasi-isomorphism.
This is the duality of the Galois cochains of the fibre (DEPARTURE 5 of `Print.lean`); the
text's complexes are `C ⊗_R k` (tex 4977–4990), and `horth` for the text's derivative-prime
conditions `D⁰`, `D⁰ ⊕ (F ⊕ S)[−1]` (tex 4860–4875, 5059–5061) is not discharged here.
Kind: PROVED from the PRINT `NekovarFibreGlobalDuality` (and the hypothesis `horth`). -/
theorem fibreSelmerDualityT (h : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hX : IsLatticeTop (GKS K S) X) (hX' : IsLatticeTop (GKS K S) X')
    (hTl : IsLatticeTop (GKS K S) T) (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (ΔA : GaloisLocalConditions K S (ResAt P) X) (ΔB : GaloisLocalConditions K S (ResAt P) X')
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc ΔA ΔB)
    (tr : (galCompactTT S (ResAt P) β hβ hβc ΔA ΔB I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc ΔA ΔB I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) (horth : FibreOrthogonalComplementsT β hβ hβc ΔA ΔB I tr htr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galPairDataT S (ResAt P) β hβ hβc ΔA ΔB I) tr htr)) :=
  selmerDuality_of_global_local β hβ hβc ΔA ΔB I tr htr
    (h S P hset X X' T hX hX' hTl hT β hβ hβc hb hb' ΔA ΔB I tr htr htr3) horth

/-- **The zero condition is the orthogonal complement of the full condition, from the local
duality PRINT** (`NekovarFibreLocalDuality`, Nekovář 5.6.3(i)): for one packet of local traces
`L` (inducing `H²(G_{K_v}, T) ≅ k(𝔭)`, one trivialization) and a global trace normalized by it
(`L.Normalizes tr`, lane RC26's `hsum`). Kind: PROVED from the PRINT. -/
theorem fibreOrthogonal_strict_relaxedT_of_print (h : NekovarFibreLocalDuality K)
    (hset : NekovarFibreSetting K S) (hX : IsLatticeTop (GKS K S) X)
    (hX' : IsLatticeTop (GKS K S) X') (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T) (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    [Fintype (Places K S)] (L : FibreLocalTraces S (ResAt P) T)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc (strictConditions (ResAt P) _ _ _ X)
      (relaxedConditions (ResAt P) _ _ _ X'))
    (tr : (galCompactTT S (ResAt P) β hβ hβc _ _ I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc _ _ I).d 2 3 rfl z) = 0)
    (hsum : L.Normalizes tr) :
    FibreOrthogonalComplementsT β hβ hβc _ _ I tr htr :=
  fibreOrthogonal_strict_relaxedT β hβ hβc L.trv L.htrv
    (fun v => h S P hset X X' T hX hX' hTl hT β hβ hβc hb hb' v (L.trv v) (L.htrv v) (L.iso v))
    I tr htr hsum

/-- **The relaxed fibre Selmer complex is dual to the strict one** (full conditions on `X`, zero
conditions on `X'` at every place of `S`; tex 2813–2814: "A full condition is paired with the
zero condition"): `C_rel(X) ≃ Hom_{k(𝔭)}(C_str(X'), k(𝔭))[−3]`. Not the strict/relaxed pair of
tex 5059–5070: at a derivative prime those are `D⁰` and `D⁰ ⊕ (F ⊕ S)[−1]`, "not the full local
complex" (tex 4855–4876); that duality is `fibreSelmerDualityT` with `horth` for those conditions.
Kind: PROVED from the PRINT `NekovarFibreGlobalDuality`. -/
theorem fibreSelmerDuality_relaxed_strict (h : NekovarFibreGlobalDuality K)
    (hset : NekovarFibreSetting K S) (hX : IsLatticeTop (GKS K S) X)
    (hX' : IsLatticeTop (GKS K S) X') (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T) (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc (relaxedConditions (ResAt P) _ _ _ X)
      (strictConditions (ResAt P) _ _ _ X'))
    (tr : (galCompactTT S (ResAt P) β hβ hβc _ _ I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc _ _ I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galPairDataT S (ResAt P) β hβ hβc _ _ I) tr htr)) :=
  fibreSelmerDualityT β hβ hβc h hset hX hX' hTl hT hb hb' _ _ I tr htr htr3
    (fibreOrthogonal_relaxed_strictT β hβ hβc I tr htr)

/-- **The strict fibre Selmer complex is dual to the relaxed one** (zero conditions on `X`, full
conditions on `X'`): `C_str(X) ≃ Hom_{k(𝔭)}(C_rel(X'), k(𝔭))[−3]`, for a global trace normalized
by ONE packet of local traces `L` (`L.Normalizes tr`; the local and global traces share one
trivialization). Kind: PROVED from the PRINTs `NekovarFibreGlobalDuality` and
`NekovarFibreLocalDuality`. -/
theorem fibreSelmerDuality_strict_relaxed (hG : NekovarFibreGlobalDuality K)
    (hL : NekovarFibreLocalDuality K) (hset : NekovarFibreSetting K S)
    (hX : IsLatticeTop (GKS K S) X) (hX' : IsLatticeTop (GKS K S) X')
    (hTl : IsLatticeTop (GKS K S) T) (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) [Fintype (Places K S)]
    (L : FibreLocalTraces S (ResAt P) T)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc (strictConditions (ResAt P) _ _ _ X)
      (relaxedConditions (ResAt P) _ _ _ X'))
    (tr : (galCompactTT S (ResAt P) β hβ hβc _ _ I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc _ _ I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) (hsum : L.Normalizes tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galPairDataT S (ResAt P) β hβ hβc _ _ I) tr htr)) :=
  fibreSelmerDualityT β hβ hβc hG hset hX hX' hTl hT hb hb' _ _ I tr htr htr3
    (fibreOrthogonal_strict_relaxedT_of_print β hβ hβc hL hset hX hX' hTl hT hb hb' L I tr htr
      hsum)

/-- **The strict/relaxed fibre duality with the canonical trace packet**: under the three PRINTs,
there is ONE packet of local traces `L` such that for any truncated isotropy data of (zero on `X`,
full on `X'`) there is a global trace normalized by `L` (the canonical `r_S`, Nekovář 5.4.1) for
which the strict fibre Selmer complex of `X` is dual to the relaxed one of `X'`. Kind: PROVED from
the PRINTs. -/
theorem exists_fibreSelmerDuality_strict_relaxed (hG : NekovarFibreGlobalDuality K)
    (hL : NekovarFibreLocalDuality K) (hTr : NekovarFibreTraces K)
    (hset : NekovarFibreSetting K S) (hX : IsLatticeTop (GKS K S) X)
    (hX' : IsLatticeTop (GKS K S) X') (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T) (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    [Fintype (Places K S)] :
    ∃ L : FibreLocalTraces S (ResAt P) T,
      ∀ I : GalTruncIsotropyData S (ResAt P) β hβ hβc (strictConditions (ResAt P) _ _ _ X)
        (relaxedConditions (ResAt P) _ _ _ X'),
      ∃ (tr : (galCompactTT S (ResAt P) β hβ hβc _ _ I).X 3 →ₗ[ResAt P] ResAt P)
        (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc _ _ I).d 2 3 rfl z) = 0),
        InducesIsoH3 tr ∧ L.Normalizes tr ∧
          QuasiIso (GHom.toCC (selmerDualityMap (galPairDataT S (ResAt P) β hβ hβc _ _ I)
            tr htr)) := by
  obtain ⟨L, hglob⟩ := hTr S P hset T hTl hT
  refine ⟨L, fun I => ?_⟩
  obtain ⟨tr, htr, htr3, hsum⟩ := hglob X X' β hβ hβc _ _ I
  exact ⟨tr, htr, htr3, hsum, fibreSelmerDuality_strict_relaxed β hβ hβc hG hL hset hX hX' hTl
    hT hb hb' L I tr htr htr3 hsum⟩

end Fibre

end ZInQ.Manuscript.RC.FibreDuality
