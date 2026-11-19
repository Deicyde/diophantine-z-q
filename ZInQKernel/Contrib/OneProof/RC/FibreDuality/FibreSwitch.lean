import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Duality

/-!
# Lane RC31, part 9: the switch duality adjunction for non-discrete fibre coefficients

Manuscript `diophantine_zq.tex`, the switch at a derivative prime (tex 4855–4897 and 5055–5075):
"`U = im(H¹(C_rel ⊗ k) → F ⊕ S)` … The retained localization-duality diagrams give `U = U^⊥`.
Specifically, localization's connecting map is its dual under the strict/relaxed duality, so its
kernel is both `U` and `U^⊥`; this is the exactness in [Nekovář 6.3.3–6.3.4]" (tex 5062–5070), at
the characteristic-zero fibres (tex 4976–5200).

Lane RC26's `GenuineSwitch` packages the switch data for DISCRETE coefficients. `FibreSwitch` is the
same structure for arbitrary topological coefficients (the fibres `V_𝔭` of lane RC28 are not
discrete), and its adjunction is `ZInQ.Contrib.CloudB3RC53.SwitchInputs.SwitchDualityAdjunction`
(in `CloudB3RC53/SwitchInputs/QuasiSide.lean`), through lane RC26's cochain-level Nekovář 6.3.3
(`switchAdjunctionFromDuality_proof`, PROVED for any field) with the duality quasi-isomorphism
supplied by `fibreSelmerDualityT` (Nekovář 6.8.1).

* `FibreSwitch`, `FibreSwitch.ΔS`, `toQuasi`, `Dstr` (`Dstr_eq`), `δ`, `hex`, `SwitchCoordinates`.
* `FibreSwitch.adjunction`, `FibreSwitch.localizationDualityInput` (PROVED from `hγ`).
* **`FibreSwitch.adjunction_of_prints`** (PROVED from the PRINT `NekovarFibreGlobalDuality`, the
  local orthogonality of the strict and relaxed conditions and the switch coordinates).
* `exFibreSwitch`: non-vacuity.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain CategoryTheory
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.LambdaCoef (IsHeightOneOdd)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
  [ContinuousSMul (GKS K S) M]

/-- **Switch data with topological (not necessarily discrete) coefficients** (tex 5055–5075; the
non-discrete form of lane RC26's `GenuineSwitch`): genuine relaxed local conditions `ΔR`, strict
condition complexes `US v` with injective maps `φ v : US v → ΔR.U v`, the switch quotient
`g : ⊕_v ΔR.U v → W` (degreewise surjective with kernel the image of `φ`), and coordinates
`eR : H¹(W) ≃ k² × k²` (`F ⊕ S`). Kind: definition. -/
structure FibreSwitch where
  ΔR : GaloisLocalConditions K S k M
  US : Places K S → GCx k
  φ : ∀ v, GHom (US v) (ΔR.U v)
  W : GCx k
  g : GHom (galoisSelData K S k M ΔR).U W
  hfg : ∀ n (u : (piCx US).X n), g.f n n rfl ((piMap φ).f n n rfl u) = 0
  φ_inj : ∀ n, Function.Injective ((piMap φ).f n n rfl)
  g_surj : ∀ n, Function.Surjective (g.f n n rfl)
  ex : ∀ n (u : (galoisSelData K S k M ΔR).U.X n), g.f n n rfl u = 0 →
    ∃ u', (piMap φ).f n n rfl u' = u
  eR : W.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)

namespace FibreSwitch

variable {K S k M} (X : FibreSwitch K S k M)

/-- The strict local conditions `ΔS`: the complexes `US v` with the composite maps
`US v → ΔR.U v → C(G_v, M)`. Kind: definition. -/
def ΔS : GaloisLocalConditions K S k M := ⟨X.US, fun v => ghomComp (X.φ v) (X.ΔR.i v)⟩

/-- **The relaxed localization** (`QuasiRelaxedLocalization`): the genuine relaxed Selmer data,
the switch quotient and its coordinates. Kind: definition. -/
def toQuasi : QuasiRelaxedLocalization k := ⟨galoisSelData K S k M X.ΔR, X.W, X.g, X.eR⟩

/-- The strict Selmer data `C_str` (the restriction of the relaxed data along `φ`). Kind:
definition. -/
abbrev Dstr : SelData k :=
  ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData X.toQuasi.D (piMap X.φ)

/-- `C_str` is definitionally the genuine Selmer data of `ΔS`. Kind: PROVED. -/
theorem Dstr_eq : X.Dstr = galoisSelData K S k M X.ΔS := rfl

/-- **The connecting map** `δ : H¹(W_rel) → H²(C_str)` of `0 → C_str → C_rel → W_rel → 0`. Kind:
definition. -/
def δ : X.toQuasi.Wrel.toCC.homology 1 →ₗ[k] (selCx X.Dstr).toCC.homology 2 :=
  switchDelta X.toQuasi (piMap X.φ) X.hfg X.φ_inj X.g_surj X.ex

/-- Exactness at `H¹(W_rel)`: `im H¹(λ) = ker δ`. Kind: PROVED. -/
theorem hex : LinearMap.range (H1 (quotMap X.toQuasi.D X.toQuasi.gR)) = LinearMap.ker X.δ :=
  switchDelta_exact X.toQuasi (piMap X.φ) X.hfg X.φ_inj X.g_surj X.ex

/-- **The local residue pairing hypothesis** (tex 2816–2818 and 5037–5039: "the transported cross
pairing is exactly `β(x, y) = ε e₂(x, J y)`, `ε ∈ k^×`"): the trace of the Selmer cup product of
`(0, s, −ι u)` and `(0, t, 0)` is the switch pairing of the classes of `g t`, `g u` in the
coordinates. Kind: hypothesis (definition), the text's coordinate claim. -/
def SwitchCoordinates (Q : SelPairData X.Dstr X.toQuasi.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) : Prop :=
  ∀ (t u : X.toQuasi.D.U.X 1) (s : (piCx X.US).X 2) (_ht : X.toQuasi.D.U.d 1 2 rfl t = 0)
    (_hu : X.toQuasi.D.U.d 1 2 rfl u = (piMap X.φ).f 2 2 rfl s)
    (ct cu : LinearMap.ker (X.toQuasi.Wrel.d 1 2 rfl))
    (_hct : ct.1 = X.toQuasi.gR.f 1 1 rfl t) (_hcu : cu.1 = X.toQuasi.gR.f 1 1 rfl u),
    tr (selCupFun Q 2 1 3 rfl ((0 : X.toQuasi.D.G.X 2), s,
        -(X.toQuasi.D.ι.f 1 (2 - 1) (by omega) u))
        ((0 : X.toQuasi.D.G.X 1), t, (0 : X.toQuasi.D.L.X (1 - 1)))) =
      ZInQ.Manuscript.RC.Uniform.switchPairing ε σ J (X.toQuasi.eR (cls1 X.toQuasi.Wrel ct))
        (X.toQuasi.eR (cls1 X.toQuasi.Wrel cu))

/-- **The switch duality adjunction** (Nekovář 6.3.3 in cochain form, lane RC26's
`switchAdjunctionFromDuality_proof`): from the Selmer duality quasi-isomorphism
`C_str → Hom(C_rel, k)[−3]` and the switch coordinates. Kind: PROVED. -/
theorem adjunction (Q : SelPairData X.Dstr X.toQuasi.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (hsw : X.SwitchCoordinates Q tr ε σ J) :
    SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex :=
  switchAdjunctionFromDuality_proof k X.toQuasi (piCx X.US) (piMap X.φ) X.hfg X.φ_inj X.g_surj
    X.ex Q tr htr ε σ J hε hσ hJ2 hγ hsw

/-- **`U = U^⊥` for the relaxed localization image** (tex 5065–5070;
`ZInQ.Contrib.CloudB3RC53.SwitchInputs.localizationDualityInput_of_adjunction` in
`CloudB3RC53/SwitchInputs/QuasiSide.lean`). Kind: PROVED. -/
theorem localizationDualityInput (Q : SelPairData X.Dstr X.toQuasi.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (hsw : X.SwitchCoordinates Q tr ε σ J) :
    LocalizationDualityInput ε σ J hε hσ hJ2 X.toQuasi.U :=
  localizationDualityInput_of_adjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex
    (X.adjunction Q tr htr ε σ J hε hσ hJ2 hγ hsw)

end FibreSwitch

/-! ### At the fibres: the adjunction from the PRINT -/

section Fibre

variable {K S} {P : Ideal Lambda} [P.IsPrime] [IsHeightOneOdd P]
  {M T : Type}
  [AddCommGroup M] [Module (ResAt P) M] [Module Lambda M] [IsScalarTower Lambda (ResAt P) M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) (ResAt P) M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul (ResAt P) M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup T] [Module (ResAt P) T] [Module Lambda T] [IsScalarTower Lambda (ResAt P) T]
  [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) (ResAt P) T] [TopologicalSpace T]
  [IsTopologicalAddGroup T] [ContinuousConstSMul (ResAt P) T] [ContinuousSMul (GKS K S) T]

/-- **The switch adjunction at a fibre, from the PRINT** (tex 5055–5075; Nekovář 6.8.1 with
6.3.3): for switch data on a fibre coefficient module `M` with Nekovář's topology, a perfect
continuous equivariant self-pairing `β : M × M → T` with `T ≅ k(𝔭)(1)`, truncated isotropy data
for (strict, relaxed), a trace inducing `H³_c ≅ k(𝔭)`, the orthogonality of the strict and relaxed
conditions, and the switch coordinates, `SwitchDualityAdjunction` holds.
This is the duality of the Galois cochains of the fibre (DEPARTURE 5 of `Print.lean`); the
text's complexes are `C ⊗_R k` (tex 4977–4990), and `horth` for the text's derivative-prime
conditions `D⁰`, `D⁰ ⊕ (F ⊕ S)[−1]` (tex 4860–4875, 5059–5061) is not discharged here.
Kind: PROVED from the PRINT `NekovarFibreGlobalDuality`. -/
theorem FibreSwitch.adjunction_of_prints (X : FibreSwitch K S (ResAt P) M)
    (h : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (β : M →ₗ[ResAt P] M →ₗ[ResAt P] T)
    (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hβc : Continuous fun x : M × M => β x.1 x.2)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc X.ΔS X.ΔR)
    (tr : (galCompactTT S (ResAt P) β hβ hβc X.ΔS X.ΔR I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc X.ΔS X.ΔR I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) (horth : FibreOrthogonalComplementsT β hβ hβc X.ΔS X.ΔR I tr htr)
    (ε σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hJ2 : J * J = 1)
    (hsw : X.SwitchCoordinates (galPairDataT S (ResAt P) β hβ hβc X.ΔS X.ΔR I) tr ε σ J) :
    SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex :=
  X.adjunction (galPairDataT S (ResAt P) β hβ hβc X.ΔS X.ΔR I) tr htr ε σ J hε hσ hJ2
    (fibreSelmerDualityT β hβ hβc h hset hM hM hTl hT hb hb' X.ΔS X.ΔR I tr htr htr3 horth) hsw

end Fibre

/-! ### Non-vacuity -/

section NonVacuity

variable {k : Type} [Field k]

/-- The complex with `V` in every degree and zero differentials. Kind: definition. -/
def constCxF (V : Type) [AddCommGroup V] [Module k V] : GCx k where
  X _ := ModuleCat.of k V
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

theorem constCxF_toCC_d (V : Type) [AddCommGroup V] [Module k V] (i j : ℤ) :
    (constCxF (k := k) V).toCC.d i j = 0 := by
  by_cases h : i + 1 = j
  · ext x
    exact GCx.toCC_d_hom (constCxF (k := k) V) i j h x
  · exact (constCxF (k := k) V).toCC.shape i j h

/-- `H¹` of the complex with zero differentials is `V`. Kind: definition. -/
def constCxFH1 (V : Type) [AddCommGroup V] [Module k V] :
    (constCxF (k := k) V).toCC.homology 1 ≃ₗ[k] V :=
  (((constCxF (k := k) V).toCC.isoHomologyπ 0 1 (by simp) (constCxF_toCC_d V 0 1)).symm ≪≫
    (constCxF (k := k) V).toCC.iCyclesIso 1 2 (by simp) (constCxF_toCC_d V 1 2)).toLinearEquiv

variable (K : Type) [Field K] [NumberField K] (q : HeightOneSpectrum (𝓞 K))

/-- **Non-vacuity of `FibreSwitch`**: for `S = {q}` and the trivial coefficient module (with its
discrete topology, a special case), the relaxed condition `F ⊕ S = k² × k²` (zero differential,
zero map to the local complex), the strict condition `0`, and the switch quotient the identity onto
`F ⊕ S`. Kind: definition. -/
def exFibreSwitch :
    FibreSwitch K {q} k (TrivMod (GKS K {q}) PUnit) where
  ΔR := ⟨fun _ => constCxF ((Fin 2 → k) × (Fin 2 → k)), fun _ => zeroGHom _ _⟩
  US _ := ZInQ.Manuscript.RC.SelmerComplex.zeroCx k
  φ _ := zeroGHom _ _
  W := constCxF ((Fin 2 → k) × (Fin 2 → k))
  g :=
    { f := fun n m h => by
        subst h
        exact LinearMap.proj (R := k)
          (φ := fun _ : Places K {q} => ((Fin 2 → k) × (Fin 2 → k))) ⟨q, rfl⟩
      comm := fun i i₁ j j₁ hij h₁ h₂ hj x => by
        subst hij hj
        rfl }
  hfg _ _ := rfl
  φ_inj _ _ _ _ := funext fun _ => rfl
  g_surj _ y := ⟨fun _ => y, rfl⟩
  ex n u hu := ⟨0, by
    funext v
    have hv : v = ⟨q, rfl⟩ := Subsingleton.elim _ _
    subst hv
    exact hu.symm⟩
  eR := constCxFH1 _

end NonVacuity

end ZInQ.Manuscript.RC.FibreDuality
