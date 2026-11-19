import ZInQKernel.Contrib.CloudB3RC53.Hsw.CupOneGeneral
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncReverse
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefDerivative
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericCoords
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Iota
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthActual

/-!
# Strict local symmetry: the actual degree bounds

For strict and relaxed local complexes S and U, an inclusion f : S → U, a local
inclusion i : U → L, and a forward isotropy homotopy h, the general strict-symmetry
condition in degrees (2, 1) is

  h(s, f t) = c h(t, f s) + X(i f s, i f t) - Z(i f s, i f d t).

Its truncated version requires the difference of the two sides to lie in d(E¹).
The integration convention uses H₂₁(i f s, i f t) instead of X - Z and imposes
this condition at every place, also modulo d(E¹). Both conditions are automatic
if S² = 0, independently of the chosen forward isotropy homotopy.

The genuine derivative condition `strictAt` is [Z⁰ → 0], and `relaxedAt` is
[C⁰ → Z¹]. The genuine Kummer conditions `kummerAt`, `actualKummerAt`, and
`actualKummerAtS` have terms C⁰ and span(Kummer cocycles) + B¹ in degrees 0 and 1,
and zero in degree 2. The unramified condition is [M → M] in degrees 0 and 1.
These are degree bounds for the defined complexes, not just statements about H².

Manuscript support:
* Lemma ex:arith-local-kummer, tex 3413–3456: derived reduction retains torsion
  in degree 0 and the Kummer quotient in degree 1.
* Lemma ex:limits-derivative-switch, tex 4834–4887: D² belongs to the ambient
  local complex, not to any of its four derivative conditions.
* tex 3471–3498: the unramified complex and retention of arbitrary old conditions.
* tex 5055–5061: old Kummer, unramified, previous derivative, and full conditions
  are retained during a switch.

The last point matters: an unchanged full condition is not a low-degree
condition. `switch_degreeTwoZero_iff` makes the exact old-place requirement
explicit, and `fullAt_not_degreeTwoZero` shows why it cannot be silently dropped.
No external arithmetic fact or new printed premise is needed for these bounds.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.StrictLocal

open CategoryTheory NumberField IsDedekindDomain
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules
  ZInQ.Manuscript.RC.KummerMaps
  ZInQ.Manuscript.RC.HeegnerAlgebra

/-- The degree-two term itself is zero, not merely its cohomology. -/
def DegreeTwoZero {k : Type} [CommRing k] (U : GCx k) : Prop :=
  ∀ x : U.X 2, x = 0

/-- A product of local conditions has zero degree-two term exactly when every factor does. -/
theorem degreeTwoZero_pi_iff {k : Type} [CommRing k] {V : Type} (U : V → GCx k) :
    DegreeTwoZero (piCx U) ↔ ∀ v, DegreeTwoZero (U v) := by
  classical
  constructor
  · intro h v x
    have hx := congrFun (h (Pi.single v x)) v
    change (Pi.single v x : ∀ w, (U w).X 2) v = 0 at hx
    simpa only [Pi.single_eq_same] using hx
  · intro h x
    exact funext fun v => h v (x v)

/-- A genuine two-term complex in degrees 0 and 1 has zero degree-two term. -/
theorem double_degreeTwoZero {k : Type} [CommRing k] {A B : Type}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] (d : A →ₗ[k] B) :
    DegreeTwoZero (ofCC (dblCx d)) := by
  change ∀ x : (dblCx d).X 2, x = 0
  have : Subsingleton ((dblCx d).X 2) :=
    ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_double_X (ModuleCat.ofHom d) rel01 2 (by decide) (by decide))
  intro x
  exact Subsingleton.elim x 0

section GaloisConditions

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] {M : Type}
  [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- Both actual derivative truncations omit the ambient degree-two term (tex 4834–4887). -/
theorem derivativeAt_degreeTwoZero (v : Places K S) :
    DegreeTwoZero (strictAt K S k M v).U ∧ DegreeTwoZero (relaxedAt K S k M v).U :=
  ⟨double_degreeTwoZero (0 : Z0K k (Gloc K v.1) (ResMod (locMap K S v.1) M) →ₗ[k] PUnit),
    double_degreeTwoZero (relaxedDK k (Gloc K v.1) (ResMod (locMap K S v.1) M))⟩

omit [ContinuousAdd M] [ContinuousConstSMul k M] in
/-- The actual finite-level Kummer subcomplex, for any equivariant coefficient map, has U² = 0. -/
theorem kummerAt_degreeTwoZero (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (B : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] (m : ℕ) [NeZero m]
    (j : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)
    (hj : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), j (σ • t) = σ • j t) :
    DegreeTwoZero (kummerAt (k := k) v B m j hj).U := by
  have : Subsingleton ((kummerAt (k := k) v B m j hj).U.X 2) :=
    orth_kummerAt_concentrated v B m j hj 2 (by decide) (by decide)
  intro x
  exact Subsingleton.elim x 0

omit [DiscreteTopology M] in
/-- Full continuous cochains really have degree-two cochains, even when their H² vanishes. -/
theorem fullAt_not_degreeTwoZero [Nontrivial M] (v : Places K S) :
    ¬ DegreeTwoZero (fullAt K S k M v).U := by
  intro hzero
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let x : contCochain k (Gloc K v.1) (ResMod (locMap K S v.1) M) 2 :=
    ⟨(fun _ => m : (Fin 2 → Gloc K v.1) → ResMod (locMap K S v.1) M), continuous_const⟩
  have hx := congrArg
    (fun y : contCochain k (Gloc K v.1) (ResMod (locMap K S v.1) M) 2 =>
      cFun y (fun _ => 1)) (hzero x)
  exact hm hx

end GaloisConditions

section ActualKummer

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}

/-- Degree-two vanishing for the Kummer condition with the actual twist and coefficient map. -/
theorem actualKummerAt_degreeTwoZero (W : WeierstrassCurve K) [W.IsElliptic]
    (a : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
    (α : GKS K S →* (Acoef a)ˣ) [IsOpenKer α]
    (hFull : FullTorsion K S W (2 ^ a)) (v : Places K S)
    (hα : IsLocallyQuadAt a α (quadChar s hs hs0) v.1) :
    DegreeTwoZero (actualKummerAt W a s hs hs0 α hFull v hα).U := by
  classical
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact kummerAt_degreeTwoZero v (localTwist W h v.1) (2 ^ a)
    (kummerIota W a s hs hs0 α hFull v.1)
    (kummerIota_smul W a s hs hs0 α hFull v.1 hα)

/-- The same degree bound for the actual Kummer condition inflated from the coefficient support. -/
theorem actualKummerAtS_degreeTwoZero {S₀ : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]
    (a : ℕ) (s : KS K S₀) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
    (α : GKS K S₀ →* (Acoef a)ˣ) [IsOpenKer α]
    (hFull : FullTorsion K S₀ W (2 ^ a)) (v : Places K S)
    (hα : IsLocallyQuadAt (S := S₀) a α (quadChar s hs hs0) v.1) :
    DegreeTwoZero (actualKummerAtS hS W a s hs hs0 α hFull v hα).U := by
  classical
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact kummerAt_degreeTwoZero v (localTwist W h v.1) (2 ^ a)
    (kummerIotaS hS W a s hs hs0 α hFull v)
    (kummerIotaS_smul hS W a s hs hs0 α hFull v hα)

end ActualKummer

section Unramified

variable {K : Type} [Field K] [NumberField K]
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
  (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [DistribMulAction (GKS K S₀) M₀]
  [SMulCommClass (GKS K S₀) k M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
  [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]

/-- The actual unramified condition at a newly added support place has degree-two term zero. -/
theorem urAt_degreeTwoZero (v : Places K S) (hv : v.1 ∉ S₀) :
    DegreeTwoZero (urAt hS k M₀ v hv).U := by
  have : Subsingleton ((urAt hS k M₀ v hv).U.X 2) :=
    orth_urAt_vanishes hS k M₀ v hv 2 (by decide) (by decide)
  intro x
  exact Subsingleton.elim x 0

end Unramified

section SwitchFamily

variable {k : Type} [Field k] {V : Type} [DecidableEq V]
  (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  (Mv : V → Type) [∀ v, AddCommGroup (Mv v)] [∀ v, Module k (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) k (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, ContinuousAdd (Mv v)]
  [∀ v, ContinuousConstSMul k (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]

/-- For the defined derivative switch, only the unchanged old places can contribute U_str². -/
theorem switch_degreeTwoZero_iff (q : V)
    (old : ∀ v, SubFam (locCxK k Gv Mv v)) (T : ∀ v, Set (Gv v)) :
    DegreeTwoZero (switchFamK k Gv Mv q old T).Ustr ↔
      ∀ v, v ≠ q → DegreeTwoZero (old v).cx := by
  rw [degreeTwoZero_pi_iff]
  constructor
  · intro h v hv
    have hh := h v
    simpa only [switchFamK, switchStr_neK q old hv] using hh
  · intro h v
    by_cases hv : v = q
    · subst v
      change DegreeTwoZero ((switchStrK k Gv Mv q old q).cx)
      rw [switchStr_qK]
      change ∀ x : (⊥ : Submodule k ((locCxK k Gv Mv q).X 2)), x = 0
      intro x
      exact Subtype.ext ((Submodule.mem_bot k).1 x.2)
    · change DegreeTwoZero ((switchStrK k Gv Mv q old v).cx)
      rw [switchStr_neK q old hv]
      exact h v hv

end SwitchFamily

section AbstractSymmetry

variable {k : Type} [Field k]
  (D : SelData k) (Ustr : GCx k) (f : GHom Ustr D.U)

/-- The exact strict-symmetry target is automatic for any isotropy datum when U_str² = 0. -/
theorem strictSymm_of_degreeTwoZero (Q : SelPairData (restrictData D f) D)
    {P : GPair D.L D.L Q.EL} {c : k}
    (Cd : ZInQ.Contrib.CloudB3RC53.Hsw.PairCupOneGen P c) (h2 : DegreeTwoZero Ustr) :
    ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymm D Ustr f Q Cd :=
  ZInQ.Contrib.CloudB3RC53.Hsw.strictSymm_of_zero D Ustr f Q Cd h2

/-- The same reduction before and after the canonical target truncation. -/
theorem strictSymmTrunc_of_degreeTwoZero (Q : SelPairDataTrunc (restrictData D f) D)
    {P : GPair D.L D.L Q.EL} {c : k}
    (Cd : ZInQ.Contrib.CloudB3RC53.Hsw.PairCupOneGen P c) (h2 : DegreeTwoZero Ustr) :
    ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymmTrunc D Ustr f Q Cd ∧
      ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymm D Ustr f Q.toSelPairData Cd.trunc := by
  have hsym : ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymmTrunc D Ustr f Q Cd := by
    intro s t
    rw [h2 s]
    simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero, sub_zero, sub_self]
    have hz : Q.hU 2 1 2 rfl (0 : Ustr.X 2) (f.f 1 1 rfl t) = 0 :=
      LinearMap.map_zero₂ _ _
    rw [hz]
    exact Submodule.zero_mem _
  exact ⟨hsym, ZInQ.Contrib.CloudB3RC53.Hsw.strictSymm_trunc D Ustr f Q Cd hsym⟩

end AbstractSymmetry

section GenuineSymmetry

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]
  (X : GenuineSwitch K S k M) (β : M →ₗ[k] M →ₗ[k] T)
  (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)

/-- The integration strict-symmetry target needs U_str² = 0, not the stronger U_str¹ = 0. -/
theorem genuine_strictSymm_of_degreeTwoZero
    (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (c : k)
    (h2 : ∀ v, DegreeTwoZero (X.US v)) :
    ZInQ.Manuscript.RC.SelmerComplex.StrictSymm X β hβ I c := by
  intro v s t
  rw [h2 v s]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, sub_zero]
  have hz : I.h v 2 1 2 rfl (0 : (X.US v).X 2) ((X.φ v).f 1 1 rfl t) = 0 :=
    LinearMap.map_zero₂ _ _
  rw [hz]
  exact Submodule.zero_mem _

/-- The general cup-one strict-symmetry target for the same genuine truncated Galois data. -/
theorem genuine_strictSymmTrunc_of_degreeTwoZero
    (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (c : k)
    (hc : ∀ a b : M, β a b = c • β b a) (h2 : ∀ v, DegreeTwoZero (X.US v)) :
    ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymmTrunc X.toQuasi.D (piCx X.US) (piMap X.φ)
      (galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I)
      (ZInQ.Contrib.CloudB3RC53.Hsw.localPairCupOneGen (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
        β hβ (continuous_pairing β) c hc) :=
  (strictSymmTrunc_of_degreeTwoZero X.toQuasi.D (piCx X.US) (piMap X.φ) _ _
    ((degreeTwoZero_pi_iff X.US).2 h2)).1

/-- The resulting genuine reverse isotropy datum, without an additional strict-symmetry premise. -/
def genuine_reverseIsotropy_of_degreeTwoZero
    (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (c : k)
    (hc : ∀ a b : M, β a b = c • β b a) (h2 : ∀ v, DegreeTwoZero (X.US v)) :
    ZInQ.Contrib.CloudB3RC53.Hsw.ReverseIsotropy X.toQuasi.D (piCx X.US) (piMap X.φ)
      (galoisPairDataT K S k β hβ X.ΔS X.ΔR I) :=
  reverseIsotropyOfCupOne X β hβ I c hc (genuine_strictSymm_of_degreeTwoZero X β hβ I c h2)

end GenuineSymmetry

section Audit

set_option pp.fullNames true
set_option pp.proofs true

end Audit

end ZInQ.Contrib.RC53Assist.StrictLocal
