import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompArith
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegEmpty

/-!
# The two fields of the finite-level Selmer description `KcArithSelmerLevel`

Manuscript `diophantine_zq.tex`, tex 4005–4014 (the Kummer coefficient comparison of the
calibration).

`KcArithSelmerLevel k S E` (the named input of the concrete Kummer coefficient comparison) has two
fields, each with the premises `E` elliptic, `k < 0`, `S` finite containing the primes above `2`,
and `E[2^∞] ⊂ E(K_S)`: (i) locally trivial cocycles of `G_{K,S}` inflate into `Sel_{2^m}(E/K)`, and
(ii) every class of `Sel_{2^m}(E/K)` is such an inflation. Here:

* `KcSelOfLoc`, `KcLocOfSel` (definitions) and `kcArithSelmerLevel_iff` (PROVED): the split;
* `decomp_subsingleton`, `locK_real_eq_zero` (PROVED): for `k < 0` the decomposition group at a
  real embedding of `ℚˢ` is trivial, so the real places impose nothing;
* `KcSelOfLocFinite` (definition; the named finite-place input of (i), PRINT + GLUE: Milne,
  *Arithmetic Duality Theorems*, I, Proposition 6.5 (p. 75, proof p. 76, using I.3.8) at the places
  outside `S`; the comparison of the two local models at the places of `S`), and
  `kcSelOfLoc_of_finite` (PROVED): (i) from it;
* `kcArithSelmerLevel_of` (PROVED): `KcArithSelmerLevel` from `KcSelOfLocFinite` and (ii).

Kinds: definitions and PROVED; the named inputs `KcSelOfLocFinite` (PRINT + GLUE) and `KcLocOfSel`
(PRINT + GLUE: Milne, *Arithmetic Duality Theorems*, I, Proposition 6.5 and Corollary 6.6,
pp. 75–76; the Néron–Ogg–Shafarevich criterion, Silverman AEC VII.7.1, page unverified; the
finite-level reading and the local models).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.KcSplit

open NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC53Assist.QuadraticDescent ZInQ.Manuscript.SelmerTwoPower

/-- `ℂ` is an algebraic closure of `ℝ` (PROVED). -/
theorem isAlgClosure_real_complex : IsAlgClosure ℝ ℂ :=
  ⟨Complex.isAlgClosed, Algebra.IsAlgebraic.of_finite ℝ ℂ⟩

attribute [local instance] isAlgClosure_real_complex

/-- **At a real embedding of `ℚˢ`, the decomposition group of an imaginary quadratic field is
trivial** (PROVED): an automorphism of `ℝˢ ≅ ℂ` over `ℝ` fixing a square root of `k < 0` is the
identity. -/
theorem decomp_subsingleton {k : ℤ} (hk : k < 0) (τ : SepEmb ℚ ℝ) :
    Subsingleton (decomp (sqrtK k) τ) := by
  have hR : IsAlgClosure ℝ (SeparableClosure ℝ) := inferInstance
  let e : SeparableClosure ℝ ≃ₐ[ℝ] ℂ := IsAlgClosure.equiv ℝ (SeparableClosure ℝ) ℂ
  suffices h : ∀ g : decomp (sqrtK k) τ, g = 1 from
    ⟨fun a b => by rw [h a, h b]⟩
  rintro ⟨g, hg⟩
  apply Subtype.ext
  change g = 1
  have hfix : g (τ (sqrtK k)) = τ (sqrtK k) := by
    rw [← absoluteGaloisGroupMap_commutes]
    exact congrArg τ (mem_galK.mp hg)
  set z := e (τ (sqrtK k))
  have hz2 : z ^ 2 = (k : ℂ) := by
    simp only [z, ← map_pow, sqrtK_sq]
    rw [show (sepMap ℚ (k : ℚ)) = algebraMap ℚ (SeparableClosure ℚ) (k : ℚ) from rfl,
      AlgHom.commutes]
    exact (eq_ratCast ((e : SeparableClosure ℝ →+* ℂ).comp (algebraMap ℚ _)) (k : ℚ)).trans
      (by push_cast; rfl)
  let f : ℂ →ₐ[ℝ] ℂ := (e.symm.trans (g.trans e)).toAlgHom
  have hf : f z = z := by
    show e (g (e.symm (e (τ (sqrtK k))))) = e (τ (sqrtK k))
    rw [e.symm_apply_apply, hfix]
  rcases Complex.real_algHom_eq_id_or_conj f with h | h
  · ext x
    have := congrArg (fun φ : ℂ →ₐ[ℝ] ℂ => e.symm (φ (e x))) h
    simpa [f] using this
  · exfalso
    have hc : (starRingEnd ℂ) z = z := by
      have := hf; rw [h] at this; simpa using this
    have him : z.im = 0 := Complex.conj_eq_iff_im.mp hc
    have hre : (z ^ 2).re = z.re ^ 2 := by simp [sq, him]
    have : (z ^ 2).re = (k : ℝ) := by rw [hz2]; simp
    have hk' : (k : ℝ) < 0 := by exact_mod_cast hk
    nlinarith [sq_nonneg z.re]

open ZInQ.Manuscript.RC CategoryTheory CategoryTheory.Limits
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.DiskOrders.Limit ZInQ.Contrib.CloudB3RC53

attribute [local instance] levTop continuousSMul_lev
open ZInQ.Manuscript.RC.SelmerComplex

/-- **At a real embedding, localization of an imaginary quadratic field's classes vanishes**
(PROVED). -/
theorem locK_real_eq_zero {k : ℤ} (hk : k < 0) (E : WeierstrassCurve ℚ)
    (τ : SepEmb ℚ (RealCompletion ())) (z : H1 (galK (sqrtK k)) E.PointCoeff) :
    locK (sqrtK k) τ E z = 0 := by
  have := decomp_subsingleton hk τ
  have : Subsingleton (H1 (decomp (sqrtK k) τ) (E.baseChange (RealCompletion ())).PointCoeff) :=
    ZInQ.Manuscript.RC.GlueSweep.Heeg.subsingleton_H1_of_subsingleton
  exact Subsingleton.elim _ _

section Split

variable (k : ℤ) (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (E : WeierstrassCurve ℚ)

/-- **Field (i) of `KcArithSelmerLevel`**: locally trivial cocycles of `G_{K,S}` inflate into
`Sel_{2^m}(E/K)`. Kind: definition (the statement). -/
def KcSelOfLoc : Prop :=
  E.IsElliptic → k < 0 → S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S) →
    (∀ n : ℕ, FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ n)) →
    ∀ (m : ℕ) (f : (contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).X 1)
      (hf : ((contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).d 1 2).hom f = 0),
      KcLocTriv (E.baseChange (QuadraticField k)) f →
        kerToH1 (k := ℤ) ⟨((kcInfl k S E m).f 1).hom f, kcInfl_mem_ker k S E hf⟩ ∈
          selmerLevelK (sqrtK k) E m

/-- **Field (ii) of `KcArithSelmerLevel`**: every class of `Sel_{2^m}(E/K)` is such an inflation.
Literature (PRINT): Milne, *Arithmetic Duality Theorems*, 2nd ed., Ch. I, Proposition 6.5, p. 75,
verbatim: "There are exact sequences 0 → H¹(G_S, A(m)) → H¹(K, A(m)) → ⊕_{v∉S} H¹(K_v, A) …", with
its proof on p. 76 ("Conversely, let a lie in this kernel. … it suffices to show that b (hence a) is
split by a finite extension of K unramified outside S") and Corollary 6.6, p. 76 ("S_S(K, A, m) =
S(K, A, m)"); the standing hypotheses of §6 (pp. 72–73): `S` contains the archimedean primes and the
primes of bad reduction, and `m` is a unit in `R_{K,S}`. GLUE: the level-`2^m` reading of the proof
(which works with `A_m`, using Lemma 6.1, p. 73), good reduction outside `S` from `E[2^∞] ⊂ E(K_S)`
(Néron–Ogg–Shafarevich, Silverman AEC VII.7.1, page unverified), and the local models (`KcLocTriv`
at the places of `S`).
Kind: definition (the statement; the named input). -/
def KcLocOfSel : Prop :=
  E.IsElliptic → k < 0 → S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S) →
    (∀ n : ℕ, FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ n)) →
    ∀ (m : ℕ) (c : H1 (galK (sqrtK k)) (E.TorsionCoeff (2 ^ m))),
      c ∈ selmerLevelK (sqrtK k) E m →
      ∃ (f : (contCochains ℤ (GKS (QuadraticField k) S)
          (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).X 1)
        (hf : ((contCochains ℤ (GKS (QuadraticField k) S)
          (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).d 1 2).hom f = 0),
        KcLocTriv (E.baseChange (QuadraticField k)) f ∧
          kerToH1 (k := ℤ) ⟨((kcInfl k S E m).f 1).hom f, kcInfl_mem_ker k S E hf⟩ = c

/-- `KcArithSelmerLevel` is its two fields (PROVED). -/
theorem kcArithSelmerLevel_iff :
    KcArithSelmerLevel k S E ↔ KcSelOfLoc k S E ∧ KcLocOfSel k S E :=
  ⟨fun h => ⟨h.sel_of_loc, h.loc_of_sel⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **The finite-place local input of field (i)** (named; PRINT + GLUE): for every prime `p` and
embedding `τ : ℚˢ → ℚ_pˢ` (a place `v` of `K` above `p`), the localization at `τ` of the image in
`H¹(G_K, E)` of the inflation of a cocycle of `G_{K,S}` that is locally trivial at `S` vanishes.
* At `v ∉ S`: the cocycle is inflated from `G_{K,S}`, hence unramified at `v`, with values in
  `E[2^m] ⊂ E(K_v^un)`, and `E` has good reduction at `v`; its class dies by Milne, *Arithmetic
  Duality Theorems*, 2nd ed., Ch. I, Proposition 3.8 (pp. 46–47), verbatim: "Let A be an abelian
  variety over K, and let 𝒜 be its Néron model over R. Then H^1(G/I, A(K^un)) = H^1(G/I,
  π_0(𝒜_0)) where 𝒜_0 is the closed fibre of 𝒜/R. In particular, if A has good reduction, then
  H^1(G/I, A(K^un)) = 0." (PRINT; its proof uses Lang's lemma and Hensel's lemma.) The global
  form is Milne, I, Proposition 6.5 (p. 75), whose proof (p. 76) reads: "According to (3.8),
  H¹(g_v, A(K_v^un)) = 0, and so the diagram shows that the image of H¹(G_S, A(m)) in H¹(K, A(m))
  is contained in the kernel of H¹(K, A(m)) → ⊕_{v∉S} H¹(K_v, A)." GLUE: the good reduction
  outside `S` (from `E[2^∞] ⊂ E(K_S)` and the Néron–Ogg–Shafarevich criterion, Silverman AEC
  VII.7.1, page unverified).
* At `v ∈ S`: GLUE, the comparison of `KcLocTriv` (stated with `G_{K_v}` and the points over the
  completion `K_v`) with the localization `locK` at `τ` (stated with embeddings of separable
  closures); the tree has no map from `τ` to the place `v`, which a split of this input by place
  needs.
Kind: definition (the statement; the named input). -/
def KcSelOfLocFinite : Prop :=
  E.IsElliptic → k < 0 → S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S) →
    (∀ n : ℕ, FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ n)) →
    ∀ (m : ℕ) (f : (contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).X 1)
      (hf : ((contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).d 1 2).hom f = 0),
      KcLocTriv (E.baseChange (QuadraticField k)) f →
        ∀ (p : Nat.Primes) (τ : SepEmb ℚ (QpCompletion p)),
          locK (sqrtK k) τ E (levelIncl (sqrtK k) E m
            (kerToH1 (k := ℤ) ⟨((kcInfl k S E m).f 1).hom f, kcInfl_mem_ker k S E hf⟩)) = 0

/-- **Field (i) from the finite-place input** (PROVED): the real places are discharged
(`locK_real_eq_zero`). -/
theorem kcSelOfLoc_of_finite (h : KcSelOfLocFinite k S E) : KcSelOfLoc k S E := by
  intro hE hk hS h2 hF m f hf hloc
  change levelIncl (sqrtK k) E m _ ∈ shaK (sqrtK k) E
  rw [mem_shaK]
  exact ⟨fun p τ => h hE hk hS h2 hF m f hf hloc p τ, fun τ => locK_real_eq_zero hk E τ _⟩

/-- **`KcArithSelmerLevel` from the finite-place input and field (ii)** (PROVED). -/
theorem kcArithSelmerLevel_of (h1 : KcSelOfLocFinite k S E) (h2 : KcLocOfSel k S E) :
    KcArithSelmerLevel k S E :=
  (kcArithSelmerLevel_iff k S E).2 ⟨kcSelOfLoc_of_finite k S E h1, h2⟩

end Split

end ZInQ.Contrib.CloudB3E2.KcSplit
