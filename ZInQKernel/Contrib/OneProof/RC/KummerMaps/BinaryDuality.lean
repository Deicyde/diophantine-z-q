import ZInQKernel.Contrib.OneProof.RC.KummerMaps.BinaryAnn
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CycloInfl

/-!
# Lane RC29 (round 3): binary duality at the Kummer places `v ∣ 2N`

Manuscript `diophantine_zq.tex` (11/5):

* Lemma `ex:arith-local-kummer`, tex 3418–3421: "Its Kummer image is its exact local annihilator,
  and the comparison has integral isotropy homotopies. At `v ∣ 2N`, triviality of the moving
  character and the common old quadratic type identify the scalar and binary versions by derived
  coefficient extension."
* tex 3433–3439: "In the universal binary family every `h_x` has the same local squareclasses at
  `2N` as `h_0 = 1`. Hence every sign character evaluates the universal character `ε` trivially on
  `G_{K_v}`, and therefore `ε|_{G_{K_v}} = 1` in `G`, before reduction modulo two. The `A_i[G]`
  Kummer condition and its null-homotopy are consequently derived scalar extensions of the fixed
  local data."
* tex 3442–3453: "The local finite dualities [Milne I.2.3, I.3.2–I.3.5] make the Kummer map
  adjoint to `H¹(F, B[2^a]) → H¹(F, B)[2^a]`. The latter has Kummer image as kernel, so the Kummer
  image is its exact annihilator. … Reduction modulo two, including the torsion in degree zero,
  gives the perfect quotient-to-dual comparison; derived Nakayama lifts it."
* Lemma `ex:arith-conjugate-duality`, tex 2761–2768: the coefficient ring `R_i = A_i` or `A_i[G]`;
  tex 3465–3467: finite Frobenius rings.

Round 2 of this lane derived, for the scalar ring `A_i`, the per-place isotropy (`OrthIsotropicAt`)
and the per-place quasi-isomorphism of `orthLocalMap` for the pair of actual Kummer conditions on
`M_i(α)` and `M_i(α⁻¹)` from Milne's print and Nekovář's 5.2.4 (`KummerPerPlace.lean`,
`KummerMilne.lean`). This file proves the same for the binary ring `A_i[G]` at the places where
the binary character `α_i = χ_0εΨ_i` is `χ_{h_0}` on the decomposition group (`v ∣ 2N`: the moving
character is trivial there by the ELLIOT input of round 1, and `ε` by the local squareclass
argument proved in round 2's `Binary.lean`).

**(i) Generic coefficient ring.** For a commutative `ℤ/2^i`-algebra `R` with a finite
`ℤ/2^i`-basis, a topology making it discrete, and a character `α` equal to `χ_h` on the
decomposition group at `v`, with the Kummer conditions `genKummerAtS` for `α` and `α⁻¹` and the
inflated Weil pairing over `R` (lane RC28's `weilPairingM`):
* statements (definitions): `binDTr`, `binDTrKills` (local traces killing coboundaries),
  `binDAnnAt` (lane RC26's `OrthKummerAnnihilator` for the pair), `binDIsoAt` (`OrthIsotropicAt`
  for the pair), `binDTrunc` (its isotropy homotopies), `binDPerfAt` (the per-place local duality
  map `orthLocalMap` is a quasi-isomorphism), `binDPerfAll` (for every isotropy homotopy);
* `binD_annihilator` (PROVED): `binDAnnAt`, from `KummerExactAnn ψ₀` (round 2) and a local trace
  inducing `H² ≅ R`, through the coefficient extension of `BinaryAnn.lean` and the bridge
  `orthKummerAnnihilator_of_cup`;
* `binD_isotropic` (PROVED): `binDIsoAt`;
* `binD_perf` (PROVED from the PRINT `NekovarProp524`): `binDPerfAt` for every isotropy homotopy,
  given `IsLocalRing R` and `NekovarFiniteSetting K S 2 R`; the cyclotomic twist hypothesis is
  PROVED (`cycloInfl_isCyclotomicTwist_tate1A`, generic in the coefficient ring);
* `binD_isotropic_of_milne`, `binD_perf_of_milne`: with `KummerExactAnn ψ₀` from Milne's print
  (round 2's `kummerExactAnn_kannPsi`, the same pairing `ψ₀` for every coefficient ring);
* `binDZeroJ`: the zero isotropy homotopy (non-vacuity of `binDTrunc`).

**The binary pair** (generic in the scalar ring `A`): `binDDualAt` (the Kummer condition over
`A[G]` for `α_bin⁻¹`), `binDIsoAt_binary_iff` (`binDIsoAt` for `α_bin` is the isotropy of the
pair (`binaryKummerAtS`, `binDDualAt`)).

**(ii) The ring `A_i[G]`** (`MonoidAlgebra (Acoef i) G`, `G` a finite elementary abelian
`2`-group):
* `binDAug` (the augmentation), `binD_of_sub_one_isNilpotent` (`([g] − 1)² = −2([g] − 1)`, so
  `[g] − 1` is nilpotent when `g² = 1` and `2` is nilpotent), `binD_sub_aug_mem_nilradical`,
  **`binD_isLocalRing`** (PROVED: `A[G]` is local when `A` has a residue map to `𝔽₂` with nilpotent
  kernel — every element is a unit or `1` minus a unit), `binD_isLocalRing_acoef`;
* **`binD_selfInjective`** (PROVED: a nondegenerate Frobenius form `λ` on `A` gives the
  nondegenerate form `x ↦ λ(x_1)` on `A[G]`,
  `ZInQ.Contrib.CloudB3RC53.SelmerDuality.selfInjective_of_frobeniusForm`
  (`CloudB3RC53/SelmerDuality/SelfInjective.lean`)),
  `binD_selfInjective_acoef` (with the top-coefficient form of `A_i`), `binD_finite_acoef`;
* **`binD_nekovarFiniteSetting`** (PROVED): Nekovář's finite standing hypotheses for `A_i[G]`;
* `binDBasis`, `binDBasis_apply`: the `ℤ/2^i`-basis `t^k [g]` of `A_i[G]`
  (`Module.Basis.smulTower` of the power basis of `A_i` and the group basis);
* `binD_isCyclotomicTwist`: `A_i[G](1)` inflated to `G_{K,S}` is a cyclotomic twist (PROVED).

**(iii) The binary per-place duality at `v ∣ 2N`:** **`binaryPerPlace_annihilator_of_milne`,
`binaryPerPlace_isotropic_of_milne`, `binaryPerPlace_perf_of_milne`** (PROVED from the PRINTs
`MilneLocalTateDualityKummerCharZero` and `NekovarProp524`, the GLUE `FullTorsion` of lane RC28,
the ELLIOT input `hα` as in round 1, and `hε`, PROVED in round 2 from the common local
squareclasses).

**Non-vacuity:** `binD_isLocalRing_trivial` (`G` trivial), `binD_isLocalRing_unit`,
`binD_nekovarFiniteSetting_sign` (`G = ℤˣ`), `binD_hyps_nonvacuous` (the hypotheses `hα`, `hε`
for the universal family of `h = 1`, `G = {±1}`, at every place), `binDTrKills_zero`, `binDZeroJ`.

**What the global binary duality still needs** (not in this file): `ε^τ = ε` (tex 2794) for the
conjugate transport `τ^*M_i ≅ M_i^*(1)` over `A_i[G]` (round 2's `ε` is built on `G_{K,S}`, with no
complex conjugation in the model); binary local conditions at the other places of `S` (the family
primes `q ∈ Q`, where `ε` is ramified — the universal augmentation at `Q`, tex 3488, and the local
lift of tex 4283–4310; the moving prime; the derivative primes) and their isotropy and
per-place perfectness over `A_i[G]`; the global traces over `A_i[G]` (Nekovář 5.4.1; here the
local traces `trv` and `InducesIsoH2` are hypotheses, as in round 2). The cyclotomic twist over
`A_i[G]` and Nekovář's finite standing hypotheses for `A_i[G]` are PROVED here.

DEPARTURE (form): `G` is a finite commutative group with `g² = 1` (the text's finite elementary
abelian `2`-group, tex 1834, 2748–2749); the ring is any commutative ring `A` in the ring-theoretic
statements (`A_i` in the text).

Kinds: definitions and PROVED (from the named PRINTs, the GLUE `FullTorsion` and the ELLIOT
input `hα` with tex lines in each statement).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero LocalTruncIsotropy)
open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open scoped TensorProduct

/-- PROVED. `E(K_S)[2^i]` is finite (lane RC28's `finite_torsS`), as an instance. -/
instance binD_finiteTorsS {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) : Finite (TorsS K S W ((2 ^ i : ℕ) : ℤ)) :=
  finite_torsS (by exact_mod_cast (pow_ne_zero i two_ne_zero : (2 : ℕ) ^ i ≠ 0))

/-! ### (i) The per-place duality over a coefficient ring with a finite basis -/

section PerPlace

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (v : Places K S) (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (R : Type) [CommRing R] [Algebra (ZMod (2 ^ i)) R] [TopologicalSpace R] [DiscreteTopology R]
  [Finite R] {ιb : Type} [Fintype ιb] (b : Module.Basis ιb (ZMod (2 ^ i)) R)
  (α : GKS K S₀ →* Rˣ) [IsOpenKer α]

/-- Definition (Nekovář 5.4.1; tex 3465–3466). **The local traces at `v`**: `R`-linear maps from the
degree-two continuous cochains of `G_{K_v}` with values in `R(1)` to `R`. -/
abbrev binDTr : Type :=
  (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
    (InflMod hS (Tate1 R hμ₀)) v).X 2 →ₗ[R] R

/-- Definition (Nekovář 5.4.1; tex 3465–3466). **A local trace kills the coboundaries.** -/
abbrev binDTrKills (trv : binDTr hS i v hμ₀ R) : Prop :=
  ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
    (InflMod hS (Tate1 R hμ₀)) v).d 1 2 rfl z) = 0

omit [TopologicalSpace R] [DiscreteTopology R] [Finite R] in
/-- PROVED (non-vacuity of `binDTrKills`). The zero map kills the coboundaries. -/
theorem binDTrKills_zero : binDTrKills hS i v hμ₀ R 0 := fun _ => LinearMap.zero_apply _

open scoped Classical in
/-- Definition (tex 3418–3421). **The annihilator statement for the Kummer pair over `R` at `v`**:
lane RC26's `OrthKummerAnnihilator` for the Kummer conditions of `α` and of `α⁻¹`
(`genKummerAtS`), the inflated Weil pairing over `R` (lane RC28's `weilPairingM`) and a local
trace `trv`. -/
def binDAnnAt (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (trv : binDTr hS i v hμ₀ R) : Prop :=
  OrthKummerAnnihilator (orthInflPair hS R (weilPairingM (S := S₀) W hμ₀ R α))
    (orthInflPair_smul hS R _ (weilPairingM_smul (S := S₀) W hμ₀ R α))
    (genKummerAtS hS R W (2 ^ i) s hs hs0 α hFull v hα)
    (genKummerAtS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα))
    trv

open scoped Classical in
/-- Definition (tex 3418–3421, 3437–3439). **The per-place isotropy statement for the Kummer pair
over `R` at `v`**: lane RC26's `OrthIsotropicAt` (`τ≥2` form) for the Kummer conditions of `α`
and of `α⁻¹` and the inflated Weil pairing over `R`. -/
def binDIsoAt (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1) : Prop :=
  OrthIsotropicAt (orthInflPair hS R (weilPairingM (S := S₀) W hμ₀ R α))
    (orthInflPair_smul hS R _ (weilPairingM_smul (S := S₀) W hμ₀ R α))
    (genKummerAtS hS R W (2 ^ i) s hs hs0 α hFull v hα)
    (genKummerAtS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα))

open scoped Classical in
/-- Definition (Nekovář 6.2.2; tex 3418–3419, 3437–3439). **The isotropy homotopies of the Kummer
pair over `R` at `v`** (`ZInQ.Contrib.CloudB3RC53.Duality.LocalTruncIsotropy`
(`CloudB3RC53/Duality/KummerTruncIsotropy.lean`) for the Galois-equivariant inflated Weil
pairing). -/
def binDTrunc (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1) : Type :=
  LocalTruncIsotropy (genKummerAtS hS R W (2 ^ i) s hs hs0 α hFull v hα).i
    (genKummerAtS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα)).i
    (orthUrPair hS R (weilPairingM (S := S₀) W hμ₀ R α) (weilPairingM_smul (S := S₀) W hμ₀ R α) v)

open scoped Classical in
/-- Definition (Nekovář 6.2.3–6.2.4; tex 3448–3453). **The per-place perfectness statement for the
Kummer pair over `R` at `v`**: the per-place local duality map (lane RC26's `orthLocalMap`) for
the isotropy homotopy `J` and the trace `trv` is a quasi-isomorphism. -/
def binDPerfAt (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (trv : binDTr hS i v hμ₀ R) (htrv : binDTrKills hS i v hμ₀ R trv)
    (J : binDTrunc hS W i s hs hs0 hFull v hμ₀ R α hα) : Prop :=
  QuasiIso (GHom.toCC (orthLocalMap (genKummerAtS hS R W (2 ^ i) s hs hs0 α hFull v hα).i
    (genKummerAtS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα)).i
    (orthUrPair hS R (weilPairingM (S := S₀) W hμ₀ R α) (weilPairingM_smul (S := S₀) W hμ₀ R α) v)
    J trv htrv))

open scoped Classical in
/-- Definition (Nekovář 6.2.3–6.2.4; tex 3448–3453). **The per-place perfectness for every isotropy
homotopy**: `binDPerfAt` for all `J`. -/
def binDPerfAll (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (trv : binDTr hS i v hμ₀ R) (htrv : binDTrKills hS i v hμ₀ R trv) : Prop :=
  ∀ J : binDTrunc hS W i s hs hs0 hFull v hμ₀ R α hα,
    binDPerfAt hS W i s hs hs0 hFull v hμ₀ R α hα trv htrv J

open scoped Classical in
include b in
/-- PROVED (tex 3418–3421, 3437–3444). **The annihilator condition for the Kummer pair over `R` at
`v`**, from the exact annihilator for `ψ₀` (Milne's local duality for `B[2^i]`, in the trace-free
form; the pairing `ψ₀` of round 2, the same for every coefficient ring) and a local trace killing
coboundaries and inducing `H²(G_{K_v}, R(1)) ≅ R`: the input `OrthKummerAnnihilator` of the
per-place duality of `OrthLocalDuality.lean`. -/
theorem binD_annihilator
    (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (hA : haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      KummerExactAnn (kannPsi hS W i s hs hs0 hFull v hμ₀))
    (trv : binDTr hS i v hμ₀ R) (htrv : binDTrKills hS i v hμ₀ R trv)
    (h2 : InducesIsoH2 trv) :
    binDAnnAt hS W i s hs hs0 hFull v hμ₀ R α hα trv := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  have hannF := kummerExactAnn_neg _ _ (kannPsi_flip hS W i s hs hs0 hFull v hμ₀) hA
  exact orthKummerAnnihilator_of_cup _ _ v (localTwist W h v.1) (localTwist W h v.1) (2 ^ i)
    (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v)
    (genIotaS_smul hS R W (2 ^ i) s hs hs0 α hFull v hα)
    (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v)
    (genIotaS_smul hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα))
    trv htrv h2
    (fun u hu u' hu' => binA_iso hS W i s hs hs0 hFull v R b hμ₀ α hα
      (fun P Q => hA.iso P Q) hu hu')
    (fun y hy hall => binA_ann hS W i s hs hs0 hFull v R b hμ₀ α hα
      (fun y' hy' hcup => (hannF y' hy').2 hcup) y hy
      (fun Q => hall _ (Submodule.mem_sup_left (kummerCocycleIn_mem _ (1 : R) Q))))

open scoped Classical in
include b in
/-- PROVED (tex 3418–3421, 3437–3439). **The per-place isotropy for the Kummer pair over `R`**
(`binDIsoAt`: `OrthIsotropicAt`, lane RC26's `τ≥2` form), from the exact annihilator for `ψ₀` and
a local trace inducing `H² ≅ R`. -/
theorem binD_isotropic
    (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (hA : haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      KummerExactAnn (kannPsi hS W i s hs hs0 hFull v hμ₀))
    (trv : binDTr hS i v hμ₀ R) (htrv : binDTrKills hS i v hμ₀ R trv)
    (h2 : InducesIsoH2 trv) :
    binDIsoAt hS W i s hs hs0 hFull v hμ₀ R α hα := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact orthLD_isotropicAt _ _ _ _ trv
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v)
      (genIotaS_smul hS R W (2 ^ i) s hs hs0 α hFull v hα))
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v)
      (genIotaS_smul hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα)))
    (binD_annihilator hS W i s hs hs0 hFull v hμ₀ R b α hα hA trv htrv h2) h2

open scoped Classical in
include b in
/-- PROVED from the PRINT `NekovarProp524` (Nekovář, *Selmer complexes*, 5.2.4) and the GLUE
`FullTorsion` (tex 3418–3421, 3437–3453). **The per-place quasi-isomorphism for the Kummer pair over
`R`** (`binDPerfAt`): under Nekovář's finite standing hypotheses for `R` (`IsLocalRing R`, `hset`),
the per-place local duality map of the pair is a quasi-isomorphism for every isotropy homotopy `J`.
The cyclotomic twist hypothesis of the print is PROVED (`cycloInfl_isCyclotomicTwist_tate1A`). -/
theorem binD_perf [IsLocalRing R] (h524 : NekovarProp524 K) (hset : NekovarFiniteSetting K S 2 R)
    (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (hA : haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      KummerExactAnn (kannPsi hS W i s hs hs0 hFull v hμ₀))
    (trv : binDTr hS i v hμ₀ R) (htrv : binDTrKills hS i v hμ₀ R trv)
    (h2 : InducesIsoH2 trv) (J : binDTrunc hS W i s hs hs0 hFull v hμ₀ R α hα) :
    binDPerfAt hS W i s hs hs0 hFull v hμ₀ R α hα trv htrv J := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  have := hset.selfInjective
  have : Finite (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)))) :=
    inferInstanceAs (Finite (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))
  have : Finite (InflMod hS (CoefMod R (charInv α) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)))) :=
    inferInstanceAs (Finite (CoefMod R (charInv α) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))
  exact orthPerPlace_of_localDuality _ _ (genKummerAtS hS R W (2 ^ i) s hs hs0 α hFull v hα)
    (genKummerAtS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα))
    J trv htrv
    (h524 S 2 R hset (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))
      (InflMod hS (CoefMod R (charInv α) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))
      (InflMod hS (Tate1 R hμ₀)) (orthInflPair hS R (weilPairingM (S := S₀) W hμ₀ R α))
      (orthInflPair_smul hS R _ (weilPairingM_smul (S := S₀) W hμ₀ R α))
      (weilPairingM_bijective (S := S₀) W hμ₀ R α hFull)
      (weilPairingM_flip_bijective (S := S₀) W hμ₀ R α hFull)
      (cycloInfl_isCyclotomicTwist_tate1A hS R hμ₀) v trv htrv h2)
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v)
      (genIotaS_smul hS R W (2 ^ i) s hs hs0 α hFull v hα))
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v)
      (genIotaS_smul hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα)))
    (orth_kummerAt_h01 v (localTwist W h v.1) (2 ^ i)
      (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v)
      (genIotaS_smul hS R W (2 ^ i) s hs hs0 α hFull v hα))
    (orth_kummerAt_h01 v (localTwist W h v.1) (2 ^ i)
      (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v)
      (genIotaS_smul hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα)))
    (binD_annihilator hS W i s hs hs0 hFull v hμ₀ R b α hα hA trv htrv h2)

open scoped Classical in
include b in
/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` (tex 3418–3421, 3437–3448).
**The per-place isotropy over `R`**, with the exact annihilator for `ψ₀` from Milne's print
(round 2's `kummerExactAnn_kannPsi`). -/
theorem binD_isotropic_of_milne (hM : MilneLocalTateDualityKummerCharZero)
    (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (trv : binDTr hS i v hμ₀ R) (htrv : binDTrKills hS i v hμ₀ R trv)
    (h2 : InducesIsoH2 trv) :
    binDIsoAt hS W i s hs hs0 hFull v hμ₀ R α hα :=
  binD_isotropic hS W i s hs hs0 hFull v hμ₀ R b α hα
    (kummerExactAnn_kannPsi hS W i s hs hs0 hFull v hμ₀ hM) trv htrv h2

open scoped Classical in
include b in
/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero` and `NekovarProp524` and the GLUE
`FullTorsion` (tex 3418–3421, 3437–3453). **The per-place quasi-isomorphism over `R`**, for every
isotropy homotopy (`binDPerfAll`). -/
theorem binD_perf_of_milne [IsLocalRing R] (hM : MilneLocalTateDualityKummerCharZero)
    (h524 : NekovarProp524 K) (hset : NekovarFiniteSetting K S 2 R)
    (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (trv : binDTr hS i v hμ₀ R) (htrv : binDTrKills hS i v hμ₀ R trv)
    (h2 : InducesIsoH2 trv) :
    binDPerfAll hS W i s hs hs0 hFull v hμ₀ R α hα trv htrv := fun J =>
  binD_perf hS W i s hs hs0 hFull v hμ₀ R b α h524 hset hα
    (kummerExactAnn_kannPsi hS W i s hs hs0 hFull v hμ₀ hM) trv htrv h2 J

open scoped Classical in
/-- Definition (non-vacuity of `binDTrunc`; Nekovář 6.2.1.5). **The zero isotropy homotopy of the
Kummer pair over `R`** (lane RC26's `orthZeroIsotropy`): both conditions are concentrated in degrees
`0, 1`, and they are isotropic. -/
def binDZeroJ (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (hiso : binDIsoAt hS W i s hs hs0 hFull v hμ₀ R α hα) :
    binDTrunc hS W i s hs hs0 hFull v hμ₀ R α hα :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  orthZeroIsotropy
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v)
      (genIotaS_smul hS R W (2 ^ i) s hs hs0 α hFull v hα))
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v)
      (genIotaS_smul hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα)))
    hiso

end PerPlace

/-! ### The binary pair: `binaryKummerAtS` and the condition for `α_bin⁻¹` -/

section BinaryPair

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (v : Places K S) (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (A : Type) [CommRing A] (G : Type) [CommGroup G] (α : GKS K S₀ →* Aˣ) (ε : GKS K S₀ →* G)
  [IsOpenKer (binaryAlpha A G α ε)]

/-- Definition (tex 2790–2796, 3433–3439). **The dual binary Kummer condition at `v`**: the Kummer
condition over `A[G]` for the inverse `α_bin⁻¹` of the binary character `α_bin = α·[ε]`
(`genKummerAtS`), at a place where `α = χ_h` and `ε = 1` on the decomposition group. -/
def binDDualAt (hα : IsLocallyQuadAtGen (S := S₀) A α (quadChar s hs hs0) v.1)
    (hε : ∀ σ : Gloc K v.1, ε (locMap K S₀ v.1 σ) = 1) :
    CondAt K S (MonoidAlgebra A G) (InflMod hS (CoefMod (MonoidAlgebra A G)
      (charInv (binaryAlpha A G α ε)) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)))) v :=
  genKummerAtS hS (MonoidAlgebra A G) W (2 ^ i) s hs hs0 (charInv (binaryAlpha A G α ε)) hFull v
    (isLocallyQuadAtGen_charInv
      (isLocallyQuadAtGen_binaryAlpha (S := S₀) A G α ε _ v.1 hα hε))

variable [Algebra (ZMod (2 ^ i)) A] [TopologicalSpace (MonoidAlgebra A G)]
  [DiscreteTopology (MonoidAlgebra A G)] [Finite (MonoidAlgebra A G)]

/-- PROVED (unfolding). **`binDIsoAt` for the binary character is the isotropy of the pair
(`binaryKummerAtS` for `α_bin`, `binDDualAt` for `α_bin⁻¹`)** for the inflated Weil pairing over
`A[G]`. -/
theorem binDIsoAt_binary_iff (hα : IsLocallyQuadAtGen (S := S₀) A α (quadChar s hs hs0) v.1)
    (hε : ∀ σ : Gloc K v.1, ε (locMap K S₀ v.1 σ) = 1) :
    binDIsoAt hS W i s hs hs0 hFull v hμ₀ (MonoidAlgebra A G) (binaryAlpha A G α ε)
        (isLocallyQuadAtGen_binaryAlpha (S := S₀) A G α ε _ v.1 hα hε) ↔
      OrthIsotropicAt (orthInflPair hS (MonoidAlgebra A G)
          (weilPairingM (S := S₀) W hμ₀ (MonoidAlgebra A G) (binaryAlpha A G α ε)))
        (orthInflPair_smul hS (MonoidAlgebra A G) _
          (weilPairingM_smul (S := S₀) W hμ₀ (MonoidAlgebra A G) (binaryAlpha A G α ε)))
        (binaryKummerAtS hS A G W (2 ^ i) s hs hs0 α ε hFull v hα hε)
        (binDDualAt hS W i s hs hs0 hFull v A G α ε hα hε) :=
  Iff.rfl

end BinaryPair

/-! ### (ii) The ring `A[G]`: local, self-injective, Nekovář's finite setting -/

section Ring

variable {A G : Type} [CommRing A] [CommGroup G]

/-- Definition (tex 4634–4637: "after augmentation `𝔽₂[G] → 𝔽₂`"). **The augmentation**
`A[G] → A`, `∑ a_g [g] ↦ ∑ a_g`, as an `A`-algebra map. -/
def binDAug : MonoidAlgebra A G →ₐ[A] A :=
  MonoidAlgebra.lift A A G 1

/-- PROVED. The augmentation of `a[g]` is `a`. -/
theorem binDAug_single (g : G) (a : A) : binDAug (MonoidAlgebra.single g a) = a := by
  rw [binDAug, MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

/-- PROVED. **`[g] − 1` is nilpotent** in `A[G]` when `g² = 1` and `2` is nilpotent in `A`:
`([g] − 1)² = −2([g] − 1)`, so `([g] − 1)^{n+1} = (−2)^n ([g] − 1)`. -/
theorem binD_of_sub_one_isNilpotent (h2 : IsNilpotent (2 : A)) (g : G) (hg : g * g = 1) :
    IsNilpotent (MonoidAlgebra.of A G g - 1) := by
  obtain ⟨n, hn⟩ := h2
  have hgg : MonoidAlgebra.of A G g * MonoidAlgebra.of A G g = 1 := by
    rw [← map_mul, hg, map_one]
  have hsq : (MonoidAlgebra.of A G g - 1) * (MonoidAlgebra.of A G g - 1) =
      (-2 : MonoidAlgebra A G) * (MonoidAlgebra.of A G g - 1) := by
    linear_combination hgg
  have hpow : ∀ k : ℕ, (MonoidAlgebra.of A G g - 1) ^ (k + 1) =
      (-2 : MonoidAlgebra A G) ^ k * (MonoidAlgebra.of A G g - 1) := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_one, pow_zero, one_mul]
    | succ k ih => rw [pow_succ, ih, mul_assoc, hsq, ← mul_assoc, ← pow_succ]
  have h2n : (2 : MonoidAlgebra A G) ^ n = 0 := by
    rw [← map_ofNat (algebraMap A (MonoidAlgebra A G)) 2, ← map_pow, hn, map_zero]
  refine ⟨n + 1, ?_⟩
  rw [hpow, neg_pow, h2n, mul_zero, zero_mul]

/-- PROVED. **`x − aug(x)` lies in the nilradical** of `A[G]` (`g² = 1`, `2` nilpotent). -/
theorem binD_sub_aug_mem_nilradical (h2 : IsNilpotent (2 : A)) (hG : ∀ g : G, g * g = 1)
    (x : MonoidAlgebra A G) :
    x - algebraMap A (MonoidAlgebra A G) (binDAug x) ∈ nilradical (MonoidAlgebra A G) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, sub_zero]; exact zero_mem _
  | add x y hx hy =>
    have e : x + y - algebraMap A (MonoidAlgebra A G) (binDAug (x + y)) =
        (x - algebraMap A (MonoidAlgebra A G) (binDAug x)) +
          (y - algebraMap A (MonoidAlgebra A G) (binDAug y)) := by
      rw [map_add, map_add]
      abel
    rw [e]
    exact add_mem hx hy
  | single g a =>
    rw [binDAug_single]
    have e : MonoidAlgebra.single g a - algebraMap A (MonoidAlgebra A G) a =
        algebraMap A (MonoidAlgebra A G) a * (MonoidAlgebra.of A G g - 1) := by
      rw [mul_sub, mul_one, ← Algebra.smul_def, MonoidAlgebra.of_apply,
        MonoidAlgebra.smul_single', mul_one]
    rw [e]
    exact Ideal.mul_mem_left _ _ (mem_nilradical.2 (binD_of_sub_one_isNilpotent h2 g (hG g)))

/-- PROVED (tex 3455–3456, 3465–3467: Nekovář's finite theory for the finite coefficient rings; tex
4635–4637, 7500–7502: the group rings over `𝔽₂((t))` and `𝒪` are local, the augmentation ideal in
the maximal ideal). **`A[G]` is a
local ring** when `A` has a ring map `ρ : A → 𝔽₂` with nilpotent kernel, `2` is nilpotent in `A`
and `g² = 1` on `G`: the kernel of `ρ ∘ aug : A[G] → 𝔽₂` consists of nilpotents, so every element
is a unit or `1` minus a unit. -/
theorem binD_isLocalRing (ρ : A →+* ZMod 2) (hρ : ∀ a, ρ a = 0 → IsNilpotent a)
    (h2 : IsNilpotent (2 : A)) (hG : ∀ g : G, g * g = 1) : IsLocalRing (MonoidAlgebra A G) := by
  let res : MonoidAlgebra A G →+* ZMod 2 :=
    ρ.comp (binDAug : MonoidAlgebra A G →ₐ[A] A).toRingHom
  have hker : ∀ x, res x = 0 → IsNilpotent x := by
    intro x hx
    have h1 := binD_sub_aug_mem_nilradical h2 hG x
    have h3 : algebraMap A (MonoidAlgebra A G) (binDAug x) ∈ nilradical (MonoidAlgebra A G) :=
      mem_nilradical.2 ((hρ (binDAug x) hx).map _)
    have e : x = (x - algebraMap A (MonoidAlgebra A G) (binDAug x)) +
        algebraMap A (MonoidAlgebra A G) (binDAug x) := by abel
    rw [e]
    exact mem_nilradical.1 (add_mem h1 h3)
  have : Nontrivial (MonoidAlgebra A G) := res.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases zmod_two_eq_zero_or_one (res a) with ha | ha
  · exact Or.inr (hker a ha).isUnit_one_sub
  · refine Or.inl ?_
    have h1 : res (1 - a) = 0 := by rw [map_sub, map_one, ha, sub_self]
    have h3 := (hker _ h1).isUnit_one_sub
    rwa [sub_sub_cancel] at h3

/-- PROVED (tex 3465–3467: a top-coefficient functional tests a finite Frobenius ring's
perfection). **A nondegenerate Frobenius form on `A` gives self-injectivity of
`A[G]`** (`G` finite): `x ↦ λ(x_1)` is nondegenerate on `A[G]` (`(x · y[g⁻¹])_1 = x_g y`), and a
finite commutative ring with a nondegenerate Frobenius form is self-injective
(`ZInQ.Contrib.CloudB3RC53.SelmerDuality.selfInjective_of_frobeniusForm`
(`CloudB3RC53/SelmerDuality/SelfInjective.lean`)). -/
theorem binD_selfInjective [Finite A] [Finite G] (lam : A →+ AddCircle (1 : ℚ))
    (hlam : ∀ a, (∀ c, lam (a * c) = 0) → a = 0) :
    Module.Injective (MonoidAlgebra A G) (MonoidAlgebra A G) := by
  have : Module.Finite A (MonoidAlgebra A G) := Module.Finite.of_basis (MonoidAlgebra.basis G A)
  have : Finite (MonoidAlgebra A G) := Module.finite_of_finite A
  refine selfInjective_of_frobeniusForm (lam.comp (binaryCoeffAt A G 1)) fun x hx => ?_
  apply MonoidAlgebra.ext
  ext g
  show x.coeff g = 0
  refine hlam (x.coeff g) fun c => ?_
  have e : lam ((x * MonoidAlgebra.single g⁻¹ c).coeff 1) = 0 := hx (MonoidAlgebra.single g⁻¹ c)
  rwa [MonoidAlgebra.coeff_mul_single_apply, one_mul, inv_inv] at e

end Ring

section RingAcoef

/-- PROVED. **`A_i[G]` is a local ring** for `i ≠ 0` and `g² = 1` on `G` (lane RC28's residue map
`A_i → 𝔽₂`, whose kernel `(2, t)` is nilpotent). -/
theorem binD_isLocalRing_acoef (i : ℕ) (hi : i ≠ 0) {G : Type} [CommGroup G]
    (hG : ∀ g : G, g * g = 1) : IsLocalRing (MonoidAlgebra (Acoef i) G) :=
  binD_isLocalRing (acoefResidue i hi) (fun _ ha => isNilpotent_of_acoefResidue_eq_zero hi ha)
    (acoef_isNilpotent_two i) hG

/-- PROVED. **`A_i[G]` is self-injective** (`i ≠ 0`, `G` finite), with the Frobenius form
`x ↦ (coefficient of t^{i−1} in x_1)` read in `ℚ/ℤ`. -/
theorem binD_selfInjective_acoef (i : ℕ) (hi : i ≠ 0) (G : Type) [CommGroup G] [Finite G] :
    Module.Injective (MonoidAlgebra (Acoef i) G) (MonoidAlgebra (Acoef i) G) := by
  have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow hi⟩
  let pb : PowerBasis (ZMod (2 ^ i)) (Acoef i) :=
    AdjoinRoot.powerBasis' (Polynomial.monic_X_pow i)
  have hdim : pb.dim = i := by
    change (Polynomial.X ^ i : Polynomial (ZMod (2 ^ i))).natDegree = i
    exact Polynomial.natDegree_X_pow i
  have hd : 0 < pb.dim := by rw [hdim]; exact Nat.pos_of_ne_zero hi
  have hnil : pb.gen ^ pb.dim = 0 := by
    rw [hdim]
    change (AdjoinRoot.root (Polynomial.X ^ i : Polynomial (ZMod (2 ^ i)))) ^ i = 0
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  exact binD_selfInjective ((ZMod.toRatAddCircle (2 ^ i)).comp (topCoord pb hd).toAddMonoidHom)
    (fun a ha => topCoord_nondegenerate pb hd hnil a ha)

/-- PROVED. `A_i[G]` is finite (`G` finite), as an instance. -/
instance binD_finite_acoef (i : ℕ) (G : Type) [CommGroup G] [Finite G] :
    Finite (MonoidAlgebra (Acoef i) G) := by
  have : Module.Finite (Acoef i) (MonoidAlgebra (Acoef i) G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G (Acoef i))
  exact Module.finite_of_finite (Acoef i)

/-- PROVED (Nekovář 5.1, p. 113; 5.2.3 and 6.2.5 (A) with `J = I[0] = R`; tex 3455–3456,
3465–3467).
**Nekovář's finite standing hypotheses for the binary ring `A_i[G]`**: for a totally complex number
field `K` (condition (P) at `p = 2`), a finite set `S` containing the primes above `2`, `i ≠ 0` and
a finite elementary abelian `2`-group `G`, the ring `A_i[G]` is a finite local ring with nilpotent
`2`, injective over itself. -/
theorem binD_nekovarFiniteSetting (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) (i : ℕ) (hi : i ≠ 0)
    (G : Type) [CommGroup G] [Finite G] (hG : ∀ g : G, g * g = 1) :
    haveI := binD_isLocalRing_acoef i hi hG
    NekovarFiniteSetting K S 2 (MonoidAlgebra (Acoef i) G) := by
  have := binD_isLocalRing_acoef i hi hG
  exact
    { prime := Nat.prime_two
      finite_S := hS
      above_p := fun v hv => h2 v (by exact_mod_cast hv)
      condP := fun _ => hK
      finite_R := binD_finite_acoef i G
      nilpotent_p := by
        have h := (acoef_isNilpotent_two i).map (algebraMap (Acoef i) (MonoidAlgebra (Acoef i) G))
        rw [map_ofNat] at h
        exact_mod_cast h
      selfInjective := binD_selfInjective_acoef i hi G }

/-- Definition (tex 2725–2728, 2766–2767: "it fixes `t` and the group-ring basis"). **The
`ℤ/2^i`-basis `t^k [g]` of `A_i[G]`**: the tower basis
(`Module.Basis.smulTower`) of the power basis `1, t, …, t^{i−1}` of `A_i` over `ℤ/2^i` and the
group basis of `A_i[G]` over `A_i`. -/
def binDBasis (i : ℕ) (G : Type) [CommGroup G] :
    Module.Basis (Fin (kannPB i).dim × G) (ZMod (2 ^ i)) (MonoidAlgebra (Acoef i) G) :=
  (kannPB i).basis.smulTower (MonoidAlgebra.basis G (Acoef i))

/-- PROVED. The basis vectors are `t^k [g]`. -/
theorem binDBasis_apply (i : ℕ) (G : Type) [CommGroup G] (k : Fin (kannPB i).dim) (g : G) :
    binDBasis i G (k, g) = (kannPB i).basis k • MonoidAlgebra.single g (1 : Acoef i) := by
  rw [binDBasis, Module.Basis.smulTower_apply, MonoidAlgebra.basis_apply]

/-- PROVED (tex 2798–2801: `R_i(1)` with `R_i = A_i[G]`). **The inflation of `A_i[G](1)` to
`G_{K,S}` is a cyclotomic twist** (round 2's `cycloInfl_isCyclotomicTwist_tate1A`, generic in the
coefficient ring) — the cyclotomic twist hypothesis of the Selmer-duality prints over `A_i[G]`. -/
theorem binD_isCyclotomicTwist {K : Type} [Field K] [NumberField K]
    {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (i : ℕ) (G : Type) [CommGroup G]
    (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i)) :
    IsCyclotomicTwist K S (MonoidAlgebra (Acoef i) G)
      (InflMod hS (Tate1 (MonoidAlgebra (Acoef i) G) hμ₀)) :=
  cycloInfl_isCyclotomicTwist_tate1A hS (MonoidAlgebra (Acoef i) G) hμ₀

end RingAcoef

/-! ### (iii) The binary per-place duality at `v ∣ 2N` -/

section Binary

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (v : Places K S) (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (G : Type) [CommGroup G] [Fintype G] (α : GKS K S₀ →* (Acoef i)ˣ) (ε : GKS K S₀ →* G)
  [IsOpenKer (binaryAlpha (Acoef i) G α ε)]
  [TopologicalSpace (MonoidAlgebra (Acoef i) G)] [DiscreteTopology (MonoidAlgebra (Acoef i) G)]

/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` (tex 3418–3421, 3433–3448).
**The annihilator condition for the binary Kummer pair at `v ∣ 2N`** (`α_bin = α·[ε]` on
`A_i[G]`, for the text's `α_i = χ_0εΨ_i`): at a place where `α = χ_{h_0}` (ELLIOT `hα`: the moving
character is trivial at `2N`, tex 2729, 3431; round 2's `isLocallyQuadAtGen_binaryAlpha_alphaChar`)
and `ε = 1` (`hε`: the common local squareclasses, tex 3433–3437, PROVED from them in round 2's
`binaryUnivChar_locMap`, `binary_locMap_eq_one_of_signChars`) on the decomposition group, for any
local trace inducing `H²(G_{K_v}, A_i[G](1)) ≅ A_i[G]`. -/
theorem binaryPerPlace_annihilator_of_milne (hM : MilneLocalTateDualityKummerCharZero)
    (hα : IsLocallyQuadAtGen (S := S₀) (Acoef i) α (quadChar s hs hs0) v.1)
    (hε : ∀ σ : Gloc K v.1, ε (locMap K S₀ v.1 σ) = 1)
    (trv : binDTr hS i v hμ₀ (MonoidAlgebra (Acoef i) G))
    (htrv : binDTrKills hS i v hμ₀ (MonoidAlgebra (Acoef i) G) trv)
    (h2 : InducesIsoH2 trv) :
    binDAnnAt hS W i s hs hs0 hFull v hμ₀ (MonoidAlgebra (Acoef i) G) (binaryAlpha (Acoef i) G α ε)
      (isLocallyQuadAtGen_binaryAlpha (S := S₀) (Acoef i) G α ε _ v.1 hα hε) trv := by
  have h := binD_annihilator hS W i s hs hs0 hFull v hμ₀ (MonoidAlgebra (Acoef i) G)
    (binDBasis i G) (binaryAlpha (Acoef i) G α ε)
    (isLocallyQuadAtGen_binaryAlpha (S := S₀) (Acoef i) G α ε _ v.1 hα hε)
    (kummerExactAnn_kannPsi hS W i s hs hs0 hFull v hμ₀ hM) trv htrv h2
  exact h

/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` (tex 3418–3421, 3433–3448).
**The binary per-place isotropy at `v ∣ 2N`** (tex 3437–3439: "the `A_i[G]` Kummer condition and its
null-homotopy are … derived scalar extensions of the fixed local data"): the binary Kummer pair
(`binaryKummerAtS` for `α_bin`, `binDDualAt` for `α_bin⁻¹`; `binDIsoAt_binary_iff`) is isotropic
for the inflated Weil pairing over `A_i[G]` (`OrthIsotropicAt`, lane RC26's `τ≥2` form), for any
local trace inducing `H²(G_{K_v}, A_i[G](1)) ≅ A_i[G]`. -/
theorem binaryPerPlace_isotropic_of_milne (hM : MilneLocalTateDualityKummerCharZero)
    (hα : IsLocallyQuadAtGen (S := S₀) (Acoef i) α (quadChar s hs hs0) v.1)
    (hε : ∀ σ : Gloc K v.1, ε (locMap K S₀ v.1 σ) = 1)
    (trv : binDTr hS i v hμ₀ (MonoidAlgebra (Acoef i) G))
    (htrv : binDTrKills hS i v hμ₀ (MonoidAlgebra (Acoef i) G) trv)
    (h2 : InducesIsoH2 trv) :
    binDIsoAt hS W i s hs hs0 hFull v hμ₀ (MonoidAlgebra (Acoef i) G) (binaryAlpha (Acoef i) G α ε)
      (isLocallyQuadAtGen_binaryAlpha (S := S₀) (Acoef i) G α ε _ v.1 hα hε) := by
  have h := binD_isotropic_of_milne hS W i s hs hs0 hFull v hμ₀ (MonoidAlgebra (Acoef i) G)
    (binDBasis i G) (binaryAlpha (Acoef i) G α ε) hM
    (isLocallyQuadAtGen_binaryAlpha (S := S₀) (Acoef i) G α ε _ v.1 hα hε) trv htrv h2
  exact h

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero` and `NekovarProp524`, the GLUE
`FullTorsion` (lane RC28) and the ELLIOT input `hα` (tex 2729, 3431) (tex 3418–3421, 3433–3453).
**The binary per-place quasi-isomorphism at `v ∣ 2N`** (`binDPerfAll`): the per-place local
duality map of the binary Kummer pair over `A_i[G]` is a quasi-isomorphism, for every isotropy
homotopy `J` (for example `binDZeroJ`). Nekovář's finite standing hypotheses for `A_i[G]` are PROVED
(`binD_nekovarFiniteSetting`), from the standing setting (`K` totally complex, `S` finite
containing the primes above `2`; tex 3455–3456), `i ≠ 0` and `g² = 1`. -/
theorem binaryPerPlace_perf_of_milne (hM : MilneLocalTateDualityKummerCharZero)
    (h524 : NekovarProp524 K) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) (hi : i ≠ 0)
    (hG : ∀ g : G, g * g = 1)
    (hα : IsLocallyQuadAtGen (S := S₀) (Acoef i) α (quadChar s hs hs0) v.1)
    (hε : ∀ σ : Gloc K v.1, ε (locMap K S₀ v.1 σ) = 1)
    (trv : binDTr hS i v hμ₀ (MonoidAlgebra (Acoef i) G))
    (htrv : binDTrKills hS i v hμ₀ (MonoidAlgebra (Acoef i) G) trv)
    (h2 : InducesIsoH2 trv) :
    binDPerfAll hS W i s hs hs0 hFull v hμ₀ (MonoidAlgebra (Acoef i) G)
      (binaryAlpha (Acoef i) G α ε)
      (isLocallyQuadAtGen_binaryAlpha (S := S₀) (Acoef i) G α ε _ v.1 hα hε) trv htrv := by
  have := binD_isLocalRing_acoef i hi hG
  have h := binD_perf_of_milne hS W i s hs hs0 hFull v hμ₀ (MonoidAlgebra (Acoef i) G)
    (binDBasis i G) (binaryAlpha (Acoef i) G α ε) hM h524
    (binD_nekovarFiniteSetting K hK S hSfin (fun v hv => hS (h2₀ v hv)) i hi G hG)
    (isLocallyQuadAtGen_binaryAlpha (S := S₀) (Acoef i) G α ε _ v.1 hα hε) trv htrv h2
  exact h

end Binary

/-! ### Non-vacuity -/

section NonVacuity

/-- PROVED (non-vacuity of `binD_isLocalRing`, `G` trivial). `A_1[1]` is a local ring. -/
theorem binD_isLocalRing_trivial : IsLocalRing (MonoidAlgebra (Acoef 1) Unit) :=
  binD_isLocalRing_acoef 1 one_ne_zero fun _ => rfl

/-- PROVED (non-vacuity of `binD_isLocalRing`, `G = ℤˣ ≅ ℤ/2`). `A_1[{±1}]` is a local ring. -/
theorem binD_isLocalRing_unit : IsLocalRing (MonoidAlgebra (Acoef 1) ℤˣ) :=
  binD_isLocalRing_acoef 1 one_ne_zero Int.units_mul_self

/-- PROVED (non-vacuity of `binD_nekovarFiniteSetting`). For every totally complex number field
`K`, the primes above `2` and the binary ring `A_1[{±1}]` satisfy Nekovář's finite standing
hypotheses. -/
theorem binD_nekovarFiniteSetting_sign (K : Type) [Field K] [NumberField K]
    (hK : IsTotallyComplex K) :
    haveI := binD_isLocalRing_unit
    NekovarFiniteSetting K {v : HeightOneSpectrum (𝓞 K) | (2 : 𝓞 K) ∈ v.asIdeal} 2
      (MonoidAlgebra (Acoef 1) ℤˣ) :=
  binD_nekovarFiniteSetting K hK _ (ZInQ.Contrib.CloudB3RC53.RankCounts.primesAboveTwo_finite K)
    (fun _ hv => hv) 1 one_ne_zero ℤˣ Int.units_mul_self

/-- PROVED (non-vacuity of the hypotheses `hα`, `hε`, `hG` and of the instance arguments of the
binary per-place theorems, `G = {±1}`). Over `ℚ`, for every `S` and every place `v`, with `h_0 = 1`
(square root `1`), `α = χ_1` read in `A_1^×` and `ε` the universal character of the one-element
family `d = 1`: `α = χ_1` on the decomposition group, `ε = 1` there (`1` is a square in every
`ℚ_v`, round 2's `binaryUnivChar_locMap`), `g² = 1` on `G`, the binary character has open kernel,
and `A_1[G]` carries a discrete topology. -/
theorem binD_hyps_nonvacuous (S : Set (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsLocallyQuadAtGen (Acoef 1)
        ((intUnitsTo (Acoef 1)).comp (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero))
        (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero) v ∧
      (∀ σ : Gloc ℚ v, binaryUnivChar (fun _ : Unit => (1 : KS ℚ S)) (d := fun _ => 1)
        (fun _ => one_sq_KS S) (fun _ => one_ne_zero) (locMap ℚ S v σ) = 1) ∧
      (∀ g : Unit → ℤˣ, g * g = 1) ∧
      IsOpenKer (binaryAlpha (Acoef 1) (Unit → ℤˣ)
        ((intUnitsTo (Acoef 1)).comp (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero))
        (binaryUnivChar (fun _ : Unit => (1 : KS ℚ S)) (d := fun _ => 1)
          (fun _ => one_sq_KS S) (fun _ => one_ne_zero))) ∧
      @DiscreteTopology (MonoidAlgebra (Acoef 1) (Unit → ℤˣ)) ⊥ :=
  ⟨isLocallyQuadAtGen_intUnitsTo (Acoef 1) _ v,
    binaryUnivChar_locMap _ _ _ v fun _ => by rw [map_one]; exact IsSquare.one,
    fun g => funext fun _ => Int.units_mul_self _, inferInstance, discreteTopology_bot _⟩

/-- PROVED (non-vacuity of the conclusion's hypothesis `hα` of the generic theorems for the
binary character). Over `ℚ`, for every `S` and every place, the binary character `α·[ε]` of
`h_0 = 1` (`G = {±1}`) is `χ_1` on the decomposition group. -/
theorem binD_isLocallyQuadAtGen_nonvacuous (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsLocallyQuadAtGen (MonoidAlgebra (Acoef 1) (Unit → ℤˣ))
      (binaryAlpha (Acoef 1) (Unit → ℤˣ)
        ((intUnitsTo (Acoef 1)).comp (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero))
        (binaryUnivChar (fun _ : Unit => (1 : KS ℚ S)) (d := fun _ => 1)
          (fun _ => one_sq_KS S) (fun _ => one_ne_zero)))
      (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero) v :=
  isLocallyQuadAtGen_binaryAlpha (Acoef 1) (Unit → ℤˣ) _ _ _ v
    (binD_hyps_nonvacuous S v).1 (binD_hyps_nonvacuous S v).2.1

end NonVacuity

end ZInQ.Manuscript.RC.KummerMaps
