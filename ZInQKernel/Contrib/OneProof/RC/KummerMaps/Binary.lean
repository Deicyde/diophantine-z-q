import ZInQKernel.Contrib.OneProof.RC.KummerMaps.IotaGen

/-!
# Lane RC29 (Kummer maps), round 2: the binary coefficient ring `A_i[G]` at the Kummer places

Manuscript `diophantine_zq.tex` (11/5):

* tex 2728–2730: "For a fixed binary group `G`, use `A_i[G]` and the universal quadratic
  character. The character `Ψ_i` is finite, trivial at `2N`, …"
* tex 2748–2751 (Definition `ex:arith-data`): "A binary family uses one finite elementary abelian
  two-group `G`, one real sign and common local squareclasses at `2N`. Its universal varying
  quadratic character is therefore trivial at the real place and at `2N`."
* tex 2790–2796: "Let `R_i = A_i` in the scalar construction and `R_i = A_i[G]` in the binary
  construction. Write `α_i = χ_hΨ_i`, respectively `α_i = χ_0εΨ_i`, where `ε : G_K → G` is the
  restriction of the universal rational quadratic character. Then `ε^τ = ε = ε⁻¹` …"
* tex 1864–1871: "the binary family is required to have one real sign and fixed local
  squareclasses at `2N`. Writing its characters as `χ_x = χ_0(x∘ε)`, this means `ε(c) = 1` for
  complex conjugation `c`, and `ε|_{G_{ℚ_v}} = 1` at every `v ∣ 2N`. Indeed every character of `G`
  evaluates these elements to one, and the characters separate `G`."
* Lemma `ex:arith-local-kummer`, tex 3419–3421 and 3429–3440: "At `v ∣ 2N`, triviality of the
  moving character and the common old quadratic type identify the scalar and binary versions by
  derived coefficient extension. … In the universal binary family every `h_x` has the same local
  squareclasses at `2N` as `h_0 = 1`. Hence every sign character evaluates the universal character
  `ε` trivially on `G_{K_v}`, and therefore `ε|_{G_{K_v}} = 1` in `G`, before reduction modulo two.
  The `A_i[G]` Kummer condition and its null-homotopy are consequently derived scalar extensions
  of the fixed local data."

## Contents

**The binary ring and the binary character.** `R_i = A_i[G]` is Mathlib's `MonoidAlgebra A G`
(`A = A_i = Acoef i` in the text; any commutative ring here), for a commutative group `G` (the
text's finite elementary abelian `2`-group; only the sign-character argument uses `g² = 1`).
`binaryGroupUnit : G → A[G]^×`, `g ↦ [g]`; `binaryScalarUnit : A^× → A[G]^×`, `a ↦ a[1]`;
`binaryAlpha α ε = α·[ε]`, the character of the binary module; `binaryAlpha_alphaChar`: for
`α = alphaChar i χ_0 ξ` it is **`α_i = χ_0 · [ε] · Ψ_i`** (tex 2792); `isOpenKer_binaryAlpha`;
`binaryGroupUnit_mul_self`: `[g]⁻¹ = [g]` for `g² = 1` (tex 2794, "`ε = ε⁻¹`", through RC10's
`groupRing_basis_sq`).

**The universal character and its local triviality (tex 1864–1871, 3433–3437).**
* `quadChar_locMap_eq_one_of_isSquare`: if `d ∈ K` is a square in `K_v`, the quadratic character
  `χ_d` of RC28 is trivial on the decomposition group `p_v(G_{K_v})` — PROVED in our model, through
  round 1's `twistSign_localSqrt` (the embedding `j = embS`): `j(√d) = ±b ∈ K_v` is fixed by
  `G_{K_v}`.
* `binaryUnivChar s`: **the universal character** of a finite family of square roots
  `s_j ∈ K_S` of `d_j ∈ K`, `σ ↦ (χ_{d_j}(σ))_j ∈ G = {±1}^ι` (elementary abelian:
  `binaryUnivChar_mul_self`; open kernel for finite `ι`: `isOpen_ker_binaryUnivChar`);
  `binaryUnivChar_locMap`: **`ε ∘ p_v = 1` when every `d_j` is a square in `K_v`**. Every
  character of the text's family is `x ∘ ε = ∏_j χ_{d_j}^{x_j}`; the text's `G` (the dual of the
  parameter space `𝔽_2^b`, family `h_x = ∏_q (q^*)^{λ_q(x)}`, tex 2680–2686) receives `ε` through a
  homomorphism `π : {±1}^Q → G` (`binary_comp_locMap_eq_one`, `binary_isOpen_ker_comp`).
* The text's own argument, for an abstract `ε : G_{K,S} → G`: `binary_eq_one_of_signChar`
  (**the sign characters `G → {±1}` separate the points of an elementary abelian `2`-group**:
  PROVED via `G` as an `𝔽_2`-vector space and `Module.Projective.exists_dual_ne_zero`), and
  `binary_locMap_eq_one_of_signChars`: if every sign character `x` has `x ∘ ε = χ_{d_x}` with
  `d_x` a square in `K_v` (the text's `x ∘ ε = χ_0χ_x`, `d_x = h_0h_x`, "the same local
  squareclasses at `2N` as `h_0`"), then **`ε|_{G_{K_v}} = 1` in `G`** (before any reduction).
  The other group's `LocalSquareclassNode` (CloudB3RC53, Duality/LocalSquareclass.lean) proves
  the analogue in its own model (separable closures, `absoluteGaloisGroupMap`); it is not used.

**The binary Kummer condition at `v ∣ 2N`.**
* `isLocallyQuadAtGen_binaryAlpha`: if `α = χ` and `ε = 1` on `G_{K_v}`, then `α·[ε] = χ` there;
  `isLocallyQuadAtGen_binaryAlpha_alphaChar`: for the text's `α_i = χ_0εΨ_i`, from the ELLIOT
  input `ξ ∘ p_v = 1` (`Ψ_i` trivial at `2N`, as in round 1's `isLocallyQuadAt_alphaChar`) and
  `ε ∘ p_v = 1` (PROVED above from the local squareclass hypothesis).
* `binaryKummerAt`: **the `A[G]` Kummer condition** at `v` — `genKummerAt` over `A[G]` with the
  coefficient map `ι_v^{bin} : B(K̄_v)[N] → (A[G] ⊗ E(K_S)[N])(α·[ε])` of `IotaGen.lean`, for the
  twist `B = E^{(h_0)}` (`s² = h_0`; the text's universal family has `h_0 = 1`, `χ_0 = 1`);
  `binaryKummerAt_isInjective`, `binaryKummerAt_isIso_H0`, `binaryKummerAt_mono_H1`,
  `binaryKummerAt_range_eq_span` (its `H¹` image is the `A[G]`-span of the image of its local
  Kummer map), `binaryKummerAt_i` (its inclusion is RC28's `kummerConditionInι`, by `rfl`);
  `binaryKummerAtS`, `binaryKummerAtS_isInjective`: the same for the binary module built over
  `G_{K,S₀}` and inflated to `S ⊇ S₀`.

**Derived scalar extension (tex 3419–3421, 3436–3439).**
* `binaryCoefExt : (A ⊗ T)(α) → (A[G] ⊗ T)(α·[ε])`, `a ⊗ t ↦ a[1] ⊗ t` (`binaryCoefExt_tmul`,
  `binaryCoefExt_oneTmul`); `A`-semilinear over `A → A[G]` (`binaryCoefExt_smul_scalar`);
  **equivariant on every `g` with `ε(g) = 1`** (`binaryCoefExt_smul_of_eq_one`), in particular on
  `G_{K_v}` at `v ∣ 2N` (`binaryCoefExtRes_smul`); its image spans (`span_range_binaryCoefExt`).
* `genIota_binary_eq`: **`ι_v^{bin} = (a ↦ a[1]) ∘ ι_v^{sc}`** — the binary Kummer coefficient map
  is the coefficient extension of the scalar one (`A`, character `α = χ_0Ψ_i`, twist `h_0`).
* Generic statements for a coefficient map `c : M₁ → M₂` along a ring map `ρ : k₁ → k₂`
  (`binaryCochainPush`, `c ∘ −` on continuous cochains; `binaryCochainPush_contD`: it commutes with
  the differential; `binary_kummerCocycleIn_comp`, `binary_kummerZ'_comp`, `binary_push_mem_contB1`,
  `binary_contB1_push`, `binary_condOne_push`, `binary_range_H1_push`, `binary_kummerMapIn_push`).
* For the binary condition: **`binaryKummer_condOne_eq_span`: its degree-one term
  `span_{A[G]}(ι^{bin}∘κ_P) + B¹` is the `A[G]`-span of the image of the scalar degree-one term
  `span_A(ι^{sc}∘κ_P) + B¹` under `c ∘ −`**; **`binaryKummerAt_range_H1_eq_span`: its `H¹` image is
  the `A[G]`-span of the classes `[c ∘ z]`, `z` in the scalar degree-one term**;
  `binaryKummerMap_eq_push`: the binary local Kummer class of `P` is the class of `c ∘ (ι^{sc}∘κ_P)`,
  the coefficient extension of the scalar Kummer cocycle (whose class is the scalar local Kummer
  class, `binaryScalarKummerMap_eq`); **`binaryKummerAt_range_eq_span_push`: the `H¹` image of the
  binary condition is the `A[G]`-span of these coefficient-extended scalar Kummer classes**.
* Components (`A[G]` is free over `A` on `G`): `binaryCoefProj g : r ⊗ t ↦ r_g ⊗ t`,
  `binaryCoefProj_smul_coefExt` (`π_g(r • c(x)) = r_g • x`), `binaryCoefProj_smul_of_eq_one`
  (equivariant where `ε = 1`), `binaryCoefExt_sum_proj` (`x = ∑_g [g] • c(π_g x)`, `G` finite);
  generic `binaryCochainPush_span_proj`, `binaryCochainPush_sum_proj`,
  `binaryCochainPush_span_of_proj`; **`binaryKummer_condOne_iff_components`: a binary `1`-cochain
  lies in the degree-one term of the `A[G]` condition iff each of its `G`-components lies in the
  degree-one term of the scalar `A` condition** — the degree-one term is `⊕_{g ∈ G} [g]·c_*(U¹_{sc})`,
  i.e. that of `U_{sc} ⊗_A A[G]` (in degree zero both conditions are all cochains).

**Non-vacuity.** `binaryKummerAt_nonvacuous_trivial` (`G = 1`), `binaryKummerAt_nonvacuous_sign`
(`G = {±1}`, `ε` the universal character of `h = 1`), `binary_locMap_eq_one_of_signChars_nonvacuous`
(`G = {±1}`, `ε = 1`).

**DEPARTURES (form).**
1. `ε` is defined on `G_{K,S}` from square roots in `K_S` of elements of `K`, not as the restriction
   of a character of `G_ℚ`; hence `ε^τ = ε` (tex 2794) is not modeled here (only `ε = ε⁻¹`).
2. "Derived scalar extension" is formalized at the finite level: the identity `ι^{bin} = c ∘ ι^{sc}`,
   the degree-one term as an `A[G]`-span and in component form (`⊕_g [g]·c_*(U¹_{sc})`; derived =
   underived since `A[G]` is `A`-free on `G`), and the `H¹` images. An isomorphism of complexes
   `U_{bin} ≅ U_{sc} ⊗_A A[G]` as a categorical object is not built. The null-homotopy (isotropy)
   part of the sentence is not covered (round 1 keeps Kummer isotropy as the ELLIOT hypothesis
   `hiso`).
3. The local squareclass hypothesis "`h_x` has the same local squareclasses at `2N` as `h_0`" is
   `IsSquare (d_x)` in `K_v` with `d_x = h_0h_x`; the restriction to `v ∣ 2N` is not encoded (the
   statements hold at every `v` satisfying it).
4. `G` is any commutative group (the text: a finite elementary abelian `2`-group); `g² = 1` is
   assumed exactly where the text uses it (sign-character separation, `[g]⁻¹ = [g]`). The coefficient
   ring is any commutative ring `A` (the text: `A_i`).

Kinds: definitions and PROVED; ELLIOT only in `isLocallyQuadAtGen_binaryAlpha_alphaChar` (`ξ`
trivial on the decomposition group, as round 1's `isLocallyQuadAt_alphaChar`); GLUE `FullTorsion`
(lane RC28) for the coefficient map.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve TensorProduct
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
  ZInQ.Manuscript.RC.TwistDictionary ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef groupRing_basis_sq)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-! ### The binary coefficient ring `A[G]` and the binary character -/

section Ring

variable (A : Type) [CommRing A] (G : Type) [CommGroup G]

/-- Definition (tex 2728, 2792: `ε : G_K → G ⊂ A_i[G]^×`). **The group-ring units** `g ↦ [g]`. -/
def binaryGroupUnit : G →* (MonoidAlgebra A G)ˣ :=
  (MonoidAlgebra.of A G).toHomUnits

/-- PROVED. `[g]` is the basis element `single g 1`. -/
theorem binaryGroupUnit_val (g : G) :
    ((binaryGroupUnit A G g : (MonoidAlgebra A G)ˣ) : MonoidAlgebra A G) =
      MonoidAlgebra.of A G g :=
  rfl

/-- Definition (tex 3436–3439, the coefficient map `A_i → A_i[G]`). **The scalar units**
`a ↦ a[1]`, `A^× → A[G]^×`. -/
def binaryScalarUnit : Aˣ →* (MonoidAlgebra A G)ˣ :=
  Units.map (algebraMap A (MonoidAlgebra A G)).toMonoidHom

/-- PROVED. The value of `binaryScalarUnit`. -/
theorem binaryScalarUnit_val (u : Aˣ) :
    ((binaryScalarUnit A G u : (MonoidAlgebra A G)ˣ) : MonoidAlgebra A G) =
      algebraMap A (MonoidAlgebra A G) (u : A) :=
  rfl

/-- PROVED. `ℤ^× → A^× → A[G]^×` is `ℤ^× → A[G]^×`. -/
theorem binaryScalarUnit_intUnitsTo (u : ℤˣ) :
    binaryScalarUnit A G (intUnitsTo A u) = intUnitsTo (MonoidAlgebra A G) u :=
  units_map_intUnitsTo _ u

/-- PROVED (tex 2794: "`ε = ε⁻¹`"; lane RC10's `groupRing_basis_sq`). For an elementary abelian
`2`-group, `[g][g] = 1`. -/
theorem binaryGroupUnit_mul_self (hG : ∀ g : G, g * g = 1) (g : G) :
    binaryGroupUnit A G g * binaryGroupUnit A G g = 1 :=
  Units.ext (groupRing_basis_sq hG g)

variable {Γ : Type} [Group Γ]

/-- Definition (tex 2790–2796). **The character of the binary module**: `α · [ε]`, for a character
`α : Γ → A^×` (the scalar character, `α = χ_0Ψ_i`) and a homomorphism `ε : Γ → G` (the universal
character). For `α = alphaChar i χ_0 ξ` this is the text's `α_i = χ_0εΨ_i`
(`binaryAlpha_alphaChar`). -/
def binaryAlpha (α : Γ →* Aˣ) (ε : Γ →* G) : Γ →* (MonoidAlgebra A G)ˣ :=
  charMul ((binaryScalarUnit A G).comp α) ((binaryGroupUnit A G).comp ε)

/-- PROVED. The value of the binary character. -/
theorem binaryAlpha_apply (α : Γ →* Aˣ) (ε : Γ →* G) (g : Γ) :
    binaryAlpha A G α ε g = binaryScalarUnit A G (α g) * binaryGroupUnit A G (ε g) :=
  rfl

/-- PROVED. Where `ε` is trivial, the binary character is the scalar character read in `A[G]^×`. -/
theorem binaryAlpha_of_eq_one (α : Γ →* Aˣ) (ε : Γ →* G) (g : Γ) (hg : ε g = 1) :
    binaryAlpha A G α ε g = binaryScalarUnit A G (α g) := by
  rw [binaryAlpha_apply, hg, map_one, mul_one]

omit [NumberField K] in
/-- PROVED (tex 2792). **`α_i = χ_0 · [ε] · Ψ_i`**: for the scalar character `alphaChar i χ_0 ξ`
(`= χ_0Ψ_i`, lane RC28), the binary character is `χ_0 [ε] Ψ_i` in `A_i[G]^×`. -/
theorem binaryAlpha_alphaChar (i : ℕ) (χ0 : GKS K S →* ℤˣ)
    (ξ : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))) (ε : GKS K S →* G) (σ : GKS K S) :
    binaryAlpha (Acoef i) G (alphaChar i χ0 ξ) ε σ =
      intUnitsTo (MonoidAlgebra (Acoef i) G) (χ0 σ) * binaryGroupUnit (Acoef i) G (ε σ) *
        binaryScalarUnit (Acoef i) G (movingCharS i ξ σ) := by
  rw [binaryAlpha_apply, alphaChar, charMul_apply, map_mul, MonoidHom.comp_apply,
    binaryScalarUnit_intUnitsTo, mul_right_comm]

omit [NumberField K] in
/-- PROVED. **The binary character has open kernel** when `α` has and `ε` has open kernel. -/
theorem isOpenKer_binaryAlpha (α : GKS K S →* Aˣ) [IsOpenKer α] (ε : GKS K S →* G)
    (hε : IsOpen (ε.ker : Set (GKS K S))) : IsOpenKer (binaryAlpha A G α ε) := by
  have h1 : IsOpenKer ((binaryScalarUnit A G).comp α) := isOpenKer_map α (binaryScalarUnit A G)
  have h2 : IsOpenKer ((binaryGroupUnit A G).comp ε) :=
    ⟨Subgroup.isOpen_mono (H₁ := ε.ker) (fun g hg => by
      rw [MonoidHom.mem_ker] at hg ⊢
      rw [MonoidHom.comp_apply, hg, map_one]) hε⟩
  exact isOpenKer_charMul _ _

end Ring

/-! ### The universal character and its local triviality -/

section Universal

/-- PROVED (tex 3433–3437, one sign character). **If `d ∈ K` is a square in `K_v`, the quadratic
character `χ_d` is trivial on the decomposition group at `v`**: `j(√d)² = d = b²` with `b ∈ K_v`,
so `j(√d) = ±b` is fixed by `G_{K_v}`, and the local sign of `j(√d)` is `χ_d ∘ p_v` (round 1's
`twistSign_localSqrt`, through the embedding `j = embS`). -/
theorem quadChar_locMap_eq_one_of_isSquare (s : KS K S) {d : K}
    (hs : s ^ 2 = algebraMap K (KS K S) d) (hs0 : s ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (hsq : IsSquare (algebraMap K (v.adicCompletion K) d)) (σ : Gloc K v) :
    quadChar s hs hs0 (locMap K S v σ) = 1 := by
  rw [← twistSign_localSqrt s hs hs0 v σ]
  obtain ⟨b, hb⟩ := hsq
  have hq : localSqrt s v ^ 2 =
      (algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b) ^ 2 := by
    rw [localSqrt_sq s hs v, hb, map_mul, sq]
  have hb' : σ.toAlgHom (algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b) =
      algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b :=
    σ.toAlgHom.commutes b
  have hfix : σ.toAlgHom (localSqrt s v) = localSqrt s v := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hq with h1 | h1
    · rw [h1, hb']
    · rw [h1, map_neg, hb']
  unfold twistSign
  rw [ite_eq_left hfix]

variable {ι : Type} (s : ι → KS K S) {d : ι → K} (hs : ∀ j, s j ^ 2 = algebraMap K (KS K S) (d j))
  (hs0 : ∀ j, s j ≠ 0)

/-- Definition (tex 2728, 2792, 1864–1871). **The universal quadratic character** of a family of
square roots `s_j ∈ K_S` of `d_j ∈ K`: `ε(σ) = (χ_{d_j}(σ))_j ∈ {±1}^ι`. Its characters are the
products `∏_j χ_{d_j}^{x_j}` (the quadratic characters of the family `∏_j d_j^{x_j}`). -/
def binaryUnivChar : GKS K S →* (ι → ℤˣ) :=
  MonoidHom.pi fun j => quadChar (s j) (hs j) (hs0 j)

/-- PROVED. The coordinates of the universal character are the quadratic characters `χ_{d_j}`. -/
theorem binaryUnivChar_apply (σ : GKS K S) (j : ι) :
    binaryUnivChar s hs hs0 σ j = quadChar (s j) (hs j) (hs0 j) σ :=
  rfl

/-- PROVED. The target `{±1}^ι` is an elementary abelian `2`-group. -/
theorem binaryUnivChar_mul_self (g : ι → ℤˣ) : g * g = 1 :=
  funext fun j => Int.units_mul_self (g j)

/-- PROVED. For a finite family the universal character has open kernel (the intersection of the
open kernels of the `χ_{d_j}`). -/
theorem isOpen_ker_binaryUnivChar [Finite ι] :
    IsOpen ((binaryUnivChar s hs hs0).ker : Set (GKS K S)) := by
  have heq : ((binaryUnivChar s hs hs0).ker : Set (GKS K S)) =
      ⋂ j, ((quadChar (s j) (hs j) (hs0 j)).ker : Set (GKS K S)) := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter]
    constructor
    · intro h j
      exact congrFun h j
    · intro h
      exact funext h
  rw [heq]
  exact isOpen_iInter_of_finite fun j => (quadChar_isOpenKer (s j) (hs j) (hs0 j)).isOpen_ker

/-- PROVED (tex 3433–3437, 1869: "`ε|_{G_{ℚ_v}} = 1` at every `v ∣ 2N`"). **The universal
character is trivial on the decomposition group at `v` when every `d_j` is a square in `K_v`.** -/
theorem binaryUnivChar_locMap (v : HeightOneSpectrum (𝓞 K))
    (hsq : ∀ j, IsSquare (algebraMap K (v.adicCompletion K) (d j))) (σ : Gloc K v) :
    binaryUnivChar s hs hs0 (locMap K S v σ) = 1 :=
  funext fun j => quadChar_locMap_eq_one_of_isSquare (s j) (hs j) (hs0 j) v (hsq j) σ

/-- PROVED. Local triviality passes to `π ∘ ε` for any homomorphism `π` (the text's `G` receives
the universal character of its generators through the dual of the parametrization). -/
theorem binary_comp_locMap_eq_one {G₁ G₂ : Type} [Group G₁] [Group G₂] (ε : GKS K S →* G₁)
    (π : G₁ →* G₂) (v : HeightOneSpectrum (𝓞 K)) (hε : ∀ σ : Gloc K v, ε (locMap K S v σ) = 1)
    (σ : Gloc K v) : (π.comp ε) (locMap K S v σ) = 1 := by
  rw [MonoidHom.comp_apply, hε σ, map_one]

omit [NumberField K] in
/-- PROVED. Open kernel passes to `π ∘ ε`. -/
theorem binary_isOpen_ker_comp {G₁ G₂ : Type} [Group G₁] [Group G₂] (ε : GKS K S →* G₁)
    (π : G₁ →* G₂) (hε : IsOpen (ε.ker : Set (GKS K S))) :
    IsOpen ((π.comp ε).ker : Set (GKS K S)) :=
  Subgroup.isOpen_mono (H₁ := ε.ker) (fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]) hε

end Universal

/-! ### The text's argument: sign characters separate an elementary abelian `2`-group -/

section SignCharacters

/-- PROVED (tex 1870–1871: "every character of `G` evaluates these elements to one, and the
characters separate `G`"). **The sign characters `G → {±1}` separate the points of an elementary
abelian `2`-group**: if `x(g) = 1` for every homomorphism `x : G → ℤ^×`, then `g = 1`. (`G` is an
`𝔽_2`-vector space; a nonzero vector has a linear form not vanishing on it.) -/
theorem binary_eq_one_of_signChar {G : Type} [CommGroup G] (hG : ∀ g : G, g * g = 1) (g : G)
    (hg : ∀ x : G →* ℤˣ, x g = 1) : g = 1 := by
  have h2 : ∀ y : Additive G, (2 : ℕ) • y = 0 := fun y => by
    rw [two_nsmul]
    exact hG (Additive.toMul y)
  let _ : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule h2
  by_contra hne
  have hy : Additive.ofMul g ≠ 0 := fun h => hne h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hy
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  let x : G →* ℤˣ :=
    { toFun := fun a => if φ (Additive.ofMul a) = 0 then 1 else -1
      map_one' := by
        have : φ (Additive.ofMul (1 : G)) = 0 := map_zero φ
        simp only [this, ite_true]
      map_mul' := fun a b => by
        have hab : φ (Additive.ofMul (a * b)) = φ (Additive.ofMul a) + φ (Additive.ofMul b) :=
          map_add φ (Additive.ofMul a) (Additive.ofMul b)
        rw [hab]
        rcases zmod_two_eq_zero_or_one (φ (Additive.ofMul a)) with ha | ha <;>
          rcases zmod_two_eq_zero_or_one (φ (Additive.ofMul b)) with hb | hb <;>
          simp [ha, hb, h11, h10] }
  have hx : x g = -1 := by
    change (if φ (Additive.ofMul g) = 0 then (1 : ℤˣ) else -1) = -1
    rw [ite_eq_right hφ]
  have := hg x
  rw [hx] at this
  exact absurd this (by decide)

/-- PROVED from the local squareclass hypothesis (tex 3433–3437, the text's argument verbatim).
**`ε|_{G_{K_v}} = 1` in `G`**: let `ε : G_{K,S} → G` be a homomorphism to an elementary abelian
`2`-group such that every sign character `x : G → {±1}` has `x ∘ ε = χ_{d_x}` (the text's
`x ∘ ε = χ_0χ_x`, `d_x = h_0h_x`), and suppose every `d_x` is a square in `K_v` ("every `h_x` has
the same local squareclasses at `2N` as `h_0`"). Then every sign character evaluates `ε` trivially
on `G_{K_v}`, and hence `ε` is trivial there (`binary_eq_one_of_signChar`), before any reduction
modulo two. -/
theorem binary_locMap_eq_one_of_signChars {G : Type} [CommGroup G] (hG : ∀ g : G, g * g = 1)
    (ε : GKS K S →* G) (sx : (G →* ℤˣ) → KS K S) {dx : (G →* ℤˣ) → K}
    (hsx : ∀ x, sx x ^ 2 = algebraMap K (KS K S) (dx x)) (hsx0 : ∀ x, sx x ≠ 0)
    (hεx : ∀ x : G →* ℤˣ, x.comp ε = quadChar (sx x) (hsx x) (hsx0 x))
    (v : HeightOneSpectrum (𝓞 K))
    (hsq : ∀ x, IsSquare (algebraMap K (v.adicCompletion K) (dx x))) (σ : Gloc K v) :
    ε (locMap K S v σ) = 1 :=
  binary_eq_one_of_signChar hG _ fun x =>
    (DFunLike.congr_fun (hεx x) (locMap K S v σ)).trans
      (quadChar_locMap_eq_one_of_isSquare (sx x) (hsx x) (hsx0 x) v (hsq x) σ)

end SignCharacters

/-! ### The binary character at `v ∣ 2N` -/

section Local

variable (A : Type) [CommRing A] (G : Type) [CommGroup G]

/-- PROVED. **Where `ε` is trivial on the decomposition group, the binary character is the scalar
one there**: if `α = χ` and `ε = 1` on `G_{K_v}`, then `α·[ε] = χ` on `G_{K_v}` (in `A[G]^×`). -/
theorem isLocallyQuadAtGen_binaryAlpha (α : GKS K S →* Aˣ) (ε : GKS K S →* G)
    (χ : GKS K S →* ℤˣ) (v : HeightOneSpectrum (𝓞 K)) (hα : IsLocallyQuadAtGen A α χ v)
    (hε : ∀ σ : Gloc K v, ε (locMap K S v σ) = 1) :
    IsLocallyQuadAtGen (MonoidAlgebra A G) (binaryAlpha A G α ε) χ v := fun σ => by
  rw [binaryAlpha_of_eq_one A G α ε _ (hε σ), hα σ, binaryScalarUnit_intUnitsTo]

/-- PROVED from ELLIOT (tex 2729, 3431–3437). **For the text's `α_i = χ_0εΨ_i`, the character of
the binary module is `χ_0` on the decomposition group at `v ∣ 2N`**: from `ξ ∘ p_v = 1` (ELLIOT:
"`Ψ_i` is trivial at `2N`", as in round 1's `isLocallyQuadAt_alphaChar`) and `ε ∘ p_v = 1`
(`binaryUnivChar_locMap` or `binary_locMap_eq_one_of_signChars`). -/
theorem isLocallyQuadAtGen_binaryAlpha_alphaChar (i : ℕ) (χ0 : GKS K S →* ℤˣ)
    (ξ : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))) (ε : GKS K S →* G)
    (v : HeightOneSpectrum (𝓞 K)) (hξ : ∀ σ : Gloc K v, ξ (locMap K S v σ) = 1)
    (hε : ∀ σ : Gloc K v, ε (locMap K S v σ) = 1) :
    IsLocallyQuadAtGen (MonoidAlgebra (Acoef i) G) (binaryAlpha (Acoef i) G (alphaChar i χ0 ξ) ε)
      χ0 v :=
  isLocallyQuadAtGen_binaryAlpha (Acoef i) G _ ε χ0 v (isLocallyQuadAt_alphaChar i χ0 ξ v hξ) hε

end Local

/-! ### The coefficient map `A → A[G]` on the coefficient modules -/

section CoefExt

variable (A : Type) [CommRing A] (G : Type) [CommGroup G] {Γ : Type} [Group Γ]
  (α : Γ →* Aˣ) (ε : Γ →* G) (T : Type) [AddCommGroup T]

/-- Definition (tex 3419–3421, 3436–3439: "derived coefficient extension"). **The coefficient
extension** `(A ⊗ T)(α) → (A[G] ⊗ T)(α·[ε])`, `a ⊗ t ↦ a[1] ⊗ t`. -/
def binaryCoefExt : CoefMod A α T →+ CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) T :=
  (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T).toAddEquiv.toAddMonoidHom.comp
    ((LinearMap.rTensor T
        (algebraMap A (MonoidAlgebra A G)).toAddMonoidHom.toIntLinearMap).toAddMonoidHom.comp
      (CoefMod.equiv A α T).symm.toAddEquiv.toAddMonoidHom)

/-- PROVED. `a ⊗ t ↦ a[1] ⊗ t`. -/
theorem binaryCoefExt_tmul (a : A) (t : T) :
    binaryCoefExt A G α ε T (CoefMod.equiv A α T (a ⊗ₜ t)) =
      CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T
        (algebraMap A (MonoidAlgebra A G) a ⊗ₜ t) :=
  rfl

/-- PROVED. The coefficient extension sends `1 ⊗ t` to `1 ⊗ t`. -/
theorem binaryCoefExt_oneTmul (t : T) :
    binaryCoefExt A G α ε T (oneTmul A α T t) =
      oneTmul (MonoidAlgebra A G) (binaryAlpha A G α ε) T t := by
  rw [oneTmul_apply, oneTmul_apply, binaryCoefExt_tmul, map_one]

/-- PROVED. **The coefficient extension is semilinear over `A → A[G]`**: `c(a • m) = a[1] • c(m)`. -/
theorem binaryCoefExt_smul_scalar (a : A) (x : CoefMod A α T) :
    binaryCoefExt A G α ε T (a • x) =
      algebraMap A (MonoidAlgebra A G) a • binaryCoefExt A G α ε T x := by
  obtain ⟨y, rfl⟩ := (CoefMod.equiv A α T).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul a' t =>
    rw [← map_smul (CoefMod.equiv A α T) a (a' ⊗ₜ t), TensorProduct.smul_tmul', smul_eq_mul,
      binaryCoefExt_tmul, binaryCoefExt_tmul,
      ← map_smul (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T)
        (algebraMap A (MonoidAlgebra A G) a) (algebraMap A (MonoidAlgebra A G) a' ⊗ₜ t),
      TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add y y' hy hy' =>
    rw [map_add, smul_add, map_add, hy, hy', map_add, smul_add]

/-- PROVED (tex 3436–3439: "equivariant on `G_{K_v}` since `ε` is trivial there"). **The coefficient
extension commutes with every `g` with `ε(g) = 1`.** -/
theorem binaryCoefExt_smul_of_eq_one [DistribMulAction Γ T] (g : Γ) (hg : ε g = 1)
    (x : CoefMod A α T) :
    binaryCoefExt A G α ε T (g • x) = g • binaryCoefExt A G α ε T x := by
  obtain ⟨y, rfl⟩ := (CoefMod.equiv A α T).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul a t =>
    rw [CoefMod.smul_tmul, binaryCoefExt_tmul, binaryCoefExt_tmul, CoefMod.smul_tmul,
      binaryAlpha_of_eq_one A G α ε g hg, binaryScalarUnit_val, map_mul]
  | add y y' hy hy' =>
    rw [map_add, smul_add, map_add, hy, hy', map_add, smul_add]

/-- PROVED. **The image of the coefficient extension spans** `(A[G] ⊗ T)(α·[ε])` over `A[G]`
(`r ⊗ t = r • c(1 ⊗ t)`). -/
theorem span_range_binaryCoefExt :
    Submodule.span (MonoidAlgebra A G) (Set.range (binaryCoefExt A G α ε T)) = ⊤ := by
  have key : ∀ y : MonoidAlgebra A G ⊗[ℤ] T,
      CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T y ∈
        Submodule.span (MonoidAlgebra A G) (Set.range (binaryCoefExt A G α ε T)) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul r t =>
      have hrt : CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T (r ⊗ₜ t) =
          r • binaryCoefExt A G α ε T (CoefMod.equiv A α T ((1 : A) ⊗ₜ t)) := by
        rw [binaryCoefExt_tmul, map_one,
          ← map_smul (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T) r
            ((1 : MonoidAlgebra A G) ⊗ₜ t), TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hrt]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨_, rfl⟩)
    | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, rfl⟩ := (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T).surjective x
  exact key y

end CoefExt

/-! ### Components: `(A[G] ⊗ T)(α·[ε])` is a `G`-indexed sum of copies of `(A ⊗ T)(α)` -/

section Components

variable (A : Type) [CommRing A] (G : Type) [CommGroup G] {Γ : Type} [Group Γ]
  (α : Γ →* Aˣ) (ε : Γ →* G) (T : Type) [AddCommGroup T]

/-- Definition. The coefficient of `g ∈ G` in `A[G]`, an additive map `A[G] → A`. -/
def binaryCoeffAt (g : G) : MonoidAlgebra A G →+ A where
  toFun r := r.coeff g
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Definition (tex 3436–3439: `A[G]` is free over `A` on `G`). **The `g`-component**
`(A[G] ⊗ T)(α·[ε]) → (A ⊗ T)(α)`, `r ⊗ t ↦ r_g ⊗ t`. -/
def binaryCoefProj (g : G) :
    CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) T →+ CoefMod A α T :=
  (CoefMod.equiv A α T).toAddEquiv.toAddMonoidHom.comp
    ((LinearMap.rTensor T (binaryCoeffAt A G g).toIntLinearMap).toAddMonoidHom.comp
      (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T).symm.toAddEquiv.toAddMonoidHom)

/-- PROVED. `r ⊗ t ↦ r_g ⊗ t`. -/
theorem binaryCoefProj_tmul (g : G) (r : MonoidAlgebra A G) (t : T) :
    binaryCoefProj A G α ε T g
        (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T (r ⊗ₜ t)) =
      CoefMod.equiv A α T (r.coeff g ⊗ₜ t) :=
  rfl

/-- PROVED. **The `g`-component of `r • c(x)` is `r_g • x`.** -/
theorem binaryCoefProj_smul_coefExt (g : G) (r : MonoidAlgebra A G) (x : CoefMod A α T) :
    binaryCoefProj A G α ε T g (r • binaryCoefExt A G α ε T x) = r.coeff g • x := by
  obtain ⟨y, rfl⟩ := (CoefMod.equiv A α T).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul a t =>
    rw [binaryCoefExt_tmul,
      ← map_smul (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T) r
        (algebraMap A (MonoidAlgebra A G) a ⊗ₜ t),
      TensorProduct.smul_tmul', smul_eq_mul, binaryCoefProj_tmul,
      ← map_smul (CoefMod.equiv A α T) (r.coeff g) (a ⊗ₜ t), TensorProduct.smul_tmul',
      smul_eq_mul]
    rw [show (r * algebraMap A (MonoidAlgebra A G) a).coeff g = r.coeff g * a from
      MonoidAlgebra.coeff_mul_single_one r a g]
  | add y y' hy hy' =>
    rw [map_add, map_add, smul_add, map_add, hy, hy', smul_add]

/-- PROVED. **The `g`-component commutes with every `σ` with `ε(σ) = 1`** (on `G_{K_v}` at
`v ∣ 2N`). -/
theorem binaryCoefProj_smul_of_eq_one [DistribMulAction Γ T] (g : G) (σ : Γ) (hσ : ε σ = 1)
    (x : CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) T) :
    binaryCoefProj A G α ε T g (σ • x) = σ • binaryCoefProj A G α ε T g x := by
  obtain ⟨y, rfl⟩ := (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul r t =>
    rw [CoefMod.smul_tmul, binaryCoefProj_tmul, binaryCoefProj_tmul, CoefMod.smul_tmul,
      binaryAlpha_of_eq_one A G α ε σ hσ, binaryScalarUnit_val]
    rw [show (algebraMap A (MonoidAlgebra A G) ((α σ : Aˣ) : A) * r).coeff g =
        ((α σ : Aˣ) : A) * r.coeff g from MonoidAlgebra.coeff_single_one_mul r _ g]
  | add y y' hy hy' =>
    rw [map_add, smul_add, map_add, hy, hy', map_add, smul_add]

/-- PROVED. **Reconstruction from the components** (`G` finite): `x = ∑_g [g] • c(x_g)`. -/
theorem binaryCoefExt_sum_proj [Fintype G]
    (x : CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) T) :
    ∑ g : G, MonoidAlgebra.of A G g •
      binaryCoefExt A G α ε T (binaryCoefProj A G α ε T g x) = x := by
  obtain ⟨y, rfl⟩ := (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul r t =>
    have h1 : ∀ g : G, MonoidAlgebra.of A G g • binaryCoefExt A G α ε T (binaryCoefProj A G α ε T g
        (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T (r ⊗ₜ t))) =
        CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T
          (MonoidAlgebra.single g (r.coeff g) ⊗ₜ t) := by
      intro g
      rw [binaryCoefProj_tmul, binaryCoefExt_tmul,
        ← map_smul (CoefMod.equiv (MonoidAlgebra A G) (binaryAlpha A G α ε) T)
          (MonoidAlgebra.of A G g) (algebraMap A (MonoidAlgebra A G) (r.coeff g) ⊗ₜ t),
        TensorProduct.smul_tmul', smul_eq_mul]
      rw [show MonoidAlgebra.of A G g * algebraMap A (MonoidAlgebra A G) (r.coeff g) =
          MonoidAlgebra.single g (r.coeff g) by
        change MonoidAlgebra.single g 1 * MonoidAlgebra.single 1 (r.coeff g) = _
        rw [MonoidAlgebra.single_mul_single, mul_one, one_mul]]
    have h2 : ∑ g : G, MonoidAlgebra.single g (r.coeff g) = r :=
      (Finsupp.sum_fintype r.coeff MonoidAlgebra.single
        (fun g => MonoidAlgebra.single_zero g)).symm.trans (MonoidAlgebra.sum_coeff_single r)
    rw [Finset.sum_congr rfl fun g _ => h1 g, ← map_sum, ← TensorProduct.sum_tmul, h2]
  | add y y' hy hy' =>
    simp only [map_add, smul_add, Finset.sum_add_distrib]
    rw [hy, hy']

end Components

/-! ### Coefficient maps on continuous cochains (generic) -/

section CochainPush

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M₁ M₂ : Type} [AddCommGroup M₁] [Module k₁ M₁] [DistribMulAction Γ M₁] [SMulCommClass Γ k₁ M₁]
  [TopologicalSpace M₁] [DiscreteTopology M₁]
  [AddCommGroup M₂] [Module k₂ M₂] [DistribMulAction Γ M₂] [SMulCommClass Γ k₂ M₂]
  [TopologicalSpace M₂] [DiscreteTopology M₂]

/-- Definition (tex 3436–3439). **The push-forward of continuous cochains along an additive map**
`c : M₁ → M₂` of discrete modules, `f ↦ c ∘ f` (continuous since `M₁` is discrete). -/
def binaryCochainPush (c : M₁ →+ M₂) (n : ℕ) : contCochain k₁ Γ M₁ n →+ contCochain k₂ Γ M₂ n where
  toFun f := ⟨(fun x => c (asFun k₁ Γ M₁ f.1 x) : (Fin n → Γ) → M₂),
    mem_contCochain.2 ((continuous_of_discreteTopology (f := fun m : M₁ => c m)).comp
      (mem_contCochain.1 f.2))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero c)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add c _ _)

/-- PROVED. The value of the push-forward. -/
theorem binaryCochainPush_apply (c : M₁ →+ M₂) (n : ℕ) (f : contCochain k₁ Γ M₁ n)
    (x : Fin n → Γ) :
    asFun k₂ Γ M₂ (binaryCochainPush (k₁ := k₁) (k₂ := k₂) c n f).1 x = c (asFun k₁ Γ M₁ f.1 x) :=
  rfl

/-- PROVED. The push-forward is semilinear along `ρ : k₁ → k₂` when `c` is. -/
theorem binaryCochainPush_smul (ρ : k₁ →+* k₂) (c : M₁ →+ M₂)
    (hρ : ∀ (a : k₁) (m : M₁), c (a • m) = ρ a • c m) (n : ℕ) (a : k₁)
    (f : contCochain k₁ Γ M₁ n) :
    binaryCochainPush (k₁ := k₁) (k₂ := k₂) c n (a • f) = ρ a • binaryCochainPush (k₁ := k₁) (k₂ := k₂) c n f :=
  Subtype.ext (funext fun _ => hρ a _)

/-- PROVED. `(−1)^n • m` is the integer multiple `(−1)^n • m`, in any module. -/
theorem binary_neg_one_pow_smul {k M : Type} [CommRing k] [AddCommGroup M] [Module k M] (n : ℕ)
    (m : M) : ((-1 : k) ^ n) • m = ((-1 : ℤ) ^ n) • m := by
  rw [← Int.cast_smul_eq_zsmul k, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- PROVED. **The push-forward along an equivariant map commutes with the differential** of the
continuous cochains. -/
theorem binaryCochainPush_contD [ContinuousMul Γ] [ContinuousSMul Γ M₁] [ContinuousSMul Γ M₂]
    (c : M₁ →+ M₂) (hc : ∀ (g : Γ) (m : M₁), c (g • m) = g • c m) (n : ℕ)
    (f : contCochain k₁ Γ M₁ n) :
    contD k₂ Γ M₂ n (binaryCochainPush c n f) =
      binaryCochainPush c (n + 1) (contD k₁ Γ M₁ n f) := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := k₂) (G := Γ) (M := M₂) n
    (binaryCochainPush (k₁ := k₁) (k₂ := k₂) c n f) g
  have h2 := contCochains_d_apply (k := k₁) (G := Γ) (M := M₁) n f g
  have hneg : ∀ (e : ℕ) (x : M₁), ((-1 : k₂) ^ e) • c x = c (((-1 : k₁) ^ e) • x) :=
    fun e x => by
      rw [binary_neg_one_pow_smul (k := k₂), binary_neg_one_pow_smul (k := k₁), map_zsmul]
  refine h1.trans (Eq.trans ?_ (congrArg c h2).symm)
  rw [map_add, map_sum, hc]
  congr 1
  exact Finset.sum_congr rfl fun j _ => hneg _ _

/-- Definition. Evaluation of a continuous cochain at a point of `Γⁿ`, an additive map. -/
def binaryCochainEval (n : ℕ) (x : Fin n → Γ) : contCochain k₂ Γ M₂ n →+ M₂ where
  toFun f := asFun k₂ Γ M₂ f.1 x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- PROVED. **Components of a span of push-forwards**: if `π(r • c(m)) = coef(r) • m`, then `π ∘ −`
maps the `k₂`-span of `c ∘ U` into `U`, for any `k₁`-submodule `U` of cochains. -/
theorem binaryCochainPush_span_proj (c : M₁ →+ M₂) (π : M₂ →+ M₁) (coef : k₂ → k₁)
    (hπ : ∀ (r : k₂) (m : M₁), π (r • c m) = coef r • m) (n : ℕ)
    (U : Submodule k₁ (contCochain k₁ Γ M₁ n)) (f : contCochain k₂ Γ M₂ n)
    (hf : f ∈ Submodule.span k₂ (binaryCochainPush (k₁ := k₁) (k₂ := k₂) c n '' (U : Set _))) :
    binaryCochainPush (k₁ := k₂) (k₂ := k₁) π n f ∈ U := by
  obtain ⟨m, cf, xf, rfl⟩ := Submodule.mem_span_set'.1 hf
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨z, hz, hzx⟩ := (Set.mem_image _ _ _).1 (xf i).2
  have key : binaryCochainPush (k₁ := k₂) (k₂ := k₁) π n (cf i • (xf i).1) = coef (cf i) • z := by
    rw [← hzx]
    exact Subtype.ext (funext fun _ => hπ (cf i) _)
  rw [key]
  exact Submodule.smul_mem _ _ (SetLike.mem_coe.1 hz)

/-- PROVED. **Reconstruction of a cochain from its components**: if `∑_j e_j • c(π_j m) = m` on
`M₂`, then `∑_j e_j • c_*((π_j)_* f) = f` for every cochain `f`. -/
theorem binaryCochainPush_sum_proj {ι : Type} [Fintype ι] (c : M₁ →+ M₂) (π : ι → M₂ →+ M₁)
    (e : ι → k₂) (hrec : ∀ m : M₂, ∑ j, e j • c (π j m) = m) (n : ℕ)
    (f : contCochain k₂ Γ M₂ n) :
    ∑ j, e j • binaryCochainPush (k₁ := k₁) (k₂ := k₂) c n
      (binaryCochainPush (k₁ := k₂) (k₂ := k₁) (π j) n f) = f :=
  Subtype.ext (funext fun x => (map_sum (binaryCochainEval (k₂ := k₂) (M₂ := M₂) n x) _ _).trans
    (hrec _))

/-- PROVED. **A cochain whose components all lie in `U` lies in the `k₂`-span of `c ∘ U`.** -/
theorem binaryCochainPush_span_of_proj {ι : Type} [Fintype ι] (c : M₁ →+ M₂) (π : ι → M₂ →+ M₁)
    (e : ι → k₂) (hrec : ∀ m : M₂, ∑ j, e j • c (π j m) = m) (n : ℕ)
    (U : Submodule k₁ (contCochain k₁ Γ M₁ n)) (f : contCochain k₂ Γ M₂ n)
    (hf : ∀ j, binaryCochainPush (k₁ := k₂) (k₂ := k₁) (π j) n f ∈ U) :
    f ∈ Submodule.span k₂ (binaryCochainPush (k₁ := k₁) (k₂ := k₂) c n '' (U : Set _)) := by
  rw [← binaryCochainPush_sum_proj (k₁ := k₁) c π e hrec n f]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hf j, rfl⟩)

end CochainPush

/-! ### Kummer conditions along a coefficient map (generic) -/

section KummerPush

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m] {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂]
  {M₁ M₂ : Type} [AddCommGroup M₁] [Module k₁ M₁]
  [DistribMulAction (Field.absoluteGaloisGroup F) M₁]
  [SMulCommClass (Field.absoluteGaloisGroup F) k₁ M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M₁]
  [AddCommGroup M₂] [Module k₂ M₂] [DistribMulAction (Field.absoluteGaloisGroup F) M₂]
  [SMulCommClass (Field.absoluteGaloisGroup F) k₂ M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M₂]
  (ρ : k₁ →+* k₂) (c : M₁ →+ M₂) (hρ : ∀ (a : k₁) (x : M₁), c (a • x) = ρ a • c x)
  (hc : ∀ (σ : Field.absoluteGaloisGroup F) (x : M₁), c (σ • x) = σ • c x)
  (ι : TorsAlg F B m →+ M₁)

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M₁]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M₂] in
/-- PROVED. **The Kummer cochains of `c ∘ ι` are the push-forwards of those of `ι`**:
`g ↦ a • c(ι(κ_P(g)))` is `a • (c ∘ (ι ∘ κ_P))`. -/
theorem binary_kummerCocycleIn_comp (a : k₂) (P : B.toAffine.Point) :
    kummerCocycleIn (c.comp ι) a P =
      a • binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 (kummerCocycleIn ι (1 : k₁) P) := by
  apply Subtype.ext
  funext g
  change a • c (ι (kummerFun F B m P (g 0))) = a • c ((1 : k₁) • ι (kummerFun F B m P (g 0)))
  rw [one_smul]

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M₁]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M₂] in
include hρ in
/-- PROVED. **The Kummer submodule of `c ∘ ι` is the `k₂`-span of the push-forward of the Kummer
submodule of `ι`.** -/
theorem binary_kummerZ'_comp :
    kummerZ' k₂ (c.comp ι) =
      Submodule.span k₂ (binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 '' (kummerZ' k₁ ι : Set _)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, P⟩, rfl⟩
    change kummerCocycleIn (c.comp ι) a P ∈ _
    rw [binary_kummerCocycleIn_comp (k₁ := k₁) c ι a P]
    exact Submodule.smul_mem _ a
      (Submodule.subset_span ⟨_, kummerCocycleIn_mem ι (1 : k₁) P, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨a, P⟩, rfl⟩ := hw
      change binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 (kummerCocycleIn ι a P) ∈ kummerZ' k₂ (c.comp ι)
      rw [kummerCocycleIn_eq_smul ι a P, binaryCochainPush_smul ρ c hρ, ←
        binary_kummerCocycleIn_comp (k₁ := k₁) c ι (ρ a) P]
      exact kummerCocycleIn_mem (c.comp ι) (ρ a) P
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [binaryCochainPush_smul ρ c hρ]; exact Submodule.smul_mem _ _ hx

omit [CharZero F] [DecidableEq F] in
include hc in
/-- PROVED. **The push-forward of a continuous coboundary is a coboundary.** -/
theorem binary_push_mem_contB1 (z : contCochain k₁ (Field.absoluteGaloisGroup F) M₁ 1)
    (hz : z ∈ contB1 k₁ (Field.absoluteGaloisGroup F) M₁) :
    binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 z ∈ contB1 k₂ (Field.absoluteGaloisGroup F) M₂ := by
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hz
  exact LinearMap.mem_range.2 ⟨binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 0 f,
    binaryCochainPush_contD c hc 0 f⟩

omit [CharZero F] [DecidableEq F] in
include hc in
/-- PROVED. **When the image of `c` spans `M₂`, the coboundaries of `M₂` are the `k₂`-span of the
push-forward of the coboundaries of `M₁`** (`d(r • c(m)) = r • c_*(d m)`). -/
theorem binary_contB1_push (hspan : Submodule.span k₂ (Set.range c) = ⊤) :
    contB1 k₂ (Field.absoluteGaloisGroup F) M₂ =
      Submodule.span k₂ (binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 ''
        (contB1 k₁ (Field.absoluteGaloisGroup F) M₁ : Set _)) := by
  apply le_antisymm
  · intro b hb
    obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hb
    let D : M₂ →ₗ[k₂] contCochain k₂ (Field.absoluteGaloisGroup F) M₂ 1 :=
      contD k₂ (Field.absoluteGaloisGroup F) M₂ 0 ∘ₗ
        { toFun := fun t => constCochain t
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    have hf : contD k₂ (Field.absoluteGaloisGroup F) M₂ 0 f = D (cfun f default) := by
      change contD k₂ (Field.absoluteGaloisGroup F) M₂ 0 f =
        contD k₂ (Field.absoluteGaloisGroup F) M₂ 0 (constCochain (cfun f default))
      rw [← eq_constCochain]
    have hm : cfun f default ∈ Submodule.span k₂ (Set.range c) := by
      rw [hspan]
      trivial
    have hle : (Submodule.span k₂ (Set.range c)).map D ≤
        Submodule.span k₂ (binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 ''
          (contB1 k₁ (Field.absoluteGaloisGroup F) M₁ : Set _)) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨m', rfl⟩, rfl⟩
      refine ⟨contD k₁ (Field.absoluteGaloisGroup F) M₁ 0 (constCochain m'),
        LinearMap.mem_range.2 ⟨_, rfl⟩, ?_⟩
      rw [← binaryCochainPush_contD c hc 0 (constCochain m')]
      rfl
    rw [hf]
    exact hle ⟨_, hm, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact binary_push_mem_contB1 c hc z hz

include hρ hc in
/-- PROVED (tex 3419–3421, 3436–3439: "derived scalar extension", degree one). **The degree-one
term of the Kummer condition of `c ∘ ι` is the `k₂`-span of the push-forward of the degree-one term
of the Kummer condition of `ι`**: `Z'(c∘ι) + B¹(M₂) = span_{k₂} c_*(Z'(ι) + B¹(M₁))`. -/
theorem binary_condOne_push (hspan : Submodule.span k₂ (Set.range c) = ⊤) :
    kummerZ' k₂ (c.comp ι) ⊔ contB1 k₂ (Field.absoluteGaloisGroup F) M₂ =
      Submodule.span k₂ (binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 ''
        ((kummerZ' k₁ ι ⊔ contB1 k₁ (Field.absoluteGaloisGroup F) M₁ :
          Submodule k₁ (contCochain k₁ (Field.absoluteGaloisGroup F) M₁ 1)) : Set _)) := by
  rw [binary_kummerZ'_comp ρ c hρ ι, binary_contB1_push (k₁ := k₁) c hc hspan]
  apply le_antisymm
  · refine sup_le (Submodule.span_mono (Set.image_mono ?_))
      (Submodule.span_mono (Set.image_mono ?_))
    · exact fun z hz => Submodule.mem_sup_left hz
    · exact fun z hz => Submodule.mem_sup_right hz
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨z, hz, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨z, hz, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M₁] in
/-- PROVED. **The local Kummer class of `c ∘ ι` is the class of the push-forward of the Kummer
cocycle of `ι`**: `kummerMapIn (c∘ι) P = [c ∘ (ι ∘ κ_P)]`. -/
theorem binary_kummerMapIn_push (hι' : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m),
      (c.comp ι) (σ • t) = σ • (c.comp ι) t) (P : B.toAffine.Point) :
    ∃ y : (natCx (contCochains k₂ (Field.absoluteGaloisGroup F) M₂)).toCC.cycles 1,
      ((natCx (contCochains k₂ (Field.absoluteGaloisGroup F) M₂)).toCC.iCycles 1).hom y =
        binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 (kummerCocycleIn ι (1 : k₁) P) ∧
      ((natCx (contCochains k₂ (Field.absoluteGaloisGroup F) M₂)).toCC.homologyπ 1).hom y =
        kummerMapIn k₂ (c.comp ι) hι' P := by
  obtain ⟨y, hy1, hy2⟩ := cocycleCondition_homologyMap_inv_mk (kummerZ' k₂ (c.comp ι))
    (kummerZ'_cocycle k₂ (c.comp ι) hι') (kummerEltIn k₂ (c.comp ι) hι' P)
  refine ⟨y, hy1.trans ?_, hy2.symm⟩
  change kummerCocycleIn (c.comp ι) (1 : k₂) P = _
  rw [binary_kummerCocycleIn_comp (k₁ := k₁) c ι, one_smul]

include hρ hc in
/-- PROVED (tex 3419–3421, 3436–3439, in `H¹`). **The `H¹` image of the Kummer condition of
`c ∘ ι` is the `k₂`-span of the classes of the push-forwards `c ∘ z` of the degree-one term `z` of
the Kummer condition of `ι`.** -/
theorem binary_range_H1_push (hι' : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m),
      (c.comp ι) (σ • t) = σ • (c.comp ι) t)
    (hspan : Submodule.span k₂ (Set.range c) = ⊤) :
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (kummerConditionInι k₂ (c.comp ι) hι')) 1).hom =
      Submodule.span k₂ {x | ∃ z ∈ kummerZ' k₁ ι ⊔ contB1 k₁ (Field.absoluteGaloisGroup F) M₁,
        ∃ y : (natCx (contCochains k₂ (Field.absoluteGaloisGroup F) M₂)).toCC.cycles 1,
          ((natCx (contCochains k₂ (Field.absoluteGaloisGroup F) M₂)).toCC.iCycles 1).hom y =
            binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 z ∧
          ((natCx (contCochains k₂ (Field.absoluteGaloisGroup F) M₂)).toCC.homologyπ 1).hom y =
            x} := by
  apply le_antisymm
  · rw [range_homologyMap_kummerConditionIn k₂ (c.comp ι) hι']
    refine Submodule.span_mono ?_
    rintro _ ⟨P, rfl⟩
    obtain ⟨y, hy1, hy2⟩ := binary_kummerMapIn_push (k₁ := k₁) (k₂ := k₂) c ι hι' P
    exact ⟨kummerCocycleIn ι (1 : k₁) P,
      Submodule.mem_sup_left (kummerCocycleIn_mem ι (1 : k₁) P), y, hy1, hy2⟩
  · refine Submodule.span_le.2 ?_
    rintro x ⟨z, hz, y, hy1, rfl⟩
    have hmem : binaryCochainPush (k₁ := k₁) (k₂ := k₂) c 1 z ∈
        kummerZ' k₂ (c.comp ι) ⊔ contB1 k₂ (Field.absoluteGaloisGroup F) M₂ := by
      rw [binary_condOne_push ρ c hρ hc ι hspan]
      exact Submodule.subset_span ⟨z, hz, rfl⟩
    exact (cocycleCondition_range_homologyMap_one (kummerZ' k₂ (c.comp ι))
      (kummerZ'_cocycle k₂ (c.comp ι) hι') _).2 ⟨y, hy1 ▸ hmem, rfl⟩

end KummerPush

/-! ### The binary Kummer condition at `v ∣ 2N` -/

section BinaryCond

variable (A : Type) [CommRing A] (G : Type) [CommGroup G] (W : WeierstrassCurve K) [W.IsElliptic]
  (N : ℕ) [NeZero N] (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
  (α : GKS K S →* Aˣ) (ε : GKS K S →* G) (hFull : FullTorsion K S W N)

/-- Definition. The coefficient extension `a ⊗ t ↦ a[1] ⊗ t` on the modules with `G_{K_v}` acting
through `p_v` (the format of lane RC28's `kummerAt`). -/
def binaryCoefExtRes (T : Type) [AddCommGroup T] [DistribMulAction (GKS K S) T]
    (v : HeightOneSpectrum (𝓞 K)) :
    ResMod (locMap K S v) (CoefMod A α T) →+
      ResMod (locMap K S v) (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) T) :=
  binaryCoefExt A G α ε T

/-- PROVED (tex 3436–3439). **The coefficient extension is `G_{K_v}`-equivariant when `ε` is
trivial on the decomposition group at `v`.** -/
theorem binaryCoefExtRes_smul (T : Type) [AddCommGroup T] [DistribMulAction (GKS K S) T]
    (v : HeightOneSpectrum (𝓞 K)) (hε : ∀ σ : Gloc K v, ε (locMap K S v σ) = 1) (σ : Gloc K v)
    (x : ResMod (locMap K S v) (CoefMod A α T)) :
    binaryCoefExtRes A G α ε T v (σ • x) = σ • binaryCoefExtRes A G α ε T v x :=
  binaryCoefExt_smul_of_eq_one A G α ε T (locMap K S v σ) (hε σ) x

/-- PROVED (tex 3419–3421, 3436–3439). **The binary Kummer coefficient map is the coefficient
extension of the scalar one**: `ι_v^{bin} = (a ↦ a[1]) ∘ ι_v^{sc}`, both `t ↦ 1 ⊗ j⁻¹(φ_q t)`
(`φ_q` at the square root `s` of `h = h_0`), over `A[G]` with the character `α·[ε]`, resp. over `A`
with the character `α`. -/
theorem genIota_binary_eq (v : HeightOneSpectrum (𝓞 K)) :
    genIota (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v =
      (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v).comp
        (genIota A W N s hs hs0 α hFull v) := by
  refine AddMonoidHom.ext fun t => ?_
  rw [AddMonoidHom.comp_apply, genIota_apply, genIota_apply, genIotaBase_apply,
    genIotaBase_apply]
  exact (binaryCoefExt_oneTmul A G α ε (TorsS K S W (N : ℤ)) _).symm

/-- Definition. The `g`-component on the modules with `G_{K_v}` acting through `p_v`. -/
def binaryCoefProjRes (T : Type) [AddCommGroup T] [DistribMulAction (GKS K S) T] (g : G)
    (v : HeightOneSpectrum (𝓞 K)) :
    ResMod (locMap K S v) (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) T) →+
      ResMod (locMap K S v) (CoefMod A α T) :=
  binaryCoefProj A G α ε T g

variable [IsOpenKer (binaryAlpha A G α ε)] (v : Places K S)
  (hα : IsLocallyQuadAtGen A α (quadChar s hs hs0) v.1)
  (hε : ∀ σ : Gloc K v.1, ε (locMap K S v.1 σ) = 1)

/-- Definition (tex 2754–2756, 3429–3440). **The `A[G]` Kummer condition at `v`** (`v ∣ 2N` in
the text): `genKummerAt` over the binary ring `A[G]`, for the binary module
`(A[G] ⊗ E(K_S)[N])(α·[ε])` and the twist `B = E^{(h_0)}` (`s² = h_0`); its coefficient map is
equivariant because `α·[ε] = χ_{h_0}` on `G_{K_v}` (`isLocallyQuadAtGen_binaryAlpha`). -/
def binaryKummerAt :
    CondAt K S (MonoidAlgebra A G)
      (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v :=
  genKummerAt (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v
    (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε)

/-- PROVED. The `A[G]` Kummer condition is a subcomplex of the local cochains. -/
theorem binaryKummerAt_isInjective :
    (binaryKummerAt A G W N s hs hs0 α ε hFull v hα hε).IsInjective :=
  genKummerAt_isInjective (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v
    (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε)

/-- PROVED (tex 3415–3417). The `A[G]` Kummer condition has all of `H⁰`. -/
theorem binaryKummerAt_isIso_H0 :
    IsIso (HomologicalComplex.homologyMap
      (GHom.toCC (binaryKummerAt A G W N s hs hs0 α ε hFull v hα hε).i) 0) :=
  genKummerAt_isIso_H0 (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v
    (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε)

/-- PROVED (tex 3415–3418). The `A[G]` Kummer condition injects on `H¹`. -/
theorem binaryKummerAt_mono_H1 :
    Mono (HomologicalComplex.homologyMap
      (GHom.toCC (binaryKummerAt A G W N s hs hs0 α ε hFull v hα hε).i) 1) :=
  genKummerAt_mono_H1 (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v
    (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε)

/-- PROVED (tex 3415–3418, 3436–3439). **The `H¹` image of the `A[G]` Kummer condition is the
`A[G]`-span of the image of its local Kummer map** `E^{(h_0)}(K_v) → H¹(K_v, M_i^{bin})`. -/
theorem binaryKummerAt_range_eq_span :
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (binaryKummerAt A G W N s hs hs0 α ε hFull v hα hε).i) 1).hom =
      Submodule.span (MonoidAlgebra A G) (Set.range (genKummerMap (MonoidAlgebra A G) W N s hs
        hs0 (binaryAlpha A G α ε) hFull v (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε))) :=
  genKummerAt_range_eq_span (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v
    (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε)

open scoped Classical in
/-- PROVED (`rfl`). The inclusion of the `A[G]` Kummer condition is lane RC28's
`kummerConditionInι` for the binary coefficient map. -/
theorem binaryKummerAt_i :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    (binaryKummerAt A G W N s hs hs0 α ε hFull v hα hε).i =
      kummerConditionInι (MonoidAlgebra A G)
        (genIota (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1)
        (genIota_smul (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1
          (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε)) :=
  rfl

variable [IsOpenKer α]

open scoped Classical in
include hε in
/-- PROVED (tex 3419–3421, 3436–3439: "identify the scalar and binary versions by derived coefficient
extension", degree one). **The degree-one term of the `A[G]` Kummer condition at `v` is the
`A[G]`-span of the image, under `c ∘ −` (`c : a ⊗ t ↦ a[1] ⊗ t`), of the degree-one term of the
scalar `A` Kummer condition** (same twist `E^{(h_0)}`, scalar character `α`):
`span_{A[G]}(ι^{bin}∘κ_P) + B¹ = span_{A[G]} c_*(span_A(ι^{sc}∘κ_P) + B¹)`. Only `ε ∘ p_v = 1`
is used. -/
theorem binaryKummer_condOne_eq_span :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    kummerZ' (MonoidAlgebra A G)
        (genIota (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1) ⊔
      contB1 (MonoidAlgebra A G) (Gloc K v.1) (ResMod (locMap K S v.1)
        (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ)))) =
      Submodule.span (MonoidAlgebra A G)
        (binaryCochainPush (k₁ := A) (k₂ := MonoidAlgebra A G)
          (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1) 1 ''
          ((kummerZ' A (genIota A W N s hs hs0 α hFull v.1) ⊔
            contB1 A (Gloc K v.1) (ResMod (locMap K S v.1) (CoefMod A α (TorsS K S W (N : ℤ)))) :
              Submodule A _) : Set _)) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  rw [genIota_binary_eq A G W N s hs hs0 α ε hFull v.1]
  exact binary_condOne_push (algebraMap A (MonoidAlgebra A G))
    (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1)
    (binaryCoefExt_smul_scalar A G α ε (TorsS K S W (N : ℤ)))
    (binaryCoefExtRes_smul A G α ε (TorsS K S W (N : ℤ)) v.1 hε)
    (genIota A W N s hs hs0 α hFull v.1)
    (span_range_binaryCoefExt A G α ε (TorsS K S W (N : ℤ)))

open scoped Classical in
/-- PROVED (tex 3419–3421, 3436–3439, in `H¹`). **The `H¹` image of the `A[G]` Kummer condition
at `v` is the `A[G]`-span of the classes `[c ∘ z]` of the coefficient extensions of the cocycles
`z` of the degree-one term of the scalar `A` Kummer condition.** -/
theorem binaryKummerAt_range_H1_eq_span :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (binaryKummerAt A G W N s hs hs0 α ε hFull v hα hε).i) 1).hom =
      Submodule.span (MonoidAlgebra A G) {x | ∃ z ∈ kummerZ' A (genIota A W N s hs hs0 α hFull v.1) ⊔
          contB1 A (Gloc K v.1) (ResMod (locMap K S v.1) (CoefMod A α (TorsS K S W (N : ℤ)))),
        ∃ y : (locAt K S (MonoidAlgebra A G)
            (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.cycles 1,
          ((locAt K S (MonoidAlgebra A G)
            (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.iCycles
              1).hom y =
            binaryCochainPush (k₁ := A) (k₂ := MonoidAlgebra A G)
              (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1) 1 z ∧
          ((locAt K S (MonoidAlgebra A G)
            (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.homologyπ
              1).hom y = x} := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  have key : ∀ (ι' : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) N →+
      ResMod (locMap K S v.1)
        (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))))
      (hι' : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) N),
        ι' (σ • t) = σ • ι' t),
      ι' = (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1).comp
        (genIota A W N s hs hs0 α hFull v.1) →
      LinearMap.range (HomologicalComplex.homologyMap
        (GHom.toCC (kummerConditionInι (MonoidAlgebra A G) ι' hι')) 1).hom =
      Submodule.span (MonoidAlgebra A G) {x | ∃ z ∈ kummerZ' A (genIota A W N s hs hs0 α hFull v.1) ⊔
          contB1 A (Gloc K v.1) (ResMod (locMap K S v.1) (CoefMod A α (TorsS K S W (N : ℤ)))),
        ∃ y : (locAt K S (MonoidAlgebra A G)
            (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.cycles 1,
          ((locAt K S (MonoidAlgebra A G)
            (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.iCycles
              1).hom y =
            binaryCochainPush (k₁ := A) (k₂ := MonoidAlgebra A G)
              (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1) 1 z ∧
          ((locAt K S (MonoidAlgebra A G)
            (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.homologyπ
              1).hom y = x} := by
    intro ι' hι' heq
    subst heq
    exact binary_range_H1_push (algebraMap A (MonoidAlgebra A G))
      (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1)
      (binaryCoefExt_smul_scalar A G α ε (TorsS K S W (N : ℤ)))
      (binaryCoefExtRes_smul A G α ε (TorsS K S W (N : ℤ)) v.1 hε)
      (genIota A W N s hs hs0 α hFull v.1) hι'
      (span_range_binaryCoefExt A G α ε (TorsS K S W (N : ℤ)))
  rw [binaryKummerAt_i A G W N s hs hs0 α ε hFull v hα hε]
  exact key _ _ (genIota_binary_eq A G W N s hs hs0 α ε hFull v.1)

omit [IsOpenKer α] in
open scoped Classical in
/-- PROVED (tex 3419–3421, 3436–3439, on Kummer classes). **The binary local Kummer class of
`P ∈ E^{(h_0)}(K_v)` is the class of the coefficient extension `c ∘ (ι^{sc} ∘ κ_P)` of the scalar
Kummer cocycle.** -/
theorem binaryKummerMap_eq_push (P : (localTwist W h v.1).toAffine.Point) :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    ∃ y : (locAt K S (MonoidAlgebra A G)
        (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.cycles 1,
      ((locAt K S (MonoidAlgebra A G)
        (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.iCycles
          1).hom y =
        binaryCochainPush (k₁ := A) (k₂ := MonoidAlgebra A G)
          (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1) 1
          (kummerCocycleIn (genIota A W N s hs hs0 α hFull v.1) (1 : A) P) ∧
      ((locAt K S (MonoidAlgebra A G)
        (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.homologyπ
          1).hom y =
        genKummerMap (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v
          (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε) P := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  obtain ⟨y, hy1, hy2⟩ := cocycleCondition_homologyMap_inv_mk
    (kummerZ' (MonoidAlgebra A G)
      (genIota (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1))
    (kummerZ'_cocycle (MonoidAlgebra A G)
      (genIota (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1)
      (genIota_smul (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1
        (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε)))
    (kummerEltIn (MonoidAlgebra A G)
      (genIota (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1)
      (genIota_smul (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1
        (isLocallyQuadAtGen_binaryAlpha A G α ε _ v.1 hα hε)) P)
  refine ⟨y, hy1.trans ?_, hy2.symm⟩
  change kummerCocycleIn
    (genIota (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1)
      (1 : MonoidAlgebra A G) P = _
  rw [genIota_binary_eq A G W N s hs hs0 α ε hFull v.1, binary_kummerCocycleIn_comp (k₁ := A),
    one_smul]

omit [IsOpenKer α] in
open scoped Classical in
/-- PROVED (tex 3419–3421, 3436–3439, in `H¹`). **The `H¹` image of the `A[G]` Kummer condition
at `v` is the `A[G]`-span of the coefficient extensions of the scalar local Kummer classes**: of the
classes of the cocycles `c ∘ (ι^{sc} ∘ κ_P)`, `P ∈ E^{(h_0)}(K_v)` (the scalar Kummer cocycle
`ι^{sc} ∘ κ_P` represents the scalar local Kummer class, `binaryScalarKummerMap_eq`). -/
theorem binaryKummerAt_range_eq_span_push :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (binaryKummerAt A G W N s hs hs0 α ε hFull v hα hε).i) 1).hom =
      Submodule.span (MonoidAlgebra A G) {x | ∃ P : (localTwist W h v.1).toAffine.Point,
        ∃ y : (locAt K S (MonoidAlgebra A G)
            (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.cycles 1,
          ((locAt K S (MonoidAlgebra A G)
            (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.iCycles
              1).hom y =
            binaryCochainPush (k₁ := A) (k₂ := MonoidAlgebra A G)
              (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1) 1
              (kummerCocycleIn (genIota A W N s hs hs0 α hFull v.1) (1 : A) P) ∧
          ((locAt K S (MonoidAlgebra A G)
            (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ))) v).toCC.homologyπ
              1).hom y = x} := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  rw [binaryKummerAt_range_eq_span A G W N s hs hs0 α ε hFull v hα hε]
  congr 1
  ext x
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨y, hy1, hy2⟩ := binaryKummerMap_eq_push A G W N s hs hs0 α ε hFull v hα hε P
    exact ⟨P, y, hy1, hy2⟩
  · rintro ⟨P, y, hy1, rfl⟩
    obtain ⟨y', hy1', hy2'⟩ := binaryKummerMap_eq_push A G W N s hs hs0 α ε hFull v hα hε P
    have hyy : y = y' := (ModuleCat.mono_iff_injective _).1 inferInstance (hy1.trans hy1'.symm)
    exact ⟨P, by rw [hyy, hy2']⟩

open scoped Classical in
include hε in
/-- PROVED (tex 3436–3439: "The `A_i[G]` Kummer condition … [is a] derived scalar extension of the
fixed local data", component form; `A[G]` is free over `A` on `G`). **The degree-one term of the
`A[G]` Kummer condition at `v` is the `G`-indexed sum of copies of the degree-one term of the
scalar `A` Kummer condition**: a binary `1`-cochain `f` lies in `span_{A[G]}(ι^{bin}∘κ_P) + B¹` iff
every component `(π_g)_* f` (`g ∈ G`, `π_g : r ⊗ t ↦ r_g ⊗ t`) lies in `span_A(ι^{sc}∘κ_P) + B¹`
(`G` finite). -/
theorem binaryKummer_condOne_iff_components [Fintype G]
    (f : contCochain (MonoidAlgebra A G) (Gloc K v.1) (ResMod (locMap K S v.1)
      (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ)))) 1) :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    f ∈ kummerZ' (MonoidAlgebra A G)
        (genIota (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v.1) ⊔
      contB1 (MonoidAlgebra A G) (Gloc K v.1) (ResMod (locMap K S v.1)
        (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S W (N : ℤ)))) ↔
    ∀ g : G, binaryCochainPush (k₁ := MonoidAlgebra A G) (k₂ := A)
        (binaryCoefProjRes A G α ε (TorsS K S W (N : ℤ)) g v.1) 1 f ∈
      kummerZ' A (genIota A W N s hs hs0 α hFull v.1) ⊔
        contB1 A (Gloc K v.1) (ResMod (locMap K S v.1) (CoefMod A α (TorsS K S W (N : ℤ)))) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  rw [binaryKummer_condOne_eq_span A G W N s hs hs0 α ε hFull v hε]
  constructor
  · intro hf g
    exact binaryCochainPush_span_proj (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1)
      (binaryCoefProjRes A G α ε (TorsS K S W (N : ℤ)) g v.1) (fun r => r.coeff g)
      (binaryCoefProj_smul_coefExt A G α ε (TorsS K S W (N : ℤ)) g) 1 _ f hf
  · intro hf
    exact binaryCochainPush_span_of_proj (binaryCoefExtRes A G α ε (TorsS K S W (N : ℤ)) v.1)
      (fun g => binaryCoefProjRes A G α ε (TorsS K S W (N : ℤ)) g v.1) (MonoidAlgebra.of A G)
      (binaryCoefExt_sum_proj A G α ε (TorsS K S W (N : ℤ))) 1 _ f hf

end BinaryCond

/-! ### The binary module built over `G_{K,S₀}`, inflated to the Selmer support `S ⊇ S₀` -/

section BinaryInflated

variable {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (A : Type) [CommRing A] (G : Type)
  [CommGroup G] (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (α : GKS K S₀ →* Aˣ) (ε : GKS K S₀ →* G)
  [IsOpenKer (binaryAlpha A G α ε)] (hFull : FullTorsion K S₀ W N)

/-- Definition (tex 2754–2756, 3429–3440 with (4.3), tex 3455–3463). **The `A[G]` Kummer condition
at `v ∈ S` for the binary module built over `G_{K,S₀}` and inflated to `G_{K,S}`**
(`genKummerAtS` over `A[G]`). -/
def binaryKummerAtS (v : Places K S)
    (hα : IsLocallyQuadAtGen (S := S₀) A α (quadChar s hs hs0) v.1)
    (hε : ∀ σ : Gloc K v.1, ε (locMap K S₀ v.1 σ) = 1) :
    CondAt K S (MonoidAlgebra A G) (InflMod hS
      (CoefMod (MonoidAlgebra A G) (binaryAlpha A G α ε) (TorsS K S₀ W (N : ℤ)))) v :=
  genKummerAtS hS (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v
    (isLocallyQuadAtGen_binaryAlpha (S := S₀) A G α ε _ v.1 hα hε)

/-- PROVED. The inflated `A[G]` Kummer condition is a subcomplex of the local cochains. -/
theorem binaryKummerAtS_isInjective (v : Places K S)
    (hα : IsLocallyQuadAtGen (S := S₀) A α (quadChar s hs hs0) v.1)
    (hε : ∀ σ : Gloc K v.1, ε (locMap K S₀ v.1 σ) = 1) :
    (binaryKummerAtS hS A G W N s hs hs0 α ε hFull v hα hε).IsInjective :=
  genKummerAtS_isInjective hS (MonoidAlgebra A G) W N s hs hs0 (binaryAlpha A G α ε) hFull v
    (isLocallyQuadAtGen_binaryAlpha (S := S₀) A G α ε _ v.1 hα hε)

end BinaryInflated

open scoped Classical in
/-- PROVED (tex 3415–3418). **The scalar local Kummer class of `P` is the class of the scalar
Kummer cocycle `ι^{sc} ∘ κ_P`** (the scalar counterpart of `binaryKummerMap_eq_push`). -/
theorem binaryScalarKummerMap_eq (A : Type) [CommRing A] (W : WeierstrassCurve K) [W.IsElliptic]
    (N : ℕ) [NeZero N] (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
    (α : GKS K S →* Aˣ) [IsOpenKer α] (hFull : FullTorsion K S W N) (v : Places K S)
    (hα : IsLocallyQuadAtGen A α (quadChar s hs hs0) v.1)
    (P : (localTwist W h v.1).toAffine.Point) :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    ∃ y : (locAt K S A (CoefMod A α (TorsS K S W (N : ℤ))) v).toCC.cycles 1,
      ((locAt K S A (CoefMod A α (TorsS K S W (N : ℤ))) v).toCC.iCycles 1).hom y =
        kummerCocycleIn (genIota A W N s hs hs0 α hFull v.1) (1 : A) P ∧
      ((locAt K S A (CoefMod A α (TorsS K S W (N : ℤ))) v).toCC.homologyπ 1).hom y =
        genKummerMap A W N s hs hs0 α hFull v hα P := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  obtain ⟨y, hy1, hy2⟩ := cocycleCondition_homologyMap_inv_mk
    (kummerZ' A (genIota A W N s hs hs0 α hFull v.1))
    (kummerZ'_cocycle A (genIota A W N s hs hs0 α hFull v.1)
      (genIota_smul A W N s hs hs0 α hFull v.1 hα))
    (kummerEltIn A (genIota A W N s hs hs0 α hFull v.1)
      (genIota_smul A W N s hs hs0 α hFull v.1 hα) P)
  exact ⟨y, hy1, hy2.symm⟩


/-! ### Non-vacuity -/

section NonVacuity

omit [NumberField K] in
/-- PROVED. `1 ∈ K_S` is a square root of `1`. -/
theorem binary_one_sq : (1 : KS K S) ^ 2 = algebraMap K (KS K S) 1 := by
  rw [one_pow, map_one]

/-- PROVED. The quadratic character of `h = 1` (square root `1`) is trivial. -/
theorem binary_quadChar_one :
    quadChar (1 : KS K S) binary_one_sq one_ne_zero = 1 := by
  ext σ
  simp [quadChar]

/-- PROVED (non-vacuity of the hypotheses of `binary_locMap_eq_one_of_signChars`). For
`G = {±1}`, `ε = 1`, every sign character composed with `ε` is the quadratic character of `1`, a
square everywhere; the conclusion holds. -/
theorem binary_locMap_eq_one_of_signChars_nonvacuous (v : HeightOneSpectrum (𝓞 K))
    (σ : Gloc K v) : (1 : GKS K S →* ℤˣ) (locMap K S v σ) = 1 :=
  binary_locMap_eq_one_of_signChars (G := ℤˣ) Int.units_mul_self 1 (fun _ => (1 : KS K S))
    (dx := fun _ => 1) (fun _ => binary_one_sq) (fun _ => one_ne_zero)
    (fun x => by rw [MonoidHom.comp_one, binary_quadChar_one]) v
    (fun _ => by rw [map_one]; exact IsSquare.one) σ

omit [NumberField K] in
/-- PROVED. The trivial character to the trivial group has open kernel. -/
theorem binary_isOpen_ker_one : IsOpen ((1 : GKS K S →* Unit).ker : Set (GKS K S)) := by
  rw [MonoidHom.ker_one, Subgroup.coe_top]
  exact isOpen_univ

/-- PROVED. The binary character for the trivial group and `ε = 1` has open kernel. -/
instance binaryIsOpenKer_trivial (A : Type) [CommRing A] (α : GKS K S →* Aˣ) [IsOpenKer α] :
    IsOpenKer (binaryAlpha A Unit α 1) :=
  isOpenKer_binaryAlpha A Unit α 1 binary_isOpen_ker_one

/-- PROVED. The binary character of a finite universal character has open kernel. -/
instance binaryIsOpenKer_univ (A : Type) [CommRing A] (α : GKS K S →* Aˣ) [IsOpenKer α]
    {ι : Type} [Finite ι] (s : ι → KS K S) {d : ι → K}
    (hs : ∀ j, s j ^ 2 = algebraMap K (KS K S) (d j)) (hs0 : ∀ j, s j ≠ 0) :
    IsOpenKer (binaryAlpha A (ι → ℤˣ) α (binaryUnivChar s hs hs0)) :=
  isOpenKer_binaryAlpha A (ι → ℤˣ) α _ (isOpen_ker_binaryUnivChar s hs hs0)

/-- PROVED (non-vacuity of `binaryKummerAt`, `G = 1`). Over `ℚ`, for every `S`, every `v ∈ S` and
every coefficient ring `A`, with `h_0 = 1`, `α = χ_1` read in `A^×`, `E_1` and `N = 2`, the binary
Kummer condition for the trivial group exists and is a subcomplex. -/
theorem binaryKummerAt_nonvacuous_trivial (A : Type) [CommRing A]
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (v : Places ℚ S) :
    ∃ c : CondAt ℚ S (MonoidAlgebra A Unit)
        (CoefMod (MonoidAlgebra A Unit) (binaryAlpha A Unit ((intUnitsTo A).comp
          (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero)) 1)
          (TorsS ℚ S (curveEll (1 : ℚ)) ((2 ^ 1 : ℕ) : ℤ))) v,
      c.IsInjective := by
  have := isElliptic_curveEll (K := ℚ) one_ne_zero
  exact ⟨_, binaryKummerAt_isInjective A Unit (curveEll 1) (2 ^ 1) 1 (one_sq_KS S) one_ne_zero
    ((intUnitsTo A).comp (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero)) 1
    (fullTorsion_curveEll_one S) v (isLocallyQuadAtGen_intUnitsTo A _ v.1) (fun _ => rfl)⟩

/-- PROVED (non-vacuity of `binaryKummerAt` and of the local squareclass hypothesis,
`G = {±1}`). Over `ℚ`, with the universal character of the one-element family `d = 1` (square root
`1`), which is trivial on every decomposition group by `binaryUnivChar_locMap` (`1` is a square in
every `ℚ_v`), the binary Kummer condition over `A[{±1}]` exists and is a subcomplex. -/
theorem binaryKummerAt_nonvacuous_sign (A : Type) [CommRing A]
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (v : Places ℚ S) :
    ∃ c : CondAt ℚ S (MonoidAlgebra A (Unit → ℤˣ))
        (CoefMod (MonoidAlgebra A (Unit → ℤˣ)) (binaryAlpha A (Unit → ℤˣ) ((intUnitsTo A).comp
          (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero))
          (binaryUnivChar (fun _ : Unit => (1 : KS ℚ S)) (d := fun _ => 1)
            (fun _ => one_sq_KS S) (fun _ => one_ne_zero)))
          (TorsS ℚ S (curveEll (1 : ℚ)) ((2 ^ 1 : ℕ) : ℤ))) v,
      c.IsInjective := by
  have := isElliptic_curveEll (K := ℚ) one_ne_zero
  exact ⟨_, binaryKummerAt_isInjective A (Unit → ℤˣ) (curveEll 1) (2 ^ 1) 1 (one_sq_KS S)
    one_ne_zero ((intUnitsTo A).comp (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero))
    (binaryUnivChar (fun _ : Unit => (1 : KS ℚ S)) (d := fun _ => 1) (fun _ => one_sq_KS S)
      (fun _ => one_ne_zero))
    (fullTorsion_curveEll_one S) v (isLocallyQuadAtGen_intUnitsTo A _ v.1)
    (binaryUnivChar_locMap _ _ _ v.1 fun _ => by rw [map_one]; exact IsSquare.one)⟩

end NonVacuity

end ZInQ.Manuscript.RC.KummerMaps
