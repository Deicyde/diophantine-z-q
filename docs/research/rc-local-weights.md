# Appendix F local Schwartz weights

**Result and scoped stop.** The split, Eichler, dyadic, and nilpotent weights are defined on concrete 2×2 p-adic matrix models. Their finite precision, compact open support, and unit transformation rules are proved on the ambient trace-zero spaces. At the division prime, the same results and the uniformizer sign are proved from the stated maximal-order coordinates. The missing construction is an inhabitant of that division model at p = ℓ₀, plus its identification with the completed order. The finite product gives the two rules at tex 8571–8577. For the actual valuation ring of the character field at a place above two, (2ᴹ) contracts to (2ᴹ) in the integers; `coefficientRing_two` supplies `ThetaSide.ring_two`.

The local weights, the coefficient field, and the norm and scaling characters are independent of M. The product is evaluated at a tuple of local coordinates, which may be the images of a single global vector. The local compactness results prepare `ThetaStage.finite_supp`; they do not by themselves give finiteness on a rational norm sphere. The subsequent join must translate by the class representatives, handle the good-prime integrality conditions, and use definiteness and the resulting rational lattice. Likewise the local norm rule prepares `ThetaStage.f_conj`: after translation the definite order units have reduced norm 1. These data prepare the ELLIOT input about weights in the theta comparison. The join, `P_M`, and the transformation law are outside this work.

## Exact interface to the order construction

- **Split (`SplitCoordinates`, `SplitIdentification`).** For the completed order `R` and algebra `B`, supply `incl : R →+* B`, an `ℤ_[p]`-algebra equivalence from `R` to `eichler p e` and a `ℚ_[p]`-algebra equivalence from `B` to `Mat ℚ_[p]`. They must commute with `incl` and the entrywise inclusion of integral matrices. In these coordinates the images have trace `tr x` and determinant `nrd x`, respectively, for the given reduced trace and norm on `B`. The specified cyclic-quotient action `quotientAction : R →+* ZMod (p ^ e)` must equal `level p e (order x)` at every `x`. That map is lower-right entry reduction; its module is the quotient of the column lattice by `ℤ_p e₀ + p^e ℤ_p e₁`. At level zero the order is the full matrix ring and the quotient is zero. Use e = vₚ(N) at all level primes and e = 0 at the other split primes.
- **Division (`DivisionCoordinates`, `DivisionLocalModel`, `DivisionIdentification`).** Supply a Hausdorff `DivisionRing D` with compatible `ℚ_[p]`- and `ℤ_[p]`-algebra structures and rank four over `ℚ_[p]`. Supply a compact open finite `ℤ_[p]`-subalgebra `order` maximal among finite subalgebras containing it; a continuous `ℚ_[p]`-linear reduced trace `tr` invariant under inverse conjugation; and a multiplicative reduced norm `nrd` whose restriction to order units lands in `ℤ_[p]ˣ` via the given homomorphism. Supply a surjective locally constant ring map `red : order →+* GaloisField p 2`, taking scalars to their ordinary reductions and killing exactly the nonunits. Give a nonzero `beta` with `beta ^ p = -beta`; every trace-zero order element must reduce to `algebraMap (ZMod p) (GaloisField p 2) t * beta` for some `t`. Give `uniformizer : Dˣ` whose norm has valuation one and whose inverse conjugation restricts to an order ring equivalence with residue action a ↦ aᵖ. For the completed `R` and `B` and their inclusion, supply the order and algebra isomorphisms, commuting with inclusion and preserving trace and norm on `B`. The sign uses ℓ₀ ≡ 3 (mod 4).

The smallest missing local theorem provides `C : DivisionCoordinates p D` and `DivisionLocalModel C` as above. One route is the unramified quadratic extension L/ℚₚ and the algebra L ⊕ LΠ, where Π² = p and Πa = Frob(a)Π. It needs the norm valuation calculation exhibiting a division algebra, the maximal order 𝒪_L ⊕ 𝒪_LΠ with residue algebra and topology, and the trace and norm formulas. This is a local algebra construction plus the separate identification with the given completion. No new print or axiom stands in for either. An inhabitant of the interface already instantiates the residue weight, the unit scaling and conjugation rules, compact open support, and the uniformizer sign in Lean.

## Weights and tree inputs

| Model | Weight and uniform precision | Prepares |
| --- | --- | --- |
| Good split prime | `goodWeight` is the characteristic function of integral trace-zero matrices. Integral trace-zero translations are periods. | `ThetaStage.f`, `f_conj`, `finite_supp` |
| Positive odd level | `levelSchwartz` uses y = (1+x)/2. Hensel lifts the root of T² − T + det y selected by the quotient, and the weight is αₚ(2a−1). Modulo pᵏ in y suffices for a character modulo pᵏ. For the residue-field characters k = 1. | `ThetaStage.f`, `f_conj`, `finite_supp` |
| Two | At positive level, use the same root selection and a character modulo four in the affine coordinate. Without level the dyadic support remains and has weight 1; reduction of y modulo two suffices. The period in the ambient variable is twice the respective congruence lattice in y. | `ThetaStage.f`, `f_conj`, `finite_supp` |
| p ∣ m | `nilSchwartz` has determinant valuation one and is weighted by the determinant character of a basis conjugating X₀ to the nonzero nilpotent reduction. Modulo p² suffices. | `ThetaStage.f`, `f_conj`, `finite_supp` |
| ℓ₀ | `divisionSchwartz` is zero off the order and at zero reduction. On tβ it is (t/ℓ₀). The reduction modulo the maximal ideal suffices; the scalar p times the order is already in the kernel. | `ThetaStage.f`, `f_conj`, `finite_supp` |
| Coefficients | For the field generated by the fixed values, choose a place containing 2 and take its valuation subring in the field. Character values lift as units. | `ThetaSide.ring_two`; the coefficient type of `ThetaStage.f` |

For αₚ(−1), the parity input is s = w_{pᵉ} χ_{h_*}(p)ᵉ ∈ {1, −1}. The two existence theorems realize either such value, with the residue character pulled back along units reduction. The finite product uses `goodRule`, `levelRule`, `dyadicRule`, `nilRule`, and `DivisionCoordinates.divisionRule`. The only nontrivial norm characters of order units are the Legendre factors at p ∣ m. `negativeDiscriminant_unit_character` verifies their identification with the character of −m on odd positive integer representatives by quadratic reciprocity. For local unit tuples their residues admit such representatives by CRT. The prior proof of α(−1) = 1 lives in the existing root-number lane.

## Known issues

- The task shorthand r ↦ ur belongs to scalar unit multiplication; order-unit conjugation fixes the selected root. Tex 8512–8515 says this correctly.
- The Voight citation at tex 8462 (Main Theorem 14.6.1) and the Jetchev–Kane section citations at tex 8474 are **UNVERIFIED** here. They are not used as prints. No source or manuscript error was identified in the steps checked here.
- The division model has the explicit open construction obligation above. Its formal weights are conditional on those coordinates, and the report makes no assertion that the completed order has already been identified with them.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8462–8465 | unverified | Global quaternion ramification and the global order are supplied at the join; the local interface records what is needed. |
| 8466–8474 | unverified | Class-set, automorphism and geometric identifications are outside this work. |
| 8496 | OK | Extend by zero from the stated lattices; the compact open and transformation lemmas include the zero branch. |
| 8497 | OK | Q_B = −x² is already in `Visibility.Theta`; split coordinates use determinant and trace. |
| 8498 | OK | Integral trace zero is the good-prime support. |
| 8499–8502 | gap filled | Described the cyclic quotient in coordinates and proved the selected integral projector acts as identity on it. |
| 8502–8504 | gap filled | Hensel on T² − T + det y with a unit derivative, followed by the congruence of roots on a fixed residue branch. |
| 8505–8511 | OK | The cyclic odd-part power followed by an isomorphism of cyclic groups realizes the required parity. |
| 8512–8515 | OK | Conjugation fixes the selected root; unit scaling changes it by that unit. |
| 8517–8520 | OK | The affine support is equivalent to the given unit-square condition, and the integral projectors remain distinct modulo two. |
| 8521–8525 | gap filled | On the cyclic quotient the selected projector acts as one and its complement as zero. |
| 8525–8531 | OK | The integral offset exists and affine scaling preserves each projector. |
| 8532–8534 | OK | Trivial and mod-four characters give the two parities; no character at dyadic level zero. |
| 8536–8539 | gap filled | Exact divisibility equals valuation one, the reduction is nonzero, and a basis is obtained from (Xeᵢ, eᵢ). |
| 8540–8545 | OK | Use `Odd.quadraticChar_det_eq_of_conj` and the centralizer calculation already in the tree. |
| 8546–8549 | OK | Apply the basis determinant rule for conjugation and `Odd.diag_conj_X0` for scaling. |
| 8551–8554 | gap filled | The residue-line weight is well-defined and order units act trivially after commutative reduction; the maximal-order identification is a model input. |
| 8554–8556 | OK | Given Frobenius on reduction and βᵖ = −β, the sign and scaling follow from the quadratic character. |
| 8556–8561 | gap filled | Reduce the integral representative of the norm as the scalar −x². The nonsquare and extraction algebra is already in `Odd.trace_zero_sq_not_square` and `Odd.legendre_extracted`. |
| 8563–8564 | gap filled | Uniform congruence and compact open support are proved on the ambient trace-zero spaces; the division case uses the stated model. |
| 8564–8566 | OK | The squareclass adapter preserves both transformation rules and compact open support under the locally constant norm test. |
| 8567–8570 | gap filled | Identify the field generated by the values as cyclotomic of two-power conductor parameter, choose a place above two, and prove the integer contraction. |
| 8571–8577 | gap filled | Multiply the local rules on a finite index set; identify the ramified unit factors by quadratic reciprocity. |
| 8579–8592 | OK | Already proved in `Odd.ThetaLocal` and `GlueSweep.OddRootNumber`; no new sign proof here. |

The supplemental coordinate algebra, fixed-precision arguments, topology, reciprocity identification and ideal contraction are on-the-spot (provenance (c)). No printed-form leaves were added.

All 18 modules compile individually with `lake env lean`. The 118 theorem checks and six additional rule checks report only `propext`, `Classical.choice`, and `Quot.sound`.

## Theorem statements and dependencies

The source statements below inherit their implicit parameters and notation from the indicated module. Each listed theorem has a corresponding `#print axioms` in its module.

### [Models.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Models.lean)

ThetaStage.f and ThetaStage.finite_supp: the cyclic quotient, reduction and the good-prime period.

```lean
@[simp] theorem eichler_zero : eichler p 0 = ⊤

theorem level_mulVec (e : ℕ) (x : eichler p e) (v : Fin 2 → ℤ_[p]) :
    PadicInt.toZModPow e (x.val.mulVec v 1) =
      level p e x * PadicInt.toZModPow e (v 1)

theorem level_coordinate (e : ℕ) :
    Function.Surjective (fun v : Fin 2 → ℤ_[p] => PadicInt.toZModPow e (v 1)) ∧
      ∀ v : Fin 2 → ℤ_[p], PadicInt.toZModPow e (v 1) = 0 ↔ (p : ℤ_[p]) ^ e ∣ v 1

theorem goodWeight_congr {O : Type*} [Zero O] [One O] (x y : TraceZero ℚ_[p])
    (h : ∀ i j, x.val i j - y.val i j ∈ PadicInt.subring p) :
    goodWeight p x = (goodWeight p y : O)

theorem red_eq_iff (k : ℕ) (a b : ℤ_[p]) :
    PadicInt.toZModPow k a = PadicInt.toZModPow k b ↔ (p : ℤ_[p]) ^ k ∣ a - b

theorem red_locallyConstant (k : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow k : ℤ_[p] → ZMod (p ^ k))

theorem redMat_locallyConstant (k : ℕ) : IsLocallyConstant (redMat p k)
```

### [Characters.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Characters.lean)

ThetaStage.f: realizability of the prescribed local parity (O.3).

```lean
theorem odd_character_exists {p k m : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [IsDomain O] {ζ : O} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hp : p ≠ 2) (hcard : Nat.card (ZMod p)ˣ = 2 ^ k * m) (hm : Odd m)
    (s : Oˣ) (hs : s = 1 ∨ s = -1) :
    ∃ α : (ZMod p)ˣ →* Oˣ, α (-1) = s ∧ ∀ u, α u ^ (2 ^ k) = 1

theorem odd_character_complex {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (s : ℂˣ) (hs : s = 1 ∨ s = -1) :
    ∃ k : ℕ, ∃ α : (ZMod p)ˣ →* ℂˣ, α (-1) = s ∧ ∀ u, α u ^ (2 ^ k) = 1

theorem dyadic_character_exists {O : Type*} [CommRing O]
    (s : Oˣ) (hs : s = 1 ∨ s = -1) :
    ∃ α : (ZMod 4)ˣ →* Oˣ, α (-1) = s ∧ ∀ u, α u ^ 2 = 1
```

### [Compact.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Compact.lean)

ThetaStage.finite_supp: compact open ambient supports from finite tests in a chart.

```lean
theorem locallyConstant_of_factors {X Y Z : Type*} [TopologicalSpace X]
    {g : X → Y} {f : X → Z} (hg : IsLocallyConstant g)
    (h : ∀ x y, g x = g y → f x = f y) : IsLocallyConstant f

theorem compactOpen_support {X O : Type*} [TopologicalSpace X] [CompactSpace X]
    [Zero O] {f : X → O} (hf : IsLocallyConstant f) :
    IsCompact (support f) ∧ IsOpen (support f)

theorem extendWeight_spec {X A O : Type*} [Zero O] (i : A → X) (f : A → O)
    (hi : Function.Injective i) :
    (∀ a, extendWeight i f (i a) = f a) ∧
      (∀ x ∉ Set.range i, extendWeight i f x = 0)

theorem extendWeight_compactOpen {X A O : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [CompactSpace A] [Zero O] {i : A → X} {f : A → O}
    (hi : IsOpenEmbedding i) (hf : IsLocallyConstant f) :
    IsLocallyConstant (extendWeight i f) ∧ IsCompact (support (extendWeight i f)) ∧
    IsOpen (support (extendWeight i f))

theorem goodWeight_compactOpen {O : Type*} [Zero O] [One O] [Nontrivial O]
    (h : (1 : O) ≠ 0) :
    IsLocallyConstant (goodWeight p : TraceZero ℚ_[p] → O) ∧
      IsCompact (support (goodWeight p : TraceZero ℚ_[p] → O)) ∧
      IsOpen (support (goodWeight p : TraceZero ℚ_[p] → O))
```

### [Level.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Level.lean)

ThetaStage.f and ThetaStage.f_conj: existence, uniqueness and conjugation of the selected branch.

```lean
theorem unit_iff_red_ne_zero (a : ℤ_[p]) : IsUnit a ↔ red 1 a ≠ 0

theorem branch_congr (k : ℕ) {a b d d' : ℤ_[p]} (ha : a ^ 2 - a + d = 0)
    (hb : b ^ 2 - b + d' = 0) (hu : IsUnit (2 * a - 1))
    (hab : red 1 a = red 1 b) (hd : red k d = red k d') :
    red k a = red k b

theorem lift_branch {a d : ℤ_[p]} (hu : IsUnit (2 * a - 1))
    (h : red 1 (a ^ 2 - a + d) = 0) :
    ∃ b : ℤ_[p], b ^ 2 - b + d = 0 ∧ red 1 b = red 1 a ∧ IsUnit (2 * b - 1)

theorem level_residue_root {e : ℕ} (y : eichler p e) (ht : y.val.trace = 1) :
    red e ((y.val 1 1) ^ 2 - y.val 1 1 + y.val.det) = 0

theorem levelRoot_existsUnique {e : ℕ} (he : 0 < e) (y : eichler p e)
    (ht : y.val.trace = 1) :
    (∃! a, LevelRoot y a) ↔ IsUnit (2 * y.val 1 1 - 1)

theorem levelRoot_conj {e : ℕ} (u : (eichler p e)ˣ) (y : eichler p e) (a : ℤ_[p]) :
    LevelRoot ((↑u⁻¹ : eichler p e) * y * (↑u : eichler p e)) a ↔ LevelRoot y a

theorem levelWeight_eq {O : Type*} [CommRing O] {e : ℕ} (he : 0 < e)
    (χ : ℤ_[p]ˣ →* Oˣ) {y : eichler p e} (ht : y.val.trace = 1)
    {a : ℤ_[p]} (ha : LevelRoot y a) :
    levelWeight χ y = (χ ha.2.1.unit : O)
```

### [LevelRules.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/LevelRules.lean)

ThetaStage.f, ThetaStage.f_conj and ThetaStage.finite_supp: local scaling, conjugation and finite precision.

```lean
theorem levelRoot_congr {y z : eichler p e} {a b : ℤ_[p]} (ha : LevelRoot y a)
    (hb : LevelRoot z b) (he : 0 < e) {k : ℕ} (hk : 0 < k)
    (h : redMat p k y.val = redMat p k z.val) : red k a = red k b

theorem levelWeight_congr (he : 0 < e) {k : ℕ} (hk : 0 < k)
    (χ : (ZMod (p ^ k))ˣ →* Oˣ) {y z : eichler p e}
    (hy : y.val.trace = 1) (hz : z.val.trace = 1)
    (h : redMat p k y.val = redMat p k z.val) :
    levelWeight (χ.comp (Units.map (red k).toMonoidHom)) y =
      levelWeight (χ.comp (Units.map (red k).toMonoidHom)) z

theorem levelWeight_conj (he : 0 < e) (χ : ℤ_[p]ˣ →* Oˣ)
    (u : (eichler p e)ˣ) (y : eichler p e) :
    levelWeight χ ((↑u⁻¹ : eichler p e) * y * (↑u : eichler p e)) = levelWeight χ y

theorem affine_offset (v : ℤ_[p]ˣ) : ∃ t : ℤ_[p], (2 : ℤ_[p]) * t = 1 - v.val

theorem affine_trace (v t : ℤ_[p]) (hv : 2 * t = 1 - v) (y : eichler p e)
    (hy : y.val.trace = 1) : (affine v t y).val.trace = 1

theorem affine_det (v t : ℤ_[p]) {y : eichler p e} (hy : y.val.trace = 1) :
    (affine v t y).val.det = v ^ 2 * y.val.det + v * t + t ^ 2

theorem affine_root (v : ℤ_[p]ˣ) (t : ℤ_[p]) (hv : 2 * t = 1 - v.val)
    {y : eichler p e} (hy : y.val.trace = 1)
    {a : ℤ_[p]} (ha : LevelRoot y a) :
    LevelRoot (affine v.val t y) (v.val * a + t)

theorem levelWeight_scale (he : 0 < e) (χ : ℤ_[p]ˣ →* Oˣ)
    (v : ℤ_[p]ˣ) (t : ℤ_[p]) (hv : 2 * t = 1 - v.val)
    (y : eichler p e) (hy : y.val.trace = 1) :
    levelWeight χ (affine v.val t y) = (χ v : O) * levelWeight χ y

theorem levelWeight_locallyConstant (he : 0 < e) {k : ℕ} (hk : 0 < k)
    (χ : (ZMod (p ^ k))ˣ →* Oˣ) :
    IsLocallyConstant (fun (y : {y : eichler p e // y.val.trace = 1}) =>
      levelWeight (χ.comp (Units.map (red k).toMonoidHom)) y.val)
```

### [LevelSupport.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/LevelSupport.lean)

ThetaStage.f: the exact support and eigensummand in the cyclic quotient.

```lean
theorem odd_integral_half (hp : p ≠ 2) (x : eichler p e) (hx : x.val.trace = 0) :
    ∃! y : eichler p e, y.val.trace = 1 ∧ (2 : ℤ_[p]) • y - 1 = x

theorem splitSupport_selected (he : 0 < e) (y : eichler p e) (hy : y.val.trace = 1) :
    SplitSupport y ↔ ∃ a, LevelRoot y a

theorem affine_square (y : eichler p e) (hy : y.val.trace = 1) :
    ((2 : ℤ_[p]) • y.val - 1) ^ 2 =
      algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - 4 * y.val.det)

theorem projector_numerator (y : eichler p e) (hy : y.val.trace = 1)
    (a : ℤ_[p]) (ha : a ^ 2 - a + y.val.det = 0) :
    let z := y.val - algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - a)
    z * z = (2 * a - 1) • z

theorem projector_idempotent (y : eichler p e) (hy : y.val.trace = 1)
    {a : ℤ_[p]} (ha : a ^ 2 - a + y.val.det = 0) (u : IsUnit (2 * a - 1)) :
    projector u y * projector u y = projector u y

theorem projector_eigen (y : eichler p e) (hy : y.val.trace = 1)
    {a : ℤ_[p]} (ha : a ^ 2 - a + y.val.det = 0) (u : IsUnit (2 * a - 1)) :
    y * projector u y = a • projector u y

theorem level_scalar (e : ℕ) (a : ℤ_[p]) :
    level p e (algebraMap ℤ_[p] (eichler p e) a) = red e a

theorem projector_level (y : eichler p e) {a : ℤ_[p]} (ha : LevelRoot y a) :
    level p e (projector ha.2.1 y) = 1 ∧
      level p e (1 - projector ha.2.1 y) = 0

theorem projector_affine (v : ℤ_[p]ˣ) (t : ℤ_[p]) (hv : 2 * t = 1 - v.val)
    {y : eichler p e} (hy : y.val.trace = 1) {a : ℤ_[p]} (ha : LevelRoot y a) :
    projector (affine_root v t hv hy ha).2.1 (affine v.val t y) = projector ha.2.1 y

theorem splitSupport_square (y : eichler p e) (hy : y.val.trace = 1) :
    SplitSupport y ↔ ∃ r : ℤ_[p]ˣ, ((2 : ℤ_[p]) • y.val - 1) ^ 2 =
      algebraMap ℤ_[p] (Mat ℤ_[p]) (r.val ^ 2)

theorem levelWeight_nonzero_iff {O : Type*} [CommRing O] [Nontrivial O]
    (he : 0 < e) (χ : ℤ_[p]ˣ →* Oˣ) (y : eichler p e) (hy : y.val.trace = 1) :
    levelWeight χ y ≠ 0 ↔ SplitSupport y
```

### [Dyadic.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Dyadic.lean)

ThetaStage.f, ThetaStage.f_conj and ThetaStage.finite_supp: the exact unweighted dyadic function and its rules.

```lean
theorem dyadicUnit_red (v : ℤ_[2]ˣ) : red₂ v.val = 1

theorem dyadic_projectors_distinct {e : ℕ} (P : eichler 2 e) :
    redMat 2 1 P.val ≠ redMat 2 1 (1 - P).val

theorem dyadic_split_iff {e : ℕ} (y : eichler 2 e) :
    SplitSupport y ↔ red₂ y.val.det = 0

theorem dyadicWeight_congr {O : Type*} [Zero O] [One O] (y z : eichler 2 0)
    (h : redMat 2 1 y.val = redMat 2 1 z.val) :
    (dyadicWeight y : O) = dyadicWeight z

theorem dyadicWeight_conj {O : Type*} [Zero O] [One O] (u : (eichler 2 0)ˣ) (y : eichler 2 0) :
    dyadicWeight ((↑u⁻¹ : eichler 2 0) * y * (↑u : eichler 2 0)) = (dyadicWeight y : O)

theorem dyadicWeight_scale {O : Type*} [Zero O] [One O] (v : ℤ_[2]ˣ) (t : ℤ_[2])
    (y : AffineOrder 2 0) : dyadicWeight (affine v.val t y.val) = (dyadicWeight y.val : O)

theorem dyadicSchwartz_compactOpen {O : Type*} [Zero O] [One O] :
    IsLocallyConstant (dyadicSchwartz : TraceZero ℚ_[2] → O) ∧
      IsCompact (Function.support (dyadicSchwartz : TraceZero ℚ_[2] → O)) ∧
      IsOpen (Function.support (dyadicSchwartz : TraceZero ℚ_[2] → O))
```

### [Nilpotent.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Nilpotent.lean)

ThetaStage.f and ThetaStage.f_conj: the determinant sign and its independence of basis.

```lean
theorem nilBasis_exists (A : Mat F) (ht : A.trace = 0) (hd : A.det = 0) (hn : A ≠ 0) :
    ∃ g : GL (Fin 2) F, NilBasis A g

theorem nilBasis_sign_eq {A : Mat F} {g h : GL (Fin 2) F}
    (hg : NilBasis A g) (hh : NilBasis A h) :
    quadraticChar F (g : Mat F).det = quadraticChar F (h : Mat F).det

theorem nilSign_of_basis {A : Mat F} {g : GL (Fin 2) F} (hg : NilBasis A g) :
    nilSign A = quadraticChar F (g : Mat F).det

theorem nilSign_conj (u : GL (Fin 2) F) (A : Mat F) :
    nilSign ((↑u⁻¹ : Mat F) * A * (u : Mat F)) =
      quadraticChar F (u : Mat F).det * nilSign A

theorem nilSign_scale (v : Fˣ) (A : Mat F) :
    nilSign ((v : F) • A) = quadraticChar F (v : F) * nilSign A

theorem nilSupport_reduction (x : TraceZero ℤ_[p]) (hx : NilSupport p x) :
    let A := x.val.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
    A.trace = 0 ∧ A.det = 0 ∧ A ≠ 0
```

### [NilpotentRules.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/NilpotentRules.lean)

ThetaStage.f, ThetaStage.f_conj and ThetaStage.finite_supp: the exact valuation condition, rules and precision.

```lean
theorem nilSupport_valuation (x : TraceZero ℤ_[p]) :
    NilSupport p x ↔ x.val.det.valuation = 1

theorem nilWeight_nonzero_iff {O : Type*} [Ring O] [Nontrivial O]
    (x : TraceZero ℤ_[p]) : (nilWeight p x : O) ≠ 0 ↔ NilSupport p x

theorem nilWeight_conj {O : Type*} [Ring O] (u : GL (Fin 2) ℤ_[p]) (x : TraceZero ℤ_[p]) :
    nilWeight p ⟨(↑u⁻¹ : Mat ℤ_[p]) * x.val * (u : Mat ℤ_[p]),
      (Matrix.trace_units_conj' u x.val).trans x.property⟩ =
      (quadraticChar (ZMod p) (res (u : Mat ℤ_[p]).det) : O) * nilWeight p x

theorem nilWeight_scale {O : Type*} [Ring O] (v : ℤ_[p]ˣ) (x : TraceZero ℤ_[p]) :
    nilWeight p ⟨v.val • x.val, by rw [Matrix.trace_smul, x.property, smul_zero]⟩ =
      (quadraticChar (ZMod p) (res v.val) : O) * nilWeight p x

theorem nilWeight_congr {O : Type*} [Ring O] (x y : TraceZero ℤ_[p])
    (h : redMat p 2 x.val = redMat p 2 y.val) : (nilWeight p x : O) = nilWeight p y

theorem nilWeight_compactOpen {O : Type*} [Ring O] :
    IsLocallyConstant (nilWeight p : TraceZero ℤ_[p] → O) ∧
      IsCompact (Function.support (nilWeight p : TraceZero ℤ_[p] → O)) ∧
      IsOpen (Function.support (nilWeight p : TraceZero ℤ_[p] → O))
```

### [SplitAmbient.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/SplitAmbient.lean)

ThetaStage.f and ThetaStage.finite_supp: compact open charts and the ambient supports.

```lean
theorem openEmbedding_restrictPreimage {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {i : A → B} (hi : IsOpenEmbedding i) (s : Set B) :
    IsOpenEmbedding (s.restrictPreimage i)

theorem integralMat_openEmbedding : IsOpenEmbedding (integralMat p)

theorem integralMat_trace (x : Mat ℤ_[p]) : (integralMat p x).trace = (x.trace : ℚ_[p])

theorem integralZero_openEmbedding : IsOpenEmbedding (integralZero p)

theorem traceZero_compactSpace : CompactSpace (TraceZero ℤ_[p])

theorem nilSchwartz_compactOpen {O : Type*} [Ring O] :
    IsLocallyConstant (nilSchwartz p : TraceZero ℚ_[p] → O) ∧
      IsCompact (Function.support (nilSchwartz p : TraceZero ℚ_[p] → O)) ∧
      IsOpen (Function.support (nilSchwartz p : TraceZero ℚ_[p] → O))

theorem eichler_openEmbedding (e : ℕ) :
    IsOpenEmbedding (fun y : eichler p e => integralMat p y.val)

theorem eichler_compactSpace (e : ℕ) : CompactSpace (eichler p e)

theorem affineInclusion_trace_iff {e : ℕ} (y : eichler p e) :
    (affineInclusion p y).trace = 0 ↔ y.val.trace = 1

theorem affineZero_openEmbedding (e : ℕ) : IsOpenEmbedding (affineZero p (e := e))

theorem affineOrder_compactSpace (e : ℕ) : CompactSpace (AffineOrder p e)

theorem levelSchwartz_compactOpen {O : Type*} [CommRing O] {e k : ℕ}
    (he : 0 < e) (hk : 0 < k) (χ : (ZMod (p ^ k))ˣ →* Oˣ) :
    IsLocallyConstant (levelSchwartz p (e := e) χ) ∧
      IsCompact (Function.support (levelSchwartz p (e := e) χ)) ∧
      IsOpen (Function.support (levelSchwartz p (e := e) χ))
```

### [Transport.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Transport.lean)

ThetaStage.f_conj: transformation rules including zero branches outside the integral chart.

```lean
theorem extendWeight_transform {X A O : Type*} [MulZeroClass O]
    (i : A → X) (hi : Function.Injective i) (f : A → O) (c : O)
    (g : X → X) (v : A → A) (g' : X → X) (v' : A → A)
    (hg : Function.LeftInverse g' g)
    (h : ∀ a, g (i a) = i (v a)) (h' : ∀ a, g' (i a) = i (v' a))
    (hf : ∀ a, f (v a) = c * f a) (x : X) :
    extendWeight i f (g x) = c * extendWeight i f x
```

### [SplitActions.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/SplitActions.lean)

ThetaStage.f_conj: the actual inverse conjugation and scaling actions on split models.

```lean
theorem matrixConj_inverse (u : (Mat A)ˣ) :
    Function.LeftInverse (matrixConj u⁻¹) (matrixConj u)

theorem matrixScale_inverse (v : Aˣ) :
    Function.LeftInverse (matrixScale v⁻¹) (matrixScale v)

theorem integralMat_smul (a : ℤ_[p]) (x : Mat ℤ_[p]) :
    integralMat p (a • x) = (a : ℚ_[p]) • integralMat p x

theorem integralMat_scalar (a : ℤ_[p]) :
    integralMat p (algebraMap ℤ_[p] (Mat ℤ_[p]) a) = (a : ℚ_[p]) • (1 : Mat ℚ_[p])

theorem integralZero_conj (u : (Mat ℤ_[p])ˣ) (x : TraceZero ℤ_[p]) :
    matrixConj (Units.map (integralMat p).toMonoidHom u) (integralZero p x) =
      integralZero p (matrixConj u x)

theorem integralZero_scale (v : ℤ_[p]ˣ) (x : TraceZero ℤ_[p]) :
    matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v) (integralZero p x) =
      integralZero p (matrixScale v x)

theorem goodWeight_extend :
    (goodWeight p : TraceZero ℚ_[p] → O) = extendWeight (integralZero p) (fun _ => 1)

theorem affineZero_conj (u : (eichler p e)ˣ) (y : AffineOrder p e) :
    matrixConj (Units.map (integralMat p).toMonoidHom (eichlerUnit u)) (affineZero p y) =
      affineZero p (affineConj u y)

theorem affineZero_scale (v : ℤ_[p]ˣ) (y : AffineOrder p e) :
    matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v) (affineZero p y) =
      affineZero p (affineScale v y)
```

### [Division.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Division.lean)

ThetaStage.f, ThetaStage.f_conj and ThetaStage.finite_supp: the residue-line weight, its sign and norm residue.

```lean
private theorem coordinate_injective :
    Function.Injective (fun t : ZMod p =>
      algebraMap (ZMod p) (GaloisField p 2) t * C.beta)

theorem residueWeight_eq {O : Type*} [Ring O] (t : ZMod p) :
    C.residueWeight (algebraMap (ZMod p) (GaloisField p 2) t * C.beta) =
      (quadraticChar (ZMod p) t : O)

theorem divisionWeight_nonzero_iff {O : Type*} [Ring O] [Nontrivial O]
    (x : C.order) (hx : C.tr x.val = 0) : (C.divisionWeight x : O) ≠ 0 ↔ C.red x ≠ 0

theorem norm_residue_of_trace_zero (x : C.order) (hx : C.tr x.val = 0) (a : ℤ_[p])
    (ha : algebraMap ℤ_[p] D a = -(x.val ^ 2)) :
    ∃ t : ZMod p, C.red x = algebraMap (ZMod p) (GaloisField p 2) t * C.beta ∧
      algebraMap (ZMod p) (GaloisField p 2) (PadicInt.toZMod a) =
        -(algebraMap (ZMod p) (GaloisField p 2) t * C.beta) ^ 2

theorem divisionWeight_locallyConstant {O : Type*} [Ring O] :
    IsLocallyConstant (C.divisionWeight : C.order → O)

theorem divisionWeight_conj {O : Type*} [Ring O] (u : C.orderˣ) (x : C.order) :
    C.divisionWeight ((↑u⁻¹ : C.order) * x * ↑u) = (C.divisionWeight x : O)

theorem divisionWeight_scale {O : Type*} [Ring O] (x : C.order) (hx : C.tr x.val = 0)
    (v : ℤ_[p]ˣ) :
    C.divisionWeight (algebraMap ℤ_[p] C.order v.val * x) =
      (quadraticChar (ZMod p) (PadicInt.toZMod v.val) : O) * C.divisionWeight x

theorem divisionWeight_uniformizer {O : Type*} [Ring O] (x : C.order)
    (hx : C.tr x.val = 0) (hp : p % 4 = 3) :
    C.divisionWeight (C.uniformizer_order x) = -(C.divisionWeight x : O)
```

### [DivisionAmbient.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/DivisionAmbient.lean)

ThetaStage.f_conj and ThetaStage.finite_supp: the division-prime ambient rules and support, conditional on the local model.

```lean
theorem zeroInclusion_openEmbedding : IsOpenEmbedding C.zeroInclusion

theorem integralZero_compactSpace : CompactSpace C.IntegralZero

theorem divisionSchwartz_compactOpen {O : Type*} [Ring O] [T2Space D] :
    IsLocallyConstant (C.divisionSchwartz : C.RationalZero → O) ∧
      IsCompact (Function.support (C.divisionSchwartz : C.RationalZero → O)) ∧
      IsOpen (Function.support (C.divisionSchwartz : C.RationalZero → O))

theorem conjZero_inverse (u : Dˣ) : Function.LeftInverse (C.conjZero H u⁻¹) (C.conjZero H u)

theorem scaleZero_inverse (v : ℚ_[p]ˣ) :
    Function.LeftInverse (C.scaleZero v⁻¹) (C.scaleZero v)

theorem scaleZero_inclusion (v : ℤ_[p]ˣ) (x : C.IntegralZero) :
    C.scaleZero (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v) (C.zeroInclusion x) =
      C.zeroInclusion (C.scaleOrder H v x)

theorem divisionSchwartz_uniformizer {O : Type*} [Ring O] (hp : p % 4 = 3)
    (x : C.RationalZero) :
    C.divisionSchwartz (C.conjZero H C.uniformizer x) = -(C.divisionSchwartz x : O)
```

### [AmbientCongruence.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/AmbientCongruence.lean)

ThetaStage.finite_supp: uniform periods including outside the integral charts.

```lean
theorem extendWeight_period {X A O : Type*} [AddGroup X] [Zero O]
    (i : A → X) (hi : Function.Injective i) (f : A → O) (δ : X)
    (add sub : A → A) (hadd : ∀ a, i (add a) = i a + δ)
    (hsub : ∀ a, i (sub a) = i a - δ)
    (hf : ∀ a, f (add a) = f a) (x : X) :
    extendWeight i f (x + δ) = extendWeight i f x

theorem nilSchwartz_period {O : Type*} [Ring O] (a : TraceZero ℤ_[p])
    (ha : redMat p 2 a.val = 0) (x : TraceZero ℚ_[p]) :
    nilSchwartz p (⟨x.val + integralMat p a.val,
      by rw [Matrix.trace_add, x.property, integralMat_trace, a.property,
        PadicInt.coe_zero, add_zero]⟩) = (nilSchwartz p x : O)

theorem affineSchwartz_period {O : Type*} [Zero O] {e k : ℕ} (f : AffineOrder p e → O)
    (hf : ∀ y z, redMat p k y.val.val = redMat p k z.val.val → f y = f z)
    (a : eichler p e) (hta : a.val.trace = 0) (ha : redMat p k a.val = 0)
    (x : TraceZero ℚ_[p]) :
    extendWeight (affineZero p) f (⟨x.val + (2 : ℚ_[p]) • integralMat p a.val,
      by rw [Matrix.trace_add, x.property, Matrix.trace_smul, integralMat_trace,
        hta, PadicInt.coe_zero, smul_zero, add_zero]⟩) =
      extendWeight (affineZero p) f x

theorem levelSchwartz_chart_congr {O : Type*} [CommRing O] {e k : ℕ} (he : 0 < e) (hk : 0 < k)
    (χ : (ZMod (p ^ k))ˣ →* Oˣ) (y z : AffineOrder p e)
    (h : redMat p k y.val.val = redMat p k z.val.val) :
    levelSchwartz p (e := e) χ (affineZero p y) = levelSchwartz p (e := e) χ (affineZero p z)

theorem red_prime_mul (a : C.order) :
    C.red (algebraMap ℤ_[p] C.order (p : ℤ_[p]) * a) = 0

theorem divisionSchwartz_period {O : Type*} [Ring O] (a : C.IntegralZero)
    (ha : C.red a.val = 0) (x : C.RationalZero) :
    C.divisionSchwartz (⟨x.val + a.val.val, by rw [map_add, x.property, a.property, add_zero]⟩) =
      (C.divisionSchwartz x : O)
```

### [Product.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Product.lean)

ThetaStage.f and ThetaStage.f_conj: the finite product and the identification of its norm character.

```lean
theorem legendreUnit_apply (p : ℕ) [Fact p.Prime] (v : ℤ_[p]ˣ) :
    ((legendreUnit (O := O) p v : Oˣ) : O) =
      (quadraticChar (ZMod p) (PadicInt.toZMod v.val) : ℤ) := rfl

theorem legendreUnit_inv (p : ℕ) [Fact p.Prime] (v : ℤ_[p]ˣ) :
    (legendreUnit (O := O) p v)⁻¹ = legendreUnit p v

theorem legendreUnit_inv (p : ℕ) [Fact p.Prime] (v : ℤ_[p]ˣ) :
    (legendreUnit (O := O) p v)⁻¹ = legendreUnit p v

theorem negativeDiscriminant_unit_character (m d : ℕ) (hm : m % 4 = 3)
    (hs : Squarefree m) (hd : Odd d) :
    jacobiSym (-(m : ℤ)) d = ∏ p ∈ m.primeFactors, jacobiSym d p

theorem finiteWeight_conj (S : Finset ι) (W : ∀ i, LocalRule (O := O) (X i) (G i) (V i))
    (u : ∀ i, G i) (x : ∀ i, X i) :
    finiteWeight S W (fun i => (W i).conj (u i) (x i)) =
      (((finiteNormChar S W (fun i => (W i).norm (u i)))⁻¹ : Oˣ) : O) * finiteWeight S W x

theorem finiteWeight_scale (S : Finset ι) (W : ∀ i, LocalRule (O := O) (X i) (G i) (V i))
    (v : ∀ i, V i) (x : ∀ i, X i) :
    finiteWeight S W (fun i => (W i).scale (v i) (x i)) =
      (finiteAlpha S W v : O) * finiteWeight S W x
```

### [SquareClass.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/SquareClass.lean)

ThetaStage.f_conj and ThetaStage.finite_supp: extra fixed squareclass conditions preserve the rules and support.

```lean
theorem squareClass_compactOpen [TopologicalSpace X]
    (f : X → O) (q : X → A) (Q : Set A) [DecidablePred (· ∈ Q)]
    (hf : IsLocallyConstant f) (hc : IsCompact (Function.support f))
    (hQ : IsLocallyConstant (fun x => decide (q x ∈ Q))) :
    IsLocallyConstant (fun x => if q x ∈ Q then f x else 0) ∧
    IsCompact (Function.support (fun x => if q x ∈ Q then f x else 0)) ∧
    IsOpen (Function.support (fun x => if q x ∈ Q then f x else 0))
```

### [Coefficients.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalWeights/Coefficients.lean)

ThetaSide.ring_two and ThetaStage.f: the field, valuation ring, contraction and character lifts.

```lean
theorem ring_two_of_nonunit {O : Type*} [CommRing O] [IsDomain O] [CharZero O]
    (h₂ : ¬ IsUnit (2 : O)) (M : ℕ) (z : ℤ) :
    (2 : O) ^ M ∣ (z : O) ↔ (2 : ℤ) ^ M ∣ z

theorem coefficientRing_two (v : HeightOneSpectrum (𝓞 K))
    (hv : (2 : 𝓞 K) ∈ v.asIdeal) (M : ℕ) (z : ℤ) :
    (2 : coefficientRing K v) ^ M ∣ (z : coefficientRing K v) ↔ (2 : ℤ) ^ M ∣ z

theorem coefficientPlace_exists :
    ∃ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal

theorem primitiveRoot_integralAt (v : HeightOneSpectrum (𝓞 K)) {k : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) :
    ∃ η : coefficientRing K v, (η : K) = ζ ∧ IsPrimitiveRoot η (2 ^ k)

theorem characterField_cyclotomic {S : Set ℂ}
    (h : ∃ k : ℕ, ∀ z ∈ S, z ^ (2 ^ k) = 1) :
    ∃ k : ℕ, IsCyclotomicExtension {2 ^ k} ℚ (IntermediateField.adjoin ℚ S)

theorem characterField_numberField {S : Set ℂ}
    (h : ∃ k : ℕ, ∀ z ∈ S, z ^ (2 ^ k) = 1) :
    NumberField (IntermediateField.adjoin ℚ S)

theorem rootOfUnity_mem_coefficientRing (v : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : 0 < n) {a : K} (ha : a ^ n = 1) :
    a ∈ (v.valuation K).valuationSubring.toSubring

theorem character_lifts_to_coefficients {G : Type*} [Group G] (χ : G →* ℂˣ)
    (S : Set ℂ) (hS : ∀ u, (χ u : ℂ) ∈ S) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ u, χ u ^ n = 1) [NumberField (IntermediateField.adjoin ℚ S)]
    (v : HeightOneSpectrum (𝓞 (IntermediateField.adjoin ℚ S))) :
    ∃ χ' : G →* (coefficientRing (IntermediateField.adjoin ℚ S) v)ˣ,
      ∀ u, ((((χ' u).val : IntermediateField.adjoin ℚ S)) : ℂ) = (χ u : ℂ)
```
