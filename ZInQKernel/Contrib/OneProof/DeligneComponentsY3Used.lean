import ZInQKernel.Contrib.OneProof.RayClassShimura
import ZInQKernel.OneProof.H.TailZ40


/-!
# dcy3-used: the used form of `deligneComponentsY3PrintedAb`, proved from `shimuraMainThmIDeligneY3AbU`

Task dcy3-used (2026-11-15). Report: `docs/research/dcy3-used.md`; log: `scratch/dcy3-used/log.md`.

The added field `HDec.HSyn.OpenAddedLeaves17.deligneComponentsY3PrintedAb` (Deligne's `π₀` of `Sh_{K₃}` with its
Galois action, on one fine witness `Y₃`) is read by the chain only through `TSHecke.Y3Connected` (`TailZ13`:
`y3Connected_of_deligne ∘ deligneComponentsY3_of_printed`; consumer `heckeIrreducible_of_connected`). Its used
form is `DCY3Used.Y3ConnectedAb`: some fine witness of `R1fpPropsAb` is connected over `ℚ`.

* `DCY3Used.y3ConnectedAb_of_U : RayClassCFT.ShimuraMainThmIDeligneY3AbU → Y3ConnectedAb`, from the research
  field already in the bundle (Shimura's Main Theorem I in Deligne's adelic form on `Y₃`), with no new leaf. Only
  the uniformization `B^×_+ \ (ℍ × G(𝔸_f)) / K₃ ≃ Y(ℂ)`, the holomorphy of `τ ↦ Ψ(τ, g)` and the reciprocity law at
  one CM point are used; the rest is the proved class number one of `𝒪` (`classNumberOneB_proof`), Tau Ceti's
  absolute Artin map with Steinitz's extension to `Aut(ℂ)`, and a `decide` table over `𝒪/3𝒪`.
* `DCY3Used.y3ConnectedAb_of_field : ShimuraGlue.DeligneComponentsY3PrintedAb → Y3ConnectedAb`: the used form is not
  stronger than the field.
* `DCY3Used.y3Connected_of_leaves`: the chain's `TSHecke.Y3Connected` from the two research fields
  `mumfordGroupLaw` (for `R1fpProps = R1fpPropsAb`) and `shimuraMainThmIDeligneY3AbU`.

The argument (paper): for a clopen `U ⊆ Y`, `χ(g) = [Ψ(τ, g) ∈ U]` does not depend on `τ` (`ℍ` is connected and
`τ ↦ Ψ(τ, g)` is continuous for the Zariski topology), is invariant under `g ↦ γ g k` (`γ ∈ B^×_+`, `k ∈ K₃`) by
the uniformization, and under `g ↦ h g` for `h = q̂(s)`, `s` the idele `1 + i` above 3 and `1` elsewhere of
`K = ℚ(i)`, by the reciprocity law at the CM point `√2 + i` of `q : i ↦ i + j` (`σ` with `σ = [s, K]` exists for
every idele and fixes the points of `U`). Class number one gives `G(𝔸_f) = B^×_+ 𝒪̂^×`; `𝒪¹` reaches every class of
reduced norm 1 in `(𝒪/3𝒪)^×` (36 classes, table `L36`) and `h ≡ 1 + i + j` has reduced norm `2 ≡ −1`, so `χ` is
constant; a nonempty open subset of `Y` has a `ℂ`-point (Jacobson), so `U = ∅` or `U = Y`.
-/

set_option linter.all false

noncomputable section

namespace DCY3Used

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields


open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

open scoped IsMulCommutative in
/-- **Every idele `s` of `K` is `[s, K]` for some `σ ∈ Aut(ℂ)`** (any `κ`): represent the absolute Artin
symbol of `s` by `g ∈ Gal(Kˢ/K)` and extend `g` to `ℂ` (Steinitz, `T5Glue.exists_ringEquiv_extend`). -/
theorem exists_sigma_artinCondC (κ : K →+* ℂ) (s : IdeleGroup (𝓞 K) K) :
    ∃ σ : ℂ ≃+* ℂ, ArtinCondC κ σ s := by
  letI : Algebra K ℂ := κ.toAlgebra
  let e : SeparableClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  have he : (e : SeparableClosure K →+* ℂ).comp (algebraMap K (SeparableClosure K)) = κ := by
    ext k; exact e.commutes k
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((globalClassFormation K).absoluteArtinMap
      (globalGroundEquiv K (Additive.ofMul (QuotientGroup.mk s : IdeleClassGroup (𝓞 K) K)))).toMul
  have hg' := congrArg Additive.ofMul hg
  rw [ofMul_toMul] at hg'
  obtain ⟨σ, hσ⟩ := T5Glue.exists_ringEquiv_extend (e : SeparableClosure K →+* ℂ) g.toRingEquiv
  refine ⟨σ, ?_⟩
  intro L _ _ _ _ j hj x
  obtain ⟨ι, hι⟩ := exists_iota κ (e : SeparableClosure K →+* ℂ) he L j hj
  have h1 := of_ideleClassArtinMap K L ι (QuotientGroup.mk s)
  have h0 := globalArtinMap_eq_of_mk_eq_absoluteArtinMap K L ι g hg'
  have h3 : Abelianization.of (ideleClassArtinMap K L (QuotientGroup.mk s)) =
      Abelianization.of (ι.restrictNormalHom g) := by
    rw [h1, h0, toMul_ofMul]
  have h2 : ideleClassArtinMap K L (QuotientGroup.mk s) = ι.restrictNormalHom g :=
    (Abelianization.equivOfComm (H := Gal(L/K))).injective h3
  rw [h2, ← hι, ← hι, AlgHom.restrictNormalHom_commutes]
  exact hσ (ι x)

/-- `σ` does not move the underlying point of a `ℂ`-point. -/
theorem ptC_galPt {Y : Over (Spec (CommRingCat.of ℚ))} (σ : ℂ ≃+* ℂ) (y : fieldPt ℂ ⟶ Y) :
    ShimuraSplit.ptC (galPt σ y).left = ShimuraSplit.ptC y.left := by
  have h := specToEquivOfField_comp ((σ : ℂ →+* ℂ).toRatAlgHom : ℂ →+* ℂ)
    (y.left : Spec (CommRingCat.of ℂ) ⟶ Y.left)
  have h2 := congrArg Sigma.fst h
  exact h2




open LeafQM ShimuraCFT RayClassCFT

def conjC (m : Fin 4 → ℤ) : Fin 4 → ℤ := ![m 0 + m 2, -m 1, -m 2, -m 3]
def red3 (m : Fin 4 → ℤ) : Fin 4 → ZMod 3 := fun i => (m i : ZMod 3)

/-! ## Integer coordinates -/

theorem mulCoordR_cast {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n m : Fin 4 → R) :
    (fun i => f (ShimuraGlue.mulCoordR n m i)) = ShimuraGlue.mulCoordR (fun i => f (n i)) (fun i => f (m i)) := by
  funext i; fin_cases i <;> simp [ShimuraGlue.mulCoordR]

theorem N4_mul {R : Type*} [CommRing R] (n m : Fin 4 → R) :
    ShimuraGlue.N4 (ShimuraGlue.mulCoordR n m) = ShimuraGlue.N4 n * ShimuraGlue.N4 m := by
  simp [ShimuraGlue.N4, ShimuraGlue.mulCoordR]; ring

theorem ofInt_mul (n m : Fin 4 → ℤ) : ofInt n * ofInt m = ofInt (ShimuraGlue.mulCoordR n m) := by
  rw [← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt,
    ShimuraGlue.ofQ_mul]
  congr 1
  exact (mulCoordR_cast (Int.castRingHom ℚ) n m).symm

theorem ofInt_add (n m : Fin 4 → ℤ) : ofInt n + ofInt m = ofInt (n + m) := by
  rw [← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt,
    ShimuraGlue.ofQ_add]
  congr 1; funext i; simp

theorem ofInt_injective : Function.Injective ofInt := by
  intro n m h
  have := congrArg cQ h
  rw [cQ_ofInt, cQ_ofInt] at this
  funext i
  exact_mod_cast congrFun this i

theorem ofInt_e1 : ofInt ![1, 0, 0, 0] = 1 := by ext <;> simp [ofInt]

theorem nrd_ofInt (n : Fin 4 → ℤ) : ShimuraGlue.nrdQ ℚ (ofInt n) = ((ShimuraGlue.N4 n : ℤ) : ℚ) := by
  rw [← ShimuraGlue.ofQ_eq_ofInt, ShimuraGlue.nrdQ_ofQ]
  exact (ShimuraGlue.map_N4 (Int.castRingHom ℚ) n).symm

theorem ofInt_mul_star {n : Fin 4 → ℤ} (h : ShimuraGlue.N4 n = 1) : ofInt n * star (ofInt n) = 1 := by
  rw [← nrd_coe_eq, nrd_ofInt, h]; simp

theorem star_ofInt' (n : Fin 4 → ℤ) : star (ofInt n) = ofInt (conjC n) := by
  rw [star_ofInt]; rfl

/-- Lift a congruence mod 3 from `ZMod 3` to `ℤ`. -/
theorem lift3 {z e : Fin 4 → ℤ} (h : red3 z = red3 e) : ∃ n : Fin 4 → ℤ, z = e + 3 • n := by
  have : ∀ i, (3 : ℤ) ∣ z i - e i := fun i => by
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd (z i - e i) 3).1 (by
      push_cast
      have := congrFun h i; simp only [red3] at this; rw [this, sub_self])
    exact_mod_cast h3
  choose n hn using this
  exact ⟨n, funext fun i => by simp; linarith [hn i]⟩

/-! ## Approximation mod `3𝒪̂` -/

theorem bEmb_ofInt_eq (m : Fin 4 → ℤ) : bEmb (ofInt m) = ShimuraGlue.ofQ (fun i => ((m i : ℤ) : AQ)) := by
  have h1 := ShimuraGlue.ofQ_coords (bEmb (ofInt m))
  have h2 : (![(bEmb (ofInt m)).re - (bEmb (ofInt m)).imJ,
      (bEmb (ofInt m)).imI - (bEmb (ofInt m)).imK,
      2 * (bEmb (ofInt m)).imJ, 2 * (bEmb (ofInt m)).imK] : Fin 4 → AQ) =
      fun i => ((m i : ℤ) : AQ) := by
    have := cQ_bEmb (ofInt m)
    rw [cQ_ofInt] at this
    rw [show (![(bEmb (ofInt m)).re - (bEmb (ofInt m)).imJ,
      (bEmb (ofInt m)).imI - (bEmb (ofInt m)).imK,
      2 * (bEmb (ofInt m)).imJ, 2 * (bEmb (ofInt m)).imK] : Fin 4 → AQ) = cQ (bEmb (ofInt m)) from rfl,
      this]
    funext i; simp
  rw [h2] at h1
  exact h1

theorem ofQ_smul3 (b : Fin 4 → AQ) : ShimuraGlue.ofQ (fun i => (3 : AQ) * b i) = 3 * ShimuraGlue.ofQ b := by
  have : (3 : BAQ) = algebraMap AQ BAQ 3 := (map_ofNat _ 3).symm
  rw [this]
  ext <;> simp [ShimuraGlue.ofQ, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem approx3 {u : BAQ} (hu : u ∈ OhatQ) : ∃ m : Fin 4 → ℤ, ∃ y ∈ OhatQ, u = bEmb (ofInt m) + 3 * y := by
  obtain ⟨n, hn, rfl⟩ := hu
  choose m b hb hab using fun i => exists_int_approx (hn i) 3 (by norm_num)
  refine ⟨m, ShimuraGlue.ofQ b, ⟨b, hb, rfl⟩, ?_⟩
  rw [bEmb_ofInt_eq, ← ofQ_smul3, ShimuraGlue.ofQ_add]
  congr 1
  funext i
  rw [hab i]; simp

/-! ## Units mod 3 -/

theorem bEmb_smul (r : ℚ) (x : B) : bEmb (r • x) = algebraMap ℚ BAQ r * bEmb x := by
  rw [Algebra.smul_def, map_mul, AlgHom.commutes]

theorem inO_of_three_mul {x : B} {W : BAQ} (hW : W ∈ OhatQ) (h : bEmb x = 3 * W) :
    InO ((1 / 3 : ℚ) • x) := by
  apply inO_of_bEmb_mem
  rw [bEmb_smul, h, ← mul_assoc]
  have : algebraMap ℚ BAQ (1 / 3) * 3 = 1 := by
    rw [show (3 : BAQ) = algebraMap ℚ BAQ 3 from (map_ofNat _ 3).symm, ← map_mul]; norm_num
  rw [this, one_mul]; exact hW

/-- `x ∈ 𝒪` with `bEmb x ∈ 3𝒪̂` has coordinates divisible by 3. -/
theorem coords_of_three_mul {z : Fin 4 → ℤ} {W : BAQ} (hW : W ∈ OhatQ) (h : bEmb (ofInt z) = 3 * W) :
    ∃ n : Fin 4 → ℤ, z = 3 • n := by
  obtain ⟨n, hn⟩ := inO_of_three_mul hW h
  refine ⟨n, ofInt_injective ?_⟩
  have : ofInt z = (3 : ℚ) • ofInt n := by
    rw [← hn, smul_smul]; norm_num
  rw [this, ← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt]
  ext <;> simp [ShimuraGlue.ofQ] <;> ring

theorem unit3 {u : BAQˣ} (hu : u ∈ OhatU) :
    ∃ m : Fin 4 → ℤ, ∃ y ∈ OhatQ, (u : BAQ) = bEmb (ofInt m) + 3 * y ∧
      ShimuraGlue.N4 (red3 m) ≠ 0 := by
  obtain ⟨m, y, hy, hu1⟩ := approx3 hu.1
  obtain ⟨m', y', hy', hu2⟩ := approx3 hu.2
  refine ⟨m, y, hy, hu1, ?_⟩
  set W : BAQ := bEmb (ofInt m) * y' + y * bEmb (ofInt m') + 3 * y * y'
  have hW : W ∈ OhatQ := OhatQ_add (OhatQ_add (OhatQ_mul (bEmb_mem_of_inO ⟨m, rfl⟩) hy')
    (OhatQ_mul hy (bEmb_mem_of_inO ⟨m', rfl⟩))) (OhatQ_mul (OhatQ_mul (OhatQ_natCast 3) hy) hy')
  have h1 : (1 : BAQ) = bEmb (ofInt (ShimuraGlue.mulCoordR m m')) + 3 * W := by
    have := u.mul_inv
    rw [← this, hu1, hu2, ← ofInt_mul, map_mul]
    have c3 : ∀ z : BAQ, z * 3 = 3 * z := fun z => (Commute.ofNat_right z 3).eq
    simp only [W, mul_add, add_mul, mul_assoc, c3]
    noncomm_ring
  have h2 : bEmb (ofInt (ShimuraGlue.mulCoordR m m' - ![1, 0, 0, 0])) = 3 * (-W) := by
    have e : ofInt (ShimuraGlue.mulCoordR m m' - ![1, 0, 0, 0]) =
        ofInt (ShimuraGlue.mulCoordR m m') - 1 := by
      rw [← ofInt_e1, eq_sub_iff_add_eq, ofInt_add]; congr 1; abel
    rw [e, map_sub, map_one]
    rw [mul_neg, eq_neg_iff_add_eq_zero]
    rw [h1]; abel
  obtain ⟨n, hn⟩ := coords_of_three_mul (OhatQ_neg hW) h2
  have hz : red3 (ShimuraGlue.mulCoordR m m') = red3 ![1, 0, 0, 0] := by
    funext i
    have := congrFun hn i
    simp only [red3]
    have e : ShimuraGlue.mulCoordR m m' i = ![1, 0, 0, 0] i + 3 * n i := by
      have := congrFun hn i; simp at this; linarith
    rw [e]; push_cast
    rw [show (3 : ZMod 3) = 0 from rfl]; ring
  have hN := congrArg ShimuraGlue.N4 hz
  rw [show red3 (ShimuraGlue.mulCoordR m m') = ShimuraGlue.mulCoordR (red3 m) (red3 m') from
    mulCoordR_cast (Int.castRingHom (ZMod 3)) m m', N4_mul] at hN
  intro h0
  rw [h0, zero_mul] at hN
  revert hN; decide


/-! ## The table -/

/-- 36 elements of `𝒪` of reduced norm 1, one in each class of `{x ∈ (𝒪/3𝒪)^× : nrd x = 1}`. -/
def L36 : List (Fin 4 → ℤ) :=
  [![0, 0, 1, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![0, 0, -1, 0], ![-1, 0, 1, 0], ![1, 0, -1, 0],
   ![1, -1, 1, 0], ![1, 0, 1, -1], ![1, 0, 1, 1], ![1, 1, 1, 0], ![-1, -1, -1, 0], ![-1, 0, -1, -1],
   ![-1, 0, -1, 1], ![-1, 1, -1, 0], ![1, -1, 1, 1], ![1, 1, 1, -1], ![-1, -1, -1, 1], ![-1, 1, -1, -1],
   ![-3, 2, 0, 0], ![-3, 0, 0, 2], ![-3, 0, 0, -2], ![-3, -2, 0, 0], ![-2, 1, -1, 1], ![-2, -1, -1, -1],
   ![-1, 1, -2, 1], ![-1, -1, -2, -1], ![-3, 1, 1, 1], ![3, 1, -1, 1], ![-3, -1, 1, -1], ![3, -1, -1, -1],
   ![1, 1, -3, 1], ![1, -1, -3, -1], ![-1, 1, 3, 1], ![-1, -1, 3, -1], ![-3, 2, 0, -2], ![-3, -2, 0, 2]]

theorem L36_norm : ∀ γ ∈ L36, ShimuraGlue.N4 γ = 1 := by decide


set_option maxRecDepth 100000 in
theorem table3 : ∀ a b c d : ZMod 3, ShimuraGlue.N4 ![a, b, c, d] ≠ 0 →
    ∃ γ ∈ L36, ShimuraGlue.mulCoordR (red3 (conjC γ)) ![a, b, c, d] = ![1, 0, 0, 0] ∨
      ShimuraGlue.mulCoordR (red3 (conjC γ)) ![a, b, c, d] = ![0, 1, 2, 0] := by
  decide


/-! ## Decomposition of `𝒪̂^×` modulo `K₃` -/

theorem ofInt_three_smul (n : Fin 4 → ℤ) : ofInt (3 • n) = 3 * ofInt n := by
  rw [← map_ofNat (algebraMap ℚ B) 3, ← Algebra.smul_def]
  ext <;> simp [ofInt] <;> ring

theorem red3_eta (m : Fin 4 → ℤ) : ![red3 m 0, red3 m 1, red3 m 2, red3 m 3] = red3 m := by
  funext i; fin_cases i <;> rfl

/-- The coordinates of `1 + i + j = q(1 + √−1)`. -/
def cc : Fin 4 → ℤ := ![0, 1, 2, 0]

theorem red3_e1 : red3 ![1, 0, 0, 0] = ![1, 0, 0, 0] := by funext i; fin_cases i <;> rfl
theorem red3_cc : red3 cc = ![0, 1, 2, 0] := by funext i; fin_cases i <;> rfl

/-- **Every `u ∈ 𝒪̂^×` is `γ k` or `γ h k`** with `γ ∈ 𝒪¹` and `k ∈ K₃`, for any `h ∈ 𝒪̂^×` congruent to
`1 + i + j` mod `3𝒪̂` (the table, through the approximation of `u` mod `3𝒪̂`). -/
theorem decomp3 {h : BAQˣ} (hh : h ∈ OhatU) {yh : BAQ} (hyh : yh ∈ OhatQ)
    (hhe : (h : BAQ) = bEmb (ofInt cc) + 3 * yh) {u : BAQˣ} (hu : u ∈ OhatU) :
    ∃ γ : B, ShimuraGlue.nrdQ ℚ γ = 1 ∧ ∃ k : BAQˣ, k ∈ K3Q ∧
      ((u : BAQ) = bEmb γ * k ∨ (u : BAQ) = bEmb γ * h * k) := by
  have c3 : ∀ z : BAQ, z * 3 = 3 * z := fun z => (Commute.ofNat_right z 3).eq
  obtain ⟨m, y, hy, hu1, hN⟩ := unit3 hu
  obtain ⟨γ, hγL, hcase⟩ := table3 (red3 m 0) (red3 m 1) (red3 m 2) (red3 m 3) (by rwa [red3_eta])
  rw [red3_eta] at hcase
  have hγN := L36_norm γ hγL
  set G : B := ofInt γ with hGdef
  have hGG : G * star G = 1 := ofInt_mul_star hγN
  have hGG' : star G * G = 1 := by rw [star_mul_eq]; exact hGG
  have hnrd : ShimuraGlue.nrdQ ℚ G = 1 := by rw [nrd_ofInt, hγN]; simp
  have hGO : bEmb G ∈ OhatQ := bEmb_mem_of_inO ⟨γ, rfl⟩
  have hGsO : bEmb (star G) ∈ OhatQ := bEmb_mem_of_inO (inO_star ⟨γ, rfl⟩)
  let Gu : BAQˣ := bUnit (star G) G hGG' hGG
  have hGu : (Gu : BAQ) = bEmb (star G) := rfl
  have hGui : ((Gu⁻¹ : BAQˣ) : BAQ) = bEmb G := rfl
  have hred : ∀ e : Fin 4 → ℤ, ShimuraGlue.mulCoordR (red3 (conjC γ)) (red3 m) = red3 e →
      ∃ n : Fin 4 → ℤ, star G * ofInt m = ofInt e + 3 * ofInt n := by
    intro e he
    have he' : red3 (ShimuraGlue.mulCoordR (conjC γ) m) = red3 e := by
      rw [show red3 (ShimuraGlue.mulCoordR (conjC γ) m) =
        ShimuraGlue.mulCoordR (red3 (conjC γ)) (red3 m) from
          mulCoordR_cast (Int.castRingHom (ZMod 3)) (conjC γ) m, he]
    obtain ⟨n, hn⟩ := lift3 he'
    refine ⟨n, ?_⟩
    rw [hGdef, star_ofInt', ofInt_mul, hn, ← ofInt_add, ofInt_three_smul]
  refine ⟨G, hnrd, ?_⟩
  rcases hcase with hA | hB
  · obtain ⟨n, hn⟩ := hred ![1, 0, 0, 0] (by rw [hA, red3_e1])
    rw [ofInt_e1] at hn
    refine ⟨Gu * u, ⟨?_, ?_, bEmb (ofInt n) + bEmb (star G) * y, ?_, ?_⟩, Or.inl ?_⟩
    · rw [Units.val_mul, hGu]; exact OhatQ_mul hGsO hu.1
    · rw [mul_inv_rev, Units.val_mul, hGui]; exact OhatQ_mul hu.2 hGO
    · exact OhatQ_add (bEmb_mem_of_inO ⟨n, rfl⟩) (OhatQ_mul hGsO hy)
    · rw [Units.val_mul, hGu, hu1, mul_add, ← map_mul, hn, map_add, map_one, map_mul, map_ofNat]
      rw [← mul_assoc (bEmb (star G)) 3 y, c3]; noncomm_ring
    · rw [Units.val_mul, hGu, ← mul_assoc, ← map_mul, hGG, map_one, one_mul]
  · obtain ⟨n, hn⟩ := hred cc (by rw [hB, red3_cc])
    have hhi : ((h⁻¹ : BAQˣ) : BAQ) * (h : BAQ) = 1 := by simp
    refine ⟨h⁻¹ * Gu * u, ⟨?_, ?_, ((h⁻¹ : BAQˣ) : BAQ) * (-yh + bEmb (ofInt n) + bEmb (star G) * y), ?_, ?_⟩,
      Or.inr ?_⟩
    · rw [Units.val_mul, Units.val_mul, hGu]; exact OhatQ_mul (OhatQ_mul hh.2 hGsO) hu.1
    · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, hGui]
      first | exact OhatQ_mul hu.2 (OhatQ_mul hGO hh.1) | exact OhatQ_mul (OhatQ_mul hu.2 hGO) hh.1
    · exact OhatQ_mul hh.2 (OhatQ_add (OhatQ_add (OhatQ_neg hyh) (bEmb_mem_of_inO ⟨n, rfl⟩))
        (OhatQ_mul hGsO hy))
    · rw [Units.val_mul, Units.val_mul, hGu, hu1, mul_assoc, mul_add, ← map_mul, hn, map_add, map_mul,
        map_ofNat]
      have e1 : bEmb (ofInt cc) = (h : BAQ) - 3 * yh := by rw [hhe]; abel
      rw [e1]
      rw [← mul_assoc (bEmb (star G)) 3 y, c3]
      have : ((h⁻¹ : BAQˣ) : BAQ) * ((h : BAQ) - 3 * yh + 3 * bEmb (ofInt n) + 3 * bEmb (star G) * y) =
          ((h⁻¹ : BAQˣ) : BAQ) * h + ((h⁻¹ : BAQˣ) : BAQ) * 3 * (-yh + bEmb (ofInt n) + bEmb (star G) * y) := by
        noncomm_ring
      rw [this, hhi, c3]; noncomm_ring
    · rw [Units.val_mul, Units.val_mul, hGu]
      have hh2 : (h : BAQ) * ((h⁻¹ : BAQˣ) : BAQ) = 1 := by simp
      calc (u : BAQ) = bEmb G * ((h : BAQ) * ((h⁻¹ : BAQˣ) : BAQ)) * bEmb (star G) * u := by
            rw [hh2, mul_one, ← map_mul, hGG, map_one, one_mul]
        _ = bEmb G * h * (((h⁻¹ : BAQˣ) : BAQ) * bEmb (star G) * u) := by
            noncomm_ring



open LeafQM ShimuraCFT RayClassCFT IsDedekindDomain NumberField Complex

abbrev K4 : Type := ShimuraGlue.Ray.K4

instance : IsTotallyComplex K4 := isTotallyComplex_of_root y4_rel (by norm_num)

/-- `β = i + j ∈ 𝒪`, `β² = −1`. -/
def beta : B := ⟨0, 1, 1, 0⟩

theorem inO_beta : InO beta := ⟨![-1, 1, 2, 0], by ext <;> simp [beta, ofInt] <;> norm_num⟩

theorem beta_sq : beta * beta + (0 : ℚ) • beta + algebraMap ℚ B 1 = 0 := by
  ext <;> simp [beta] <;> norm_num

/-- `τ₀ = √2 + i`, the fixed point of `ι(β)` in `ℍ`. -/
def tau0 : UpperHalfPlane := ⟨(Real.sqrt 2 : ℂ) + I, by simp⟩

theorem heig0 : Matrix.mulVec ((BPAnalytic.QM.iota beta).map (algebraMap ℝ ℂ)) ![(tau0 : ℂ), 1] =
    I • ![(tau0 : ℂ), 1] := by
  have h := ZInQ.Contrib.TYZGenus.Shimura.sqrt_mul_self_C 2
  push_cast at h
  ext i
  fin_cases i
  · simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, tau0, beta]
    linear_combination h - Complex.I_sq
  · simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, tau0, beta]

theorem y4_ne : ∀ r : ℚ, y4 ≠ r := not_rat_of_disc y4_rel (by norm_num)

/-- `q : ℚ(i) → B`, `i ↦ β`. -/
def q4 : K4 →ₐ[ℚ] B := liftQuad finrank_K4 y4_ne y4_rel beta beta_sq

theorem hl0 : I * I + (0 : ℚ) • I + algebraMap ℚ ℂ 1 = 0 :=
  eig_rel (v := ![(tau0 : ℂ), 1]) (by simp) heig0 beta_sq

/-- The reflex embedding `κ₀ : ℚ(i) → ℂ`, `i ↦ i`. -/
def kappa0 : K4 →+* ℂ := (liftQuad finrank_K4 y4_ne y4_rel I hl0).toRingHom

theorem q4_integral : ∀ x : 𝓞 K4, InO (q4 x) := by
  intro x
  obtain ⟨a, b, hab⟩ := ringOfIntegersGen_K4 x
  have e : (x : K4) = ((a : ℚ) : K4) + ((b : ℚ) : K4) * y4 := by rw [hab]; push_cast; ring
  rw [e, q4, liftQuad_apply]
  have e2 : algebraMap ℚ LeafQM.B (a : ℚ) + (b : ℚ) • beta = (a : LeafQM.B) + (b : LeafQM.B) * beta := by
    rw [Algebra.smul_def]; simp
  rw [e2]
  exact inO_int_comb inO_beta a b

theorem isCMPoint0 : IsCMPoint q4 kappa0 tau0 := by
  intro a
  obtain ⟨r, s, rfl⟩ := exists_rat_repr finrank_K4 y4_ne a
  show Matrix.mulVec (iotaC _) _ = _
  rw [kappa0, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, q4, liftQuad_apply, liftQuad_apply, map_add,
    AlgHom.commutes, map_smul, Matrix.add_mulVec, Matrix.smul_mulVec, show Matrix.mulVec (iotaC beta)
      ![(tau0 : ℂ), 1] = I • ![(tau0 : ℂ), 1] from heig0]
  ext i
  fin_cases i <;>
    simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal, Algebra.smul_def] <;> ring

/-- `c = 1 + i`. -/
def c4 : K4 := ((1 : ℚ) : K4) + ((1 : ℚ) : K4) * y4

theorem q4_c4 : q4 c4 = ofInt ![0, 1, 2, 0] := by
  rw [c4, q4, liftQuad_apply]
  ext <;> simp [beta, ofInt, Algebra.smul_def] <;> norm_num



open LeafQM ShimuraCFT RayClassCFT IsDedekindDomain NumberField


/-! ## The idele `s`: `1 + i` above 3, `1` elsewhere -/

theorem y4_sq : y4 * y4 = -1 := by
  have := y4_rel; push_cast at this; linear_combination this

theorem y4_integral : IsIntegral ℤ y4 :=
  (IsCyclotomicExtension.zeta_spec 4 ℚ K4).isIntegral (by norm_num)

def y4O : 𝓞 K4 := ⟨y4, y4_integral⟩

theorem y4O_coe : ((y4O : 𝓞 K4) : K4) = y4 := rfl
theorem y4O_alg : algebraMap (𝓞 K4) K4 y4O = y4 := rfl

theorem c4_ne : c4 ≠ 0 := by
  intro h
  have h2 : c4 * (1 - y4) = 2 := by rw [c4]; push_cast; linear_combination (-1 : K4) * y4_sq
  rw [h, zero_mul] at h2; norm_num at h2

variable (w : HeightOneSpectrum (𝓞 K4))

theorem v_eq (x : K4) : Valued.v (algebraMap K4 (w.adicCompletion K4) x) = w.valuation K4 x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem v_int_le (x : 𝓞 K4) : w.valuation K4 (x : K4) ≤ 1 := w.valuation_le_one x

theorem v_nat_eq_one (n : ℕ) (h : (n : 𝓞 K4) ∉ w.asIdeal) : w.valuation K4 (n : K4) = 1 := by
  have : (n : K4) = algebraMap (𝓞 K4) K4 n := (map_natCast _ n).symm
  rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact h

theorem two_not_mem (h3 : (3 : 𝓞 K4) ∈ w.asIdeal) : ((2 : ℕ) : 𝓞 K4) ∉ w.asIdeal := by
  intro h2
  have : (1 : 𝓞 K4) ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem h3 h2; push_cast at this; norm_num at this; exact this
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem v_c4_le : w.valuation K4 c4 ≤ 1 := by
  have : c4 = ((1 + y4O : 𝓞 K4) : K4) := by rw [c4]; push_cast; simp only [y4O_coe, y4O_alg]; ring
  rw [this]; exact v_int_le w _

theorem v_c4_eq (h3 : (3 : 𝓞 K4) ∈ w.asIdeal) : w.valuation K4 c4 = 1 := by
  have h2 : c4 * (1 - y4) = ((2 : ℕ) : K4) := by rw [c4]; push_cast; linear_combination (-1 : K4) * y4_sq
  have hv := congrArg (w.valuation K4) h2
  rw [map_mul, v_nat_eq_one w 2 (two_not_mem w h3)] at hv
  have hb : w.valuation K4 (1 - y4) ≤ 1 := by
    have : (1 - y4 : K4) = ((1 - y4O : 𝓞 K4) : K4) := by push_cast; simp only [y4O_coe, y4O_alg]
    rw [this]; exact v_int_le w _
  have ha := v_c4_le w
  by_contra hne
  have hlt : w.valuation K4 c4 < 1 := lt_of_le_of_ne ha hne
  have : w.valuation K4 c4 * w.valuation K4 (1 - y4) < 1 :=
    lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt hb) le_rfl
  rw [hv] at this; exact lt_irrefl _ this

open Classical in
/-- The components of `s`. -/
def uf (w : HeightOneSpectrum (𝓞 K4)) : w.adicCompletion K4 :=
  if (3 : 𝓞 K4) ∈ w.asIdeal then algebraMap K4 _ c4 else 1

open Classical in
def uf' (w : HeightOneSpectrum (𝓞 K4)) : w.adicCompletion K4 :=
  if (3 : 𝓞 K4) ∈ w.asIdeal then algebraMap K4 _ c4⁻¹ else 1

theorem uf_mem : uf w ∈ w.adicCompletionIntegers K4 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  unfold uf; split_ifs with h
  · rw [v_eq]; exact v_c4_le w
  · simp

theorem uf'_mem : uf' w ∈ w.adicCompletionIntegers K4 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  unfold uf'; split_ifs with h
  · rw [v_eq, map_inv₀, v_c4_eq w h, inv_one]
  · simp

def u4 : FiniteAdeleRing (𝓞 K4) K4 := ⟨uf, Filter.Eventually.of_forall uf_mem⟩
def u4' : FiniteAdeleRing (𝓞 K4) K4 := ⟨uf', Filter.Eventually.of_forall uf'_mem⟩

theorem u4_mul : u4 * u4' = 1 := by
  apply FiniteAdeleRing.ext K4
  intro w
  show uf w * uf' w = 1
  unfold uf uf'; split_ifs with h
  · rw [← map_mul, mul_inv_cancel₀ c4_ne, map_one]
  · rw [one_mul]

theorem u4'_mul : u4' * u4 = 1 := by rw [mul_comm]; exact u4_mul

def u4U : (FiniteAdeleRing (𝓞 K4) K4)ˣ := ⟨u4, u4', u4_mul, u4'_mul⟩

/-- **The idele `s`**: `1 + i` at the place above 3, `1` at every other place (finite or infinite). -/
def s4 : IdeleGroup (𝓞 K4) K4 := IdeleGroup.ofFiniteIdele (𝓞 K4) K4 u4U

/-- `s ≡ 1 + i mod 3`: `u = c + 3b` with `b` integral. -/
def b4 : FiniteAdeleRing (𝓞 K4) K4 :=
  (u4 - algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) c4) * algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) (1 / 3)

theorem u4_eq : u4 = algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) c4 + 3 * b4 := by
  have h3 : (3 : FiniteAdeleRing (𝓞 K4) K4) * algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) (1 / 3) = 1 := by
    rw [show (3 : FiniteAdeleRing (𝓞 K4) K4) = algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) 3 from
        (map_ofNat _ 3).symm, ← map_mul]; norm_num
  calc u4 = algebraMap K4 _ c4 + (u4 - algebraMap K4 _ c4) * ((3 : FiniteAdeleRing (𝓞 K4) K4) *
        algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) (1 / 3)) := by rw [h3]; ring
    _ = algebraMap K4 _ c4 + 3 * b4 := by simp only [b4]; ring

theorem b4_mem : b4 w ∈ w.adicCompletionIntegers K4 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : b4 w = (uf w - algebraMap K4 (w.adicCompletion K4) c4) * algebraMap K4 _ (1 / 3) := rfl
  rw [e]
  unfold uf; split_ifs with h
  · simp
  · rw [← map_one (algebraMap K4 (w.adicCompletion K4)), ← map_sub, ← map_mul, v_eq, map_mul]
    have h1 : w.valuation K4 (1 - c4) ≤ 1 := by
      have : (1 - c4 : K4) = ((-y4O : 𝓞 K4) : K4) := by rw [c4]; push_cast; simp only [y4O_coe, y4O_alg]; ring
      rw [this]; exact v_int_le w _
    have h2 : w.valuation K4 (1 / 3) = 1 := by
      rw [one_div, map_inv₀]
      have : ((3 : ℕ) : 𝓞 K4) ∉ w.asIdeal := by exact_mod_cast h
      have h3 := v_nat_eq_one w 3 this
      push_cast at h3; rw [h3, inv_one]
    rw [h2, mul_one]; exact h1


/-! ## The unit `h = q̂(s)` -/

theorem h4_val : ((qHatU q4 s4 : BAQˣ) : BAQ) = qHat q4 u4 := by
  rw [qHatU_coe, s4, IdeleGroup.toFiniteIdele_ofFiniteIdele]; rfl

theorem h4_inv : (((qHatU q4 s4)⁻¹ : BAQˣ) : BAQ) = qHat q4 u4' := by
  rw [← map_inv, qHatU_coe, s4, ← map_inv, IdeleGroup.toFiniteIdele_ofFiniteIdele]; rfl

theorem h4_mem : qHatU q4 s4 ∈ OhatU :=
  ⟨by rw [h4_val]; exact qHat_mem_OhatQ q4 q4_integral u4 (fun w => uf_mem w),
   by rw [h4_inv]; exact qHat_mem_OhatQ q4 q4_integral u4' (fun w => uf'_mem w)⟩

theorem yh_mem : qHat q4 b4 ∈ OhatQ := qHat_mem_OhatQ q4 q4_integral b4 (fun w => b4_mem w)

theorem h4_eq : ((qHatU q4 s4 : BAQˣ) : BAQ) = bEmb (ofInt cc) + 3 * qHat q4 b4 := by
  rw [h4_val, u4_eq, map_add, qHat_algebraMap, q4_c4, map_mul, map_ofNat]; rfl

/-! ## A function on `G(𝔸_f)` invariant under `B^×_+`, `K₃` and `h` is constant -/

theorem const_of_inv {P : BAQˣ → Prop} {h : BAQˣ} (hh : h ∈ OhatU) {yh : BAQ} (hyh : yh ∈ OhatQ)
    (hhe : (h : BAQ) = bEmb (ofInt cc) + 3 * yh)
    (hD : ∀ γ : B, 0 < ShimuraGlue.nrdQ ℚ γ → ∀ g g' k : BAQˣ, k ∈ K3Q →
      (g' : BAQ) = bEmb γ * g * k → (P g ↔ P g'))
    (hH : ∀ g, P (h * g) ↔ P g) : ∀ g, P g ↔ P 1 := by
  intro g
  obtain ⟨γ, hγ, u, hu, hg⟩ := exists_pos_decomp classNumberOneB_proof g
  have e1 : P u ↔ P g := hD γ hγ u g 1 K3Q_one (by rw [hg, Units.val_one, mul_one])
  obtain ⟨γ', hn, k, hk, hc⟩ := decomp3 hh hyh hhe hu
  have hpos : 0 < ShimuraGlue.nrdQ ℚ γ' := by rw [hn]; norm_num
  rcases hc with hA | hB
  · have e2 : P 1 ↔ P u := hD γ' hpos 1 u k hk (by rw [Units.val_one, mul_one]; exact hA)
    rw [← e1, e2]
  · have e2 : P h ↔ P u := hD γ' hpos h u k hk hB
    have e3 := hH 1
    rw [mul_one] at e3
    rw [← e1, ← e2, e3]

/-! ## Points -/

/-- A nonempty open subset of a `ℚ`-scheme locally of finite type contains the point of a `ℂ`-point. -/
theorem exists_C_point (Y : Over (Spec (CommRingCat.of ℚ))) [LocallyOfFiniteType Y.hom]
    (V : Set Y.left) (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ y : fieldPt ℂ ⟶ Y, ShimuraSplit.ptC y.left ∈ V := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  obtain ⟨x, hxV, hx⟩ := nonempty_inter_closedPoints hne hV.isLocallyClosed
  obtain ⟨emb, y0, hy0⟩ := HDec.ModelGlue.exists_qbarPt Y x hx
  refine ⟨fieldMap ιC ≫ y0, ?_⟩
  have h := specToEquivOfField_comp (ιC : Qbar →+* ℂ) (y0.left : Spec (CommRingCat.of Qbar) ⟶ Y.left)
  have h1 : ShimuraSplit.ptC (fieldMap ιC ≫ y0).left =
      (Scheme.SpecToEquivOfField Qbar Y.left y0.left).1 := congrArg Sigma.fst h
  rw [h1, hy0, Equiv.apply_symm_apply]
  exact hxV

/-! ## Connectedness from the Deligne body -/

theorem isCM_delta (δ : Bool) :
    IsCMPoint q4 (if δ then (if δ then kappa0 else (starRingEnd ℂ).comp kappa0)
      else (starRingEnd ℂ).comp (if δ then kappa0 else (starRingEnd ℂ).comp kappa0)) tau0 := by
  cases δ
  · simp only [Bool.false_eq_true, if_false]
    have : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp kappa0) = kappa0 := by ext x; simp
    rw [this]; exact isCMPoint0
  · simpa using isCMPoint0

/-- **`Y` is connected**, for every `(Y, Φ, Ψ)` with the clauses of Shimura's Main Theorem I in
Deligne's adelic form (`DeligneBodyAt`; only the uniformization, the holomorphy and the reciprocity law are
used), by the class number one of `𝒪` and the mod-3 table. -/
theorem connected_of_body {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} [LocallyOfFiniteType Y.hom]
    (hb : DeligneBodyAt Y Φ Ψ) : ConnectedSpace Y.left := by
  obtain ⟨hsurj, hrel, hhol, -, ε, δ, hrec⟩ := hb
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨ShimuraSplit.ptC (Ψ UpperHalfPlane.I 1).left⟩, fun U hU => ?_⟩
  have tind : ∀ (g : BAQˣ) (τ : UpperHalfPlane),
      (ShimuraSplit.ptC (Ψ τ g).left ∈ U ↔ ShimuraSplit.ptC (Ψ UpperHalfPlane.I g).left ∈ U) := by
    intro g τ
    set S : Set UpperHalfPlane := {τ | ShimuraSplit.ptC (Ψ τ g).left ∈ U}
    have hSo : IsOpen S := (hhol g).1 ⟨U, hU.isOpen⟩
    have hSc : IsOpen Sᶜ := (hhol g).1 ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
    have hS : IsClopen S := ⟨isOpen_compl_iff.1 hSc, hSo⟩
    rcases isClopen_iff.1 hS with h0 | h0
    · have a : τ ∉ S := by rw [h0]; exact id
      have b : UpperHalfPlane.I ∉ S := by rw [h0]; exact id
      exact ⟨fun h => absurd h a, fun h => absurd h b⟩
    · have a : τ ∈ S := by rw [h0]; trivial
      have b : UpperHalfPlane.I ∈ S := by rw [h0]; trivial
      exact ⟨fun _ => b, fun _ => a⟩
  let P : BAQˣ → Prop := fun g => ShimuraSplit.ptC (Ψ UpperHalfPlane.I g).left ∈ U
  have hD : ∀ γ : B, 0 < ShimuraGlue.nrdQ ℚ γ → ∀ g g' k : BAQˣ, k ∈ K3Q →
      (g' : BAQ) = bEmb γ * g * k → (P g ↔ P g') := by
    intro γ hγ g g' k hk hg'
    have hd : DCRel UpperHalfPlane.I g (iotaGL γ hγ.ne' • UpperHalfPlane.I) g' :=
      ⟨γ, hγ, ⟨_, iotaGL_coe _ _, rfl⟩, k, hk, hg'⟩
    have he := (hrel _ _ _ _).2 hd
    show ShimuraSplit.ptC (Ψ UpperHalfPlane.I g).left ∈ U ↔ _
    rw [he]
    exact tind g' _
  have hH : ∀ g, P (qHatU q4 s4 * g) ↔ P g := by
    intro g
    obtain ⟨s', hs'⟩ : ∃ s' : IdeleGroup (𝓞 K4) K4, qHatU q4 s' ^ (ε : ℤ) = qHatU q4 s4 := by
      rcases Int.units_eq_one_or ε with rfl | rfl
      · exact ⟨s4, by simp⟩
      · exact ⟨s4⁻¹, by simp⟩
    obtain ⟨σ, hσ⟩ := exists_sigma_artinCondC (if δ then kappa0 else (starRingEnd ℂ).comp kappa0) s'
    have h1 := hrec K4 finrank_K4 _ q4 tau0 (isCM_delta δ) σ s' hσ g
    rw [hs'] at h1
    have h2 : ShimuraSplit.ptC (Ψ tau0 (qHatU q4 s4 * g)).left = ShimuraSplit.ptC (Ψ tau0 g).left := by
      rw [← h1, ptC_galPt]
    show ShimuraSplit.ptC (Ψ UpperHalfPlane.I (qHatU q4 s4 * g)).left ∈ U ↔
      ShimuraSplit.ptC (Ψ UpperHalfPlane.I g).left ∈ U
    rw [← tind (qHatU q4 s4 * g) tau0, h2, tind g tau0]
  have hconst : ∀ g, P g ↔ P 1 := const_of_inv h4_mem yh_mem h4_eq hD hH
  by_contra hne
  rw [not_or] at hne
  obtain ⟨y, hy⟩ := exists_C_point Y U hU.isOpen (Set.nonempty_iff_ne_empty.2 hne.1)
  obtain ⟨y', hy'⟩ := exists_C_point Y Uᶜ hU.isClosed.isOpen_compl
    (Set.nonempty_compl.2 hne.2)
  obtain ⟨τ, g, rfl⟩ := hsurj y
  obtain ⟨τ', g', rfl⟩ := hsurj y'
  have a : P g := (tind g τ).1 hy
  have b : ¬ P g' := fun hp => hy' ((tind g' τ').2 hp)
  exact b ((hconst g').2 ((hconst g).1 a))

/-! ## The used form of `deligneComponentsY3PrintedAb` -/

/-- **The used form of `ShimuraGlue.DeligneComponentsY3PrintedAb`** (dcy3-used): some fine witness `(Y, Φ)` of the
abelian-scheme moduli clause list `R1fpPropsAb` (the level-3 Shimura curve `Y₃`) is connected over `ℚ`. This is
the only property of the field the chain reads (`TSHecke.Y3Connected`, through `TailZ13`). -/
def Y3ConnectedAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ ConnectedSpace Y.left

/-- **`Y₃` is connected, from Shimura's Main Theorem I in Deligne's adelic form** (the leaf
`ShimuraMainThmIDeligneY3Ab`; its moduli clause is not used). -/
theorem y3ConnectedAb_of_mainThmI (h : ShimuraMainThmIDeligneY3Ab) : Y3ConnectedAb := by
  obtain ⟨Y, Φ, h1, Ψ, hb⟩ := h
  haveI : IsProper Y.hom := h1.1
  exact ⟨Y, Φ, h1, connected_of_body (Ψ := Ψ) hb⟩

/-- **The same from the bundle field `shimuraMainThmIDeligneY3AbU`.** -/
theorem y3ConnectedAb_of_U (h : ShimuraMainThmIDeligneY3AbU) : Y3ConnectedAb :=
  y3ConnectedAb_of_mainThmI (mainThmI_of_U h)

/-! ## Not stronger than the field -/

open ShimuraSplit in
/-- **`Y` is connected if `π₀(Y_ℚ̄) ≃ ℚ^×_{>0}\𝔸_f^×/nrd(K₃)` with the cyclotomic Galois action** and `Y` has a
`ℚ̄`-point (shimura-glue's `deligneComponentsY3_of_printed` and shimura-split's `y3Connected_of_deligne`, with the
clause list replaced by its only used clause, the `ℚ̄`-point). -/
theorem connected_of_delignePi0 {Y : Over (Spec (CommRingCat.of ℚ))} (y₀ : fieldPt Qbar ⟶ Y)
    (hD : ShimuraGlue.DelignePi0 Y ShimuraGlue.K3) : ConnectedSpace Y.left := by
  obtain ⟨c0, ε, hc0⟩ := hD
  let c := c0.trans ShimuraGlue.pi0K3Equiv.toEquiv
  have hc : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (z : _root_.ConnectedComponents (baseQbar Y)),
      c (galActπ₀ Y σ z) = chi3 σ * c z := by
    intro σ z
    have := hc0 σ (ShimuraGlue.cycU σ.toRingEquiv) (fun v => ShimuraGlue.cycU_apply _ v) z
    simp only [c, Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, this, map_mul,
      map_zpow, ShimuraGlue.pi0K3Equiv_mk]
    rw [ShimuraGlue.chi_cycU card_mu3, ShimuraGlue.zmod3_zpow]
    rfl
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨y₀.left (IsLocalRing.closedPoint _)⟩, fun U hU => ?_⟩
  let p : baseQbar Y ⟶ Y.left := pullback.fst _ _
  have hpsurj : Function.Surjective p := p.surjective
  let V : Set (baseQbar Y) := p ⁻¹' U
  have hV : IsClopen V := hU.preimage p.continuous
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hne0, hne1⟩ := hne
  obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.2 hne0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra hall
    exact hne1 (Set.eq_univ_of_forall fun a => by by_contra ha; exact hall ⟨a, ha⟩)
  obtain ⟨z, hz⟩ := hpsurj u
  obtain ⟨z', hz'⟩ := hpsurj u'
  have hzV : z ∈ V := by show p z ∈ U; rw [hz]; exact hu
  have hz'V : z' ∉ V := by show p z' ∉ U; rw [hz']; exact hu'
  let T : Set (ZMod 3)ˣ := {t | ∃ w ∈ V, c (ConnectedComponents.mk w) = t}
  have hT : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ t ∈ T, chi3 σ * t ∈ T := by
    rintro σ t ⟨w, hw, rfl⟩
    refine ⟨galAct Y σ w, ?_, ?_⟩
    · show p (galAct Y σ w) ∈ U
      change (pullback.fst Y.hom sQbar) (galAct Y σ w) ∈ U
      rw [← Scheme.Hom.comp_apply, galAct_fst]; exact hw
    · rw [← hc σ]; rfl
  obtain ⟨σ, hσ⟩ := exists_chi3_neg
  have hzT : c (ConnectedComponents.mk z) ∈ T := ⟨z, hzV, rfl⟩
  rcases units_zmod3 (c (ConnectedComponents.mk z)) (c (ConnectedComponents.mk z')) with e | e
  · have hmk : ConnectedComponents.mk z' = ConnectedComponents.mk z := c.injective e
    rw [ConnectedComponents.coe_eq_coe'] at hmk
    exact hz'V (hV.connectedComponent_subset hzV hmk)
  · obtain ⟨w, hw, hwe⟩ := hT σ _ hzT
    rw [hσ, ← e] at hwe
    have hmk : ConnectedComponents.mk z' = ConnectedComponents.mk w := c.injective hwe.symm
    rw [ConnectedComponents.coe_eq_coe'] at hmk
    exact hz'V (hV.connectedComponent_subset hw hmk)

/-- **The used form is implied by the field** (so it is not stronger than the field). -/
theorem y3ConnectedAb_of_field (h : ShimuraGlue.DeligneComponentsY3PrintedAb) : Y3ConnectedAb := by
  obtain ⟨Y, Φ, h1, hD⟩ := h
  obtain ⟨y₀⟩ := h1.2.2.1
  exact ⟨Y, Φ, h1, connected_of_delignePi0 y₀ hD⟩

/-! ## The chain's form -/

/-- `Y3ConnectedAb` is the chain's `TSHecke.Y3Connected` under the group-law leaf (`r1fpProps_eq_ab_gl`). -/
theorem y3Connected_of_ab_gl (hG : LeafQM.AV.R1UnivRigid.QMFamilyGroupLaw) (h : Y3ConnectedAb) :
    HDec.TSHecke.Y3Connected := by
  unfold HDec.TSHecke.Y3Connected
  rw [LeafQM.AV.R1UnivRigid.r1fpProps_eq_ab_gl hG]
  exact h

/-- **`TSHecke.Y3Connected` from the research fields `mumfordGroupLaw` and `shimuraMainThmIDeligneY3AbU`**: the
term that replaces `y3Connected_of_deligne (deligneComponentsY3_of_printed …)` in the fold. -/
theorem y3Connected_of_leaves (hM : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw)
    (hU : ShimuraMainThmIDeligneY3AbU) : HDec.TSHecke.Y3Connected :=
  y3Connected_of_ab_gl (LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw hM) (y3ConnectedAb_of_U hU)

end DCY3Used
