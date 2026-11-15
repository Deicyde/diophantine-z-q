import ZInQKernel.Contrib.OneProof.QMRecPrinted
import ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used

/-! # composite-out: the three uses of gt-rayclass's composite `ShimuraMainThmIDeligneY3AbU` without it

gt-rayclass's composite GLUE field `RayClassCFT.ShimuraMainThmIDeligneY3AbU` is read in three places:
`rayClassCMAb`, `shimuraFamilyAb` (`RayClassCFT.rayClassCMAb_of_leaves`, `RayClassCFT.shimuraFamilyAb_of_U`) and
dcy3-used's `HDec.TSHecke.Y3Connected` (`DCY3Used.y3Connected_of_leaves`). This file proves all three from

* qmrec-printed's printed leaf `QMRecPrinted.MainTheoremCM` (the adelic main theorem of complex multiplication, with
  torsion), through `QMRecPrinted.qmReciprocityL3_of_textbook` (Shimura's reciprocity law on the objects `T(z, g)`);
* one new leaf `ShimuraHolFamilyL3`: Shimura's Main Theorem I, complex part, **with the level structure**: some fine
  witness `(Y, Φ)` of `R1fpPropsAb` carries a holomorphic `τ ↦ y_τ ∈ Y(ℂ)` whose object is `T(τ, g₀)` (the torus
  `ℂ²/ι(𝒪)(τ, 1)ᵀ` with `ι` and the level structure `η(a) = [ι(x)(τ,1)ᵀ/3]`, `x g₀ ≡ a mod 3𝒪̂`) for one fixed
  `g₀ ∈ 𝒪̂^×`. This is shimura-split2's `ShimuraHolFamilyAb` with the level structure of the moduli point kept;
* the kept fields `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed` (textbook) and `mumfordGroupLaw`
  (research, for `R1fpProps = R1fpPropsAb`).

**Why the level structure.** dcy3-used's argument reads, from the composite, the openness of the preimages of Zariski
opens under `τ ↦ Ψ(τ, g)` *for every `g`*, together with the uniformization relation. A holomorphic family whose
object is only known as a QM pair (shimura-split2's `ShimuraHolFamilyAb`) may change its level structure with `τ`, and
then the relation `B^×_+` gives is `F(x) = F(x ε_{γτ} γ ε_τ⁻¹)` with unknown `ε`'s. With the level fixed, two
families suffice: `A_τ = y_τ` (the object `T(τ, 1)` after a normalization by a unit of `𝒪`) and `B_τ = y_τ ≫ e`,
with `e` the automorphism of `Y` that right-multiplies the level structure by the unit `c = 1/2 + i − j/2 ∈ 𝒪^×`
(`R1heckeProps`, proved in the chain: `HDec.QMSplit.Moduli.heckeOfFine_proof`). Then:

1. every `ℂ`-point is some `A_τ` or `B_τ` (`ComplexUnifL3`, dcy3-used's `decomp3`, `DCRelTransport`,
   `UnifDetermines`, all proved);
2. for a clopen `U ⊆ Y`, `[A_τ ∈ U]` and `[B_τ ∈ U]` do not depend on `τ` (holomorphy: openness of preimages);
3. at the CM point `τ₀ = √2 + i` of `q : ℚ(i) → B`, `i ↦ i + j`, Shimura's reciprocity law (from `MainTheoremCM`)
   moves `A_{τ₀}` to `B_{τ₀}` by some `σ ∈ Aut(ℂ)`, which does not move the underlying point of `Y`.

So `U` is empty or everything: `Y` is connected. No class-number argument is needed. -/

noncomputable section

namespace CompositeOut

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT RayClassCFT ShimuraSplit2 DCY3Used
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)

/-! ## §1 The leaf -/

/-- **LEAF `ShimuraHolFamilyL3` (Shimura's Main Theorem I, complex part, with the level structure, on a fine
witness).** Some fine witness `(Y, Φ)` (`R1fpPropsAb`: the moduli scheme `Y₃` of QM abelian surfaces with level-3
structure, as in every moduli leaf of the bundles) has a holomorphic `τ ↦ y_τ ∈ Y(ℂ)` (`ShimuraSplit.IsHolFamily`:
preimages of Zariski opens are open, regular functions pull back to holomorphic functions) and one `g₀ ∈ 𝒪̂^×` such
that, for every `τ ∈ ℍ`, the object at `y_τ` is `T(τ, g₀)` (shimura-split2's `MIsAt`): an `ι`-compatible analytic
uniformization `ℂ² → A(ℂ)` with kernel `ι(𝒪)(τ, 1)ᵀ` carrying the level structure `a ↦ [ι(x)(τ, 1)ᵀ/3]`
(`x ∈ B`, `x g₀ ≡ a mod 3𝒪̂`) to `η`.

*Published statements* (locators recalled, UNVERIFIED; no network):
* G. Shimura, *Construction of class fields and zeta functions of algebraic curves*, Ann. of Math. 85 (1967),
  Main Theorem I and §§2-3: the canonical model `V_S` of `Γ_S\ℍ` with a holomorphic `φ_S : ℍ → V_S(ℂ)` whose value at
  `z` is the moduli point of the PEL datum `(A_z, ι, C, t_z)` with `A_z = ℂ²/ι(𝒪)(z, 1)ᵀ` and `t_z` the point of
  finite order given by a fixed vector of `B ⊗ ℚ` (the level structure, a fixed formula in `z`);
* G. Shimura, *On analytic families of polarized abelian varieties and automorphic functions*, Ann. of Math. 78
  (1963) (the analytic family over `ℍ` and the holomorphy of its classifying map);
* P. Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §4: the moduli scheme of QM abelian surfaces with
  level `K` is the canonical model of `Sh_K(B^×, ℍ^±)`, its complex points `B^×\(ℍ^± × (B ⊗ 𝔸_f)^×)/K`, the point
  `[τ, g]` being `(ℂ²/ι(L_g)(τ,1)ᵀ, ι, η_g)`; Milne, *Introduction to Shimura varieties* (2005), §§8, 14.

*Form*: the composite's clauses 2 and 3 at one `g = g₀ ∈ 𝒪̂^×` with the level structure kept (Deligne's `[τ, g₀]`);
one family; the representability clause (R) that every moduli leaf of the bundle carries. Shimura's `φ_S` lands in
one geometric component of `Y₃`; `T(τ, g₀)` for a fixed `g₀` is exactly such a component's moduli description. It is
shimura-split2's `ShimuraHolFamilyAb` (implied: `shimuraHolFamilyAb_of_L3`) plus the level structure of the moduli
point. -/
def ShimuraHolFamilyL3 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (yτ τ).left) ∧
      ∃ g₀ ∈ OhatU, ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧ MIsAt P τ g₀

/-! ## §2 Units of `𝒪` and the level structure -/

/-- A unit of `𝒪` as a unit of `B ⊗ 𝔸_f`. -/
def uU (u : (LeafQM.O)ˣ) : BAQˣ :=
  bUnit ((u : LeafQM.O) : LeafQM.B) (((u⁻¹ : (LeafQM.O)ˣ) : LeafQM.O) : LeafQM.B)
    (by rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one])
    (by rw [← Subring.coe_mul, Units.inv_mul, Subring.coe_one])

theorem uU_val (u : (LeafQM.O)ˣ) : ((uU u : BAQˣ) : BAQ) = bEmb ((u : LeafQM.O) : LeafQM.B) := rfl

theorem uU_inv_val (u : (LeafQM.O)ˣ) :
    (((uU u)⁻¹ : BAQˣ) : BAQ) = bEmb (((u⁻¹ : (LeafQM.O)ˣ) : LeafQM.O) : LeafQM.B) := rfl

theorem uU_mem (u : (LeafQM.O)ˣ) : uU u ∈ OhatU :=
  ⟨bEmb_mem_of_inO (u : LeafQM.O).2, bEmb_mem_of_inO ((u⁻¹ : (LeafQM.O)ˣ) : LeafQM.O).2⟩

/-- **Right multiplication of the level structure by `u ∈ 𝒪^×` moves `T(τ, g)` to `T(τ, g u⁻¹)`**: the same
uniformization works, `L_{g u⁻¹} = L_g` and `x g ≡ a u ⇒ x (g u⁻¹) ≡ a`. -/
theorem mIsAt_rightMul {P : QML3 ℂ} {τ : UpperHalfPlane} {g : BAQˣ} (u : (LeafQM.O)ˣ) (h : MIsAt P τ g) :
    MIsAt (P.rightMul u) τ (g * (uU u)⁻¹) := by
  obtain ⟨Φu, hU, hI, hL⟩ := h
  have hu1 : ((uU u : BAQˣ) : BAQ) ∈ OhatQ := (uU_mem u).1
  have hu2 : (((uU u)⁻¹ : BAQˣ) : BAQ) ∈ OhatQ := (uU_mem u).2
  have hlat : vecLat (τ : ℂ) (g * (uU u)⁻¹) = vecLat (τ : ℂ) g := by
    ext v
    rw [mem_vecLat, mem_vecLat]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      have e : bEmb x * (g : BAQ) = bEmb x * ((g * (uU u)⁻¹ : BAQˣ) : BAQ) * ((uU u : BAQˣ) : BAQ) := by
        rw [Units.val_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
      rw [e]; exact OhatQ_mul hx hu1
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      rw [Units.val_mul, ← mul_assoc]; exact OhatQ_mul hx hu2
  refine ⟨Φu, hlat ▸ hU, hI, fun a => ?_⟩
  obtain ⟨x, ⟨y, hy, hx⟩, hΦ⟩ := hL (a * u)
  refine ⟨x, ⟨y * (((uU u)⁻¹ : BAQˣ) : BAQ), OhatQ_mul hy hu2, ?_⟩, hΦ⟩
  have hc : bEmb ((u : LeafQM.O) : LeafQM.B) * bEmb (((u⁻¹ : (LeafQM.O)ˣ) : LeafQM.O) : LeafQM.B) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
  rw [Units.val_mul, ← mul_assoc, hx, uU_inv_val, Subring.coe_mul, map_mul, add_mul, mul_assoc, hc, mul_one,
    mul_assoc]

/-- `DCRel τ g τ (g k)` for `k ∈ K₃` (`γ = 1`). -/
theorem dcRel_K3 (τ : UpperHalfPlane) (g k : BAQˣ) (hk : k ∈ K3Q) : DCRel τ g τ (g * k) := by
  refine ⟨1, by rw [map_one]; norm_num, ⟨1, ?_, one_smul _ _⟩, k, hk, by rw [map_one, one_mul, Units.val_mul]⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [BPAnalytic.QM.iota]

/-- **A unit of `𝒪` congruent to `g ∈ 𝒪̂^×` mod `3`**: `g u⁻¹ ∈ K₃` (shimura-split2's 72-unit table through
`exists_unit_cong`, after dcy3-used's approximation `unit3`). -/
theorem exists_unitO {g : BAQˣ} (hg : g ∈ OhatU) : ∃ u : (LeafQM.O)ˣ, g * (uU u)⁻¹ ∈ K3Q := by
  obtain ⟨m, y, hy, hgm, hN⟩ := unit3 hg
  have h3 : ¬ (3 : ℤ) ∣ nrdZ m := by
    intro hd
    apply hN
    have e : ShimuraGlue.N4 (red3 m) = ((nrdZ m : ℤ) : ZMod 3) := by
      simp only [red3, ShimuraGlue.N4, nrdZ]; push_cast; ring
    rw [e]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast hd)
  obtain ⟨ε, ε', d, hε, hε', hd, h1, h2, hm⟩ := exists_unit_cong m h3
  let u : (LeafQM.O)ˣ := ⟨⟨ε, hε⟩, ⟨ε', hε'⟩, Subtype.ext h1, Subtype.ext h2⟩
  refine ⟨u, ?_, ?_, bEmb d * bEmb ε' + y * bEmb ε', ?_, ?_⟩
  · rw [Units.val_mul]; exact OhatQ_mul hg.1 (uU_mem u).2
  · rw [mul_inv_rev, inv_inv, Units.val_mul]; exact OhatQ_mul (uU_mem u).1 hg.2
  · exact OhatQ_add (OhatQ_mul (bEmb_mem_of_inO hd) (bEmb_mem_of_inO hε'))
      (OhatQ_mul hy (bEmb_mem_of_inO hε'))
  · have c3 : ∀ z : BAQ, z * 3 = 3 * z := fun z => (Commute.ofNat_right z 3).eq
    have hee : bEmb ε * bEmb ε' = 1 := by rw [← map_mul, h1, map_one]
    rw [Units.val_mul, uU_inv_val, hgm, hm]
    show (bEmb (ε + 3 * d) + 3 * y) * bEmb ε' = _
    rw [map_add, map_mul, map_ofNat, add_mul, add_mul, hee, mul_assoc]
    noncomm_ring

/-! ## §3 Families of `ℂ`-points -/

/-- Openness of preimages survives composition with a morphism of `Y`. -/
theorem isOpen_comp {Y : Over (Spec (CommRingCat.of ℚ))} (f : UpperHalfPlane → (fieldPt ℂ ⟶ Y))
    (hf : ∀ U : Y.left.Opens, IsOpen {τ | ShimuraSplit.ptC (f τ).left ∈ U}) (e : Y ⟶ Y) :
    ∀ U : Y.left.Opens, IsOpen {τ | ShimuraSplit.ptC (f τ ≫ e).left ∈ U} := by
  intro U
  exact hf (e.left ⁻¹ᵁ U)

/-- A family with open preimages takes a clopen set either always or never. -/
theorem tind {Y : Over (Spec (CommRingCat.of ℚ))} (f : UpperHalfPlane → (fieldPt ℂ ⟶ Y))
    (hf : ∀ U : Y.left.Opens, IsOpen {τ | ShimuraSplit.ptC (f τ).left ∈ U}) (U : Set Y.left) (hU : IsClopen U)
    (τ τ' : UpperHalfPlane) : ShimuraSplit.ptC (f τ).left ∈ U ↔ ShimuraSplit.ptC (f τ').left ∈ U := by
  set S : Set UpperHalfPlane := {τ | ShimuraSplit.ptC (f τ).left ∈ U}
  have hSo : IsOpen S := hf ⟨U, hU.isOpen⟩
  have hSc : IsOpen Sᶜ := hf ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
  have hS : IsClopen S := ⟨isOpen_compl_iff.1 hSc, hSo⟩
  rcases isClopen_iff.1 hS with h0 | h0
  · have a : τ ∉ S := by rw [h0]; exact id
    have b : τ' ∉ S := by rw [h0]; exact id
    exact ⟨fun h => absurd h a, fun h => absurd h b⟩
  · have a : τ ∈ S := by rw [h0]; trivial
    have b : τ' ∈ S := by rw [h0]; trivial
    exact ⟨fun _ => b, fun _ => a⟩

/-- **Normalization of the level**: a family with objects `T(τ, g₀)`, `g₀ ∈ 𝒪̂^×`, composed with the automorphism of
`Y` that right-multiplies the level structure by a unit `u ≡ g₀ mod 3`, has objects `T(τ, 1)`. -/
theorem family_one {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (hHk : R1heckeProps Y Φ)
    (y : UpperHalfPlane → (fieldPt ℂ ⟶ Y))
    (hopen : ∀ U : Y.left.Opens, IsOpen {τ | ShimuraSplit.ptC (y τ).left ∈ U})
    {g₀ : BAQˣ} (hg₀ : g₀ ∈ OhatU) (hlev : ∀ τ, ∃ P : QML3 ℂ, Φ ℂ (y τ) = M3.mk P ∧ MIsAt P τ g₀) :
    ∃ y' : UpperHalfPlane → (fieldPt ℂ ⟶ Y),
      (∀ U : Y.left.Opens, IsOpen {τ | ShimuraSplit.ptC (y' τ).left ∈ U}) ∧
      ∀ τ, ∃ P : QML3 ℂ, Φ ℂ (y' τ) = M3.mk P ∧ MIsAt P τ 1 := by
  obtain ⟨u, hu⟩ := exists_unitO hg₀
  obtain ⟨e, he⟩ := hHk.2 u
  refine ⟨fun τ => y τ ≫ e.hom, isOpen_comp y hopen e.hom, fun τ => ?_⟩
  obtain ⟨P, hP, hM⟩ := hlev τ
  refine ⟨P.rightMul u, ?_, ?_⟩
  · rw [he ℂ (y τ), hP]; rfl
  · have h1 := mIsAt_rightMul u hM
    have h2 := dcRel_K3 τ 1 (g₀ * (uU u)⁻¹) hu
    rw [one_mul] at h2
    exact dcRelTransport_proof _ τ 1 τ _ h2 h1

/-! ## §4 The unit `c` and the second family -/

/-- `c = 1/2 + i − j/2 ∈ 𝒪` (coordinates `(1, 1, −1, 0)`; shimura-split2's `tabV 0 1 2 0`). -/
def cB : LeafQM.B := LeafQM.ofInt ![1, 1, -1, 0]
/-- `c⁻¹ = −1/2 + i − j/2` (coordinates `(0, 1, −1, 0)`; `tabU 0 1 2 0`), `≡ 1 + i + j mod 3`. -/
def eB : LeafQM.B := LeafQM.ofInt ![0, 1, -1, 0]

theorem cB_mul : cB * eB = 1 := by
  ext <;> simp [cB, eB, LeafQM.ofInt] <;> norm_num

theorem eB_mul : eB * cB = 1 := by
  ext <;> simp [cB, eB, LeafQM.ofInt] <;> norm_num

/-- `c` as a unit of `𝒪`. -/
def cO : (LeafQM.O)ˣ := ⟨⟨cB, ⟨_, rfl⟩⟩, ⟨eB, ⟨_, rfl⟩⟩, Subtype.ext cB_mul, Subtype.ext eB_mul⟩

theorem cO_inv_val : (((uU cO)⁻¹ : BAQˣ) : BAQ) = bEmb eB := rfl

theorem cO_val : ((uU cO : BAQˣ) : BAQ) = bEmb cB := rfl

/-- `c⁻¹ = (1 + i + j) + 3·(−(1+j)/2)` in `𝒪`. -/
theorem eB_eq : eB = LeafQM.ofInt cc + 3 * LeafQM.ofInt ![0, 0, -1, 0] := by
  rw [← ofInt_three_smul, LeafQM.ofInt_add]
  unfold eB cc
  congr 1
  funext i; fin_cases i <;> rfl

theorem cO_inv_eq : (((uU cO)⁻¹ : BAQˣ) : BAQ) = bEmb (LeafQM.ofInt cc) + 3 * bEmb (LeafQM.ofInt ![0, 0, -1, 0]) := by
  rw [cO_inv_val, eB_eq, map_add, map_mul, map_ofNat]

theorem yc_mem : bEmb (LeafQM.ofInt ![0, 0, -1, 0]) ∈ OhatQ := bEmb_mem_of_inO ⟨_, rfl⟩

/-- **`q̂(s) = c⁻¹ k` with `k ∈ K₃`** for dcy3-used's `h = q̂(s₄) ≡ 1 + i + j mod 3`. -/
theorem h4_K3 : uU cO * qHatU q4 s4 ∈ K3Q := by
  have c3 : ∀ z : BAQ, z * 3 = 3 * z := fun z => (Commute.ofNat_right z 3).eq
  have hcc : bEmb cB * bEmb (LeafQM.ofInt cc) = 1 - 3 * bEmb (cB * LeafQM.ofInt ![0, 0, -1, 0]) := by
    have e1 : LeafQM.ofInt cc = eB - 3 * LeafQM.ofInt ![0, 0, -1, 0] := by rw [eB_eq]; abel
    rw [← map_mul, e1, mul_sub, cB_mul, map_sub, map_one, map_mul, map_mul, map_ofNat, map_mul]
    rw [← mul_assoc (bEmb cB) 3, c3]; noncomm_ring
  refine ⟨?_, ?_, bEmb cB * qHat q4 b4 - bEmb (cB * LeafQM.ofInt ![0, 0, -1, 0]), ?_, ?_⟩
  · rw [Units.val_mul]; exact OhatQ_mul (uU_mem cO).1 h4_mem.1
  · rw [mul_inv_rev, Units.val_mul]; exact OhatQ_mul h4_mem.2 (uU_mem cO).2
  · rw [sub_eq_add_neg]
    exact OhatQ_add (OhatQ_mul (uU_mem cO).1 yh_mem) (OhatQ_neg (bEmb_mem_of_inO ⟨_, LeafQM.ofInt_mul _ _⟩))
  · rw [Units.val_mul, cO_val, h4_eq, mul_add, hcc, ← mul_assoc (bEmb cB) 3, c3]
    noncomm_ring

/-! ## §5 Connectedness -/

/-- **`Y` is connected**, for a fine witness with the chain's Hecke automorphisms, given a family `τ ↦ y_τ` with open
preimages whose object is `T(τ, 1)`, Shimura's reciprocity law on objects and the proved glue. -/
theorem connected_of_family {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ) (hHk : R1heckeProps Y Φ) (hS : QMReciprocityL3)
    (hD : UnifDetermines) (hC : ComplexUnifL3) (y : UpperHalfPlane → (fieldPt ℂ ⟶ Y))
    (hopen : ∀ U : Y.left.Opens, IsOpen {τ | ShimuraSplit.ptC (y τ).left ∈ U})
    (hlev : ∀ τ, ∃ P : QML3 ℂ, Φ ℂ (y τ) = M3.mk P ∧ MIsAt P τ 1) : ConnectedSpace Y.left := by
  have : IsProper Y.hom := h1.1
  obtain ⟨-, -, -, hnat, -, -⟩ := h1
  obtain ⟨ε, δ, hrec⟩ := hS
  obtain ⟨e, he⟩ := hHk.2 cO
  -- the second family
  let B : UpperHalfPlane → (fieldPt ℂ ⟶ Y) := fun τ => y τ ≫ e.hom
  have hopenB := isOpen_comp y hopen e.hom
  have hlevB : ∀ τ, ∃ P : QML3 ℂ, Φ ℂ (B τ) = M3.mk P ∧ MIsAt P τ (uU cO)⁻¹ := by
    intro τ
    obtain ⟨P, hP, hM⟩ := hlev τ
    refine ⟨P.rightMul cO, ?_, ?_⟩
    · show Φ ℂ (y τ ≫ e.hom) = _
      rw [he ℂ (y τ), hP]; rfl
    · have := mIsAt_rightMul cO hM
      rwa [one_mul] at this
  -- reciprocity at `τ₀ = √2 + i`
  have hgal : ShimuraSplit.ptC (B tau0).left = ShimuraSplit.ptC (y tau0).left := by
    obtain ⟨s', hs'⟩ : ∃ s' : IdeleGroup (𝓞 K4) K4, qHatU q4 s' ^ (ε : ℤ) = qHatU q4 s4 := by
      rcases Int.units_eq_one_or ε with rfl | rfl
      · exact ⟨s4, by simp⟩
      · exact ⟨s4⁻¹, by simp⟩
    obtain ⟨σ, hσ⟩ := exists_sigma_artinCondC (if δ then kappa0 else (starRingEnd ℂ).comp kappa0) s'
    obtain ⟨P, hP, hM⟩ := hlev tau0
    obtain ⟨P', hP', hbc⟩ := hnat ℂ ℂ (σ : ℂ →+* ℂ).toRatAlgHom (y tau0) P hP
    have h4 := hrec K4 finrank_K4 _ q4 tau0 (isCM_delta δ) σ s' hσ 1 P P' hbc hM
    rw [mul_one, hs'] at h4
    have hdc := dcRel_K3 tau0 (uU cO)⁻¹ (uU cO * qHatU q4 s4) h4_K3
    rw [inv_mul_cancel_left] at hdc
    have h5 : MIsAt P' tau0 (uU cO)⁻¹ := dcRelTransport_proof P' tau0 _ tau0 _ hdc h4
    obtain ⟨Q, hQ, hMQ⟩ := hlevB tau0
    have h6 : M3.mk P' = M3.mk Q := hD P' Q tau0 _ h5 hMQ
    have h7 : galPt σ (y tau0) = B tau0 := by
      apply (Φ ℂ).injective
      show Φ ℂ (fieldMap (σ : ℂ →+* ℂ).toRatAlgHom ≫ y tau0) = _
      rw [hP', h6, hQ]
    rw [← h7, ptC_galPt]
  -- every `ℂ`-point is in one of the two families
  have hcU : (uU cO)⁻¹ ∈ OhatU := ⟨(uU_mem cO).2, by rw [inv_inv]; exact (uU_mem cO).1⟩
  have hcover : ∀ y' : fieldPt ℂ ⟶ Y, ∃ τ, y' = y τ ∨ y' = B τ := by
    intro y'
    obtain ⟨P', hP'⟩ := Quotient.exists_rep (Φ ℂ y')
    obtain ⟨τ, u, hu, hM⟩ := hC P'
    obtain ⟨γ, hγ, k, hk, hcase⟩ := decomp3 hcU yc_mem cO_inv_eq hu
    have hγ0 : ShimuraGlue.nrdQ ℚ γ ≠ 0 := by rw [hγ]; norm_num
    have hγp : 0 < ShimuraGlue.nrdQ ℚ γ := by rw [hγ]; norm_num
    refine ⟨(iotaGL γ hγ0)⁻¹ • τ, ?_⟩
    rcases hcase with hA | hB
    · have hdc : DCRel ((iotaGL γ hγ0)⁻¹ • τ) 1 τ u :=
        ⟨γ, hγp, ⟨iotaGL γ hγ0, iotaGL_coe _ _, smul_inv_smul _ _⟩, k, hk, by
          rw [hA, Units.val_one, mul_one]⟩
      have hM' := dcRelTransport_proof P' _ 1 τ u hdc hM
      obtain ⟨Q, hQ, hMQ⟩ := hlev ((iotaGL γ hγ0)⁻¹ • τ)
      refine Or.inl ((Φ ℂ).injective ?_)
      rw [hQ, ← hD P' Q _ 1 hM' hMQ]
      exact hP'.symm
    · have hdc : DCRel ((iotaGL γ hγ0)⁻¹ • τ) (uU cO)⁻¹ τ u :=
        ⟨γ, hγp, ⟨iotaGL γ hγ0, iotaGL_coe _ _, smul_inv_smul _ _⟩, k, hk, hB⟩
      have hM' := dcRelTransport_proof P' _ _ τ u hdc hM
      obtain ⟨Q, hQ, hMQ⟩ := hlevB ((iotaGL γ hγ0)⁻¹ • τ)
      refine Or.inr ((Φ ℂ).injective ?_)
      rw [hQ, ← hD P' Q _ _ hM' hMQ]
      exact hP'.symm
  -- conclusion
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨ShimuraSplit.ptC (y tau0).left⟩, fun U hU => ?_⟩
  have hall : ∀ y' : fieldPt ℂ ⟶ Y,
      (ShimuraSplit.ptC y'.left ∈ U ↔ ShimuraSplit.ptC (y tau0).left ∈ U) := by
    intro y'
    obtain ⟨τ, rfl | rfl⟩ := hcover y'
    · exact tind y hopen U hU τ tau0
    · rw [tind B hopenB U hU τ tau0, hgal]
  by_contra hne
  rw [not_or] at hne
  obtain ⟨a, ha⟩ := exists_C_point Y U hU.isOpen (Set.nonempty_iff_ne_empty.2 hne.1)
  obtain ⟨b, hb⟩ := exists_C_point Y Uᶜ hU.isClosed.isOpen_compl (Set.nonempty_compl.2 hne.2)
  exact hb ((hall b).2 ((hall a).1 ha))

/-! ## §6 The three uses of the composite -/

/-- **`Y₃` is connected (dcy3-used's used form) from the new leaf and `MainTheoremCM`.** -/
theorem y3ConnectedAb_of_L3 (hH : ShimuraHolFamilyL3) (hM : QMRecPrinted.MainTheoremCM)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hMum : AvSplit.MumfordTorsionAlgClosed) (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) :
    DCY3Used.Y3ConnectedAb := by
  obtain ⟨Y, Φ, h1, y, hhol, g₀, hg₀, hlev⟩ := hH
  have h1' : R1fpProps Y Φ := by
    rw [LeafQM.AV.R1UnivRigid.r1fpProps_eq_ab_gl (LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw hGL)]
    exact h1
  have hHk : R1heckeProps Y Φ := HDec.QMSplit.Moduli.heckeOfFine_proof Y Φ h1'
  obtain ⟨y', hop', hlev'⟩ := family_one hHk y hhol.1 hg₀ hlev
  exact ⟨Y, Φ, h1, connected_of_family h1 hHk (QMRecPrinted.qmReciprocityL3_of_textbook hM hUL hG)
    (unifDetermines_of (AvSplit.Final.h69 hUL hG)) (complexUnifL3_of_textbook hUL hG hMum) y' hop' hlev'⟩

/-- **The chain's `TSHecke.Y3Connected`** (the term that replaces `DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw
r.shimuraMainThmIDeligneY3AbU` in dcy3-used's bypass). -/
theorem y3Connected_of_L3 (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) (hH : ShimuraHolFamilyL3)
    (hM : QMRecPrinted.MainTheoremCM) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) : HDec.TSHecke.Y3Connected :=
  y3Connected_of_ab_gl (LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw hGL)
    (y3ConnectedAb_of_L3 hH hM hUL hG hMum hGL)

/-- The new leaf implies shimura-split2's `ShimuraHolFamilyAb` (forget the level structure). -/
theorem shimuraHolFamilyAb_of_L3 (hH : ShimuraHolFamilyL3) : ShimuraHolFamilyAb := by
  obtain ⟨Y, Φ, h1, y, hhol, g₀, hg₀, hlev⟩ := hH
  refine ⟨Y, Φ, h1, y, fun τ => ?_, hhol⟩
  obtain ⟨P, hP, hM⟩ := hlev τ
  exact ⟨P, hP, unif_of_mIsAt_unit hg₀ hM⟩

/-- **The field `shimuraFamilyAb`** from the new leaf. -/
theorem shimuraFamilyAb_of_L3 (hH : ShimuraHolFamilyL3) : HDec.QMSplit.Moduli.ShimuraFamilyAb :=
  shimuraFamilyAb_of_hol (shimuraHolFamilyAb_of_L3 hH)

/-- **The field `rayClassCMAb`** from the new leaf (only its fine witness is used) and `MainTheoremCM`. -/
theorem rayClassCMAb_of_L3 (hH : ShimuraHolFamilyL3) (hM : QMRecPrinted.MainTheoremCM)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hMum : AvSplit.MumfordTorsionAlgClosed) : ShimuraGlue.Ray.RayClassCMAb :=
  rayClassCMAb_of_printed (shimuraHolFamilyAb_of_L3 hH) (QMRecPrinted.qmReciprocityL3_of_textbook hM hUL hG)
    hUL hG hMum

/-- **Everything the composite `ShimuraMainThmIDeligneY3AbU` is used for**, from `ShimuraHolFamilyL3`,
`MainTheoremCM`, the textbook fields and `mumfordGroupLaw`. -/
theorem compositeUses_of_L3 (hH : ShimuraHolFamilyL3) (hM : QMRecPrinted.MainTheoremCM)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hMum : AvSplit.MumfordTorsionAlgClosed) (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) :
    ShimuraGlue.Ray.RayClassCMAb ∧ HDec.QMSplit.Moduli.ShimuraFamilyAb ∧ HDec.TSHecke.Y3Connected :=
  ⟨rayClassCMAb_of_L3 hH hM hUL hG hMum, shimuraFamilyAb_of_L3 hH, y3Connected_of_L3 hGL hH hM hUL hG hMum⟩

end CompositeOut

end

#print axioms CompositeOut.y3ConnectedAb_of_L3
#print axioms CompositeOut.y3Connected_of_L3
#print axioms CompositeOut.shimuraFamilyAb_of_L3
#print axioms CompositeOut.rayClassCMAb_of_L3
#print axioms CompositeOut.compositeUses_of_L3
