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

namespace CompositeOutL3

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
def uU : (LeafQM.O)ˣ →* BAQˣ :=
  Units.map ((bEmb : LeafQM.B →ₐ[ℚ] BAQ).toRingHom.comp LeafQM.O.subtype).toMonoidHom

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

/-! ## §7 Without the level structure: shimura-split2's `ShimuraHolFamilyAb` suffices

The family of `ShimuraHolFamilyAb` has objects `ℂ²/Λ_τ` as QM pairs; its level structure `c_τ ∈ 𝒪^×/(≡ 1 mod 3)`
may depend on `τ`. Put `A^w_τ = y_τ ≫ e_w` (`e_w` the Hecke automorphism of `R1heckeProps`); its object is
`T(τ, (w c_τ)⁻¹)`, and `χ(w) = [A^w_τ ∈ U]` does not depend on `τ`. Three relations on `χ`:

* (classes) `χ` depends only on `w mod 3`;
* (reciprocity at `τ₁ = √2 + i`, the CM point of `ℚ(i)`) `χ(w) = χ(w a)`, `a = c₁ c c₁⁻¹`, `c ≡ (1+i+j)⁻¹`;
* (the elliptic point `τ₂ = i√3` of `ω = (1+j)/2`, order 6) `χ(w) = χ(w b)`, `b = c₂ ω⁻¹ c₂⁻¹`.

The conjugators `c₁ = c_{τ₁}`, `c₂ = c_{τ₂}` are unknown. A `decide` computation in `(𝒪/3𝒪)^×` (72 elements) shows
that the class `c` (order 8) and the square of any conjugate of `ω⁻¹` (order 3) generate everything, with an explicit
word for every class (tables `nList`, `tab2`, from `scratch/composite-out/py/classes.py`). So `χ` is constant. -/

/-! ### Class tables in `(𝒪/3𝒪)^×` (coordinates of `LeafQM.ofInt`, product `ShimuraGlue.mulCoordR`) -/

/-- Coordinates mod 3. -/
abbrev C3 := Fin 4 → ZMod 3
/-- The class of `1`. -/
def e1C : C3 := ![1, 0, 0, 0]
/-- The product of classes. -/
def mulC (a b : C3) : C3 := ShimuraGlue.mulCoordR a b
/-- Powers of a class. -/
def pwC (a : C3) : ℕ → C3
  | 0 => e1C
  | n + 1 => mulC (pwC a n) a
/-- The class of `c = 1/2 + i − j/2` (order 8). -/
def cbarC : C3 := ![1, 1, 2, 0]
/-- The class of `ω⁻¹ = 1/2 − j/2` (order 6). -/
def wbarC : C3 := ![1, 0, 2, 0]
/-- The inverse of a unit class: `nrd(a) · ā`. -/
def inv3 (a : C3) : C3 := fun i => ShimuraGlue.N4 a * (![a 0 + a 2, -a 1, -a 2, -a 3] : C3) i
def tab2 : Fin 4 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![0, 0, 0], ![2, 1, 6], ![2, 1, 2]], ![![1, 0, 4], ![1, 1, 3], ![2, 0, 1]], ![![1, 0, 0], ![2, 0, 5], ![1, 1, 7]]], ![![![0, 1, 2], ![0, 0, 0], ![1, 1, 6]], ![![1, 1, 1], ![1, 2, 4], ![2, 2, 3]], ![![0, 0, 7], ![1, 1, 0], ![0, 2, 5]]], ![![![0, 1, 6], ![1, 1, 2], ![0, 0, 0]], ![![0, 0, 3], ![0, 2, 1], ![1, 1, 4]], ![![1, 1, 5], ![2, 2, 7], ![1, 2, 0]]]],
    ![![![![0, 0, 0], ![0, 1, 5], ![2, 0, 7]], ![![0, 0, 0], ![2, 0, 6], ![2, 2, 2]], ![![2, 0, 4], ![0, 2, 3], ![1, 2, 1]]], ![![![1, 2, 7], ![0, 1, 0], ![1, 0, 5]], ![![0, 2, 2], ![0, 0, 0], ![1, 0, 6]], ![![0, 0, 1], ![2, 2, 4], ![1, 0, 3]]], ![![![2, 2, 5], ![0, 1, 7], ![0, 2, 0]], ![![0, 0, 6], ![1, 2, 2], ![0, 0, 0]], ![![2, 1, 3], ![2, 1, 1], ![2, 1, 4]]]],
    ![![![![0, 0, 4], ![2, 0, 3], ![0, 1, 1]], ![![2, 0, 0], ![1, 2, 5], ![0, 2, 7]], ![![0, 0, 0], ![2, 2, 6], ![2, 0, 2]]], ![![![2, 2, 1], ![0, 2, 4], ![0, 1, 3]], ![![2, 1, 7], ![2, 1, 0], ![2, 1, 5]], ![![0, 0, 2], ![0, 0, 0], ![1, 2, 6]]], ![![![1, 2, 3], ![1, 0, 1], ![0, 1, 4]], ![![0, 0, 5], ![1, 0, 7], ![2, 2, 0]], ![![0, 2, 6], ![1, 0, 2], ![0, 0, 0]]]]],
  ![![![![![0, 0, 0], ![1, 1, 6], ![1, 1, 2]], ![![0, 2, 4], ![1, 2, 3], ![0, 1, 1]], ![![0, 2, 0], ![0, 1, 5], ![1, 2, 7]]], ![![![1, 0, 2], ![0, 0, 0], ![1, 2, 6]], ![![1, 2, 1], ![2, 2, 4], ![2, 1, 3]], ![![0, 0, 7], ![1, 2, 0], ![2, 0, 5]]], ![![![1, 0, 6], ![1, 2, 2], ![0, 0, 0]], ![![0, 0, 3], ![2, 0, 1], ![1, 2, 4]], ![![1, 2, 5], ![2, 1, 7], ![2, 2, 0]]]],
    ![![![![0, 0, 0], ![1, 0, 5], ![0, 1, 7]], ![![0, 0, 0], ![0, 1, 6], ![2, 1, 2]], ![![0, 1, 4], ![2, 0, 3], ![2, 2, 1]]], ![![![2, 2, 7], ![1, 0, 0], ![0, 2, 5]], ![![2, 0, 2], ![0, 0, 0], ![0, 2, 6]], ![![0, 0, 1], ![2, 1, 4], ![0, 2, 3]]], ![![![2, 1, 5], ![1, 0, 7], ![2, 0, 0]], ![![0, 0, 6], ![2, 2, 2], ![0, 0, 0]], ![![1, 1, 3], ![1, 1, 1], ![1, 1, 4]]]],
    ![![![![0, 0, 4], ![0, 1, 3], ![1, 0, 1]], ![![0, 1, 0], ![2, 2, 5], ![2, 0, 7]], ![![0, 0, 0], ![2, 1, 6], ![0, 1, 2]]], ![![![2, 1, 1], ![2, 0, 4], ![1, 0, 3]], ![![1, 1, 7], ![1, 1, 0], ![1, 1, 5]], ![![0, 0, 2], ![0, 0, 0], ![2, 2, 6]]], ![![![2, 2, 3], ![0, 2, 1], ![1, 0, 4]], ![![0, 0, 5], ![0, 2, 7], ![2, 1, 0]], ![![2, 0, 6], ![0, 2, 2], ![0, 0, 0]]]]],
  ![![![![![0, 0, 0], ![2, 2, 6], ![2, 2, 2]], ![![0, 1, 4], ![2, 1, 3], ![0, 2, 1]], ![![0, 1, 0], ![0, 2, 5], ![2, 1, 7]]], ![![![2, 0, 2], ![0, 0, 0], ![2, 1, 6]], ![![2, 1, 1], ![1, 1, 4], ![1, 2, 3]], ![![0, 0, 7], ![2, 1, 0], ![1, 0, 5]]], ![![![2, 0, 6], ![2, 1, 2], ![0, 0, 0]], ![![0, 0, 3], ![1, 0, 1], ![2, 1, 4]], ![![2, 1, 5], ![1, 2, 7], ![1, 1, 0]]]],
    ![![![![0, 0, 0], ![2, 0, 5], ![0, 2, 7]], ![![0, 0, 0], ![0, 2, 6], ![1, 2, 2]], ![![0, 2, 4], ![1, 0, 3], ![1, 1, 1]]], ![![![1, 1, 7], ![2, 0, 0], ![0, 1, 5]], ![![1, 0, 2], ![0, 0, 0], ![0, 1, 6]], ![![0, 0, 1], ![1, 2, 4], ![0, 1, 3]]], ![![![1, 2, 5], ![2, 0, 7], ![1, 0, 0]], ![![0, 0, 6], ![1, 1, 2], ![0, 0, 0]], ![![2, 2, 3], ![2, 2, 1], ![2, 2, 4]]]],
    ![![![![0, 0, 4], ![0, 2, 3], ![2, 0, 1]], ![![0, 2, 0], ![1, 1, 5], ![1, 0, 7]], ![![0, 0, 0], ![1, 2, 6], ![0, 2, 2]]], ![![![1, 2, 1], ![1, 0, 4], ![2, 0, 3]], ![![2, 2, 7], ![2, 2, 0], ![2, 2, 5]], ![![0, 0, 2], ![0, 0, 0], ![1, 1, 6]]], ![![![1, 1, 3], ![0, 1, 1], ![2, 0, 4]], ![![0, 0, 5], ![0, 1, 7], ![1, 2, 0]], ![![1, 0, 6], ![0, 1, 2], ![0, 0, 0]]]]],
  ![![![![![0, 0, 0], ![1, 2, 6], ![1, 2, 2]], ![![2, 0, 4], ![2, 2, 3], ![1, 0, 1]], ![![2, 0, 0], ![1, 0, 5], ![2, 2, 7]]], ![![![0, 2, 2], ![0, 0, 0], ![2, 2, 6]], ![![2, 2, 1], ![2, 1, 4], ![1, 1, 3]], ![![0, 0, 7], ![2, 2, 0], ![0, 1, 5]]], ![![![0, 2, 6], ![2, 2, 2], ![0, 0, 0]], ![![0, 0, 3], ![0, 1, 1], ![2, 2, 4]], ![![2, 2, 5], ![1, 1, 7], ![2, 1, 0]]]],
    ![![![![0, 0, 0], ![0, 2, 5], ![1, 0, 7]], ![![0, 0, 0], ![1, 0, 6], ![1, 1, 2]], ![![1, 0, 4], ![0, 1, 3], ![2, 1, 1]]], ![![![2, 1, 7], ![0, 2, 0], ![2, 0, 5]], ![![0, 1, 2], ![0, 0, 0], ![2, 0, 6]], ![![0, 0, 1], ![1, 1, 4], ![2, 0, 3]]], ![![![1, 1, 5], ![0, 2, 7], ![0, 1, 0]], ![![0, 0, 6], ![2, 1, 2], ![0, 0, 0]], ![![1, 2, 3], ![1, 2, 1], ![1, 2, 4]]]],
    ![![![![0, 0, 4], ![1, 0, 3], ![0, 2, 1]], ![![1, 0, 0], ![2, 1, 5], ![0, 1, 7]], ![![0, 0, 0], ![1, 1, 6], ![1, 0, 2]]], ![![![1, 1, 1], ![0, 1, 4], ![0, 2, 3]], ![![1, 2, 7], ![1, 2, 0], ![1, 2, 5]], ![![0, 0, 2], ![0, 0, 0], ![2, 1, 6]]], ![![![2, 1, 3], ![2, 0, 1], ![0, 2, 4]], ![![0, 0, 5], ![2, 0, 7], ![1, 1, 0]], ![![0, 1, 6], ![2, 0, 2], ![0, 0, 0]]]]]]
def nList : Fin 4 → Fin 4 → ZMod 3 := ![![0, 0, 2, 0], ![1, 1, 0, 1], ![1, 2, 0, 2], ![2, 0, 1, 0]]
/-- The class of the word `n^{e₁} (c n c⁷)^{e₂} c^k`. -/
def wordC (n : C3) (t : Fin 3 → ℕ) : C3 :=
  mulC (mulC (pwC n (t 0)) (pwC (mulC (mulC cbarC n) (pwC cbarC 7)) (t 1))) (pwC cbarC (t 2))

set_option maxRecDepth 100000 in
theorem inv3_spec : ∀ a b c d : ZMod 3, ShimuraGlue.N4 ![a, b, c, d] ≠ 0 →
    mulC (inv3 ![a, b, c, d]) ![a, b, c, d] = e1C := by
  decide

set_option maxRecDepth 100000 in
/-- The square of every conjugate of `ω⁻¹` is one of four classes of order 3. -/
theorem nList_spec : ∀ a b c d : ZMod 3, ShimuraGlue.N4 ![a, b, c, d] ≠ 0 →
    ∃ j : Fin 4, pwC (mulC (mulC ![a, b, c, d] wbarC) (inv3 ![a, b, c, d])) 2 = nList j := by
  decide

set_option maxRecDepth 100000 in
/-- Every unit class is a word in `n` (any of the four) and `c`. -/
theorem tab2_spec : ∀ (j : Fin 4) (a b c d : ZMod 3), ShimuraGlue.N4 ![a, b, c, d] ≠ 0 →
    wordC (nList j) (tab2 j a b c d) = ![a, b, c, d] := by
  decide

theorem eta4 (a : C3) : (![a 0, a 1, a 2, a 3] : C3) = a := by
  funext i; fin_cases i <;> rfl

theorem mulC_assoc (a b c : C3) : mulC (mulC a b) c = mulC a (mulC b c) := by
  funext i; fin_cases i <;> simp [mulC, ShimuraGlue.mulCoordR] <;> ring

theorem e1C_mul (a : C3) : mulC e1C a = a := by
  funext i; fin_cases i <;> simp [mulC, e1C, ShimuraGlue.mulCoordR]

theorem mul_e1C (a : C3) : mulC a e1C = a := by
  funext i; fin_cases i <;> simp [mulC, e1C, ShimuraGlue.mulCoordR]

/-! ### Classes of units of `𝒪` -/

theorem inO_coe (w : (LeafQM.O)ˣ) : InO ((w : LeafQM.O) : LeafQM.B) := (w : LeafQM.O).2

/-- The class mod 3 of a unit of `𝒪`. -/
def cl (w : (LeafQM.O)ˣ) : C3 := red3 (Classical.choose (inO_coe w))

theorem cl_of {w : (LeafQM.O)ˣ} {n : Fin 4 → ℤ} (h : ((w : LeafQM.O) : LeafQM.B) = LeafQM.ofInt n) :
    cl w = red3 n := by
  unfold cl
  rw [DCY3Used.ofInt_injective ((Classical.choose_spec (inO_coe w)).symm.trans h)]

theorem cl_mul (w w' : (LeafQM.O)ˣ) : cl (w * w') = mulC (cl w) (cl w') := by
  obtain ⟨n, hn⟩ := inO_coe w
  obtain ⟨n', hn'⟩ := inO_coe w'
  rw [cl_of hn, cl_of hn', cl_of (n := ShimuraGlue.mulCoordR n n')
    (by rw [Units.val_mul, Subring.coe_mul, hn, hn', DCY3Used.ofInt_mul])]
  exact mulCoordR_cast (Int.castRingHom (ZMod 3)) n n'

theorem cl_one : cl 1 = e1C := by
  rw [cl_of (n := ![1, 0, 0, 0]) (by rw [Units.val_one, Subring.coe_one, ofInt_e1]), red3_e1]; rfl

theorem cl_pow (w : (LeafQM.O)ˣ) (n : ℕ) : cl (w ^ n) = pwC (cl w) n := by
  induction n with
  | zero => rw [pow_zero, cl_one]; rfl
  | succ n ih => rw [pow_succ, cl_mul, ih]; rfl

theorem N4_cl_ne (w : (LeafQM.O)ˣ) : ShimuraGlue.N4 (cl w) ≠ 0 := by
  intro h
  have e := congrArg ShimuraGlue.N4 (show cl (w * w⁻¹) = cl 1 by rw [mul_inv_cancel])
  rw [cl_mul, cl_one, mulC, N4_mul, h, zero_mul] at e
  revert e; decide

theorem cl_inv (w : (LeafQM.O)ˣ) : cl w⁻¹ = inv3 (cl w) := by
  have h1 : mulC (inv3 (cl w)) (cl w) = e1C := by
    have := inv3_spec (cl w 0) (cl w 1) (cl w 2) (cl w 3) (by rw [eta4]; exact N4_cl_ne w)
    rwa [eta4] at this
  have h2 : mulC (cl w) (cl w⁻¹) = e1C := by rw [← cl_mul, mul_inv_cancel, cl_one]
  calc cl w⁻¹ = mulC (mulC (inv3 (cl w)) (cl w)) (cl w⁻¹) := by rw [h1, e1C_mul]
    _ = inv3 (cl w) := by rw [mulC_assoc, h2, mul_e1C]

/-- A unit `≡ 1 mod 3` is in `K₃`. -/
theorem uU_K3 {x : (LeafQM.O)ˣ} (hx : cl x = e1C) : uU x ∈ K3Q := by
  obtain ⟨n, hn⟩ := inO_coe x
  rw [cl_of hn] at hx
  have hx' : red3 n = red3 ![1, 0, 0, 0] := by rw [hx, red3_e1]; rfl
  obtain ⟨m, hm⟩ := lift3 hx'
  refine ⟨(uU_mem x).1, (uU_mem x).2, bEmb (LeafQM.ofInt m), bEmb_mem_of_inO ⟨m, rfl⟩, ?_⟩
  rw [uU_val, hn, hm, ← LeafQM.ofInt_add, ofInt_three_smul, ofInt_e1, map_add, map_one, map_mul, map_ofNat]

theorem uU_K3_of_cl {w w' : (LeafQM.O)ˣ} (h : cl w = cl w') : uU (w * w'⁻¹) ∈ K3Q := by
  apply uU_K3
  rw [cl_mul, h, ← cl_mul, mul_inv_cancel, cl_one]

/-! ### The group-theoretic step -/

/-- The unit `ω = (1 + j)/2` of `𝒪` (order 6, reduced norm 1), inverse `1/2 − j/2`. -/
def wB : LeafQM.B := ⟨1 / 2, 0, 1 / 2, 0⟩
def wBinv : LeafQM.B := ⟨1 / 2, 0, -1 / 2, 0⟩

theorem wB_mul : wB * wBinv = 1 := by ext <;> simp [wB, wBinv] <;> norm_num
theorem wBinv_mul : wBinv * wB = 1 := by ext <;> simp [wB, wBinv] <;> norm_num
theorem inO_wB : InO wB := ⟨![0, 0, 1, 0], by ext <;> simp [wB, LeafQM.ofInt]⟩
theorem wBinv_eq : wBinv = LeafQM.ofInt ![1, 0, -1, 0] := by ext <;> simp [wBinv, LeafQM.ofInt] <;> norm_num
theorem inO_wBinv : InO wBinv := ⟨_, wBinv_eq⟩

/-- `ω` as a unit of `𝒪`. -/
def wO : (LeafQM.O)ˣ := ⟨⟨wB, inO_wB⟩, ⟨wBinv, inO_wBinv⟩, Subtype.ext wB_mul, Subtype.ext wBinv_mul⟩

theorem cl_wO_inv : cl wO⁻¹ = wbarC := by
  rw [cl_of (n := ![1, 0, -1, 0]) wBinv_eq]; funext i; fin_cases i <;> rfl

theorem cl_cO : cl cO = cbarC := by
  rw [cl_of (n := ![1, 1, -1, 0]) rfl]; funext i; fin_cases i <;> rfl

/-- **A function of `w ∈ 𝒪^×` that depends only on `w mod 3` and is right-invariant under a conjugate of `c` and a
conjugate of `ω⁻¹` is constant.** -/
theorem const_of_inv' (χ : (LeafQM.O)ˣ → Prop) (hcl : ∀ w w', cl w = cl w' → (χ w ↔ χ w'))
    (c1 c2 : (LeafQM.O)ˣ) (ha : ∀ w, χ (w * (c1 * cO * c1⁻¹)) ↔ χ w)
    (hb : ∀ w, χ (w * (c2 * wO⁻¹ * c2⁻¹)) ↔ χ w) : ∀ w, χ w ↔ χ 1 := by
  let χ' : (LeafQM.O)ˣ → Prop := fun x => χ (x * c1⁻¹)
  have hcl' : ∀ x x', cl x = cl x' → (χ' x ↔ χ' x') := fun x x' h =>
    hcl _ _ (by rw [cl_mul, cl_mul, h])
  have hA : ∀ x, χ' (x * cO) ↔ χ' x := by
    intro x
    have := ha (x * c1⁻¹)
    rw [show x * c1⁻¹ * (c1 * cO * c1⁻¹) = x * cO * c1⁻¹ by group] at this
    exact this
  set v := c1⁻¹ * c2
  set t := v * wO⁻¹ * v⁻¹
  have hT : ∀ x, χ' (x * t) ↔ χ' x := by
    intro x
    have := hb (x * c1⁻¹)
    rw [show x * c1⁻¹ * (c2 * wO⁻¹ * c2⁻¹) = x * t * c1⁻¹ by simp only [t, v]; group] at this
    exact this
  have hApow : ∀ x (n : ℕ), χ' (x * cO ^ n) ↔ χ' x := by
    intro x n
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih => rw [pow_succ, ← mul_assoc, hA, ih]
  have hTpow : ∀ x (n : ℕ), χ' (x * t ^ n) ↔ χ' x := by
    intro x n
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih => rw [pow_succ, ← mul_assoc, hT, ih]
  have hBpow : ∀ x (n : ℕ), χ' (x * (cO * t ^ 2 * cO ^ 7) ^ n) ↔ χ' x := by
    intro x n
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, show x * (cO * t ^ 2 * cO ^ 7) ^ n * (cO * t ^ 2 * cO ^ 7) =
        x * (cO * t ^ 2 * cO ^ 7) ^ n * cO * t ^ 2 * cO ^ 7 by group, hApow, hTpow, hA, ih]
  -- the class of `t²` is one of the four classes of order 3
  have hclt : cl t = mulC (mulC (cl v) wbarC) (inv3 (cl v)) := by
    simp only [t]; rw [cl_mul, cl_mul, cl_wO_inv, cl_inv]
  obtain ⟨j, hj⟩ := nList_spec (cl v 0) (cl v 1) (cl v 2) (cl v 3) (by rw [eta4]; exact N4_cl_ne v)
  rw [eta4, ← hclt] at hj
  have hall : ∀ x, χ' x ↔ χ' 1 := by
    intro x
    have hx := tab2_spec j (cl x 0) (cl x 1) (cl x 2) (cl x 3) (by rw [eta4]; exact N4_cl_ne x)
    rw [eta4] at hx
    set T := tab2 j (cl x 0) (cl x 1) (cl x 2) (cl x 3)
    let W : (LeafQM.O)ˣ := (t ^ 2) ^ (T 0) * (cO * t ^ 2 * cO ^ 7) ^ (T 1) * cO ^ (T 2)
    have hW : cl W = cl x := by
      rw [← hx, ← hj]
      simp only [W, wordC, cl_mul, cl_pow, cl_cO]
    rw [hcl' x W hW.symm]
    have e : W = 1 * t ^ (2 * T 0) * (cO * t ^ 2 * cO ^ 7) ^ (T 1) * cO ^ (T 2) := by
      simp only [W, one_mul, pow_mul]
    rw [e, hApow, hBpow, hTpow]
  intro w
  have e1 : χ w ↔ χ' (w * c1) := by simp only [χ', mul_inv_cancel_right]
  have e2 : χ 1 ↔ χ' c1 := by simp only [χ', mul_inv_cancel]
  rw [e1, e2, hall, hall c1]

/-! ### The elliptic point `τ₂ = i√3` of `ω` -/

/-- `τ₂ = i√3`. -/
def tau2 : UpperHalfPlane := ⟨Complex.I * (Real.sqrt 3 : ℂ), by simp⟩

theorem heig2 : Matrix.mulVec ((BPAnalytic.QM.iota wB).map (algebraMap ℝ ℂ)) ![(tau2 : ℂ), 1] =
    ((1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2) • ![(tau2 : ℂ), 1] := by
  have h := ZInQ.Contrib.TYZGenus.Shimura.sqrt_mul_self_C 3
  push_cast at h
  ext i
  fin_cases i
  · simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, tau2, wB]
    linear_combination (-(1 / 2 : ℂ) * Complex.I ^ 2) * h + (-(3 / 2 : ℂ)) * Complex.I_sq
  · simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, tau2, wB]
    ring

theorem nrd_wB_pos : 0 < ShimuraGlue.nrdQ ℚ wB := by
  simp [ShimuraGlue.nrdQ_apply, wB]; norm_num

/-! ### Points with a given object -/

/-- `p` is the point whose object is `T(τ, d⁻¹)`. -/
def IsPt {Y : Over (Spec (CommRingCat.of ℚ))} (Φ : PtEquiv Y) (p : fieldPt ℂ ⟶ Y) (τ : UpperHalfPlane)
    (d : (LeafQM.O)ˣ) : Prop :=
  ∃ P : QML3 ℂ, Φ ℂ p = M3.mk P ∧ MIsAt P τ (uU d)⁻¹

theorem isPt_unique {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (hD : UnifDetermines)
    {p p' : fieldPt ℂ ⟶ Y} {τ : UpperHalfPlane} {d : (LeafQM.O)ˣ} (h : IsPt Φ p τ d) (h' : IsPt Φ p' τ d) :
    p = p' := by
  obtain ⟨P, hP, hM⟩ := h
  obtain ⟨P', hP', hM'⟩ := h'
  apply (Φ ℂ).injective
  rw [hP, hP', hD P P' τ _ hM hM']

theorem isPt_cl {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {p : fieldPt ℂ ⟶ Y}
    {τ : UpperHalfPlane} {d d' : (LeafQM.O)ˣ} (h : cl d = cl d') (hp : IsPt Φ p τ d) : IsPt Φ p τ d' := by
  obtain ⟨P, hP, hM⟩ := hp
  refine ⟨P, hP, ?_⟩
  have h2 := dcRel_K3 τ (uU d')⁻¹ _ (uU_K3_of_cl h.symm)
  rw [show (uU d')⁻¹ * uU (d' * d⁻¹) = (uU d)⁻¹ by rw [map_mul, map_inv]; group] at h2
  exact dcRelTransport_proof P τ _ τ _ h2 hM

theorem isPt_ell {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {p : fieldPt ℂ ⟶ Y}
    {d : (LeafQM.O)ˣ} (hp : IsPt Φ p tau2 (d * wO⁻¹)) : IsPt Φ p tau2 d := by
  obtain ⟨P, hP, hM⟩ := hp
  refine ⟨P, hP, ?_⟩
  have hdc : DCRel tau2 (uU d)⁻¹ tau2 (uU (d * wO⁻¹))⁻¹ := by
    refine dcRel_fix nrd_wB_pos tau2 heig2 _ 1 _ K3Q_one ?_
    rw [map_mul, mul_inv_rev, map_inv, inv_inv, Units.val_mul, Units.val_one, mul_one, uU_val]
    rfl
  exact dcRelTransport_proof P tau2 _ tau2 _ hdc hM

open scoped MonObj in
/-- **The level of an object with a given `ι`-compatible uniformization by `Λ_τ`**: it is `T(τ, d⁻¹)` for a unit
`d ∈ 𝒪^×` (shimura-split2's `complexUnifL3_of`, from a given uniformization; the proof is copied with the unit kept
global). -/
theorem levelUnit {P : QML3 ℂ} {τ : UpperHalfPlane} {Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    (hI : HDec.HSyn.G0Split.FibreQM.IotaCompatible P Φu) : ∃ d : (LeafQM.O)ˣ, MIsAt P τ (uU d)⁻¹ := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  set τc : ℂ := (τ : ℂ)
  obtain ⟨v, hv⟩ := hU.2.2.1 (Additive.toMul (P.e.eta 1))
  have h3v : v + v + v ∈ BPAnalytic.QM.qmLattice hτ.ne' := by
    rw [← hU.2.1, hU.1, hU.1, hv]
    show Additive.toMul (P.e.eta 1 + P.e.eta 1 + P.e.eta 1) = _
    rw [← map_add, ← map_add]
    have e : (1 + 1 + 1 : LeafQM.O) = 3 * 1 := by norm_num
    rw [e, (P.e.ker _).2 ⟨1, rfl⟩]
    rfl
  obtain ⟨b, hbO, hbv⟩ := exists_of_mem_qmLattice hτ.ne' h3v
  have hv3 : v = (3 : ℂ)⁻¹ • (iotaC b).mulVec ![τc, 1] := by
    rw [hbv]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have heta : ∀ a : LeafQM.O,
      Φu ((3 : ℂ)⁻¹ • (iotaC ((a : LeafQM.B) * b)).mulVec ![τc, 1]) = Additive.toMul (P.e.eta a) := by
    intro a
    have e1 : P.e.eta a = P.e.eta (a * 1) := by rw [_root_.mul_one]
    rw [e1, P.e.linear]
    show _ = Additive.toMul (P.e.eta 1) ≫ (P.q.iota a).hom
    have k1 := hI a v
    have k2 : (3 : ℂ)⁻¹ • (iotaC ((a : LeafQM.B) * b)).mulVec ![τc, 1] =
        (HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec v := by
      rw [hv3, Matrix.mulVec_smul, qmMat_eq, map_mul, ← Matrix.mulVec_mulVec]
    rw [k2]
    rw [hv] at k1
    exact k1
  obtain ⟨m, rfl⟩ := hbO
  have hnd : ¬ (3 : ℤ) ∣ nrdZ m := by
    rintro ⟨n, hn⟩
    let sb : LeafQM.O := ⟨star (LeafQM.ofInt m), inO_star ⟨m, rfl⟩⟩
    have h0 : P.e.eta sb = 0 := by
      have h := heta sb
      have hmem : (3 : ℂ)⁻¹ • (iotaC ((sb : LeafQM.B) * LeafQM.ofInt m)).mulVec ![τc, 1] ∈
          BPAnalytic.QM.qmLattice hτ.ne' := by
        have e : (3 : ℂ)⁻¹ • (iotaC ((sb : LeafQM.B) * LeafQM.ofInt m)).mulVec ![τc, 1] =
            n • ![τc, 1] := by
          show (3 : ℂ)⁻¹ • (iotaC (star (LeafQM.ofInt m) * LeafQM.ofInt m)).mulVec ![τc, 1] = _
          rw [star_mul_ofInt, iotaC_smul_mulVec, map_one, Matrix.one_mulVec, hn, smul_smul,
            ← Int.cast_smul_eq_zsmul ℂ]
          congr 1
          push_cast
          ring
        rw [e]
        exact Submodule.smul_mem _ _ (qmVec0_mem hτ.ne')
      have h1 := (hU.2.1 _).2 hmem
      rw [h1] at h
      exact (congrArg Additive.ofMul h).symm
    obtain ⟨c, hc⟩ := (P.e.ker sb).1 h0
    have hb3 : LeafQM.ofInt m = (3 : ℚ) • star (c : LeafQM.B) := by
      have e := congrArg (fun x : LeafQM.O => star (x : LeafQM.B)) hc
      simp only [sb, star_star, Subring.coe_mul] at e
      have hs3 : star (3 : LeafQM.B) = 3 := by ext <;> simp
      rw [e, show ((3 : LeafQM.O) : LeafQM.B) = 3 from rfl, star_mul, hs3, three_mul_eq_smulB']
    have h1 : P.e.eta 1 = 0 := by
      have hv' : v ∈ BPAnalytic.QM.qmLattice hτ.ne' := by
        rw [hv3, hb3, iotaC_smul_mulVec, smul_smul,
          show ((3 : ℂ)⁻¹ * ((3 : ℚ) : ℂ)) = 1 by norm_num, one_smul]
        exact mem_qmLattice_of_inO hτ.ne' (inO_star c.2)
      have h := (hU.2.1 v).2 hv'
      rw [hv] at h
      exact congrArg Additive.ofMul h
    obtain ⟨c', hc'⟩ := (P.e.ker 1).1 h1
    exact one_ne_three_mul c' hc'
  obtain ⟨ε, ε', d, hε, hε', hd, h1, h2, hbe⟩ := exists_unit_cong m hnd
  let dO : (LeafQM.O)ˣ := ⟨⟨ε, hε⟩, ⟨ε', hε'⟩, Subtype.ext h1, Subtype.ext h2⟩
  have hu : (uU dO)⁻¹ ∈ OhatU := ⟨(uU_mem dO).2, by rw [inv_inv]; exact (uU_mem dO).1⟩
  refine ⟨dO, Φu, by rw [vecLat_unit hu τ]; exact hU, hI, fun a => ?_⟩
  refine ⟨(a : LeafQM.B) * LeafQM.ofInt m, ⟨bEmb ((a : LeafQM.B) * (d * ε')),
    bEmb_mem_of_inO (LeafQM.O.mul_mem a.2 (LeafQM.O.mul_mem hd hε')), ?_⟩, heta a⟩
  show bEmb ((a : LeafQM.B) * LeafQM.ofInt m) * bEmb ε' = _
  have e : (a : LeafQM.B) * LeafQM.ofInt m * ε' = (a : LeafQM.B) + 3 * ((a : LeafQM.B) * (d * ε')) := by
    rw [hbe]
    have h3 : (a : LeafQM.B) * 3 = 3 * (a : LeafQM.B) := (Commute.ofNat_right _ 3).eq
    calc (a : LeafQM.B) * (ε + 3 * d) * ε' = (a : LeafQM.B) * (ε * ε') + ((a : LeafQM.B) * 3) * (d * ε') := by
          noncomm_ring
      _ = _ := by rw [h1, h3]; noncomm_ring
  rw [← map_mul, e, map_add, map_mul, map_ofNat]

/-! ### Connectedness from a family without level structure -/

/-- **`Y` is connected**, for a fine witness with the chain's Hecke automorphisms, given a family `τ ↦ y_τ` with open
preimages whose object is `ℂ²/Λ_τ` as a QM pair (any level structure), Shimura's reciprocity law on objects and the
proved glue. -/
theorem connected_of_holFamily {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ) (hHk : R1heckeProps Y Φ) (hS : QMReciprocityL3)
    (hD : UnifDetermines) (hQ : HDec.HSyn.G0Split.FibreQM.QMComplexUnif)
    (y : UpperHalfPlane → (fieldPt ℂ ⟶ Y))
    (hopen : ∀ U : Y.left.Opens, IsOpen {τ | ShimuraSplit.ptC (y τ).left ∈ U})
    (hmod : ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (y τ) = M3.mk P ∧
      ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
        IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
        HDec.HSyn.G0Split.FibreQM.IotaCompatible P Φu) : ConnectedSpace Y.left := by
  have : IsProper Y.hom := h1.1
  obtain ⟨-, -, -, hnat, -, -⟩ := h1
  obtain ⟨ε, δ, hrec⟩ := hS
  -- the level of the family at each `τ`
  have hc : ∀ τ, ∃ c : (LeafQM.O)ˣ, IsPt Φ (y τ) τ c := by
    intro τ
    obtain ⟨P, hP, Φu, hU, hI⟩ := hmod τ
    obtain ⟨d, hd⟩ := levelUnit hU hI
    exact ⟨d, P, hP, hd⟩
  choose cτ hcτ using hc
  choose E hE using hHk.2
  let A : (LeafQM.O)ˣ → UpperHalfPlane → (fieldPt ℂ ⟶ Y) := fun w τ => y τ ≫ (E w).hom
  have hA : ∀ w τ, IsPt Φ (A w τ) τ (w * cτ τ) := by
    intro w τ
    obtain ⟨P, hP, hM⟩ := hcτ τ
    refine ⟨P.rightMul w, ?_, ?_⟩
    · show Φ ℂ (y τ ≫ (E w).hom) = _
      rw [hE w ℂ (y τ), hP]; rfl
    · have := mIsAt_rightMul w hM
      rwa [show (uU (cτ τ))⁻¹ * (uU w)⁻¹ = (uU (w * cτ τ))⁻¹ by rw [map_mul, mul_inv_rev]] at this
  have hopenA : ∀ w, ∀ U : Y.left.Opens, IsOpen {τ | ShimuraSplit.ptC (A w τ).left ∈ U} :=
    fun w => isOpen_comp y hopen (E w).hom
  -- every point is some `A w τ`
  have hcover : ∀ p : fieldPt ℂ ⟶ Y, ∃ w τ, p = A w τ := by
    intro p
    obtain ⟨P', hP'⟩ := Quotient.exists_rep (Φ ℂ p)
    obtain ⟨τc, hτ, Φu, hU, hI⟩ := hQ P'
    obtain ⟨d, hd⟩ := levelUnit (τ := ⟨τc, hτ⟩) hU hI
    refine ⟨d * (cτ ⟨τc, hτ⟩)⁻¹, ⟨τc, hτ⟩, isPt_unique hD ⟨P', hP'.symm, hd⟩ ?_⟩
    have := hA (d * (cτ ⟨τc, hτ⟩)⁻¹) ⟨τc, hτ⟩
    rwa [inv_mul_cancel_right] at this
  -- reciprocity at `τ₁ = √2 + i`
  have hgal : ∀ w, ShimuraSplit.ptC (A (w * (cτ tau0 * cO * (cτ tau0)⁻¹)) tau0).left =
      ShimuraSplit.ptC (A w tau0).left := by
    intro w
    set c1 := cτ tau0
    obtain ⟨s', hs'⟩ : ∃ s' : IdeleGroup (𝓞 K4) K4, qHatU q4 s' ^ (ε : ℤ) = qHatU q4 s4 := by
      rcases Int.units_eq_one_or ε with rfl | rfl
      · exact ⟨s4, by simp⟩
      · exact ⟨s4⁻¹, by simp⟩
    obtain ⟨σ, hσ⟩ := exists_sigma_artinCondC (if δ then kappa0 else (starRingEnd ℂ).comp kappa0) s'
    obtain ⟨P, hP, hM⟩ := hA w tau0
    obtain ⟨P', hP', hbc⟩ := hnat ℂ ℂ (σ : ℂ →+* ℂ).toRatAlgHom (A w tau0) P hP
    have h4 := hrec K4 finrank_K4 _ q4 tau0 (isCM_delta δ) σ s' hσ _ P P' hbc hM
    rw [hs'] at h4
    set g := (uU (w * c1))⁻¹
    have hg : g ∈ OhatU := ⟨(uU_mem _).2, by rw [inv_inv]; exact (uU_mem _).1⟩
    have hk := conj_mem_K3Q hg h4_K3
    have hdc := dcRel_K3 tau0 (uU (w * c1 * cO))⁻¹ _ hk
    rw [show (uU (w * c1 * cO))⁻¹ * (g⁻¹ * (uU cO * qHatU q4 s4) * g) = qHatU q4 s4 * g by
      simp only [g, map_mul]; group] at hdc
    have h5 : IsPt Φ (galPt σ (A w tau0)) tau0 (w * c1 * cO) :=
      ⟨P', hP', dcRelTransport_proof P' tau0 _ tau0 _ hdc h4⟩
    have h6 := hA (w * (c1 * cO * c1⁻¹)) tau0
    rw [show w * (c1 * cO * c1⁻¹) * cτ tau0 = w * c1 * cO by simp only [c1]; group] at h6
    rw [isPt_unique hD h6 h5, ptC_galPt]
  -- the elliptic point `τ₂ = i√3`
  have hell : ∀ w, A (w * (cτ tau2 * wO⁻¹ * (cτ tau2)⁻¹)) tau2 = A w tau2 := by
    intro w
    have h6 := hA (w * (cτ tau2 * wO⁻¹ * (cτ tau2)⁻¹)) tau2
    rw [show w * (cτ tau2 * wO⁻¹ * (cτ tau2)⁻¹) * cτ tau2 = w * cτ tau2 * wO⁻¹ by group] at h6
    exact isPt_unique hD (isPt_ell h6) (hA w tau2)
  -- conclusion
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨ShimuraSplit.ptC (y tau0).left⟩, fun U hU => ?_⟩
  let χ : (LeafQM.O)ˣ → Prop := fun w => ShimuraSplit.ptC (A w tau0).left ∈ U
  have tA : ∀ w τ, ShimuraSplit.ptC (A w τ).left ∈ U ↔ χ w := fun w τ => tind (A w) (hopenA w) U hU τ tau0
  have hcl : ∀ w w', cl w = cl w' → (χ w ↔ χ w') := by
    intro w w' h
    have e : A w' tau0 = A w tau0 :=
      isPt_unique hD (isPt_cl (by rw [cl_mul, cl_mul, h]) (hA w' tau0)) (hA w tau0)
    show _ ∈ U ↔ _ ∈ U
    rw [e]
  have ha : ∀ w, χ (w * (cτ tau0 * cO * (cτ tau0)⁻¹)) ↔ χ w := by
    intro w; show _ ∈ U ↔ _ ∈ U; rw [hgal]
  have hb : ∀ w, χ (w * (cτ tau2 * wO⁻¹ * (cτ tau2)⁻¹)) ↔ χ w := by
    intro w; rw [← tA _ tau2, ← tA w tau2, hell]
  have hconst := const_of_inv' χ hcl _ _ ha hb
  have hall : ∀ p : fieldPt ℂ ⟶ Y, ShimuraSplit.ptC p.left ∈ U ↔ χ 1 := by
    intro p
    obtain ⟨w, τ, rfl⟩ := hcover p
    rw [tA, hconst]
  by_contra hne
  rw [not_or] at hne
  obtain ⟨a, ha'⟩ := exists_C_point Y U hU.isOpen (Set.nonempty_iff_ne_empty.2 hne.1)
  obtain ⟨b, hb'⟩ := exists_C_point Y Uᶜ hU.isClosed.isOpen_compl (Set.nonempty_compl.2 hne.2)
  exact hb' ((hall b).2 ((hall a).1 ha'))

/-! ## §8 The three uses of the composite from shimura-split2's leaf -/

/-- **`Y₃` is connected (dcy3-used's used form) from shimura-split2's `ShimuraHolFamilyAb` and `MainTheoremCM`.** -/
theorem y3ConnectedAb_of_hol (hH : ShimuraHolFamilyAb) (hM : QMRecPrinted.MainTheoremCM)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hMum : AvSplit.MumfordTorsionAlgClosed) (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) :
    DCY3Used.Y3ConnectedAb := by
  obtain ⟨Y, Φ, h1, y, hmod, hhol⟩ := hH
  have h1' : R1fpProps Y Φ := by
    rw [LeafQM.AV.R1UnivRigid.r1fpProps_eq_ab_gl (LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw hGL)]
    exact h1
  have hHk : R1heckeProps Y Φ := HDec.QMSplit.Moduli.heckeOfFine_proof Y Φ h1'
  have hQ : HDec.HSyn.G0Split.FibreQM.QMComplexUnif :=
    HDec.HSyn.G0Split.FibreQM.qmComplexUnif_of_textbook (AvSplit.Final.h38 hUL hMum)
      (ZInQ.HomUnify.t11a_riemannEnd_of_corr (AvSplit.Final.h69 hUL hG))
      (HDec.HSyn.G0Split.FibreQM.qmLatticeAlgebra_of_free
        (HDec.HSyn.G0Split.FibreQM.qmLatticeFree_of HDec.HSyn.G0Split.FibreQM.qmSkolemNoetherC_proof
          HDec.QMSplit.CNO.qmClassNumberOne_proof))
  exact ⟨Y, Φ, h1, connected_of_holFamily h1 hHk (QMRecPrinted.qmReciprocityL3_of_textbook hM hUL hG)
    (unifDetermines_of (AvSplit.Final.h69 hUL hG)) hQ y hhol.1 hmod⟩

/-- **The chain's `TSHecke.Y3Connected`** from `ShimuraHolFamilyAb` and `MainTheoremCM`. -/
theorem y3Connected_of_hol (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) (hH : ShimuraHolFamilyAb)
    (hM : QMRecPrinted.MainTheoremCM) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) : HDec.TSHecke.Y3Connected :=
  y3Connected_of_ab_gl (LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw hGL)
    (y3ConnectedAb_of_hol hH hM hUL hG hMum hGL)

/-- The same from shimura-split2's `∀`-form `ShimuraHolModAll` and the fine witness of `deligneComponentsX6PrintedAb`
(the leaves of the queued qmrec-printed spec). -/
theorem y3Connected_of_modAll (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw)
    (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hH : ShimuraHolModAll)
    (hM : QMRecPrinted.MainTheoremCM) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) : HDec.TSHecke.Y3Connected :=
  y3Connected_of_hol hGL (shimuraHolFamilyAb_of_all (witness_of_x6 hR) hH) hM hUL hG hMum

/-- **Everything the composite `ShimuraMainThmIDeligneY3AbU` is used for**, from shimura-split2's `ShimuraHolFamilyAb`
(itself a consequence of the composite: `ShimuraSplit2.shimuraHolFamilyAb_of_composite`), qmrec-printed's
`MainTheoremCM`, the textbook fields and `mumfordGroupLaw`. -/
theorem compositeUses_of_hol (hH : ShimuraHolFamilyAb) (hM : QMRecPrinted.MainTheoremCM)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hMum : AvSplit.MumfordTorsionAlgClosed) (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) :
    ShimuraGlue.Ray.RayClassCMAb ∧ HDec.QMSplit.Moduli.ShimuraFamilyAb ∧ HDec.TSHecke.Y3Connected :=
  ⟨rayClassCMAb_of_printed hH (QMRecPrinted.qmReciprocityL3_of_textbook hM hUL hG) hUL hG hMum,
    shimuraFamilyAb_of_hol hH, y3Connected_of_hol hGL hH hM hUL hG hMum⟩


end CompositeOutL3

end

#print axioms CompositeOutL3.y3ConnectedAb_of_L3
#print axioms CompositeOutL3.y3Connected_of_L3
#print axioms CompositeOutL3.shimuraFamilyAb_of_L3
#print axioms CompositeOutL3.rayClassCMAb_of_L3
#print axioms CompositeOutL3.compositeUses_of_L3
#print axioms CompositeOutL3.y3ConnectedAb_of_hol
#print axioms CompositeOutL3.y3Connected_of_hol
#print axioms CompositeOutL3.y3Connected_of_modAll
#print axioms CompositeOutL3.compositeUses_of_hol
