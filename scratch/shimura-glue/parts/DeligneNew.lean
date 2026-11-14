/-! # shimura-glue: Deligne's `π₀` in printed form; `DeligneComponentsY3`, `DeligneComponentsX6` from it -/

namespace ShimuraGlue

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

attribute [local instance 2000] instAlgebraAdicCompletion

/-- **The display of Deligne's theorem on `π₀` for `Sh_K(B^×)`** (with its Galois action), for a
`ℚ`-scheme `Y` and a compact open `K ⊆ (B ⊗ 𝔸_f)^×`: a bijection
`c : π₀(Y ×_ℚ ℚ̄) ≃ ℚ^×_{>0} \ 𝔸_f^× / nrd(K)` under which `σ ∈ Aut(ℚ̄/ℚ)` acts by multiplication by
the class of `u^ε` for every idele `u ∈ ℤ̂^×` whose `p`-components are the `p`-adic cyclotomic
characters of `σ` (Mathlib's `cyclotomicCharacter`), for a fixed sign `ε = ±1`.

* `π₀(Y ×_ℚ ℚ̄)`: Mathlib's `ConnectedComponents` of the scheme `Y ×_{Spec ℚ} Spec ℚ̄`
  (`ShimuraSplit.baseQbar`); `σ` acts by `id × Spec σ` (`ShimuraSplit.galActπ₀`).
* `𝔸_f = FiniteAdeleRing ℤ ℚ`, `B ⊗ 𝔸_f = QuaternionAlgebra 𝔸_f 2 0 (−3)`, `nrd = x x̄`
  (`nrdQ_eq_mul_star`), `ℚ^×_{>0} = posRat`, the double coset space `Pi0 K`.
* The idele condition `u_v = χ_p(σ)` (via Mathlib's `padicEquiv : ℚ_v ≅ ℚ_p`) is the reciprocity map
  of `ℚ` made explicit: `art_ℚ(u)` acts on `μ_∞` by `ζ ↦ ζ^{u^{∓1}}` (sign by normalization), so the
  ideles `s` with `art(s) = σ|ℚ^ab` are `ℚ^×_{>0}·u^{±1}`; the sign `ε` absorbs both the normalization
  of `art` and the left/right convention of `galActπ₀`. -/
def DelignePi0 (Y : Over (Spec (CommRingCat.of ℚ))) (K : Subgroup BAfˣ) : Prop :=
  ∃ (c : _root_.ConnectedComponents (ShimuraSplit.baseQbar Y) ≃ Pi0 K) (ε : ℤˣ),
    ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (u : Afˣ),
      (∀ v : Place, (u : Af) v = (adicCompletion.padicEquiv (R := ℤ) v).symm
        ((cyclotomicCharacter Qbar (primesEquiv v) σ.toRingEquiv : ℤ_[primesEquiv v]) :
          ℚ_[primesEquiv v])) →
      ∀ z : _root_.ConnectedComponents (ShimuraSplit.baseQbar Y),
        c (ShimuraSplit.galActπ₀ Y σ z) = (QuotientGroup.mk u : Pi0 K) ^ (ε : ℤ) * c z

/-- **LEAF (Deligne's theorem on the connected components of a Shimura variety and the Galois action on
them; printed form, at level `K₃` on the canonical model `Y₃`).**

*Published statement*: P. Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), Thm 2.4 and §3
(reciprocity on `π₀`), and *Variétés de Shimura*, Proc. Sympos. Pure Math. 33 (1979), Part 2,
2.1.3 and Thm 2.6.3 (`π₀(Sh_K(G,X)_ℂ) = G(ℚ)_+ \ G(𝔸_f) / K ≅ T(ℚ)^† \ T(𝔸_f) / ν(K)` for `G^der`
simply connected, `T = G/G^der`, with `Aut(ℂ/ℚ)` acting through the reciprocity map); also
J. S. Milne, *Introduction to Shimura varieties* (2005), Thm 5.17 and Thm 13.6 (locators UNVERIFIED, no
network). For `G = B^×` (`B` indefinite, `G^der = SL₁(B)` simply connected, `ν = nrd`, `T = 𝔾_m`,
`T(ℚ)^† = ℚ^×_{>0}`) this is the display `DelignePi0 Y K` for `Y = Sh_K`.

*Lean form*: some fine witness `(Y, Φ)` of the moduli clause lists (`R1fpProps`: the canonical model
`Y₃ = Sh_{K₃}` with its moduli interpretation, as in `CanonicalModelY3`) satisfies `DelignePi0 Y K3`, where
`K3 = ker(𝒪̂^× → (𝒪̂/3𝒪̂)^×)` is the level of the kernel's `Level3`.

*Reading*: printed form, with (i) the reciprocity map of `ℚ` written through the cyclotomic character,
and (ii) `π₀` of `Sh_K ⊗ ℚ̄` in the Zariski topology, which equals `π₀(Sh_K(ℂ))` (finite type over an
algebraically closed field; GAGA). Not stronger than the print. -/
def DeligneComponentsY3Printed : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ DelignePi0 Y K3

/-- **LEAF (Deligne's theorem, printed form, at level `𝒪̂^×` on the canonical model `X₆ = X₀(6,1)`).**
Same source and reading as `DeligneComponentsY3Printed`; the witness is a coarse witness
(`X6Props`: `X₆ = Sh_{𝒪̂^×}` with the coarse moduli interpretation of its `ℚ̄`-points) and the level is
`Kfull = 𝒪̂^×`. -/
def DeligneComponentsX6Printed : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ DelignePi0 X Kfull

instance : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

theorem zmod3_zpow (x : (ZMod 3)ˣ) (ε : ℤˣ) : x ^ (ε : ℤ) = x := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · have : ∀ y : (ZMod 3)ˣ, y⁻¹ = y := by decide
    simp [this]

/-- **`DeligneComponentsY3` (shimura-split) from the printed leaf**, by the computation
`ℚ^×_{>0} \ 𝔸_f^× / nrd(K₃) ≅ (ℤ/3)^×` (`pi0K3Equiv`) and `χ(χ_cyc(σ)) = χ₃(σ)` (`chi_cycU`). -/
theorem deligneComponentsY3_of_printed (h : DeligneComponentsY3Printed) :
    ShimuraSplit.DeligneComponentsY3 := by
  obtain ⟨Y, Φ, h1, c, ε, hc⟩ := h
  refine ⟨Y, Φ, h1, c.trans pi0K3Equiv.toEquiv, fun σ z => ?_⟩
  have := hc σ (cycU σ.toRingEquiv) (fun v => cycU_apply _ v) z
  simp only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, this, map_mul,
    map_zpow, pi0K3Equiv_mk]
  rw [chi_cycU ShimuraSplit.card_mu3, zmod3_zpow]
  rfl

/-- A space whose `π₀` is a nonempty subsingleton is connected. -/
theorem connectedSpace_of_subsingleton {T : Type*} [TopologicalSpace T] [Nonempty T]
    (h : Subsingleton (_root_.ConnectedComponents T)) : ConnectedSpace T := by
  haveI : PreconnectedSpace T := by
    rw [preconnectedSpace_iff_connectedComponent]
    intro x
    apply Set.eq_univ_of_forall
    intro y
    have : ConnectedComponents.mk y = ConnectedComponents.mk x := Subsingleton.elim _ _
    rw [ConnectedComponents.coe_eq_coe] at this
    rw [← this]; exact mem_connectedComponent
  exact ⟨inferInstance⟩

/-- **`DeligneComponentsX6` (shimura-split) from the printed leaf**, by the computation
`ℚ^×_{>0} \ 𝔸_f^× / nrd(𝒪̂^×) = 1` (`pi0_Kfull_eq_one`: `𝔸_f^× = ℚ^×_{>0} ℤ̂^×` and
`nrd(𝒪̂^×) = ℤ̂^×`). -/
theorem deligneComponentsX6_of_printed (h : DeligneComponentsX6Printed) :
    HDec.QMSplit.Moduli.DeligneComponentsX6 := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, c, -, -⟩ := h
  refine ⟨Y, Φ, X, Ψ, fY, h1, h6, ?_⟩
  obtain ⟨x⟩ := h6.2.2.1
  haveI : Nonempty (ShimuraSplit.baseQbar X) := by
    let s : Spec (CommRingCat.of Qbar) ⟶ ShimuraSplit.baseQbar X :=
      pullback.lift x.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w x)
    obtain ⟨pt⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of Qbar)))
    exact ⟨s pt⟩
  exact connectedSpace_of_subsingleton c.subsingleton

end ShimuraGlue

#print axioms ShimuraGlue.deligneComponentsY3_of_printed
#print axioms ShimuraGlue.deligneComponentsX6_of_printed
