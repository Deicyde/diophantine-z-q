import ZInQKernel.Contrib.OneProof.C8Conrad
import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap

/-! # c8-conrad2: two of c8-conrad's glue Props for step C8

* `LocAlgExponentEqWeight` (diophantine_zq.tex L763-764, "removing its integral local Hodge–Tate weight") is proved
  from `TateTwistInvariantsInertia` (Tate 1967 §3.3 Thm 2 for the completion of `K^{ur}`) and Tau Ceti's local
  class field theory of `ℚ_p` (`locAlgExponentEqWeight_of_tateInertia`). Proof: a nonzero `φ ∈ H_{-w}(ψ)` gives
  `x = φ(v) ≠ 0` in `ℂ_p` with `σ(x) = χ(σ)^{w-n} x` for every `σ` in the inertia group of `K = ℚ_p(ζ_{p^k})`, since
  every such `σ` is an Artin lift of a unit `u ≡ 1 mod p^k` (`exists_unit_isArtinLift`, `cyc_of_isArtinLift`,
  `toZModPow_cyc_eq_one`); Tate's theorem forces `w = n`.
* `FiniteOfLocAlgTrivialQ` (L761-765, "class field theory over ℚ") is reduced to three smaller Props
  (`finiteOfLocAlgTrivialQ_of_pieces`): `InertiaFiniteAwayFromP` (on-the-spot), `InertiaAtPDecomp` (dictionary) and
  `CFTFiniteQ` (class field theory over `ℚ`); the local part at `p` is proved (`pow_card_eq_one_of_mem_inertia`). -/

set_option linter.style.longLine false

noncomputable section

namespace HDec.G0Galois.C8Conrad

open Module
open _root_.PkgI4 (GaloisRep GaloisChar)

section Units

variable (p : ℕ) [Fact p.Prime]

/-- A `p`-adic number of valuation one (Tau Ceti's `ValuativeRel` valuation) has norm one. -/
theorem norm_eq_one_of_valuation_eq_one (x : ℚ_[p]ˣ) (h : ValuativeRel.valuation ℚ_[p] (x : ℚ_[p]) = 1) :
    ‖(x : ℚ_[p])‖ = 1 := by
  have h1 : Padic.mulValuation (x : ℚ_[p]) = 1 := by
    have he : (ValuativeRel.valuation ℚ_[p]).IsEquiv (Padic.mulValuation (p := p)) :=
      ValuativeRel.isEquiv _ _
    exact (he.eq_one_iff_eq_one).1 h
  rw [Padic.norm_eq_zpow_log_mulValuation x.ne_zero, h1]
  simp

/-- Every lift of an element of the inertia group of `ℚ_p` represents the Artin symbol of a unit of `ℤ_p`. -/
theorem exists_unit_isArtinLift (σ : PkgI4.GQp p)
    (hσ : (show Field.absoluteGaloisGroup ℚ_[p] from σ) ∈ TauCeti.inertiaSubgroup ℚ_[p]) :
    ∃ u : ℤ_[p]ˣ, IsArtinLift p σ (unitsQp p u) := by
  have hmem : (QuotientGroup.mk' _ (show Field.absoluteGaloisGroup ℚ_[p] from σ) :
      Field.absoluteGaloisGroupAbelianization ℚ_[p]) ∈
      (TauCeti.inertiaSubgroup ℚ_[p]).map (QuotientGroup.mk' _) := ⟨_, hσ, rfl⟩
  rw [← TauCeti.ClassFieldTheory.map_artinMap_unitFiltration_zero] at hmem
  obtain ⟨y, hy, hyσ⟩ := hmem
  have hn : ‖(y : ℚ_[p])‖ = 1 :=
    norm_eq_one_of_valuation_eq_one p y ((TauCeti.mem_unitFiltration_zero y).1 hy)
  let u : ℤ_[p]ˣ := PadicInt.mkUnits hn
  refine ⟨u, ?_⟩
  have hyu : unitsQp p u = y := Units.ext rfl
  rw [IsArtinLift, hyu, hyσ]
  rfl

/-- The cyclotomic character of an Artin lift of a unit `u` is `u⁻¹` (Tau Ceti). -/
theorem cyc_of_isArtinLift (σ : PkgI4.GQp p) (u : ℤ_[p]ˣ) (h : IsArtinLift p σ (unitsQp p u)) :
    PkgI4.cyc p σ = u⁻¹ :=
  TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic p u σ h

/-- If `σ` fixes a primitive `p^k`-th root of unity, its cyclotomic character is `1` modulo `p^k`. -/
theorem toZModPow_cyc_eq_one (k : ℕ) (ζ : PadicAlgCl p) (hζ : IsPrimitiveRoot ζ (p ^ k)) (σ : PkgI4.GQp p)
    (hσ : σ ζ = ζ) : PadicInt.toZModPow k ((PkgI4.cyc p σ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
  have hs := cyclotomicCharacter.spec (L := PadicAlgCl p) p σ.toRingEquiv ζ hζ.pow_eq_one
  have hs' : ζ ^ (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).toZModPow k).val
      = ζ ^ 1 := by
    rw [pow_one, ← hs]; exact hσ
  change PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = 1
  set c := PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])
  rcases k with _ | k
  · have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  · have hp1 : 1 < p ^ (k + 1) := Nat.one_lt_pow (Nat.succ_ne_zero k) (Fact.out : p.Prime).one_lt
    haveI : NeZero (p ^ (k + 1)) := ⟨by positivity⟩
    have hv : c.val = 1 := hζ.pow_inj (ZMod.val_lt c) hp1 hs'
    apply ZMod.val_injective
    rw [hv, ZMod.val_one'' (by omega)]

end Units

/-- **LEAF candidate (Tate 1967, §3.3, Theorem 2, for the complete discretely valued field `\hat{K^{ur}}`; locator
UNVERIFIED).** J. Tate, *p-divisible groups*, Proc. Conf. Local Fields (Driebergen 1966), Springer 1967, §3.3,
Theorem 2: for a complete discretely valued field `L` of characteristic `0` with perfect residue field of
characteristic `p` and `i ≠ 0`, `H⁰(G_L, ℂ(i)) = 0`. Specialization: `L` the completion of the maximal unramified
extension of a finite `K/ℚ_p` inside `ℚ̄_p`; then `G_L` is the inertia group `I_K = G_K ∩ I_{ℚ_p}` acting on
`ℂ = ℂ_p` (a dictionary step, STANDARD: Krasner's lemma and the continuity of the action identify `Gal(\bar L/L)`
with `I_K` and the completion of `\bar L` with `ℂ_p`). The same theorem, specialized to `L = K` finite, is the tree's
`ZInQ.Contrib.HodgeSplit.TateTwistInvariants` (proved, `CloudB3W11.tateTwistInvariants_proof`). Inertia is Tau Ceti's
`TauCeti.inertiaSubgroup ℚ_[p]` (the fixing group of the maximal unramified extension). -/
def TateTwistInvariantsInertia : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (i : ℤ), i ≠ 0 → ∀ x : ℂ_[p],
      (∀ σ ∈ K.fixingSubgroup, (show Field.absoluteGaloisGroup ℚ_[p] from σ) ∈ TauCeti.inertiaSubgroup ℚ_[p] →
        PkgI4.cycPow p σ i • PkgI4.cpAct p σ x = x) → x = 0

/-- **`LocAlgExponentEqWeight` proved** from Tate's theorem over `\hat{K^{ur}}` and Tau Ceti's local class field
theory (the manuscript's "removing its integral local Hodge–Tate weight", diophantine_zq.tex L763-764). -/
theorem locAlgExponentEqWeight_of_tateInertia (hT : TateTwistInvariantsInertia) : LocAlgExponentEqWeight := by
  intro p _ E _ ψ w n _hcont hHT hLA
  by_contra hne
  obtain ⟨k, hk⟩ := hLA
  have h1 : PkgI4.htMult p (charRep ψ) w = 1 := by rw [hHT w]; simp
  have hne_bot : PkgI4.htSpace p (charRep ψ) (-w) ≠ ⊥ := by
    intro h
    rw [PkgI4.htMult, h, finrank_bot, Nat.zero_div] at h1
    exact zero_ne_one h1
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (LinearMap.ext h)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl p) (p ^ k)
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.adjoin ℚ_[p] {ζ}
  haveI : FiniteDimensional ℚ_[p] K :=
    IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (pow_pos (Fact.out : p.Prime).pos k)).tower_top
  refine hv (hT p K (n - w) (sub_ne_zero.2 hne) (φ v) fun σ hσK hσI => ?_)
  obtain ⟨u, hu⟩ := exists_unit_isArtinLift p σ hσI
  have hcyc : PkgI4.cyc p σ = u⁻¹ := cyc_of_isArtinLift p σ u hu
  have hfix : σ ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff K σ).1 hσK ζ (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ)
  have hk1 : PadicInt.toZModPow k (u : ℤ_[p]) = 1 := by
    have h2 := toZModPow_cyc_eq_one p k ζ hζ σ hfix
    rw [hcyc] at h2
    have h3 : PadicInt.toZModPow k ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * PadicInt.toZModPow k (u : ℤ_[p]) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rwa [h2, one_mul] at h3
  have hψ := hk u hk1 σ hu
  have hφσ := hφ σ v
  set a : ℚ_[p] := ((u : ℤ_[p]) : ℚ_[p]) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    have : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
      rw [Ne, PadicInt.coe_eq_zero]; exact u.ne_zero
    exact this h0
  have hcp : ∀ i : ℤ, PkgI4.cycPow p σ i = a ^ (-i) := by
    intro i
    rw [PkgI4.cycPow, hcyc]
    change ((Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom (u⁻¹ ^ i) : ℚ_[p]ˣ) : ℚ_[p]) = _
    rw [map_zpow, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, inv_zpow']
    rfl
  have hmv : Matrix.mulVec ((charRep ψ σ : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) v = (a ^ n) • v := by
    ext j
    simp [charRep, hψ, Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal, Algebra.smul_def, ha_def]
  rw [hmv, map_smul, hcp] at hφσ
  rw [hcp]
  calc a ^ (-(n - w)) • PkgI4.cpAct p σ (φ v) = a ^ (-n) • (a ^ (- -w) • PkgI4.cpAct p σ (φ v)) := by
        rw [smul_smul, ← zpow_add₀ ha]; ring_nf
    _ = a ^ (-n) • (a ^ n • φ v) := by rw [← hφσ]
    _ = φ v := by rw [smul_smul, ← zpow_add₀ ha]; simp


/-! ## `FiniteOfLocAlgTrivialQ` reduced: local part proved, three smaller Props -/

/-- `ψ` has finite image on the inertia group of the place `v` of `ℚ̄`. -/
def CharInertiaFinite {ℓ : ℕ} [Fact ℓ.Prime] (ψ : GaloisChar ℓ) (v : ValuationSubring PkgI4.Qbar) : Prop :=
  (Set.range fun σ : v.inertiaSubgroup ℚ => ψ.toHom ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ)).Finite

/-- **GLUE, on-the-spot (C8, N5 L763-765 "finite inertia … at every other prime"; rv-h-c8 §4 item 3: N5 states it
without argument).** A continuous character `ψ : G_ℚ → ℚ̄_p^×` has finite image on every inertia group at a prime
`q ≠ p`. Sketch: `ψ` takes values in `O_E^×` for a finite `E/ℚ_p` (Baire); `ψ|_{D_v}` factors through `D_v^{ab}`,
where inertia is the image of `ℤ_q^×` (local class field theory at `q`); on the pro-`q` group `1 + q²ℤ_q` the image
lies in `1 + 𝔪_E` after shrinking (continuity), where `x ↦ x^q` is an isometry, so `ψ(x) = lim ψ(x^{q^m}) ⇒` trivial;
hence `ψ(I_v)` is a quotient of a finite group. -/
def InertiaFiniteAwayFromP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ψ : GaloisChar p) (q : ℕ), q.Prime → q ≠ p →
    ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v q → CharInertiaFinite ψ v

/-- **GLUE (dictionary, STANDARD).** Every element of an inertia group of `ℚ̄` above `p` is conjugate in `G_ℚ` to the
image under `PkgI4.decomp` of an element of the inertia group of `ℚ_p` (Tau Ceti's `inertiaSubgroup ℚ_[p]`): the
places above `p` are conjugate, and for the place cut out by the embedding `ℚ̄ → ℚ̄_p` defining `decomp`, the
decomposition group is `decomp(G_{ℚ_p})` and its inertia group is `decomp(I_{ℚ_p})` (Neukirch, *Algebraic Number
Theory*, II §9, UNVERIFIED locator). -/
def InertiaAtPDecomp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (v : ValuationSubring PkgI4.Qbar), PkgI4.LiesOver v p →
    ∀ τ : v.inertiaSubgroup ℚ, ∃ (σ : PkgI4.GQp p) (g : PkgI4.GQ),
      (show Field.absoluteGaloisGroup ℚ_[p] from σ) ∈ TauCeti.inertiaSubgroup ℚ_[p] ∧
        ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = g * PkgI4.decomp p σ * g⁻¹

/-- **Class field theory over `ℚ` (C8, N5 L761-765: "class field theory over ℚ … hence a finite ray-class
character"; the manuscript cites nothing for it: ELLIOT-class).** A continuous character `ψ : G_ℚ → ℚ̄_p^×` with
finite image on every inertia group and unramified outside a finite set has finite image. A consequence of the
Kronecker–Weber theorem with conductors (Tau Ceti: `kroneckerWeber`,
`nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd`): every finite subextension of the abelian field cut out
by `ψ` has conductor dividing a fixed `M`, so lies in `ℚ(ζ_M)`. Not a printed statement in this form (GLUE by the
strict reading). -/
def CFTFiniteQ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ψ : GaloisChar p),
    (∀ q : ℕ, q.Prime → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v q → CharInertiaFinite ψ v) →
    (∃ T : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ T → CharUnramifiedAt ψ q) →
    (Set.range ψ.toHom).Finite

/-- **The local part, proved:** if `ψ ∘ decomp` is trivial on the Artin lifts of `1 + p^kℤ_p`, then on the inertia
group of `ℚ_p` it takes values in the `N`-th roots of unity, `N = #(ℤ/p^k)^×` (Tau Ceti's local class field theory:
every inertia element is an Artin lift of a unit). -/
theorem pow_card_eq_one_of_mem_inertia (p : ℕ) [Fact p.Prime] (ψ : GaloisChar p) (k : ℕ)
    (hk : ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∀ σ : PkgI4.GQp p,
      IsArtinLift p σ (unitsQp p u) → ψ.toHom (PkgI4.decomp p σ) = 1)
    (σ : PkgI4.GQp p) (hσ : (show Field.absoluteGaloisGroup ℚ_[p] from σ) ∈ TauCeti.inertiaSubgroup ℚ_[p]) :
    haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out : p.Prime).ne_zero⟩
    ψ.toHom (PkgI4.decomp p σ) ^ (p ^ k).totient = 1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨u, hu⟩ := exists_unit_isArtinLift p σ hσ
  set N := (p ^ k).totient
  have hN : PadicInt.toZModPow k ((u ^ N : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    have := pow_card_eq_one (G := (ZMod (p ^ k))ˣ) (x := Units.map (PadicInt.toZModPow k).toMonoidHom u)
    have h2 := congrArg (fun x : (ZMod (p ^ k))ˣ => (x : ZMod (p ^ k))) this
    simpa [← map_pow] using h2
  have hl : IsArtinLift p (σ ^ N) (unitsQp p (u ^ N)) := by
    unfold IsArtinLift at hu ⊢
    have e1 : unitsQp p (u ^ N) = unitsQp p u ^ N := by
      simp only [unitsQp, map_pow]
    rw [e1, map_pow, ← hu]
    rfl
  have := hk (u ^ N) hN (σ ^ N) hl
  rwa [map_pow, map_pow] at this

/-- **`FiniteOfLocAlgTrivialQ` from the three smaller Props** (the local part at `p` proved above). -/
theorem finiteOfLocAlgTrivialQ_of_pieces (hA : InertiaFiniteAwayFromP) (hB : InertiaAtPDecomp)
    (hC : CFTFiniteQ) : FiniteOfLocAlgTrivialQ := by
  intro p _ ψ hram ⟨k, hk⟩
  refine hC p ψ (fun q hq v hv => ?_) hram
  by_cases hqp : q = p
  · subst hqp
    haveI : NeZero (q ^ k) := ⟨pow_ne_zero k hq.ne_zero⟩
    set N := (q ^ k).totient
    have hNpos : 0 < N := Nat.totient_pos.2 (pow_pos hq.pos k)
    haveI : NeZero N := ⟨hNpos.ne'⟩
    have hfin : (rootsOfUnity N (PadicAlgCl q) : Set (PadicAlgCl q)ˣ).Finite :=
      Set.finite_coe_iff.mp (inferInstance : Finite (rootsOfUnity N (PadicAlgCl q)))
    refine (hfin.image (fun x : (PadicAlgCl q)ˣ => x)).subset ?_
    rintro _ ⟨τ, rfl⟩
    obtain ⟨σ, g, hσ, hτ⟩ := hB q v hv τ
    refine ⟨ψ.toHom ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ), ?_, rfl⟩
    rw [hτ, map_mul, map_mul, mul_comm (ψ.toHom g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    show _ ∈ rootsOfUnity N (PadicAlgCl q)
    rw [mem_rootsOfUnity]
    exact pow_card_eq_one_of_mem_inertia q ψ k hk σ hσ
  · exact hA p ψ q hq hqp v hv

end HDec.G0Galois.C8Conrad


