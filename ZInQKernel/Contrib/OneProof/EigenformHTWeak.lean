import ZInQKernel.OneProof.H.TailX

/-! # ht-bypass: where the field `eigenformHTNew` is used, and the weakest form its consumers need

Task ht-bypass, 2026-11-15 (report `docs/research/ht-bypass.md`, log `scratch/ht-bypass/log.md`); the same text as
`scratch/ht-bypass/HTBypass.lean`. It proves no open field: it records the weakest form of `eigenformHTNew` that the
route needs, and the consumers re-proved with it, for a later bypass fold.

The field `eigenformHTNew : ZInQ.Contrib.HodgeSplit.EigenformHTNew` (bundle `OpenResearchLeaves21`) has exactly
one use on the route to `ZInQ.OneProof.frozenTarget`: `TailX.lean` line 205 turns it into the old research field
`r13 : HDec.PkgI4.EigenformHT`, whose only consumer is `G0Galois.g8_g12_of_leaves3` (`TailD.lean`), which passes
it to `G0Galois.g12` (`TailA.lean`), which passes it to the glue `G12Weight` (proved by
`G0Galois.g12Weight_of_senTwist`, i.e. `g12Weight_of`, `TailB.lean`). There it is applied once, at `ℓ = 5`, to the
eigenform `g` that Pan's theorem (`r11r12`) attaches to G8's `r₅`, in the branch `k ≥ 2`, to show `k = 2`.
At `k = 2` the conclusion `∃ n, {n, n + 1 − k} = {0, −1}` holds trivially, so only `k ≥ 3` is used: the field
serves to exclude eigenforms of weight `≥ 3`.

* §0: the field, copied verbatim, checked equal to the chain's constant.
* §1: the weakest form `EigenformHTNew5Ge3` (`ℓ = 5`, `k ≥ 3`, newforms), and its eigenform version
  `EigenformHT5Ge3`, proved from it with the kernel's I4-L5 and Diamond–Shurman's two theorems.
* §2: `G12Weight`, `g12`, `g8_g12` re-proved with `EigenformHT5Ge3` in place of `EigenformHT` (the consumers need
  only the weaker form); `k = 2` needs nothing.
* §3: `AfterG7` (the input of `GluePieces.modularConstituent`, TailK) re-proved with the weak form
  (`afterG7_of3Weak`), and `afterG7_of3` recovered from it (`afterG7_of3_via_weak`).
-/

set_option maxHeartbeats 1000000

/-! ## §0. The field, verbatim -/

namespace ZInQ.Contrib.HodgeSplit.HTBypass

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)

/-- Verbatim copy of `ZInQ.Contrib.HodgeSplit.EigenformHTNew` (`TailS.lean` line 1275). -/
def EigenformHTNewCopy : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ZInQ.Contrib.G9.PkgI4.CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

theorem eigenformHTNewCopy_eq : EigenformHTNewCopy = ZInQ.Contrib.HodgeSplit.EigenformHTNew := rfl

/-! ## §1. The weakest form the route needs -/

instance fact_prime_five_htb : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **The instance of `EigenformHTNew` the route uses (GLUE (c); Kato 2004 §§9.2-9.4 for newforms, or Faltings
1987 / Saito 1997 / Scholl 1990 with Scholze 2013, at `ℓ = 5`, transported to any semisimple attached `ρ`;
weight `k ≥ 3` only).** A semisimple `ρ : G_ℚ → GL₂(ℚ̄₅)` attached (arithmetic Frobenius, trace `a_p`) to a
newform of weight `k ≥ 3` and any level `N` (including `5 ∣ N`) is Hodge–Tate at `5` with weights `{0, 1 − k}`
(cyclotomic weight `−1`). `EigenformHTNew` at `ℓ = 5`, `k ≥ 3`; not a leaf for the same reason as the field
(Kato's `V_{F_λ}(f)` is not definable in Mathlib). -/
def EigenformHTNew5Ge3 : Prop :=
  ∀ (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ZInQ.Contrib.G9.PkgI4.CF N k) (ρ : GaloisRep 5 2),
    0 < N → 3 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    ρ.HasHTWeightsAtSelf 5 {0, 1 - k}

/-- The same for all normalized eigenforms (the `ℓ = 5`, `k ≥ 3` part of `EigenformHT`). -/
def EigenformHT5Ge3 : Prop :=
  ∀ (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k) (ρ : GaloisRep 5 2),
    0 < N → 3 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    ρ.HasHTWeightsAtSelf 5 {0, 1 - k}

/-- The field implies its weakest form. -/
theorem eigenformHTNew5Ge3_of_field (h : ZInQ.Contrib.HodgeSplit.EigenformHTNew) : EigenformHTNew5Ge3 :=
  fun ιC ιL N k χ f ρ hN hk hf hss hatt => h 5 ιC ιL N k χ f ρ hN (by omega) hf hss hatt

/-- **`EigenformHT5Ge3` from the newform case** (hodge-split's `eigenformHT_of_new` at `ℓ = 5`, `k ≥ 3`). -/
theorem eigenformHT5Ge3_of_new (hNew : EigenformHTNew5Ge3) (hL5 : NewformOfEigenform)
    (hR : EigenformRepExists) (hAC : AttachedConj) (hHC : HTConj) : EigenformHT5Ge3 := by
  intro ιC ιL M k χ g ρ hM hk hg hss hatt
  obtain ⟨N, χ', f, hN, hNM, hf, hcoef⟩ := hL5 M k χ g hM hg
  obtain ⟨ρf, hssf, hattf⟩ := hR 5 ιC ιL N k χ' f hN (by omega) hf.1
  have hHT := hNew ιC ιL N k χ' f ρf hN hk hf hssf hattf
  have hconj : IsConj ρf ρ := by
    refine hAC 5 ρf ρ (M * 5).primeFactors hssf hss fun p hp hpS => ?_
    have hpM : ¬ p ∣ M * 5 := by
      intro h
      exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h, by
        exact Nat.mul_ne_zero (by omega) (by norm_num)⟩)
    have hpN : ¬ p ∣ N * 5 := fun h => hpM (by
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      · exact Dvd.dvd.mul_right (h1.trans hNM) 5
      · exact Dvd.dvd.mul_left h1 M)
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpM
    obtain ⟨huf, αf, hαf, htrf⟩ := hattf p hp hpN
    have hpM' : ¬ p ∣ M := fun h => hpM (Dvd.dvd.mul_right h 5)
    have heq : αf = α := by
      apply ιC.toRingHom.injective
      change ιC αf = ιC α
      rw [hαf, hα, hcoef p hp hpM']
    refine ⟨huf, hu, fun v σ hv hσ => ?_⟩
    rw [htrf v σ hv hσ, htr v σ hv hσ, heq]
  exact hHC 5 2 ρf ρ _ hconj hHT

/-- **`EigenformHT5Ge3` from the weakest form, the kernel's I4-L5 and Diamond–Shurman's Thms 9.6.5-9.6.6**
(the same inputs as `TailX`'s `r13 := …eigenformHT_of_kato_ds r.eigenformHTNew …`). -/
theorem eigenformHT5Ge3_of_ds (hNew : EigenformHTNew5Ge3) (hD : DSThm965) (hDS : DSThm966) :
    EigenformHT5Ge3 :=
  eigenformHT5Ge3_of_new hNew HDec.HSyn.HodgeLF7.newformOfEigenformG9
    (eigenformRepExists_of_r14Det (r14Det_of_printed hD hDS)) attachedConj_proof htConj_proof

end ZInQ.Contrib.HodgeSplit.HTBypass

/-! ## §2. The consumers with the weakest form -/

namespace HDec

namespace G0Galois

open _root_.PkgI4 (GaloisRep GaloisChar)

/-- `EigenformHT5Ge3` on the chain's constants (`PkgI4.EigenformHT` at `ℓ = 5`, `k ≥ 3`). -/
def EigenformHT5Ge3Chain : Prop :=
  ∀ (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k) (ρ : GaloisRep 5 2),
    0 < N → 3 ≤ k → PkgI4.IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ) 5 {0, 1 - k}

/-- Transport along the identity (as `HodgeLF7.eigenformHT`). -/
theorem eigenformHT5Ge3Chain_of (h : _root_.ZInQ.Contrib.HodgeSplit.HTBypass.EigenformHT5Ge3) :
    EigenformHT5Ge3Chain := by
  intro ιC ιL N k χ g ρ hN hk hg hss hatt
  exact h ιC ιL N k χ g (HSyn.HodgeLF7.toG9Rep ρ) hN hk hg hss hatt

/-- The chain's `r13` implies the weak form. -/
theorem eigenformHT5Ge3Chain_of_r13 (h : PkgI4.EigenformHT) : EigenformHT5Ge3Chain :=
  fun ιC ιL N k χ g ρ hN hk hg hss hatt => h 5 ιC ιL N k χ g ρ hN (by omega) hg hss hatt

/-- `G12Weight` with `EigenformHT5Ge3Chain` in place of `PkgI4.EigenformHT` (otherwise verbatim). -/
def G12WeightWeak : Prop :=
  HSyn.EigenformRepExists → EigenformHT5Ge3Chain → HSyn.DeligneSerreConseq → HSyn.FrobeniusDense →
  HSyn.BrauerNesbitt →
  ∀ (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ),
    0 < N → 1 ≤ k → PkgI4.IsNormalizedEigenform g χ → r.IsIrreducible →
    PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1} → r.AttachedUpToTwist ψ ιC ιL g S →
    ∃ n : ℤ, ({n, n + 1 - k} : Multiset ℤ) = {0, -1}

/-- `G12WeightWeak` implies `G12Weight` (its antecedent is weaker). -/
theorem g12Weight_of_weak (h : G12WeightWeak) : G12Weight :=
  fun hR hHT hDS hFD hBN => h hR (eigenformHT5Ge3Chain_of_r13 hHT) hDS hFD hBN

/-- **`G12WeightWeak` from the named pieces** (`g12Weight_of` with the case `k = 2` closed by `n = 0` and
the Hodge–Tate weights of `ρ_g` used only for `k ≥ 3`). -/
theorem g12WeightWeak_of (hTE : TwistExists) (hTC : TwistConj) (hHC : HTConj) (hSen : SenTwist)
    (hFI : FiniteImageHT) : G12WeightWeak := by
  intro hR hHT hDS _hFD _hBN r N k χ g ψ ιC ιL S hN hk hg hirr hw hatt
  rcases eq_or_lt_of_le hk with h1 | h2
  · -- weight one: as in `g12Weight_of`
    obtain ⟨ρH, hss, hρatt⟩ := hR 5 ιC ιL N k χ g hN hk hg
    let ρ : GaloisRep 5 2 := ⟨ρH.toHom, ρH.continuous_toHom⟩
    have hss' : ρ.IsSemisimple := hss
    have hatt' : ρ.AttachedTo ιC ιL g := hρatt
    obtain ⟨ρ', htw⟩ := hTE 5 2 ρ ψ
    have hconj : IsConj r ρ' := hTC 5 r ρ ρ' ψ ιC ιL N k g S hN hirr hss' hatt' hatt htw
    have hw' : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ') 5 {0, -1} := hHC 5 2 r ρ' _ hconj hw
    exfalso
    subst h1
    have hfin : (Set.range ρH.toHom).Finite := hDS 5 ιC ιL ρH N χ g hN hg hss hρatt
    have h0 : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ) 5 (Multiset.replicate 2 0) := hFI 5 2 ρ hfin
    obtain ⟨s, hs⟩ := hSen 5 2 ρ ρ' ψ _ _ htw (by simp) (by simp) h0 hw'
    have ha : (0 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    have hb : (-1 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    rw [hs] at ha hb
    simp only [Multiset.mem_map, Multiset.mem_replicate] at ha hb
    obtain ⟨a, ⟨-, rfl⟩, ha⟩ := ha
    obtain ⟨b, ⟨-, rfl⟩, hb⟩ := hb
    omega
  · rcases eq_or_lt_of_le (show (2 : ℤ) ≤ k by omega) with h2' | h3
    · -- weight two: nothing to prove
      subst h2'
      exact ⟨0, by norm_num⟩
    · -- weight `k ≥ 3`: weights `{0, 1 − k} + s = {0, −1}`
      obtain ⟨ρH, hss, hρatt⟩ := hR 5 ιC ιL N k χ g hN hk hg
      let ρ : GaloisRep 5 2 := ⟨ρH.toHom, ρH.continuous_toHom⟩
      have hss' : ρ.IsSemisimple := hss
      have hatt' : ρ.AttachedTo ιC ιL g := hρatt
      obtain ⟨ρ', htw⟩ := hTE 5 2 ρ ψ
      have hconj : IsConj r ρ' := hTC 5 r ρ ρ' ψ ιC ιL N k g S hN hirr hss' hatt' hatt htw
      have hw' : PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ') 5 {0, -1} := hHC 5 2 r ρ' _ hconj hw
      have h := hHT ιC ιL N k χ g ρ hN (by omega) hg hss' hatt'
      obtain ⟨s, hs⟩ := hSen 5 2 ρ ρ' ψ _ _ htw (by simp) (by simp) h hw'
      refine ⟨s, ?_⟩
      rw [hs]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
      congr 1
      · ring
      · congr 1; ring

/-- **`G12WeightWeak` from `SenTwist` and `FiniteImageHT`** (as `g12Weight_of_senTwist`; all glue proved). -/
theorem g12WeightWeak_of_senTwist (hSen : SenTwist) (hFI : FiniteImageHT) : G12WeightWeak := by
  intro hR hHT hDS hFD hBN
  exact g12WeightWeak_of twistExists (twistConj_of hFD hBN) (htConj_of htExtend) hSen hFI hR hHT hDS hFD hBN

/-- **G12 with the weak form** (`g12`, verbatim but for `hR13`, `hW`). -/
theorem g12Weak (hPB : PkgI4.PanBerger) (hR14 : HSyn.EigenformRepExists) (hR13 : EigenformHT5Ge3Chain)
    (hR15 : HSyn.DeligneSerreConseq) (hT18 : HSyn.FrobeniusDense) (hT19 : HSyn.BrauerNesbitt)
    (hT9 : LeafPush.T09_WeilPairing.{0}) (hW : G12WeightWeak) (hD : G12Det)
    {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (T : Finset ℕ) (r : GaloisRep 5 2)
    (e : Vb A 5 ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5) × (Fin 2 → PadicAlgCl 5))
    (hdim : A.dim = 2) (hint : Intertwines (tate A 5) (fun σ => r.mat (resQ K σ)) e)
    (hirr : r.IsIrreducible) (h9 : G9Out r) (h10 : G10Out r) (h11 : G11Out T r) :
    G12Out r := by
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, ιC, ιL, S, hatt⟩ :=
    hPB 5 (le_refl 5) r hirr (finitelyRamified_of_g11 h11) h9.1 h10 ⟨0, -1, by norm_num, h9.2⟩
  obtain ⟨n, hn⟩ := hW hR14 hR13 hR15 hT18 hT19 r N k χ g ψ ιC ιL S hN hk hg hirr h9.2 hatt
  obtain ⟨-, rfl⟩ := PkgI4.weight_match n k hk hn
  obtain ⟨H, hH, dr, εg, χc, hdet, hHsq, hε⟩ :=
    hD hR14 hT9 K A r e N χ g ψ ιC ιL S hdim hint hN hg hatt
  have := hH
  exact ⟨N, χ, g, ψ, ιC, ιL, S, hN, hg,
    GlueAssembly.twist_finite H dr εg χc ψ.toHom hdet hHsq hε, hatt⟩

/-- **G8-G12 at `ℓ = 5` with the weak form** (`g8_g12`, verbatim but for `hR13`, `hW`). -/
theorem g8_g12Weak (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate)
    (hT : PkgI3.TateModuleFree) (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange)
    (hR10 : PkgI4.DeRhamComparison)
    (hT11 : ZInQ.LeafPush2.T11a_RiemannEnd) (hT12 : ZInQ.LeafPush2.T11b_Rigidity)
    (hPB : PkgI4.PanBerger) (hR14 : HSyn.EigenformRepExists) (hR13 : EigenformHT5Ge3Chain)
    (hR15 : HSyn.DeligneSerreConseq) (hT18 : HSyn.FrobeniusDense) (hT19 : HSyn.BrauerNesbitt)
    (hT9 : LeafPush.T09_WeilPairing.{0})
    (hM : G8Matrix) (h9g : G9GlueNoT23) (h10g : G10Glue) (hW : G12WeightWeak) (hD : G12Det)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r ∧ G9Out r ∧ G10Out r ∧
      G11Out T r ∧ G12Out r := by
  obtain ⟨r, h8, h9, h10, h11⟩ :=
    g8_g11 hS hF hT hH hSS hR10 hT11 hT12 hM h9g h10g A T h2 h6 5 h3 Tm c ε a β u h7
  obtain ⟨hres, e, hint, hadj⟩ := h8
  exact ⟨r, ⟨hres, e, hint, hadj⟩, h9, h10, h11,
    g12Weak hPB hR14 hR13 hR15 hT18 hT19 hT9 hW hD A T r e h7.1 (intertwines_res hres hint)
      (isIrreducible_of_g8 hadj) h9 h10 h11⟩

end G0Galois

end HDec

/-! ## §3. One level up: `AfterG7` with the weak form

`afterG7_of3` (TailD) reads `r.r13` only through `g8_g12_of_leaves3`. Here it is re-proved from the fields of
`ResearchLeaves3` it actually reads, given one by one, with `EigenformHT5Ge3Chain` in place of `r13` and
`G12WeightWeak` in place of `m.weight` (`m.weight` is not read). -/

namespace HDec

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open _root_.HDec.G0ModField

/-- **`AfterG7` with the weak form** (`afterG7_of3`, verbatim but for the research fields, given separately, and
`g8_g12Weak` in place of `g8_g12_of_leaves3`). -/
theorem afterG7_of3Weak (r9a : PkgI3.FaltingsSemisimple) (r9b : PkgI3.FaltingsTate)
    (r10 : PkgI4.DeRhamComparison) (r11r12 : PkgI4.PanBerger) (r14 : EigenformRepExists)
    (r13w : G0Galois.EigenformHT5Ge3Chain) (r15 : DeligneSerreConseq)
    (r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1')
    (t : TextbookLeaves) (m : G0Galois.GaloisPieces) (hWw : G0Galois.G12WeightWeak)
    (h9 : G0Galois.G9GlueNoT23)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6) (hLink : LinkedTateData) : AfterG7 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h6, h3₅, h3₃⟩ := hG36 Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  obtain ⟨Tm₅, c₅, ε₅, a₅, β₅, u₅, Tm₃, c₃, ε₃, a₃, β₃, u₃, h7₅, h7₃, hlink⟩ :=
    hLink Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  have h2 : G0Galois.G2Out L' (T u) :=
    galoisG2Out_of_g7Data resQRange u P L A ε N χ β L' hLL' hdata
  obtain ⟨r₅, h8₅, -, -, h11₅, h12⟩ :=
    G0Galois.g8_g12Weak r9a r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r10 t.t11a t.t11b
      r11r12 r14 r13w r15 t.frobeniusDense HSyn.t19_proved t.t9
      (G0Galois.g8Matrix_of_burnside m.burnside) h9 m.odd hWw
      (G0Galois.g12Det_of m.r14det m.detTate m.finIndex (G0Galois.frobeniusDenseQ_of t.frobeniusDense))
      _ (T u) h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, h8₃, -, -, h11₃⟩ :=
    G0Galois.g8_g11 r9a r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r10 t.t11a
      t.t11b (G0Galois.g8Matrix_of_burnside m.burnside) h9 m.odd _ (T u) h2 h6 3 h3₃
      Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨i, ιC, ι5, hspec⟩ := G0ModNewform.g12Spec_of_galois hDF _ _ _ r₅ r₃ h8₅ h8₃ h12
  obtain ⟨ι3, h14, h15⟩ := hlink r₅ r₃ h8₅ h8₃ i ιC ι5
  have hNL : G0ModNewform.NewformLeaves :=
    ⟨C9Rhof.eigenformTwist_of_hsyn t.t24, t.t25, C9Rhof.eigenformRepExists_of_hsyn r14, r16,
      hCar, r9a, r9b, t.t26, C9Rhof.frobeniusDense_of_hsyn t.frobeniusDense,
      TSkolemKW.C10.brauerNesbittChar0'⟩
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ :=
    G0ModNewform.modularConstituent_tail_G hNL t.t33 t.x1ModelExists
      hSw hL8 hAd _ u ⟨_, hspec ι3, h14, g15RamG_of_wild _ u h15 h11₅ h11₃⟩
  exact ⟨M, J, hM, hJ, hMle, (commonConstituent_copy' _ _).1 hCC⟩

/-- `afterG7_of3` is recovered: `afterG7_of3Weak` applied to a full `ResearchLeaves3` (check that nothing else of
`r` is read). -/
theorem afterG7_of3_via_weak (r : ResearchLeaves3) (t : TextbookLeaves) (m : G0Galois.GaloisPieces)
    (h9 : G0Galois.G9GlueNoT23)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6) (hLink : LinkedTateData) (hSen : G0Galois.SenTwist)
    (hFI : G0Galois.FiniteImageHT) : AfterG7 :=
  afterG7_of3Weak r.r9a r.r9b r.r10 r.r11r12 r.r14 (G0Galois.eigenformHT5Ge3Chain_of_r13 r.r13) r.r15 r.r16 t m
    (G0Galois.g12WeightWeak_of_senTwist hSen hFI) h9 hDF hCar hSw hL8 hAd hG36 hLink

end HSyn.G0AssembleMod

end HDec
