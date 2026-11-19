import ZInQKernel.Contrib.CloudB3RC53.OldKummer.Actual
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Odd

/-!
# Old Kummer, part 3: the old-Kummer row of the genuine table from the actual Kummer condition

Manuscript `diophantine_zq.tex`, the table of local condition dimensions (tex 4544–4573, the old
Kummer row `h⁰ + h¹ = dim E(K_w)[2] + dim E(K_w)/2`), Lemma `ex:arith-local-kummer` (tex
3413–3438) and Mattuck's theorem (the Mattuck lane).

`GenuineInst.genCondDim2 K S w .oldKummer kd = kd` takes the old-Kummer dimension as an input,
computed by Mattuck from a local integral model (`kummerResidualDim w C`); until now it was not
tied to the Kummer condition itself. Here, for RC29's actual Kummer condition `actualKummerAt` at
`i = 1` (the residual level):

* `natCard_mul_eq_two_pow`: for an elliptic curve `B` with `B/2B` finite,
  `|B[2]| · |B/2B| = 2^(dim B[2] + dim B/2B)`;
* **`genCondDim2_oldKummer_actual`**: if the local integral model `C` at `v` is a model of the
  actual local twist (`C ×_{𝒪_v} K_v = E^{(h)} ×_K K_v`), then
  `|H⁰(U_v)| · |H¹(U_v)| = 2^(genCondDim2 K S v .oldKummer (kummerResidualDim v C))`, i.e. the
  genuine table's old-Kummer row is the exponent of `2` in the order of the actual Kummer
  condition's cohomology (`H⁰, H¹` are `𝔽₂`-vector spaces of these orders); the model
  identification `hC` is an explicit hypothesis (the Mattuck lane's models `C` are arbitrary
  integral models);
* **`genCondDim2_oldKummer_actual_odd`**: at an odd place with full rational `2`-torsion of the
  twist, `|H⁰(U_v)| · |H¹(U_v)| = 2⁴ = 2^(LocalCondition.dim .oldKummer 0)` (Mattuck at odd
  places, no finiteness hypothesis);
* `OldKummerActualOdd` (node, PROVED).

Scope: level `i = 1` only (see part 2, `Actual.lean`).

**Classification.** PROVED (from RC29's hypotheses of `actualKummerAt` and the model
identification `hC`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.OldKummer

open NumberField IsDedekindDomain WeierstrassCurve ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps ZInQ.Contrib.CloudB3RC53.Mattuck
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-- `|B[2]| · |B/2B| = 2^(dim B[2] + dim B/2B)` for an elliptic curve over a field with `B/2B`
finite. PROVED. -/
theorem natCard_mul_eq_two_pow {L : Type} [Field L] [DecidableEq L] (B : WeierstrassCurve L) [B.IsElliptic]
    [Finite (ModN B.toAffine.Point 2)] :
    Nat.card (AddSubgroup.torsionBy B.toAffine.Point ((2 ^ 1 : ℕ) : ℤ)) *
        Nat.card (B.toAffine.Point ⧸
          (nsmulAddMonoidHom (α := B.toAffine.Point) (2 ^ 1)).range) =
      2 ^ (finrankTwoTorsion B.toAffine.Point +
        Module.finrank (ZMod 2) (ModN B.toAffine.Point 2)) := by
  have hfinT : Finite (Submodule.torsionBy ℤ B.toAffine.Point 2) :=
    B.finite_torsionBy (by norm_num)
  have h1 : Nat.card (AddSubgroup.torsionBy B.toAffine.Point ((2 ^ 1 : ℕ) : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ B.toAffine.Point 2) := by
    norm_num
  have h2 : Nat.card (B.toAffine.Point ⧸
      (nsmulAddMonoidHom (α := B.toAffine.Point) (2 ^ 1)).range) =
      Nat.card (ModN B.toAffine.Point 2) := by
    rw [natCard_modN_two, pow_one]
    rfl
  have hT : Nat.card (Submodule.torsionBy ℤ B.toAffine.Point 2) =
      2 ^ finrankTwoTorsion B.toAffine.Point := by
    let := twoTorsionModule B.toAffine.Point
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite (Submodule.torsionBy ℤ B.toAffine.Point 2)
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    rfl
  have hM : Nat.card (ModN B.toAffine.Point 2) =
      2 ^ Module.finrank (ZMod 2) (ModN B.toAffine.Point 2) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite (ModN B.toAffine.Point 2)
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rw [h1, h2, hT, hM, pow_add]

section Actual

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef 1)ˣ) [IsOpenKer α]
  (hFull : FullTorsion K S W (2 ^ 1))

open scoped Classical in
/-- **The genuine table's old-Kummer row is the dimension of the actual Kummer condition**
(tex 4544–4573 with tex 3413–3438): for a local integral model `C` of the actual local twist
`E^{(h)} ×_K K_v` with `C(K_v)/2` finite, `|H⁰(U_v)| · |H¹(U_v)| = 2^(genCondDim2 … .oldKummer
(kummerResidualDim v C))` for RC29's actual Kummer condition `U_v` at `i = 1`. PROVED. -/
theorem genCondDim2_oldKummer_actual (v : Places K S)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1)
    (C : WeierstrassCurve (v.1.adicCompletionIntegers K))
    [(C.baseChange (v.1.adicCompletion K)).IsElliptic]
    (hC : C.baseChange (v.1.adicCompletion K) = localTwist W h v.1)
    [Finite (ModN (C.baseChange (v.1.adicCompletion K)).toAffine.Point 2)] :
    Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
        Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 1) =
      2 ^ GenuineInst.genCondDim2 K S v.1 .oldKummer (kummerResidualDim v.1 C) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  obtain ⟨h0, h1⟩ := natCard_actualKummerAt_one W s hs hs0 α hFull v hα
  rw [h0, h1]
  change _ = 2 ^ kummerResidualDim v.1 C
  have hfin : Finite (ModN (localTwist W h v.1).toAffine.Point 2) := by
    rw [← hC]; infer_instance
  have hk : kummerResidualDim v.1 C = finrankTwoTorsion (localTwist W h v.1).toAffine.Point +
      Module.finrank (ZMod 2) (ModN (localTwist W h v.1).toAffine.Point 2) := by
    have key : ∀ B' : WeierstrassCurve (v.1.adicCompletion K), B' = localTwist W h v.1 →
        finrankTwoTorsion B'.toAffine.Point + Module.finrank (ZMod 2) (ModN B'.toAffine.Point 2) =
          finrankTwoTorsion (localTwist W h v.1).toAffine.Point +
            Module.finrank (ZMod 2) (ModN (localTwist W h v.1).toAffine.Point 2) := by
      rintro _ rfl; rfl
    exact key _ hC
  rw [hk]
  exact natCard_mul_eq_two_pow (localTwist W h v.1)

open scoped Classical in
/-- **At an odd place the actual Kummer condition has the table's dimension `4`** (tex 4551–4556,
Mattuck at odd places): with full rational `2`-torsion of the local integral model `C` of the
actual twist, `|H⁰(U_v)| · |H¹(U_v)| = 2^(LocalCondition.dim .oldKummer 0) = 2⁴`. No finiteness
hypothesis (`|C(K_v)/2| = |C(K_v)[2]|`, Mattuck lane). PROVED. -/
theorem genCondDim2_oldKummer_actual_odd (v : Places K S)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1) (h2 : (2 : 𝓞 K) ∉ v.1.asIdeal)
    (C : WeierstrassCurve (v.1.adicCompletionIntegers K))
    [(C.baseChange (v.1.adicCompletion K)).IsElliptic]
    (hC : C.baseChange (v.1.adicCompletion K) = localTwist W h v.1)
    (h4 : Nat.card
      (Submodule.torsionBy ℤ (C.baseChange (v.1.adicCompletion K)).toAffine.Point 2) = 4) :
    Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
        Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 1) =
      2 ^ ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer 0 := by
  have := compactSpace_place K v.1
  have hcard := card_modN_two_eq_card_twoTorsion v.1 C h2
  have : Finite (ModN (C.baseChange (v.1.adicCompletion K)).toAffine.Point 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard, h4]; norm_num)
  rw [genCondDim2_oldKummer_actual W s hs hs0 α hFull v hα C hC]
  exact congrArg (2 ^ ·) (kummerResidualDim_odd v.1 C h2 h4)

end Actual

section Node

open scoped Classical in
/-- **Node: the actual old Kummer condition has the table's residual dimension at odd places.**
Manuscript tex 4544–4573 (old Kummer row `4` at odd places), tex 3413–3438 (the actual Kummer
condition `U_v` for `B = E^{(h)}` over `K_v`, coefficients extended along `ι_v`), Mattuck. Claim:
for every number field `K`, `S`, elliptic `E/K`, square root `s ∈ K_S` of `h`, character
`α : G_{K,S} → A_1^×` with open kernel, `FullTorsion K S E 2`, place `v ∈ S` not above `2` with
`α = χ_h` on `G_{K_v}`, and local integral model `C` of `E^{(h)} ×_K K_v` with full rational
`2`-torsion, RC29's actual Kummer condition at `i = 1` satisfies
`|H⁰(U_v)| · |H¹(U_v)| = 2^(LocalCondition.dim .oldKummer 0)`. Kind: PROVED
(`oldKummerActualOdd_proof`). -/
def OldKummerActualOdd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (W : WeierstrassCurve K) [W.IsElliptic] (s : KS K S) (h : K)
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef 1)ˣ)
    [IsOpenKer α] (hFull : FullTorsion K S W (2 ^ 1)) (v : Places K S)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1), (2 : 𝓞 K) ∉ v.1.asIdeal →
    ∀ (C : WeierstrassCurve (v.1.adicCompletionIntegers K))
      [(C.baseChange (v.1.adicCompletion K)).IsElliptic],
      C.baseChange (v.1.adicCompletion K) = localTwist W h v.1 →
      Nat.card (Submodule.torsionBy ℤ (C.baseChange (v.1.adicCompletion K)).toAffine.Point 2) =
        4 →
      Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
          Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 1) =
        2 ^ ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer 0

theorem oldKummerActualOdd_proof : OldKummerActualOdd := by
  intro K _ _ S W _ s h hs hs0 α _ hFull v hα h2 C _ hC h4
  exact genCondDim2_oldKummer_actual_odd W s hs hs0 α hFull v hα h2 C hC h4

end Node

end ZInQ.Contrib.CloudB3RC53.OldKummer
