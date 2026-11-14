import ZInQKernel.Contrib.TYZGenus.RingClassBridge

/-!
# tyz-35: `Thm35First ℓ tyzZ` (TYZ Theorem 3.5, first assertion, for the pinned genus points)
# reduced to TYZ Theorem 3.3 (with Lemma 3.14) for the pinned CM points

Task tyz-35 (2026-11-13/14). Report: `docs/research/tyz-35.md`; log: `scratch/tyz-35/log.md`.

§0–§9 are a verbatim copy of cm-bridge's `scratch/cm-bridge/Bridge.lean` §0–§9 (itself cm-numeric's
`Class7.lean`), namespace renamed `CMBridge → TYZ35`; every `Prop` and definition unchanged
(`Thm35First`, `tyzZ`, `Phi0`, `Z7`, … are copied, not re-stated). §T onwards are new.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option maxRecDepth 8000

namespace ZInQ.Contrib.TYZGenus.TYZ35

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b

/-! ## §0. Verbatim copies of the Props of this task (checked equal by `rfl`) -/

namespace Copy

/-- Verbatim copy of `CM.CMFieldOfDefinition`. -/
def CMFieldOfDefinition (H : ℤ → IntermediateField ℚ Qbar) : Prop :=
  ∀ (D : ℤ) (Q : HeegnerForm 32 D), heegnerPt Q ∈ ptsOver (H D)

/-- Verbatim copy of `Package.TYZSigmaFixesZn`. -/
def TYZSigmaFixesZn : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n (sigmaClass n) → galPt ρ (tyzZn n) = tyzZn n

/-- Verbatim copy of `Package.Lemma318Literal`. -/
def Lemma318Literal (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ P ∈ ptsOver (Hn n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0

/-- Verbatim copy of `Package.GenusPtsDefined`. -/
def GenusPtsDefined (Hn : ℕ → IntermediateField ℚ Qbar) (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ ptsOver (Hn n)

/-- Verbatim copy of `Package.Thm35First`. -/
def Thm35First (ℓ : ℕ → ℤ) (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧ (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε Z n))

/-- Verbatim copy of `Package.Lemma321`. -/
def Lemma321 (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 → galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG 1)

/-- Verbatim copy of `Package.GenusPointLeafCM`. -/
def GenusPointLeafCM (ℓ : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ (Φ : ℕ → Finset GalQ) (Z7 : ℕ → PtA),
    (∀ e ∈ n.divisors, e % 8 = 7 → Z7 e ∈ ptsOver (Lni e)) ∧
    (∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧
      (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε (tyzGenusPt Φ Z7) n))) ∧
    (∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 → ∃ k : ℤ,
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 →
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG 1))

theorem cmFieldOfDefinition_eq : CMFieldOfDefinition = CM.CMFieldOfDefinition := rfl
theorem tyzSigmaFixesZn_eq : TYZSigmaFixesZn = Package.TYZSigmaFixesZn := rfl
theorem lemma318Literal_eq : Lemma318Literal = Package.Lemma318Literal := rfl
theorem genusPtsDefined_eq : GenusPtsDefined = Package.GenusPtsDefined := rfl
theorem thm35First_eq : Thm35First = Package.Thm35First := rfl
theorem lemma321_eq : Lemma321 = Package.Lemma321 := rfl
theorem genusPointLeafCM_eq : GenusPointLeafCM = Package.GenusPointLeafCM := rfl

end Copy

/-! ## §1. TYZ's class-7 CM point -/

/-- TYZ's `δ` (L1205: "an integer such that `δ² ≡ −n (mod 128)`"), pinned as the least `δ ∈ [0, 128)`
with `δ² + n ≡ 0 (mod 128)` (junk `0` if there is none; there is one for `n ≡ 7 (mod 8)`,
`tyzDelta_spec`). Numerically the CM point depends only on `δ mod 64`, and `δ ↦ −δ` conjugates it
(`class7.out`). -/
def tyzDelta (n : ℕ) : ℕ :=
  ((List.range 128).find? fun d => (d * d + n) % 128 == 0).getD 0

theorem tyzDelta_mod (n : ℕ) : tyzDelta n = tyzDelta (n % 128) := by
  unfold tyzDelta
  congr 2
  funext d
  rw [Nat.add_mod (d * d) n, Nat.add_mod (d * d) (n % 128), Nat.mod_mod]

theorem tyzDelta_spec_aux : ∀ m < 128, m % 8 = 7 → (tyzDelta m * tyzDelta m + m) % 128 = 0 := by
  decide +kernel

theorem tyzDelta_spec {n : ℕ} (hn : n % 8 = 7) : (tyzDelta n * tyzDelta n + n) % 128 = 0 := by
  have h := tyzDelta_spec_aux (n % 128) (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [← tyzDelta_mod] at h
  rw [Nat.add_mod, ← Nat.mod_mod n 128, ← Nat.add_mod]
  rw [Nat.add_mod] at h
  simpa [Nat.mod_mod] using h

theorem tyzDelta_dvd {n : ℕ} (hn : n % 8 = 7) :
    (128 : ℤ) ∣ (n : ℤ) + (tyzDelta n : ℤ) ^ 2 := by
  have h := Nat.dvd_of_mod_eq_zero (tyzDelta_spec hn)
  have h' : ((128 : ℕ) : ℤ) ∣ ((tyzDelta n * tyzDelta n + n : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
  push_cast at h'
  rw [pow_two, add_comm]
  exact h'

/-- **TYZ's class-7 Heegner form** `[(n+δ²)/4, δ, 1]` (level 32, discriminant `−n`): the fixed point
of TYZ's embedding `√−n ↦ [[δ, 2], [−(n+δ²)/2, −δ]]` (L1203–1205) solves `(n+δ²)h² + 4δh + 4 = 0`. -/
def tyzForm7 (n : ℕ) (hn : n % 8 = 7) : HeegnerForm 32 (-(n : ℤ)) where
  A := ((n : ℤ) + (tyzDelta n : ℤ) ^ 2) / 4
  B := tyzDelta n
  C := 1
  A_pos := by
    have := tyzDelta_dvd hn
    have h0 : (0 : ℤ) ≤ (tyzDelta n : ℤ) ^ 2 := by positivity
    have h7 : (7 : ℤ) ≤ n := by have : 7 ≤ n := by omega
                                exact_mod_cast this
    omega
  N_dvd := by
    have := tyzDelta_dvd hn
    omega
  disc := by
    have := tyzDelta_dvd hn
    omega
  D_neg := by
    have : (0 : ℤ) < n := by have : 0 < n := by omega
                             exact_mod_cast this
    omega
  primitive := by simp

/-- **`z_n = f_n(P_n)` for `n ≡ 7 (mod 8)`** (TYZ L1196: `f_n = i₀`), the Heegner point of
`tyzForm7 n` on `A = X₀(32)` (junk `0` otherwise). -/
def tyzZ7 (n : ℕ) : PtA :=
  if hn : n % 8 = 7 then heegnerPt (tyzForm7 n hn) else 0

/-! ## §2. Artin symbols of an arbitrary order, lifted to `ℚ̄` -/

section ArtinO

variable (d : ℕ) [NeZero d] (O : NumberFieldOrder (QNeg d))

/-- `ρ ∈ Gal(ℚ̄/ℚ)` acts on the ring class field of `O` (inside `ℚ̄` through ring-class's `embed d`)
as Tau Ceti's Artin symbol of `c ∈ Pic(O)` (for `O = O4 d` the same shape as `Package.ActsAsArtin4`). -/
def ActsAsArtinO (ρ : GalQ) (c : Pic O) : Prop :=
  ∀ x : ringClassField O, ρ (embed d (x : SeparableClosure (QNeg d))) =
    embed d ((ringClassArtinEquiv O c x : ringClassField O) : SeparableClosure (QNeg d))

/-- The ring class field restricted to `ℚ`-scalars. -/
abbrev RQ : IntermediateField ℚ (SeparableClosure (QNeg d)) := (ringClassField O).restrictScalars ℚ

/-- The ring automorphism of the ring class field (as `ℚ`-subfield) given by `g`. -/
def gQO (g : Gal(ringClassField O/QNeg d)) : RQ d O ≃+* RQ d O := g.toRingEquiv

/-- The induced automorphism of its image in `ℚ̄`. -/
def gBarO (g : Gal(ringClassField O/QNeg d)) : (RQ d O).map (embed d) ≃ₐ[ℚ] (RQ d O).map (embed d) :=
  AlgEquiv.ofRingEquiv (f := ((IntermediateField.equivMap (RQ d O) (embed d)).toRingEquiv.symm.trans
    ((gQO d O g).trans (IntermediateField.equivMap (RQ d O) (embed d)).toRingEquiv)))
    (fun q => by simp)

/-- **Every element of `Gal(ring class field / K_d)` is induced by an automorphism of `ℚ̄`** (the
proof of cm-points' `exists_actsAsArtin4`, for an arbitrary order). -/
theorem exists_actsAsArtinO (c : Pic O) : ∃ ρ : GalQ, ActsAsArtinO d O ρ c := by
  let χ := gBarO d O (ringClassArtinEquiv O c)
  refine ⟨AlgEquiv.ofBijective (χ.toAlgHom.liftNormal Qbar) (AlgHom.normal_bijective _ _ _ _), ?_⟩
  intro x
  have hx : embed d (x : SeparableClosure (QNeg d)) =
      algebraMap ((RQ d O).map (embed d)) Qbar (IntermediateField.equivMap (RQ d O) (embed d) x) := rfl
  rw [AlgEquiv.ofBijective_apply, hx, AlgHom.liftNormal_commutes]
  have e : χ (IntermediateField.equivMap (RQ d O) (embed d) x) =
      IntermediateField.equivMap (RQ d O) (embed d) (ringClassArtinEquiv O c x) := by
    simp only [χ, gBarO, gQO, AlgEquiv.ofRingEquiv_apply]
    change IntermediateField.equivMap (RQ d O) (embed d) (ringClassArtinEquiv O c
      ((IntermediateField.equivMap (RQ d O) (embed d)).symm
        (IntermediateField.equivMap (RQ d O) (embed d) x))) = _
    have h := AlgEquiv.symm_apply_apply (IntermediateField.equivMap (RQ d O) (embed d))
      (show ↥(RQ d O) from x)
    exact congrArg (fun y : ↥(RQ d O) => IntermediateField.equivMap (RQ d O) (embed d)
      (show ↥(RQ d O) from ringClassArtinEquiv O c (show ↥(ringClassField O) from y))) h
  show algebraMap _ Qbar (χ (IntermediateField.equivMap (RQ d O) (embed d) x)) = _
  rw [e]
  rfl

end ArtinO

/-! ## §3. The class-7 genus point -/

/-- The maximal order of `K_d = ℚ(√−d)`; its ring class field is ring-class's `hilbertField d`. -/
abbrev OK (d : ℕ) [NeZero d] : NumberFieldOrder (QNeg d) := maximalNumberFieldOrder (QNeg d)

/-- A fixed lift to `ℚ̄` of the Artin symbol of `c ∈ Cl(K_d)` on the Hilbert class field. -/
def liftMax (d : ℕ) [NeZero d] (c : Pic (OK d)) : GalQ := (exists_actsAsArtinO d (OK d) c).choose

theorem liftMax_spec (d : ℕ) [NeZero d] (c : Pic (OK d)) : ActsAsArtinO d (OK d) (liftMax d c) c :=
  (exists_actsAsArtinO d (OK d) c).choose_spec

/-- `2Cl_d = Cl(K_d)²` as a finite set. -/
def sqClasses (d : ℕ) [NeZero d] : Finset (Pic (OK d)) :=
  ((picSquares (OK d) : Subgroup (Pic (OK d))) : Set (Pic (OK d))).toFinite.toFinset

/-- **TYZ's class-7 genus point** `Z(e) = Σ_{t ∈ 2Cl_e} z_e^t` (L1316–1318 with `σ = 1`, L1268;
`Φ₀ = 2Cl_e` since `H'_e = H_e`, Prop 3.2(3)), each `t` realized by `liftMax`. On `A(H_e)` the value
does not depend on the lifts (`z_e ∈ A(H_e)` is the leaf `CMFieldOfDefinition7`). Junk `0` at `e = 0`. -/
def Z7 (e : ℕ) : PtA :=
  if h : e = 0 then 0 else
    haveI : NeZero e := ⟨h⟩
    ∑ c ∈ sqClasses e, galPt (liftMax e c) (tyzZ7 e)

/-! ## §4. TYZ's sets `Φ₀` for class 5, pinned -/

/-- `T` is a choice of TYZ's `Φ₀` for `e ≡ 5 (mod 8)` (L1316–1317): every `ρ ∈ T` acts on `H_{e,4}`
as the Artin symbol of a square class (so its restriction to `H'_e` lies in `2Cl'_e`), and over each
element of `2Cl_e = Cl(K_e)²` (acting on the Hilbert class field) lies exactly one `ρ ∈ T`; i.e. `T`
represents `2Cl'_e/⟨σ⟩ ≅ 2Cl_e` (L1270–1272). -/
def IsPhi0 (e : ℕ) [NeZero e] (T : Finset GalQ) : Prop :=
  (∀ ρ ∈ T, ∃ c ∈ picSquares (O4 e), ActsAsArtin4 ρ e c) ∧
    ∀ c' ∈ picSquares (OK e), ∃! ρ, ρ ∈ T ∧ ActsAsArtinO e (OK e) ρ c'

open Classical in
/-- **TYZ's `Φ₀` for class 5, pinned by choice** (the `∅` branches are never taken for `e ≠ 0`:
`phi0_spec : IsPhi0 e (Phi0 e)`, §9, from the extension of automorphisms `H_e → H_{e,4}`; TYZ
L1270–1276). TYZ: Lemma 3.21 holds for any choice (L2547–2554). -/
def Phi0 (e : ℕ) : Finset GalQ :=
  if h0 : e = 0 then ∅ else
    haveI : NeZero e := ⟨h0⟩
    if h : ∃ T : Finset GalQ, IsPhi0 e T then h.choose else ∅

/-- **TYZ's genus points, every one pinned**: `Z(e) = Σ_{t ∈ Φ₀(e)} t(z_e)` for `e ≡ 5 (mod 8)` and
`Z7 e` otherwise. -/
def tyzZ : ℕ → PtA := tyzGenusPt Phi0 Z7

theorem tyzZ_five {e : ℕ} (he : e % 8 = 5) : tyzZ e = genusSum (Phi0 e) (tyzZn e) := by
  simp only [tyzZ, tyzGenusPt, he, ↓reduceIte]

theorem tyzZ_seven {e : ℕ} (he : e % 8 = 7) : tyzZ e = Z7 e := by
  have : ¬ e % 8 = 5 := by omega
  simp only [tyzZ, tyzGenusPt, this, ↓reduceIte]

/-! ## §5. The leaves about the pinned genus points -/

/-- The Hilbert class field `H_d ⊂ ℚ̄` (`⊥` at `d = 0`). -/
def hilbertBar (d : ℕ) : IntermediateField ℚ Qbar :=
  if h : d = 0 then ⊥ else
    haveI : NeZero d := ⟨h⟩; ((hilbertField d).restrictScalars ℚ).map (embed d)

/-- **Leaf CM-2-7 (field of definition of TYZ's class-7 CM point)**: for squarefree `n ≡ 7 (mod 8)`,
`z_n` (the Heegner point of `[(n+δ²)/4, δ, 1]`, maximal order, discriminant `−n`) is defined over the
Hilbert class field `H_n`. Classical case of Shimura's reciprocity law (conductor 1, prime to `N`):
Gross, *Heegner points on X₀(N)* (1984) §1–3; Gross–Zagier (1986) II §1; Shimura (1971) Thm. 5.7
(UNVERIFIED numbers); TYZ Prop. 3.2(3) (`H'_n = H_n`, L1260, VERIFIED read). Refereed. Numerically
the coordinates generate exactly `H_n` for n = 7, …, 71 (`class7.out`). Instance of
`CM.CMFieldOfDefinition` at `D = −n`, `H(−n) = H_n`. -/
def CMFieldOfDefinition7 : Prop :=
  ∀ n : ℕ, n % 8 = 7 → Squarefree n → tyzZ7 n ∈ ptsOver (hilbertBar n)

/-- **Leaf TYZ-2558 (field of definition of the class-7 genus point)**: for squarefree `e ≡ 7
(mod 8)`, `Z(e) ∈ A(L_e(i))`, `L_e(i) = ℚ(i, √p : p ∣ e)`. TYZ L2558 ("`H_n' = H_n` and thus `Z(n)` is
already defined over `L_n`", n ≡ 7), from `z_n ∈ A(H_n)` and genus theory (the subfield of `H_e` fixed
by `2Cl_e` is the genus field `ℚ(√p* : p ∣ e) ⊆ L_e(i)`, L2525). Refereed. Proved as glue below
(`class7GenusPtDefined_of`). Numerically the coordinates of `Z(e)` lie in `ℚ(√p* : p ∣ e)` for 12
values of `e` (`lemma321_7.out`). -/
def Class7GenusPtDefined : Prop :=
  ∀ e : ℕ, e % 8 = 7 → Squarefree e → Z7 e ∈ ptsOver (Lni e)

/-- **Leaf TYZ-3.21(4) (pinned)**: for squarefree `e ≡ 7 (mod 8)` and every `σ` acting on the
quadratic fields as `β₁` (`IsBetaOneLift`), `Z(e)^{σ} + Z(e) = g(e)·τ(1/2)`. TYZ Lemma 3.21(4)
(L2514–2516, "for any lifting"); since `Z(e) ∈ A(L_e(i))` (multiquadratic) the action of `σ` on it
only depends on `IsBetaOneLift`, so this follows from TYZ's statement with `Class7GenusPtDefined`.
Refereed. VERIFIED numerically for e = 7, 15, …, 103 (12 values, `lemma321_7.out`). -/
def Lemma321Seven : Prop :=
  ∀ e : ℕ, e % 8 = 7 → Squarefree e → ∀ σ : GalQ, IsBetaOneLift σ →
    galPt σ (Z7 e) + Z7 e = (gNat e : ℤ) • tauG 1

/-- **Leaf TYZ-3.21(1) (pinned)**: for squarefree `n ≡ 5 (mod 8)` there is `σ` with
`IsBetaOneLift σ` such that `Z(e)^{σ} + Z(e) ∈ g(e)τ((1−i)/2) + ℤτ(1)` for every `e ∣ n`,
`e ≡ 5 (mod 8)`, `Z(e) = Σ_{t ∈ Φ₀(e)} t(z_e)`. TYZ Lemma 3.21(1) (L2496–2512, for any lifting `β'`
and any choice of `Φ₀`, L2547–2554). Refereed. VERIFIED numerically for n = 5, 13, 37 with both
choices `Φ₀ = {1}, {σ}` and 8 lifts each (`lemma321_5.out`; uses ShimuraReciprocity). -/
def Lemma321Five : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ σ : GalQ, IsBetaOneLift σ ∧
      ∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (tyzZ e) + tyzZ e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2

/-! ## §6. Glue: the split of `GenusPointLeafCM` -/

theorem lemma321_of (h5 : Lemma321Five) (h7 : Lemma321Seven) : Lemma321 tyzZ := by
  intro n hn hsq
  obtain ⟨σ, hσ, h5'⟩ := h5 n hn hsq
  refine ⟨σ, hσ, h5', fun e he he7 => ?_⟩
  have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
  rw [tyzZ_seven he7]
  exact h7 e he7 hse σ hσ

theorem genusPtsDefined_tyzZ (hz : TYZZnOverHprime) (hN : HprimeNormal) (h7 : Class7GenusPtDefined) :
    GenusPtsDefined HHprime tyzZ :=
  genusPtsDefined_of hz hN Phi0 tyzZ (fun e he => tyzZ_five he)
    (fun e he hsq => by rw [tyzZ_seven he]; exact h7 e he hsq)

/-- **`GenusPointLeafCM` from the pinned leaves** (witnesses `Φ := Phi0`, `Z7 := Z7`). -/
theorem genusPointLeafCM_of_pinned {ℓ : ℕ → ℤ} (h7 : Class7GenusPtDefined)
    (h35 : Thm35First ℓ tyzZ) (h321 : Lemma321 tyzZ) : GenusPointLeafCM ℓ := by
  intro n hn hsq
  obtain ⟨ε, hε, hP⟩ := h35 n hn hsq
  obtain ⟨σ, hσ, h5, h7'⟩ := h321 n hn hsq
  refine ⟨Phi0, Z7, fun e he he7 => h7 e he7 (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)),
    ⟨ε, hε, hP⟩, σ, hσ, h5, h7'⟩

/-- **`GenusPointLeaf` via cm-points' `genusPointLeaf_of_split`**, for the pinned genus points. -/
theorem genusPointLeaf_of_pinned {ℓ : ℕ → ℤ} (hz : TYZZnOverHprime) (hN : HprimeNormal)
    (h7 : Class7GenusPtDefined) (h35 : Thm35First ℓ tyzZ) (h321 : Lemma321 tyzZ) :
    GenusPointLeaf ℓ HHprime :=
  genusPointLeaf_of_split (genusPtsDefined_tyzZ hz hN h7) h35 h321

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem, every genus point pinned.** The premise `TYZThm35ReadingA` from the three
`𝓛`-leaves, the CM leaves `CMFieldOfDefinitionTYZ`, `IInH4`, `TYZSigmaFixesZn`, `HprimeNormal`,
TYZ Lemma 3.18 (literal) and the closed leaves about the pinned genus points `tyzZ`:
`Class7GenusPtDefined` (TYZ L2458), `Thm35First ℓ tyzZ` (TYZ Thm 3.3/3.5), `Lemma321Five`
(TYZ Lemma 3.21(1)) and `Lemma321Seven` (TYZ Lemma 3.21(4)). No existential over genus points
remains. -/
theorem tyzThm35ReadingA_of_pinned (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (h7 : Class7GenusPtDefined)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ) (h5 : Lemma321Five)
    (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_ringClass h11 h1 h29 tyzZ hN ((lemma318_iff_literal HHprime).mpr h318)
    (genusPtsDefined_tyzZ (tyzZnOverHprime_of hcm hi hs) hN h7) h35 (lemma321_of h5 h7')

open ZInQ.Contrib.TYZDecomp in
/-- The same, through cm-points' `tyzThm35ReadingA_of_cmLeaves` (consistency check: the pinned
leaves imply cm-points' bundled `GenusPointLeafCM`). -/
theorem tyzThm35ReadingA_of_pinned' (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (h7 : Class7GenusPtDefined)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ) (h5 : Lemma321Five)
    (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmLeaves h11 h1 h29 hcm hi hs hN h318
    fun ℓ hℓ => genusPointLeafCM_of_pinned h7 (h35 ℓ hℓ) (lemma321_of h5 h7')

/-! ## §7. `TYZSigmaFixesZn` from the shape of the Galois action (computation) -/

/-- `τ(1) = (0, 0)` is fixed by `[i]`, so `(1 − [i])` kills it. -/
theorem sub_iPt_pt00 : pt00 - iPt pt00 = 0 := by rw [iPt_pt00, sub_self]

/-- Points of `H'_d ⊂ ℚ̄` are fixed by every `ρ` acting on `H_{d,4}` as `σ_{1+2ϖ}` (the easy
direction of the Galois correspondence; converse: cm-points' `mem_Hprimebar_of_fixed`). -/
theorem fixed_of_mem_Hprimebar (d : ℕ) [NeZero d] {x : Qbar} (hx : x ∈ Hprimebar d) (ρ : GalQ)
    (hρ : ActsAsArtin4 ρ d (sigmaClass d)) : ρ x = x := by
  rw [Hprimebar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ H4 d := Hprime_le_H4 d hy
  have h1 : ρ (embed d y) =
      embed d ((artin4 d (sigmaClass d) ⟨y, hy'⟩ : H4 d) : SeparableClosure (QNeg d)) := hρ ⟨y, hy'⟩
  change ρ (embed d y) = embed d y
  rw [h1]
  congr 1
  have hy3 : (⟨y, hy'⟩ : H4 d).1 ∈ IntermediateField.lift
      (IntermediateField.fixedField (Subgroup.zpowers (artin4 d (sigmaClass d)))) := hy
  have hy2 := (IntermediateField.mem_lift _).mp hy3
  rw [IntermediateField.mem_fixedField_iff] at hy2
  exact congrArg Subtype.val (hy2 _ (Subgroup.mem_zpowers _))

/-- **Leaf GT' (`i ∈ H'_n`)**: for squarefree `n ≡ 5 (mod 8)`, `i ∈ H'_n`. Genus theory (`i` lies in
the genus field of `ℚ(√−n)`, hence in `H_n`; Cox Thm 6.1, UNVERIFIED number) and `H_n ⊆ H'_n` (TYZ
Prop. 3.2(1): `σ_{1+2ϖ} ∈ Gal(H_{n,4}/H_n)`, L1253–1256). Refereed (textbook + TYZ). -/
def IInHprime : Prop := ∀ n : ℕ, n % 8 = 5 → Squarefree n → iQ ∈ Hprimebar n

/-- **Leaf TYZ-3.7(1)+SR (the Galois action of `σ_{1+2ϖ}` on `f₀(P_n)` is translation by
`τ(1) = (0,0)`)**. Consequence of TYZ's Proposition `heckeaction5`(1) (L1488–1490: `Q^{1+2ϖ} = Q + τ(1)`
for every `Q ∈ X_U(ℂ)`; proposition number UNVERIFIED) and Shimura's reciprocity law at the CM point
`P_n` (`σ_t P_n = P_n^t`), `f₀` being defined over `ℚ`. Refereed. VERIFIED numerically for
n = 5, 13, 21, 29, 37 (3 primes each, `sigma5.out`, through `CM.ShimuraReciprocity`, whose direction is
VERIFIED in `shimura.out`). Unlike `TYZSigmaFixesZn` (printed as TYZ Thm 3.6(1), L1413) it does not
involve the `[i]`-sign of `CM.tyzZn`. -/
def TYZSigmaShiftsF0 : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n (sigmaClass n) → galPt ρ (tyzHeegnerPt n) = tyzHeegnerPt n + pt00

/-- **`TYZSigmaFixesZn` from `TYZSigmaShiftsF0` and `i ∈ H'_n`** (glue): `ρ` fixes `i`, so it commutes
with `[i]`, and `(1 − [i])(f₀ + (0,0)) = (1 − [i])f₀`. -/
theorem tyzSigmaFixesZn_of (hsh : TYZSigmaShiftsF0) (hi : IInHprime) : TYZSigmaFixesZn := by
  intro n hn0 hn hsq ρ hρ
  have hρi : ρ iQ = iQ := fixed_of_mem_Hprimebar n (hi n hn hsq) ρ hρ
  have e := hsh n hn0 hn hsq ρ hρ
  unfold tyzZn
  rw [map_sub, galPt_iPt ρ hρi, e, iPt_add, iPt_pt00]
  abel

/-! ## §8. `Class7GenusPtDefined` from the CM field of definition and genus theory -/

section Class7Descent

/-- `galPt` is multiplicative: `(στ)(P) = σ(τ(P))`. -/
theorem galPt_mul (σ τ : GalQ) (P : PtA) : galPt (σ * τ) P = galPt σ (galPt τ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h1, e1⟩ := galPt_some (σ * τ) h
    obtain ⟨h2, e2⟩ := galPt_some τ h
    obtain ⟨h3, e3⟩ := galPt_some σ h2
    rw [e1, e2, e3, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨AlgEquiv.mul_apply σ τ x, AlgEquiv.mul_apply σ τ y⟩

/-- Two automorphisms agreeing on `K` act identically on `A(K)`. -/
theorem galPt_congr {K : IntermediateField ℚ Qbar} {ρ ρ' : GalQ} (h : ∀ x ∈ K, ρ x = ρ' x)
    {P : PtA} (hP : P ∈ ptsOver K) : galPt ρ P = galPt ρ' P := by
  rw [mem_ptsOver_iff] at hP
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · obtain ⟨h1, e1⟩ := galPt_some ρ hxy
    obtain ⟨h2, e2⟩ := galPt_some ρ' hxy
    rw [e1, e2, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨h x hP.1, h y hP.2⟩

variable (d : ℕ) [NeZero d]

theorem hilbertBar_eq : hilbertBar d = ((hilbertField d).restrictScalars ℚ).map (embed d) := by
  simp only [hilbertBar, NeZero.ne d, ↓reduceDIte]

variable {d}

theorem actsO_mem {ρ : GalQ} {c : Pic (OK d)} (hρ : ActsAsArtinO d (OK d) ρ c) {x : Qbar}
    (hx : x ∈ hilbertBar d) : ρ x ∈ hilbertBar d := by
  rw [hilbertBar_eq] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : ρ (embed d y) = embed d ((ringClassArtinEquiv (OK d) c ⟨y, hy⟩ : ringClassField (OK d)) :
      SeparableClosure (QNeg d)) := hρ ⟨y, hy⟩
  change ρ (embed d y) ∈ _
  rw [h1]
  exact ⟨_, (ringClassArtinEquiv (OK d) c ⟨y, hy⟩).2, rfl⟩

theorem actsO_agree {ρ ρ' : GalQ} {c : Pic (OK d)} (hρ : ActsAsArtinO d (OK d) ρ c)
    (hρ' : ActsAsArtinO d (OK d) ρ' c) : ∀ x ∈ hilbertBar d, ρ x = ρ' x := by
  intro x hx
  rw [hilbertBar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : ρ (embed d y) = embed d ((ringClassArtinEquiv (OK d) c ⟨y, hy⟩ : ringClassField (OK d)) :
      SeparableClosure (QNeg d)) := hρ ⟨y, hy⟩
  have h2 : ρ' (embed d y) = embed d ((ringClassArtinEquiv (OK d) c ⟨y, hy⟩ : ringClassField (OK d)) :
      SeparableClosure (QNeg d)) := hρ' ⟨y, hy⟩
  change ρ (embed d y) = ρ' (embed d y)
  rw [h1, h2]

theorem actsO_mul {ρ ρ' : GalQ} {c c' : Pic (OK d)} (hρ : ActsAsArtinO d (OK d) ρ c)
    (hρ' : ActsAsArtinO d (OK d) ρ' c') : ActsAsArtinO d (OK d) (ρ * ρ') (c * c') := by
  intro x
  rw [AlgEquiv.mul_apply, hρ' x, hρ (ringClassArtinEquiv (OK d) c' x), map_mul, AlgEquiv.mul_apply]

theorem mem_sqClasses {c : Pic (OK d)} : c ∈ sqClasses d ↔ c ∈ picSquares (OK d) := by
  simp [sqClasses]

theorem sum_sqClasses_mul {s : Pic (OK d)} (hs : s ∈ picSquares (OK d)) (f : Pic (OK d) → PtA) :
    ∑ c ∈ sqClasses d, f (s * c) = ∑ c ∈ sqClasses d, f c := by
  refine Finset.sum_nbij' (fun c => s * c) (fun c => s⁻¹ * c) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).mul_mem hs hc
  · intro c hc
    simp only [mem_sqClasses] at hc ⊢
    exact (picSquares (OK d)).mul_mem ((picSquares (OK d)).inv_mem hs) hc
  · intro c _; simp
  · intro c _; simp
  · intro c _; rfl

theorem Z7_eq (e : ℕ) [NeZero e] : Z7 e = ∑ c ∈ sqClasses e, galPt (liftMax e c) (tyzZ7 e) := by
  simp only [Z7, NeZero.ne e, ↓reduceDIte]

theorem Z7_mem {e : ℕ} [NeZero e] (hz : tyzZ7 e ∈ ptsOver (hilbertBar e)) :
    Z7 e ∈ ptsOver (hilbertBar e) := by
  rw [Z7_eq]
  exact (ptsOver _).sum_mem fun c _ =>
    galPt_mem (liftMax e c) (fun x hx => actsO_mem (liftMax_spec e c) hx) hz

/-- **The lifts of `2Cl_e` fix `Z(e)`** (reindexing the genus sum; the lifts act on `A(H_e)` through
their Artin symbols). -/
theorem galPt_Z7 {e : ℕ} [NeZero e] (hz : tyzZ7 e ∈ ptsOver (hilbertBar e)) {s : Pic (OK e)}
    (hs : s ∈ picSquares (OK e)) : galPt (liftMax e s) (Z7 e) = Z7 e := by
  rw [Z7_eq, map_sum]
  have : ∀ c ∈ sqClasses e, galPt (liftMax e s) (galPt (liftMax e c) (tyzZ7 e)) =
      galPt (liftMax e (s * c)) (tyzZ7 e) := fun c _ => by
    rw [← galPt_mul]
    exact galPt_congr (actsO_agree (actsO_mul (liftMax_spec e s) (liftMax_spec e c))
      (liftMax_spec e (s * c))) hz
  rw [Finset.sum_congr rfl this, sum_sqClasses_mul hs (fun c => galPt (liftMax e c) (tyzZ7 e))]

/-- The genus field `G_d ⊂ ℚ̄` of `K_d` (ring-class's `genusField` of the maximal order: the subfield
of `H_d` fixed by `2Cl_d`), `⊥` at `d = 0`. -/
def genusBar (d : ℕ) : IntermediateField ℚ Qbar :=
  if h : d = 0 then ⊥ else
    haveI : NeZero d := ⟨h⟩; ((genusField (OK d)).restrictScalars ℚ).map (embed d)

/-- **Galois descent `H_d → G_d`**: a point of `H_d ⊂ ℚ̄` fixed by the lifts of `2Cl_d` lies in the
genus field. -/
theorem mem_genusBar_of_fixed {x : Qbar} (hx : x ∈ hilbertBar d)
    (hfix : ∀ s ∈ picSquares (OK d), liftMax d s x = x) : x ∈ genusBar d := by
  rw [hilbertBar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hg : genusBar d = ((genusField (OK d)).restrictScalars ℚ).map (embed d) := by
    simp only [genusBar, NeZero.ne d, ↓reduceDIte]
  rw [hg]
  refine ⟨y, ?_, rfl⟩
  show y ∈ genusField (OK d)
  rw [genusField, show y = (⟨y, hy⟩ : ringClassField (OK d)).1 from rfl, IntermediateField.mem_lift,
    IntermediateField.mem_fixedField_iff]
  rintro f ⟨s, hs, rfl⟩
  have h1 : liftMax d s (embed d y) = embed d ((ringClassArtinEquiv (OK d) s ⟨y, hy⟩ :
      ringClassField (OK d)) : SeparableClosure (QNeg d)) := liftMax_spec d s ⟨y, hy⟩
  have h0 : liftMax d s (embed d y) = embed d y := hfix s hs
  rw [h0] at h1
  exact Subtype.ext ((embed d).injective h1).symm

/-- **Leaf GT-7 (genus theory)**: for squarefree `e ≡ 7 (mod 8)` the genus field of `ℚ(√−e)` (the
subfield of the Hilbert class field fixed by `Cl²`) lies in `L_e(i) = ℚ(i, √p : p ∣ e)`; it is
`ℚ(√p* : p ∣ e)`, `p* = (−1)^{(p−1)/2} p` (Gauss; Cox, *Primes of the form x² + ny²*, Thm. 6.1 and
§6.C, UNVERIFIED numbers; TYZ L2525 uses it). Refereed (textbook). -/
def GenusFieldLeLni : Prop := ∀ e : ℕ, e % 8 = 7 → Squarefree e → genusBar e ≤ Lni e

/-- **`Class7GenusPtDefined` is glue** from the field of definition of TYZ's class-7 CM point
(`CMFieldOfDefinition7`, Gross/Shimura) and genus theory (`GenusFieldLeLni`). -/
theorem class7GenusPtDefined_of (hcm : CMFieldOfDefinition7) (hg : GenusFieldLeLni) :
    Class7GenusPtDefined := by
  intro e he hsq
  have : NeZero e := ⟨by omega⟩
  have hz := hcm e he hsq
  have hZ := Z7_mem hz
  have hfix : ∀ s ∈ picSquares (OK e), galPt (liftMax e s) (Z7 e) = Z7 e :=
    fun s hs => galPt_Z7 hz hs
  rw [mem_ptsOver_iff] at hZ ⊢
  revert hZ hfix
  rcases Z7 e with _ | ⟨x, y, h⟩
  · intro _ _; trivial
  · intro hZ hfix
    have hc : ∀ s ∈ picSquares (OK e), liftMax e s x = x ∧ liftMax e s y = y := by
      intro s hs
      have e1 := hfix s hs
      obtain ⟨h', e'⟩ := galPt_some (liftMax e s) h
      rw [e', WeierstrassCurve.Affine.Point.some.injEq] at e1
      exact e1
    exact ⟨hg e he hsq (mem_genusBar_of_fixed hZ.1 fun s hs => (hc s hs).1),
      hg e he hsq (mem_genusBar_of_fixed hZ.2 fun s hs => (hc s hs).2)⟩

end Class7Descent

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem, finest form**: as `tyzThm35ReadingA_of_pinned`, with `Class7GenusPtDefined`
replaced by the textbook leaves `CMFieldOfDefinition7` and `GenusFieldLeLni`. -/
theorem tyzThm35ReadingA_of_pinnedLeaves (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
    (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (hcm7 : CMFieldOfDefinition7)
    (hg : GenusFieldLeLni) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_pinned h11 h1 h29 hcm hi hs hN h318 (class7GenusPtDefined_of hcm7 hg) h35 h5 h7'


/-! ## §9. Existence of TYZ's `Φ₀` (so `Phi0` is never the junk value) -/

section Phi0Exists

variable (e : ℕ) [NeZero e]

theorem hle : hilbertField e ≤ H4 e := hilbertLeH4 e inferInstance

instance : Normal (QNeg e) (SeparableClosure (QNeg e)) := inferInstance

/-- **Every element of `Gal(H_e/K_e)` extends to `Gal(H_{e,4}/K_e)`**: for `d' ∈ Cl(K_e)` there is
`c₄ ∈ Pic(O_{e,4})` whose Artin symbol restricts to that of `d'` on `H_e ⊆ H_{e,4}`. -/
theorem exists_restrict (d' : Pic (OK e)) : ∃ c4 : Pic (O4 e), ∀ x : hilbertField e,
    ((artin4 e c4 ⟨x, hle e x.2⟩ : H4 e) : SeparableClosure (QNeg e)) =
      ((ringClassArtinEquiv (OK e) d' x : hilbertField e) : SeparableClosure (QNeg e)) := by
  let g := ringClassArtinEquiv (OK e) d'
  let τ : SeparableClosure (QNeg e) ≃ₐ[QNeg e] SeparableClosure (QNeg e) :=
    AlgEquiv.ofBijective (g.toAlgHom.liftNormal (SeparableClosure (QNeg e)))
      (AlgHom.normal_bijective _ _ _ _)
  refine ⟨(artin4 e).symm (AlgEquiv.restrictNormal τ (H4 e)), fun x => ?_⟩
  rw [MulEquiv.apply_symm_apply]
  have h1 := AlgEquiv.restrictNormal_commutes τ (H4 e) ⟨x, hle e x.2⟩
  have h2 := AlgHom.liftNormal_commutes g.toAlgHom (SeparableClosure (QNeg e)) x
  exact h1.trans h2

theorem exists_phi0_elem {c' : Pic (OK e)} (hc : c' ∈ picSquares (OK e)) :
    ∃ ρ : GalQ, (∃ c ∈ picSquares (O4 e), ActsAsArtin4 ρ e c) ∧ ActsAsArtinO e (OK e) ρ c' := by
  obtain ⟨d', rfl⟩ := hc
  obtain ⟨c4, hc4⟩ := exists_restrict e d'
  obtain ⟨ρ, hρ⟩ := exists_actsAsArtin4 e (c4 ^ 2)
  refine ⟨ρ, ⟨c4 ^ 2, ⟨c4, rfl⟩, hρ⟩, fun x => ?_⟩
  have h := hρ ⟨x, hle e x.2⟩
  change ρ (embed e (x : SeparableClosure (QNeg e))) = _ at h
  rw [h]
  congr 1
  have hx1 := hc4 x
  have hx2 := hc4 (ringClassArtinEquiv (OK e) d' x)
  simp only [powMonoidHom_apply, pow_two, map_mul, AlgEquiv.mul_apply]
  rw [show (artin4 e c4 ⟨x, hle e x.2⟩ : H4 e) =
      ⟨_, hle e (ringClassArtinEquiv (OK e) d' x).2⟩ from Subtype.ext hx1]
  exact hx2

open Classical in
/-- A fixed `ρ` for each square class (`exists_phi0_elem`). -/
def phi0Elem (c' : Pic (OK e)) : GalQ :=
  if h : c' ∈ picSquares (OK e) then (exists_phi0_elem e h).choose else 1

theorem artinO_inj {ρ : GalQ} {c c' : Pic (OK e)} (h : ActsAsArtinO e (OK e) ρ c)
    (h' : ActsAsArtinO e (OK e) ρ c') : c = c' := by
  apply (ringClassArtinEquiv (OK e)).injective
  ext x
  have := (h x).symm.trans (h' x)
  rw [(embed e).injective this]

/-- **TYZ's `Φ₀` exists** (TYZ L1270–1276), so `Phi0 e` satisfies `IsPhi0`. -/
theorem exists_isPhi0 : ∃ T : Finset GalQ, IsPhi0 e T := by
  classical
  refine ⟨(sqClasses e).image (phi0Elem e), ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hρ
    rw [mem_sqClasses] at hc'
    rw [phi0Elem, dite_eq_left hc']
    exact (exists_phi0_elem e hc').choose_spec.1
  · intro c' hc'
    have hspec : ∀ c ∈ picSquares (OK e), ActsAsArtinO e (OK e) (phi0Elem e c) c := fun c hc => by
      rw [phi0Elem, dite_eq_left hc]
      exact (exists_phi0_elem e hc).choose_spec.2
    refine ⟨phi0Elem e c', ⟨Finset.mem_image.mpr ⟨c', mem_sqClasses.mpr hc', rfl⟩, hspec c' hc'⟩, ?_⟩
    rintro ρ ⟨hρ, hρc⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hρ
    rw [mem_sqClasses] at hc
    rw [artinO_inj e (hspec c hc) hρc]

theorem phi0_spec : IsPhi0 e (Phi0 e) := by
  classical
  have h := exists_isPhi0 e
  simp only [Phi0, NeZero.ne e, ↓reduceDIte, h]
  exact h.choose_spec

end Phi0Exists


/-! ## §R. Restriction `H_{d,4} → H_d` of Artin symbols (verbatim from cm-bridge §12) -/

section Restrict

/-- Restriction of ring class Artin symbols to the Hilbert class field, on elements. -/
theorem coe_artin_restrict {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (c : Pic O) (x : ringClassField (maximalNumberFieldOrder K)) :
    ((ringClassArtinEquiv O c (IntermediateField.inclusion (ringClassField_maximal_le O) x) :
        ringClassField O) : SeparableClosure K) =
      ((ringClassArtinEquiv (maximalNumberFieldOrder K) (picToMax O c) x :
        ringClassField (maximalNumberFieldOrder K)) : SeparableClosure K) := by
  rw [← restrict_ringClassArtinEquiv, ← IntermediateField.coe_inclusion (ringClassField_maximal_le O),
    restrictNormalHom_inclusion_apply]

variable {d : ℕ} [NeZero d]

/-- Restriction `H_{d,4} → H_d` of Artin symbols, in `ℚ̄`. -/
theorem actsO_of_acts4 {ρ : GalQ} {c4 : Pic (O4 d)} (h : ActsAsArtin4 ρ d c4) :
    ActsAsArtinO d (OK d) ρ (picToMax (O4 d) c4) := by
  intro x
  have h1 := h (IntermediateField.inclusion (ringClassField_maximal_le (O4 d)) x)
  rw [IntermediateField.coe_inclusion] at h1
  rw [h1, coe_artin_restrict]

end Restrict

/-! ## §T. TYZ Theorem 3.3 for the pinned CM points (the leaf) -/

section Leaf

open ZInQ.RouteK.Redei

/-- `±1` from a bit: `1 ↦ 1`, the other element of `Multiplicative (ZMod 2)` `↦ −1`. -/
def sgn2 (x : Multiplicative (ZMod 2)) : ℤ := if x = 1 then 1 else -1

/-- `Pic(𝒪_{K_n})` is finite (as a `Fintype`, for sums). -/
noncomputable instance instFintypePicOK (n : ℕ) [NeZero n] : Fintype (Pic (OK n)) :=
  Fintype.ofFinite _

/-- **The genus character `χ_T = Π_{q ∈ T} χ_q`** of `Cl(K_n)`, `K_n = ℚ(√−n)`, for a set `T` of
primes of `n`, with values `±1`; `χ_q([𝔞]) = (N𝔞/q)` is the project's genus character
`RouteK.Redei.chi`. For `e = Π_{q∈T} q ≡ 1 (mod 4)` it is the Artin character of the unramified
quadratic extension `K_n(√e)/K_n` (Jacobi reciprocity: `Π_{q∣e} (p/q) = (e/p)`); every genus
character of `K_n` (`n ≡ 5, 7 (mod 8)` squarefree) is one of the `χ_T` (genus theory,
`picSquares_eq_iInf_ker_chi`). -/
def gchar (n : ℕ) [NeZero n] (T : Finset n.primeFactors) (c : Pic (OK n)) : ℤ :=
  ∏ q ∈ T, sgn2 (chi n q c)

/-- TYZ's CM point `z_n = f_n(P_n)` for both classes: `(1 − [i]) f₀(P_n)` (Heegner point of
`[16(n+1), −8, 1]`, `CM.tyzZn`) for `n ≡ 5`, the Heegner point of `[(n+δ²)/4, δ, 1]` (`tyzZ7`) else. -/
def basePt (n : ℕ) : PtA := if n % 8 = 5 then tyzZn n else tyzZ7 n

/-- **A family of lifts of `Cl(K_n)` to `Gal(ℚ̄/ℚ)`**: `f c` acts on the Hilbert class field `H_n` as
the Artin symbol of `c`, and, for `n ≡ 5 (mod 8)`, on `H_{n,4}` as the Artin symbol of some class of
`Pic(𝒪_{n,4})` (so on `H'_n ∋ z_n` as an element of TYZ's `Cl'_n = Gal(H'_n/K_n)` over `c`).
TYZ's set `Φ` of representatives of `Cl'_n/⟨kernel⟩ ≅ Cl_n` (L1316–1318) is such a family. -/
def IsLiftFamily (n : ℕ) [NeZero n] (f : Pic (OK n) → GalQ) : Prop :=
  ∀ c, ActsAsArtinO n (OK n) (f c) c ∧ (n % 8 = 5 → ∃ c4 : Pic (O4 n), ActsAsArtin4 (f c) n c4)

/-- **TYZ's `P_χ = Σ_{t ∈ Φ} χ(t) z_n^t`** (TYZ §3, the character components of the CM point
`z_n`; proof of Theorem 3.5, L2343–2380), for `χ = χ_T` and the lifts `f`. -/
def Pchi (n : ℕ) [NeZero n] (f : Pic (OK n) → GalQ) (T : Finset n.primeFactors) : PtA :=
  ∑ c : Pic (OK n), (gchar n T c) • galPt (f c) (basePt n)

/-- **TYZ's character `χ_{d₀,d₁}`** for `n = d₀d₁` (`d₁ ≡ 1, 3 (mod 8)` contributing): the genus
character of `K_n(√d₁) = K_n(√−d₀)` (for `n ≡ 5`) resp. of the unramified one of `K_n(√±d₁)` (for
`n ≡ 7`), i.e. `χ_T` with `T` the primes of whichever of `d₁`, `d₀` is `≡ 1 (mod 4)` when `d₁ ≡ 1, 3`
(for `d₁ ≡ 1 (mod 4)` it is `d₁`; for `d₁ ≡ 3 (mod 4)` it is `d₀`). Same convention as tyz-t1's
numerics (`tmany.py`: `χ_e ↔ K(√e)`, `e = d₁`). -/
def pairSet (n d₀ d₁ : ℕ) : Finset n.primeFactors :=
  Finset.univ.filter fun q => (q : ℕ) ∣ (if d₁ % 4 = 1 then d₁ else d₀)

/-- TYZ's `h₂(n)`, the 2-rank of `Cl(K_n)`: `t − 1`, `t` the number of primes dividing the
discriminant of `ℚ(√−n)` (`ramSet n`; Gauss's genus theory, `RouteK.Redei.card_ker_sq_eq`:
`#Cl[2] = 2^{t−1}`). `= k(n)` for `n ≡ 5`, `k(n) − 1` for `n ≡ 7` (tyz-t1 §2). -/
def h2 (n : ℕ) : ℕ := (ramSet n).card - 1

/-- **Leaf TYZ-3.3 (pinned): TYZ Theorem 3.3 with Lemma 3.14 (`char'`), for the pinned CM points.**

For every sign choice `ℓ` of TYZ's `𝓛`: there are `𝒫(d) = Q d / m d ∈ A(ℚ̄) ⊗ ℚ` (TYZ's
`𝒫(d) = 2^{−1−ρ(d)} 𝓛(d) α_d ∈ A(K_d)^− ⊗ ℚ`, one vector for each `d`, independent of `n`) and
`ε(d₀, d₁) ∈ μ₄` in TYZ's classes (`±i` on `(5, 3)`, `±1` on `(5,1)`, `(7,1)`, `(7,3)`) such that

* `𝒫(n) = 0` when `𝓛(n) = 0` (`n ≡ 5`; TYZ L1295 — `𝒫(n)` has the factor `𝓛(n)`);
* for every squarefree `n ≡ 5, 7 (mod 8)`, every family `f` of lifts (`IsLiftFamily`) and every
  `n = d₀d₁` with `d₁ ≡ 1, 3 (mod 8)`: `P_{χ_{d₀,d₁}} = ε(d₀,d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` in
  `A(ℚ̄) ⊗ ℚ`, i.e. `m(d₀) P_χ − ε 2^{h₂} ℓ(d₁) Q(d₀)` is torsion (TYZ Theorem 3.3, L1299–1311);
* for `n ≡ 5` and `d₁ ≡ 5, 7 (mod 8)`, `P_{χ_{d₀,d₁}}` is torsion (TYZ Lemma 3.14 = first part of
  Theorem 3.3: `P_χ` is non-torsion only for the contributing `χ_{d₀,d₁}`; for `n ≡ 5` the `2^{k}`
  characters `χ_T` are distinct (genus theory, `RouteK.Redei.exists_chi_eq`), so these are not
  contributing characters).

Sources: TYZ (Tian–Yuan–Zhang, arXiv:1411.4728v1; Asian J. Math. 21 (2017)) Theorem 3.3
(L1299–1311, proof L1865–2023) with Lemma 3.14 (`char'`, L1868) and Lemma 3.15 (`multiples1`, L1919);
its inputs are TYZ's explicit Gross–Zagier formula Theorem A.9 (L3062–3077, from Yuan–Zhang–Zhang)
and Gross–Zagier/Kolyvagin; the constant's unprinted computation (L2014–2015) is written out and
tested in `tyz-t1.md`. Refereed. As stated here it is a consequence of the published theorem plus:
`ℓ = ±𝓛` on classes 1, 3 (signs absorbed into `ε`) and `ℓ(n) = 0 ↔ 𝓛(n) = 0` on class 5
(`IsTYZLcal`, TYZ L338–345); `z_n ∈ A(H'_n)` (Shimura reciprocity + TYZ Thm 3.6(1)); for `n ≡ 5`, that
`P_χ` modulo torsion does not depend on the choice of the lifts (the fibres of
`Pic(𝒪_{n,4}) → Cl_n` are `⟨σ_{1+2ϖ}, σ_ϖ²⟩`, which fix `z_n` resp. add `τ(1)`: TYZ Prop 3.2,
Thm 3.6(1), as quoted in tyz-t1 §3.1; HUMAN CHECK against the source). Numerically VERIFIED by
tyz-t1 (`tmany.py`: 73 contributing pairs and 102 excluded characters, 30 values `n ≡ 5`, exactly
this convention for `χ_{d₀,d₁}`). -/
def TYZThm33Pinned (ℓ : ℕ → ℤ) : Prop :=
  ∃ (Q : ℕ → PtA) (m : ℕ → ℕ) (ε : ℕ → ℕ → GaussianInt),
    (∀ d, 0 < m d) ∧
    (∀ d₀ d₁ : ℕ, d₀ % 8 = 5 → d₁ % 8 = 3 → ε d₀ d₁ = gi ∨ ε d₀ d₁ = -gi) ∧
    (∀ d₀ d₁ : ℕ, (d₀ % 8 = 5 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 3) →
      ε d₀ d₁ = 1 ∨ ε d₀ d₁ = -1) ∧
    (∀ n : ℕ, Squarefree n → n % 8 = 5 → ℓ n = 0 → IsOfFinAddOrder (Q n)) ∧
    ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
      ∀ f : Pic (OK n) → GalQ, IsLiftFamily n f →
        (∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₁ % 8 = 1 ∨ d₁ % 8 = 3) →
          IsOfFinAddOrder ((m d₀ : GaussianInt) • Pchi n f (pairSet n d₀ d₁) -
            (ε d₀ d₁ * 2 ^ h2 n * (ℓ d₁ : GaussianInt)) • Q d₀)) ∧
        (n % 8 = 5 → ∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₁ % 8 = 5 ∨ d₁ % 8 = 7) →
          IsOfFinAddOrder (Pchi n f (pairSet n d₀ d₁)))

end Leaf


/-! ## §G. Glue: `Thm35First ℓ tyzZ` from `TYZThm33Pinned ℓ` (all proved) -/

section Glue

open ZInQ.RouteK.Redei

attribute [local instance] Classical.propDecidable

/-! ### G.1 Torsion -/

/-- The torsion points of `A(ℚ̄)`, a `ℤ[i]`-submodule. -/
def torG : Submodule GaussianInt PtA where
  carrier := {P | IsOfFinAddOrder P}
  add_mem' ha hb := IsOfFinAddOrder.add ha hb
  zero_mem' := IsOfFinAddOrder.zero
  smul_mem' r P hP := (DistribSMul.toAddMonoidHom PtA r).isOfFinAddOrder hP

theorem mkQ_eq_zero_iff {P : PtA} : torG.mkQ P = 0 ↔ IsOfFinAddOrder P := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; rfl

/-- `A(ℚ̄)/torsion` is torsion-free. -/
theorem quot_cancel {k : ℕ} (hk : k ≠ 0) {a : PtA ⧸ torG} (h : (k : GaussianInt) • a = 0) :
    a = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective torG a
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  rw [Submodule.Quotient.mk_eq_zero]
  have h' : k • x ∈ torG := by rwa [← Nat.cast_smul_eq_nsmul GaussianInt]
  exact IsOfFinAddOrder.of_nsmul h' hk

/-! ### G.2 The character sum (genus theory) -/

theorem sgn2_mul : ∀ x y : Multiplicative (ZMod 2), sgn2 (x * y) = sgn2 x * sgn2 y := by decide

/-- `sgn2` as a monoid hom. -/
def sgnHom : Multiplicative (ZMod 2) →* ℤ where
  toFun := sgn2
  map_one' := by simp [sgn2]
  map_mul' := sgn2_mul

variable {n : ℕ} [NeZero n]

theorem sum_gchar (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) (c : Pic (OK n)) :
    ∑ T : Finset n.primeFactors, gchar n T c =
      if c ∈ picSquares (OK n) then 2 ^ n.primeFactors.card else 0 := by
  classical
  have e1 : ∑ T : Finset n.primeFactors, gchar n T c =
      ∏ q : n.primeFactors, (sgn2 (chi n q c) + 1) := by
    rw [Finset.prod_add_one, Finset.powerset_univ]; rfl
  rw [e1]
  have hsqi := picSquares_eq_iInf_ker_chi n hn hsq h1
  have hiff : c ∈ picSquares (OK n) ↔ ∀ q, chi n q c = 1 :=
    (SetLike.ext_iff.mp hsqi c).trans (Subgroup.mem_iInf.trans (forall_congr' fun q => MonoidHom.mem_ker))
  split_ifs with hc
  · rw [hiff] at hc
    have : ∀ q : n.primeFactors, sgn2 (chi n q c) + 1 = 2 := fun q => by
      rw [hc q]; simp [sgn2]
    rw [Finset.prod_congr rfl (fun q _ => this q), Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]
  · rw [hiff, not_forall] at hc
    obtain ⟨q, hq⟩ := hc
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    simp [sgn2, hq]

/-- **The character formula** (TYZ L998, proof of Theorem 3.5): `Σ_χ P_χ = 2^{k} Σ_{c ∈ 2Cl} z^{f c}`. -/
theorem sum_Pchi (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) (f : Pic (OK n) → GalQ) :
    ∑ T : Finset n.primeFactors, Pchi n f T =
      (2 ^ n.primeFactors.card : ℤ) •
        ∑ c ∈ Finset.univ.filter (· ∈ picSquares (OK n)), galPt (f c) (basePt n) := by
  classical
  simp only [Pchi]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_gchar hn hsq h1, ite_smul, zero_smul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.smul_sum]

/-- **Genus theory, product formula**: for `n ≡ 3 (mod 4)`, `Π_{q ∣ n} χ_q = 1` (the image of the
genus map is the sum-zero hyperplane: it contains it by `exists_chi_eq` and has the same order
`2^{t−1} = #Cl[2]`). -/
theorem prod_sgn_chi_eq_one (h4 : n % 4 = 3) (hsq : Squarefree n) (h1 : 1 < n) (c : Pic (OK n)) :
    ∏ q : n.primeFactors, sgnHom (chi n q c) = 1 := by
  classical
  have hn : Odd n := Nat.odd_iff.mpr (by omega)
  rw [← map_prod]
  suffices hs : ∑ q, Multiplicative.toAdd (chi n q c) = 0 by
    have : ∏ q, chi n q c = 1 := by
      apply Multiplicative.toAdd.injective; rw [toAdd_prod, hs]; rfl
    rw [this, map_one]
  have hne := fourRank_primeFactors_nonempty h1
  have hle : (fourRankSum n.primeFactors).ker ≤ (genusMap n).range := by
    intro ε hε
    rw [MonoidHom.mem_ker] at hε
    have hs : ∑ q, Multiplicative.toAdd ε q = 0 := by
      rw [← fourRankSum_apply, hε]; rfl
    obtain ⟨c, hc⟩ := exists_chi_eq n hn hsq (Multiplicative.toAdd ε) fun _ => hs
    refine ⟨c, ?_⟩
    apply Multiplicative.toAdd.injective
    funext q
    rw [genusMap_apply, hc q, toAdd_ofAdd]
  have hcardR : Nat.card (genusMap n).range ≤ Nat.card (fourRankSum n.primeFactors).ker := by
    obtain ⟨hR, hK⟩ := range_sq_eq_ker_genusMap_and_card hn hsq h1
    have hA := card_ker_sq_mul_card_range_sq (G := ClassGroup (𝓞 (QNeg n)))
    have hB := Subgroup.card_ker_mul_card_range (genusMap n)
    rw [← hR] at hB
    have hk := card_ker_fourRankSum (ι := n.primeFactors) hne
    rw [fourRank_card_ramSet hn, if_pos h4] at hK
    rw [Fintype.card_coe] at hk
    have hpos : 0 < Nat.card (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* _).range := Nat.card_pos
    have hRc : Nat.card (genusMap n).range =
        Nat.card (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* _).ker := by
      have := hA.trans hB.symm
      rw [mul_comm] at this
      exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
    have hcpos : 0 < n.primeFactors.card := by
      obtain ⟨q⟩ := hne; exact Finset.card_pos.2 ⟨q, q.2⟩
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hcpos.ne'
    rw [hr, pow_succ] at hk
    rw [hr, Nat.succ_sub_one] at hK
    omega
  have heq := Subgroup.eq_of_le_of_card_ge hle hcardR
  have hmem : genusMap n c ∈ (fourRankSum n.primeFactors).ker := heq ▸ ⟨c, rfl⟩
  rw [MonoidHom.mem_ker] at hmem
  have := congrArg Multiplicative.toAdd hmem
  rw [fourRankSum_apply] at this
  exact this

/-! ### G.3 Subsets of primes and divisors -/

/-- The primes of `n` dividing `e`. -/
def divSet (n e : ℕ) : Finset n.primeFactors := Finset.univ.filter fun q => (q : ℕ) ∣ e

theorem pairSet_eq (n d₁ : ℕ) :
    pairSet n (n / d₁) d₁ = divSet n (if d₁ % 4 = 1 then d₁ else n / d₁) := rfl

theorem divSet_prod (T : Finset n.primeFactors) : divSet n (∏ q ∈ T, (q : ℕ)) = T := by
  classical
  ext q
  simp only [divSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hq := Nat.prime_of_mem_primeFactors q.2
  constructor
  · intro h
    obtain ⟨q', hq', hd⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors q'.2)).mp hd
    rwa [show q = q' from Subtype.ext this]
  · intro h; exact Finset.dvd_prod_of_mem (fun q : n.primeFactors => (q : ℕ)) h

theorem prod_divSet (hsq : Squarefree n) {e : ℕ} (he : e ∣ n) :
    ∏ q ∈ divSet n e, (q : ℕ) = e := by
  classical
  have hsqe : Squarefree e := hsq.squarefree_of_dvd he
  have he0 : e ≠ 0 := hsqe.ne_zero
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsqe]
  rw [show (∏ q ∈ divSet n e, (q : ℕ)) =
      ∏ p ∈ (divSet n e).map (Function.Embedding.subtype _), p from
        (Finset.prod_map (divSet n e) (Function.Embedding.subtype _) (fun p : ℕ => p)).symm]
  congr 1
  ext p
  simp only [Finset.mem_map, Function.Embedding.coe_subtype, divSet, Finset.mem_filter,
    Finset.mem_univ, true_and, Nat.mem_primeFactors]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨Nat.prime_of_mem_primeFactors q.2, hq, he0⟩
  · rintro ⟨hp, hpe, -⟩
    exact ⟨⟨p, Nat.mem_primeFactors.2 ⟨hp, hpe.trans he, hsq.ne_zero⟩⟩, hpe, rfl⟩

theorem sum_finset_eq_sum_divisors (hsq : Squarefree n) {M : Type*} [AddCommMonoid M]
    (F : Finset n.primeFactors → M) :
    ∑ T, F T = ∑ e ∈ n.divisors, F (divSet n e) := by
  classical
  apply Finset.sum_nbij' (fun T : Finset n.primeFactors => ∏ q ∈ T, (q : ℕ)) (fun e : ℕ => divSet n e)
  · intro T _
    rw [Nat.mem_divisors]
    refine ⟨?_, hsq.ne_zero⟩
    calc ∏ q ∈ T, (q : ℕ) ∣ ∏ q : n.primeFactors, (q : ℕ) :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ T)
      _ = ∏ p ∈ n.primeFactors, p := Finset.prod_coe_sort n.primeFactors (fun p => p)
      _ = n := Nat.prod_primeFactors_of_squarefree hsq
  · intro e _; simp
  · intro T _; exact divSet_prod T
  · intro e he; exact prod_divSet hsq (Nat.dvd_of_mem_divisors he)
  · intro T _; rw [divSet_prod]

/-- `e ∣ n` squarefree: the primes of `n/e` are the other primes of `n`. -/
theorem divSet_div (hsq : Squarefree n) {e : ℕ} (he : e ∣ n) :
    divSet n (n / e) = (divSet n e)ᶜ := by
  classical
  ext ⟨p, hp⟩
  simp only [divSet, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  have hq := Nat.prime_of_mem_primeFactors hp
  obtain ⟨k, hk⟩ := he
  have he0 : e ≠ 0 := by rintro rfl; simp at hk; exact hsq.ne_zero hk
  have hdiv : n / e = k := by rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)]
  have hqn : p ∣ e * k := by rw [← hk]; exact Nat.dvd_of_mem_primeFactors hp
  rw [hdiv]
  constructor
  · intro hqk hqe
    have : p * p ∣ n := by rw [hk]; exact Nat.mul_dvd_mul hqe hqk
    exact hq.one_lt.ne' (Nat.isUnit_iff.mp (hsq _ this))
  · intro hqe
    exact (hq.dvd_mul.mp hqn).resolve_left hqe

/-- For `n ≡ 3 (mod 4)` the characters of `T` and of its complement agree. -/
theorem Pchi_compl (h4 : n % 4 = 3) (hsq : Squarefree n) (h1 : 1 < n) (f : Pic (OK n) → GalQ)
    {e : ℕ} (he : e ∣ n) : Pchi n f (divSet n (n / e)) = Pchi n f (divSet n e) := by
  classical
  unfold Pchi
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hp := prod_sgn_chi_eq_one h4 hsq h1 c
  rw [← Finset.prod_mul_prod_compl (divSet n e)] at hp
  rw [divSet_div hsq he]
  unfold gchar
  change ∏ q ∈ (divSet n e)ᶜ, sgnHom (chi n q c) = ∏ q ∈ divSet n e, sgnHom (chi n q c)
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hp with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;>
    rw [h1', h2']

theorem mod_lemma {a b n : ℕ} (h : a * b = n) :
    n % 8 = (a % 8) * (b % 8) % 8 := by
  rw [← h, Nat.mul_mod]

theorem odd_of_mem_divisors (hodd : n % 2 = 1) {d₁ : ℕ} (hd : d₁ ∈ n.divisors) : d₁ % 2 = 1 := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mem_divisors hd
  rcases Nat.even_or_odd d₁ with ⟨r, hr⟩ | h
  · exfalso
    have : n = 2 * (r * k) := by rw [hk, hr]; ring
    omega
  · exact Nat.odd_iff.mp h

/-- `gmap n d₁`: the factor of `n = d₀d₁` whose primes give `χ_{d₀,d₁}`. -/
def gmap (n d₁ : ℕ) : ℕ := if d₁ % 4 = 1 then d₁ else n / d₁

theorem gmap_mem {d₁ : ℕ} (hd : d₁ ∈ n.divisors) : gmap n d₁ ∈ n.divisors := by
  unfold gmap
  split_ifs
  · exact hd
  · exact Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), NeZero.ne n⟩

theorem div_div_of_mem {d₁ : ℕ} (hd : d₁ ∈ n.divisors) : n / (n / d₁) = d₁ :=
  Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (NeZero.ne n)

theorem div_mul_of_mem {d₁ : ℕ} (hd : d₁ ∈ n.divisors) : n / d₁ * d₁ = n :=
  Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)

/-- Odd `n ≡ 1 (mod 4)`: `gmap n` is an involution of the divisors. -/
theorem gmap_gmap (h4 : n % 4 = 1) {d₁ : ℕ} (hd : d₁ ∈ n.divisors) : gmap n (gmap n d₁) = d₁ := by
  have hm := mod_lemma (div_mul_of_mem hd)
  unfold gmap
  by_cases h : d₁ % 4 = 1
  · simp [h]
  · have hd4 : (n / d₁) % 4 ≠ 1 := by
      have h8 : n % 8 = 1 ∨ n % 8 = 5 := by omega
      have ha8 : (n / d₁) % 8 < 8 := Nat.mod_lt _ (by norm_num)
      have hb8 : d₁ % 8 < 8 := Nat.mod_lt _ (by norm_num)
      interval_cases hx : (n / d₁) % 8 <;> interval_cases hy : d₁ % 8 <;> omega
    simp only [h, ↓reduceIte, hd4, div_div_of_mem hd]

/-- Odd `n ≡ 3 (mod 4)`: `gmap n (n / d₁) = gmap n d₁`. -/
theorem gmap_div (h4 : n % 4 = 3) {d₁ : ℕ} (hd : d₁ ∈ n.divisors) : gmap n (n / d₁) = gmap n d₁ := by
  have hm := mod_lemma (div_mul_of_mem hd)
  have h8 : n % 8 = 3 ∨ n % 8 = 7 := by omega
  have ha8 : (n / d₁) % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hb8 : d₁ % 8 < 8 := Nat.mod_lt _ (by norm_num)
  unfold gmap
  by_cases h : d₁ % 4 = 1
  · have hd4 : (n / d₁) % 4 ≠ 1 := by
      interval_cases hx : (n / d₁) % 8 <;> interval_cases hy : d₁ % 8 <;> omega
    simp only [h, ↓reduceIte, hd4, div_div_of_mem hd]
  · have hd4 : (n / d₁) % 4 = 1 := by
      have hodd := odd_of_mem_divisors (n := n) (by omega) hd
      interval_cases hx : (n / d₁) % 8 <;> interval_cases hy : d₁ % 8 <;> omega
    simp only [h, ↓reduceIte, hd4]

/-- **`Σ_{T} P_T = Σ_{n = d₀d₁} P_{χ_{d₀,d₁}}`** (every ordered factorization, each character of
`Cl(K_n)` met once for `n ≡ 1 (mod 4)`; for `n ≡ 3 (mod 4)` both sides count each character twice). -/
theorem sum_Pchi_divisors (hsq : Squarefree n) (hodd : n % 2 = 1) (h1 : 1 < n)
    (f : Pic (OK n) → GalQ) :
    ∑ T, Pchi n f T = ∑ d₁ ∈ n.divisors, Pchi n f (pairSet n (n / d₁) d₁) := by
  classical
  rw [sum_finset_eq_sum_divisors hsq]
  simp_rw [pairSet_eq]
  change _ = ∑ d₁ ∈ n.divisors, Pchi n f (divSet n (gmap n d₁))
  rcases (show n % 4 = 1 ∨ n % 4 = 3 by omega) with h4 | h4
  · symm
    apply Finset.sum_nbij' (gmap n) (gmap n)
    · intro d hd; exact gmap_mem hd
    · intro d hd; exact gmap_mem hd
    · intro d hd; exact gmap_gmap h4 hd
    · intro d hd; exact gmap_gmap h4 hd
    · intro d _; rfl
  · refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
    unfold gmap
    split_ifs
    · rfl
    · exact (Pchi_compl h4 hsq h1 f (Nat.dvd_of_mem_divisors hd₁)).symm

/-- The contributing `d₁` (classes 1, 3). -/
def contrib (n : ℕ) : Finset ℕ := n.divisors.filter fun d₁ => d₁ % 8 = 1 ∨ d₁ % 8 = 3

/-- `n ≡ 7 (mod 8)`: the non-contributing half equals the contributing half (`d₁ ↦ n/d₁`). -/
theorem sum_divisors_seven (h7 : n % 8 = 7) (G : ℕ → PtA)
    (hG : ∀ d₁ ∈ n.divisors, G (n / d₁) = G d₁) :
    ∑ d₁ ∈ n.divisors, G d₁ = 2 • ∑ d₁ ∈ contrib n, G d₁ := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d₁ => d₁ % 8 = 1 ∨ d₁ % 8 = 3),
    two_nsmul]
  congr 1
  symm
  have hmem : ∀ d ∈ n.divisors, n / d ∈ n.divisors := fun d hd =>
    Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), NeZero.ne n⟩
  apply Finset.sum_nbij' (fun d => n / d) (fun d => n / d)
  · intro d hd
    obtain ⟨hd, hc⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr ⟨hmem d hd, ?_⟩
    have hm := mod_lemma (div_mul_of_mem hd)
    have ha8 : (n / d) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hb8 : d % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases hx : (n / d) % 8 <;> interval_cases hy : d % 8 <;> omega
  · intro d hd
    obtain ⟨hd, hc⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr ⟨hmem d hd, ?_⟩
    have hm := mod_lemma (div_mul_of_mem hd)
    have ha8 : (n / d) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hb8 : d % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases hx : (n / d) % 8 <;> interval_cases hy : d % 8 <;> omega
  · intro d hd
    exact div_div_of_mem (Finset.mem_filter.mp hd).1
  · intro d hd
    exact div_div_of_mem (Finset.mem_filter.mp hd).1
  · intro d hd
    exact (hG d (Finset.mem_filter.mp hd).1).symm

/-- `ℕ`-casts act as `nsmul`. -/
theorem natCast_gsmul (k : ℕ) (P : PtA) : ((k : GaussianInt)) • P = k • P := by
  first
    | exact Nat.cast_smul_eq_nsmul GaussianInt k P
    | (rw [gsmul_def]; simp)

theorem natCast_gsmul_q (k : ℕ) (P : PtA ⧸ torG) : ((k : GaussianInt)) • P = k • P := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_smul, ih, one_smul, succ_nsmul]

/-! ### G.4 A lift family whose square part is `Φ₀` -/

/-- Some lift of `c ∈ Cl(K_n)` acting on `H_{n,4}` as an Artin symbol. -/
def liftAny (n : ℕ) [NeZero n] (c : Pic (OK n)) : GalQ :=
  (exists_actsAsArtin4 n ((picToMax_surjective (O4 n) c).choose)).choose

theorem liftAny_spec (c : Pic (OK n)) :
    ActsAsArtinO n (OK n) (liftAny n c) c ∧ ∃ c4 : Pic (O4 n), ActsAsArtin4 (liftAny n c) n c4 := by
  have h4 := (exists_actsAsArtin4 n ((picToMax_surjective (O4 n) c).choose)).choose_spec
  have hO := actsO_of_acts4 h4
  rw [(picToMax_surjective (O4 n) c).choose_spec] at hO
  exact ⟨hO, _, h4⟩

theorem picToMax_mem_picSquares {c4 : Pic (O4 n)} (h : c4 ∈ picSquares (O4 n)) :
    picToMax (O4 n) c4 ∈ picSquares (OK n) := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨picToMax (O4 n) b, by simp [map_pow]⟩

/-- **The pinned genus point as a character-free sum over a lift family**: there is a lift family `f`
with `Σ_{c ∈ 2Cl_n} z_n^{f c} = Z(n) = tyzZ n` (for `n ≡ 5`, `f` takes the values `Φ₀(n)` on `2Cl_n`). -/
theorem exists_liftFamily (hc : n % 8 = 5 ∨ n % 8 = 7) :
    ∃ f : Pic (OK n) → GalQ, IsLiftFamily n f ∧
      ∑ c ∈ Finset.univ.filter (· ∈ picSquares (OK n)), galPt (f c) (basePt n) = tyzZ n := by
  classical
  rcases hc with h5 | h7
  · have hP := phi0_spec n
    let f : Pic (OK n) → GalQ := fun c =>
      if hc : c ∈ picSquares (OK n) then (hP.2 c hc).exists.choose else liftAny n c
    have hfsq : ∀ c (hc : c ∈ picSquares (OK n)),
        f c ∈ Phi0 n ∧ ActsAsArtinO n (OK n) (f c) c := fun c hc => by
      simp only [f, dif_pos hc]; exact (hP.2 c hc).exists.choose_spec
    refine ⟨f, fun c => ?_, ?_⟩
    · by_cases hc : c ∈ picSquares (OK n)
      · refine ⟨(hfsq c hc).2, fun _ => ?_⟩
        obtain ⟨c4, -, h4⟩ := hP.1 _ (hfsq c hc).1
        exact ⟨c4, h4⟩
      · have hf : f c = liftAny n c := by simp only [f, dif_neg hc]
        rw [hf]
        exact ⟨(liftAny_spec c).1, fun _ => (liftAny_spec c).2⟩
    · rw [tyzZ_five h5, genusSum, basePt, if_pos h5]
      apply Finset.sum_bij (fun c _ => f c)
      · intro c hc
        exact (hfsq c (Finset.mem_filter.mp hc).2).1
      · intro c₁ h₁ c₂ h₂ he
        have e1 := (hfsq c₁ (Finset.mem_filter.mp h₁).2).2
        have e2 := (hfsq c₂ (Finset.mem_filter.mp h₂).2).2
        rw [he] at e1
        exact artinO_inj n e1 e2
      · intro ρ hρ
        obtain ⟨c4, hc4, h4⟩ := hP.1 ρ hρ
        have hsq := picToMax_mem_picSquares hc4
        refine ⟨picToMax (O4 n) c4, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsq⟩, ?_⟩
        exact (hP.2 _ hsq).unique (hfsq _ hsq) ⟨hρ, actsO_of_acts4 h4⟩
      · intro c _; rfl
  · refine ⟨liftMax n, fun c => ⟨liftMax_spec n c, fun h => by omega⟩, ?_⟩
    have h5 : ¬ n % 8 = 5 := by omega
    rw [tyzZ_seven h7, Z7_eq, basePt, if_neg h5]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext c
    simp [mem_sqClasses]

/-! ### G.5 The level identity and the induction -/

/-- The common denominator at level `d`. -/
def bigM (m : ℕ → ℕ) (d : ℕ) : ℕ := ∏ x ∈ d.divisors, m (d / x)

/-- The cofactor of `m (d / d₁)` in `bigM m d`. -/
def cofR (m : ℕ → ℕ) (d d₁ : ℕ) : ℕ := ∏ x ∈ d.divisors.erase d₁, m (d / x)

theorem bigM_eq {m : ℕ → ℕ} {d d₁ : ℕ} (h : d₁ ∈ d.divisors) :
    bigM m d = m (d / d₁) * cofR m d d₁ :=
  (Finset.mul_prod_erase d.divisors (fun x => m (d / x)) h).symm

theorem cofR_pos {m : ℕ → ℕ} (hm : ∀ d, 0 < m d) (d d₁ : ℕ) : cofR m d d₁ ≠ 0 :=
  (Finset.prod_pos fun x _ => hm _).ne'

/-- **Level identity** (TYZ's proof of Theorem 3.5, L2343–2380, at one level `d`): in
`A(ℚ̄)/torsion`, `M·Z(d) = Σ_{d = d₀d₁, d₁ ≡ 1,3} R(d₁) ε(d₀,d₁) ℓ(d₁) Q(d₀)`. -/
theorem level_identity {ℓ : ℕ → ℤ} {Q : ℕ → PtA} {m : ℕ → ℕ} {ε : ℕ → ℕ → GaussianInt}
    (hm : ∀ d, 0 < m d)
    (hP : ∀ f : Pic (OK n) → GalQ, IsLiftFamily n f →
        (∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₁ % 8 = 1 ∨ d₁ % 8 = 3) →
          IsOfFinAddOrder ((m d₀ : GaussianInt) • Pchi n f (pairSet n d₀ d₁) -
            (ε d₀ d₁ * 2 ^ h2 n * (ℓ d₁ : GaussianInt)) • Q d₀)) ∧
        (n % 8 = 5 → ∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₁ % 8 = 5 ∨ d₁ % 8 = 7) →
          IsOfFinAddOrder (Pchi n f (pairSet n d₀ d₁))))
    (hsq : Squarefree n) (hc : n % 8 = 5 ∨ n % 8 = 7) :
    torG.mkQ ((bigM m n : GaussianInt) • tyzZ n) =
      ∑ d₁ ∈ contrib n, torG.mkQ
        (((cofR m n d₁ : GaussianInt) * ε (n / d₁) d₁ * (ℓ d₁ : GaussianInt)) • Q (n / d₁)) := by
  classical
  have hodd : n % 2 = 1 := by omega
  have hn : Odd n := Nat.odd_iff.mpr hodd
  have h1 : 1 < n := by omega
  obtain ⟨f, hf, hZ⟩ := exists_liftFamily hc
  obtain ⟨ha, hb⟩ := hP f hf
  set k := n.primeFactors.card with hk
  set G : ℕ → PtA := fun d₁ => Pchi n f (pairSet n (n / d₁) d₁) with hG
  have hsum : ((2 ^ k : ℕ) : GaussianInt) • tyzZ n = ∑ d₁ ∈ n.divisors, G d₁ := by
    rw [← sum_Pchi_divisors hsq hodd h1 f, sum_Pchi hn hsq h1 f, hZ, natCast_gsmul]
    have e2 : ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) := by push_cast; rfl
    rw [e2, natCast_zsmul]
  -- the contributing part
  have hcon : torG.mkQ (∑ d₁ ∈ n.divisors, G d₁) =
      (((if n % 8 = 5 then 1 else 2 : ℕ)) : GaussianInt) • torG.mkQ (∑ d₁ ∈ contrib n, G d₁) := by
    rcases hc with h5 | h7
    · rw [if_pos h5, Nat.cast_one, one_smul, contrib,
        ← Finset.sum_filter_add_sum_filter_not n.divisors (fun d₁ => d₁ % 8 = 1 ∨ d₁ % 8 = 3),
        map_add, add_eq_left, map_sum]
      refine Finset.sum_eq_zero fun d₁ hd₁ => ?_
      rw [Finset.mem_filter] at hd₁
      rw [mkQ_eq_zero_iff]
      have ho := odd_of_mem_divisors hodd hd₁.1
      exact hb h5 (n / d₁) d₁ (div_mul_of_mem hd₁.1) (by omega)
    · have h5 : ¬ n % 8 = 5 := by omega
      rw [if_neg h5, sum_divisors_seven h7 G fun d₁ hd₁ => ?_, natCast_gsmul_q, map_nsmul]
      simp only [hG]
      rw [pairSet_eq, pairSet_eq, div_div_of_mem hd₁]
      have hg := gmap_div (n := n) (by omega) hd₁
      unfold gmap at hg
      rw [div_div_of_mem hd₁] at hg
      rw [hg]
  have hterm : ∀ d₁ ∈ contrib n, (bigM m n : GaussianInt) • torG.mkQ (G d₁) =
      ((2 ^ h2 n : ℕ) : GaussianInt) • torG.mkQ
        (((cofR m n d₁ : GaussianInt) * ε (n / d₁) d₁ * (ℓ d₁ : GaussianInt)) • Q (n / d₁)) := by
    intro d₁ hd₁
    rw [contrib, Finset.mem_filter] at hd₁
    have h := ha (n / d₁) d₁ (div_mul_of_mem hd₁.1) hd₁.2
    rw [← mkQ_eq_zero_iff, map_sub, sub_eq_zero, map_smul, map_smul] at h
    rw [bigM_eq hd₁.1, Nat.cast_mul, mul_comm, mul_smul, h, map_smul, smul_smul, smul_smul]
    congr 1
    push_cast; ring
  have hk2 : (2 ^ k : ℕ) = (if n % 8 = 5 then 1 else 2) * 2 ^ h2 n := by
    unfold h2
    rw [fourRank_card_ramSet hn]
    rcases hc with h5 | h7
    · rw [if_neg (show ¬ n % 4 = 3 by omega), if_pos h5]
      simp [hk]
    · rw [if_pos (show n % 4 = 3 by omega), if_neg (show ¬ n % 8 = 5 by omega)]
      have hpos : 0 < n.primeFactors.card := by
        obtain ⟨q⟩ := fourRank_primeFactors_nonempty h1; exact Finset.card_pos.2 ⟨q, q.2⟩
      rw [← hk] at hpos ⊢
      obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hr, Nat.succ_sub_one, pow_succ]; ring
  apply sub_eq_zero.mp
  apply quot_cancel (k := 2 ^ k) (by positivity)
  rw [smul_sub, ← map_smul, smul_comm, map_smul, hsum, hcon, smul_comm, map_sum, Finset.smul_sum,
    Finset.sum_congr rfl hterm, ← Finset.smul_sum, smul_smul, ← Nat.cast_mul, ← hk2, Finset.smul_sum,
    sub_self]


/-- **Main glue theorem**: TYZ Theorem 3.5, first assertion, for the pinned genus points, from TYZ
Theorem 3.3 (with Lemma 3.14) for the pinned CM points; only `ℓ(1) = 1` is used of `ℓ`. TYZ's proof
(L2343–2380): character formula + induction on `n`, made Lean. -/
theorem thm35First_of_thm33 (ℓ : ℕ → ℤ) (hℓ1 : ℓ 1 = 1) (h : TYZThm33Pinned ℓ) :
    Thm35First ℓ tyzZ := by
  classical
  obtain ⟨Q, m, ε, hm, hε53, hε1, hQ0, hP⟩ := h
  set ε' : ℕ → ℕ → GaussianInt := fun d₀ d₁ => ε d₀ d₁ * ε d₀ 1 with hε'
  set Q' : ℕ → PtA := fun d => ε d 1 • Q d with hQ'
  have hsq1 : ∀ d, (d % 8 = 5 ∨ d % 8 = 7) → ε d 1 * ε d 1 = 1 := by
    intro d hd
    have h1 : ε d 1 = 1 ∨ ε d 1 = -1 := by
      apply hε1
      rcases hd with h | h
      · exact Or.inl ⟨h, rfl⟩
      · exact Or.inr (Or.inl ⟨h, rfl⟩)
    rcases h1 with h | h <;> rw [h] <;> ring
  have key : ∀ d, Squarefree d → (d % 8 = 5 ∨ d % 8 = 7) →
      torG.mkQ ((m d : GaussianInt) • Pseq ℓ ε' tyzZ d) = torG.mkQ (Q' d) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro hsq hc
      haveI : NeZero d := ⟨hsq.ne_zero⟩
      have hd0 : d ≠ 0 := hsq.ne_zero
      have hL := level_identity hm (hP d inferInstance hsq hc) hsq hc
      set F : Finset ℕ := d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3))
        with hF
      have hcontrib : contrib d = insert 1 F := by
        ext d₁
        simp only [contrib, hF, Finset.mem_filter, Finset.mem_insert, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hd, hd0'⟩, hcl⟩
          by_cases h1 : d₁ = 1
          · left; exact h1
          · right
            refine ⟨⟨hd, hd0'⟩, ?_, hcl⟩
            have := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hd0')
            omega
        · rintro (rfl | ⟨⟨hd, hd0'⟩, -, hcl⟩)
          · exact ⟨⟨one_dvd _, hd0⟩, Or.inl rfl⟩
          · exact ⟨⟨hd, hd0'⟩, hcl⟩
      have h1F : 1 ∉ F := by simp [hF]
      rw [hcontrib, Finset.sum_insert h1F, Nat.div_one, hℓ1] at hL
      have hstep : ∀ d₁ ∈ F, (bigM m d : GaussianInt) • torG.mkQ
          ((ε' (d / d₁) d₁ * (ℓ d₁ : GaussianInt)) • Pseq ℓ ε' tyzZ (d / d₁)) =
          torG.mkQ (((cofR m d d₁ : GaussianInt) * ε (d / d₁) d₁ * (ℓ d₁ : GaussianInt)) •
            Q (d / d₁)) := by
        intro d₁ hd₁
        have hdiv := div_class (n := d) (Nat.mem_divisors_self d hd0) hc hd₁
        obtain ⟨hd₁d, hlt, -⟩ := Finset.mem_filter.mp hd₁
        have hlt' : d / d₁ < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hlt
        have hsq' : Squarefree (d / d₁) :=
          hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd₁d))
        have ih' := ih _ hlt' hsq' hdiv.2
        calc (bigM m d : GaussianInt) • torG.mkQ
              ((ε' (d / d₁) d₁ * (ℓ d₁ : GaussianInt)) • Pseq ℓ ε' tyzZ (d / d₁))
            = ((ε' (d / d₁) d₁ * (ℓ d₁ : GaussianInt)) * (cofR m d d₁ : GaussianInt)) •
                torG.mkQ ((m (d / d₁) : GaussianInt) • Pseq ℓ ε' tyzZ (d / d₁)) := by
              rw [map_smul, map_smul, smul_smul, smul_smul, bigM_eq hd₁d, Nat.cast_mul]
              congr 1; ring
          _ = torG.mkQ (((cofR m d d₁ : GaussianInt) * ε (d / d₁) d₁ * (ℓ d₁ : GaussianInt)) •
                Q (d / d₁)) := by
              rw [ih']
              simp only [hQ']
              rw [map_smul, map_smul, smul_smul]
              congr 1
              simp only [hε']
              linear_combination ((cofR m d d₁ : GaussianInt) * ε (d / d₁) d₁ *
                (ℓ d₁ : GaussianInt)) * hsq1 _ hdiv.2
      have hmain : torG.mkQ ((bigM m d : GaussianInt) • Pseq ℓ ε' tyzZ d) =
          (cofR m d 1 : GaussianInt) • torG.mkQ (Q' d) := by
        rw [Pseq_eq, map_smul, map_sub, map_sum, smul_sub, Finset.smul_sum, ← map_smul, hL,
          Finset.sum_congr rfl hstep, add_sub_cancel_right]
        simp only [hQ']
        rw [map_smul, map_smul, smul_smul]
        congr 1
        push_cast; ring
      have hM : bigM m d = m d * cofR m d 1 := by
        rw [bigM_eq (Nat.one_mem_divisors.mpr hd0), Nat.div_one]
      rw [hM, Nat.cast_mul, mul_comm, mul_smul, map_smul] at hmain
      have h0 : (cofR m d 1 : GaussianInt) • (torG.mkQ ((m d : GaussianInt) • Pseq ℓ ε' tyzZ d) -
          torG.mkQ (Q' d)) = 0 := by rw [smul_sub, hmain, sub_self]
      exact sub_eq_zero.mp (quot_cancel (cofR_pos hm d 1) h0)
  intro n hn hsq
  refine ⟨ε', ⟨fun d₀ d₁ _ h5 h3 => ?_, fun d₀ d₁ _ hcl => ?_⟩, fun h0 => ?_⟩
  · rcases hε53 d₀ d₁ h5 h3 with h | h <;>
      rcases hε1 d₀ 1 (Or.inl ⟨h5, rfl⟩) with h' | h' <;> simp [hε', h, h']
  · have hd₀ : d₀ % 8 = 5 ∨ d₀ % 8 = 7 := by omega
    rcases hε1 d₀ d₁ hcl with h | h <;>
      rcases (show ε d₀ 1 = 1 ∨ ε d₀ 1 = -1 from by
        apply hε1
        rcases hd₀ with h5 | h7
        · exact Or.inl ⟨h5, rfl⟩
        · exact Or.inr (Or.inl ⟨h7, rfl⟩)) with h' | h' <;> simp [hε', h, h']
  · have hk := key n hsq (Or.inl hn)
    have hQn : torG.mkQ (Q' n) = 0 := by
      simp only [hQ']
      rw [map_smul, mkQ_eq_zero_iff.mpr (hQ0 n hsq hn h0), smul_zero]
    rw [hQn, map_smul] at hk
    exact mkQ_eq_zero_iff.mp (quot_cancel (hm n).ne' hk)

open ZInQ.Contrib.TYZDecomp in
/-- **`Thm35First ℓ tyzZ` for every `IsTYZLcal ℓ`, from the pinned TYZ Theorem 3.3.** -/
theorem thm35First_of_lcal_thm33 (h33 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → TYZThm33Pinned ℓ) :
    ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ :=
  fun ℓ hℓ => thm35First_of_thm33 ℓ hℓ.1 (h33 ℓ hℓ)

end Glue

end ZInQ.Contrib.TYZGenus.TYZ35

#print axioms ZInQ.Contrib.TYZGenus.TYZ35.thm35First_of_thm33
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.thm35First_of_lcal_thm33
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.level_identity
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.prod_sgn_chi_eq_one
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.sum_Pchi
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.exists_liftFamily
#print axioms ZInQ.Contrib.TYZGenus.TYZ35.sum_Pchi_divisors
