import ZInQKernel.Contrib.CloudB3RC53.Prints
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Elliot
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Arith

/-!
# GenusOdd: Proposition `ex:sec7-genus-lower`, identity (3.4) (tex L2403–2439)

**Known issue K3**: (3.4) needs Cai–Shu–Tian
Theorem 1.1 in a form whose conductor factor is `c √|disc K|` with no other dependence on `c` or
`K`, with the unaveraged sum and the height relative to `K`. That form is exactly the printed leaf
`Prints.cst` (`CST.CSTThm11Split`), stated in `Prints/CST.lean` (Theorem 1.1 read,
arXiv:1408.1733v2, p. 2); it is used here as stated and is **not** reconstructed or re-proved.
No Gross–Zagier argument of our own enters.

## The objects (tex L2403–2416)

For a positive squarefree `h` in the prepared filter containing one (`Prepared`), a fixed negative
genus partner `h_*` (`GenusPartner`) and a rough companion `k'` (`Companion`):

* the genus point `P_h^gen`: the unaveraged conductor-one genus sum over `ℚ(√(h h_*))`, weighted by
  `χ_{h_*}(N𝔞)` ((O.1), tex L8213–8217): `heegnerSum` of a `HeegnerDatum` with `D = h h_*`,
  `c = 1`, `d₁ = h_*`;
* the ring-class point `P_{h,k'}^rc`: the unaveraged conductor-`|h|` sum over `ℚ(√k')` weighted by
  `χ_h`: `heegnerSum` of a `HeegnerDatum` with `D = k'`, `c = |h|`, `d₁ = h`;
* `j_gen(h)`, `j_rc(h, k')`: their index valuations in their native lattices (`twoDivIndex` in
  `eigenLattice`).

A `HeegnerDatum` carries the field, the character, a Heegner form, an embedding `ι : H_c → ℂ` and a
point `y ∈ E(H_c)` with `ι(y) = φ(τ)`: the complex-analytic model of `Prints/CST.lean` (the
algebraic Heegner point on `X₀(N)` is not available). `jgenOf`, `jrcOf` read the index off a
selection of data (one datum per `h`, resp. `(h, k')`).

## The proof (tex L2427–2439)

PRINT `Prints.cst` twice (common constant `C`: "the parametrization is the same"), GLUE
`Prints.kolyvagin` (a cited statement) and PRINT `Prints.bcdt` (ranks of `E^{(h)}`, `E^{(h_*)}`,
`E^{(hk')}`), the GLUE of `Glue.lean`, and Elliot's index-at-most-two comparison (PROVED,
`Elliot.lean`).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

section Data

variable (E : WeierstrassCurve ℚ)
  (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
  (Lat : PeriodPair) (κ : ℂ)

-- `open Classical` exactly as in `CST.CSTThm11Split`, so that `hy` is CST's hypothesis verbatim.
open Classical in
/-- **A Heegner datum** for discriminant `D`, conductor `c` and character `χ = χ_{d₁} ∘ N`: an
imaginary quadratic field `K` of discriminant `D`, a primitive quadratic ring class character of
conductor `c` equal to `χ_{d₁} ∘ N`, a Heegner form `[A, B, C]` of level `N` and discriminant
`D c²`, an embedding `ι : H_c → ℂ` and a point `y ∈ E(H_c)` with `ι(y) = φ(τ_{[A,B,C]})` (the
analytic model of the Heegner point, `Prints/CST.lean`). -/
structure HeegnerDatum (D : ℤ) (c : ℕ) (d₁ : ℤ) where
  K : Type
  [field : Field K]
  [nf : NumberField K]
  [nz : NeZero c]
  finrank_two : Module.finrank ℚ K = 2
  totallyComplex : IsTotallyComplex K
  disc : discr K = D
  χ : Pic (conductorOrder K c) →* ℂˣ
  quad : IsQuadRingClassChar K c d₁ χ
  prim : IsPrimitiveRingClassChar K c χ
  A : ℤ
  B : ℤ
  C : ℤ
  form : IsHeegnerForm (newformLevel E) (D * c ^ 2) A B C
  ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ
  y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point
  hy : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
    phiAn E f Lat κ (cmPoint A B (D * c ^ 2))

variable {E f Lat κ}

/-- The index valuation of `P_χ` in its native lattice (`j` of tex L2416). -/
def nativeIndex (E : WeierstrassCurve ℚ) {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]
    (χ : Pic (conductorOrder K c) →* ℂˣ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point) : ℕ∞ :=
  letI := Classical.decEq (ringClassField (conductorOrder K c))
  twoDivIndex (eigenLattice E χ) (heegnerSum E χ y)

/-- The index valuation of the datum's unaveraged Heegner sum in its native lattice. -/
def HeegnerDatum.index {D : ℤ} {c : ℕ} {d₁ : ℤ} (dat : HeegnerDatum E f Lat κ D c d₁) : ℕ∞ :=
  letI := dat.field; letI := dat.nf; letI := dat.nz
  nativeIndex E dat.χ dat.y

variable (E f Lat κ)

/-- **`j_gen(h)`** (tex L2411–2416) read off a selection of genus data (`D = h h_*`, `c = 1`,
`χ = χ_{h_*} ∘ N`); `0` where no datum is selected. -/
def jgenOf (hstar : ℤ) (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (h : ℤ) : ℤ :=
  match selG h with
  | some dat => (dat.index.toNat : ℤ)
  | none => 0

/-- **`j_rc(h, k')`** (tex L2411–2416) read off a selection of ring-class data (`D = k'`,
`c = |h|`, `χ = χ_h ∘ N`); `0` where no datum is selected. -/
def jrcOf (selR : (h k : ℤ) → Option (HeegnerDatum E f Lat κ k h.natAbs h)) (h k : ℤ) : ℤ :=
  match selR h k with
  | some dat => (dat.index.toNat : ℤ)
  | none => 0

end Data

/-! ### The parameters of (3.4) -/

/-- **The prepared positive filter containing one** (tex L2404–2410, L2343–2346): `h` positive,
squarefree, a unit square at every prime of `2N` (the squareclasses of one), prime to `h_*` (the
fixed support includes `h_*`, tex L2407–2408). -/
def Prepared (E : WeierstrassCurve ℚ) (hstar h : ℤ) : Prop :=
  0 < h ∧ Squarefree h ∧ (∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel E → SquareAt p h) ∧
    IsCoprime h hstar

/-- **The negative genus partner** (tex L2403–2406): `h_*` a negative odd fundamental
discriminant (`≡ 1 mod 4`, squarefree) with `|h_*| > 4`, in the squareclasses of one at `2N`, and
`L(E^{(h_*)}, 1) ≠ 0`. -/
def GenusPartner (E : WeierstrassCurve ℚ) (hstar : ℤ) : Prop :=
  hstar < 0 ∧ hstar % 4 = 1 ∧ Squarefree hstar ∧ 4 < |hstar| ∧
    (∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel E → SquareAt p hstar) ∧
    AnalyticRank (qtwist E hstar) 0

/-- **The rough companion relation** (Proposition `ex:sec7-rough-companion`, tex L2349–2353, with
the primes of `h_*` in the avoidance set, tex L2408–2409): `k'` a negative odd fundamental
discriminant (`≡ 1 mod 4`, squarefree), a unit square at every prime dividing `2Nh` (so it avoids
the extra-unit fields: `k' ≡ 1 mod 8`), prime to `h_*`, with `L_*(hk') ≠ 0`. -/
def Companion (E : WeierstrassCurve ℚ) (Lat : PeriodPair) (hstar h k' : ℤ) : Prop :=
  k' < 0 ∧ k' % 4 = 1 ∧ Squarefree k' ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * newformLevel E * h → SquareAt p k') ∧
    IsCoprime k' hstar ∧ Lstar E Lat (h * k') ≠ 0

/-! ### One application of Cai–Shu–Tian -/

section Core

open Classical in
/-- The conclusion of `CST.CSTThm11Split` for fixed `(E, f, Lat, κ)` and constant `C` (verbatim). -/
def CSTFormula (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    discr K ≠ -3 → discr K ≠ -4 →
    (∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p) →
    ∀ (c : ℕ) [NeZero c], Nat.Coprime c (newformLevel E) →
    ∀ χ : Pic (conductorOrder K c) →* ℂˣ, IsPrimitiveRingClassChar K c χ →
    ∀ A B C' : ℤ, IsHeegnerForm (newformLevel E) (discr K * c ^ 2) A B C' →
    ∀ ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ,
    ∀ y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point,
      WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
        phiAn E f Lat κ (cmPoint A B (discr K * c ^ 2)) →
    ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = LSeries (twistedLFunction E (chiAt (conductorOrder K c) χ)) s) →
      deriv F 1 = ((C / ((c : ℝ) * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) * heightK E K c χ y

theorem cst_formula (P : Prints) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat) (κ : ℂ)
    (hκ : IsParamScale (newformLevel E) f Lat κ) : ∃ C : ℝ, 0 < C ∧ CSTFormula E f Lat κ C :=
  P.cst E f hf Lat hLat hNC κ hκ

theorem splits_of_squareAt (G : Glue34) {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {N : ℕ} (h : ∀ p : ℕ, p.Prime → p ∣ N → SquareAt p (discr K)) :
    ∀ p : ℕ, p.Prime → p ∣ N → SplitsIn K p :=
  fun p hp hpN => G.split K hK p hp (h p hp hpN)

theorem coprime_of_squareAt {N : ℕ} {d : ℤ} (h : ∀ p : ℕ, p.Prime → p ∣ N → SquareAt p d) :
    Nat.Coprime d.natAbs N := by
  refine Nat.coprime_of_dvd fun p hp hpd hpN => (h p hp hpN).1 ?_
  exact Int.natCast_dvd.mpr hpd

open Classical in
/-- **One application of Cai–Shu–Tian, with Elliot's comparison** (PROVED from `Prints.cst` and the
GLUE). For a field `K` of discriminant `D`, `χ = χ_{d₁} ∘ N` on `Pic(O_c)`, `d₁ d₂ = D c²`, a
Heegner point `y` and entire continuations `F₁, F₂` of `L(E^{(d₁)}, s)`, `L(E^{(d₂)}, s)`: if
`E^{(d_T)}(ℚ)` is torsion for the one of `d₁, d₂` called `d_T`, there is `Q` on the rational line
`E^{(d_R)}(ℚ)` (the other one) with `(F₁F₂)'(1) = C/(c√|D|) · ĥ(Q)/2` and
`j(P_χ) ≤ j(Q) ≤ j(P_χ) + 1`. -/
theorem datum_facts_core (G : Glue34) {E : WeierstrassCurve ℚ} [E.IsElliptic] (h₁ : E.a₁ = 0)
    (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {C : ℝ} (hC : CSTFormula E f Lat κ C)
    {D : ℤ} {c : ℕ} {d₁ d₂ dR dT : ℤ} (K : Type) [Field K] [NumberField K] [NeZero c]
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (hdisc : discr K = D)
    (χ : Pic (conductorOrder K c) →* ℂˣ) (hquad : IsQuadRingClassChar K c d₁ χ)
    (hprim : IsPrimitiveRingClassChar K c χ) (A B C' : ℤ)
    (hform : IsHeegnerForm (newformLevel E) (D * c ^ 2) A B C')
    (ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (hy : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
        phiAn E f Lat κ (cmPoint A B (D * c ^ 2)))
    (hprod : d₁ * d₂ = D * c ^ 2) (hd₁ : d₁ % 4 = 1) (hsq : Squarefree d₁) (hcd : (c : ℤ) ∣ d₁)
    (hcD : Nat.Coprime c D.natAbs) (hDodd : Odd D) (hD3 : D ≠ -3) (hD4 : D ≠ -4)
    (hDN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p D)
    (hcN : Nat.Coprime c (newformLevel E)) (hdN : Nat.Coprime (d₁ * d₂).natAbs (newformLevel E))
    (hRT : (dR = d₁ ∧ dT = d₂) ∨ (dR = d₂ ∧ dT = d₁))
    (htorT : ∀ P : (qtwist E dT).toAffine.Point, IsOfFinAddOrder P)
    {F₁ F₂ : ℂ → ℂ} (hF₁ : IsLContinuation (qtwist E d₁) F₁)
    (hF₂ : IsLContinuation (qtwist E d₂) F₂) :
    ∃ Q : (qtwist E dR).toAffine.Point,
      deriv (fun s => F₁ s * F₂ s) 1 =
        ((C / ((c : ℝ) * Real.sqrt |(D : ℝ)|) : ℝ) : ℂ) * ((Q.canonicalHeight / 2 : ℝ) : ℂ) ∧
      nativeIndex E χ y ≤ twoDivIndex ⊤ Q ∧ twoDivIndex ⊤ Q ≤ nativeIndex E χ y + 1 := by
  subst hdisc
  let _ : DecidableEq (ringClassField (conductorOrder K c)) :=
    Classical.decEq (ringClassField (conductorOrder K c))
  -- genus theory: `√d₁, √d₂ ∈ H_c` and complex conjugation
  obtain ⟨hgal, s₁, s₂, hs₁, hs₂, hσ, ρ, hρ⟩ := G.genus K hK2 hTC hDodd c d₁ d₂ hprod hd₁ hsq
    hcd hcD χ hquad
  have hd₁0 : d₁ ≠ 0 := by rintro rfl; norm_num at hd₁
  have hd₂0 : d₂ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hprod
    have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne c)
    have hD0 : discr K ≠ 0 := by rintro h; rw [h] at hDodd; norm_num at hDodd
    exact (mul_ne_zero hD0 (pow_ne_zero 2 hc0)) hprod.symm
  have _ := hgal
  have hsplit := splits_of_squareAt G hK2 hDN
  -- Cai–Shu–Tian at this datum
  have hCST := hC K hK2 hTC hD3 hD4 hsplit c hcN χ hprim A B C' hform ι y hy
    (fun s => F₁ s * F₂ s) (hF₁.1.mul hF₂.1) (fun s hs => by
      rw [hF₁.2 s hs, hF₂.2 s hs]
      exact (G.artin E K hK2 hTC hDodd hsplit c d₁ d₂ hprod hd₁ hsq hcd hcD hdN χ hquad s hs).symm)
  rw [heightK_eq_canonicalHeight E hquad.1 y] at hCST
  have hP : heegnerSum E χ y ∈ eigenLattice E χ := heegnerSum_mem_eigenLattice E hquad.1 y
  have hn : 0 < Module.finrank K (ringClassField (conductorOrder K c)) := Module.finrank_pos
  have htower : Module.finrank ℚ (ringClassField (conductorOrder K c)) =
      2 * Module.finrank K (ringClassField (conductorOrder K c)) := by
    rw [← Module.finrank_mul_finrank ℚ K, hK2]
  have finish : ∀ (dR' dT' : ℤ) (sR sT : ringClassField (conductorOrder K c)),
      sR ^ 2 = (dR' : ringClassField (conductorOrder K c)) →
      sT ^ 2 = (dT' : ringClassField (conductorOrder K c)) → dR' ≠ 0 → dT' ≠ 0 →
      (∀ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
        σ sR = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * sR ∧
        σ sT = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * sT) →
      ((ρ sR = sR ∧ ρ sT = -sT) ∨ (ρ sR = -sR ∧ ρ sT = sT)) →
      (∀ P : (qtwist E dT').toAffine.Point, IsOfFinAddOrder P) →
      ∃ Q : (qtwist E dR').toAffine.Point,
        deriv (fun s => F₁ s * F₂ s) 1 =
          ((C / ((c : ℝ) * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) *
            ((Q.canonicalHeight / 2 : ℝ) : ℂ) ∧
        nativeIndex E χ y ≤ twoDivIndex ⊤ Q ∧ twoDivIndex ⊤ Q ≤ nativeIndex E χ y + 1 := by
    intro dR' dT' sR sT hsR hsT hdR hdT hσ' hρ' htor'
    have hcast : ∀ d : ℤ, ((d : ringClassField (conductorOrder K c))) =
        algebraMap ℚ (ringClassField (conductorOrder K c)) (d : ℚ) := fun d => by
      rw [map_intCast]
    have hne : ∀ {d : ℤ} {s : ringClassField (conductorOrder K c)},
        s ^ 2 = (d : ringClassField (conductorOrder K c)) → d ≠ 0 → s ≠ 0 := by
      intro d s hs hd h0
      rw [h0] at hs
      have : ((d : ringClassField (conductorOrder K c))) = 0 := by rw [← hs]; ring
      exact hd (by exact_mod_cast this)
    have hsR0 := hne hsR hdR
    have hsT0 := hne hsT hdT
    have hsRd : sR ^ 2 = algebraMap ℚ _ (dR' : ℚ) := by rw [hsR, hcast]
    have hsTd : sT ^ 2 = algebraMap ℚ _ (dT' : ℚ) := by rw [hsT, hcast]
    have helliot := two_nsmul_mem_twist_add_torsion E G.descent h₁ h₃ hK2 hsR0 hsRd hsT0 hsTd
      hσ' ρ hρ' htor'
    obtain ⟨Q, hQ⟩ := helliot _ hP
    refine ⟨Q, ?_, ?_⟩
    · have hsqH : ∀ (m : ℕ) (x : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point),
          ((m • x).canonicalHeight) = (m : ℝ) ^ 2 * x.canonicalHeight :=
        fun m x => WeierstrassCurve.Affine.Point.canonicalHeight_nsmul m x
      have h2P := height_add_torsion hsqH
        (twistEmb E dR' sR (twistVC_smul E h₁ h₃ hsR0 hsRd) Q) _ hQ
      rw [add_sub_cancel, hsqH, G.height E h₁ h₃ (dR' : ℚ) _ sR hsR0 hsRd Q, htower] at h2P
      have hn' : (Module.finrank K (ringClassField (conductorOrder K c)) : ℝ) ≠ 0 := by
        exact_mod_cast hn.ne'
      push_cast at h2P
      have key : ((Module.finrank K (ringClassField (conductorOrder K c)) : ℝ))⁻¹ *
          (heegnerSum E χ y).canonicalHeight = Q.canonicalHeight / 2 := by
        rw [show (heegnerSum E χ y).canonicalHeight = 2 * (Module.finrank K
            (ringClassField (conductorOrder K c)) : ℝ) * Q.canonicalHeight / 4 by linarith]
        field_simp
        ring
      rw [hCST, key]
    · have hψM : ∀ r, twistEmb E dR' sR (twistVC_smul E h₁ h₃ hsR0 hsRd) r ∈ eigenLattice E χ := by
        intro r σ
        have hsRne : sR ≠ -sR := fun h => hsR0 (by
          have : (2 : ringClassField (conductorOrder K c)) * sR = 0 := by linear_combination h
          simpa using this)
        have hcs : chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) = 1 ∨
            chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) = -1 := by
          unfold chiSign; split_ifs <;> simp
        have hs := (hσ' σ).1
        show galPt E σ _ = _
        rcases hcs with h | h
        · rw [h] at hs
          have hσs : σ sR = sR := by rw [hs]; simp
          rw [galPt, map_twistEmb_eq_ite E h₁ h₃ (dR' : ℚ) (σ.toAlgHom.restrictScalars ℚ) hsR0
            hsRd (Or.inl hσs) r, if_pos (by exact hσs), h, one_smul]
        · rw [h] at hs
          have hσs : σ sR = -sR := by rw [hs]; simp
          have hσs' : ¬ σ sR = sR := fun h' => hsRne (h'.symm.trans hσs)
          rw [galPt, map_twistEmb_eq_ite E h₁ h₃ (dR' : ℚ) (σ.toAlgHom.restrictScalars ℚ) hsR0
            hsRd (Or.inr hσs) r, if_neg (by exact hσs'), h, neg_smul, one_smul]
      have := twoDivIndex_transfer _ (twistEmb_injective E (dR' : ℚ) sR _) (eigenLattice E χ) hψM
        helliot hP hQ
      exact this
  rcases hRT with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · subst e1 e2
    exact finish _ _ s₁ s₂ hs₁ hs₂ hd₁0 hd₂0 hσ hρ htorT
  · subst e1 e2
    refine finish _ _ s₂ s₁ hs₂ hs₁ hd₂0 hd₁0 (fun σ => ⟨(hσ σ).2, (hσ σ).1⟩) ?_ htorT
    rcases hρ with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr ⟨b, a⟩
    · exact Or.inl ⟨b, a⟩

theorem torsion_of_rank_zero {M : Type*} [AddCommGroup M] (h : Module.rank ℤ M = 0) (x : M) :
    IsOfFinAddOrder x := by
  obtain ⟨a, ha, hax⟩ := rank_eq_zero_iff.mp h x
  exact isOfFinAddOrder_of_zsmul ha (by rw [hax]; simp)

theorem LstarQ_eq {E : WeierstrassCurve ℚ} {Lat : PeriodPair} {d : ℤ} {q : ℚ}
    (h : (q : ℂ) = Lstar E Lat d) : LstarQ E Lat d = q := by
  have hex : ∃ q : ℚ, (q : ℂ) = Lstar E Lat d := ⟨q, h⟩
  unfold LstarQ
  rw [dif_pos hex]
  exact_mod_cast (Classical.choose_spec hex).trans h.symm

/-- **(3.4) at one `(h, k')` with selected data** (PROVED from `Prints` and `Glue34`). -/
theorem core34 (P : Prints) (G : Glue34) {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel E) f Lat κ) {hstar : ℤ} (hgp : GenusPartner E hstar)
    (hMD : ∃ q : ℚ, (q : ℂ) = Lstar E Lat hstar) {h k' : ℤ} (hp : Prepared E hstar h)
    (hz : AnalyticRank (qtwist E h) 1) (hk : Companion E Lat hstar h k')
    (datG : HeegnerDatum E f Lat κ (h * hstar) 1 hstar)
    (datR : HeegnerDatum E f Lat κ k' h.natAbs h) :
    datG.index ≠ ⊤ ∧ datR.index ≠ ⊤ ∧ ∃ ε : ℤ, |ε| ≤ 2 ∧
      2 * (datR.index.toNat : ℤ) - 2 * (datG.index.toNat : ℤ) =
        padicValRat 2 (LstarQ E Lat (h * k')) - padicValRat 2 (LstarQ E Lat hstar) + ε := by
  obtain ⟨C, hC0, hC⟩ := cst_formula P E f hf Lat hLat hNC κ hκ
  obtain ⟨h0, hsqh, hsqp, hcop⟩ := hp
  obtain ⟨hs0, hs4, hssq, hs5, hsp, har0⟩ := hgp
  obtain ⟨k0, k4, ksq, kp, kcop, hL⟩ := hk
  have hN2 : ∀ p : ℕ, p ∣ newformLevel E → p ∣ 2 * newformLevel E :=
    fun p hp => dvd_mul_of_dvd_right hp 2
  have h2h : SquareAt 2 h := hsqp 2 Nat.prime_two (dvd_mul_right 2 _)
  have h2k : SquareAt 2 k' := kp 2 Nat.prime_two (by
    push_cast; exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) h)
  have h2s : SquareAt 2 hstar := hsp 2 Nat.prime_two (dvd_mul_right 2 _)
  have h8 : h % 8 = 1 := h2h.2.1 rfl
  have s8 : hstar % 8 = 1 := h2s.2.1 rfl
  have k8 : k' % 8 = 1 := h2k.2.1 rfl
  have hDg4 : 4 < |h * hstar| := by rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg hstar]
  -- ranks
  have hh0 : (h : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
  have hs0' : (hstar : ℚ) ≠ 0 := by exact_mod_cast hs0.ne
  have hk0' : ((h * k' : ℤ) : ℚ) ≠ 0 := by
    have : h * k' ≠ 0 := mul_ne_zero h0.ne' k0.ne
    exact_mod_cast this
  have hEh : (qtwist E h).IsElliptic := qtwist_isElliptic E hh0
  have hrank1 : Module.rank ℤ (qtwist E h).toAffine.Point = 1 := by
    have := (P.kolyvagin (qtwist E h) hEh (P.bcdt _ hEh) 1 le_rfl hz).1
    exact_mod_cast this
  have htorS : ∀ Q : (qtwist E hstar).toAffine.Point, IsOfFinAddOrder Q := by
    have hE := qtwist_isElliptic E hs0'
    have := (P.kolyvagin (qtwist E hstar) hE (P.bcdt _ hE) 0 (by norm_num) har0).1
    exact torsion_of_rank_zero (by exact_mod_cast this)
  -- `L(E^{(hk')}, 1) ≠ 0` and `Ω⁻ ≠ 0`, from `L_*(hk') ≠ 0`
  have hΩ : (omegaMinus Lat : ℂ) ≠ 0 := by
    intro h0'; apply hL; unfold Lstar; rw [h0', div_zero]
  have hLk : Lval (qtwist E (h * k' : ℤ)) ≠ 0 := by
    intro h0'; apply hL; unfold Lstar; rw [h0', mul_zero, zero_div]
  have hark := analyticRank_zero_of_Lval_ne_zero hLk
  have htorK : ∀ Q : (qtwist E (h * k' : ℤ)).toAffine.Point, IsOfFinAddOrder Q := by
    have hE := qtwist_isElliptic E hk0'
    have := (P.kolyvagin (qtwist E (h * k' : ℤ)) hE (P.bcdt _ hE) 0 (by norm_num) hark).1
    exact torsion_of_rank_zero (by exact_mod_cast this)
  -- continuations
  obtain ⟨Fh, hFh, hFh1, hFh'⟩ := analyticRank_one hz
  obtain ⟨Fs, hFs, hFs1⟩ := analyticRank_zero_iff.mp har0
  obtain ⟨Fk, hFk, hFk1⟩ := analyticRank_zero_iff.mp hark
  -- square classes
  have hsqDg : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p (h * hstar) := fun p hp hpN =>
    (hsqp p hp (hN2 p hpN)).mul (hsp p hp (hN2 p hpN)) hp
  have hsqDr : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p k' := fun p hp hpN =>
    kp p hp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by exact_mod_cast hpN) 2) h)
  have hsqhN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p h := fun p hp hpN => hsqp p hp (hN2 p hpN)
  have hsqsN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p hstar := fun p hp hpN => hsp p hp (hN2 p hpN)
  have habs : (h.natAbs : ℤ) = h := by rw [Int.natCast_natAbs, abs_of_pos h0]
  -- the genus datum: `D = h h_*`, `c = 1`, `d₁ = h_*`, `d₂ = h`
  obtain ⟨Qg, hderG, hjG1, hjG2⟩ := by
    letI := datG.field; letI := datG.nf; letI := datG.nz
    exact datum_facts_core G h₁ h₃ hC datG.K datG.finrank_two datG.totallyComplex datG.disc
      datG.χ datG.quad datG.prim datG.A datG.B datG.C datG.form datG.ι datG.y datG.hy
      (d₂ := h) (dR := h) (dT := hstar) (by push_cast; ring) hs4 hssq (by simp)
      (Nat.coprime_one_left _) (Int.odd_iff.mpr (by
        rw [Int.mul_emod, show h % 2 = 1 by omega, show hstar % 2 = 1 by omega]; norm_num))
      (by intro hD; rw [hD] at hDg4; norm_num at hDg4)
      (by intro hD; rw [hD] at hDg4; norm_num at hDg4)
      hsqDg (Nat.coprime_one_left _)
      (coprime_of_squareAt fun p hp hpN => (hsqsN p hp hpN).mul (hsqhN p hp hpN) hp)
      (Or.inr ⟨rfl, rfl⟩) htorS hFs hFh
  -- the ring-class datum: `D = k'`, `c = |h|`, `d₁ = h`, `d₂ = h k'`
  have hcopHK : Nat.Coprime h.natAbs k'.natAbs := by
    refine Nat.coprime_of_dvd fun p hp hph hpk => (kp p hp ?_).1 (Int.natCast_dvd.mpr hpk)
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hph) _
  obtain ⟨Qr, hderR, hjR1, hjR2⟩ := by
    letI := datR.field; letI := datR.nf; letI := datR.nz
    exact datum_facts_core G h₁ h₃ hC datR.K datR.finrank_two datR.totallyComplex datR.disc
      datR.χ datR.quad datR.prim datR.A datR.B datR.C datR.form datR.ι datR.y datR.hy
      (d₂ := h * k') (dR := h) (dT := h * k') (by rw [habs]; ring) (h2h.mod_four) hsqh
      (by rw [habs]) hcopHK (h2k.odd) (by intro hD; rw [hD] at k8; norm_num at k8)
      (by intro hD; rw [hD] at k8; norm_num at k8) hsqDr
      (coprime_of_squareAt hsqhN)
      (coprime_of_squareAt fun p hp hpN => (hsqhN p hp hpN).mul
        ((hsqhN p hp hpN).mul (hsqDr p hp hpN) hp) hp)
      (Or.inl ⟨rfl, rfl⟩) htorK hFh hFk
  -- the two derivatives
  have dG : deriv (fun s => Fs s * Fh s) 1 = Fs 1 * deriv Fh 1 := by
    rw [show (fun s => Fs s * Fh s) = Fs * Fh from rfl, deriv_mul (hFs.1 1) (hFh.1 1), hFh1]; ring
  have dR : deriv (fun s => Fh s * Fk s) 1 = deriv Fh 1 * Fk 1 := by
    rw [show (fun s => Fh s * Fk s) = Fh * Fk from rfl, deriv_mul (hFh.1 1) (hFk.1 1), hFh1]; ring
  rw [dG] at hderG
  rw [dR] at hderR
  -- the real square roots
  have hhR : (0 : ℝ) < h := by exact_mod_cast h0
  set a := Real.sqrt (h : ℝ) with ha
  set b := Real.sqrt |(k' : ℝ)| with hb
  set e := Real.sqrt |(hstar : ℝ)| with he
  have ha0 : 0 < a := Real.sqrt_pos.mpr hhR
  have hb0 : 0 < b := Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast k0.ne))
  have he0 : 0 < e := Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hs0.ne))
  have ha2 : a ^ 2 = h := Real.sq_sqrt hhR.le
  have hsg : Real.sqrt |((h * hstar : ℤ) : ℝ)| = a * e := by
    push_cast; rw [abs_mul, abs_of_pos hhR, Real.sqrt_mul hhR.le]
  have hsk : Real.sqrt |((h * k' : ℤ) : ℝ)| = a * b := by
    push_cast; rw [abs_mul, abs_of_pos hhR, Real.sqrt_mul hhR.le]
  have hnat : ((h.natAbs : ℕ) : ℝ) = h := by
    rw [Nat.cast_natAbs, abs_of_pos h0]
  rw [hsg] at hderG
  rw [hnat] at hderR
  -- heights are nonzero
  have hDh := hFh'
  have hXs := hFs1
  have hYk := hFk1
  have hg0 : Qg.canonicalHeight ≠ 0 := by
    intro h0'
    rw [h0', zero_div, Complex.ofReal_zero, mul_zero] at hderG
    exact mul_ne_zero hXs hDh hderG
  have hr0 : Qr.canonicalHeight ≠ 0 := by
    intro h0'
    rw [h0', zero_div, Complex.ofReal_zero, mul_zero] at hderR
    exact mul_ne_zero hDh hYk hderR
  -- the rank-one comparison on `E^{(h)}(ℚ)`
  have hsqZ : ∀ (n : ℤ) (x : (qtwist E h).toAffine.Point),
      (n • x).canonicalHeight = (n : ℝ) ^ 2 * x.canonicalHeight :=
    fun n x => WeierstrassCurve.Affine.Point.canonicalHeight_zsmul n x
  have hsqN : ∀ (n : ℕ) (x : (qtwist E h).toAffine.Point),
      (n • x).canonicalHeight = (n : ℝ) ^ 2 * x.canonicalHeight :=
    fun n x => WeierstrassCurve.Affine.Point.canonicalHeight_nsmul n x
  have hfinB : ∀ B : ℝ, {x : (qtwist E h).toAffine.Point | x.canonicalHeight ≤ B}.Finite :=
    fun B => Northcott.finite_le (h := WeierstrassCurve.Affine.Point.canonicalHeight) B
  have hpos : ∀ Q : (qtwist E h).toAffine.Point, Q.canonicalHeight ≠ 0 →
      0 < Q.canonicalHeight := fun Q hQ =>
    lt_of_le_of_ne (WeierstrassCurve.Affine.Point.canonicalHeight_nonneg Q) (Ne.symm hQ)
  have hnt : ∀ Q : (qtwist E h).toAffine.Point, Q.canonicalHeight ≠ 0 → ¬ IsOfFinAddOrder Q :=
    fun Q hQ ht => hQ (WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_of_isOfFinAddOrder ht)
  have hJg := twoDivIndex_ne_top hsqN hfinB (hpos Qg hg0)
  have hJr := twoDivIndex_ne_top hsqN hfinB (hpos Qr hr0)
  obtain ⟨q, hq0, hqeq, hqv⟩ := rank_one_ratio hsqZ (exists_dep_of_rank_le_one (le_of_eq hrank1))
    (hnt Qr hr0) (hnt Qg hg0) hJr hJg
  -- `L_*(hk') = q² L_*(h_*)`
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hec : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
  have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have ha2c : (a : ℂ) ^ 2 = h := by exact_mod_cast ha2
  have E1 := hderG
  have E2 := hderR
  rw [hqeq] at E2
  push_cast at E1 E2
  have key : ((a : ℂ) * b * Fk 1 - (q : ℂ) ^ 2 * (e * Fs 1)) * deriv Fh 1 = 0 := by
    calc ((a : ℂ) * b * Fk 1 - (q : ℂ) ^ 2 * (e * Fs 1)) * deriv Fh 1
        = (a : ℂ) * b * (deriv Fh 1 * Fk 1) - (q : ℂ) ^ 2 * e * (Fs 1 * deriv Fh 1) := by ring
      _ = (a : ℂ) * b * ((C : ℂ) / ((h : ℂ) * b) * ((q : ℂ) ^ 2 * Qg.canonicalHeight / 2)) -
          (q : ℂ) ^ 2 * e * ((C : ℂ) / (1 * ((a : ℂ) * e)) * (Qg.canonicalHeight / 2)) := by
        rw [E1, E2]
      _ = (C : ℂ) * (q : ℂ) ^ 2 * Qg.canonicalHeight * ((a : ℂ) ^ 2 - h) / (2 * h * a) := by
        field_simp
      _ = 0 := by rw [ha2c, sub_self, mul_zero, zero_div]
  have key' : (a : ℂ) * b * Fk 1 = (q : ℂ) ^ 2 * (e * Fs 1) :=
    sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hDh)
  have hLs : Lstar E Lat (h * k') = (q : ℂ) ^ 2 * Lstar E Lat hstar := by
    unfold Lstar
    rw [Lval_eq hFk, Lval_eq hFs, hsk, ← he]
    push_cast
    rw [key']
    ring
  obtain ⟨qs, hqs⟩ := hMD
  have hLsq : ((q ^ 2 * qs : ℚ) : ℂ) = Lstar E Lat (h * k') := by
    rw [hLs, ← hqs]; push_cast; ring
  have hqs0 : qs ≠ 0 := by
    intro h0'
    rw [h0', Rat.cast_zero] at hqs
    unfold Lstar at hqs
    rw [Lval_eq hFs, ← he] at hqs
    exact (div_ne_zero (mul_ne_zero hec hXs) hΩ) hqs.symm
  rw [LstarQ_eq hLsq, LstarQ_eq hqs]
  have := Fact.mk Nat.prime_two
  rw [padicValRat.mul (pow_ne_zero 2 hq0) hqs0, padicValRat.pow q]
  -- the index valuations
  have hjG1' : datG.index ≤ twoDivIndex ⊤ Qg := hjG1
  have hjG2' : twoDivIndex ⊤ Qg ≤ datG.index + 1 := hjG2
  have hjR1' : datR.index ≤ twoDivIndex ⊤ Qr := hjR1
  have hjR2' : twoDivIndex ⊤ Qr ≤ datR.index + 1 := hjR2
  obtain ⟨JG, hJG⟩ := ENat.ne_top_iff_exists.mp hJg
  obtain ⟨JR, hJR⟩ := ENat.ne_top_iff_exists.mp hJr
  rw [← hJG] at hjG1' hjG2' hqv
  rw [← hJR] at hjR1' hjR2' hqv
  have hgT : datG.index ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top JG) hjG1'
  have hrT : datR.index ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top JR) hjR1'
  obtain ⟨jg, hjg⟩ := ENat.ne_top_iff_exists.mp hgT
  obtain ⟨jr, hjr⟩ := ENat.ne_top_iff_exists.mp hrT
  rw [← hjg] at hjG1' hjG2' ⊢
  rw [← hjr] at hjR1' hjR2' ⊢
  have a1 : jg ≤ JG := by exact_mod_cast hjG1'
  have a2 : JG ≤ jg + 1 := by exact_mod_cast hjG2'
  have a3 : jr ≤ JR := by exact_mod_cast hjR1'
  have a4 : JR ≤ jr + 1 := by exact_mod_cast hjR2'
  simp only [ENat.toNat_natCast] at hqv ⊢
  refine ⟨ENat.natCast_ne_top jg, ENat.natCast_ne_top jr, 2 * ((JG : ℤ) - jg) - 2 * ((JR : ℤ) - jr),
    abs_le.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [hqv]
  push_cast
  ring

end Core

end ZInQ.Contrib.CloudB3RC53.GenusOdd
