import ZInQKernel.Contrib.OneProof.RC.Wiring.Data
import ZInQKernel.Contrib.OneProof.RC.Wiring.Even
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ArtinEndpoints
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.FromPrintsAnalytic
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic

/-!
# Theorem 5.3, Lane RC0: (3.4) from the shared layer's GenusOdd at the genuine objects

The shared layer's GenusOdd proves (3.4) at every rough companion (`gzEveryCompanion_of_scaled_artin`,
with `C_per = 0`) from `Prints` and one GLUE statement, the Artin factorization of the ring-class
`L`-functions (`ArtinFactorization`); genus theory's square roots, the Galois closure and the
splitting criterion are PROVED there. Its objects are: `j_gen`, `j_rc` read
off selections of Heegner data, the prepared filter `Prepared`, the genus partner `GenusPartner`,
the rough companion relation `Companion`, and any `L_*` that is a nonzero real rescaling of
`√|d| L(E^{(d)},1)` at negative arguments (`LstarScaled`).

**The normalization of `L_*`** (tex 1825–1830, 7175–7177). Lane RC11's `CentralNormalization` is
such a rescaling (`lstarScaled_of_centralNormalization`), given entire continuations of the twists
by negative integers, which the root numbers supply (`cont_of_rootNumberExists`). The valuation
differences of (3.4) do not depend on the rescaling. GenusOdd also uses that
`√|h_*| L(E^{(h_*)},1)/Ω⁻`, for the lattice's `Ω⁻`, is a nonzero rational (Manin–Drinfeld, tex 2403),
a named input of the instance; `Ω⁻ ≠ 0` follows from it.

`gz34Target_of_genusOdd` (PROVED) gives `Gz34Target` (both clauses: the rough companions and the
final `k`) from `Prints`, `ArtinFactorization`, the root numbers and a `GenusOddInstance`: RC11's
normalization of the interface's `L_*`, the CST data of `E`, the Manin–Drinfeld input just named,
the Heegner selections, the identification of the interface data with GenusOdd's objects, and the
final `k`'s conditions (as in `RCSteps.companion`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- Every twist of an elliptic curve has an entire continuation of its `L`-series, from the root
numbers (PROVED). -/
theorem cont_of_rootNumberExists (hRN : Nonvanishing.FromRC8.RootNumberExists)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) : ∃ F, IsLContinuation E F := by
  obtain ⟨w, N, -, F, hF, -⟩ := hRN E hE
  exact ⟨F, hF⟩

/-! ## The instance -/

/-- **An instance of GenusOdd's genuine objects of (3.4) for the interface data `W`** (tex
2343–2353, 2403–2440, 2595–2603). Kinds and owners:
* `N`, `hN`: lane RC11's normalization of the interface's `L_*` (GLUE Birch–Manin, tex 1825–1830,
  7175–7177); owner RC11;
* `f`, `hf`, `Lat`, `hLat`, `hNC`, `κ`, `hκ`: the newform of `E`, a non-CM lattice of `E` and the
  scale of the modular parametrization (definition; the data of Cai–Shu–Tian's statement);
* `hElkikMD`: `√|h_*| L(E^{(h_*)},1)/Ω⁻`, for the lattice's least positive imaginary period `Ω⁻`,
  is a nonzero rational (GLUE: Manin–Drinfeld; tex 1826–1827, 2403, 7176–7177); owner batch 3
  GenusOdd;
* `hgp`: `h_*` is a genus partner in GenusOdd's sense (ELLIOT/definition, tex 2403–2406; it adds the
  squares at the level of the newform to lane RC13's partner);
* `selG`, `selR`, `hselG`, `hselR`: Heegner data at the prepared simple zeros and their companions
  (definition: the Heegner points of Cai–Shu–Tian's statement, tex 2411–2416);
* `hprep`, `hjg`, `hjr`, `hcomp`: the interface data are GenusOdd's objects (definition);
* `hk0`, `hksq`, `hk4`, `hk2N`, `hkcop`: the final `k` (ELLIOT, tex 2595–2603 with 2349–2352). -/
structure GenusOddInstance {ℓ : ℕ} (W : WData ℓ) : Type 1 where
  hE : (Ecurve ℓ).IsElliptic
  f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) : Subgroup (GL (Fin 2) ℝ)) 2
  hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ)
  Lat : PeriodPair
  hLat : IsLatticeOf (Ecurve ℓ) Lat
  hNC : IsNonCMLattice Lat
  κ : ℂ
  hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ
  /-- lane RC11's normalization of `L_*` -/
  N : Even.CentralNormalization (Ecurve ℓ)
  /-- it is the interface's `L_*` -/
  hN : N.Lstar = W.Lstar
  /-- `L_*(h_*)` over the lattice's `Ω⁻` is a nonzero rational (Manin–Drinfeld) -/
  hElkikMD : ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat W.hstar
  /-- `h_*` is a genus partner in GenusOdd's sense -/
  hgp : GenusPartner (Ecurve ℓ) W.hstar
  selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * W.hstar) 1 W.hstar)
  selR : (h k : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ k h.natAbs h)
  hselG : ∀ h, Prepared (Ecurve ℓ) W.hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
    (selG h).isSome
  hselR : ∀ h k', Prepared (Ecurve ℓ) W.hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
    Companion (Ecurve ℓ) Lat W.hstar h k' → (selR h k').isSome
  /-- the prepared filter is GenusOdd's -/
  hprep : ∀ h, W.prepared h → Prepared (Ecurve ℓ) W.hstar h
  /-- `j_gen` is read off the genus selections -/
  hjg : W.jgen = jgenOf (Ecurve ℓ) f Lat κ W.hstar selG
  /-- `j_rc` is read off the ring-class selections -/
  hjr : W.jrc = jrcOf (Ecurve ℓ) f Lat κ selR
  /-- a rough companion is a companion in GenusOdd's sense -/
  hcomp : ∀ h k', W.IsRoughCompanion h k' → Companion (Ecurve ℓ) Lat W.hstar h k'
  /-- the final `k`: negative, squarefree, `≡ 1 (mod 4)`, a unit square at `2N`, prime to `h_*` -/
  hk0 : W.kfin < 0
  hksq : Squarefree W.kfin
  hk4 : W.kfin % 4 = 1
  hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → UnitSquareAt p W.kfin
  hkcop : IsCoprime W.kfin W.hstar

/-- The instance carries lane RC11's normalization of `L_*` (PROVED). -/
theorem lstarNormalized_of_instance {ℓ : ℕ} {W : WData ℓ} (I : GenusOddInstance W) :
    LstarNormalized W.toRCData :=
  ⟨I.N, I.hN⟩

/-- The interface's `L_*` is a rescaled `√|d| L(E^{(d)},1)` at negative arguments (PROVED: batch 3's
`lstarScaled_of_centralNormalization`, the continuations from the root numbers). -/
theorem lstarScaled_of_instance {ℓ : ℕ} {W : WData ℓ}
    (hRN : Nonvanishing.FromRC8.RootNumberExists) (I : GenusOddInstance W) :
    LstarScaled (Ecurve ℓ) W.Lstar := by
  have := I.hE
  rw [← I.hN]
  refine lstarScaled_of_centralNormalization I.N fun d hd => ?_
  exact cont_of_rootNumberExists hRN
    (PrintsAnalytic.qtwist_isElliptic (E := Ecurve ℓ) (by exact_mod_cast hd.ne))

/-- **(3.4) with one period constant (`C_per = 0`)** from GenusOdd (PROVED from
`gzEveryCompanion_of_scaled_artin`). The final `k` is a companion of every prepared simple zero `h` with
`L_*(hk) ≠ 0` whose primes are outside the support with `(k/q) = 1`: at the primes of `2N` by the
recorded squares, at the primes of `h` by `(k/q) = 1` (`h` is odd, being `≡ 1 (mod 8)`). -/
theorem gz34Target_of_genusOdd {ℓ : ℕ} {W : WData ℓ} (P : Prints) (hArtin : ArtinFactorization)
    (hRN : Nonvanishing.FromRC8.RootNumberExists) (I : GenusOddInstance W) : Gz34Target W := by
  have := I.hE
  have hsc := lstarScaled_of_instance hRN I
  obtain ⟨q, hq0, hq⟩ := I.hElkikMD
  have hΩ0 : omegaMinus I.Lat ≠ 0 :=
    omegaMinus_ne_zero_of (E := Ecurve ℓ) (a := W.hstar) (by rw [← hq]; exact_mod_cast hq0)
  have hall := gzEveryCompanion_of_scaled_artin P hArtin (E := Ecurve ℓ) rfl rfl I.hf
    I.hLat I.hNC I.hκ I.hgp ⟨q, hq⟩ I.selG I.selR I.hselG I.hselR hsc
  refine ⟨0, fun h k' hp hz hk => ?_, fun h hp hz hLk hq => ?_⟩
  · obtain ⟨ε, hε, heq⟩ := hall h k' (I.hprep h hp) hz (I.hcomp h k' hk)
    refine ⟨ε, hε, ?_⟩
    rw [I.hjg, I.hjr]
    exact heq
  · have hP := I.hprep h hp
    have hneg : h * W.kfin < 0 := mul_neg_of_pos_of_neg hP.1 I.hk0
    -- `L_*(hk) ≠ 0` for GenusOdd's `L_*`
    obtain ⟨Ω', -, hrel⟩ := hsc
    have hLv : Lval (qtwist (Ecurve ℓ) (((h * W.kfin : ℤ)) : ℚ)) ≠ 0 := by
      intro h0
      apply hLk
      have := hrel (h * W.kfin) hneg
      rw [h0, mul_zero, zero_div] at this
      exact_mod_cast this
    have hLC : Lstar (Ecurve ℓ) I.Lat (h * W.kfin) ≠ 0 := Lstar_ne_zero_of hΩ0 hneg.ne hLv
    have h2N2 : 2 ∣ 2 * newformLevel (Ecurve ℓ) := dvd_mul_right 2 _
    have hh2 : ¬ (2 : ℤ) ∣ h := (hP.2.2.1 2 Nat.prime_two h2N2).1
    have hcompk : Companion (Ecurve ℓ) I.Lat W.hstar h W.kfin := by
      refine ⟨I.hk0, I.hk4, I.hksq, fun p hp' hpd => ?_, I.hkcop, hLC⟩
      have hpd' : (p : ℤ) ∣ ((2 * newformLevel (Ecurve ℓ) : ℕ) : ℤ) * h := by
        exact_mod_cast hpd
      rcases (Int.prime_iff_natAbs_prime.mpr (by simpa using hp')).dvd_mul.mp hpd' with h1 | h1
      · exact I.hk2N p hp' (Int.natCast_dvd_natCast.mp h1)
      · have hp2 : p ≠ 2 := by
          rintro rfl
          exact hh2 (by exact_mod_cast h1)
        exact squareAt_of_jacobiSym hp' hp2 (hq p hp' h1).2
    obtain ⟨ε, hε, heq⟩ := hall h W.kfin hP hz hcompk
    refine ⟨ε, hε, ?_⟩
    rw [I.hjg, I.hjr]
    exact heq

end ZInQ.Manuscript.RC.Wiring
