import ZInQKernel.Contrib.OneProof.RC.KatoP2.EvenBridge
import ZInQKernel.Contrib.OneProof.RC.KatoP2.Kodai08Transport
import ZInQKernel.Contrib.OneProof.RC.KatoP2.Kodai08Purity

/-! Conditional Appendix E wiring on the actual constituent indices. The
remaining Appendix E construction consumes (K15) for those constituents;
the length bound is supplied here by the Kodai draft, not by that construction. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2.Checked

open PrintsArith AppEK1 _root_.ZInQ.Manuscript.RC.Even ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-- The unspecialized arithmetic data for one constituent before applying the
1999 theorem. `d` is the full odd conductor. Only the arithmetic inputs to
(K8), §0.6, §0.7, and the support comparison are bundled. -/
structure KodaiConstituent {E : WeierstrassCurve ℚ} {c ds : ℕ}
    (retained : RetainedZeta E c ds) (d : ℕ) where
  a : ℕ
  es : EulerSystemData ℤ_[2]
  transfer : TwistTransfer retained d a es
  full : KodaiFullOpen (kodaiBase E d)
  retainedIw : KodaiJStar
  finiteH2 : Module.Finite KatoLambda2 full.iw.H2
  tower : KodaiTower es (kodaiBase E d) full.iw
  class07 : tower.IsClass07
  H1compare : KatoH1Comparison es (kodaiBase E d) full.iw retainedIw.iw tower
  H2cone : KatoOddSupportCone full retainedIw
  charGalois : GalQ →* ℤˣ
  char_eq : ∀ [NeZero (primitiveD d a)] {ζ : Qbar}
    (hζ : IsPrimitiveRoot ζ (primitiveD d a)) (g : GalQ),
      ((charGalois g : ℤ) : ℤ_[2]) = (transfer.χ (hζ.autToPow ℚ g) : ℤ_[2])
  realSign : Module.finrank ℚ_[2]
    (LinearMap.ker (rationalTwist E charGalois OpenImage.complexConj + 1)) = 1
  nonzeroClass : GenericNonzero full.iw

/-- The print remains separate from all of the arithmetic object
identifications; its specialization uses the polynomial on the full twist. -/
abbrev KodaiConstituent.Print08 {E : WeierstrassCurve ℚ} {c ds d : ℕ}
    {Z : RetainedZeta E c ds} (K : KodaiConstituent Z d) : Prop :=
  KatoKodai99Thm08Print (rationalTwist E K.charGalois) OpenImage.complexConj
    K.es (kodaiBase E d) (c * ds)
    (twistedPoly E K.transfer.χ) K.full K.tower

/-- Applying the print to the extended system supplies the bound on the
(K15) module and the ideal of the retained class. -/
theorem KodaiConstituent.retainedK15 {E : WeierstrassCurve ℚ} {c ds d : ℕ}
    {Z : RetainedZeta E c ds} (K : KodaiConstituent Z d)
    (h812 : Kato812.KatoProp812Print E c ds Z.es Z.zAt) (h08 : K.Print08)
    (hS : SerreThm3) (hCM : @HasNoCM E Z.elliptic) (hd : 0 < d) (hs : Nat.Coprime d (c * ds)) :
    RetainedK15 K.retainedIw.iw := by
  have := Z.elliptic
  have hfixed := Z.smooth_fixed.symm
  have hbase : Nat.Coprime (kodaiBase E d) (c * ds) := hfixed.mul_left hs
  have h₂ : Nat.Coprime 2 (c * ds) := hfixed.coprime_dvd_left (dvd_mul_right _ _)
  have hD : Nat.Coprime (primitiveD d K.a) (c * ds) := hs.mul_left (h₂.pow_left _)
  have hpos : 0 < kodaiBase E d := by
    have := Z.level_pos
    dsimp [kodaiBase]
    positivity
  have h₂d : 2 ∣ kodaiBase E d := (dvd_mul_right 2 _).trans (dvd_mul_right _ _)
  have hbound := h08 hpos h₂d hbase
    (fun _ _ hq hm hmq =>
      kodaiNorm_prime (kodaiNorm_of_prop812 Z h812 K.transfer hd hD) hm hmq hq)
    K.realSign (kodaiAbsIrred_of_serre hS E hCM (DetTateCyclotomic.detTateTwoCyclotomic E) K.charGalois)
    (kodaiUnipotent_of_serre E hS hCM K.charGalois)
    (kodaiPurity_of_quadratic K.transfer.χ K.transfer.quadratic) K.class07 K.nonzeroClass
  have htrace : Kodai07Corestriction K.transfer := fun n _ =>
    K.transfer.trans (2 ^ n) (kodaiBase E d * 2 ^ n) (dvd_mul_left _ _)
  exact retainedK15_of_kodai08 K.H1compare K.H2cone
    (kodai07_eq_retained K.transfer h812 hd hbase K.H1compare K.class07 htrace)
    K.finiteH2 hbound

/-- One family's print input is applied to each of its primitive constituents
with that family's (K5) smoothers. `oddConductor` is `natAbs (fam.h x)`,
never the conductor with the fixed bad primes removed. -/
structure KodaiFamilyData (E : WeierstrassCurve ℚ) (e Nodd : ℕ) {N : ℕ}
    (fam : BinaryFamily N) where
  retained : RetainedZeta E (smoothing e Nodd (supportProduct fam))
    (smoothing e Nodd (supportProduct fam))
  normPrint : Kato812.KatoProp812Print E (smoothing e Nodd (supportProduct fam))
    (smoothing e Nodd (supportProduct fam)) retained.es retained.zAt
  serre : SerreThm3
  nonCM : @HasNoCM E retained.elliptic
  part : ∀ x : Fin fam.b → ZMod 2, KodaiConstituent retained (oddConductor fam x)
  conductor : ∀ x, (part x).a = if fam.h x % 4 = 1 then 0 else 2
  character : ∀ (x : Fin fam.b → ZMod 2) (r : Qbar), r ^ 2 = (fam.h x : Qbar) →
    ∀ g : GalQ, g r = (((part x).charGalois g : ℤ) : Qbar) * r

/-- The remaining Appendix E construction at its new cut: after (K15), use
the local corrections, the determinant of the positive complex, and central
calibration to construct the family output. The constants are chosen
uniformly. The same unresolved manuscript work was part of the old bridge. -/
def AppEFromKatoP2 (E : WeierstrassCurve ℚ) (N : ℕ) (L : CentralNormalization E)
    (e Nodd : ℕ) (K : ∀ fam : BinaryFamily N, KodaiFamilyData E e Nodd fam) : Prop :=
  ∃ (cE : ℕ) (CE Cfix Cg Cr Ce : ℤ),
    0 ≤ CE ∧ 0 ≤ Cfix ∧ 0 ≤ Cg ∧ 0 ≤ Cr ∧ 0 ≤ Ce ∧
    ∀ fam : BinaryFamily N, (∀ x, RetainedK15 ((K fam).part x).retainedIw.iw) →
      Nonempty (EvenFamilyOutput E N L cE CE Cfix Cg Cr Ce fam)

/-- The unchanged Appendix E output at the new boundary. -/
theorem appEOutputs_of_katoP2 {E : WeierstrassCurve ℚ} {N : ℕ}
    {L : CentralNormalization E} {e Nodd : ℕ}
    {K : ∀ fam : BinaryFamily N, KodaiFamilyData E e Nodd fam}
    (h08 : ∀ fam x, ((K fam).part x).Print08) (hE : AppEFromKatoP2 E N L e Nodd K) :
    AppEOutputs E N L := by
  obtain ⟨cE, CE, Cfix, Cg, Cr, Ce, hCE, hCfix, hCg, hCr, hCe, assemble⟩ := hE
  refine ⟨cE, CE, Cfix, Cg, Cr, Ce, hCE, hCfix, hCg, hCr, hCe, fun fam => assemble fam ?_⟩
  intro x
  exact ((K fam).part x).retainedK15 (K fam).normPrint (h08 fam x) (K fam).serre (K fam).nonCM
    (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (fam.sqfree x).ne_zero))
    (family_smoothers_coprime fam x e Nodd)

/-- (3.2), consuming the corrected Kodai draft and the construction after (K15). -/
theorem evenScalar32_of_katoP2 {E : WeierstrassCurve ℚ} {N : ℕ} (hN : N ≠ 0)
    {L : CentralNormalization E} {e Nodd : ℕ}
    {K : ∀ fam : BinaryFamily N, KodaiFamilyData E e Nodd fam}
    (h08 : ∀ fam x, ((K fam).part x).Print08) (hE : AppEFromKatoP2 E N L e Nodd K) :
    EvenScalar32 E N L :=
  evenScalar32_of_appE hN (appEOutputs_of_katoP2 h08 hE)

/-- The fixed-curve App E output used by the even upper bounds. -/
theorem appEOutputs_of_katoP2_fixed {ℓ : ℕ} {L : CentralNormalization (Ecurve ℓ)}
    {e Nodd : ℕ} {K : ∀ fam : BinaryFamily (EvenUpperText.N₀ ℓ),
      KodaiFamilyData (Ecurve ℓ) e Nodd fam}
    (h08 : ∀ fam x, ((K fam).part x).Print08)
    (hE : AppEFromKatoP2 (Ecurve ℓ) (EvenUpperText.N₀ ℓ) L e Nodd K) :
    AppEOutputs (Ecurve ℓ) (EvenUpperText.N₀ ℓ) L :=
  appEOutputs_of_katoP2 h08 hE

open EvenUpperText Wiring in
/-- Same two outputs as the existing fixed-level wiring. -/
theorem evenScalar32_of_katoP2_fixed (hB : PoleS12.BCDTThmA)
    {ℓ : ℕ} (hℓ : 0 < ℓ) {W : WData ℓ} (C : CentralNormalization (Ecurve ℓ))
    (hCW : C.Lstar = W.Lstar) {e Nodd : ℕ}
    {K : ∀ fam : BinaryFamily (N₀ ℓ), KodaiFamilyData (Ecurve ℓ) e Nodd fam}
    (h08 : ∀ fam x, ((K fam).part x).Print08)
    (hE : AppEFromKatoP2 (Ecurve ℓ) (N₀ ℓ) C e Nodd K) :
    EvenScalar32 (Ecurve ℓ) (N₀ ℓ) C ∧ Scalar32 W := by
  have h := evenScalar32_of_katoP2 (level_pos_of_bcdt hB hℓ).ne' h08 hE
  exact ⟨h, (EvenUpperText.scalar32_iff_even C hCW).mpr h⟩

/-- The glue sweep's (3.2) statement at `Ecurve ℓ` with dyadic inputs. -/
theorem evenScalar32_of_katoP2_ecurve {ℓ N : ℕ} (hN : N ≠ 0)
    {L : CentralNormalization (Ecurve ℓ)} {e Nodd : ℕ}
    {K : ∀ fam : BinaryFamily N, KodaiFamilyData (Ecurve ℓ) e Nodd fam}
    (h08 : ∀ fam x, ((K fam).part x).Print08)
    (hE : AppEFromKatoP2 (Ecurve ℓ) N L e Nodd K) : EvenScalar32 (Ecurve ℓ) N L :=
  evenScalar32_of_katoP2 hN h08 hE

/-- Same (E.9) conclusion as the glue sweep on the dyadic inputs. -/
theorem evenLowerBound_of_katoP2_ecurve (hP : ZInQ.Contrib.CloudB3RC53.Prints)
    (hH : PrintsAnalytic.HasseConvergence) {ℓ N : ℕ} (hℓ : 0 < ℓ) (hN : N ≠ 0)
    {L : CentralNormalization (Ecurve ℓ)} {e Nodd : ℕ}
    {K : ∀ fam : BinaryFamily N, KodaiFamilyData (Ecurve ℓ) e Nodd fam}
    (h08 : ∀ fam x, ((K fam).part x).Print08)
    (hE : AppEFromKatoP2 (Ecurve ℓ) N L e Nodd K) : EvenLowerBound (Ecurve ℓ) L := by
  have : (Ecurve ℓ).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  exact GlueSweep.Even.evenLowerBound_of_evenScalar32_of_prints hP hH
    (evenScalar32_of_katoP2_ecurve hN h08 hE)

end ZInQ.Manuscript.RC.KatoP2.Checked
