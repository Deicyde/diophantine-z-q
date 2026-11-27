import ZInQKernel.Contrib.OneProof.GaudronRemondSection9SS
import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.ConnectedOpenFromProperModel
import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.MarkedSemiabelianComponent
import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.MarkedHeightWitness
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed

/-!
# The printed lower bound for the stable Faltings height

Gaudron–Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
§9, proof of Lemma 9.1, p. 2098, quotes Bost's lower bound
`h_F(A) ≥ -(3/2) dim A` in Faltings' original normalization. The metric
convention is that of *Théorème des périodes et degrés minimaux d'isogénies*,
Comment. Math. Helv. 89 (2014), §2.3, pp. 351–352. Only the inequality printed
in §9 is assumed here, not the stronger bound in Corollary 8.4 of that paper.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped BigOperators CategoryTheory.MonObj NumberField

namespace ZInQ.Contrib.FaltingsLowerBound

open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightFix ZInQ.H5Glue ZInQ.SemistabAssembly
open ZInQ.BostGR9 ZInQ.Contrib.IsogenyDegree
open ZInQ.Contrib.CloudB3W16Torsion (mumfordTorsionAlgClosed_proof)
open DictModels.RaynaudOr (HasSemiAbelianIdCompTorus)

/-- The §9 inequality evaluated on a semiabelian model of the marked variety
`A_L`. The determinant lattice, chosen section, and all squared norms belong
to that model over `𝓞 L`, in Faltings' original normalization. -/
def DukeSec9OnSemiabelianModel : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (A : PkgI3.AbVar K) (G : GroupModel A L) (g : ℕ),
    A.dim = (g : WithBot ℕ∞) →
    (∀ (p : Ideal (𝓞 L)) [p.IsMaximal],
      ConnectedSpace (resFibre G p).left ∧ HasSemiAbelianIdCompTorus (resFibre G p)) →
    ∀ (eta : G.hodgeSpace g), eta ∈ printedDetLattice G g → eta ≠ 0 →
      secIndex (printedDetLattice G g) eta ≠ 0 →
    ∀ (r : (L →+* ℂ) → ℝ), (∀ τ, IsPrintedMetricSq G τ eta (r τ)) →
      -(3 / 2) * (g : ℝ) ≤
        (Real.log (secIndex (printedDetLattice G g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L

/-- Compare the full witness for the root's height with its computation on the
actual marked semiabelian identity component. In particular the index and the
squared norm at each embedding are preserved, without any metric rescaling. -/
theorem gaudronRemondSec9LowerAnSS_of_dukeSec9 (hPrint : DukeSec9OnSemiabelianModel) :
    GaudronRemondSec9LowerAnSS := by
  intro K _ _ A g hg x hx
  obtain ⟨L, iField, iNumber, iAlg, N, g', hN, hs, hg', eta, hEta, hNZ, hIndex, r, hNorm, hVal⟩ := hx
  have heq : g' = g := by exact_mod_cast hg'.symm.trans hg
  subst g'
  obtain ⟨V, hV, hConn⟩ := connectedOpenOfGroupModels_proof K L A N
  obtain ⟨G, j, hjOpen, hjMon, _, hjIso, _, hSemi⟩ :=
    exists_markedSemiabelianComponent_of_goodOpen N hs.2 V hV hConn
  have hT35 := AvSplit.Final.h38 uniformizationLeafAll_proof mumfordTorsionAlgClosed_proof
  let eta' := hodgeMap G N j g eta
  obtain ⟨hEta', hNZ', hIndex', hNorm'⟩ :=
    @markedHeightWitness_openIso K _ _ A L _ _ _ hT35 g hg G N hN j hjMon hjOpen hjIso
      eta hEta hNZ hIndex r hNorm
  have hIndexNonzero : secIndex (printedDetLattice G g) eta' ≠ 0 := by
    rw [show secIndex (printedDetLattice G g) eta' = secIndex (printedDetLattice N g) eta from hIndex']
    exact hIndex
  have hb := hPrint K L A G g hg hSemi eta' hEta' hNZ' hIndexNonzero r hNorm'
  rw [show secIndex (printedDetLattice G g) eta' = secIndex (printedDetLattice N g) eta from hIndex',
    ← hVal] at hb
  exact hb

end ZInQ.Contrib.FaltingsLowerBound
