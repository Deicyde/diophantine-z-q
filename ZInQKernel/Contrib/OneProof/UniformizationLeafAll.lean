import ZInQKernel.Contrib.HDecomp.Analytic.Uniformization
import ZInQKernel.Contrib.CloudB3W17Uniformization.Uniformization

/-!
# Exact H103: analytic uniformization of every complex abelian variety

The original BP coordinate-form statement is proved from genuine scheme-point
analytic manifolds, proper compactness, connectedness, actual analytic
exponentials and full-lattice torus quotients. All supporting constructions and
source attributions are under the W17 donor and uniformization directories.
No additional literature leaf, uniformization premise, changed statement,
custom parser or build-time proof shortcut is used.
-/

/-- The unchanged H103 statement, proved without additional open hypotheses. -/
theorem uniformizationLeafAll_proof : BPAnalytic.Uniformization.UniformizationLeafAll :=
  CloudB3W17Uniformization.uniformizationLeafAll
