import Mathlib
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
example (v : HeightOneSpectrum ℤ) (c : ℚ) : (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) c) v = algebraMap ℚ (v.adicCompletion ℚ) c := rfl
example (v : HeightOneSpectrum ℤ) (c : ℚ) : (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) c) v = algebraMap ℚ (v.adicCompletion ℚ) c := by simp
#check @Submonoid.mem_units_iff
#check @Subgroup.mem_map_equiv
#check @Units.mapEquiv
#check @GlueVigneras.coord_smul
