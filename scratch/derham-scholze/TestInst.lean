import ZInQKernel.Contrib.OneProof.DeRhamScholze
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4
set_option synthInstance.maxHeartbeats 400000
variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  (V : Type) [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
#synth AddCommGroup (ddrSpaceOver p ρ)
#synth Module.Free ℚ_[p] (ddrSpaceOver p ρ)
#synth AddCommGroup (htSpaceOver p ρ 0)
#check (ddrSpaceOver p ρ : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))
set_option pp.explicit true in
#check (ddrSpaceOver p ρ)
