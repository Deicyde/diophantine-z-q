import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.MilneIsogenyQuasiInverse

open HDec.HSyn in
/-- The field's type, read from the current bundle, is the proved Prop, by `rfl`. -/
example : (∀ b : OpenAddedLeaves17, (b.milneIsogenyQuasiInverse : AvSplit.MilneIsogenyQuasiInverse)
    = b.milneIsogenyQuasiInverse) := fun _ => rfl

open HDec.HSyn in
example (b : OpenAddedLeaves17) : b.milneIsogenyQuasiInverse =
    ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof := rfl
