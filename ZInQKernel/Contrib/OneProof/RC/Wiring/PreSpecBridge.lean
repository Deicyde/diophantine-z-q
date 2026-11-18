import ZInQKernel.Contrib.OneProof.RC.Wiring.PreSpec
import ZInQKernel.Contrib.CloudB3RC53.PreFields.Spec

/-!
# The two statements of the data specification agree

`Wiring.PreDataSpec` (lane RC0) restates the RC53 group's `PreFields.PreFieldsSpec` field for field, because the latter's
file imports `Wiring/Leaves.lean` and so cannot be imported back. They are equivalent.
-/

namespace ZInQ.Manuscript.RC.Wiring

theorem preDataSpec_iff_preFieldsSpec {ℓ : ℕ} (W : WData ℓ) :
    PreDataSpec W ↔ ZInQ.Contrib.CloudB3RC53.PreFields.PreFieldsSpec W :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

end ZInQ.Manuscript.RC.Wiring
