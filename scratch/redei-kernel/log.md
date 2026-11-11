# redei-kernel log

- Wrote ZInQKernel/RouteK/Redei/Kernel.lean (namespace ZInQ.RouteK.Redei): redeiK_lapl_rowSum,
  redeiK_det_updateCol, redeiK_sum_updateCol, redeiK_ker_iff_det, redeiK_zmod2_cases,
  redeiK_kernel_iff_updateCol, kernel_trivial_iff_redeiG (statement verbatim from Probe.lean).
- Root ZInQKernel/RouteK/RedeiKernel.lean with #guard_msgs #print axioms (propext, Classical.choice,
  Quot.sound); imported from ZInQKernel.lean.
- Errors fixed: `lake env lean` fails (package z_in_q not built) -> use lake build; omit must precede
  docstring; Function.update_eq_self_iff direction; `0 ⟨q,hq⟩` needs Pi.zero_apply.
- lake build ZInQKernel.RouteK.RedeiKernel: success.
