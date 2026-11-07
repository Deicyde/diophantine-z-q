import ZInQKernel.Compiler.Programs.Lowering
example (J x y z : ℕ) (hx : x < J) (σ : ℕ → ℕ) (hzp : 0 < σ z) (hA0 : σ (J + 1) = 0)
 (hA2 : σ (J + 1 + 2) = 0) (hA3 : σ (J + 1 + 3) = 0) (hA4 : σ (J + 1 + 4) = 0) (hA5 : σ (J + 1 + 5) = 0) (rr qq : ℕ) (σ2 : ℕ → ℕ) (hσ2 :
  σ2 = fun i =>
    if i = x then 0 else if i = J + 1 then σ y else if i = J + 1 + 2 then σ z else if i = J + 1 + 4 then σ z else σ i) :
 (fun i =>
      if i = J + 1 then 0
      else if i = J + 4 then rr else if i = J + 5 then σ z - rr else if i = J + 6 then qq else σ2 i) =
    fun i =>
    if i = x then 0
    else
      if i = J + 1 then 0
      else
        if i = J + 1 + 3 then rr
        else if i = J + 1 + 4 then σ z - rr else if i = J + 1 + 5 then qq else if i = J + 1 + 2 then σ z else σ i := by
  subst hσ2
  funext i
  beta_reduce; split_ifs <;> subst_vars <;> omega
