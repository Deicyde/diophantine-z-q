namespace ZInQ.Manuscript.RC.Wiring

/-- **The chain conductors** `d_0 = d`, `d_{j+1} = d_j · ps[j]` (with `ps[j] = 1` past the end of
`ps`), i.e. `d_j = d ∏_{j' < j} ps[j']` (tex 2914–2921, 4142–4146). Kind: definition. -/
def chainCond (d : Nat) (ps : List Nat) : Nat → Nat
  | 0 => d
  | j + 1 => chainCond d ps j * ps.getD j 1

/-- `d ∣ d_j` (tex 2914–2921). Kind: PROVED. -/
theorem dvd_chainCond (d : Nat) (ps : List Nat) : ∀ j, d ∣ chainCond d ps j
  | 0 => Nat.dvd_refl d
  | j + 1 => Nat.dvd_mul_right_of_dvd (dvd_chainCond d ps j) _

end ZInQ.Manuscript.RC.Wiring
