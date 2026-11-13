import ZInQKernel.Contrib.GZTheta.Eta32
open ZInQ.GZTheta
example : ∀ x : Fin 32, expEQ (schreierQ (1, 0, (x : ℤ), 1) qS) % 12 = 1 := by decide
#eval (List.range 32).map fun x => expEQ (schreierQ (1, 0, (x : ℤ), 1) qS)
#eval (List.range 32).map fun x => schreierQ (1, 0, (x : ℤ), 1) qT
