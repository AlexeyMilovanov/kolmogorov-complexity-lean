import KolmogorovMathlib.Foundation.PrimrecExtras

open Kolmogorov

example : Primrec (fun n : Nat => n) := by
  primrec_auto
