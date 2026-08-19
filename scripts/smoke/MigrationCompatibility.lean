import KolmogorovMathlib
import Lean

open Kolmogorov
open Lean Meta Elab Command

elab "assert_compat " source:str " => " target:ident : command => do
  if source.getString.isEmpty then
    throwError "compatibility source name must not be empty"
  discard <| resolveGlobalConstNoOverload target

assert_compat "_root_.Primrec.list_drop" => Primrec.list_drop
assert_compat "_root_.Primrec.list_take" => Primrec.list_take
assert_compat "_root_.Primrec.list_takeWhile" => Primrec.list_takeWhile
assert_compat "exists_bits_linear_domination" => Kolmogorov.exists_bits_linear_domination
