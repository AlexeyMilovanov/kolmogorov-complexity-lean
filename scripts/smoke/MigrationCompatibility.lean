import KolmogorovMathlib
import Lean

open Kolmogorov
open Lean Meta Elab Command

elab "assert_compat " source:str " => " target:ident : command => do
  if source.getString.isEmpty then
    throwError "compatibility source name must not be empty"
  discard <| resolveGlobalConstNoOverload target
