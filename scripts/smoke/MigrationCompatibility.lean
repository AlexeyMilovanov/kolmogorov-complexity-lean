import KolmogorovMathlib
import Lean

open Kolmogorov
open Lean Meta Elab Command

elab "assert_compat " source:str " => " target:ident : command => do
  if source.getString.isEmpty then
    throwError "compatibility source name must not be empty"
  discard <| resolveGlobalConstNoOverload target

assert_compat "List.dedup" => List.localDedup
assert_compat "List.dedup_nodup" => List.nodup_localDedup
assert_compat "UniquelyDecodable" => InformationTheory.UniquelyDecodable
assert_compat "_root_.Primrec.list_drop" => Primrec.list_drop_listFirst
assert_compat "_root_.Primrec.list_take" => Primrec.list_take_listFirst
assert_compat "_root_.Primrec.list_takeWhile" => Primrec.list_takeWhile
assert_compat "emittedHalfRichChunks_fold_step" => emittedHalfRichChunksFoldStep
assert_compat "emittedHalfRichChunks_fold_step_primrec" =>
  emittedHalfRichChunksFoldStep_primrec
assert_compat "emittedHalfRichChunks_step" => emittedHalfRichChunksStep
assert_compat "emittedHalfRichChunks_step_primrec" => emittedHalfRichChunksStep_primrec
assert_compat "ge_invPow2" => RatMass.geInvPow2
assert_compat "list_dedup_eq_root" => List.localDedup_eq_dedup
assert_compat "list_dedup_eq_root_gen" => List.localDedup_eq_dedup
assert_compat "list_dedup_gen_primrec" => local_dedup_primrec
assert_compat "logSlack_add_nat_le" => logSlack_add_const_le
assert_compat "mem_List.dedup" => List.mem_localDedup
assert_compat "mem_eraseDups_bitString" => List.mem_eraseDups
assert_compat "nodup_eraseDups_bitString" =>
  CodedFiniteDistribution.eraseDups_bitstring_nodup
