/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelCover
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelGreedy.GreedyStages
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelStage
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.MonotoneComplexity.Dimension.AbsolutelyNonRandom
import KolmogorovMathlib.MonotoneComplexity.Dimension.DeficiencySemimeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.GapCover
import KolmogorovMathlib.MonotoneComplexity.Dimension.UniversalAlphaTest
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.ExitWidth
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSources
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.Reserves
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.SourceInvariant
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedSpendArithmetic
import KolmogorovMathlib.MonotoneComplexity.GacsDayEndgameScale
import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame
import KolmogorovMathlib.MonotoneComplexity.GacsDayGame
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayTestComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntryMonotonicity
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailGlobalProgress.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailGlobalProgress.Part02
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailMass
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.StateAt
import KolmogorovMathlib.MonotoneComplexity.GacsDayPinnedEndgame
import KolmogorovMathlib.MonotoneComplexity.GacsDayReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo.ServerProbes
import KolmogorovMathlib.MonotoneComplexity.GacsDaySubtreeEmbedding
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure.Part02
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2L5Disjoint
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RaisedKill
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveSupport
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.APrioriLogGap
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.ComputableCover.Decompressor
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.CondArithmeticCoding
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Converse
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.DecidableLengths
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.FinsetDeficiency
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.MaximalSupTest
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorrConverse
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.DiracSemimeasure
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.CappedScaling
import KolmogorovMathlib.MonotoneComplexity.Omega.LscBasic
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaPrefixCore
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction.REFamilyCriterion
import KolmogorovMathlib.MonotoneComplexity.Omega.Solovay.CompletenessRandomness
import KolmogorovMathlib.MonotoneComplexity.Omega.Solovay.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.BusyBeaverOmega
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.BusyBeavers
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.ExistenceFlatten
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.ExistenceSum
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.SolovayProperty
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse.Core
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse.Inequality
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison
import KolmogorovMathlib.MonotoneComplexity.PlainPrefixDips
import KolmogorovMathlib.MonotoneComplexity.SimpleTreeApproximation
import KolmogorovMathlib.MonotoneComplexity.StreamRelationEnumeration

/-!
# Deprecated aliases: MonotoneComplexity

Old names of declarations in the `KolmogorovMathlib.MonotoneComplexity`
material, kept so that code written against an earlier version of the
library still compiles.

Generated by `scripts/gen_deprecated.py` from the public rows of
`docs/history/phase3_renames.tsv`; do not edit by hand.
-/

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.IsLowerSemicomputableReal.rat_mul :=
  Kolmogorov.ComputableReals.IsLowerSemicomputableReal.rat_mul

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.KPPlain_ne_top := Kolmogorov.KPPlain_ne_top_of_isOptimalPrefixConditional

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.KPPlain_le_of_mem_cumSnapshotCodes :=
  Kolmogorov.KPPlain_le_of_mem_cumSnapshotCodes

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.KPPlain_le_of_mem_snapshotCodes :=
  Kolmogorov.KPPlain_le_of_mem_snapshotCodes

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.addPairBits := Kolmogorov.addPairBits

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.addPairBits_computable := Kolmogorov.addPairBits_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.addPairBits_eval := Kolmogorov.addPairBits_eval

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.bitsToNat_append := Kolmogorov.bitsToNat_append

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.bitsToNat_padBits := Kolmogorov.bitsToNat_padBits

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.bitsToNat_replicate_false := Kolmogorov.bitsToNat_replicate_false

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.cVal_eq_coe := Kolmogorov.cVal_eq_coe

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.cVal_le_kVal_add := Kolmogorov.cVal_le_kVal_add

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.card_le_of_ennreal_bound := Kolmogorov.card_le_of_ennreal_bound

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.cumSnapHelper_primrec := Kolmogorov.cumSnapHelper_primrec

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.cumSnapshotCodes := Kolmogorov.cumSnapshotCodes

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.cumSnapshotCodes_computable := Kolmogorov.cumSnapshotCodes_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.cumSnapshotCodes_prefix_of_le := Kolmogorov.cumSnapshotCodes_prefix_of_le

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.dyadicValue_max := Kolmogorov.dyadicValue_max

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.dyadicValue_sum := Kolmogorov.dyadicValue_sum_range_dim

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.exercise117_solovay_inequality :=
  Kolmogorov.solovay_plain_le_prefix_sub_prefix_prefix

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.four_mul_le_two_pow_add := Kolmogorov.four_mul_le_two_pow_add

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.four_mul_log2_affine_le := Kolmogorov.four_mul_log2_affine_le

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.four_mul_log2_le := Kolmogorov.four_mul_log2_le

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.getD_eq_of_prefix_common := Kolmogorov.getD_eq_of_prefix_common

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.kNatVal_diff_step := Kolmogorov.kNatVal_diff_step

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.kNatVal_eq_coe := Kolmogorov.kNatVal_eq_coe

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.kNatVal_le_log_bound := Kolmogorov.kNatVal_le_log_bound

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.kNatVal_le_two_mul_self := Kolmogorov.kNatVal_le_two_mul_self

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.kVal_eq_coe := Kolmogorov.kVal_eq_coe

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.kVal_le_cVal_add := Kolmogorov.kVal_le_cVal_add

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.length_padBits := Kolmogorov.length_padBits

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.log2_mul_le := Kolmogorov.log2_mul_le

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.natCodeToNatBitsMap := Kolmogorov.natCodeToNatBitsMap

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.natCodeToNatBitsMap_computable :=
  Kolmogorov.natCodeToNatBitsMap_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.prefix_take_eq := Kolmogorov.isPrefix_of_isPrefix_take

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCheck := Kolmogorov.solovayCheck

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCheckPair := Kolmogorov.solovayCheckPair

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCheckPair_computable := Kolmogorov.solovayCheckPair_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCheck_computable := Kolmogorov.solovayCheck_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCheck_max_isSome := Kolmogorov.solovayCheck_max_isSome

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCodes := Kolmogorov.solovayCodes

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCodes_computable := Kolmogorov.solovayCodes_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCond := Kolmogorov.solovayCond

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCond1_computable := Kolmogorov.solovayCond1_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCond2_computable := Kolmogorov.solovayCond2_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCond3_computable := Kolmogorov.solovayCond3_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCond_computable := Kolmogorov.solovayCond_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCond_lt_length := Kolmogorov.solovayCond_lt_length

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCtx := Kolmogorov.solovayCtx

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCtxFun := Kolmogorov.solovayCtxFun

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCtxFun_computable := Kolmogorov.solovayCtxFun_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCtxFun_primrec := Kolmogorov.solovayCtxFun_primrec

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayCtx_computable := Kolmogorov.solovayCtx_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayFst := Kolmogorov.solovayFst

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayFst_computable := Kolmogorov.solovayFst_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayFst_primrec := Kolmogorov.solovayFst_primrec

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayKN := Kolmogorov.solovayKN

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayKN_computable := Kolmogorov.solovayKN_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayMap := Kolmogorov.solovayMap

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayMap_isDecompressor := Kolmogorov.solovayMap_isDecompressor

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayN := Kolmogorov.solovayN

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayN_computable := Kolmogorov.solovayN_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayOfOpt_partrec := Kolmogorov.solovayOfOpt_partrec

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayOut := Kolmogorov.solovayOut

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayOutStr := Kolmogorov.solovayOutStr

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayOutStr_computable := Kolmogorov.solovayOutStr_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayOut_computable := Kolmogorov.solovayOut_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayPairMap := Kolmogorov.solovayPairMap

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayPairMap_computable := Kolmogorov.solovayPairMap_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayPairMap_primrec := Kolmogorov.solovayPairMap_primrec

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayRfind_partrec := Kolmogorov.solovayRfind_partrec

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovaySnd := Kolmogorov.solovaySnd

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovaySnd_computable := Kolmogorov.solovaySnd_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovaySnd_primrec := Kolmogorov.solovaySnd_primrec

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayVal := Kolmogorov.solovayVal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovayVal_computable := Kolmogorov.solovayVal_computable

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovay_plain_eq_prefix_sub_prefix_prefix :=
  Kolmogorov.solovay_plain_eq_prefix_sub_prefix_prefix

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovay_plain_le_prefix_sub_prefix_prefix :=
  Kolmogorov.solovay_plain_le_prefix_sub_prefix_prefix

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.solovay_prefix_plain_eq_add_condK_add :=
  Kolmogorov.solovay_prefix_plain_eq_add_condK_add

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.theorem73_solovay := Kolmogorov.solovay_plain_eq_prefix_sub_prefix_prefix

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.SUV.Ch04.theorem74_solovay_inverse :=
  Kolmogorov.solovay_prefix_plain_eq_add_condK_add

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.allocationSubset_getAlloc_mono_time := Kolmogorov.allocationSubset_mono_time

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.cantorCylinder_nil_univ := Kolmogorov.cantorCylinder_nil

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.cantorCylinder_split := Kolmogorov.cantorCylinder_eq_union_children

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.card_levelFinset_eq_two_pow := Kolmogorov.card_levelFinset

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.comparable_of_prefix_same := Kolmogorov.isPrefix_or_isPrefix_of_isPrefix

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.computable_natSize := Kolmogorov.computable_nat_size

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.computable₂_grayCallDepth := Kolmogorov.computable_grayCallDepth

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.computable₂_ratLe := Kolmogorov.computable_ratLe

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.disjoint_cantorCylinder_children := Kolmogorov.cantorCylinder_children_disjoint

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.dyadicValue_finsetSum := Kolmogorov.dyadicValue_sum_range_dim

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.dyadicValue_natCast_mul := Kolmogorov.dyadicValue_nat_mul

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.dyadicValue_ofNat_two_mul := Kolmogorov.dyadicValue_mul_two_num

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.dyadicValue_toReal := Kolmogorov.toReal_dyadicValue

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.exists_capped_scaling_semimeasure := Kolmogorov.exists_cappedScaling

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.exists_computable_summable_condK_criterion :=
  Kolmogorov.exists_computable_summable_condK_criterion'

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.exists_const_KPNat_apriori_equiv := Kolmogorov.exists_const_KPNat_aprioriNat_equiv

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.exists_const_cantorMass_le_complexityWeight_KMOf :=
  Kolmogorov.exists_const_cantorMass_mul_le_complexityWeight_KMOf

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.exists_const_condCantorMass_le_complexityWeight_condKMOf :=
  Kolmogorov.exists_const_condCantorMass_mul_le_complexityWeight_condKMOf

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.exists_history_playClientFamily := Kolmogorov.playClientFamily_eq_strategy_apply

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.exists_kaSublevel_streamLowerGraph := Kolmogorov.exists_kaSublevel_addressRelation

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.exists_not_isMartinLofRandom_forall_isComputableMeasure :=
  Kolmogorov.exists_not_isMartinLofRandom_forall_isComputableMeasure_diag

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.gacsDayNode_prefix := Kolmogorov.gacsDayNodePrefix

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.getReq_le_grayTailSonBase_of_mem :=
  Kolmogorov.getReq_le_grayTailSonBase_of_mem_global

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargeMass_nonneg := Kolmogorov.grayChargedChargeMass_nonneg

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedFinalReplayV2_of_final := Kolmogorov.grayChargedFinalReplayV2OfFinal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedFinalReplay_of_final := Kolmogorov.grayChargedFinalReplayOfFinal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedReplayV2_terminal_round_fine :=
  Kolmogorov.grayChargedReplayV2_terminal_round_adv

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedReserveCylinder_disjoint_of_ne_of_length :=
  Kolmogorov.grayChargedReserveCylinder_disjoint

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedSourceFrozenLayout := Kolmogorov.grayCharged_source_frozen_layout

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedSourceFrozenLayoutV2 := Kolmogorov.grayCharged_source_frozen_layout_v2

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedSparePairs_spare := Kolmogorov.grayChargedSparePairs_first_ge

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedSpendPairs_spare := Kolmogorov.grayChargedSpendPairs_first_ge

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedStepV2_no_return_to_advantage :=
  Kolmogorov.grayChargedStepV2_no_return_to_advantage'

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayChargedV2_prefixComparable_of_common_extension :=
  Kolmogorov.prefixComparable_of_common_extension

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayCharged_comparable_of_prefix := Kolmogorov.prefixComparable_of_common_extension

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayCharged_mem_finRange_drop := Kolmogorov.finRange_drop_val_ge

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayCharged_sum_ge_of_forall_zero_or_ge := Kolmogorov.sum_ge_of_forall_zero_or_ge

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayEndgame_a := Kolmogorov.grayEndgameA

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTailFrozenSonBase_append := Kolmogorov.grayTailFrozenSonBase_append_global

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTailGlobalStoppedWidth := Kolmogorov.grayTail_global_stopped_width

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTailNextSlots_source := Kolmogorov.grayTailNextSlots_used

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTailSlotEntries_selected_progress :=
  Kolmogorov.grayTailSlotEntries_selected_progress_global

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTailSlots_source := Kolmogorov.grayTailSlots_used

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTailSonBase_append := Kolmogorov.grayTailSonBase_append_globalEntries

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTailSonBase_eq_zero_of_no_entry :=
  Kolmogorov.grayTailSonBase_eq_zero_of_no_match

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTailSonBase_nonneg := Kolmogorov.grayTailSonBase_nonneg_global

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTail_done_of_roundCount_stateAt :=
  Kolmogorov.grayTail_done_of_roundCount_stateAt_core

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTail_prefixComparable_of_prefix :=
  Kolmogorov.prefixComparable_of_common_extension

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.grayTail_slots_eq_nil_of_roundCount_stateAt :=
  Kolmogorov.grayTail_slots_eq_nil_of_roundCount_stateAt_global

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.halfAmplification_pos' := Kolmogorov.halfAmplification_pos

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.inv_two_pow_le_inv_two_pow := Kolmogorov.inv_two_pow_antitone

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.inv_two_pow_le_of_le := Kolmogorov.inv_two_pow_antitone

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.isMartinLofRandom_of_boundedPrefixDeficiency :=
  Kolmogorov.isMartinLofRandom_of_boundedPrefixDeficiency_core

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.isMartinLofRandom_uniform_of_forall_computable_summable_le_plainK :=
  Kolmogorov.isMartinLofRandom_uniform_of_forall_computable_summable_le_plainK'

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.levelList_length := Kolmogorov.length_levelList

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.list_take_ofFn_family := Kolmogorov.list_take_ofFn

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.mem_keys_of_mem_getAlloc := Kolmogorov.grayLookup_mem_fst

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.natBits_length_le_logb_two_add_one := Kolmogorov.natBits_length_le_logb_add_one

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.natListSum_primrec := Kolmogorov.primrec_listSum

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.natSize_eq_natSize_div_two_succ := Kolmogorov.nat_size_div_two

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.newGrayCellsList_coarsen := Kolmogorov.grayChargedV2_newGrayCell_coarsen

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.ofReal_real_inv_two_pow := Kolmogorov.ofReal_inv_two_pow

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.ofReal_two_inv_pow := Kolmogorov.ofReal_inv_two_pow

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.omegaReal_isMartinLofRandomReal := Kolmogorov.isMartinLofRandomReal_omegaReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.pinnedEndgame_a := Kolmogorov.pinnedEndgameA

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.pinnedEndgame_alpha := Kolmogorov.pinnedEndgameAlpha

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.pinnedEndgame_b := Kolmogorov.pinnedEndgameB

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.pinnedEndgame_e := Kolmogorov.pinnedEndgameE

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.pinnedEndgame_h := Kolmogorov.pinnedEndgameH

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.pinnedEndgame_k := Kolmogorov.pinnedEndgameK

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.plainK_prefix_le_length_sub_logb_infinitely_often' :=
  Kolmogorov.plainK_prefix_le_length_sub_logb_infinitely_often

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.prefixComparable_of_common_extension_prefix :=
  Kolmogorov.prefixComparable_of_common_extension

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.prefix_take_eq := Kolmogorov.isPrefix_of_isPrefix_take

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.problem_140_KMOf_le_KA_add_log_KA := Kolmogorov.exists_const_KMOf_le_KA_add_log

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.problem_140_KMOf_le_KA_add_log_KA' := Kolmogorov.exists_const_KMOf_le_KA_add_log

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.problem_143_isMartinLofRandom_of_decidable_lengths :=
  Kolmogorov.isMartinLofRandom_of_boundedPrefixDeficiency_mem

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.problem_144_le_KPPair_of_isMartinLofRandom :=
  Kolmogorov.problem_144_le_KPPair_of_isMartinLofRandom'

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.problem_147_maximal_prefixSupRatio :=
  Kolmogorov.problem_147_maximal_prefixSupRatio'

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.serverMoveCoherent_of_le_branch := Kolmogorov.serverMoveCoherent_mono_branching

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.serverPlayLegal_of_le_branch := Kolmogorov.serverPlayLegal_mono_branching

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.stageExistence_isRE := Kolmogorov.stageExistenceIsRE

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_100_omega_binary_isMartinLofRandom :=
  Kolmogorov.omega_binary_isMartinLofRandom

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_100_omega_isMartinLofRandomReal :=
  Kolmogorov.isMartinLofRandomReal_omegaReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_101_isLowerSemicomputableReal_sub_of_solovayDominates :=
  Kolmogorov.isLowerSemicomputableReal_sub_of_solovayDominates

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_101_solovayDominates_iff :=
  Kolmogorov.solovayDominates_iff_isLowerSemicomputableReal_sub

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_101_solovayDominates_of_isLowerSemicomputableReal_sub :=
  Kolmogorov.solovayDominates_of_isLowerSemicomputableReal_sub

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_102_exists_isSolovayComplete := Kolmogorov.exists_isSolovayComplete

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_103_isOmegaNumber_of_isSolovayComplete :=
  Kolmogorov.isOmegaNumber_of_isSolovayComplete

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_103_isSolovayComplete_iff_isOmegaNumber :=
  Kolmogorov.isSolovayComplete_iff_isOmegaNumber

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_103_isSolovayComplete_of_isOmegaNumber :=
  Kolmogorov.isSolovayComplete_of_isOmegaNumber

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_104_hasComputableWinningStrategy_iff :=
  Kolmogorov.hasComputableWinningStrategy_iff_not_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_104_hasComputableWinningStrategy_of_not_isMartinLofRandomReal :=
  Kolmogorov.hasComputableWinningStrategy_of_not_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias
  Kolmogorov.theorem_104_hasComputableWinningStrategy_of_not_isMartinLofRandomReal_of_monotone :=
  Kolmogorov.hasComputableWinningStrategy_of_not_isMartinLofRandomReal_of_monotone

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_104_not_isMartinLofRandomReal_of_hasComputableWinningStrategy :=
  Kolmogorov.not_isMartinLofRandomReal_of_hasComputableWinningStrategy

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_105_exists_of_not_isMartinLofRandomReal :=
  Kolmogorov.exists_uniform_slack_family_of_not_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_105_exists_of_not_isMartinLofRandomReal_of_monotone :=
  Kolmogorov.exists_uniform_slack_family_of_not_isMartinLofRandomReal_of_monotone

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_105_not_isMartinLofRandomReal_of_exists :=
  Kolmogorov.not_isMartinLofRandomReal_of_exists_uniform_slack_family

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_106_exists_of_not_isMartinLofRandomReal :=
  Kolmogorov.exists_summable_slack_of_not_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_106_exists_of_not_isMartinLofRandomReal_of_monotone :=
  Kolmogorov.exists_summable_slack_of_not_isMartinLofRandomReal_of_monotone

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_106_not_isMartinLofRandomReal_of_exists :=
  Kolmogorov.not_isMartinLofRandomReal_of_exists_summable_slack

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_107_not_isMartinLofRandomReal_add :=
  Kolmogorov.not_isMartinLofRandomReal_add

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_108_not_isMartinLofRandomReal :=
  Kolmogorov.not_isMartinLofRandomReal_of_lscTailCover

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_108_not_isMartinLofRandomReal_of_monotone :=
  Kolmogorov.not_isMartinLofRandomReal_of_lscTailCover_of_monotone

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_109_exists_of_not_isMartinLofRandomReal :=
  Kolmogorov.exists_smallMassREFamily_of_not_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_109_not_isMartinLofRandomReal_iff :=
  Kolmogorov.not_isMartinLofRandomReal_iff_exists_smallMassREFamily

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_109_not_isMartinLofRandomReal_of_exists :=
  Kolmogorov.not_isMartinLofRandomReal_of_exists_smallMassREFamily

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_110_isMartinLofRandomReal_of_isSolovayComplete :=
  Kolmogorov.isMartinLofRandomReal_of_lowerSemicomputable_isSolovayComplete

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_110_isSolovayComplete_iff :=
  Kolmogorov.isSolovayComplete_iff_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_110_isSolovayComplete_of_isMartinLofRandomReal :=
  Kolmogorov.isSolovayComplete_of_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_111_isMartinLofRandomReal_iff_hasSolovayProperty :=
  Kolmogorov.isMartinLofRandomReal_iff_hasSolovayProperty

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_111_not_isMartinLofRandomReal_of_ratioTendstoZero :=
  Kolmogorov.not_isMartinLofRandomReal_of_ratioTendstoZero

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_111_ratioTendstoZero_of_not_isMartinLofRandomReal :=
  Kolmogorov.ratioTendstoZero_of_not_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_111_strengthened_lsc_terms :=
  Kolmogorov.not_isMartinLofRandomReal_iff_ratioTendstoZero_of_lsc_terms

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_112_group_of_pair := Kolmogorov.ratioTendstoZero_group_of_pair

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_112_grouping := Kolmogorov.ratioTendstoZero_group_iff_pair

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_112_pair_of_group := Kolmogorov.ratioTendstoZero_pair_of_group

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_113_isMartinLofRandomReal_of_tight :=
  Kolmogorov.isMartinLofRandomReal_of_tight

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_113_tight_iff_isMartinLofRandomReal :=
  Kolmogorov.tight_iff_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_113_tight_of_isMartinLofRandomReal :=
  Kolmogorov.tight_of_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_114_hasSolovayProperty_iff_modulus_ge :=
  Kolmogorov.hasSolovayProperty_iff_convergenceModulus_ge_busyBeaverPrefix

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_114_isMartinLofRandomReal_of_modulus_ge :=
  Kolmogorov.isMartinLofRandomReal_of_convergenceModulus_ge_busyBeaverPrefix

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_114_modulus_ge_of_isMartinLofRandomReal :=
  Kolmogorov.convergenceModulus_ge_busyBeaverPrefix_of_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_115_modulus_ge_BPprime :=
  Kolmogorov.convergenceModulus_ge_BPprime_of_isMartinLofRandomReal

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_116_busyBeaver_of_omegaPrefix := Kolmogorov.busyBeaver_of_omegaPrefix

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_116_omegaPrefix_of_busyBeaver := Kolmogorov.omegaPrefix_of_busyBeaver

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.theorem_62_upperBound_iff_tsum_ne_top :=
  Kolmogorov.KPNat_le_iff_tsum_two_pow_neg_ne_top

@[deprecated (since := "2026-09-08")]
alias Kolmogorov.universalStreamStage_pred := Kolmogorov.universalStreamStagePred
