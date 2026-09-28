import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Leaf2Source.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Leaf2Source.Part02
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Corner
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Leaf2Hereditary

/-!
# Leaf 2 (D4) — the source subfamily bound (S), per round

The hereditary source bound `(S)` `κ·(2·P_I − P) ≤ MS_I` is assembled from the
per-round subfamily inequalities.  This module proves the per-round piece: for a
frozen round `p` and a local subfamily `J ⊆ [slots.length]`,
`κ·(2·totalReqOnList J p.move − totalReq p.move) ≤ mass(roundLocalCharge.filter(·.1∈J))`.
It mirrors `grayChargedV2_rounds_request_le_mass` (the aggregate per round) with
`familyGrayChargeAtB.subfamily` in place of `.aggregate`.
-/
