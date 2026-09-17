import KolmogorovMathlib.CommonInformation.RegionLower.Part01
import KolmogorovMathlib.CommonInformation.RegionLower.Part02
import KolmogorovMathlib.CommonInformation.RegionEnvelopes
import KolmogorovMathlib.CommonInformation.OverlapExtraction

/-!
# Constructive lower-envelope witnesses for SUV Theorem 225

This module turns the three concrete shortest-description-prefix decoders into
exact `CommonInformationRegion` witnesses.  The finite five-way case cover is
proved in `RegionEnvelopes`; the eventual universal lower inclusion will combine
these leaves with exact minimizing programs and the conditional-value estimates.
-/
