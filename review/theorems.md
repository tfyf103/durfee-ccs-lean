# Numbered results and Lean entry points

The proof covers all 17 numbered results and the separately stated Canfield–Corteel–Savage conjecture. Import `DurfeeCCS.ReviewAll` to access the declarations below. Identifiers in the first column match the [manuscript coverage map](../paper-map.tsv) and the [final statement and axiom audit](step14/targets.tsv).

The main theorem applies to each integer $n\ge 1$. For $m=\lfloor\sqrt n\rfloor$, the Durfee polynomial has degree $m$. Its roots over $\mathbb C$ consist of zero and exactly $m-1$ distinct negative real roots, each of multiplicity one. The statement includes $m=1$, when zero is the only root.

| Manuscript ID | Result | Lean entry points |
| --- | --- | --- |
| C1.1 | Canfield–Corteel–Savage conjecture on real-rootedness | [`DurfeeCCS.ordinaryDurfee_allRootsReal`](../DurfeeCCS/Main.lean), [`DurfeeCCS.durfee_complex_roots_exact`](../DurfeeCCS/Main.lean) |
| R1.2 | Complete root list and simplicity of the roots | [`DurfeeCCS.durfee_simple_exact_negative_roots`](../DurfeeCCS/Main.lean), [`DurfeeCCS.durfee_negative_root_count`](../DurfeeCCS/Main.lean), [`DurfeeCCS.durfee_complex_roots_exact`](../DurfeeCCS/Main.lean), [`DurfeeCCS.durfee_factorization`](../DurfeeCCS/Main.lean), [`DurfeeCCS.durfee_factorization_one`](../DurfeeCCS/Main.lean), [`DurfeeCCS.Step11.durfeePolynomialReal_origin_simple`](../DurfeeCCS/Step11/RootData.lean) |
| R1.3 | Independent Bernoulli representation for the Durfee side of a uniform random partition, with mean and variance | [`DurfeeCCS.durfeeSide_bernoulli_mean_variance`](../DurfeeCCS/Step12/Probability.lean), [`DurfeeCCS.durfeeSide_moments_of_sqrt_eq_one`](../DurfeeCCS/Step12/Probability.lean) |
| R3.1 | Comparison near the origin and its error bound | [`DurfeeCCS.Step08.nearOrigin_approximation`](../DurfeeCCS/Step08/NearOriginApproximation.lean) |
| R3.2 | Alternating signs at phase samples near the origin | [`DurfeeCCS.Step08.nearOrigin_sign_at_kpi`](../DurfeeCCS/Step08/NearOriginApproximation.lean), [`DurfeeCCS.Step08.nearOrigin_sign_firstEight`](../DurfeeCCS/Step08/NearOriginApproximation.lean) |
| R3.3 | Integral decomposition, amplitude and phase bounds for the first saddle | [`DurfeeCCS.Step08.lemma33`](../DurfeeCCS/Step08/PhaseGapEndpoint.lean), [`DurfeeCCS.Step08.saddleG_sqrt_central_endpoint_limits`](../DurfeeCCS/Step08/PhaseGapEndpoint.lean) |
| R3.4 | First saddle remainder from the major-arc approximation | [`DurfeeCCS.Step08.lemma34_paper`](../DurfeeCCS/Step08/SaddleBesselApproximation.lean), [`DurfeeCCS.Step08.lemma34`](../DurfeeCCS/Step08/SaddleBesselApproximation.lean) |
| R3.5 | Relative error for the first saddle | [`DurfeeCCS.Step08.proposition35`](../DurfeeCCS/Step08/FirstSaddleProof.lean), [`DurfeeCCS.Step08.firstSaddle_sign`](../DurfeeCCS/Step08/FirstSaddleProof.lean), [`DurfeeCCS.Step08.firstSaddle_sign_at_phase`](../DurfeeCCS/Step08/FirstSaddlePhaseSign.lean) |
| R3.6 | Two-sided integral representation and saddle parameter bounds in the middle range | [`DurfeeCCS.Step09.lemma36`](../DurfeeCCS/Step09/MidRepresentation.lean) |
| R3.7 | Explicit error bound for the model integral $J$ in the middle range | [`DurfeeCCS.Step09.lemma37`](../DurfeeCCS/Step09/MidModelJ.lean) |
| R3.8 | Major-arc error in the middle range | [`DurfeeCCS.Step09.lemma38`](../DurfeeCCS/Step09/MidMajorProof.lean) |
| R3.9 | Small-angle error in the middle range | [`DurfeeCCS.Step09.lemma39`](../DurfeeCCS/Step09/MidMinorProof.lean) |
| R3.10 | Error for the remaining angles in the middle range | [`DurfeeCCS.Step09.lemma310`](../DurfeeCCS/Step09/MidOtherProof.lean) |
| R3.11 | Relative error in the middle range | [`DurfeeCCS.Step09.proposition311`](../DurfeeCCS/Step09/MidProof.lean), [`DurfeeCCS.Step09.midSaddle_sign_at_phase`](../DurfeeCCS/Step09/MidProof.lean), [`DurfeeCCS.Step09.saddle_ranges_at_one`](../DurfeeCCS/Step09/MidRangeOverlap.lean) |
| R4.1 | Outer-range phase and relative error | [`DurfeeCCS.Step10.proposition41_at_radius`](../DurfeeCCS/Step10/OuterComplete.lean), [`DurfeeCCS.Step10.proposition41`](../DurfeeCCS/Step10/OuterComplete.lean), [`DurfeeCCS.Step10.OuterBesselApproximation`](../DurfeeCCS/Step10/OuterSigns.lean), [`DurfeeCCS.Step10.outerBesselApproximation_of_errors`](../DurfeeCCS/Step10/OuterApproximation.lean), [`DurfeeCCS.Step10.outerTripleMass_bound`](../DurfeeCCS/Step10/OuterApproximation.lean), [`DurfeeCCS.Step10.outerBesselApproximation_at_radius`](../DurfeeCCS/Step10/OuterResults.lean) |
| R4.2 | Two-colour partition coefficient bounds at three thresholds | [`DurfeeCCS.Step10.lemma42`](../DurfeeCCS/Step10/OuterCoeff.lean) |
| R4.3 | Dominance of the designated term in the outer range | [`DurfeeCCS.Step10.lemma43`](../DurfeeCCS/Step10/OuterFar.lean) |
| R4.4 | Root counts in outer-range intervals | [`DurfeeCCS.Step10.corollary44`](../DurfeeCCS/Step10/OuterComplete.lean), [`DurfeeCCS.Step10.corollary44_of_proposition41`](../DurfeeCCS/Step10/OuterResults.lean), [`DurfeeCCS.Step10.outerFirst_eq_intCeil`](../DurfeeCCS/Step10/OuterSamples.lean), [`DurfeeCCS.Step10.outerFirst_sample`](../DurfeeCCS/Step10/OuterSamples.lean), [`DurfeeCCS.Step10.outerRoots_of_alternating`](../DurfeeCCS/Step10/OuterRoots.lean) |

## Equation (14)

The exact two-colour partition identity holds for each positive integer $n$. [`DurfeeCCS.Step14.twoColourPartitionCount_eq_rademacherRHS`](../DurfeeCCS/Step14/RademacherIdentity.lean) proves equality with the normalized Rademacher series. The series is absolutely convergent by `DurfeeCCS.Step06.summable_norm_twoColourRademacherTerm`, and `DurfeeCCS.Step06.twoColourRademacherRHS_eq_IJT` matches its normalization to the manuscript formula. See `E14` in the [final statement and axiom audit](step14/targets.tsv) for the full list of declarations.
