# Manuscript correspondence — v1.2.0

This map accompanies the weighted Pilz paper of 23 October 2026. It retains
all 123 labels of the frozen original (108 mathematical and 15 navigation)
and adds four mathematical labels. The complete manuscript inventory is
127 labels: 112 mathematical and 15 navigation labels.

The root import closure has 325 local modules: 278 `WeightedPilz` modules,
46 `Pilz` modules, and `WeightedPilz.lean`. The 319 library proof modules
from v1.1.0 are unchanged. Four new consequence modules are added, the
existing `Pilz.Parity` module is newly imported, and the root imports are
extended. All 58 previous public-type examples are retained; 11 additional
examples bring the final acceptance file to 69 explicit public-type checks.

The original independent clean build and both acceptance suites passed for
v1.0.0. The v1.1.0 review revision preserved its proof library and strengthened
the audit to select every declaration by originating module, including
private declarations and transitive dependencies. The release's
`verification/VERIFICATION.md` and `verification/results.json` record the
v1.2.0 build, acceptance runs, and actual audit counts. The accepted axiom
set remains `propext`, `Classical.choice`, and `Quot.sound`.

The v1.1.0 review revision made `n ≥ 1` explicit in the rank theorem, `e > 0`
in the recalled endpoint inequality, and nonzero weights in the prime
equality corollary. These hypotheses were already present in Lean. Its
cancellation and residue-correction examples remain illustrations. The
v1.2.0 additions are listed separately below. The frozen original remains
preserved separately; `paper/main.tex` and `paper/main.pdf` contain the
current revised manuscript.

This is a correspondence of statements and dependencies, not a line-by-line
transcription. Alternative proved arguments for intermediate results are
identified in the coverage column. Conditional infrastructure is listed
alongside the unconditional theorems that discharge its premises.

| Frozen claim / dependency | Lean implementation | Coverage |
|---|---|---|
| Valuation encoding; exact weighted interval support | `Basic.lean`: `monomialOf_mul`, `monomialOf_injective`, `support_interval`, `weight_interval`, `interval_ne_zero` | Checked, arbitrary coefficients with the stated nonzero hypotheses |
| Minimum over nonzero multipliers | `Distance.lean`: `exists_weight_eq_distance`, `distance_le_weight_mul`, `le_distance_iff` | Checked |
| Scalar monomial sharpness | `Basic.lean` singleton and scalar-monomial lemmas | Checked; does not prove the matching lower bound |
| Elementary support cancellation and translations | `Support.lean` | Checked |
| Coefficient extension (Section 2) | `CoefficientExtension.lean`: `exists_nonzero_multiple_descent_map`, `distance_map`, `exists_supported_multiple_iff` | Checked support containment and field descent |
| Monomial normalization (Section 2) | `Normalize.lean`: `exists_normalization` | Checked |
| Deletion-minimal counterexamples | `Minimal.lean`: `exists_deletionMinimal` | Checked |
| `eq:width-additivity` | `Width.lean`: `widthOf_mul`, `totalWidth_mul`; `DirectionalWidth.lean`: `integerWidth_mul`, `directionalWidth_mul` | Coordinate, total, arbitrary integer and general additive directional widths checked |
| `lem:endpoints` | `Endpoints.lean`; `AffineDimension.lean`: `affineDimension_add_one_le_weight_mul`, `affineDimension_add_one_le_distance`, Laurent-output bound | Coordinate endpoints, pure-power bounds and full rational affine-dimension statement checked, including arbitrary Laurent multipliers |
| `lem:exponent-dilation` | `Dilation.lean`: `distance_dilate` | Checked, with explicit residue decomposition |
| `lem:directed-cut` | `DirectedCut.lean`: `directed_cut_interval_lower`, `deletionMinimal_product_lower_bound`, `deletionMinimal_prime_bound` | Full quantitative inequality and strict prime bound checked |
| `lem:two-variable-shift` | `SupportShift.lean`: `two_variable_shift`, `shiftedSupport_sum_lt` | Finite-coordinate binomial shift, rational-function membership, and strict support potential checked, including full polynomial profile assembly |
| `thm:compression` | `ScalarCompression.lean`: `Compression.scalar_support_compression`, `scalar_support_compression_multiplier` | Full theorem checked over the original arbitrary field, preserving divisibility, support bound, base exponents and widths; explicit finite scalar expansion |
| `lem:powergap` | `PowerGap.lean`, `PowerGapPositive.lean`: `power_gap` | Checked over every field using exponential characteristic; no perfectness assumption |
| `thm:completion` | `Completion.lean`, `SharpCompletion.lean`, `IteratedCompletion.lean`, `FreshCompletion.lean`, `FreshRigidity.lean` | Full bound and strict-threshold rigidity checked in both explicit nested-`Option` and same-coordinate `FreshData` models |
| `lem:frobenius-extraction` | `Frobenius.lean`: `frobenius_extraction`, `frobenius_extraction_width` | Checked, including simultaneous input/output support containment and width bounds, without perfectness |
| `lem:width-descent` | `WidthDescent.lean`, `WidthZero.lean`, `FreshResidueWidth.lean`, `CompressedMinimum.lean` | Minimum choice, strict Frobenius decrease, zero-width geometry, actual correction-width bounds and positive compressed selection checked |
| `thm:residue-descent`, `cor:finite-residue` | `FullResidueDescent.lean`: `FreshData.residue_capacities`; `FiniteResidueFormula.lean`: `finite_residue_formula`; `ResidueCofactor.lean` | Full witness, scalar quotient, precise/uniform correction capacities, protected classes and constant-row budget checked; attained finite-residue formula and existence of a bounded-degree cofactor checked under the stated capacity bounds |
| `eq:digitcost`; fresh-variable degree costs | `FreshCosts.lean`: `weight_freshSum_pow_digits`, `weight_freshSum_pow_charZero`, `weight_freshSum_pow_lt_char` | Exact characteristic-zero and below-characteristic row costs, and the full base-p digit product formula checked |
| Minimal degree-cost equality cases; short fresh-row tests | `FreshCostEquality.lean`, `ShortFreshTest.lean`, `ShortFreshFive.lean` | Distinguished-power equality cases and both complete short-row criteria checked and audited, including the two-fresh-variable budget-five case |
| `thm:initial` and its named auxiliary claims | `InitialAll.lean`: `intervalBound_initial`, `distance_interval_initial`; exact cases assembled from `InitialNine.lean`, `InitialTenFinal.lean`, `InitialTwelve.lean`, `InitialFourteen.lean`, `InitialFifteen.lean`, `InitialSixteen.lean`, `InitialLateFinal.lean` | Full arbitrary-weight theorem through 24 checked, without additional core/power hypotheses. All exact auxiliary rows below are supplied by its checked construction |
| `thm:finite`, `prop:fin-odd` | `MiddleOdd.lean`: `intervalBound_middle_odd`; `BinaryMiddle.lean`: `intervalBound_middle_charTwo`; `MiddleTheorem.lean`: `intervalBound_middle` | Full odd-characteristic and characteristic-two theorems checked for 25–66, without conditional arithmetic/core premises. Combined all-field wrapper fully checked |
| `lem:fin-affine` | `MiddleAffineAll.lean`: `middle_affine_lower_all` | Full affine bound checked for every 25–66, arbitrary weights, arbitrary field of characteristic other than two; all four exceptional indices included |
| `lem:finite-binomial-squares` | `FiniteBinomialSquares.lean`: `finite_binomial_square_bounds` | Exact bounds 16/44/44/20 checked and audited at 26/27/28/40; arbitrary binomial variables and nonzero weights, characteristic other than two |
| `eq:fin-cubic-bound`; higher-degree exceptional core powers | `ExceptionalCorePowers.lean`: `exceptional_core_cube_weight`, `exceptional_core_quartic_weight`, `exceptional_core_cube_weight_forty` | Actual weighted cubic/quartic support bounds 44/15/56 checked when 2 and 3 are nonzero, using exact unordered-product certificates. These establish the stated inequalities by an alternative to the manuscript's projection proof |
| `eq:fin-higher-residue`, large residue and degree budgets | `MiddleResidueCapacities.lean`, `Arithmetic/AggregateBudgets.lean`, `Arithmetic/LargeResidueBudgets.lean` | All-degree middle capacities for primes at least five, cube capacities including 27/28 exceptions, and all-degree large-range estimates checked |
| Exact squarefree parity decomposition | `ParityDecomposition.lean`, `ParityCore.lean` | Actual inherited weights, unchanged-coefficient dilation, exact square-root class sizes, and occupied classes for interval/core checked |
| `eq:fin-block-budgets` | `Arithmetic/MiddleBudgets.lean`, `Arithmetic/UniqueProducts.lean`, `Arithmetic/MiddleUniqueBudgets.lean` | All seven persistent unique-product counts, numerical budget rows and block coverage checked |
| `eq:large-endpoint-budgets`; 229–1799 bounds | `Arithmetic/EndpointBudgets.lean`; `Arithmetic/EndpointTables.lean`: `endpointTable_correct`, `endpointTable_covers`, `endpointTable_lower_bounds`, `dimensionTable_correct`, `dimensionTable_covers`, `dimensionTable_lower_bounds` | Both exact pointwise inequalities and all literal entries/coverage of the 14-row and 13-row printed tables checked |
| `arith:lem:first-prime-budget-block`, `arith:prop:written-low-range` | `Arithmetic/Imported.lean`; `Arithmetic/FirstPrimeTable.lean`: `firstPrimeTable_rows`, `firstPrimeTable_coverage`, `firstPrimeTable_bounds` | Exact 67–1023 inequalities and all 13 printed first-prime-budget rows, values and coverage checked and audited |
| `arith:lem:elementary-chebyshev`, `arith:lem:no-core-fresh-budget` | `Arithmetic/Imported.lean` | Checked unbounded analytic estimates imported and audited |
| `arith:lem:no-core-reciprocals`, finite 7/11/13 profiles | `Arithmetic/Imported.lean` | Checked exact arithmetic imported and audited |
| `arith:lem:no-core-large-primes` numerical part | `Arithmetic/Imported.lean`: generic rough-count bound | Checked independently of any polynomial field theorem |
| Other localized numerical bands | `Arithmetic/LocalizedNumerics.lean` | Checked and transitively audited |
| `arith:eq:prime-rank-decomposition` | `Components.lean`: `weight_interval_mul_eq_sum_rough_components` | Checked exact decomposition with inherited weights `c (b*a)` |
| `arith:lem:active-prime-profile`, `arith:eq:four-component-budget`, `arith:eq:eight-component-budget` | `ComponentBounds.lean`: `component_profile_one`, `component_profile_before`, `component_profile_after`, `component_budget_four_paper`, `component_budget_eight` | Checked over arbitrary fields |
| `arith:prop:small-prime-profile-replacement` | `LocalizedSmallSupport.lean`: `localized_small_support` | Checked all support primes through 13 |
| `arith:thm:localized-expansion` | `LocalizedSupport.lean`: `localized_expansion` | Checked full weighted theorem for all `n ≥ 67` and its exact normalization/largest-prime/directed-cut hypotheses |
| `thm:large-weighted` | `LargeTheorem.lean`: `intervalBound_ge229`, `intervalBound_large_of_initial`; `InitialAll.lean`: `intervalBound_initial`; `FieldTheorem.lean`: `intervalBound_all` | Unconditional all-field theorem for every n≥67 checked, using the proved initial intervals and independent finite and unbounded arithmetic estimates |
| `eq:large-base` | `LargeBase.lean`, `LargeBaseCore.lean`: `large_base_unrestricted` | Full numerical core/base bound checked for every nonzero multiplier and every `n ≥ 67`, with arbitrary nonzero weights |
| `thm:field` | `FieldTheorem.lean`: `intervalBound_all`, `weighted_interval`, `weighted_interval_distance` | Full theorem and sharpness checked for every n over every field, arbitrary nonzero weights and arbitrary nonzero polynomial multipliers |
| Laurent form of `thm:field` | `FieldTheorem.lean`: `weighted_interval_laurent`, `weighted_interval_laurent_distance`; `Laurent.lean` clearing and minimum-distance identities | Full Laurent theorem and sharpness checked, including arbitrary integer exponents |
| `eq:convolution` | `Convolution.lean`: `interval_convolution_apply`, `intervalBound_iff_convolution_bound`; `FieldTheorem.lean`: `weighted_convolution` | Exact divisor-sum formula, equivalence, and unconditional bound checked |
| Original symmetric difference over F₂ | `Binary.lean`; `FieldTheorem.lean`: `weighted_symmetric_difference` | Exact odd-membership model and unconditional symmetric-difference bound checked |
| `prop:universal-inverse` | `UniversalInverse.lean` residue-field criterion and module recovery; `FinalConsequences.lean`: `intervalMatrix_units_erasure_inverse`; `UniversalWeightRing.lean` and `UniversalWeights.lean`: `universal_erasure_inverse`, `universal_erasure_inverse_specializes` | Exact universal Laurent ring over ℤ, evaluation at arbitrary units, existence of an inverse, and specialization of that same inverse all checked |
| `thm:module`, `cor:commuting-actions` | `FinalConsequences.lean`: `intervalEndBound_scalar_iff_injective`, `intervalEndBound_commuting_group_iff`; `ModuleActions.lean`: `intervalEndAction_sharp` | Unconditional exact injectivity criteria checked; singleton sharpness checked |
| `thm:monoid`, `thm:monoid-main` | `FinalConsequences.lean`: `intervalEndBound_commuting_monoid_iff`; `MonoidActions.lean` additive-unit reduction and examples | Unconditional exact reflection-of-zero criterion checked; it is distinct from injectivity for monoids |
| Semimodule consequence following the monoid theorem | `SemimoduleConsequences.lean`: `intervalEndBound_semimodule_iff_reflectsZero`, `intervalEndBound_semimodule_sharp` | Exact criterion over arbitrary commutative semirings and sharpness for nontrivial semimodules checked |
| Necessity of commutativity; explicit rational-plane example | `NoncommutingCounterexample.lean`: `noncommutingWeights_bijective`, `noncommutingWeights_do_not_commute`, `noncommuting_interval_counterexample`, `noncommuting_interval_bound_fails` | Four bijective weights and a nonzero input with exactly three outputs at 1, 9, 16 checked |
| `thm:coefficient-rank` | `CoefficientRank.lean`: `coefficientRank_projection_bound`; `VectorConvolution.lean`: `coefficientSpan_vectorInterval`; `FinalConsequences.lean`: `vectorInterval_rank_bound` | Unconditional rank bound checked, with equality of input/output coefficient spans and no finite-dimensional ambient-space assumption |
| `cor:prime-rigidity`, `cor:vector-prime-rigidity` | `FinalConsequences.lean`: `prime_index_multiplier_rigidity`, `prime_interval_laurent_rigidity`, `vector_prime_laurent_rigidity`, `vector_prime_polynomial_output_rigidity` | Unconditional scalar/vector classification of output and cofactor checked, including characteristic zero and the polynomial-output nonnegative-exponent conclusion |


## Four added manuscript claims

The following rows give the exact new interfaces and their hypotheses.
The errors-and-erasures result is a uniqueness guarantee, not a decoder.

| Added label | Exact implementation | Coverage |
|---|---|---|
| `rem:scope` | `ScopeLimits.lean`: `weight_interval_eq_nonzero_card`, `intervalBound_iff_nonzeroWeights`, `noninterval_binary_product`, `noninterval_binary_counterexample` | Over every field, `IntervalBound n c ↔ NonzeroWeights n c`, including `n = 0`. Over `ZMod 2`, `P = 1 + X 0 + X 0 ^ 2` has weight three, `H = 1 + X 0` is nonzero, and `P * H = 1 + X 0 ^ 3` has weight two. Thus support cardinality alone cannot replace the interval hypothesis |
| `rem:errors-erasures` | `ErrorCorrection.lean`: `CompatibleWithErrors`, `eq_of_support_distance_of_errors_erasures`, `intervalEndAction_errors_erasures_unique`, `weighted_convolution_errors_erasures_unique`, `module_interval_errors_erasures_unique`, `commuting_interval_errors_erasures_unique` | Two finitely supported inputs compatible with the same received values are equal when `2 * t + E.card < n`. Field weights are nonzero; scalar actions on a module over a commutative ring are injective; the additive-group version requires commuting injective weights. Received values may have infinite support, and no input-support bound or efficient-decoding claim is imposed |
| `cor:binary-prime-equality` | `BinaryPrimeEquality.lean`: `binary_prime_equality_iff`, `binary_prime_equality_output` | For `ℓ.Prime`, `3 ≤ ℓ`, and a nonempty `A : Finset ℕ` with every member positive, `(intervalSymmetricDifference ℓ A).card = ℓ` iff there exist natural `b, e` with `0 < b` and `Pilz.polynomialOf A = monomialOf b * interval ℓ (fun _ => (1 : ZMod 2)) ^ (2 ^ e - 1)`. For those same witnesses the output is `(Finset.Icc 1 ℓ).image (fun a => b * a ^ (2 ^ e))`; this output identity holds for any interval length when the input has the stated form |
| `cor:binary-parity` | `BinaryParity.lean`: `symmetric_difference_card_mod_two`, `symmetric_difference_odd_even_bound`, `symmetric_difference_one_two_card`, `symmetric_difference_odd_even_sharpness`; existing dependency `Pilz.Parity` | For every `n : ℕ` and positive finite input, output cardinality modulo two equals `(n * A.card) % 2`. If `n` is odd and `A` is nonempty with even cardinality, the bound is `n + 1`. The exact `{1, 2}` output size is `2 * n - 2 * (n / 2)`, giving sharpness for every odd `n`, including `n = 1` |

The parity identity was already used by Holdridge–Pach; the new bound here
combines it with the completed interval theorem. The project's uniform
`4/3` density theorem was already proved in the separate `Density`
development; it proves the strengthening proposed in Holdridge–Pach,
Remark 1.9. It is not an additional
claim of this weighted release. The group-algebra research note is outside
the weighted manuscript certificate and is not included in this proof map.

Additional checked infrastructure: `Rescale.lean` proves exact support and
minimum-distance invariance under arbitrary unit variable scalings.
`FreshRows.lean` proves the full base-only identity `eq:intro-base` over every
field, using explicit disjoint fresh rows. `Arithmetic/Counts.lean` proves its
finite square-root evaluator equals `Nat.sqrt`; public counts retain the
manuscript's exact natural-number conventions.

All 123 original labels are accounted for by the retained correspondence,
including 108 mathematical labels and 15 navigation labels. Together with
the four new mathematical rows above, the complete inventory is 127 labels.
Every mapped source module and local declaration occurs in the root's
325-module local import closure. The original independent build compiled
all then-local modules from source, reusing only pinned third-party
dependency caches, and reran both acceptance suites; current validation is
recorded separately in the release verification record.

## Detailed retained-label inventory

The following rows name the displayed equations and auxiliary
claims explicitly. `Pilz.*` entries in the arithmetic rows are proved,
field-independent numerical infrastructure imported by the weighted library;
they are not uses of the earlier coefficient-specific interval theorem.
Every declaration marked checked has passed its module build.

| Frozen label | Exact implementation | Coverage |
|---|---|---|
| `eq:descent-exponent-bounds` | `FreshResidueWidth.lean`: `aggregate_coefficient_base_bounds`, `aggregate_correction_width`, `aggregate_correction_residue_cost`; `WidthDescent.lean`: `correction_width_bound_of_exponent_bounds` | Checked coordinate exponent and correction width bounds |
| `eq:residue-capacity`, `eq:residue-budget` | `FullResidueDescent.lean`: `FreshData.residue_capacities` and its `ResidueCapacityWitness`; `ResidueCofactor.lean`: `bounded_cofactor_of_residue_relation`, `exists_minimum_bounded_aggregate_cofactor` | Checked actual counterexample witness and capacity/budget conclusions |
| `eq:binary-residue-form`, `eq:binary-u-budget` | `BinaryResidueFormula.lean`: `FreshData.binary_finite_residue_formula`; `BinaryResidueComparison.lean`: `ResidueCapacityWitness.binary_remainder_eq`, `positiveResidueCost_two`; witness constant-row budget | Checked exact characteristic-two relation and term budget |
| `eq:large-affine` | `LargeAffine.lean`: `large_affine`; `LargeAffineFinite.lean`: `large_affine_all`; `InitialAll.lean`: `intervalBound_initial` | Checked for every n≥67; the explicit small-interval premises in the general reduction are discharged by the checked initial theorem |
| `eq:large-endpoint-square` | `CoreBudgets.lean`: `intervalCore_endpoint_distance`, `intervalCore_square_weight`; `InitialAll.lean`: `intervalBound_initial` | Exact endpoint sum and square lower bound checked; required smaller interval bounds are proved by the initial theorem |
| `lem:initial-quadratic` | `QuadraticNonconstant.lean`: `quadratic_polynomial_multiple_three_rows_of_nonconstant`, using `QuadraticObstruction.lean`, `RationalNonconstant.lean`, `BivariateQuadraticRatio.lean` | Checked literal nonconstant B²/(AD) premise, encoded as B²≠aAD for every scalar a; covers equal-degree numerator and denominator as well as unequal degrees |
| `lem:initial-extraction` | `InitialExtraction.lean`: `coprime_linear_factor_two_row_extraction`, `small_power_product_single_base_slice`; `InitialExtension.lean`: `binomial_extension_distance` | Checked common cofactor extraction, weight-at-most-three slice conclusion, and distance increase |
| `lem:initial-powers` | `UnivariateWeight.lean`: `univariate_power_weight_three_all`; `BivariatePower.lean`: `bivariateQuadratic_constant_power`, `bivariateQuadratic_power_seven`; `BivariatePowerMultiplier.lean`: `bivariateQuadratic_constant_power_mul`, `bivariateQuadratic_power_mul_six`; `InitialLateRows.lean`: `initial_small_row_distance`, `initial_small_row_power_lower`, `initial_small_row_power_mul_four`; `AffineNondistinguished.lean` and fresh digit-cost equality | Dense univariate, constant/binomial quadratic, small linear/quadratic row estimates checked. Nondistinguished affine-triangle bound `interval_three_nondistinguished_power_six` is also checked |
| `eq:initial-sliced-support` | `GenericInitialOverlap.lean`: `translated_simplex_dilate_inter_card_le_one`, `translated_dilate_overlap_rows`; `InitialSlicedOverlap.lean`: `InitialSlicedData.translated_overlap_rows`, `distinguished_overlap_rows`; `LaurentSimplexOverlap.lean`: `translated_integer_simplex_dilate_inter_card_le_one` | Full generic simplex and rowwise refinement checked, including the base-row residue bound, unequal distinguished powers and arbitrary integer translations; `CoreOverlap.lean` also gives stronger interval-specific bounds |
| `lem:short-fresh-test` | `ShortFreshTest.lean`, `ShortFreshFive.lean` | Both full criteria checked, including the two-fresh-variable budget-five case; hypotheses are actual power, binomial and mixed-sum bounds |
| `eq:initial-nine-core` | `CoreNine.lean`; `CoreNinePowers.lean`: `intervalCore_nine_power_six`, `intervalCore_nine_distinguished_binomial_six` | Checked actual weighted core distance four and positive power bound six |
| `eq:initial-twelve-A` | `CoreTwelve.lean`: `baseTwelve_distance_four`, `baseTwelve_power_seven`, `baseTwelve_power_mul_six` | Checked with arbitrary nonzero inherited weights |
| `eq:initial-twelve-E` | `InitialTenBase.lean`: `initialTenBase_distance_seven`; `InitialTwoBinomials.lean`: `initialTenBase_power_mul_eight`; `InitialTwelve.lean`: `intervalCore_twelve_power_nine` | Checked distance seven, arbitrary univariate multiplier cost eight, and bare power cost nine |
| `eq:initial-late-A` | `InitialLateBases.lean`: `lateBase_distance_five`, `lateBase_power_seven`, `lateBase_power_mul_six` | Actual weighted bases 18 and 24 fully checked |
| `eq:initial-fifteen-F`, `eq:initial-late-F` | `LinearExtensionOps.lean`, `InitialLateExtension.lean`: `linear_core_power_mul_endpoints`; `InitialFifteenCores.lean`: `baseTwelve_profile`, `baseSixteen_profile`, `affine_binomial_core_distance_ten`, `affine_binomial_core_nondistinguished_power_sixteen`; `InitialLateProfiles.lean`: `InitialCoreProfile.linear_extend` | Generic endpoint machinery and actual 12/16/18/24 inherited-coefficient profile assemblies checked, including actual n15/16 core distance ten and nondistinguished-power bound sixteen |
| `eq:initial-late-E`, `eq:initial-twentyone-power` | `InitialLateProfiles.lean`: `InitialCoreProfile.linear_extend`; `InitialLateCoreBounds.lean` and `InitialLateRows.lean` | Actual profile construction and late core bounds fully checked; record fields give the stated distance, multiplier and bare-power estimates |
| `eq:initial-sixteen-mixed` | `InitialSixteenMixed.lean`: `intervalCore_sixteen_mixed_distinguished_monomials`, `intervalCore_sixteen_mixed_distinguished` | Actual weighted core-sixteen mixed-power bound checked; distinguished degrees and monomial translations are explicit |
| `eq:initial-ten-distance` | `CoreTen.lean`: `intervalCore_ten_distance_seven`, `coreTenTemplate_distance_seven` | Checked exact weighted template and valuation-coordinate identification |
| `eq:initial-ten-shape` | `InitialTenShape.lean`: `linearExtension_small_multiple_shape`; `ThreeRowShape.lean`: `three_row_shape_four_one_two` | Checked generic exact three-row shape and actual core-ten assembly |
| `eq:initial-ten-power`, `eq:initial-ten-binomial` | `CoreTenPowers.lean`: `coreTenTemplate_power_nine`, `coreTenTemplate_power_binomial_eight` | Actual weighted template bounds fully checked |
| `eq:initial-ten-two-powers` | `CoreTenTwoPowers.lean`: `coreTenTemplate_two_powers_eight` | Actual weighted unequal distinguished powers fully checked and transitively audited |
| `eq:fin-setup` | `IntervalFresh.lean`: `rescale_interval_eq_core_add_fresh`, `weight_intervalCore_add_freshCount`, `distance_interval_eq_freshData` | Checked exact normalization and unchanged core coefficients |
| `eq:fin-d0`, `lem:fin-six` | `MiddleBase.lean`: `middle_base`, `middle_interval_mul_base_lower`; `MiddleSix.lean`: `middle_six_term_bound` | Checked full base bound and all multipliers of at most six terms, including variables outside the interval |
| `eq:fin-basic-budgets` | `Arithmetic/MiddleBudgets.lean`: `middleBasicBudgets` | Checked exact finite numerical conjunction |
| `lem:binomial-lines` | `BinomialLines.lean`: `weight_mul_binomial_projection`, `weight_mul_binomial_lines`; `LineProjectionGeometry.lean`: `binomialLineProjection_eq_iff`, `exists_binomialLineProjection` | Checked twice the number of occupied projection fibers, with exact rational-parallel-line equivalence |
| General occupied-line observations following `lem:binomial-lines` | `AffineLineCounts.lean`: `affineDimension_le_binomialLineCount`, `affineDimension_add_two_le_binomialLineCount_of_four_collinear`; `FiniteLineRepresentatives.lean` | Affine dimension d gives at least d occupied lines; four transverse collinear support points give at least d+2. Both general statements checked |
| `lem:two-missing-products` | `TwoMissingProducts.lean`: `two_missing_products_translate`; `Arithmetic/TwoMissingCertificates.lean`: `two_missing_anchored` | Checked at 27 and 28 for arbitrary exponent translates, including extra variables |
| `eq:fin-unique-cover-bound` | `TwoMissingProducts.lean`: `unique_cover_bound`, `unique_cover_bound_reverse` | Checked actual coefficients; characteristic other than two and monomial cofactor hypotheses match the manuscript |
| `eq:fin-affine-weight` | `AffineRows.lean`: `FreshData.weight_mul_affine` | Checked exact row identity for arbitrary fields and weights |
| `eq:fin-affine-budget` | `AffineBudget.lean`: `affine_square_cancellation`, `affine_row_budget`, `affine_counterexample_budgets`; `Arithmetic/MiddleUniqueBudgets.lean`: `middle_unique_product_budget` | Checked algebraic inequalities and full finite budget after clearing denominators |
| `eq:fin-third-row`, `eq:fin-binomial-invariant` | `RowWeights.lean`: `endpoint_distance_of_three_rows`; `TwoRowGeneral.lean`: `binomial_coefficient_ratio_constant`, `three_le_rows_of_no_scalar_identity`, `top_three_endpoint_distance` | Checked over arbitrary characteristic-two fields, excluding every nonzero scalar identity |
| `eq:fin-binary-smooth`, `eq:fin-kappa` | `BinarySmoothCore.lean`: `middle_binary_smooth_distance`, `middle_binary_five_smooth_distance`; `BinaryCore.lean`: `middle_binary_core_distance`, `middle_binary_core_mul_lower` | Full 7/6/8 smooth profile, five-smooth six, and actual core κ bound checked and audited |
| `eq:fin-quantitative-cut` | `BinaryComparison.lean`: `comparison_quantitative_cut`; `ComparisonLifting.lean`: `prime_comparison_lifting`; `BinaryComparisonAll.lean` exact comparison rows | Checked normalized profile inequalities and arbitrary-variable lifting preserving the exact input weight |
| `lem:fin-parity-pair` | `ParityTriple.lean`, `ParityPairing.lean`, `ParityUnpaired.lean`, `ParityTwoPairs.lean`, `ParityPairBound.lean`: `interval_three_one_parity_bound`; `ParityPattern.lean`: `interval_four_term_three_class_bound`; `LaurentParity.lean`: `laurent_interval_four_term_three_class_bound` | Full 36/36/44 bounds checked for polynomial and Laurent multipliers, arbitrary weights and arbitrary multiplier variables; strict Q5 three-term cost proved via prime rigidity |
| `eq:fin-binary-u` | `BinaryCore.lean`: `middle_binary_core_counterexample_width`; `Arithmetic/ParityBudgets.lean`: `binary_width_budgets`, `binary_five_term_data` | Checked actual u≤5 and u≤4 unless n=58, with no conditional κ premise |
| `eq:fin-majorization` | `ParityMajorization.lean`: `residueWeight_mul_two_level`, `residueWeight_mul_four_not_three_one`; `ParityIntegerBounds.lean`: `intervalCore_parity_mixed_capacity`, `intervalCore_parity_four_capacity` | Checked actual residue convolution, mixed-class bound and refined four-term bound when the 3+1 pattern is absent |
| `eq:fin-capacity-gates` | `Arithmetic/ParityBudgets.lean`: `binary_capacity`; `BinaryFourComparison.lean`: `binary_four_exception_capacity`; `BinaryResidueComparison.lean` capacity contradictions | Checked exact numerical gates with actual core/cofactor support and comparison weights |
| `arith:eq:threshold-sum` | `Arithmetic/ThresholdSum.lean`: `rough_threshold_sum`, `threshold_sum`, `threshold_sum_primes`; `Pilz.ComponentCounts.card_roughNumbers_index_ge` | Exact displayed signed formula checked, plus arbitrary additive-group costs and arbitrary finite excluded-divisor sets; n=0 included |
| `arith:residue-count` | `Arithmetic/ResidueCountFive.lean`: `roughCount_five_residues`, `roughCount_five_floor_sum`, `roughRealCount_five_floor_sum`, `roughRealCount_five_residues` | Literal eight-residue floor formula and equivalent quotient/remainder count checked, including real x≥0 |
| `arith:lem:rough-discrepancy`, `arith:lem:no-core-half-discrepancy` | `Pilz.SieveSmallReal`: `roughRealCount_two_discrepancy`, `roughRealCount_three_discrepancy`; `Pilz.SieveBaseReal`: `roughRealCount_five_discrepancy`, `roughRealIntervalCount_five_discrepancy`; `Pilz.SievePrimes`: `roughDiscrepancy_primesUpTo`; `roughIntervalDiscrepancy_of_discrepancy` | Full real-variable discrepancies checked, including the sharper 22/15 half-interval error |
| `arith:lem:one-step-sieve` | `Pilz.SieveEstimates`: `roughRealCount_one_step`, `roughRealIntervalCount_one_step`, `roughRealIntervalCount_one_step_refined` | Checked for arbitrary disjoint finite prime sets and real x≥0, with the refined error |
| `arith:eq:one-step-component-bound` | `OneStepComponents.lean`: `component_budget_one_step` | Generic weighted wrapper fully checked; arbitrary sieve sets with union `primesUpTo q`, no nonnegative-α assumption |
| `arith:eq:base-five-sieve` | `Pilz.SievePrimes`: `sieveAlpha`, `sieveNu`, `card_sieveExtraPrimes`, `roughRealCount_primesUpTo_alpha_lower`, `roughRealIntervalCount_primesUpTo_alpha_lower` | Exact constants and their count inequalities checked |
| `arith:lem:rough-semiprime-count`, `arith:eq:small-prime-sieve` | `Arithmetic/RoughSemiprime.lean`: `roughCount_eleven_formula`, `roughRealCount_eleven_eq_five`, `small_prime_sieve_nat`, `small_prime_sieve` | Exact eleven-rough inclusion-exclusion for every real x and displayed real-x prime-count formula for 11≤x≤1799 fully checked. Natural certificate uses kernel-checked successive differences and induction, with exact floor transport |
| `arith:lem:eight-endpoint-prime-budget`, `arith:eq:ten-prime-budget` | `GeneralPrimeBudget.lean`: `localized_prime_budget_general`, `localized_prime_budget_general_surplus`, `primeCount_odd_threshold_growth`; `LocalizedSupport.lean`: `localized_prime_budget` | General U≥4 theorem fully checked; U=10 specialization also checked |
| `arith:eq:elementary-factorial-combination` | `Pilz.ChebyshevXi`: `xi_lower`, `xi_upper_simplified`; definitions `xi`, `mu1` | Exact real-variable factorial combination checked |
| `arith:eq:no-core-K` | `Pilz.FreshLargeReal`: `freshG_log_lower_of_rlog` applied to `Pilz.Chebyshev.freshLogLowerBound` from `Pilz.ChebyshevConclusion` | Checked multiplicative form of the displayed quotient inequality; n>0 supplies the equivalent division form |
| `arith:lem:no-core-small-primes`, `arith:eq:no-core-positive-profile` | `Arithmetic/LocalizedNumerics.lean`: `small_support_prime_numeric`; `LocalizedSupport.lean`: `localized_five_band_budget`, `localized_expansion_five_bands` | Checked complete five-band numerical and weighted inequalities, for all n≥1024 |
| `arith:lem:no-core-middle-primes` | `Arithmetic/LocalizedNumerics.lean`: `middle_support_prime_numeric`; `LocalizedSupport.lean`: `localized_middle_budget`, `localized_expansion_middle` | Checked both unbounded middle support-prime bands |
| `arith:lem:no-core-odd-product` | `Arithmetic/Imported.lean`: `prime_product_sqrt` | Checked for every odd prime, without a cutoff |

Pure navigation labels have no additional mathematical proposition:
`sec:main`, `sec:tools`, `sec:residue`, `sec:large-weighted`, `sec:modules`,
`sec:initial`, `sec:finite`, `sec:arithmetic`, `arith:sec:one-step-sieve`,
`arith:sec:written-low-range`, `sec:prime-blocks`, `arith:sec:elementary-primes`,
`arith:sec:small-prime-profile-replacement`, `arith:sec:no-core-closure`, and
`arith:sec:localized-completion`.
