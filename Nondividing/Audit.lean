import Nondividing.Main

#print axioms Nondividing.lower_construction
#print axioms Nondividing.main_lower_eps

-- Phase C progression-comparison assemblies (parameterized over E1 outputs):
-- these must reach only Lean core axioms, since the external assumptions enter only through their
-- hypotheses, not through any axiom in the proof term.
#print axioms Nondividing.GAP.progression_comparison_gt
#print axioms Nondividing.GAP.progression_comparison_le

-- Package-based progression comparison is parameterized over an abstract
-- `Package`, so it reaches only Lean core axioms; the E1 interface
-- `cfp_structure` enters exactly where the concrete package is built.
#print axioms Nondividing.progression_comparison_package
-- The `e ≤ r` package form invokes the John placement, so it reaches E2 too.
#print axioms Nondividing.progression_comparison_le_package
#print axioms Nondividing.nonempty_package

-- Further Phase C/D/H results: gap_contained and the Phase H pigeonhole chain are
-- either parameterized over external data or purely elementary, so they reach
-- only Lean core axioms.
#print axioms Nondividing.gap_contained
#print axioms Nondividing.exists_shell_reduction
#print axioms Nondividing.shellNonDividing_dOne
#print axioms Nondividing.main_log_limit_of_upper

-- Convex-lattice John placement: reaches exactly the E2 interface `discrete_john`
-- plus Lean core axioms.
#print axioms Nondividing.coordinate_section_john
#print axioms Nondividing.section_in_gap

-- lattice_section_box is proved entirely from mathlib (projection existence via
-- dual separation), so reaches only Lean core axioms.
#print axioms Nondividing.lattice_section_box
#print axioms Nondividing.index_cardinality_bound
#print axioms Nondividing.realRank_eq_of_index
#print axioms Nondividing.integerRealSpan_eq_top
#print axioms Nondividing.smul_projNorm_mem_realBox
#print axioms Nondividing.projective_span_package
#print axioms Nondividing.duality_representation_from_projective
#print axioms Nondividing.exists_capped_combination
#print axioms Nondividing.projective_duality
#print axioms Nondividing.mem_affineSpan_projNorm_iff
#print axioms Nondividing.intrinsicInterior_convexHull_projNorm_nonempty
#print axioms Nondividing.numerology

-- Phase E projective-convexity endgame + Phase H capstone: both parameterized
-- over the deep inputs (tube inclusion / projective theorem), so core axioms only.
#print axioms Nondividing.shellNonDividing_no_positive_multiple
#print axioms Nondividing.exists_positive_nsmul_mem
#print axioms Nondividing.projective_convexity_of_tube
#print axioms Nondividing.realEval_injective
#print axioms Nondividing.main_upper_eps_of_projective

-- The ψ-transferred rounding proof uses only Lean core axioms.
#print axioms Nondividing.zonotope_rounding_carrier
#print axioms Nondividing.evalHom_injective
#print axioms Nondividing.filling_assembly
#print axioms Nondividing.GAP.add_mem_dilatedCarrier
#print axioms Nondividing.one_sided_filling

-- index_bound part 2 core: [ℤ^d:L] = |det(steps)| is proved from mathlib, core only.
#print axioms Nondividing.index_range_eq_natAbs_det
#print axioms Nondividing.GAP.two_pow_mul_prod_radius_le_card

-- index_bound part 2 FULL: the Haar-volume comparison chain, all core only.
#print axioms Nondividing.abs_det_stepMapR
#print axioms Nondividing.volume_stepMapR_realBox
#print axioms Nondividing.stepMapR_realBox_bound
#print axioms Nondividing.index_mul_le_volume_bound
#print axioms Nondividing.index_bound_part2

-- slab_count r=d: shear volume bound is core-only; the count reaches E5.
#print axioms Nondividing.det_shearMatrix
#print axioms Nondividing.volume_slab_inter_box_le
#print axioms Nondividing.exists_width_coordinate
#print axioms Nondividing.slab_count_full_rank
-- full slab_count reaches E2 (John placement) + E5 (full-rank count) + core.
#print axioms Nondividing.slab_count
-- slab_exclusion counting dichotomy over the package: E2+E5+core.
#print axioms Nondividing.slab_exclusion_count
-- full slab_exclusion (explicit constants c*, K): E2+E5+core.
#print axioms Nondividing.slab_exclusion

-- robust_zonotope infrastructure: zonotope + separation, all core-only.
#print axioms Nondividing.symZonotope_separation
#print axioms Nondividing.symZonotope_isCompact
#print axioms Nondividing.symZonotope_contains_box_of_slab_bound
#print axioms Nondividing.centre_add_symZonotope_subset_realZonotope

-- robust_zonotope FULL: reaches E1 (package) + E2 + E5 + core.
#print axioms Nondividing.robust_slab_bound
#print axioms Nondividing.robust_zonotope

-- THE TUBE INCLUSION (dagger): robust_zonotope + one_sided_filling composed.
-- Reaches E2+E5+core (parameterized over the package).
#print axioms Nondividing.tube_inclusion
#print axioms Nondividing.tube_inclusion_of_zonotope

-- PROJECTIVE CONVEXITY ASSEMBLED: the complete contradiction, E2+E5+core
-- (E1 enters only via the Package at the call site).
#print axioms Nondividing.projective_convexity_assembled

-- cap_lifting alternative (i): E2+core (John placement through section_in_gap).
#print axioms Nondividing.cap_lifting_deficient
#print axioms Nondividing.ShellNonDividing.of_map

-- projective_theorem preamble numerology: core only.
#print axioms Nondividing.sigma_dimension_cap
#print axioms Nondividing.box_exponent_of_excess
#print axioms Nondividing.exists_sigma_gap

-- weighted_density injective case: reaches exactly E4 + core.
#print axioms Nondividing.weighted_density_injective

-- weighted_density machinery: perturbation core-only; step reaches E4.
#print axioms Nondividing.exists_perturbed_family
#print axioms Nondividing.mem_of_tendsto_convexBody
#print axioms Nondividing.weighted_density_step

-- weighted_density FULL (rho->0 Blaschke limit): E4+E5a+E5b+core.
#print axioms Nondividing.weighted_density

-- cap_lifting alternative (ii) cone-volume core: E5c+E5d+core.
#print axioms Nondividing.cap_cone_count
#print axioms Nondividing.volume_cone

-- unshifted_preprocessing building blocks: core + E2 (parametric in Package).
#print axioms Nondividing.irreducible_or_witness
#print axioms Nondividing.prep_step
#print axioms Nondividing.unshifted_preprocessing_toward
