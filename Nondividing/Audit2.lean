import Nondividing.FinalAssembly
import Nondividing.ProjectiveTheorem

-- Phase 3 (projective theorem iteration, ProjectiveTheorem.lean): the whole
-- iteration skeleton — ExcessiveStage facts, lexicographic termination,
-- DescentStep/CountingStep/RawStep conversions (numerology + sigma-gap),
-- PrepSupplier/IrreducibleIncrement composition, PrepChain bookkeeping
-- (master product estimate + U-cap), the d=1 adapter and the conditional
-- main-theorem compositions.  All are parameterized over the TODO supplier
-- predicates, hence reach only Lean core axioms.
#print axioms Nondividing.no_excessive_stage
#print axioms Nondividing.projective_theorem_of_descent
#print axioms Nondividing.projective_theorem_of_descent_supplier
#print axioms Nondividing.projective_theorem_dOne
#print axioms Nondividing.main_upper_eps_of_descent
#print axioms Nondividing.main_log_limit_of_descent
#print axioms Nondividing.descentStep_of_countingStep
#print axioms Nondividing.countingStep_of_rawStep
#print axioms Nondividing.descentSupplier_of_rawStep
#print axioms Nondividing.sameDim_ratio_lt
#print axioms Nondividing.rawStep_of_suppliers
#print axioms Nondividing.descentSupplier_of_pipeline
#print axioms Nondividing.PrepChain.box_master
#print axioms Nondividing.PrepChain.pow_upSum_le

-- ============================================================
-- THE MAIN THEOREM: log F(N) / log N → 1/5.
-- Expected axioms: Lean core (propext, Classical.choice, Quot.sound)
-- + the seven whitelisted mathematical axioms from E1, E2, E4 and E5.
-- ============================================================
#print axioms Nondividing.main_log_limit
#print axioms Nondividing.descentSupplier_proved
#print axioms Nondividing.prepPrimedHypothesis_proved
