import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Comparator challenge file — Erdős problem 131

**This is the trusted statement surface.**  To trust the formalization you
need to read THIS file (the two definitions and one theorem below), the axiom
whitelist in `comparator-config.json`, and the four files declaring these axioms
in `Nondividing/External/`.  The Comparator
tool (https://github.com/leanprover/comparator) certifies that the project
(`Solution.lean` → `Nondividing.FinalAssembly`) proves *exactly* the statement
below, using *only* the permitted axioms, and that the proof is accepted by
the Lean kernel.

The permitted axioms are Lean's three foundational axioms (`propext`,
`Classical.choice`, `Quot.sound`) plus the seven external results
from E1, E2, E4 and E5 declared in `Nondividing/External/` — each a published result cited to
the literature (Conlon–Fox–Pham / Pham–Zakharov, Schneider, Rogers–Shephard,
Betke–Henk–Wills); see the README.

**The statement.**  `F N` is the largest size of a *non-dividing* subset of
`{1, …, N}` — a set none of whose members divides the sum of any nonempty
subset of the other members.  The theorem: `log F(N) / log N → 1/5`, i.e.
`F(N) = N^{1/5 + o(1)}`.
-/

namespace Nondividing

open scoped BigOperators

/-- No member of `A` divides a nonempty sum of other, distinct members of `A`. -/
def NonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S.Nonempty → S ⊆ A.erase a → ¬a ∣ ∑ s ∈ S, s

/-- Non-dividing subsets of `[1,N]`. -/
noncomputable def candidates (N : ℕ) : Finset (Finset ℕ) :=
  by
    classical
    exact (Finset.Icc 1 N).powerset.filter NonDividing

/-- The largest cardinality of a non-dividing subset of `[1,N]`. -/
noncomputable def F (N : ℕ) : ℕ :=
  (candidates N).sup Finset.card

/-- **Erdős problem 131** (the main theorem of the manuscript): the maximum
size of a non-dividing subset of `[1, N]` satisfies
`log F(N) / log N → 1/5`. -/
theorem main_log_limit :
    Filter.Tendsto (fun N : ℕ => Real.log (F N) / Real.log N)
      Filter.atTop (nhds ((1 : ℝ) / 5)) := sorry

end Nondividing
