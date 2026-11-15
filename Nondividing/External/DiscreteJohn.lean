import Nondividing.GAP
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace Nondividing.External

def realPoint {d : ℕ} (z : Fin d → ℤ) : Fin d → ℝ :=
  fun i => z i

def integerRealSpan {d : ℕ} (A : Finset (Fin d → ℤ)) :
    Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (realPoint '' (A : Set (Fin d → ℤ)))

/--
Trusted external interface E2.

Source: Pham–Zakharov, Lemma 7 (citing Tao–Vu, Lemma 3.36).  This is
their statement after identifying the appropriate rank-`h` lattice with
`ℤ^h`: a proper symmetric rank-`h` progression has an inner fixed
dilate contained in the lattice points of the body and contains all those
lattice points.  The cardinality bound is the immediate cardinal form of
the same sandwich (all displayed radii are positive).  The steps are
required to lie in `H`, so the output is literally in the appropriate
lattice rather than the ambient lattice.
-/
axiom discrete_john (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, 0 < C ∧
      ∀ (h : ℕ) (H : Submodule ℝ (Fin d → ℝ))
        (K : Set (Fin d → ℝ)) (A : Finset (Fin d → ℤ)),
        Module.finrank ℝ H = h →
        IsCompact K →
        Convex ℝ K →
        (∀ x, x ∈ K ↔ -x ∈ K) →
        K ⊆ H →
        (∀ z, z ∈ A ↔ realPoint z ∈ K) →
        integerRealSpan A = H →
        K.Nonempty →
        ∃ P : GAP d h,
          (∀ i, realPoint (P.step i) ∈ H) ∧
          P.Proper ∧
          P.dilatedCarrier c ⊆ A ∧
          A ⊆ P.carrier ∧
          P.carrier.card ≤ C * A.card

end Nondividing.External
