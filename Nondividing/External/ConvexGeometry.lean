import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Nondividing.External.DiscreteJohn

namespace Nondividing.External

open Filter MeasureTheory

/-!
This file contains only the standard convex/lattice inputs permitted by E5
of `LEAN_FORMALIZATION_ROUTE.md`.  Mathlib 4.32.0 contains Minkowski's convex
body theorem, but not the four results below.
-/

/--
Trusted external interface E5(a): Blaschke selection.

Source: Rolf Schneider, *Convex Bodies: The Brunn--Minkowski Theory*,
2nd ed., Theorem 1.8.7.  `ConvexBody` already packages nonemptiness,
compactness, and convexity, and its metric is the Hausdorff metric.  The
common upper bound `C` is the usual uniform boundedness hypothesis.
-/
axiom blaschke_selection {d : ℕ}
    (K : ℕ → ConvexBody (Fin d → ℝ)) (C : ConvexBody (Fin d → ℝ))
    (hKC : ∀ n, K n ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ L : ConvexBody (Fin d → ℝ), Tendsto (K ∘ φ) atTop (nhds L)

/--
Trusted external interface E5(b): continuity of volume under Hausdorff
convergence of convex bodies.

Source: Rolf Schneider, *Convex Bodies: The Brunn--Minkowski Theory*,
2nd ed., Theorem 1.8.20.  Convergence in `ConvexBody` is Hausdorff
convergence.
-/
axiom convexBody_volume_tendsto {d : ℕ}
    {K : ℕ → ConvexBody (Fin d → ℝ)} {L : ConvexBody (Fin d → ℝ)}
    (hK : Tendsto K atTop (nhds L)) :
    Tendsto (fun n => volume (K n : Set (Fin d → ℝ))) atTop
      (nhds (volume (L : Set (Fin d → ℝ))))

/--
Trusted external interface E5(c): the Rogers--Shephard difference-body
inequality.

Source: C. A. Rogers and G. C. Shephard, "The difference body of a convex
body", *Arch. Math.* 8 (1957), Theorem 1.  Scalar multiplication by `-1`
forms `-K`; hence the body on the left is exactly `K-K`.
-/
axiom rogers_shephard {d : ℕ} (K : ConvexBody (Fin d → ℝ)) :
    volume ((K + (-1 : ℝ) • K : ConvexBody (Fin d → ℝ)) :
      Set (Fin d → ℝ)) ≤
      (Nat.choose (2 * d) d : ENNReal) *
        volume (K : Set (Fin d → ℝ))

/--
Trusted external interface E5(d): the full-rank lattice-point/volume
corollary used in the manuscript.

Source: Betke--Henk--Wills, "Successive-minima-type inequalities",
Proposition 2.1, combined with Minkowski's second theorem (their (1.3)).
If the integer points of an origin-symmetric convex body span the ambient
space, then the last successive minimum is at most one; those two cited
inequalities give a dimension-dependent constant.  This interface records
only that corollary, with the finite set required to be exactly `K ∩ ℤ^d`.
-/
axiom full_rank_lattice_points_le_volume (d : ℕ) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (K : ConvexBody (Fin d → ℝ)) (A : Finset (Fin d → ℤ)),
        (∀ x ∈ (K : Set (Fin d → ℝ)), -x ∈ K) →
        (∀ z, z ∈ A ↔ realPoint z ∈ K) →
        Submodule.span ℝ (realPoint '' (A : Set (Fin d → ℤ))) = ⊤ →
        (A.card : ENNReal) ≤ (C : ENNReal) *
          volume (K : Set (Fin d → ℝ))

end Nondividing.External
