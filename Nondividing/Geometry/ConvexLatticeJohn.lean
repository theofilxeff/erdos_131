import Nondividing.External.DiscreteJohn
import Nondividing.External.ConvexGeometry
import Nondividing.Geometry.RealBox

namespace Nondividing

open Nondividing.External

def sectionBody {d : ℕ} (H : Submodule ℝ (Fin d → ℝ))
    (M : Fin d → ℕ) : Set (Fin d → ℝ) :=
  realCoordinateBox M ∩ (H : Set (Fin d → ℝ))

noncomputable def latticeSection {d : ℕ}
    (H : Submodule ℝ (Fin d → ℝ)) (M : Fin d → ℕ) :
    Finset (Fin d → ℤ) := by
  classical
  exact (coordinateBox M).filter fun z => realPoint z ∈ H

@[simp] theorem mem_latticeSection {d : ℕ}
    {H : Submodule ℝ (Fin d → ℝ)} {M : Fin d → ℕ}
    {z : Fin d → ℤ} :
    z ∈ latticeSection H M ↔
      z ∈ coordinateBox M ∧ realPoint z ∈ H := by
  classical
  simp [latticeSection]

theorem realPoint_mem_sectionBody_iff {d : ℕ}
    (H : Submodule ℝ (Fin d → ℝ)) (M : Fin d → ℕ)
    (z : Fin d → ℤ) :
    realPoint z ∈ sectionBody H M ↔ z ∈ latticeSection H M := by
  change ((fun i => (z i : ℝ)) ∈ realCoordinateBox M ∧
    realPoint z ∈ H) ↔ z ∈ latticeSection H M
  rw [realPoint_mem_realCoordinateBox_iff, mem_latticeSection]

theorem sectionBody_isCompact {d : ℕ}
    (H : Submodule ℝ (Fin d → ℝ)) (M : Fin d → ℕ) :
    IsCompact (sectionBody H M) :=
  (realCoordinateBox_isCompact M).inter_right H.closed_of_finiteDimensional

theorem sectionBody_convex {d : ℕ}
    (H : Submodule ℝ (Fin d → ℝ)) (M : Fin d → ℕ) :
    Convex ℝ (sectionBody H M) :=
  (realCoordinateBox_convex M).inter H.convex

theorem sectionBody_symmetric {d : ℕ}
    (H : Submodule ℝ (Fin d → ℝ)) (M : Fin d → ℕ)
    (x : Fin d → ℝ) :
    x ∈ sectionBody H M ↔ -x ∈ sectionBody H M := by
  simp only [sectionBody, Set.mem_inter_iff]
  constructor
  · intro hx
    exact ⟨(realCoordinateBox_symmetric M x).mp hx.1, H.neg_mem hx.2⟩
  · intro hx
    have hbox : x ∈ realCoordinateBox M := by
      have := (realCoordinateBox_symmetric M (-x)).mp hx.1
      simpa using this
    have hH : x ∈ H := by
      have := H.neg_mem hx.2
      simpa using this
    exact ⟨hbox, hH⟩

theorem sectionBody_subset_submodule {d : ℕ}
    (H : Submodule ℝ (Fin d → ℝ)) (M : Fin d → ℕ) :
    sectionBody H M ⊆ H :=
  Set.inter_subset_right

theorem integerRealSpan_latticeSection_eq {d : ℕ}
    (H : Submodule ℝ (Fin d → ℝ)) (M : Fin d → ℕ)
    (C₀ : Finset (Fin d → ℤ))
    (hC₀box : C₀ ⊆ coordinateBox M)
    (hspan : integerRealSpan C₀ = H) :
    integerRealSpan (latticeSection H M) = H := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨z, hz, rfl⟩
    exact (mem_latticeSection.mp hz).2
  · rw [← hspan]
    apply Submodule.span_mono
    rintro x ⟨z, hz, rfl⟩
    exact ⟨z, mem_latticeSection.mpr
      ⟨hC₀box hz, by
        exact Submodule.subset_span ⟨z, hz, rfl⟩⟩, rfl⟩

/--
The coordinate-box instance of the manuscript's convex-lattice John lemma.
It is proved from E2; in particular, the section is represented by the
actual filtered `Finset` of integer points.
-/
theorem coordinate_section_john (d : ℕ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (h : ℕ) (H : Submodule ℝ (Fin d → ℝ))
        (M : Fin d → ℕ) (C₀ : Finset (Fin d → ℤ)),
        Module.finrank ℝ H = h →
        C₀ ⊆ coordinateBox M →
        integerRealSpan C₀ = H →
        ∃ P : GAP d h,
          (∀ i, realPoint (P.step i) ∈ H) ∧
          P.Proper ∧
          latticeSection H M ⊆ P.carrier ∧
          P.carrier.card ≤ C * (coordinateBox M).card := by
  obtain ⟨c, hc, C, hC, hJohn⟩ := discrete_john d
  refine ⟨C, hC, ?_⟩
  intro h H M C₀ hdim hC₀box hspan
  obtain ⟨P, hstep, hproper, _hinner, houter, hcard⟩ :=
    hJohn h H (sectionBody H M) (latticeSection H M)
      hdim (sectionBody_isCompact H M) (sectionBody_convex H M)
      (sectionBody_symmetric H M)
      (sectionBody_subset_submodule H M)
      (fun z => (realPoint_mem_sectionBody_iff H M z).symm)
      (integerRealSpan_latticeSection_eq H M C₀ hC₀box hspan)
      ⟨0, (by simp : (0 : Fin d → ℝ) ∈ realCoordinateBox M), H.zero_mem⟩
  exact ⟨P, hstep, hproper, houter,
    hcard.trans (Nat.mul_le_mul_left C (by
      classical
      simpa [latticeSection] using
        Finset.card_filter_le (coordinateBox M)
          (fun z => realPoint z ∈ H)))⟩

/-- Any finite set of lattice points in a symmetric coordinate box sits inside a
proper symmetric GAP of the same rank as its real span, of cardinality
`≪_d |box|`.  This is the rank-`r` (`r ≤ d`) containment underlying
`lem:slab-count`'s non-full-rank alternative and the general John placement; the
sharper full-rank volume estimate is separate. -/
theorem section_in_gap (d : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (S : Finset (Fin d → ℤ)) (M : Fin d → ℕ),
      S ⊆ coordinateBox M →
      ∃ (r : ℕ) (Q : GAP d r), Q.Proper ∧ S ⊆ Q.carrier ∧
        Q.carrier.card ≤ C * (coordinateBox M).card := by
  obtain ⟨C, hC, hjohn⟩ := coordinate_section_john d
  refine ⟨C, hC, ?_⟩
  intro S M hSbox
  set H := integerRealSpan S with hH
  obtain ⟨Q, _hstep, hproper, hcover, hcard⟩ :=
    hjohn (Module.finrank ℝ H) H M S rfl hSbox rfl
  refine ⟨Module.finrank ℝ H, Q, hproper, ?_, hcard⟩
  -- `S ⊆ latticeSection H M ⊆ Q.carrier`.
  intro z hz
  apply hcover
  rw [mem_latticeSection]
  exact ⟨hSbox hz, Submodule.subset_span ⟨z, hz, rfl⟩⟩

end Nondividing
