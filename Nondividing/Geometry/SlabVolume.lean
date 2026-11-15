import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.IntervalCases
import Mathlib.Analysis.Convex.Body
import Nondividing.Geometry.GAPVolume
import Nondividing.External.ConvexGeometry

open scoped BigOperators
open MeasureTheory

namespace Nondividing

/-!
# Slab volume via a determinant-1 shear (Phase F, `lem:slab-count` r = d)

The Fubini step `vol(B_ℝ ∩ {|u(x)| ≤ τw}) ≤ dτ·vol(B_ℝ)` is implemented by a
shear: the linear map fixing all coordinates except `x_j ↦ u(x)/a_j` has
determinant 1 and sends the slanted slab into a thin product box.
-/

/-- The shear matrix: identity except row `j`, which is `(a_i/a_j)_i`. -/
noncomputable def shearMatrix {d : ℕ} (a : Fin d → ℝ) (j : Fin d) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 + Matrix.replicateCol (Fin 1) (Pi.single j (1 : ℝ))
      * Matrix.replicateRow (Fin 1) (fun i => if i = j then 0 else a i / a j)

/-- The shear has determinant 1 (Sherman–Morrison: the rank-one update is
orthogonal to the diagonal entry it modifies). -/
theorem det_shearMatrix {d : ℕ} (a : Fin d → ℝ) (j : Fin d) :
    (shearMatrix a j).det = 1 := by
  have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (Pi.single j (1 : ℝ)) (fun i => if i = j then 0 else a i / a j)
  have hv : (fun i => if i = j then 0 else a i / a j) ⬝ᵥ Pi.single j (1 : ℝ)
      = 0 := by simp [dotProduct, Pi.single_apply]
  rw [hv] at h
  rw [shearMatrix]
  exact h.trans (by norm_num)

/-- Coordinates of the shear: it fixes all coordinates except `j`, which becomes
`u(x)/a_j`. -/
theorem shear_apply {d : ℕ} (a : Fin d → ℝ) (j : Fin d) (ha : a j ≠ 0)
    (x : Fin d → ℝ) :
    ∀ k, Matrix.toLin' (shearMatrix a j) x k
      = if k = j then (∑ i, a i * x i) / a j else x k := by
  intro k
  rw [Matrix.toLin'_apply]
  simp only [shearMatrix, Matrix.add_mulVec, Matrix.one_mulVec]
  rw [Pi.add_apply]
  have hcol : Matrix.mulVec (Matrix.replicateCol (Fin 1) (Pi.single j (1 : ℝ))
      * Matrix.replicateRow (Fin 1) (fun i => if i = j then 0 else a i / a j)) x
      = fun k => (Pi.single j (1 : ℝ) : Fin d → ℝ) k
          * ∑ i, (if i = j then 0 else a i / a j) * x i := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      one_smul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hcol]
  by_cases hk : k = j
  · rw [if_pos hk, hk, Pi.single_eq_same, one_mul]
    have hsplit : ∑ i, (if i = j then 0 else a i / a j) * x i
        = (∑ i, a i * x i) / a j - x j := by
      rw [eq_sub_iff_add_eq]
      rw [show (∑ i, a i * x i) / a j = ∑ i, (a i / a j) * x i from by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring]
      calc (∑ i, (if i = j then 0 else a i / a j) * x i) + x j
          = (∑ i ∈ Finset.univ.erase j, (if i = j then 0 else a i / a j) * x i)
              + (if j = j then (0 : ℝ) else a j / a j) * x j + x j := by
            rw [Finset.sum_erase_add _ _ (Finset.mem_univ j)]
        _ = (∑ i ∈ Finset.univ.erase j, (a i / a j) * x i) + (a j / a j) * x j := by
            rw [if_pos rfl, zero_mul, add_zero, div_self ha, one_mul]
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [if_neg (Finset.mem_erase.mp hi).1]
        _ = ∑ i, (a i / a j) * x i := Finset.sum_erase_add _ _ (Finset.mem_univ j)
    rw [hsplit]
    ring
  · rw [if_neg hk, Pi.single_eq_of_ne hk, zero_mul, add_zero]

/-- **Slab volume bound** (`lem:slab-count`, Fubini step, via the shear).
If `|a_j|·N_j ≥ w/d` (the pigeonhole coordinate) then the slab
`{x ∈ B_ℝ : |⟨a,x⟩| ≤ τw}` has volume at most `2dτ·N_j·∏_{i≠j}(2N_i)
= dτ·2^d·∏N_i = dτ·vol(B_ℝ)`. -/
theorem volume_slab_inter_box_le {d : ℕ} (N : Fin d → ℕ) (a : Fin d → ℝ)
    (j : Fin d) (ha : a j ≠ 0) {τ w : ℝ} (hτ : 0 ≤ τ) (hw : 0 ≤ w)
    (hjw : w ≤ d * (|a j| * (N j : ℝ))) :
    volume {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w}
      ≤ ENNReal.ofReal ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) := by
  classical
  set T := Matrix.toLin' (shearMatrix a j) with hT
  set R : Fin d → ℝ := fun k => if k = j then d * τ * (N j : ℝ) else (N k : ℝ)
    with hR
  have hRj : R j = d * τ * (N j : ℝ) := by rw [hR]; simp
  have hRne : ∀ k, k ≠ j → R k = (N k : ℝ) := by
    intro k hk; rw [hR]; simp [hk]
  have hja : (0 : ℝ) < |a j| := abs_pos.mpr ha
  -- Key coordinate bound for the sheared point.
  have hkey : ∀ x : Fin d → ℝ, |∑ i, a i * x i| ≤ τ * w →
      |(∑ i, a i * x i) / a j| ≤ d * τ * (N j : ℝ) := by
    intro x hxslab
    have h1 : |(∑ i, a i * x i) / a j| ≤ τ * w / |a j| := by
      rw [abs_div]
      exact div_le_div_of_nonneg_right hxslab hja.le
    have h2 : τ * w / |a j| ≤ d * τ * (N j : ℝ) := by
      rw [div_le_iff₀ hja]
      calc τ * w ≤ τ * (d * (|a j| * (N j : ℝ))) :=
            mul_le_mul_of_nonneg_left hjw hτ
        _ = d * τ * (N j : ℝ) * |a j| := by ring
    exact h1.trans h2
  -- The shear sends the slab into the thin product box.
  have himg : T '' {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w}
      ⊆ Set.Icc (fun k => -(R k)) R := by
    rintro _ ⟨x, ⟨hxbox, hxslab⟩, rfl⟩
    have happly := shear_apply a j ha x
    have hbnd := abs_le.mp (hkey x hxslab)
    constructor <;> intro k <;> beta_reduce <;> rw [happly k] <;> by_cases hk : k = j
    · rw [if_pos hk, hk, hRj]; exact hbnd.1
    · rw [if_neg hk, hRne k hk]; exact hxbox.1 k
    · rw [if_pos hk, hk, hRj]; exact hbnd.2
    · rw [if_neg hk, hRne k hk]; exact hxbox.2 k
  -- The shear preserves volume (det = 1).
  have hdet : LinearMap.det T = 1 := by
    rw [hT, LinearMap.det_toLin', det_shearMatrix]
  have hvolT : volume (T '' {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w})
      = volume {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w} := by
    rw [MeasureTheory.Measure.addHaar_image_linearMap, hdet]
    norm_num
  -- Volume of the thin box.
  have hbox : volume (Set.Icc (fun k => -(R k)) R)
      = ENNReal.ofReal ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) := by
    rw [Real.volume_Icc_pi]
    have hterm : ∀ k ∈ Finset.univ, ENNReal.ofReal (R k - -(R k))
        = ENNReal.ofReal (2 * R k) := by
      intro k _; congr 1; ring
    rw [Finset.prod_congr rfl hterm]
    have hRnneg : ∀ k, (0 : ℝ) ≤ R k := by
      intro k
      by_cases hk : k = j
      · rw [hk, hRj]; positivity
      · rw [hRne k hk]; positivity
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => by
      have := hRnneg k; linarith)]
    congr 1
    rw [show (∏ k, (2 * R k)) = 2 ^ d * ∏ k, R k from by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    have hprodR : (∏ k, R k)
        = (d * τ * (N j : ℝ)) * ∏ k ∈ Finset.univ.erase j, (N k : ℝ) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), hRj, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun k hk => hRne k (Finset.mem_erase.mp hk).1
    have hprodN : (∏ i, (N i : ℝ))
        = (N j : ℝ) * ∏ k ∈ Finset.univ.erase j, (N k : ℝ) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_comm]
    rw [hprodR, hprodN]
    ring
  calc volume {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w}
      = volume (T '' _) := hvolT.symm
    _ ≤ volume (Set.Icc (fun k => -(R k)) R) := measure_mono himg
    _ = ENNReal.ofReal ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) := hbox

/-- Pigeonhole width coordinate (`lem:slab-count`): if the width
`w = ∑ᵢ|aᵢ|Nᵢ` is positive, some coordinate has `|a_j|N_j ≥ w/d` (and then
necessarily `a_j ≠ 0`). -/
theorem exists_width_coordinate {d : ℕ} (a : Fin d → ℝ) (N : Fin d → ℕ)
    (hw : 0 < ∑ i, |a i| * (N i : ℝ)) :
    ∃ j, a j ≠ 0 ∧ (∑ i, |a i| * (N i : ℝ)) ≤ d * (|a j| * (N j : ℝ)) := by
  have hd : 0 < d := by
    by_contra hd0
    push_neg at hd0
    interval_cases d
    simp at hw
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => |a i| * (N i : ℝ)) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hsum : (∑ i, |a i| * (N i : ℝ)) ≤ d * (|a j| * (N j : ℝ)) := by
    calc ∑ i, |a i| * (N i : ℝ)
        ≤ ∑ _i : Fin d, |a j| * (N j : ℝ) :=
          Finset.sum_le_sum fun i _ => hmax i (Finset.mem_univ i)
      _ = d * (|a j| * (N j : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨j, ?_, hsum⟩
  intro haj
  rw [haj] at hsum
  simp only [abs_zero, zero_mul, mul_zero] at hsum
  linarith
section SlabBody

open MeasureTheory

/-- The box-slab intersection as a convex body (for E5). -/
noncomputable def slabBody {d : ℕ} (N : Fin d → ℕ) (a : Fin d → ℝ) {c : ℝ}
    (hc : 0 ≤ c) : ConvexBody (Fin d → ℝ) where
  carrier := {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ c}
  convex' := by
    intro x hx y hy s t hs ht hst
    obtain ⟨⟨hx1, hx2⟩, hxs⟩ := hx
    obtain ⟨⟨hy1, hy2⟩, hys⟩ := hy
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
    · have := add_le_add (mul_le_mul_of_nonneg_left (hx1 i) hs)
        (mul_le_mul_of_nonneg_left (hy1 i) ht)
      calc -(N i : ℝ) = s * -(N i : ℝ) + t * -(N i : ℝ) := by
            rw [← add_mul, hst]; ring
        _ ≤ s * x i + t * y i := add_le_add
            (mul_le_mul_of_nonneg_left (hx1 i) hs)
            (mul_le_mul_of_nonneg_left (hy1 i) ht)
        _ = (s • x + t • y) i := by
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · calc (s • x + t • y) i = s * x i + t * y i := by
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        _ ≤ s * (N i : ℝ) + t * (N i : ℝ) := add_le_add
            (mul_le_mul_of_nonneg_left (hx2 i) hs)
            (mul_le_mul_of_nonneg_left (hy2 i) ht)
        _ = (N i : ℝ) := by rw [← add_mul, hst, one_mul]
    · have hsum : ∑ i, a i * (s • x + t • y) i
          = s * (∑ i, a i * x i) + t * (∑ i, a i * y i) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsum]
      calc |s * (∑ i, a i * x i) + t * (∑ i, a i * y i)|
          ≤ |s * (∑ i, a i * x i)| + |t * (∑ i, a i * y i)| := abs_add_le _ _
        _ = s * |∑ i, a i * x i| + t * |∑ i, a i * y i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
        _ ≤ s * c + t * c := add_le_add
            (mul_le_mul_of_nonneg_left hxs hs)
            (mul_le_mul_of_nonneg_left hys ht)
        _ = c := by rw [← add_mul, hst, one_mul]
  isCompact' := by
    have hclosed : IsClosed {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ c} := by
      have h1 : IsClosed (realBox N) := isClosed_Icc
      have hcont : Continuous (fun x : Fin d → ℝ => |∑ i, a i * x i|) := by
        exact (continuous_finsetSum _ fun i _ =>
          (continuous_const.mul (continuous_apply i))).abs
      have h2 : IsClosed {x : Fin d → ℝ | |∑ i, a i * x i| ≤ c} :=
        isClosed_le hcont continuous_const
      exact (h1.inter h2)
    exact (isCompact_Icc).of_isClosed_subset hclosed
      (fun x hx => hx.1)
  nonempty' := by
    refine ⟨0, ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩⟩
    · simp
    · simp
    · simp [hc]

@[simp] theorem mem_slabBody {d : ℕ} {N : Fin d → ℕ} {a : Fin d → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (x : Fin d → ℝ) :
    x ∈ slabBody N a hc ↔ x ∈ realBox N ∧ |∑ i, a i * x i| ≤ c :=
  Iff.rfl

/-- Integer membership in the slab body is the integer box-and-slab condition. -/
theorem realPoint_mem_slabBody_iff {d : ℕ} {N : Fin d → ℕ} {a : Fin d → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (z : Fin d → ℤ) :
    External.realPoint z ∈ slabBody N a hc ↔
      (z ∈ coordinateBox N ∧ |∑ i, a i * (z i : ℝ)| ≤ c) := by
  rw [mem_slabBody]
  constructor
  · rintro ⟨⟨h1, h2⟩, hzslab⟩
    refine ⟨mem_coordinateBox.mpr fun i => ⟨?_, ?_⟩, hzslab⟩
    · have hcast : -(N i : ℝ) ≤ (z i : ℝ) := h1 i
      exact_mod_cast hcast
    · have hcast : (z i : ℝ) ≤ (N i : ℝ) := h2 i
      exact_mod_cast hcast
  · rintro ⟨hzbox, hzslab⟩
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, hzslab⟩
    · have := (mem_coordinateBox.mp hzbox i).1
      show -(N i : ℝ) ≤ (z i : ℝ)
      exact_mod_cast this
    · have := (mem_coordinateBox.mp hzbox i).2
      show (z i : ℝ) ≤ (N i : ℝ)
      exact_mod_cast this

/-- The slab body is symmetric. -/
theorem slabBody_neg_mem {d : ℕ} {N : Fin d → ℕ} {a : Fin d → ℝ} {c : ℝ}
    (hc : 0 ≤ c) {x : Fin d → ℝ} (hx : x ∈ slabBody N a hc) :
    -x ∈ slabBody N a hc := by
  obtain ⟨⟨h1, h2⟩, hs⟩ := hx
  refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
  · show -(N i : ℝ) ≤ (-x) i
    have := h2 i; simp only [Pi.neg_apply]; linarith
  · show (-x) i ≤ (N i : ℝ)
    have := h1 i; simp only [Pi.neg_apply]; linarith
  · rw [show ∑ i, a i * (-x) i = -(∑ i, a i * x i) from by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp [Pi.neg_apply]]
    rwa [abs_neg]

end SlabBody

section SlabCount

open MeasureTheory

/-- **Slab count, full-rank case** (`lem:slab-count`, r = d): the integer
points of a central slab of relative width `τ` inside the box number at most
`C·dτ·|B|`, provided they span `ℝ^d`.  Combines E5
(`full_rank_lattice_points_le_volume`) with the shear volume bound. -/
theorem slab_count_full_rank (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : Fin d → ℕ) (a : Fin d → ℝ) (τ : ℝ), 0 ≤ τ →
      ∀ hw : 0 < ∑ i, |a i| * (N i : ℝ),
      ∀ (A : Finset (Fin d → ℤ)),
        (∀ z, z ∈ A ↔ (z ∈ coordinateBox N ∧
          |∑ i, a i * (z i : ℝ)| ≤ τ * ∑ i, |a i| * (N i : ℝ))) →
        Submodule.span ℝ (External.realPoint '' (A : Set (Fin d → ℤ))) = ⊤ →
        (A.card : ℝ) ≤ C * (d * τ) * ((coordinateBox N).card : ℝ) := by
  classical
  obtain ⟨C, hC, hE5⟩ := External.full_rank_lattice_points_le_volume d
  refine ⟨(C : ℝ) + 1, by positivity, ?_⟩
  intro N a τ hτ hw A hAmem hAspan
  set w : ℝ := ∑ i, |a i| * (N i : ℝ) with hwdef
  have hτw : 0 ≤ τ * w := mul_nonneg hτ (le_of_lt hw)
  -- Membership matches the convex body.
  have hbodymem : ∀ z, z ∈ A ↔ External.realPoint z ∈ slabBody N a hτw := by
    intro z
    rw [hAmem z, mem_slabBody]
    constructor
    · rintro ⟨hzbox, hzslab⟩
      refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
      · have := (mem_coordinateBox.mp hzbox i).1
        show -(N i : ℝ) ≤ (z i : ℝ)
        exact_mod_cast this
      · have := (mem_coordinateBox.mp hzbox i).2
        show (z i : ℝ) ≤ (N i : ℝ)
        exact_mod_cast this
      · exact hzslab
    · rintro ⟨⟨h1, h2⟩, hzslab⟩
      refine ⟨mem_coordinateBox.mpr fun i => ⟨?_, ?_⟩, hzslab⟩
      · have hcast : -(N i : ℝ) ≤ (z i : ℝ) := h1 i
        exact_mod_cast hcast
      · have hcast : (z i : ℝ) ≤ (N i : ℝ) := h2 i
        exact_mod_cast hcast
  -- Symmetry of the body.
  have hsymm : ∀ x ∈ (slabBody N a hτw : Set (Fin d → ℝ)), -x ∈ slabBody N a hτw := by
    rintro x ⟨⟨h1, h2⟩, hs⟩
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
    · show -(N i : ℝ) ≤ (-x) i
      have := h2 i; simp only [Pi.neg_apply]; linarith
    · show (-x) i ≤ (N i : ℝ)
      have := h1 i; simp only [Pi.neg_apply]; linarith
    · rw [show ∑ i, a i * (-x) i = -(∑ i, a i * x i) from by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by simp [Pi.neg_apply]]
      rwa [abs_neg]
  -- E5 count.
  have hcount := hE5 (slabBody N a hτw) A hsymm hbodymem hAspan
  -- Volume bound (choose the pigeonhole coordinate).
  obtain ⟨j, haj, hjw⟩ := exists_width_coordinate a N hw
  have hvol : volume ((slabBody N a hτw : Set (Fin d → ℝ)))
      ≤ ENNReal.ofReal ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) :=
    volume_slab_inter_box_le N a j haj hτ (le_of_lt hw) hjw
  -- Assemble into a real inequality.
  have hchain : (A.card : ENNReal)
      ≤ (C : ENNReal) * ENNReal.ofReal ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) :=
    le_trans hcount (mul_le_mul_left' hvol _)
  have hboxprod : (2 : ℝ) ^ d * ∏ i, (N i : ℝ) ≤ ((coordinateBox N).card : ℝ) := by
    rw [card_coordinateBox]
    push_cast
    rw [show ((2 : ℝ)) ^ d * ∏ i, (N i : ℝ) = ∏ i, (2 * (N i : ℝ)) from by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    exact Finset.prod_le_prod (fun i _ => by positivity)
      (fun i _ => by linarith [Nat.cast_nonneg (α := ℝ) (N i)])
  -- Convert `hchain` to reals.
  have hrhs_ne_top : (C : ENNReal) * ENNReal.ofReal ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ)))
      ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hreal : (A.card : ℝ) ≤ (C : ℝ) * ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) := by
    have := ENNReal.toReal_mono hrhs_ne_top hchain
    rw [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  calc (A.card : ℝ)
      ≤ (C : ℝ) * ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) := hreal
    _ = (C : ℝ) * (d * τ) * (2 ^ d * ∏ i, (N i : ℝ)) := by ring
    _ ≤ ((C : ℝ) + 1) * (d * τ) * ((coordinateBox N).card : ℝ) := by
        have h2 : (0 : ℝ) ≤ 2 ^ d * ∏ i, (N i : ℝ) := by positivity
        have hC1 : (C : ℝ) ≤ (C : ℝ) + 1 := by linarith
        have hdτ : (0 : ℝ) ≤ (d : ℝ) * τ := by positivity
        have hBnn : (0 : ℝ) ≤ ((coordinateBox N).card : ℝ) := Nat.cast_nonneg _
        calc (C : ℝ) * (d * τ) * (2 ^ d * ∏ i, (N i : ℝ))
            ≤ (C : ℝ) * (d * τ) * ((coordinateBox N).card : ℝ) :=
              mul_le_mul_of_nonneg_left hboxprod (by positivity)
          _ ≤ ((C : ℝ) + 1) * (d * τ) * ((coordinateBox N).card : ℝ) := by
              apply mul_le_mul_of_nonneg_right _ hBnn
              exact mul_le_mul_of_nonneg_right hC1 hdτ

/-- **Slab count** (`lem:slab-count`, both cases).  The integer points `S` of a
central slab of relative width `τ` in the box lie in a proper symmetric rank-`r`
GAP `Q` with `|Q| ≤ C|B|` always, and `|Q| ≤ C·dτ·|B|` when `r = d`.  The John
placement is E2 on the slab body sectioned by `H = span_ℝ S`; the `r = d` count
is `slab_count_full_rank` (E5 + shear). -/
theorem slab_count (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : Fin d → ℕ) (a : Fin d → ℝ) (τ : ℝ), 0 ≤ τ →
      ∀ hw : 0 < ∑ i, |a i| * (N i : ℝ),
      ∀ (S : Finset (Fin d → ℤ)),
        (∀ z, z ∈ S ↔ (z ∈ coordinateBox N ∧
          |∑ i, a i * (z i : ℝ)| ≤ τ * ∑ i, |a i| * (N i : ℝ))) →
        ∃ (r : ℕ) (Q : GAP d r), r ≤ d ∧ Q.Proper ∧ S ⊆ Q.carrier ∧
          (Q.carrier.card : ℝ) ≤ C * ((coordinateBox N).card : ℝ) ∧
          (r = d → (Q.carrier.card : ℝ)
            ≤ C * (d * τ) * ((coordinateBox N).card : ℝ)) := by
  classical
  obtain ⟨cJ, hcJ, CJ, hCJ, hE2⟩ := External.discrete_john d
  obtain ⟨CS, hCS, hcount⟩ := slab_count_full_rank d
  refine ⟨(CJ : ℝ) * (CS + 1), by positivity, ?_⟩
  intro N a τ hτ hw S hSmem
  set w : ℝ := ∑ i, |a i| * (N i : ℝ) with hwdef
  have hτw : 0 ≤ τ * w := mul_nonneg hτ (le_of_lt hw)
  set H := External.integerRealSpan S with hHdef
  set K : Set (Fin d → ℝ) := (slabBody N a hτw : Set (Fin d → ℝ)) ∩ H with hKdef
  -- E2 hypotheses.
  have hcompact : IsCompact K :=
    ((slabBody N a hτw).isCompact').inter_right H.closed_of_finiteDimensional
  have hconvex : Convex ℝ K := ((slabBody N a hτw).convex').inter H.convex
  have hsymmK : ∀ x, x ∈ K ↔ -x ∈ K := by
    intro x
    constructor
    · rintro ⟨hb, hH⟩
      exact ⟨slabBody_neg_mem hτw hb, H.neg_mem hH⟩
    · rintro ⟨hb, hH⟩
      have h1 := slabBody_neg_mem hτw hb
      have h2 := H.neg_mem hH
      rw [neg_neg] at h1 h2
      exact ⟨h1, h2⟩
  have hKH : K ⊆ (H : Set (Fin d → ℝ)) := Set.inter_subset_right
  have hzK : ∀ z, z ∈ S ↔ External.realPoint z ∈ K := by
    intro z
    constructor
    · intro hz
      refine ⟨(realPoint_mem_slabBody_iff hτw z).mpr ((hSmem z).mp hz), ?_⟩
      exact Submodule.subset_span ⟨z, hz, rfl⟩
    · rintro ⟨hb, _⟩
      exact (hSmem z).mpr ((realPoint_mem_slabBody_iff hτw z).mp hb)
  -- E2 John placement.
  obtain ⟨Q, _hQsteps, hQprop, _hQinner, hQouter, hQcard⟩ :=
    hE2 (Module.finrank ℝ H) H K S rfl hcompact hconvex hsymmK hKH hzK rfl
      ⟨0, (by
        change (0 : Fin d → ℝ) ∈ realBox N ∧ |∑ i, a i * (0 : Fin d → ℝ) i| ≤ τ * w
        exact ⟨⟨fun i => by simp, fun i => by simp⟩, by simpa using hτw⟩), H.zero_mem⟩
  have hrle : Module.finrank ℝ H ≤ d := by
    have := Submodule.finrank_le H
    rwa [Module.finrank_pi ℝ, Fintype.card_fin] at this
  refine ⟨Module.finrank ℝ H, Q, hrle, hQprop, hQouter, ?_, ?_⟩
  -- Common facts.
  all_goals
    have hSbox : S ⊆ coordinateBox N := fun z hz => ((hSmem z).mp hz).1
    have hSB : (S.card : ℝ) ≤ ((coordinateBox N).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSbox
    have hQS : (Q.carrier.card : ℝ) ≤ (CJ : ℝ) * (S.card : ℝ) := by
      exact_mod_cast hQcard
    have hCJ1 : (1 : ℝ) ≤ CS + 1 := by linarith
  -- Unconditional bound `|Q| ≤ CJ(CS+1)|B|`.
  · calc (Q.carrier.card : ℝ)
        ≤ (CJ : ℝ) * (S.card : ℝ) := hQS
      _ ≤ (CJ : ℝ) * ((coordinateBox N).card : ℝ) :=
          mul_le_mul_of_nonneg_left hSB (Nat.cast_nonneg _)
      _ ≤ (CJ : ℝ) * (CS + 1) * ((coordinateBox N).card : ℝ) := by
          have hBnn : (0 : ℝ) ≤ ((coordinateBox N).card : ℝ) := Nat.cast_nonneg _
          nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) CJ) hCS.le) hBnn]
  -- Full-rank bound.
  · intro hr
    have hHtop : H = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hr, Module.finrank_pi ℝ]
      simp
    have hspanS : External.integerRealSpan S = ⊤ := by rw [← hHdef]; exact hHtop
    have hScount : (S.card : ℝ) ≤ CS * (d * τ) * ((coordinateBox N).card : ℝ) :=
      hcount N a τ hτ hw S hSmem hspanS
    calc (Q.carrier.card : ℝ)
        ≤ (CJ : ℝ) * (S.card : ℝ) := hQS
      _ ≤ (CJ : ℝ) * (CS * (d * τ) * ((coordinateBox N).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hScount (Nat.cast_nonneg _)
      _ ≤ (CJ : ℝ) * (CS + 1) * (d * τ) * ((coordinateBox N).card : ℝ) := by
          have hBnn : (0 : ℝ) ≤ ((coordinateBox N).card : ℝ) := Nat.cast_nonneg _
          have hdτ : (0 : ℝ) ≤ (d : ℝ) * τ := by positivity
          nlinarith [Nat.cast_nonneg (α := ℝ) CJ, mul_nonneg hdτ hBnn]

end SlabCount

end Nondividing
