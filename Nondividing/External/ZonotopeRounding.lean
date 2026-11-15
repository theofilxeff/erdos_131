import Nondividing.Box
import Nondividing.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace Nondividing.External

def InZonotope {d : ℕ} (A : Finset (Fin d → ℤ)) (z : Fin d → ℝ) : Prop :=
  ∃ t : (Fin d → ℤ) → ℝ,
    (∀ a ∈ A, 0 ≤ t a ∧ t a ≤ 1) ∧
    z = fun i => ∑ a ∈ A, t a * (a i : ℝ)

/-- Move in a direction with nonpositive cross term.  A step of size at
most one raises the squared error by at most the squared direction length. -/
private theorem energy_step {d : ℕ} (e v : Fin d → ℝ) (s : ℝ)
    (hs : s ^ 2 ≤ 1) (hcross : s * (∑ i, e i * v i) ≤ 0) :
    (∑ i, (e i + s * v i) ^ 2) ≤ (∑ i, (e i) ^ 2) + ∑ i, (v i) ^ 2 := by
  have expand (i : Fin d) :
      (e i + s * v i) ^ 2 = (e i) ^ 2 + (2 * s) * (e i * v i) + s ^ 2 * (v i) ^ 2 := by
    ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hlen : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hs hlen]

/-- Deterministic rounding in a coordinate system whose coordinate
magnitudes are at most one.  The sum of squared errors grows by at most
the dimension per rounded vector. -/
private theorem round_normalized {α : Type*} [DecidableEq α] {d : ℕ}
    (v : α → Fin d → ℝ) (t : α → ℝ) (A : Finset α)
    (ht : ∀ a ∈ A, 0 ≤ t a ∧ t a ≤ 1)
    (hv : ∀ a ∈ A, ∀ i, |v a i| ≤ 1) :
    ∃ S ⊆ A, (∑ i : Fin d, ((∑ a ∈ A, t a * v a i) - ∑ a ∈ S, v a i) ^ 2)
      ≤ (A.card : ℝ) * d := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert a A ha ih =>
    have hsub : A ⊆ insert a A := Finset.subset_insert _ _
    obtain ⟨S, hSA, henergy⟩ := ih (fun b hb => ht b (hsub hb)) (fun b hb => hv b (hsub hb))
    let e : Fin d → ℝ := fun i => (∑ b ∈ A, t b * v b i) - ∑ b ∈ S, v b i
    have he : (∑ i, (e i) ^ 2) ≤ (A.card : ℝ) * d := henergy
    have haS : a ∉ S := fun h => ha (hSA h)
    obtain ⟨ht0, ht1⟩ := ht a (Finset.mem_insert_self _ _)
    have hvlen : (∑ i, (v a i) ^ 2) ≤ (d : ℝ) := by
      calc
        _ ≤ ∑ _ : Fin d, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hi := abs_le.mp (hv a (Finset.mem_insert_self _ _) i)
          nlinarith [mul_nonneg (sub_nonneg.mpr hi.2) (sub_nonneg.mpr hi.1)]
        _ = _ := by simp
    by_cases hc : (∑ i, e i * v a i) ≤ 0
    · refine ⟨S, hSA.trans hsub, ?_⟩
      have hstep := energy_step e (v a) (t a)
        (by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)])
        (mul_nonpos_of_nonneg_of_nonpos ht0 hc)
      have hrewrite (i : Fin d) :
          (∑ b ∈ insert a A, t b * v b i) - ∑ b ∈ S, v b i =
            e i + t a * v a i := by
        rw [Finset.sum_insert ha]
        dsimp [e]
        ring
      simp_rw [hrewrite]
      rw [Finset.card_insert_of_notMem ha, Nat.cast_add_one]
      linarith
    · refine ⟨insert a S, Finset.insert_subset_insert _ hSA, ?_⟩
      have hstep := energy_step e (v a) (t a - 1)
        (by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)])
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht1) (le_of_not_ge hc))
      have hrewrite (i : Fin d) :
          (∑ b ∈ insert a A, t b * v b i) - ∑ b ∈ insert a S, v b i =
            e i + (t a - 1) * v a i := by
        rw [Finset.sum_insert ha, Finset.sum_insert haS]
        dsimp [e]
        ring
      simp_rw [hrewrite]
      rw [Finset.card_insert_of_notMem ha, Nat.cast_add_one]
      linarith

/-- Round the coefficients of a point in a zonotope to a subset sum. -/
theorem zonotope_rounding
    {d : ℕ} (A : Finset (Fin d → ℤ)) (M : Fin d → ℕ)
    (hA : A ⊆ coordinateBox M) {z : Fin d → ℝ}
    (hz : InZonotope A z) :
    ∃ S : Finset (Fin d → ℤ), S ⊆ A ∧
      ∀ i,
        |z i - ∑ a ∈ S, (a i : ℝ)| ≤
          Real.sqrt (d * (A ∪ {0}).card) * (2 * M i + 1) := by
  classical
  obtain ⟨t, ht, rfl⟩ := hz
  let w (i : Fin d) : ℝ := 2 * (M i : ℝ) + 1
  have hw (i : Fin d) : 0 < w i := by dsimp [w]; positivity
  let v (a : Fin d → ℤ) (i : Fin d) : ℝ := (a i : ℝ) / w i
  have hv (a) (ha : a ∈ A) (i : Fin d) : |v a i| ≤ 1 := by
    obtain ⟨hl, hu⟩ := (mem_coordinateBox.mp (hA ha)) i
    have hlow : -(M i : ℝ) ≤ (a i : ℝ) := by exact_mod_cast hl
    have hupp : (a i : ℝ) ≤ (M i : ℝ) := by exact_mod_cast hu
    dsimp [v]
    rw [abs_div, abs_of_pos (hw i), div_le_one (hw i)]
    apply abs_le.mpr
    dsimp [w]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (M i)]
  obtain ⟨S, hSA, hbound⟩ := round_normalized v t A ht hv
  refine ⟨S, hSA, ?_⟩
  intro i
  let e (j : Fin d) : ℝ := (∑ a ∈ A, t a * v a j) - ∑ a ∈ S, v a j
  have hei : e i ^ 2 ≤ (A.card : ℝ) * d :=
    (Finset.single_le_sum (f := fun j => e j ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)).trans hbound
  have hcard : A.card ≤ (A ∪ {0}).card := Finset.card_le_card Finset.subset_union_left
  have hsqrt : |e i| ≤ Real.sqrt (d * (A ∪ {0}).card) := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    grw [hei]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)
  have heq : e i = ((∑ a ∈ A, t a * (a i : ℝ)) - ∑ a ∈ S, (a i : ℝ)) / w i := by
    dsimp [e, v]
    simp only [div_eq_mul_inv, sub_mul, Finset.sum_mul, mul_assoc]
  rw [heq, abs_div, abs_of_pos (hw i), div_le_iff₀ (hw i)] at hsqrt
  exact hsqrt

end Nondividing.External
