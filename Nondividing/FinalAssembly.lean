import Nondividing.MuSupplier
import Nondividing.DescentInterface
import Nondividing.PrepPrimed

open scoped BigOperators

namespace Nondividing

/-!
# Final assembly (Phase Z): `DescentSupplier` and the main theorem

Couples the two discharged suppliers for every excess parameter `ζ₀ > 0`:

* `ζ₀ ≥ 4/5` — vacuous (`descentStep_of_large_zeta`);
* `ζ₀ < 4/5` — fix `β := 12`, packages from E1 (`nonempty_package`), the
  common dimension cap `Dcap := max 2 (⌈2/ζ₀⌉₊ + 13)`, the numerology
  constants at `Dcap` (`numerology`, `exists_sigma_gap`), the μ-supplier
  radius `δ₀` (`muSupplier_discharge`, at `eps := ζ₀/4`), then `δ`, the
  preprocessing parameters (the `hPP` hypothesis — `prepSupplier'_params`),
  an explicit threshold `n₁`, and `descentStep_of_primed`.

The only remaining input is `hPP`, the primed preprocessing supplier
(discharged in `PrepPrimed.lean`).
-/

/-- The shape of the primed preprocessing supplier (`prepSupplier'_params`,
with the dimension cap as an input). -/
def PrepPrimedHypothesis : Prop :=
  ∀ (β : ℝ) (pkgs : ∀ r, Package r β) (Dcap : ℕ) (ζ₀ ε₁ δ : ℝ),
    2 ≤ Dcap → 2 / ζ₀ ≤ (Dcap : ℝ) → 2 / ζ₀ + 10 ≤ (Dcap : ℝ) →
    0 < ζ₀ → 0 < ε₁ → 0 < δ → δ ≤ 1 / 2 →
    ∃ (ε γ K₀ Cdown : ℝ), 0 < ε ∧ 2 * ε ≤ ε₁ ∧ ε < 1 / 2 ∧
      (5 : ℝ) ≤ K₀ ∧ 0 < γ ∧ γ < 1 ∧ 1 ≤ Cdown ∧
      ∃ n₂ : ℕ, ∀ n₁ : ℕ, n₂ ≤ n₁ →
        PrepSupplier' pkgs Dcap ζ₀ ε δ γ K₀ Cdown n₁

/-- **The descent supplier, unconditionally modulo `hPP`.** -/
theorem descentSupplier_of_prepPrimed (hPP : PrepPrimedHypothesis) :
    DescentSupplier := by
  intro ζ₀ hζ₀
  rcases le_or_gt (4 / 5) ζ₀ with h45 | h45
  · exact ⟨1, 0, one_pos, descentStep_of_large_zeta h45⟩
  -- Packages at `β = 12`.
  set β : ℝ := 12 with hβdef
  have hβ1 : (1 : ℝ) < β := by rw [hβdef]; norm_num
  have hβ6 : (6 : ℝ) ≤ β := by rw [hβdef]; norm_num
  set pkgs : ∀ r, Package r β :=
    fun r => Classical.choice (nonempty_package r β hβ1) with hpkgsdef
  -- The common dimension cap.
  set Dcap : ℕ := max 2 (⌈2 / ζ₀⌉₊ + 13) with hDdef
  have hD2 : 2 ≤ Dcap := le_max_left _ _
  have hceil : 2 / ζ₀ ≤ (⌈2 / ζ₀⌉₊ : ℝ) := Nat.le_ceil _
  have hDcast : ((⌈2 / ζ₀⌉₊ + 13 : ℕ) : ℝ) ≤ (Dcap : ℝ) := by
    have h1 : (⌈2 / ζ₀⌉₊ + 13 : ℕ) ≤ Dcap := le_max_right _ _
    exact_mod_cast h1
  have hDζ : 2 / ζ₀ ≤ (Dcap : ℝ) := by
    have h2 : ((⌈2 / ζ₀⌉₊ + 13 : ℕ) : ℝ) = (⌈2 / ζ₀⌉₊ : ℝ) + 13 := by
      push_cast; ring
    linarith [hDcast, h2 ▸ hDcast]
  have hDζ10 : 2 / ζ₀ + 10 ≤ (Dcap : ℝ) := by
    have h2 : ((⌈2 / ζ₀⌉₊ + 13 : ℕ) : ℝ) = (⌈2 / ζ₀⌉₊ : ℝ) + 13 := by
      push_cast; ring
    have h3 := hDcast
    rw [h2] at h3
    linarith
  -- Numerology and the sigma gap at `Dcap`.
  obtain ⟨ε₀, cstar, hε₀0, hcstar0, hnum⟩ := numerology hD2 hζ₀
  obtain ⟨Δ, hΔ0, hgap⟩ := exists_sigma_gap Dcap hD2
  -- The μ-supplier at `eps := ζ₀/4`.
  obtain ⟨δ₀, hδ₀0, hMU⟩ := muSupplier_discharge pkgs hβ6 Dcap ζ₀ (ζ₀ / 4)
    hζ₀ h45 (by positivity) (le_refl _)
  -- The shared density parameter.
  set δ : ℝ := min δ₀ (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₀0 (by norm_num)
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  -- The preprocessing parameters.
  set ε₁ : ℝ := min (min (ε₀ / 2) (cstar / 4)) (min (Δ / 8) (ζ₀ / 2))
    with hε₁def
  have hε₁0 : 0 < ε₁ := by
    apply lt_min (lt_min (by linarith) (by linarith))
      (lt_min (by linarith) (by linarith))
  obtain ⟨ε, γ, K₀, Cdown, hε0, h2ε, hεhalf, hK₀5, hγ0, hγ1, hCd1,
    n₂PP, hprepfam⟩ :=
    hPP β pkgs Dcap ζ₀ ε₁ δ hD2 hDζ hDζ10 hζ₀ hε₁0 hδ0 hδhalf
  -- Epsilon side conditions.
  have hε₁a : ε₁ ≤ ε₀ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε₁b : ε₁ ≤ cstar / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₁c : ε₁ ≤ Δ / 8 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₁d : ε₁ ≤ ζ₀ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hεε₀ : 2 * ε < ε₀ := by linarith
  have hεc : 2 * ε ≤ cstar / 4 := by linarith
  have hεΔ : 2 * ε ≤ Δ / 8 := by linarith
  have hεMU : ε ≤ ζ₀ / 4 := by linarith
  -- The increment family at `(δ, γ)`.
  obtain ⟨C₂, hC₂0, hMUfam⟩ := hMU δ γ hδ0 hδδ₀ hγ0 hγ1
  -- The explicit threshold.
  set cg : ℝ := min (cstar / 10) (Δ / 8) with hcgdef
  have hcg : 0 < cg := lt_min (by positivity) (by positivity)
  have hCd0 : (0 : ℝ) < Cdown := by linarith
  set nabs : ℕ := ⌈Cdown ^ (1 / cg)⌉₊ + 1 with hnabsdef
  set n₁ : ℕ := max (max n₂PP 2) (max (C₂ * C₂) nabs) with hn₁def
  have hn₁2 : 2 ≤ n₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn₁PP : n₂PP ≤ n₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn₁C₂ : C₂ * C₂ ≤ n₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hn₁abs : nabs ≤ n₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  -- `habs : Cdown² ≤ (n₁²)^{cg}`.
  have hCdn₁ : Cdown ≤ (n₁ : ℝ) ^ cg := by
    have h1 : Cdown ^ (1 / cg) ≤ (n₁ : ℝ) := by
      have h2 : (nabs : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast hn₁abs
      have h3 : Cdown ^ (1 / cg) ≤ (nabs : ℝ) := by
        rw [hnabsdef]
        push_cast
        linarith [Nat.le_ceil (Cdown ^ (1 / cg))]
      linarith
    calc Cdown = (Cdown ^ (1 / cg)) ^ cg := by
          rw [← Real.rpow_mul hCd0.le, one_div,
            inv_mul_cancel₀ (ne_of_gt hcg), Real.rpow_one]
      _ ≤ (n₁ : ℝ) ^ cg :=
          Real.rpow_le_rpow (Real.rpow_nonneg hCd0.le _) h1 hcg.le
  have habs : Cdown ^ 2 ≤ ((n₁ * n₁ : ℕ) : ℝ) ^ cg := by
    have hn₁0 : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg _
    have h1 : ((n₁ * n₁ : ℕ) : ℝ) = (n₁ : ℝ) * (n₁ : ℝ) := by push_cast; ring
    rw [h1, Real.mul_rpow hn₁0 hn₁0]
    calc Cdown ^ 2 = Cdown * Cdown := sq Cdown
      _ ≤ (n₁ : ℝ) ^ cg * ((n₁ : ℝ) ^ cg) :=
          mul_le_mul hCdn₁ hCdn₁ hCd0.le (Real.rpow_nonneg hn₁0 _)
  -- The increment at `n₁` and the second-threshold bound at pipeline `ε`.
  obtain ⟨hn₂powMU, hincAll⟩ := hMUfam n₁ hn₁2 hn₁C₂
  have hbase1 : (1 : ℝ) ≤ (n₁ : ℝ) * (n₁ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n₁ : ℝ) := by
      have : (1 : ℕ) ≤ n₁ := by omega
      exact_mod_cast this
    nlinarith
  have hn₂pow : ((C₂ * n₁ : ℕ) : ℝ) ≤
      ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) - ε) := by
    calc ((C₂ * n₁ : ℕ) : ℝ)
        ≤ ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) - ζ₀ / 4) := hn₂powMU
      _ ≤ ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) - ε) :=
          Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith)
  -- Assemble.
  obtain ⟨n₀, hstep⟩ := descentStep_of_primed pkgs Dcap Dcap
    hζ₀ h45 (by positivity) (by linarith) hK₀5 hε0 hεhalf hεε₀ hεc hεΔ
    hcstar0 hΔ0 hD2 hDζ hDζ hgap hnum hCd1 (by rw [← hcgdef]; exact habs)
    hn₁2 hn₂pow (hprepfam n₁ hn₁PP) (hincAll ε)
  exact ⟨1, n₀, one_pos, hstep⟩

/-- **The main theorem, modulo the primed preprocessing supplier**:
`log F(N) / log N → 1/5`. -/
theorem main_log_limit_of_prepPrimed (hPP : PrepPrimedHypothesis) :
    Filter.Tendsto (fun N : ℕ => Real.log (F N) / Real.log N)
      Filter.atTop (nhds ((1 : ℝ) / 5)) :=
  main_log_limit_of_descent (descentSupplier_of_prepPrimed hPP)

/-- The primed preprocessing supplier holds (`prepSupplier'_params`). -/
theorem prepPrimedHypothesis_proved : PrepPrimedHypothesis :=
  fun _β pkgs Dcap ζ₀ ε₁ δ hD2 hDζ hslack hζ₀ hε₁ hδ0 hδhalf =>
    prepSupplier'_params pkgs Dcap ζ₀ ε₁ δ hD2 hDζ hslack hζ₀ hε₁ hδ0 hδhalf

/-- **The descent supplier, unconditionally.** -/
theorem descentSupplier_proved : DescentSupplier :=
  descentSupplier_of_prepPrimed prepPrimedHypothesis_proved

/-- **THE MAIN THEOREM** (`thm:main`, Erdős problem 131): the maximum size
`F(N)` of a non-dividing subset of `[1, N]` satisfies
`log F(N) / log N → 1/5`.  The proof uses seven external axioms
from E1, E2, E4 and E5: Conlon–Fox–Pham structure, discrete John, convex
density and four convex-geometry results. -/
theorem main_log_limit :
    Filter.Tendsto (fun N : ℕ => Real.log (F N) / Real.log N)
      Filter.atTop (nhds ((1 : ℝ) / 5)) :=
  main_log_limit_of_prepPrimed prepPrimedHypothesis_proved

end Nondividing
