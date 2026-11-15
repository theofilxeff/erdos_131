import Nondividing.ProjectiveTheorem
import Nondividing.ProjectiveConvexity
import Nondividing.WeightedDensityLimit
import Nondividing.CapLifting
import Nondividing.CapConeVolume
import Nondividing.Projective.AffineSpan
import Nondividing.Projective.Convexity
import Nondividing.Geometry.SlabVolume

open scoped BigOperators Pointwise
open MeasureTheory

namespace Nondividing

open Nondividing.External

/-!
# The irreducible-stage density increment (`IrreducibleIncrement`)

This file discharges the geometric pipeline of the irreducible-stage step
(Manuscript.tex 1941–2024): at an unshiftedly `(δ,γ)`-irreducible stage, the
projective machinery (`weighted_density` in the hyperplane chart
`H_λ ≅ ℝ^{d-1}`, cap lifting through the cone volume count, and slab exclusion
to force full rank) produces a same-dimensional stage with box decay `≤ C·η·|B|`
and retention `≥ η^{κ_{d-1}+ε}·n`.

## Structure

1. **Chart volume machinery** (the `H_λ ≅ ℝ^{d-1}` identification): the
   flat-cone Fubini formula `vol(cone 1 (insertNth j 1 '' F)) = c_r · vol F`
   and its transfer to arbitrary hyperplanes `{λℝ = 1}` through a
   determinant-`ℓⱼ` linear map (diagonal · shear).
2. **The affine chart** `chartProj j` / `chartSec ℓ j` of `H_λ`, the stage
   body `Ω = {y ∈ H_λ : X·y ∈ B_ℝ}` and its chart image, and the transfer of
   `IndexedMuConvexPosition` through the chart.
3. **Span dichotomy**: at an irreducible stage a `δ`-large subset spans `ℝ^d`
   (else it lies in a width-`0` slab, contradicting `slab_exclusion`).
4. **Full-rank cap lifting** (`cap_lifting_full`): the `r = d` alternative of
   `lem:cap-lifting`, with box bound `|B'| ≤ C·η·|B|`, via `discrete_john`
   (E2) on the lattice points of the difference cone body and the
   Rogers–Shephard / lattice-count volume chain (E5c, E5d).
5. **The increment step** (`irreducible_cap_step`) and the assemblies
   `irreducibleIncrement_of_data` / `irreducibleIncrement_of_convexPosition`
   producing the `IrreducibleIncrement` predicate.
-/

/-! ## 1. Cone volumes in a hyperplane chart

The perspective-volume formula (eq:perspective-volume) in ratio-friendly form:
for `E` in the affine hyperplane `{λℝ = 1}`, the cone volume `vol(cone 1 E)`
is a fixed positive multiple (depending only on `λ` and the deleted
coordinate) of the `(d-1)`-dimensional volume of the graph-chart image of
`E`.  We never need the exact constant. -/

/-- Linear images of truncated cones are truncated cones of the image. -/
theorem image_cone {d d' : ℕ} (G : (Fin d → ℝ) →ₗ[ℝ] (Fin d' → ℝ)) (T : ℝ)
    (E : Set (Fin d → ℝ)) : G '' cone T E = cone T (G '' E) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, t, ht0, htT, rfl⟩, rfl⟩
    exact ⟨G y, ⟨y, hy, rfl⟩, t, ht0, htT, map_smul G t y⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, t, ht0, htT, rfl⟩
    exact ⟨t • y, ⟨y, hy, t, ht0, htT, rfl⟩, map_smul G t y⟩

/-- The universal cone constant `c_r = ∫₀¹ t^r dt` (kept abstract). -/
noncomputable def coneConst (r : ℕ) : ENNReal :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (t ^ r)

theorem coneConst_le_one (r : ℕ) : coneConst r ≤ 1 := by
  have hmono : coneConst r ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, (1 : ENNReal) := by
    refine setLIntegral_mono measurable_const ?_
    intro t ht
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_one₀ ht.1 ht.2)
  calc coneConst r ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, (1 : ENNReal) := hmono
    _ = volume (Set.Icc (0 : ℝ) 1) := setLIntegral_one _
    _ = 1 := by rw [Real.volume_Icc]; norm_num

theorem coneConst_ne_top (r : ℕ) : coneConst r ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (coneConst_le_one r)

theorem coneConst_pos (r : ℕ) : 0 < coneConst r := by
  have hsub : Set.Icc (1 / 2 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 :=
    Set.Icc_subset_Icc (by norm_num) le_rfl
  have hlow : ENNReal.ofReal ((1 / 2) ^ r) * volume (Set.Icc (1 / 2 : ℝ) 1) ≤
      coneConst r := by
    rw [← setLIntegral_const]
    calc ∫⁻ _ in Set.Icc (1 / 2 : ℝ) 1, ENNReal.ofReal ((1 / 2) ^ r)
        ≤ ∫⁻ t in Set.Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (t ^ r) := by
          refine setLIntegral_mono
            (by fun_prop) ?_
          intro t ht
          exact ENNReal.ofReal_le_ofReal
            (pow_le_pow_left₀ (by norm_num) ht.1 r)
      _ ≤ coneConst r :=
          lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
  have hpos : (0 : ENNReal) <
      ENNReal.ofReal ((1 / 2) ^ r) * volume (Set.Icc (1 / 2 : ℝ) 1) := by
    rw [Real.volume_Icc]
    apply ENNReal.mul_pos
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      norm_num
  exact lt_of_lt_of_le hpos hlow

/-- **Flat-cone Fubini**: the volume of the truncated cone over a compact set
`F` placed at height `1` in coordinate `j` equals `c_r · vol F`. -/
theorem volume_cone_insertNth {r : ℕ} (j : Fin (r + 1)) {F : Set (Fin r → ℝ)}
    (hFc : IsCompact F) :
    volume (cone 1 (Fin.insertNth j (1 : ℝ) '' F)) = coneConst r * volume F := by
  classical
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) j with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) j
  set C : Set (Fin (r + 1) → ℝ) := cone 1 (Fin.insertNth j (1 : ℝ) '' F)
    with hC
  set Chat : Set (ℝ × (Fin r → ℝ)) :=
    (fun p : ℝ × (Fin r → ℝ) => (p.1, p.1 • p.2)) '' (Set.Icc (0 : ℝ) 1 ×ˢ F)
    with hChat
  -- The key pointwise computation.
  have hesmul : ∀ (t : ℝ) (y : Fin r → ℝ),
      e (t • Fin.insertNth j (1 : ℝ) y) = (t, t • y) := by
    intro t y
    have h1 : (t • Fin.insertNth j (1 : ℝ) y) j = t := by
      rw [Pi.smul_apply, Fin.insertNth_apply_same, smul_eq_mul, mul_one]
    have h2 : j.removeNth (t • Fin.insertNth j (1 : ℝ) y) = t • y := by
      funext k
      rw [Fin.removeNth_apply, Pi.smul_apply, Fin.insertNth_apply_succAbove,
        Pi.smul_apply]
    show ((t • Fin.insertNth j (1 : ℝ) y) j,
      j.removeNth (t • Fin.insertNth j (1 : ℝ) y)) = (t, t • y)
    rw [h1, h2]
  -- `e` maps the cone onto the parameterized region.
  have himg : e '' C = Chat := by
    ext p
    constructor
    · rintro ⟨x, ⟨_, ⟨y, hy, rfl⟩, t, ht0, htT, rfl⟩, rfl⟩
      exact ⟨(t, y), ⟨Set.mem_Icc.mpr ⟨ht0, htT⟩, hy⟩, (hesmul t y).symm⟩
    · rintro ⟨⟨t, y⟩, ⟨htI, hy⟩, rfl⟩
      refine ⟨t • Fin.insertNth j (1 : ℝ) y, ?_, hesmul t y⟩
      exact ⟨Fin.insertNth j (1 : ℝ) y, ⟨y, hy, rfl⟩, t,
        (Set.mem_Icc.mp htI).1, (Set.mem_Icc.mp htI).2, rfl⟩
  -- `Chat` is compact, hence measurable.
  have hChatc : IsCompact Chat := by
    rw [hChat]
    exact (isCompact_Icc.prod hFc).image
      (continuous_fst.prodMk (continuous_fst.smul continuous_snd))
  have hChatm : MeasurableSet Chat := hChatc.isClosed.measurableSet
  -- Transfer the volume through `e`.
  have hCpre : C = e ⁻¹' Chat := by
    rw [← himg, Set.preimage_image_eq _ e.injective]
  have hvolC : volume C = volume Chat := by
    rw [hCpre]
    exact hmp.measure_preimage hChatm.nullMeasurableSet
  -- Fubini for the product region.
  have hsection : ∀ t : ℝ, Prod.mk t ⁻¹' Chat =
      if t ∈ Set.Icc (0 : ℝ) 1 then t • F else ∅ := by
    intro t
    ext z
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · rw [if_pos ht]
      constructor
      · rintro ⟨⟨a, y⟩, ⟨haI, hy⟩, heq⟩
        obtain ⟨h1, h2⟩ := Prod.mk_inj.mp heq
        subst h1
        exact h2 ▸ Set.smul_mem_smul_set hy
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(t, y), ⟨ht, hy⟩, rfl⟩
    · rw [if_neg ht]
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨a, y⟩, ⟨haI, hy⟩, heq⟩
      obtain ⟨h1, _⟩ := Prod.mk_inj.mp heq
      exact ht (h1 ▸ haI)
  have hprod : volume Chat = ∫⁻ t, volume (Prod.mk t ⁻¹' Chat) := by
    rw [Measure.volume_eq_prod, Measure.prod_apply hChatm]
  have hindic : (fun t => volume (Prod.mk t ⁻¹' Chat)) =
      Set.indicator (Set.Icc (0 : ℝ) 1) (fun t => volume (t • F)) := by
    funext t
    rw [hsection t]
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · rw [if_pos ht, Set.indicator_of_mem ht]
    · rw [if_neg ht, Set.indicator_of_notMem ht, measure_empty]
  have hFvol : volume F ≠ ⊤ := hFc.measure_lt_top.ne
  calc volume C = volume Chat := hvolC
    _ = ∫⁻ t, volume (Prod.mk t ⁻¹' Chat) := hprod
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, volume (t • F) := by
        rw [hindic, lintegral_indicator measurableSet_Icc]
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (t ^ r) * volume F := by
        refine setLIntegral_congr_fun measurableSet_Icc ?_
        intro t ht
        show volume (t • F) = ENNReal.ofReal (t ^ r) * volume F
        rw [Measure.addHaar_smul_of_nonneg volume ht.1 F,
          Module.finrank_fin_fun]
    _ = coneConst r * volume F :=
        lintegral_mul_const' (volume F) _ hFvol

/-! ### The hyperplane-to-flat linear map

`hypMatrix ℓ j` fixes all coordinates except `j`, which becomes the value of
the functional `λℝ`; its determinant is `ℓ j`.  It carries `{λℝ = 1}` onto the
flat hyperplane `{x j = 1}` while acting as the identity on the chart
coordinates. -/

/-- Diagonal (coordinate `j` scaled by `ℓ j`) times the determinant-1 shear:
the map `x ↦ x[j := λℝ(x)]`. -/
noncomputable def hypMatrix {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1)) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.diagonal (fun k => if k = j then (ℓ j : ℝ) else 1) *
    shearMatrix (fun i => (ℓ i : ℝ)) j

theorem det_hypMatrix {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1)) :
    (hypMatrix ℓ j).det = (ℓ j : ℝ) := by
  rw [hypMatrix, Matrix.det_mul, det_shearMatrix, mul_one,
    Matrix.det_diagonal]
  rw [Finset.prod_eq_single j (fun k _ hk => if_neg hk)
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [if_pos rfl]

theorem hypMatrix_apply {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (hj : (ℓ j : ℝ) ≠ 0) (x : Fin (r + 1) → ℝ) (k : Fin (r + 1)) :
    Matrix.toLin' (hypMatrix ℓ j) x k =
      if k = j then ∑ i, (ℓ i : ℝ) * x i else x k := by
  rw [hypMatrix, Matrix.toLin'_mul, LinearMap.comp_apply]
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [shear_apply (fun i => (ℓ i : ℝ)) j hj x k]
  by_cases hk : k = j
  · rw [if_pos hk, if_pos hk, if_pos hk, mul_comm, div_mul_cancel₀ _ hj]
  · rw [if_neg hk, if_neg hk, if_neg hk, one_mul]

/-- On the hyperplane `{λℝ = 1}` the map `hypMatrix` agrees with placing the
chart image at height 1 in coordinate `j`. -/
theorem hypMatrix_eq_insertNth {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) (hj : (ℓ j : ℝ) ≠ 0) {x : Fin (r + 1) → ℝ}
    (hx : realFunctional ℓ x = 1) :
    Matrix.toLin' (hypMatrix ℓ j) x =
      Fin.insertNth j (1 : ℝ) (fun k => x (j.succAbove k)) := by
  set S := Matrix.toLin' (hypMatrix ℓ j) with hS
  have h1 : S x j = 1 := by
    rw [hS, hypMatrix_apply ℓ j hj, if_pos rfl]
    rw [realFunctional_apply] at hx
    exact hx
  have h2 : j.removeNth (S x) = fun k => x (j.succAbove k) := by
    funext k
    rw [Fin.removeNth_apply, hS, hypMatrix_apply ℓ j hj,
      if_neg (Fin.succAbove_ne j k)]
  calc S x = Fin.insertNth j (S x j) (j.removeNth (S x)) :=
        (Fin.insertNth_self_removeNth j (S x)).symm
    _ = Fin.insertNth j (1 : ℝ) (fun k => x (j.succAbove k)) := by
        rw [h1, h2]

/-- The chart projection deleting coordinate `j` (as a plain function). -/
def chartProj {r : ℕ} (j : Fin (r + 1)) (x : Fin (r + 1) → ℝ) : Fin r → ℝ :=
  fun k => x (j.succAbove k)

theorem continuous_chartProj {r : ℕ} (j : Fin (r + 1)) :
    Continuous (chartProj j) :=
  continuous_pi fun k => continuous_apply (j.succAbove k)

/-- The chart projection as a linear map. -/
def chartProjL {r : ℕ} (j : Fin (r + 1)) :
    (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun := chartProj j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem chartProjL_apply {r : ℕ} (j : Fin (r + 1))
    (x : Fin (r + 1) → ℝ) : chartProjL j x = chartProj j x := rfl

/-- **Cone volume through the hyperplane chart** (eq:perspective-volume,
ratio form): for compact `E ⊆ {λℝ = 1}`,
`|ℓⱼ| · vol(cone 1 E) = c_r · vol(chartProj j '' E)`. -/
theorem volume_cone_hyperplane {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) (hj : ℓ j ≠ 0) {E : Set (Fin (r + 1) → ℝ)}
    (hEc : IsCompact E) (hE1 : ∀ x ∈ E, realFunctional ℓ x = 1) :
    ENNReal.ofReal |(ℓ j : ℝ)| * volume (cone 1 E) =
      coneConst r * volume (chartProj j '' E) := by
  have hjR : (ℓ j : ℝ) ≠ 0 := by exact_mod_cast hj
  set S := Matrix.toLin' (hypMatrix ℓ j) with hS
  have himg : S '' E = Fin.insertNth j (1 : ℝ) '' (chartProj j '' E) := by
    rw [← Set.image_comp]
    apply Set.image_congr
    intro x hx
    exact hypMatrix_eq_insertNth ℓ j hjR (hE1 x hx)
  have hdet : LinearMap.det S = (ℓ j : ℝ) := by
    rw [hS, LinearMap.det_toLin', det_hypMatrix]
  have hchartc : IsCompact (chartProj j '' E) :=
    hEc.image (continuous_chartProj j)
  calc ENNReal.ofReal |(ℓ j : ℝ)| * volume (cone 1 E)
      = volume (S '' cone 1 E) := by
        rw [Measure.addHaar_image_linearMap, hdet]
    _ = volume (cone 1 (S '' E)) := by rw [image_cone]
    _ = volume (cone 1 (Fin.insertNth j (1 : ℝ) '' (chartProj j '' E))) := by
        rw [himg]
    _ = coneConst r * volume (chartProj j '' E) :=
        volume_cone_insertNth j hchartc

/-- **Cone volume ratio transfer**: a volume ratio in the chart transfers to
the ambient cone volumes. -/
theorem cone_volume_ratio {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (hj : ℓ j ≠ 0) {E' E : Set (Fin (r + 1) → ℝ)} (hE'c : IsCompact E')
    (hEc : IsCompact E) (hE'1 : ∀ x ∈ E', realFunctional ℓ x = 1)
    (hE1 : ∀ x ∈ E, realFunctional ℓ x = 1) {η : ℝ}
    (hvol : volume (chartProj j '' E') ≤
      ENNReal.ofReal η * volume (chartProj j '' E)) :
    volume (cone 1 E') ≤ ENNReal.ofReal η * volume (cone 1 E) := by
  have hjR : (ℓ j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hne0 : ENNReal.ofReal |(ℓ j : ℝ)| ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr hjR
  have hnetop : ENNReal.ofReal |(ℓ j : ℝ)| ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← ENNReal.mul_le_mul_iff_right hne0 hnetop]
  calc ENNReal.ofReal |(ℓ j : ℝ)| * volume (cone 1 E')
      = coneConst r * volume (chartProj j '' E') :=
        volume_cone_hyperplane ℓ j hj hE'c hE'1
    _ ≤ coneConst r * (ENNReal.ofReal η * volume (chartProj j '' E)) :=
        mul_le_mul' le_rfl hvol
    _ = ENNReal.ofReal η * (coneConst r * volume (chartProj j '' E)) := by
        ring
    _ = ENNReal.ofReal η * (ENNReal.ofReal |(ℓ j : ℝ)| * volume (cone 1 E)) := by
        rw [volume_cone_hyperplane ℓ j hj hEc hE1]
    _ = ENNReal.ofReal |(ℓ j : ℝ)| * (ENNReal.ofReal η * volume (cone 1 E)) := by
        ring

/-! ## 2. The affine chart of `H_λ = {λℝ = 1}`

`chartProj j` deletes coordinate `j`; `chartSec ℓ j` is its affine section
landing in the hyperplane.  Convexity, compactness, and the indexed
`μ`-convex-position predicate all transfer through the chart. -/

/-- A pointwise recognition principle for `insertNth`. -/
theorem insertNth_eq_of {r : ℕ} {j : Fin (r + 1)} {a : ℝ} {y : Fin r → ℝ}
    {x : Fin (r + 1) → ℝ} (h1 : x j = a)
    (h2 : ∀ k, x (j.succAbove k) = y k) :
    Fin.insertNth j a y = x := by
  have hy : y = j.removeNth x := funext fun k => (h2 k).symm
  rw [← h1, hy]
  exact Fin.insertNth_self_removeNth j x

/-- The affine section of the chart: the unique point of `{λℝ = 1}` above a
chart point. -/
noncomputable def chartSec {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (y : Fin r → ℝ) : Fin (r + 1) → ℝ :=
  Fin.insertNth j
    ((1 - ∑ k, (ℓ (j.succAbove k) : ℝ) * y k) / (ℓ j : ℝ)) y

@[simp] theorem chartProj_apply {r : ℕ} (j : Fin (r + 1))
    (x : Fin (r + 1) → ℝ) (k : Fin r) :
    chartProj j x k = x (j.succAbove k) := rfl

@[simp] theorem chartSec_apply_same {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) (y : Fin r → ℝ) :
    chartSec ℓ j y j =
      (1 - ∑ k, (ℓ (j.succAbove k) : ℝ) * y k) / (ℓ j : ℝ) :=
  Fin.insertNth_apply_same j _ _

@[simp] theorem chartSec_apply_succAbove {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) (y : Fin r → ℝ) (k : Fin r) :
    chartSec ℓ j y (j.succAbove k) = y k :=
  Fin.insertNth_apply_succAbove j _ _ _

theorem chartProj_chartSec {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (y : Fin r → ℝ) : chartProj j (chartSec ℓ j y) = y := by
  funext k
  rw [chartProj_apply, chartSec_apply_succAbove]

theorem realFunctional_chartSec {r : ℕ} {ℓ : Fin (r + 1) → ℤ}
    {j : Fin (r + 1)} (hj : (ℓ j : ℝ) ≠ 0) (y : Fin r → ℝ) :
    realFunctional ℓ (chartSec ℓ j y) = 1 := by
  rw [realFunctional_apply,
    Fin.sum_univ_succAbove (fun i => (ℓ i : ℝ) * chartSec ℓ j y i) j,
    chartSec_apply_same]
  have hsum : ∑ k, (ℓ (j.succAbove k) : ℝ) * chartSec ℓ j y (j.succAbove k)
      = ∑ k, (ℓ (j.succAbove k) : ℝ) * y k :=
    Finset.sum_congr rfl fun k _ => by rw [chartSec_apply_succAbove]
  rw [hsum, mul_comm, div_mul_cancel₀ _ hj]
  ring

theorem chartSec_chartProj {r : ℕ} {ℓ : Fin (r + 1) → ℤ}
    {j : Fin (r + 1)} (hj : (ℓ j : ℝ) ≠ 0) {x : Fin (r + 1) → ℝ}
    (hx : realFunctional ℓ x = 1) : chartSec ℓ j (chartProj j x) = x := by
  rw [realFunctional_apply,
    Fin.sum_univ_succAbove (fun i => (ℓ i : ℝ) * x i) j] at hx
  refine insertNth_eq_of ?_ (fun k => rfl)
  have hsum : ∑ k, (ℓ (j.succAbove k) : ℝ) * chartProj j x k
      = ∑ k, (ℓ (j.succAbove k) : ℝ) * x (j.succAbove k) := rfl
  rw [hsum]
  rw [eq_comm, div_eq_iff hj]
  linear_combination -hx

/-- The linear part of the section. -/
noncomputable def chartSecL {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1)) :
    (Fin r → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ) where
  toFun y := Fin.insertNth j
    ((-(∑ k, (ℓ (j.succAbove k) : ℝ) * y k)) / (ℓ j : ℝ)) y
  map_add' y z := by
    refine insertNth_eq_of ?_ (fun k => ?_)
    · rw [Pi.add_apply, Fin.insertNth_apply_same, Fin.insertNth_apply_same]
      rw [← add_div]
      congr 1
      rw [← neg_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Pi.add_apply]; ring
    · rw [Pi.add_apply, Fin.insertNth_apply_succAbove,
        Fin.insertNth_apply_succAbove]
      rfl
  map_smul' c y := by
    refine insertNth_eq_of ?_ (fun k => ?_)
    · show (c • Fin.insertNth j
        ((-(∑ k, (ℓ (j.succAbove k) : ℝ) * y k)) / (ℓ j : ℝ)) y) j = _
      rw [Pi.smul_apply, Fin.insertNth_apply_same, smul_eq_mul]
      have hsum : ∑ k, (ℓ (j.succAbove k) : ℝ) * (c • y) k
          = c * ∑ k, (ℓ (j.succAbove k) : ℝ) * y k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [Pi.smul_apply, smul_eq_mul]; ring
      rw [hsum]
      ring
    · show (c • Fin.insertNth j
        ((-(∑ k, (ℓ (j.succAbove k) : ℝ) * y k)) / (ℓ j : ℝ)) y)
        (j.succAbove k) = (c • y) k
      rw [Pi.smul_apply, Fin.insertNth_apply_succAbove]
      rfl

theorem chartSecL_apply {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (y : Fin r → ℝ) :
    chartSecL ℓ j y = Fin.insertNth j
      ((-(∑ k, (ℓ (j.succAbove k) : ℝ) * y k)) / (ℓ j : ℝ)) y := rfl

/-- The affine decomposition `chartSec y = chartSec 0 + chartSecL y`. -/
theorem chartSec_eq_add {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (y : Fin r → ℝ) :
    chartSec ℓ j y = chartSec ℓ j 0 + chartSecL ℓ j y := by
  refine insertNth_eq_of ?_ (fun k => ?_)
  · rw [Pi.add_apply, chartSec_apply_same, chartSecL_apply,
      Fin.insertNth_apply_same, ← add_div]
    congr 1
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    ring
  · rw [Pi.add_apply, chartSec_apply_succAbove, chartSecL_apply,
      Fin.insertNth_apply_succAbove, Pi.zero_apply, zero_add]

theorem continuous_chartSec {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) : Continuous (chartSec ℓ j) := by
  have : chartSec ℓ j = fun y => chartSec ℓ j 0 + chartSecL ℓ j y :=
    funext fun y => chartSec_eq_add ℓ j y
  rw [this]
  exact continuous_const.add (chartSecL ℓ j).continuous_of_finiteDimensional

theorem convex_chartSec_image {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) {K : Set (Fin r → ℝ)} (hK : Convex ℝ K) :
    Convex ℝ (chartSec ℓ j '' K) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩ a b ha hb hab
  refine ⟨a • u + b • w, hK hu hw ha hb hab, ?_⟩
  rw [chartSec_eq_add ℓ j (a • u + b • w), chartSec_eq_add ℓ j u,
    chartSec_eq_add ℓ j w, map_add, map_smul, map_smul]
  have hc : a • chartSec ℓ j 0 + b • chartSec ℓ j 0 = chartSec ℓ j 0 := by
    rw [← add_smul, hab, one_smul]
  calc chartSec ℓ j 0 + (a • chartSecL ℓ j u + b • chartSecL ℓ j w)
      = (a • chartSec ℓ j 0 + b • chartSec ℓ j 0) +
        (a • chartSecL ℓ j u + b • chartSecL ℓ j w) := by rw [hc]
    _ = a • (chartSec ℓ j 0 + chartSecL ℓ j u) +
        b • (chartSec ℓ j 0 + chartSecL ℓ j w) := by
        rw [smul_add, smul_add]; abel

/-- Transfer of indexed `μ`-convex position through the chart: half-spaces of
the chart pull back to half-spaces of the ambient space along the affine
section. -/
theorem indexedMuConvexPosition_chartProj {r : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {μ : ℝ} {ℓ : Fin (r + 1) → ℤ} {j : Fin (r + 1)}
    (hj : (ℓ j : ℝ) ≠ 0) {p : ι → Fin (r + 1) → ℝ}
    (hp : ∀ i, realFunctional ℓ (p i) = 1)
    (h : IndexedMuConvexPosition μ p) :
    IndexedMuConvexPosition μ (fun i => chartProj j (p i)) := by
  intro i
  obtain ⟨u, t, hti, hcount⟩ := h i
  have hkey : ∀ k, u (chartSecL ℓ j (chartProj j (p k)))
      = u (p k) - u (chartSec ℓ j 0) := by
    intro k
    have h1 : chartSec ℓ j (chartProj j (p k)) = p k :=
      chartSec_chartProj hj (hp k)
    have h2 : chartSecL ℓ j (chartProj j (p k))
        = p k - chartSec ℓ j 0 := by
      have hd := chartSec_eq_add ℓ j (chartProj j (p k))
      rw [h1] at hd
      rw [eq_sub_iff_add_eq]
      exact (add_comm _ _).trans hd.symm
    rw [h2, map_sub]
  refine ⟨u ∘ₗ chartSecL ℓ j, t - u (chartSec ℓ j 0), ?_, ?_⟩
  · rw [LinearMap.comp_apply, hkey i]
    exact sub_le_sub_right hti _
  · have hfe : (Finset.univ.filter fun k =>
        t - u (chartSec ℓ j 0) ≤ (u ∘ₗ chartSecL ℓ j) (chartProj j (p k)))
        = Finset.univ.filter fun k => t ≤ u (p k) := by
      refine Finset.filter_congr fun k _ => ?_
      rw [LinearMap.comp_apply, hkey k]
      exact sub_le_sub_iff_right _
    rw [hfe]
    exact hcount

/-- Reindexing an indexed `μ`-convex-position family along an equivalence. -/
theorem IndexedMuConvexPosition.comp_equiv {r : ℕ} {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] {μ : ℝ}
    {p : ι → Fin r → ℝ} (h : IndexedMuConvexPosition μ p) (e : κ ≃ ι) :
    IndexedMuConvexPosition μ (fun k => p (e k)) := by
  intro k
  obtain ⟨u, t, ht, hc⟩ := h (e k)
  refine ⟨u, t, ht, ?_⟩
  have hcard : (Finset.univ.filter fun k' : κ => t ≤ u (p (e k'))).card
      = (Finset.univ.filter fun i : ι => t ≤ u (p i)).card := by
    refine Finset.card_bij (fun k' _ => e k') ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha
    · intro a _ b _ hab
      exact e.injective hab
    · intro b hb
      refine ⟨e.symm b, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simpa using hb
  rw [hcard, show (Fintype.card κ) = Fintype.card ι from Fintype.card_congr e]
  exact hc

/-! ### The stage body `Ω = {y ∈ H_λ : X·y ∈ B_ℝ}` -/

/-- The stage body: points of the hyperplane whose `X`-dilate lies in the
real coordinate box. -/
def stageOmega {d : ℕ} (ℓ : Fin d → ℤ) (X : ℕ) (M : Fin d → ℕ) :
    Set (Fin d → ℝ) :=
  {x | realFunctional ℓ x = 1 ∧ (X : ℝ) • x ∈ realCoordinateBox M}

theorem stageOmega_convex {d : ℕ} (ℓ : Fin d → ℤ) (X : ℕ) (M : Fin d → ℕ) :
    Convex ℝ (stageOmega ℓ X M) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [map_add, map_smul, map_smul, hx.1, hy.1, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one, hab]
  · have hrw : (X : ℝ) • (a • x + b • y)
        = a • ((X : ℝ) • x) + b • ((X : ℝ) • y) := by
      rw [smul_add, smul_comm (X : ℝ) a x, smul_comm (X : ℝ) b y]
    rw [hrw]
    exact (realCoordinateBox_convex M) hx.2 hy.2 ha hb hab

theorem stageOmega_subset_box {d : ℕ} {ℓ : Fin d → ℤ} {X : ℕ}
    {M : Fin d → ℕ} (hX : 1 ≤ X) :
    stageOmega ℓ X M ⊆ realCoordinateBox M := by
  intro x hx
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  rw [mem_realCoordinateBox]
  intro i
  have hb := (mem_realCoordinateBox.mp hx.2) i
  rw [Pi.smul_apply, smul_eq_mul] at hb
  have hM : (0 : ℝ) ≤ (M i : ℝ) := Nat.cast_nonneg _
  constructor
  · nlinarith [hb.1, hb.2]
  · nlinarith [hb.1, hb.2]

theorem stageOmega_isCompact {d : ℕ} (ℓ : Fin d → ℤ) {X : ℕ}
    (M : Fin d → ℕ) (hX : 1 ≤ X) : IsCompact (stageOmega ℓ X M) := by
  have hclosed : IsClosed (stageOmega ℓ X M) := by
    have h1 : IsClosed {x : Fin d → ℝ | realFunctional ℓ x = 1} :=
      isClosed_eq (realFunctional ℓ).continuous_of_finiteDimensional
        continuous_const
    have h2 : IsClosed {x : Fin d → ℝ | (X : ℝ) • x ∈ realCoordinateBox M} :=
      (realCoordinateBox_isCompact M).isClosed.preimage
        (continuous_const_smul ((X : ℝ)))
    exact h1.inter h2
  exact (realCoordinateBox_isCompact M).of_isClosed_subset hclosed
    (stageOmega_subset_box hX)

/-- The projective normalizations of the shell set live in the stage body. -/
theorem projNorm_mem_stageOmega {d : ℕ} {ℓ : Fin d → ℤ} {X : ℕ}
    {V : Finset (Fin d → ℤ)} {M : Fin d → ℕ} (hX : 1 ≤ X)
    (hshell : ShellNonDividing (fun v => (intFunctional ℓ v : ℤ)) X V)
    (hVbox : V ⊆ coordinateBox M) {v : Fin d → ℤ} (hv : v ∈ V) :
    projNorm ℓ v ∈ stageOmega ℓ X M :=
  ⟨realFunctional_projNorm_of_shell hX hshell hv,
    smul_projNorm_mem_realBox hX (hshell.1 v hv).1 (hVbox hv)⟩

/-- The height-`X` cone over the stage body stays in the real box. -/
theorem cone_stageOmega_subset {d : ℕ} (ℓ : Fin d → ℤ) (X : ℕ)
    (M : Fin d → ℕ) :
    cone (X : ℝ) (stageOmega ℓ X M) ⊆ realCoordinateBox M := by
  rintro _ ⟨y, hy, t, ht0, htX, rfl⟩
  rw [mem_realCoordinateBox]
  intro i
  have hb := (mem_realCoordinateBox.mp hy.2) i
  rw [Pi.smul_apply, smul_eq_mul] at hb
  rw [Pi.smul_apply, smul_eq_mul]
  have hM : (0 : ℝ) ≤ (M i : ℝ) := Nat.cast_nonneg _
  rcases le_or_gt 0 (y i) with hyi | hyi
  · constructor
    · nlinarith
    · nlinarith
  · constructor
    · nlinarith
    · nlinarith

/-- **Interior of the chart image of the stage body is nonempty**, given that
the shell set spans `ℝ^d` (from `projective_span_package`): the chart image of
`π(V)` affinely spans the chart, and its convex hull sits inside the chart
image of `Ω`. -/
theorem interior_chart_stageOmega_nonempty {r : ℕ} {ℓ : Fin (r + 1) → ℤ}
    {j : Fin (r + 1)} (hj : (ℓ j : ℝ) ≠ 0) {V : Finset (Fin (r + 1) → ℤ)}
    {X : ℕ} {M : Fin (r + 1) → ℕ} (hX : 1 ≤ X)
    (hshell : ShellNonDividing (fun v => (intFunctional ℓ v : ℤ)) X V)
    (hVbox : V ⊆ coordinateBox M) (hVne : V.Nonempty)
    (hspanV : integerRealSpan V = ⊤) :
    (interior (chartProj j '' stageOmega ℓ X M)).Nonempty := by
  classical
  have hpos : ∀ v ∈ V, intFunctional ℓ v ≠ 0 := fun v hv =>
    ne_of_gt (intFunctional_pos_of_shell hX hshell hv)
  have hsp : Submodule.span ℝ (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ))) = ⊤ :=
    span_projNorm_eq_top ℓ hspanV hpos
  obtain ⟨v₀, hv₀⟩ := hVne
  -- The chart image of the projective family affinely spans the chart.
  have haff : affineSpan ℝ
      (chartProj j '' (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ)))) = ⊤ := by
    have hmap := AffineSubspace.map_span ((chartProjL j).toAffineMap)
      (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ)))
    rw [show ((chartProjL j).toAffineMap) ''
        (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ)))
        = chartProj j '' (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ))) from rfl]
      at hmap
    rw [← hmap]
    rw [eq_top_iff]
    intro y _
    rw [AffineSubspace.mem_map]
    refine ⟨chartSec ℓ j y, ?_, chartProj_chartSec ℓ j y⟩
    rw [mem_affineSpan_projNorm_iff (by omega : 1 ≤ r + 1) ℓ hv₀ hpos hsp]
    exact realFunctional_chartSec hj y
  -- The convex hull of the chart points has nonempty interior.
  have hconvΩc : Convex ℝ (chartProj j '' stageOmega ℓ X M) :=
    (stageOmega_convex ℓ X M).linear_image (chartProjL j)
  have hsubset : convexHull ℝ
      (chartProj j '' (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ))))
      ⊆ chartProj j '' stageOmega ℓ X M := by
    refine convexHull_min ?_ hconvΩc
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨projNorm ℓ v, projNorm_mem_stageOmega hX hshell hVbox hv, rfl⟩
  have h1 : (interior (convexHull ℝ
      (chartProj j '' (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ)))))).Nonempty := by
    rw [Convex.interior_nonempty_iff_affineSpan_eq_top
      (convex_convexHull ℝ _)]
    rw [affineSpan_convexHull]
    exact haff
  exact h1.mono (interior_mono hsubset)

/-! ## 3. Span dichotomy at an irreducible stage

A `δ`-large subset of an irreducible stage spans `ℝ^d`: otherwise it lies in
the width-`0` slab of a functional annihilating its span, contradicting
`slab_exclusion`. -/

/-- **Span dichotomy** (`lem:slab-exclusion` consequence): under
irreducibility with eligibility/scale thresholds, a `δ`-large subset `W ⊆ V`
of a stage whose full set spans `ℝ^d` must itself span `ℝ^d`. -/
theorem span_top_of_large_subset {d : ℕ} {β : ℝ} (pkg : Package d β)
    (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (V W : Finset (Fin d → ℤ)) (M : Fin d → ℕ) (δ γ : ℝ),
      Eligible β pkg.m₀ W M →
      UnshiftedIrreducible pkg δ γ V M → W ⊆ V → V ⊆ coordinateBox M →
      δ * (V.card : ℝ) ≤ (W.card : ℝ) → 0 < γ →
      1 ≤ External.structureScale W.card →
      1 ≤ pkg.c * External.structureScale W.card →
      K < External.structureScale W.card * γ →
      integerRealSpan V = ⊤ →
      integerRealSpan W = ⊤ := by
  classical
  obtain ⟨cstar, K, hcstar, hK, hexcl⟩ := slab_exclusion pkg hd
  refine ⟨K, hK, ?_⟩
  intro V W M δ γ hE hirr hWV hVbox hWcard hγ hs1 hcs1 hKs hspanV
  by_contra hne
  have hlt : integerRealSpan W < ⊤ := lt_top_iff_ne_top.mpr hne
  obtain ⟨f, hf0, hfmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  set a : Fin d → ℝ := fun i => f (Pi.single i 1) with ha
  -- The functional in coordinates.
  have hfz : ∀ z : Fin d → ℤ,
      f (External.realPoint z) = ∑ i, a i * (z i : ℝ) := by
    intro z
    have hdecomp : External.realPoint z
        = ∑ i, ((z i : ℝ)) • Pi.single (M := fun _ => ℝ) i 1 :=
      pi_eq_sum_univ' _
    rw [hdecomp, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, smul_eq_mul, ha]
      ring
  -- `f` vanishes on `W`.
  have hfW : ∀ z ∈ W, f (External.realPoint z) = 0 := by
    intro z hz
    have hmem : External.realPoint z ∈ integerRealSpan W :=
      Submodule.subset_span ⟨z, hz, rfl⟩
    have h1 : f (External.realPoint z) ∈ (integerRealSpan W).map f :=
      Submodule.mem_map_of_mem hmem
    rw [hfmap] at h1
    exact (Submodule.mem_bot ℝ).mp h1
  -- Positive width, else `f` kills the spanning set `V`.
  set w : ℝ := ∑ i, |a i| * (M i : ℝ) with hw
  have hbound : ∀ v ∈ coordinateBox M, |f (External.realPoint v)| ≤ w := by
    intro v hv
    rw [hfz v]
    calc |∑ i, a i * (v i : ℝ)| ≤ ∑ i, |a i * (v i : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |a i| * (M i : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hvi := (mem_coordinateBox.mp hv) i
          have h1 : |v i| ≤ (M i : ℤ) := abs_le.mpr hvi
          calc |(v i : ℝ)| = ((|v i| : ℤ) : ℝ) := by rw [Int.cast_abs]
            _ ≤ (M i : ℝ) := by exact_mod_cast h1
  have hw0 : 0 < w := by
    rcases lt_or_ge 0 w with h | h
    · exact h
    · exfalso
      have hwnn : 0 ≤ w := by
        rw [hw]
        exact Finset.sum_nonneg fun i _ =>
          mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
      have hweq : w = 0 := le_antisymm h hwnn
      have hfV : ∀ v ∈ V, f (External.realPoint v) = 0 := fun v hv =>
        abs_nonpos_iff.mp (hweq ▸ hbound v (hVbox hv))
      have hker : integerRealSpan V ≤ LinearMap.ker f := by
        rw [integerRealSpan, Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        exact LinearMap.mem_ker.mpr (hfV v hv)
      rw [hspanV, top_le_iff] at hker
      apply hf0
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.zero_apply]
      have hx : x ∈ LinearMap.ker f := by rw [hker]; trivial
      exact LinearMap.mem_ker.mp hx
  -- Slab exclusion at width `τ = 0`.
  refine hexcl V W M hE a 0 δ γ hirr hWV hWcard hγ le_rfl (hw ▸ hw0)
    hs1 hcs1 ?_ hKs (by positivity)
  intro z hz
  rw [← hfz z, hfW z hz, abs_zero, zero_mul]

/-! ## 4. Full-rank cap lifting (`lem:cap-lifting`, alternative (ii))

The `r = d` branch: `discrete_john` (E2) applied to the lattice points of the
difference body of the cone cap, whose count is volume-bounded via
Rogers–Shephard (E5c) and the full-rank lattice count (E5d), yields a GAP box
`B'` with `|B'| ≤ C·η·|B|` and a shell-preserving identification. -/

theorem cap_lifting_full (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (ℓ : Fin d → ℤ) (X : ℕ) (η : ℝ) (Ω Ω' : Set (Fin d → ℝ))
      (W : Finset (Fin d → ℤ)) (M : Fin d → ℕ),
      1 ≤ X → 0 ≤ η →
      Convex ℝ Ω' → IsCompact Ω' → Ω'.Nonempty →
      volume (cone 1 Ω') ≤ ENNReal.ofReal η * volume (cone 1 Ω) →
      cone (X : ℝ) Ω ⊆ realCoordinateBox M →
      ShellNonDividing (fun v => (intFunctional ℓ v : ℤ)) X W →
      (∀ v ∈ W, projNorm ℓ v ∈ Ω') →
      integerRealSpan W = ⊤ →
      ∃ (lam' : (Fin d → ℤ) →+ ℤ) (W' : Finset (Fin d → ℤ))
        (N : Fin d → ℕ),
        W' ⊆ coordinateBox N ∧ W'.card = W.card ∧
        ShellNonDividing (fun n => lam' n) X W' ∧
        ((coordinateBox N).card : ℝ) ≤
          C * η * ((coordinateBox M).card : ℝ) := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := card_latticePoints_le_volume d
  obtain ⟨cj, hcj, Cj, hCj, hjohn⟩ := External.discrete_john d
  set binom : ℕ := Nat.choose (2 * d) d with hbinom_def
  have hbinom_pos : 0 < binom := Nat.choose_pos (by omega)
  refine ⟨(Cj : ℝ) * ((C₀ : ℝ) * (binom : ℝ) * 2 ^ d), by positivity, ?_⟩
  intro ℓ X η Ω Ω' W M hX hη hconv hcomp hne hvol hconeΩ hshell hWΩ' hspan
  set T : ℝ := 2 * (X : ℝ) with hT_def
  have hT : 0 ≤ T := by positivity
  set K : ConvexBody (Fin d → ℝ) := coneBody T Ω' hT hconv hcomp hne
    with hK_def
  set Kd : ConvexBody (Fin d → ℝ) := K + (-1 : ℝ) • K with hKd_def
  have hDcoe : (Kd : Set (Fin d → ℝ)) =
      (K : Set (Fin d → ℝ)) + (-1 : ℝ) • (K : Set (Fin d → ℝ)) := by
    rw [hKd_def, ConvexBody.coe_add, ConvexBody.coe_smul]
  set A : Finset (Fin d → ℤ) :=
    latticePoints (Kd : Set (Fin d → ℝ)) Kd.isBounded with hA_def
  -- `K ⊆ K − K` since `0 ∈ K`.
  have h0K : (0 : Fin d → ℝ) ∈ (K : Set (Fin d → ℝ)) :=
    zero_mem_cone hT hne
  have hKD : (K : Set (Fin d → ℝ)) ⊆ (Kd : Set (Fin d → ℝ)) := by
    intro x hx
    rw [hDcoe]
    have hmem : x + (-1 : ℝ) • (0 : Fin d → ℝ) ∈
        (K : Set (Fin d → ℝ)) + (-1 : ℝ) • (K : Set (Fin d → ℝ)) :=
      Set.add_mem_add hx (Set.smul_mem_smul_set h0K)
    simpa using hmem
  -- `W ⊆ A` via the shell containment.
  have hWA : W ⊆ A := by
    intro v hv
    rw [hA_def, mem_latticePoints]
    obtain ⟨hlo, hhi⟩ := hshell.1 v hv
    exact hKD (realPoint_mem_cone hX hlo hhi (hWΩ' v hv))
  -- `K − K` is origin-symmetric (one-directional and iff forms).
  have hsymm : ∀ x ∈ (Kd : Set (Fin d → ℝ)), -x ∈ Kd := by
    intro x hx
    rw [hDcoe] at hx
    show -x ∈ (Kd : Set (Fin d → ℝ))
    rw [hDcoe]
    obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_add.mp hx
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.mp hw
    refine Set.mem_add.mpr ⟨k, hk, (-1 : ℝ) • u,
      Set.smul_mem_smul_set hu, ?_⟩
    simp only [neg_one_smul]
    abel
  have hsymm_iff : ∀ x, x ∈ (Kd : Set (Fin d → ℝ)) ↔
      -x ∈ (Kd : Set (Fin d → ℝ)) := by
    intro x
    constructor
    · exact hsymm x
    · intro hx
      have := hsymm (-x) hx
      rwa [neg_neg] at this
  -- The lattice points of `K − K` span (they contain `W`).
  have hspanA : integerRealSpan A = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hspan]
    exact Submodule.span_mono
      (Set.image_mono (Finset.coe_subset.mpr hWA))
  -- Discrete John (E2) on `K − K` at full rank.
  have hfr : Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ)) = d := by
    rw [finrank_top, Module.finrank_fin_fun]
  obtain ⟨Q, _hQstep, hQprop, _hQinner, hAQ, hQcard⟩ :=
    hjohn d ⊤ (Kd : Set (Fin d → ℝ)) A hfr Kd.isCompact Kd.convex
      hsymm_iff (by intro x _; exact Submodule.mem_top)
      (fun z => mem_latticePoints Kd.isBounded z) hspanA ⟨0, hKD h0K⟩
  -- The volume count for `A`.
  have hcardA : (A.card : ENNReal) ≤
      (C₀ : ENNReal) * ((binom : ENNReal) * ENNReal.ofReal (T ^ d) *
        (ENNReal.ofReal η * volume (cone 1 Ω))) := by
    calc (A.card : ENNReal)
        ≤ (C₀ : ENNReal) * volume (Kd : Set (Fin d → ℝ)) :=
          hcount Kd hsymm hspanA
      _ ≤ (C₀ : ENNReal) * ((binom : ENNReal) * ENNReal.ofReal (T ^ d) *
            volume (cone 1 Ω')) := by
          refine mul_le_mul_right ?_ _
          exact volume_coneBody_diff_le T Ω' hT hconv hcomp hne
      _ ≤ (C₀ : ENNReal) * ((binom : ENNReal) * ENNReal.ofReal (T ^ d) *
            (ENNReal.ofReal η * volume (cone 1 Ω))) := by
          exact mul_le_mul_right (mul_le_mul_right hvol _) _
  -- The cone volume is bounded by the box cardinality.
  have hconevol : ENNReal.ofReal ((X : ℝ) ^ d) * volume (cone 1 Ω) ≤
      ((coordinateBox M).card : ENNReal) := by
    have h1 : ENNReal.ofReal ((X : ℝ) ^ d) * volume (cone 1 Ω)
        = volume (cone (X : ℝ) Ω) :=
      (volume_cone (by positivity) Ω).symm
    have h2 : volume (cone (X : ℝ) Ω) ≤ volume (realCoordinateBox M) :=
      measure_mono hconeΩ
    have h3 : realCoordinateBox M = realBox M := by
      rw [realCoordinateBox, realBox, Set.pi_univ_Icc]
    have h4 : volume (realCoordinateBox M) ≤
        ((coordinateBox M).card : ENNReal) := by
      rw [h3, volume_realBox, ← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      rw [card_coordinateBox]
      push_cast
      have h5 : (2 : ℝ) ^ d * ∏ i, (M i : ℝ) = ∏ i, (2 * (M i : ℝ)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      rw [h5]
      exact Finset.prod_le_prod (fun i _ => by positivity)
        (fun i _ => by linarith [Nat.cast_nonneg (α := ℝ) (M i)])
    calc ENNReal.ofReal ((X : ℝ) ^ d) * volume (cone 1 Ω)
        = volume (cone (X : ℝ) Ω) := h1
      _ ≤ volume (realCoordinateBox M) := h2
      _ ≤ ((coordinateBox M).card : ENNReal) := h4
  -- Assemble the ENNReal bound with the box.
  have hTsplit : ENNReal.ofReal (T ^ d) =
      ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal ((X : ℝ) ^ d) := by
    rw [← ENNReal.ofReal_mul (by positivity), hT_def, mul_pow]
  have hcardA' : (A.card : ENNReal) ≤
      (C₀ : ENNReal) * ((binom : ENNReal) * (ENNReal.ofReal η *
        (ENNReal.ofReal ((2 : ℝ) ^ d) *
          ((coordinateBox M).card : ENNReal)))) := by
    refine hcardA.trans ?_
    rw [hTsplit]
    calc (C₀ : ENNReal) * ((binom : ENNReal) *
          (ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal ((X : ℝ) ^ d)) *
          (ENNReal.ofReal η * volume (cone 1 Ω)))
        = (C₀ : ENNReal) * ((binom : ENNReal) * (ENNReal.ofReal η *
            (ENNReal.ofReal ((2 : ℝ) ^ d) *
              (ENNReal.ofReal ((X : ℝ) ^ d) * volume (cone 1 Ω))))) := by
          ring
      _ ≤ (C₀ : ENNReal) * ((binom : ENNReal) * (ENNReal.ofReal η *
            (ENNReal.ofReal ((2 : ℝ) ^ d) *
              ((coordinateBox M).card : ENNReal)))) := by
          exact mul_le_mul_right (mul_le_mul_right
            (mul_le_mul_right (mul_le_mul_right hconevol _) _) _) _
  -- To the reals.
  have hRHS_ne : (C₀ : ENNReal) * ((binom : ENNReal) * (ENNReal.ofReal η *
      (ENNReal.ofReal ((2 : ℝ) ^ d) *
        ((coordinateBox M).card : ENNReal)))) ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    apply ENNReal.mul_ne_top (ENNReal.natCast_ne_top binom)
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.natCast_ne_top _)
  have hrealA := ENNReal.toReal_mono hRHS_ne hcardA'
  rw [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hη, ENNReal.toReal_ofReal (by positivity)]
    at hrealA
  -- The transported stage through the John GAP.
  have hWQ : W ⊆ Q.carrier := hWA.trans hAQ
  set lift : {x // x ∈ W} ↪ {v // v ∈ Q.carrier} :=
    ⟨fun x => ⟨x.1, hWQ x.2⟩, by
      intro x y hxy
      apply Subtype.ext
      exact Subtype.mk_eq_mk.mp hxy⟩ with hlift
  set Wsub : Finset {v // v ∈ Q.carrier} := W.attach.map lift with hWsub
  have hval : Wsub.map ⟨Subtype.val, Subtype.val_injective⟩ = W := by
    ext z
    constructor
    · intro hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (hWsub ▸ hv)
      exact x.2
    · intro hz
      refine Finset.mem_map.mpr ⟨lift ⟨z, hz⟩, ?_, rfl⟩
      rw [hWsub]
      exact Finset.mem_map_of_mem lift (Finset.mem_attach W ⟨z, hz⟩)
  have hshellsub : ShellNonDividing
      (fun v : {v // v ∈ Q.carrier} => intFunctional ℓ v.1) X Wsub := by
    have := ShellNonDividing.of_map
      (ell := fun v => (intFunctional ℓ v : ℤ)) (S := Wsub)
      ⟨Subtype.val, Subtype.val_injective⟩ (by rwa [hval])
    exact this
  have htrans := Q.shell_transport hQprop (intFunctional ℓ) X Wsub hshellsub
  refine ⟨Q.transportedFunctional (intFunctional ℓ),
    Wsub.map (Q.coeffCarrierEmbedding hQprop), Q.radius, ?_, ?_, htrans, ?_⟩
  · intro n hn
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hn
    exact Q.coeffOf_mem v
  · rw [Finset.card_map, hWsub, Finset.card_map, Finset.card_attach]
  · -- The box-cardinality chain.
    have hQA : (Q.carrier.card : ℝ) ≤ (Cj : ℝ) * (A.card : ℝ) := by
      exact_mod_cast hQcard
    calc ((coordinateBox Q.radius).card : ℝ)
        = (Q.coeffBox.card : ℝ) := by rw [GAP.coeffBox]
      _ = (Q.carrier.card : ℝ) := by
          rw [Q.card_carrier_of_proper hQprop]
      _ ≤ (Cj : ℝ) * (A.card : ℝ) := hQA
      _ ≤ (Cj : ℝ) * ((C₀ : ℝ) * ((binom : ℝ) * (η * ((2 : ℝ) ^ d *
            ((coordinateBox M).card : ℝ))))) := by
          exact mul_le_mul_of_nonneg_left hrealA (Nat.cast_nonneg _)
      _ = (Cj : ℝ) * ((C₀ : ℝ) * (binom : ℝ) * 2 ^ d) * η *
            ((coordinateBox M).card : ℝ) := by ring

/-! ## 5. The irreducible-stage increment step

The full geometric pipeline at ambient dimension `d = r + 1`, for a stage
whose projective family is in `μ`-convex position: weighted density in the
chart `H_λ ≅ ℝ^r` returns a captured body of chart volume `≤ η·vol(Ω_c)`; the
captured shell subset is `δ`-large, hence spans (`span_top_of_large_subset`);
full-rank cap lifting transports it to a box of size `≤ C·η·|B|`.  At `r = 0`
(`d = 1`) the convex-position hypothesis is itself contradictory (all
projective points coincide), so the conclusion is vacuous. -/

/-- At `d = 1` every projective normalization coincides, so indexed
`μ`-convex position with `μ < 1` on a nonempty family is absurd. -/
theorem muConvexPosition_dim_one_absurd {ℓ : Fin 1 → ℤ} {X : ℕ}
    {V : Finset (Fin 1 → ℤ)} {μ : ℝ} (hX : 1 ≤ X) (hμ1 : μ < 1)
    (hV1 : 1 ≤ V.card)
    (hshell : ShellNonDividing (fun v => (intFunctional ℓ v : ℤ)) X V)
    (hconv : IndexedMuConvexPosition μ
      (fun v : {x // x ∈ V} => projNorm ℓ v.1)) : False := by
  classical
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp (by omega : 0 < V.card)
  have hl0 : (ℓ 0 : ℝ) ≠ 0 := by
    have hpos := intFunctional_pos_of_shell hX hshell hv₀
    rw [intFunctional_apply, Fin.sum_univ_one] at hpos
    intro h0
    have : (ℓ 0 : ℝ) = 0 := h0
    have hz : ℓ 0 = 0 := by exact_mod_cast this
    rw [hz, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  -- All projective points coincide.
  have hall : ∀ v ∈ V, projNorm ℓ v = projNorm ℓ v₀ := by
    have hval : ∀ v ∈ V, projNorm ℓ v 0 = 1 / (ℓ 0 : ℝ) := by
      intro v hv
      have h1 := realFunctional_projNorm_of_shell hX hshell hv
      rw [realFunctional_apply, Fin.sum_univ_one] at h1
      field_simp
      linarith [h1]
    intro v hv
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi, hval v hv, hval v₀ hv₀]
  obtain ⟨u, t, htle, hcount⟩ := hconv ⟨v₀, hv₀⟩
  have htle' : t ≤ u (projNorm ℓ v₀) := htle
  have hfilter : (Finset.univ.filter
      fun k : {x // x ∈ V} =>
        t ≤ u ((fun v : {x // x ∈ V} => projNorm ℓ v.1) k))
      = Finset.univ := by
    refine Finset.filter_true_of_mem fun k _ => ?_
    show t ≤ u (projNorm ℓ k.1)
    rw [hall k.1 k.2]
    exact htle'
  rw [hfilter, Finset.card_univ, Fintype.card_coe] at hcount
  have hcard1 : (1 : ℝ) ≤ (V.card : ℝ) := by exact_mod_cast hV1
  nlinarith [hcount]

/-- **The irreducible-stage cap step** (Manuscript.tex 1941–2024, geometric
core).  At ambient dimension `r + 1`, given the weighted-density and
cap-lifting constants, a `μ`-convex-position stage yields `η ∈ [μ, μ^tau]`, a
shell-preserving transported set `W'` of size `≥ η^{κ_r + ε}·|V|` in a box of
size `≤ C·η·|B|` (same ambient dimension). -/
theorem irreducible_cap_step {β : ℝ} (eps : ℝ) (heps : 0 < eps) (r : ℕ)
    (pkg : Package (r + 1) β) :
    ∃ tau K C μ₀ : ℝ, 0 < tau ∧ tau < 1 ∧ 0 < K ∧ 0 < C ∧ 0 < μ₀ ∧
    ∀ μ : ℝ, ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (X : ℕ) (ℓ : Fin (r + 1) → ℤ) (V : Finset (Fin (r + 1) → ℤ))
      (M : Fin (r + 1) → ℕ) (δ γ : ℝ),
      0 < μ → μ < μ₀ → μ < 1 →
      1 ≤ X → V ⊆ coordinateBox M →
      ShellNonDividing (fun v => (intFunctional ℓ v : ℤ)) X V →
      UnshiftedIrreducible pkg δ γ V M →
      0 < γ → δ ≤ μ ^ (1 + eps) →
      n₀ ≤ V.card →
      integerRealSpan V = ⊤ →
      (∀ W : Finset (Fin (r + 1) → ℤ), W ⊆ V →
        δ * (V.card : ℝ) ≤ (W.card : ℝ) →
        Eligible β pkg.m₀ W M ∧
        1 ≤ External.structureScale W.card ∧
        1 ≤ pkg.c * External.structureScale W.card ∧
        K < External.structureScale W.card * γ) →
      IndexedMuConvexPosition μ
        (fun v : {x // x ∈ V} => projNorm ℓ v.1) →
      ∃ (η : ℝ) (lam' : (Fin (r + 1) → ℤ) →+ ℤ)
        (W' : Finset (Fin (r + 1) → ℤ)) (N : Fin (r + 1) → ℕ),
        μ ≤ η ∧ η ≤ μ ^ tau ∧
        W' ⊆ coordinateBox N ∧
        ShellNonDividing (fun n => lam' n) X W' ∧
        η ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) * (V.card : ℝ) ≤
          (W'.card : ℝ) ∧
        ((coordinateBox N).card : ℝ) ≤
          C * η * ((coordinateBox M).card : ℝ) := by
  classical
  by_cases hr0 : r = 0
  · -- `r = 0`, ambient dimension 1: the convex-position hypothesis is absurd.
    subst hr0
    refine ⟨1 / 2, 1, 1, 1 / 2, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, ?_⟩
    intro μ
    refine ⟨1, le_rfl, ?_⟩
    intro X ℓ V M δ γ hμ hμμ₀ hμ1 hX hVbox hshell hirr hγ hδμ hn hspanV
      hsupply hconv
    exact absurd hconv
      (fun h => muConvexPosition_dim_one_absurd hX hμ1 hn hshell h)
  · -- `r ≥ 1`, ambient dimension `≥ 2`: the real pipeline.
    have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    obtain ⟨tau, μ₀, htau0, htau1, hμ₀, hstep⟩ :=
      weighted_density r hr eps heps
    obtain ⟨Kspan, hKspan, hspanthm⟩ :=
      span_top_of_large_subset pkg (by omega)
    obtain ⟨Ccap, hCcap, hcap⟩ := cap_lifting_full (r + 1)
    refine ⟨tau, Kspan, Ccap, μ₀, htau0, htau1, hKspan, hCcap, hμ₀, ?_⟩
    intro μ
    by_cases hμok : 0 < μ ∧ μ < μ₀
    swap
    · refine ⟨1, le_rfl, ?_⟩
      intro X ℓ V M δ γ hμ hμμ₀ _ _ _ _ _ _ _ _ _ _ _
      exact absurd ⟨hμ, hμμ₀⟩ hμok
    obtain ⟨n₀, hn₀⟩ := hstep μ hμok.1 hμok.2
    refine ⟨max n₀ 1, le_max_right _ _, ?_⟩
    intro X ℓ V M δ γ hμ hμμ₀ hμ1 hX hVbox hshell hirr hγ hδμ hn hspanV
      hsupply hconv
    set n : ℕ := V.card with hn_def
    have hn₀n : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have h1n : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
    -- A nonvanishing coordinate of the functional.
    obtain ⟨v₀, hv₀⟩ := hVne
    obtain ⟨j, hj⟩ : ∃ j, ℓ j ≠ 0 := by
      by_contra h0
      have hall0 : ∀ i, ℓ i = 0 := fun i => by
        by_contra hi
        exact h0 ⟨i, hi⟩
      have hpos := intFunctional_pos_of_shell hX hshell hv₀
      rw [intFunctional_apply] at hpos
      rw [Finset.sum_eq_zero (fun i _ => by rw [hall0 i, zero_mul])] at hpos
      exact lt_irrefl 0 hpos
    have hjR : (ℓ j : ℝ) ≠ 0 := by exact_mod_cast hj
    -- The chart body.
    set Ωc : Set (Fin r → ℝ) := chartProj j '' stageOmega ℓ X M with hΩc_def
    have hcompΩc : IsCompact Ωc :=
      (stageOmega_isCompact ℓ M hX).image (continuous_chartProj j)
    have hconvΩc : Convex ℝ Ωc :=
      (stageOmega_convex ℓ X M).linear_image (chartProjL j)
    have hintΩc : (interior Ωc).Nonempty :=
      interior_chart_stageOmega_nonempty hjR hX hshell hVbox
        ⟨v₀, hv₀⟩ hspanV
    -- The indexed family in the chart.
    have hproj1 : ∀ v : {x // x ∈ V},
        realFunctional ℓ (projNorm ℓ v.1) = 1 := fun v =>
      realFunctional_projNorm_of_shell hX hshell v.2
    have hchartpos : IndexedMuConvexPosition μ
        (fun v : {x // x ∈ V} => chartProj j (projNorm ℓ v.1)) :=
      indexedMuConvexPosition_chartProj hjR hproj1 hconv
    set e : {x // x ∈ V} ≃ Fin n :=
      Fintype.equivFinOfCardEq (Fintype.card_coe V) with he_def
    set p : Fin n → (Fin r → ℝ) :=
      fun i => chartProj j (projNorm ℓ ((e.symm i) : {x // x ∈ V}).1)
      with hp_def
    have hppos : IndexedMuConvexPosition μ p :=
      hchartpos.comp_equiv e.symm
    have hpΩ : ∀ i, p i ∈ Ωc := fun i =>
      ⟨projNorm ℓ (e.symm i).1,
        projNorm_mem_stageOmega hX hshell hVbox (e.symm i).2, rfl⟩
    -- Weighted density in the chart.
    obtain ⟨η, hημ, hημtau, Kb, hKsub, hKvol, hcount⟩ :=
      hn₀ n p Ωc hn₀n h1n hcompΩc hconvΩc hintΩc hpΩ hppos
    have hη0 : 0 < η := lt_of_lt_of_le hμ hημ
    -- The captured shell subset.
    set W : Finset (Fin (r + 1) → ℤ) := V.filter
      (fun v => chartProj j (projNorm ℓ v) ∈ (Kb : Set (Fin r → ℝ)))
      with hW_def
    have hWV : W ⊆ V := Finset.filter_subset _ _
    have hWcard_eq : (Finset.univ.filter
        (fun i => p i ∈ (Kb : Set (Fin r → ℝ)))).card = W.card := by
      refine Finset.card_bij
        (fun i _ => ((e.symm i) : {x // x ∈ V}).1) ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨(e.symm i).2, hi.2⟩
      · intro i₁ h₁ i₂ h₂ heq
        have : e.symm i₁ = e.symm i₂ := Subtype.ext heq
        exact e.symm.injective this
      · intro v hv
        rw [Finset.mem_filter] at hv
        refine ⟨e ⟨v, hv.1⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hp_def]
          simp only [Equiv.symm_apply_apply]
          exact hv.2
        · simp only [Equiv.symm_apply_apply]
    have hWlow : η ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) * (n : ℝ) ≤
        (W.card : ℝ) := by
      rw [← hWcard_eq]
      exact hcount
    -- The captured set is `δ`-large.
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hκ0 : 0 ≤ ((r : ℝ) - 1) / ((r : ℝ) + 1) + eps := by
      have h1 : (0 : ℝ) ≤ ((r : ℝ) - 1) / ((r : ℝ) + 1) :=
        div_nonneg (by linarith) (by linarith)
      linarith
    have hκ1 : ((r : ℝ) - 1) / ((r : ℝ) + 1) + eps ≤ 1 + eps := by
      have h1 : ((r : ℝ) - 1) / ((r : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      linarith
    have hδW : δ * (n : ℝ) ≤ (W.card : ℝ) := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have h1 : μ ^ ((1 : ℝ) + eps) ≤
          μ ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) :=
        Real.rpow_le_rpow_of_exponent_ge hμ hμ1.le hκ1
      have h2 : μ ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) ≤
          η ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) :=
        Real.rpow_le_rpow hμ.le hημ hκ0
      calc δ * (n : ℝ) ≤ μ ^ ((1 : ℝ) + eps) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right hδμ hnn
        _ ≤ η ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right (h1.trans h2) hnn
        _ ≤ (W.card : ℝ) := hWlow
    obtain ⟨hE_W, hsW1, hcsW1, hKsW⟩ := hsupply W hWV hδW
    -- The captured set spans: full rank.
    have hspanW : integerRealSpan W = ⊤ :=
      hspanthm V W M δ γ hE_W hirr hWV hVbox hδW hγ hsW1 hcsW1 hKsW hspanV
    -- The ambient cap body.
    set Ω' : Set (Fin (r + 1) → ℝ) :=
      chartSec ℓ j '' (Kb : Set (Fin r → ℝ)) with hΩ'_def
    have hconvΩ' : Convex ℝ Ω' := convex_chartSec_image ℓ j Kb.convex
    have hcompΩ' : IsCompact Ω' :=
      Kb.isCompact.image (continuous_chartSec ℓ j)
    have hneΩ' : Ω'.Nonempty := Kb.nonempty.image _
    have hΩ'hyp : ∀ x ∈ Ω', realFunctional ℓ x = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      exact realFunctional_chartSec hjR y
    -- The chart image of the cap body is the captured body.
    have hchartΩ' : chartProj j '' Ω' = (Kb : Set (Fin r → ℝ)) := by
      rw [hΩ'_def, ← Set.image_comp]
      have : (chartProj j ∘ chartSec ℓ j) '' (Kb : Set (Fin r → ℝ))
          = id '' (Kb : Set (Fin r → ℝ)) := by
        refine Set.image_congr fun y _ => ?_
        show chartProj j (chartSec ℓ j y) = y
        exact chartProj_chartSec ℓ j y
      rw [this, Set.image_id]
    -- The cone-volume ratio.
    have hvolratio : volume (cone 1 Ω') ≤
        ENNReal.ofReal η * volume (cone 1 (stageOmega ℓ X M)) := by
      refine cone_volume_ratio ℓ j hj hcompΩ' (stageOmega_isCompact ℓ M hX)
        hΩ'hyp (fun x hx => hx.1) ?_
      rw [hchartΩ']
      exact hKvol
    -- Cap membership of the captured shell points.
    have hWΩ' : ∀ v ∈ W, projNorm ℓ v ∈ Ω' := by
      intro v hv
      rw [Finset.mem_filter] at hv
      refine ⟨chartProj j (projNorm ℓ v), hv.2, ?_⟩
      exact chartSec_chartProj hjR
        (realFunctional_projNorm_of_shell hX hshell hv.1)
    -- Full-rank cap lifting.
    obtain ⟨lam', W', N, hW'box, hW'card, hW'shell, hW'bound⟩ :=
      hcap ℓ X η (stageOmega ℓ X M) Ω' W M hX hη0.le hconvΩ' hcompΩ' hneΩ'
        hvolratio (cone_stageOmega_subset ℓ X M)
        (hshell.mono hWV) hWΩ' hspanW
    refine ⟨η, lam', W', N, hημ, hημtau, hW'box, hW'shell, ?_, hW'bound⟩
    rw [hW'card]
    exact hWlow

/-! ## 6. Assembly: the `IrreducibleIncrement` predicate

`TODO(orchestrator)`: the remaining hypothesis `hsup` is the per-stage
supplier package.  Its clauses are exactly:

* the coefficient-vector form of the stage functional (trivial);
* the parameter regime `0 < μ < min(1, μ₀ d)`, `δ ≤ μ^{1+ε}`, `n ≥ n₀(d, μ)`
  (manuscript hierarchy `δ = o(μ)`, `n` large);
* `integerRealSpan V = ⊤` — discharge from `projective_span_package`;
* the eligibility/scale supplier (manuscript `s(δn)⁻¹ = o(γ)` regime);
* `IndexedMuConvexPosition` — the conclusion of `thm:projective-convexity`,
  discharge from `projective_convexity_assembled` (+ `projective_duality`);
* the absorption numerics `C·η < 1`, `(C·η)^{σ_d+ζ₀-ν} ≤ η^{κ_{d-1}+ε}`,
  `n₁ ≤ η^{κ_{d-1}+ε}·n` for `η ∈ [μ, μ^τ]` (manuscript:
  `κ_{d-1}+ε ≤ σ_d+ζ₀-ν` by the choice of `ε, ν`, and `η^{κ+ε} = n^{-o(1)}`).

Note the increment always lands in the *same-dimensional* branch: at an
irreducible stage the captured set spans (`span_top_of_large_subset`), so the
dimension-lowering alternative of `lem:cap-lifting` never fires. -/

/-- **`IrreducibleIncrement` from the geometric pipeline and a per-stage
supplier.**  The constants `tau, K, C, μ₀, n₀` (indexed by the stage
dimension) are produced by the pipeline; the supplier must meet them. -/
theorem irreducibleIncrement_of_convexPosition {β : ℝ}
    (pkgs : ∀ r, Package r β) (eps : ℝ) (heps : 0 < eps) (Dcap : ℕ) :
    ∃ (tau K C μ₀ : ℕ → ℝ) (n₀ : ℕ → ℝ → ℕ),
      (∀ d, 0 < tau d ∧ tau d < 1 ∧ 0 < K d ∧ 0 < C d ∧ 0 < μ₀ d) ∧
      ∀ (ζ₀ ε δ γ ν : ℝ) (n₁ n₂ : ℕ), 2 ≤ n₁ → n₁ ≤ n₂ →
      (∀ (X : ℕ) (s : PrepStage X), 1 ≤ X → n₂ ≤ s.V.card → s.dim ≤ Dcap →
        ExcessiveStage ζ₀ s →
        StageIrreducible pkgs δ γ s →
        ∃ (ℓ : Fin s.dim → ℤ) (μ : ℝ),
          (∀ v, s.lam v = intFunctional ℓ v) ∧
          0 < μ ∧ μ < 1 ∧ μ < μ₀ s.dim ∧
          n₀ s.dim μ ≤ s.V.card ∧
          0 < γ ∧
          δ ≤ μ ^ ((1 : ℝ) + eps) ∧
          integerRealSpan s.V = ⊤ ∧
          (∀ W : Finset (Fin s.dim → ℤ), W ⊆ s.V →
            δ * (s.V.card : ℝ) ≤ (W.card : ℝ) →
            Eligible β (pkgs s.dim).m₀ W s.M ∧
            1 ≤ External.structureScale W.card ∧
            1 ≤ (pkgs s.dim).c * External.structureScale W.card ∧
            K s.dim < External.structureScale W.card * γ) ∧
          IndexedMuConvexPosition μ
            (fun v : {x // x ∈ s.V} => projNorm ℓ v.1) ∧
          (∀ η : ℝ, μ ≤ η → η ≤ μ ^ tau s.dim →
            C s.dim * η < 1 ∧
            (C s.dim * η) ^ (sigma s.dim + ζ₀ - ν) ≤
              η ^ (((s.dim : ℝ) - 2) / (s.dim : ℝ) + eps) ∧
            (n₁ : ℝ) ≤ η ^ (((s.dim : ℝ) - 2) / (s.dim : ℝ) + eps) *
              (s.V.card : ℝ))) →
      IrreducibleIncrementCapped pkgs Dcap ζ₀ ε δ γ ν n₁ n₂ := by
  classical
  have hstep := fun r : ℕ =>
    irreducible_cap_step (β := β) eps heps r (pkgs (r + 1))
  choose tau K C μ₀ htau0 htau1 hK hC hμ₀ hmain using hstep
  choose n₀ hn₀pos hn₀main using hmain
  refine ⟨fun d => tau (d - 1), fun d => K (d - 1), fun d => C (d - 1),
    fun d => μ₀ (d - 1), fun d μ => n₀ (d - 1) μ,
    fun d => ⟨htau0 _, htau1 _, hK _, hC _, hμ₀ _⟩, ?_⟩
  intro ζ₀ ε δ γ ν n₁ n₂ hn₁ hn₁₂ hsup X s hX hncard hcap hexc hirr
  obtain ⟨d, V, M, lam, hsub, hshell⟩ := s
  obtain ⟨ℓ, μ, hlam, hμ0, hμ1, hμμ₀, hn₀le, hγ, hδμ, hspanV, hsupply,
    hconv, habs⟩ := hsup X ⟨d, V, M, lam, hsub, hshell⟩ hX hncard hcap hexc hirr
  rcases d with _ | r
  · -- Dimension 0: the box has one point, contradicting `n₁ ≥ 2`.
    exfalso
    have hbox1 : (coordinateBox M).card = 1 := by
      rw [card_coordinateBox]
      simp
    have hV1 : V.card ≤ 1 := hbox1 ▸ Finset.card_le_card hsub
    have hncard' : n₁ ≤ V.card := le_trans hn₁₂ hncard
    omega
  · -- Dimension `r + 1`: run the cap step; always the same-dim branch.
    have hshell' : ShellNonDividing
        (fun v => (intFunctional ℓ v : ℤ)) X V := by
      have hfe : (fun v => lam v) = fun v => (intFunctional ℓ v : ℤ) :=
        funext hlam
      rwa [hfe] at hshell
    obtain ⟨η, lam', W', N, hημ, hημtau, hW'box, hW'shell, hW'count,
        hW'bound⟩ :=
      hn₀main r μ X ℓ V M δ γ hμ0 hμμ₀ hμ1 hX hsub hshell' hirr hγ hδμ
        hn₀le hspanV hsupply hconv
    -- Exponent bookkeeping: `κ_r = ((r+1)-2)/(r+1)`.
    have hexp : (((r : ℝ) + 1) - 2) / ((r : ℝ) + 1) + eps
        = ((r : ℝ) - 1) / ((r : ℝ) + 1) + eps := by
      ring_nf
    have hcount' : η ^ ((((r + 1 : ℕ) : ℝ) - 2) / ((r + 1 : ℕ) : ℝ) + eps) *
        (V.card : ℝ) ≤ (W'.card : ℝ) := by
      push_cast
      rw [hexp]
      exact_mod_cast hW'count
    obtain ⟨hCη1, hCηpow, hn₁W⟩ := habs η hημ hημtau
    have hCη0 : 0 < C r * η := mul_pos (hC r) (lt_of_lt_of_le hμ0 hημ)
    -- `n₁ ≤ |W'|`.
    have hn₁W' : n₁ ≤ W'.card := by
      have h1 : (n₁ : ℝ) ≤ (W'.card : ℝ) := by
        refine le_trans ?_ hcount'
        exact_mod_cast hn₁W
      exact_mod_cast h1
    -- The new stage.
    refine ⟨⟨r + 1, W', N, lam', hW'box, hW'shell⟩, hn₁W', Or.inr ?_⟩
    refine ⟨rfl, C r * η, hCη0, hCη1, ?_, ?_⟩
    · -- Retention at the absorbed density.
      have h2 : (C r * η) ^ (sigma (r + 1) + ζ₀ - ν) * (V.card : ℝ) ≤
          η ^ ((((r + 1 : ℕ) : ℝ) - 2) / ((r + 1 : ℕ) : ℝ) + eps) *
            (V.card : ℝ) :=
        mul_le_mul_of_nonneg_right hCηpow (Nat.cast_nonneg _)
      exact h2.trans hcount'
    · -- Box decay.
      exact hW'bound

/-! ## 7. The μ-convex-position dichotomy (`thm:projective-convexity`)

At an irreducible stage meeting the manuscript's parameter thresholds, the
projective family is in `μ`-convex position: a failure yields, via
`projective_duality`, capped weights `β` realizing some `a ∈ V` from the
others; rounding to `θ = T·β` with `T = ⌊μn/8⌋` and feeding the fixed package
data of `C = V∖{a}` into `projective_convexity_assembled` produces the
contradiction.  This discharges the `IndexedMuConvexPosition` clause of the
supplier of `irreducibleIncrement_of_convexPosition`. -/

set_option maxHeartbeats 1600000 in
theorem stage_convexPosition_of_thresholds {d : ℕ} {β : ℝ}
    (pkg : Package d β) (hd : 1 ≤ d) :
    ∃ cw K : ℝ, 0 < cw ∧ 0 < K ∧
    ∀ (ℓ : Fin d → ℤ) (X : ℕ) (V : Finset (Fin d → ℤ)) (M : Fin d → ℕ)
      (δ γ μ : ℝ),
      1 ≤ X →
      ShellNonDividing (fun v => (intFunctional ℓ v : ℤ)) X V →
      V ⊆ coordinateBox M →
      UnshiftedIrreducible pkg δ γ V M →
      0 < γ → 0 ≤ δ → μ ≤ 1 →
      8 ≤ μ * (V.card : ℝ) →
      δ * (V.card : ℝ) ≤ (V.card : ℝ) - 1 →
      (∀ D : Finset (Fin d → ℤ), D ⊆ V →
        δ * (V.card : ℝ) ≤ (D.card : ℝ) →
        ∃ _hE : Eligible β pkg.m₀ D M,
          1 ≤ External.structureScale D.card ∧
          1 ≤ pkg.c * External.structureScale D.card ∧
          K < External.structureScale D.card * γ) →
      -- scale thresholds (`s₁ = s(n-1)`, `Rb = c⁻¹(n-1)/log(n-1)`)
      2 ≤ pkg.c * External.structureScale (V.card - 1) →
      1 < γ * ((coordinateBox M).card : ℝ) →
      (6 : ℝ) ^ d < pkg.c ^ d *
        (External.structureScale (V.card - 1) * γ) →
      Real.sqrt (d * (V.card : ℝ)) * 3 ≤
        pkg.c * External.structureScale (V.card - 1) / 2 →
      (12 / min pkg.c 8) ^ d * γ⁻¹ + 1 ≤ μ * (V.card : ℝ) / 8 →
      0 < μ * (V.card : ℝ) / 24 - 1 -
        (pkg.c⁻¹ * ((V.card - 1 : ℕ) : ℝ) /
            Real.log ((V.card - 1 : ℕ) : ℝ) +
          External.structureScale (V.card - 1)) / 2 -
        2 * (δ * (V.card : ℝ)) →
      (12 / min pkg.c 8) ^ d * γ⁻¹ + 1 +
        ((pkg.c⁻¹ * ((V.card - 1 : ℕ) : ℝ) /
            Real.log ((V.card - 1 : ℕ) : ℝ) +
          External.structureScale (V.card - 1)) / 2 +
          External.structureScale (V.card - 1)) ≤
        cw * γ * (μ * (V.card : ℝ) / 24 - 1 -
          (pkg.c⁻¹ * ((V.card - 1 : ℕ) : ℝ) /
              Real.log ((V.card - 1 : ℕ) : ℝ) +
            External.structureScale (V.card - 1)) / 2 -
          2 * (δ * (V.card : ℝ))) →
      IndexedMuConvexPosition μ
        (fun v : {x // x ∈ V} => projNorm ℓ v.1) := by
  classical
  obtain ⟨cw, K, hcw, hK, hasm⟩ := projective_convexity_assembled pkg hd
  refine ⟨cw, K, hcw, hK, ?_⟩
  intro ℓ X V M δ γ μ hX hshell hVbox hirr hγ hδ0 hμ1 h8 herase hsupply
    h2cs hγB h6d hsqrt hidx8 hgapT hεκT
  by_contra hnc
  obtain ⟨a, hfa⟩ := not_indexedMuConvexPosition_iff.mp hnc
  -- Basic cardinalities.
  set n : ℝ := (V.card : ℝ) with hn_def
  have hn8 : (8 : ℝ) ≤ n := by
    calc (8 : ℝ) ≤ μ * n := h8
      _ ≤ 1 * n := by
          refine mul_le_mul_of_nonneg_right hμ1 ?_
          exact Nat.cast_nonneg _
      _ = n := one_mul n
  have hn8N : 8 ≤ V.card := by
    have h := hn8
    rw [hn_def] at h
    exact_mod_cast h
  have hμpos : 0 < μ := by nlinarith [Nat.cast_nonneg (α := ℝ) V.card]
  have hμn0 : 0 < μ * n := by nlinarith
  -- The deleted set.
  set C : Finset (Fin d → ℤ) := V.erase a.1 with hC_def
  have hCV : C ⊆ V := Finset.erase_subset _ _
  have hscard : C.card = V.card - 1 := Finset.card_erase_of_mem a.2
  have hscardR : (C.card : ℝ) = n - 1 := by
    rw [hscard, hn_def]
    have : (1 : ℕ) ≤ V.card := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hCcard : δ * n ≤ (C.card : ℝ) := by rw [hscardR]; exact herase
  -- The duality weights.
  have hfail : ∀ u : Module.Dual ℝ (Fin d → ℝ),
      μ * V.card < ((V.filter fun k =>
        u (projNorm ℓ a.1) ≤ u (projNorm ℓ k)).card : ℝ) := by
    intro u
    have hfa' := hfa u (u (projNorm ℓ a.1)) le_rfl
    have hfe : (Finset.univ.filter fun k : {x // x ∈ V} =>
        u (projNorm ℓ a.1) ≤
          u ((fun v : {x // x ∈ V} => projNorm ℓ v.1) k))
        = Finset.univ.filter fun k : {x // x ∈ V} =>
            u (projNorm ℓ a.1) ≤ u (projNorm ℓ k.1) :=
      Finset.filter_congr fun k _ => Iff.rfl
    have hcard : (Finset.univ.filter fun k : {x // x ∈ V} =>
        u (projNorm ℓ a.1) ≤ u (projNorm ℓ k.1)).card
        = (V.filter fun k =>
            u (projNorm ℓ a.1) ≤ u (projNorm ℓ k)).card := by
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_coe_sort V
        (fun k => if u (projNorm ℓ a.1) ≤ u (projNorm ℓ k) then 1 else 0)]
    rw [hfe, hcard, Fintype.card_coe] at hfa'
    exact hfa'
  have hμn4 : 4 ≤ μ * (V.card : ℝ) := by linarith
  obtain ⟨βw, hrepr, hβbound, hβlo, hβhi⟩ :=
    projective_duality hX hshell.1 hμn4 a.2 hfail
  -- The rounded weights.
  set T : ℕ := ⌊μ * n / 8⌋₊ with hT_def
  have hTle : (T : ℝ) ≤ μ * n / 8 := Nat.floor_le (by positivity)
  have hTgt : μ * n / 8 - 1 < (T : ℝ) := Nat.sub_one_lt_floor _
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
  set θ : (Fin d → ℤ) → ℝ := fun v => (T : ℝ) * βw v with hθ_def
  have hθ0 : ∀ v ∈ C, 0 ≤ θ v := fun v hv =>
    mul_nonneg hT0 (hβbound v hv).1
  have hθhalf : ∀ v ∈ C, θ v ≤ 1 / 2 := by
    intro v hv
    have hb := (hβbound v hv).2
    have h1 : θ v ≤ (T : ℝ) * (4 / (μ * n)) :=
      mul_le_mul_of_nonneg_left hb hT0
    have h2 : (T : ℝ) * (4 / (μ * n)) ≤ (μ * n / 8) * (4 / (μ * n)) :=
      mul_le_mul_of_nonneg_right hTle (by positivity)
    have h3 : (μ * n / 8) * (4 / (μ * n)) = 1 / 2 := by
      field_simp
      norm_num
    linarith
  -- The package data for `C`.
  obtain ⟨hE_C, hsC1, hcsC1, hKsC⟩ := hsupply C hCV hCcard
  have hirrC := hirr C hCV hCcard hE_C
  -- Rewrite the thresholds in terms of `C.card`.
  rw [← hscard] at h2cs h6d hsqrt hgapT hεκT
  generalize hgen : pkg.out C M hE_C = o at hirrC
  obtain ⟨Chat, e, P, C₀, q, hChatsub, hChatcard, _hele, hcover, hC₀sub,
    hC₀card, hqmem, hincl, hinj⟩ := o
  obtain ⟨he, hPlow⟩ := hirrC
  have he' : d = e := he.symm
  subst he'
  -- Named scale.
  set s₁ : ℝ := External.structureScale C.card with hs₁_def
  have hs₁1 : 1 ≤ s₁ := hsC1
  have hs₁0 : 0 < s₁ := lt_of_lt_of_le one_pos hs₁1
  set cs : ℝ := pkg.c * s₁ with hcs_def
  have hcs1 : 1 ≤ cs := hcsC1
  -- Box positivity.
  have hBpos : (0 : ℝ) < ((coordinateBox M).card : ℝ) := by
    have : 0 < (coordinateBox M).card :=
      Finset.card_pos.mpr ⟨0, zero_mem_coordinateBox M⟩
    exact_mod_cast this
  -- Properness.
  have hP : P.Proper := P.proper_of_dilate hcs1 hinj
  -- The core is nonempty (`1 < γ|B|` forces `|P| ≥ 2`).
  have hC₀box : C₀ ⊆ coordinateBox M :=
    (hC₀sub.trans hChatsub).trans (hCV.trans hVbox)
  have hcard1 : 1 ≤ C₀.card := by
    by_contra hc0
    have hC₀e : C₀ = ∅ := Finset.card_eq_zero.mp (by omega)
    have hsub1 : subsetSums C₀ ⊆ {0} := by
      intro x hx
      obtain ⟨S, hS, hsum⟩ := mem_subsetSums.mp hx
      rw [hC₀e, Finset.subset_empty] at hS
      rw [Finset.mem_singleton, ← hsum, hS, Finset.sum_empty]
    have hcar2 : 2 ≤ P.carrier.card := by
      have h1 : (1 : ℝ) < (P.carrier.card : ℝ) :=
        lt_of_lt_of_le hγB hPlow
      exact_mod_cast Nat.lt_iff_add_one_le.mp (by exact_mod_cast h1)
    have hcarsub : P.carrier ⊆ P.dilatedCarrier cs := by
      rw [GAP.carrier, GAP.dilatedCarrier]
      exact Finset.image_subset_image
        (P.coeffBox_subset_dilatedCoeffBox hcs1)
    have hmap : (P.dilatedCarrier cs).card ≤ (subsetSums C₀).card := by
      refine Finset.card_le_card_of_injOn (fun z => q + z)
        (fun z hz => hincl z hz) ?_
      intro z₁ _ z₂ _ hz
      exact add_left_cancel hz
    have hone : (subsetSums C₀).card ≤ 1 :=
      le_trans (Finset.card_le_card hsub1) (by simp)
    have := le_trans (Finset.card_le_card hcarsub) hmap
    omega
  -- Full rank.
  have hrank : P.realRank = d :=
    realRank_eq_of_index hd P hP pkg.c_pos hs₁1 hγ hcs1 hinj hC₀box
      hcard1 hC₀card hincl hBpos hPlow h6d
  have hinjfun : Function.Injective P.evalHom := evalHom_injective P hrank
  -- Index bound with the capped constant `c' = min c 8`.
  set c' : ℝ := min pkg.c 8 with hc'_def
  have hc'0 : 0 < c' := lt_min pkg.c_pos (by norm_num)
  have hc'8 : c' ≤ 8 := min_le_right _ _
  have hc'c : c' ≤ pkg.c := min_le_left _ _
  have hincl' : ∀ z ∈ P.dilatedCarrier (c' * s₁), q + z ∈ subsetSums C₀ :=
    fun z hz => hincl z (P.dilatedCarrier_mono
      (mul_le_mul_of_nonneg_right hc'c hs₁0.le) hz)
  have hc's2 : 2 ≤ c' * s₁ := by
    rcases le_total pkg.c 8 with hc8 | hc8
    · rw [hc'_def, min_eq_left hc8]
      exact h2cs
    · rw [hc'_def, min_eq_right hc8]
      nlinarith
  have hidxbound : ((LinearMap.range
      P.evalHom.toIntLinearMap).toAddSubgroup.index : ℝ) ≤
      (12 / c') ^ d * γ⁻¹ :=
    index_bound_part2 P hP hinjfun hc'0 hc'8 hs₁0 hc's2 hC₀box hC₀card
      hincl' hγ hPlow hBpos
  -- The tube radius.
  set ξn : ℕ := ⌈(12 / c') ^ d * γ⁻¹⌉₊ with hξn_def
  have hidxξ : (LinearMap.range
      P.evalHom.toIntLinearMap).toAddSubgroup.index ≤ ξn := by
    have h1 : ((LinearMap.range
        P.evalHom.toIntLinearMap).toAddSubgroup.index : ℝ) ≤ (ξn : ℝ) :=
      le_trans hidxbound (Nat.le_ceil _)
    exact_mod_cast h1
  have hidxT : (LinearMap.range
      P.evalHom.toIntLinearMap).toAddSubgroup.index ≤ T := by
    have h1 : ((LinearMap.range
        P.evalHom.toIntLinearMap).toAddSubgroup.index : ℝ) ≤ (T : ℝ) := by
      calc ((LinearMap.range
          P.evalHom.toIntLinearMap).toAddSubgroup.index : ℝ)
          ≤ (12 / c') ^ d * γ⁻¹ := hidxbound
        _ ≤ μ * n / 8 - 1 := by linarith
        _ ≤ (T : ℝ) := by linarith
    exact_mod_cast h1
  -- The support of the mass.
  set Cbar : Finset (Fin d → ℤ) := Chat \ C₀ with hCbar_def
  have hCbarC : Cbar ⊆ C := (Finset.sdiff_subset).trans hChatsub
  have hCbarV : Cbar ⊆ V := hCbarC.trans hCV
  have hCbarP : Cbar ⊆ P.carrier := by
    refine (Finset.sdiff_subset).trans ?_
    exact (Finset.subset_union_left).trans hcover
  -- The discarded set.
  set Rb : ℝ := pkg.c⁻¹ * (C.card : ℝ) / Real.log (C.card : ℝ) with hRb_def
  have hdiff_sub : C \ Cbar ⊆ (C \ Chat) ∪ C₀ := by
    intro z hz
    rw [Finset.mem_sdiff, hCbar_def, Finset.mem_sdiff] at hz
    rw [Finset.mem_union, Finset.mem_sdiff]
    by_cases hzC : z ∈ C₀
    · exact Or.inr hzC
    · exact Or.inl ⟨hz.1, fun hchat => hz.2 ⟨hchat, hzC⟩⟩
  have hdiff_card : ((C \ Cbar).card : ℝ) ≤ Rb + s₁ := by
    have h1 : (C \ Cbar).card ≤ (C \ Chat).card + C₀.card :=
      le_trans (Finset.card_le_card hdiff_sub) (Finset.card_union_le _ _)
    have h2 : ((C \ Chat).card : ℝ) ≤ Rb := hChatcard
    have h3 : (C₀.card : ℝ) ≤ s₁ := hC₀card
    have h4 : ((C \ Cbar).card : ℝ) ≤
        ((C \ Chat).card : ℝ) + (C₀.card : ℝ) := by exact_mod_cast h1
    linarith
  -- The mass.
  set m : ℝ := μ * n / 24 - 1 - (Rb + s₁) / 2 with hm_def
  have hθsum_sdiff : ∑ v ∈ C \ Cbar, θ v ≤ (Rb + s₁) / 2 := by
    have h1 : ∑ v ∈ C \ Cbar, θ v ≤ ∑ _v ∈ C \ Cbar, (1 / 2 : ℝ) :=
      Finset.sum_le_sum fun v hv =>
        hθhalf v (Finset.mem_sdiff.mp hv).1
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ((C \ Cbar).card : ℝ) * (1 / 2) ≤ (Rb + s₁) / 2 := by
      linarith [hdiff_card]
    linarith
  have hθsum_C : (T : ℝ) / 3 ≤ ∑ v ∈ C, θ v := by
    rw [hθ_def]
    rw [← Finset.mul_sum]
    have hβlo' : 1 / 3 ≤ ∑ v ∈ C, βw v := by
      rw [hC_def]; exact hβlo
    calc (T : ℝ) / 3 = (T : ℝ) * (1 / 3) := by ring
      _ ≤ (T : ℝ) * ∑ v ∈ C, βw v :=
          mul_le_mul_of_nonneg_left hβlo' hT0
  have hmass : m ≤ ∑ v ∈ Cbar, θ v := by
    have hsplit : ∑ v ∈ C \ Cbar, θ v + ∑ v ∈ Cbar, θ v = ∑ v ∈ C, θ v :=
      Finset.sum_sdiff hCbarC
    have h1 : (T : ℝ) / 3 - (Rb + s₁) / 2 ≤ ∑ v ∈ Cbar, θ v := by
      linarith
    have h2 : m ≤ (T : ℝ) / 3 - (Rb + s₁) / 2 := by
      rw [hm_def]
      have : μ * n / 24 - 1 / 3 ≤ (T : ℝ) / 3 := by linarith
      linarith
    linarith
  -- The gap and the tube-radius threshold.
  have hgap : 0 < m - 2 * (δ * n) := by
    rw [hm_def]
    linarith [hgapT]
  set ε₂ : ℝ := (Rb + s₁) / 2 + s₁ with hε₂_def
  have hε₂0 : 0 ≤ ε₂ := by
    have hlog : 0 < Real.log (C.card : ℝ) := by
      refine Real.log_pos ?_
      rw [hscardR]
      linarith
    have hRb0 : 0 ≤ Rb := by
      rw [hRb_def]
      have h1 : 0 ≤ pkg.c⁻¹ := (inv_pos.mpr pkg.c_pos).le
      positivity
    rw [hε₂_def]
    linarith
  have hεκ : ((ξn : ℝ) + ε₂) ≤ (cw * γ) * (m - 2 * (δ * n)) := by
    have hξle : (ξn : ℝ) ≤ (12 / c') ^ d * γ⁻¹ + 1 := by
      rw [hξn_def]
      have h0 : (0 : ℝ) ≤ (12 / c') ^ d * γ⁻¹ := by positivity
      linarith [Nat.ceil_lt_add_one h0]
    rw [hε₂_def, hm_def]
    calc (ξn : ℝ) + ((Rb + s₁) / 2 + s₁)
        ≤ (12 / c') ^ d * γ⁻¹ + 1 + ((Rb + s₁) / 2 + s₁) := by linarith
      _ ≤ cw * γ * (μ * n / 24 - 1 - (Rb + s₁) / 2 - 2 * (δ * n)) := hεκT
      _ = (cw * γ) * (μ * n / 24 - 1 - (Rb + s₁) / 2 - 2 * (δ * n)) := rfl
      _ = (cw * γ) * (μ * n / 24 - 1 - (Rb + s₁) / 2 - 2 * (δ * n)) := rfl
  -- The filling threshold.
  have hthr : Real.sqrt (d * (Cbar.card + 1)) * 3 ≤ cs / 2 := by
    have hCbarcard : (Cbar.card : ℝ) + 1 ≤ n := by
      have h1 : Cbar.card ≤ C.card := Finset.card_le_card hCbarC
      have h2 : (Cbar.card : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast h1
      rw [hscardR] at h2
      linarith
    have hmono : Real.sqrt (d * (Cbar.card + 1)) ≤
        Real.sqrt (d * n) := by
      refine Real.sqrt_le_sqrt ?_
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul_of_nonneg_left hCbarcard hd0
    calc Real.sqrt (d * (Cbar.card + 1)) * 3
        ≤ Real.sqrt (d * n) * 3 := by linarith
      _ ≤ cs / 2 := hsqrt
  -- The core inclusion and its translate.
  have hq0 : q ∈ subsetSums C₀ := by
    have h0 := hincl 0 (P.zero_mem_dilatedCarrier cs)
    rwa [add_zero] at h0
  have hqbound : ∀ i, |(q i : ℝ)| ≤ s₁ * (M i : ℝ) := by
    intro i
    have hsub := subsetSums_subset_coordinateBox hC₀box (le_refl C₀.card)
    have hmem := (mem_coordinateBox.mp (hsub hq0)) i
    have hz : |q i| ≤ ((C₀.card * M i : ℕ) : ℤ) := abs_le.mpr hmem
    have hcast : |(q i : ℝ)| ≤ (C₀.card : ℝ) * (M i : ℝ) := by
      rw [← Int.cast_abs]
      calc ((|q i| : ℤ) : ℝ) ≤ (((C₀.card * M i : ℕ) : ℤ) : ℝ) := by
            exact_mod_cast hz
        _ = (C₀.card : ℝ) * (M i : ℝ) := by push_cast; ring
    refine hcast.trans ?_
    exact mul_le_mul_of_nonneg_right hC₀card (Nat.cast_nonneg _)
  -- The centre closeness.
  have hTa : ∀ i, (T : ℝ) * (a.1 i : ℝ) = ∑ v ∈ C, θ v * (v i : ℝ) := by
    intro i
    have h := congrFun hrepr i
    rw [Finset.sum_apply] at h
    have h1 : (a.1 i : ℝ) = ∑ v ∈ C, βw v * (v i : ℝ) := by
      rw [show External.realPoint a.1 i = (a.1 i : ℝ) from rfl] at h
      rw [h]
      exact Finset.sum_congr rfl fun v _ => by
        rw [Pi.smul_apply, smul_eq_mul]
        rfl
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [hθ_def]; ring
  have hcentre : ∀ i, |(((T • a.1 - q) i : ℤ) : ℝ) -
      ∑ v ∈ Cbar, θ v * (v i : ℝ)| ≤ ε₂ * (M i : ℝ) := by
    intro i
    have hcast : (((T • a.1 - q) i : ℤ) : ℝ) =
        (T : ℝ) * (a.1 i : ℝ) - (q i : ℝ) := by
      have h1 : (T • a.1 - q) i = (T : ℤ) * a.1 i - q i := by
        simp [Pi.sub_apply]
      rw [h1]
      push_cast
      ring
    have hsdiff : ∑ v ∈ C, θ v * (v i : ℝ) -
        ∑ v ∈ Cbar, θ v * (v i : ℝ) =
        ∑ v ∈ C \ Cbar, θ v * (v i : ℝ) := by
      have := Finset.sum_sdiff (f := fun v => θ v * (v i : ℝ)) hCbarC
      exact (eq_sub_of_add_eq this).symm
    have hbound : |∑ v ∈ C \ Cbar, θ v * (v i : ℝ)| ≤
        (Rb + s₁) / 2 * (M i : ℝ) := by
      have h1 : |∑ v ∈ C \ Cbar, θ v * (v i : ℝ)| ≤
          ∑ v ∈ C \ Cbar, |θ v * (v i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∀ v ∈ C \ Cbar, |θ v * (v i : ℝ)| ≤
          (1 / 2) * (M i : ℝ) := by
        intro v hv
        have hvC := (Finset.mem_sdiff.mp hv).1
        have hvbox := (hCV.trans hVbox) hvC
        have hvi := (mem_coordinateBox.mp hvbox) i
        have hviR : |(v i : ℝ)| ≤ (M i : ℝ) := by
          rw [← Int.cast_abs]
          have : |v i| ≤ (M i : ℤ) := abs_le.mpr hvi
          exact_mod_cast this
        rw [abs_mul]
        have hθv : |θ v| ≤ 1 / 2 := by
          rw [abs_of_nonneg (hθ0 v hvC)]
          exact hθhalf v hvC
        exact mul_le_mul hθv hviR (abs_nonneg _) (by norm_num)
      have h3 : ∑ v ∈ C \ Cbar, |θ v * (v i : ℝ)| ≤
          ((C \ Cbar).card : ℝ) * ((1 / 2) * (M i : ℝ)) := by
        have := Finset.sum_le_card_nsmul (C \ Cbar)
          (fun v => |θ v * (v i : ℝ)|) ((1 / 2) * (M i : ℝ)) h2
        rw [nsmul_eq_mul] at this
        exact this
      have h4 : ((C \ Cbar).card : ℝ) * ((1 / 2) * (M i : ℝ)) ≤
          (Rb + s₁) / 2 * (M i : ℝ) := by
        have hM0 : (0 : ℝ) ≤ (M i : ℝ) := Nat.cast_nonneg _
        have h5 := mul_le_mul_of_nonneg_right hdiff_card hM0
        linarith only [h5]
      linarith only [h1, h3, h4]
    calc |(((T • a.1 - q) i : ℤ) : ℝ) - ∑ v ∈ Cbar, θ v * (v i : ℝ)|
        = |∑ v ∈ C \ Cbar, θ v * (v i : ℝ) - (q i : ℝ)| := by
          rw [hcast, hTa i]
          congr 1
          linarith only [hsdiff]
      _ ≤ |∑ v ∈ C \ Cbar, θ v * (v i : ℝ)| + |(q i : ℝ)| := by
          exact abs_sub _ _
      _ ≤ (Rb + s₁) / 2 * (M i : ℝ) + s₁ * (M i : ℝ) := by
          linarith only [hbound, hqbound i]
      _ = ε₂ * (M i : ℝ) := by rw [hε₂_def]; ring
  -- The evaluated translate.
  obtain ⟨nq, _hnq, hnq_eval⟩ := (P.mem_dilatedCarrier).mp hqmem
  -- Feed everything into the assembled contradiction.
  exact hasm (intFunctional ℓ) X V Cbar C₀ M δ γ m cs ε₂ θ P q nq a.1 T ξn
    hX hshell a.2 (hVbox a.2) hirr hCbarV hγ hδ0
    (fun D hDV hDcard => hsupply D hDV hDcard)
    (fun v hv => hθ0 v (hCbarC hv)) (fun v hv => hθhalf v (hCbarC hv))
    hmass hgap hε₂0 hεκ hrank hCbarP (by positivity) hthr hincl
    Finset.sdiff_disjoint
    (by
      rw [Finset.union_comm]
      refine Finset.union_subset ?_ ?_
      · exact hC₀sub.trans hChatsub
      · exact (Finset.sdiff_subset).trans hChatsub)
    hnq_eval hidxT hidxξ hcentre

/-! ## 8. Assembly: `IrreducibleIncrement` from numeric thresholds only

The structural clauses of the per-stage supplier of
`irreducibleIncrement_of_convexPosition` are discharged here:

* the coefficient-vector form of the stage functional
  (`addMonoidHom_eq_intFunctional` — every `→+` hom on `Fin d → ℤ` is an
  `intFunctional`);
* `integerRealSpan V = ⊤` (`stage_span_of_thresholds`, via
  `projective_span_package` with the core nonemptiness `one_le_core_card`);
* `IndexedMuConvexPosition` (`stage_convexPosition_of_thresholds`, §7).

What remains in the supplier of `irreducibleIncrement_of_numerics` is purely
numeric: the parameter regime `0 < μ < min(1, μ₀ d)`, `δ ≤ μ^{1+ε}`,
`n ≥ n₀(d,μ)`, the eligibility/scale clause on `δ`-large subsets
(manuscript `s(δn)⁻¹ = o(γ)`), the scale/gap thresholds of §7 (all of the
form "`n` large relative to `μ, δ, γ`" in the manuscript hierarchy), and the
absorption numerics for `η ∈ [μ, μ^τ]`. -/

/-- Every additive-monoid hom `(Fin d → ℤ) →+ ℤ` is the integer functional of
its coefficient vector `i ↦ lam (Pi.single i 1)`. -/
theorem addMonoidHom_eq_intFunctional {d : ℕ} (lam : (Fin d → ℤ) →+ ℤ)
    (v : Fin d → ℤ) :
    lam v = intFunctional (fun i => lam (Pi.single i 1)) v := by
  rw [intFunctional_apply]
  have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  calc lam v = lam (∑ i, Pi.single i (v i)) := by rw [← hv]
    _ = ∑ i, lam (Pi.single i (v i)) := map_sum lam _ _
    _ = ∑ i, lam (Pi.single i 1) * v i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h1 : Pi.single i (v i) =
            v i • (Pi.single i 1 : Fin d → ℤ) := by
          rw [← Pi.single_smul, smul_eq_mul, mul_one]
        rw [h1, map_zsmul, smul_eq_mul]
        ring

/-- **Core nonemptiness.**  Once the progression occupies a `γ`-fraction of the
box and `γ|B| > 1`, the progression has at least two points; since the
`cs`-dilate injects (translated) into `subsetSums C₀`, the core `C₀` cannot be
empty. -/
theorem one_le_core_card {d : ℕ} {β : ℝ} (pkg : Package d β)
    {C : Finset (Fin d → ℤ)} {M : Fin d → ℕ} (hE : Eligible β pkg.m₀ C M)
    (hcs1 : 1 ≤ pkg.c * External.structureScale C.card) {γ : ℝ}
    (hγB : 1 < γ * ((coordinateBox M).card : ℝ))
    (hPlow : γ * ((coordinateBox M).card : ℝ) ≤
      ((pkg.out C M hE).P.carrier.card : ℝ)) :
    1 ≤ (pkg.out C M hE).C₀.card := by
  classical
  set o := pkg.out C M hE with ho
  by_contra hc0
  have hC₀e : o.C₀ = ∅ := Finset.card_eq_zero.mp (by omega)
  have hsub1 : subsetSums o.C₀ ⊆ {0} := by
    intro x hx
    obtain ⟨S, hS, hsum⟩ := mem_subsetSums.mp hx
    rw [hC₀e, Finset.subset_empty] at hS
    rw [Finset.mem_singleton, ← hsum, hS, Finset.sum_empty]
  have hcar2 : 2 ≤ o.P.carrier.card := by
    have h1 : (1 : ℝ) < (o.P.carrier.card : ℝ) := lt_of_lt_of_le hγB hPlow
    exact_mod_cast Nat.lt_iff_add_one_le.mp (by exact_mod_cast h1)
  have hcarsub : o.P.carrier ⊆
      o.P.dilatedCarrier (pkg.c * External.structureScale C.card) := by
    rw [GAP.carrier, GAP.dilatedCarrier]
    exact Finset.image_subset_image
      (o.P.coeffBox_subset_dilatedCoeffBox hcs1)
  have hmap : (o.P.dilatedCarrier
      (pkg.c * External.structureScale C.card)).card ≤
      (subsetSums o.C₀).card := by
    refine Finset.card_le_card_of_injOn (fun z => o.q + z)
      (fun z hz => o.incl z hz) ?_
    intro z₁ _ z₂ _ hz
    exact add_left_cancel hz
  have hone : (subsetSums o.C₀).card ≤ 1 :=
    le_trans (Finset.card_le_card hsub1) (by simp)
  have := le_trans (Finset.card_le_card hcarsub) hmap
  omega

/-- **Stage span** (`lem:projective-span` at the stage level): an unshiftedly
irreducible eligible stage set spans `ℝ^d` once the scale product clears the
`6^d` threshold and the progression fraction exceeds one point. -/
theorem stage_span_of_thresholds {d : ℕ} {β : ℝ} (pkg : Package d β)
    (hd : 1 ≤ d) {V : Finset (Fin d → ℤ)} {M : Fin d → ℕ} {δ γ : ℝ}
    (hirr : UnshiftedIrreducible pkg δ γ V M)
    (hE : Eligible β pkg.m₀ V M) (hδ1 : δ ≤ 1) (hγ : 0 < γ)
    (hs : 1 ≤ External.structureScale V.card)
    (hcs : 1 ≤ pkg.c * External.structureScale V.card)
    (hγB : 1 < γ * ((coordinateBox M).card : ℝ))
    (hthresh : (6 : ℝ) ^ d < pkg.c ^ d *
      (External.structureScale V.card * γ)) :
    integerRealSpan V = ⊤ := by
  obtain ⟨he, hPlow⟩ := hirr.self hδ1 (Nat.cast_nonneg _) hE
  exact projective_span_package hd pkg hE hγ he hs hcs
    (one_le_core_card pkg hE hcs hγB hPlow) hPlow hthresh

/-- **`IrreducibleIncrement` from numeric thresholds.**  All structural
clauses of the per-stage supplier (functional form, span, `μ`-convex
position) are discharged; what remains is the numeric regime listed in the
section header.  The constants `tau, K, C, μ₀, cw, n₀` are produced by the
pipeline. -/
theorem irreducibleIncrement_of_numerics {β : ℝ}
    (pkgs : ∀ r, Package r β) (eps : ℝ) (heps : 0 < eps) (Dcap : ℕ) :
    ∃ (tau K C μ₀ cw : ℕ → ℝ) (n₀ : ℕ → ℝ → ℕ),
      (∀ d, 0 < tau d ∧ tau d < 1 ∧ 0 < K d ∧ 0 < C d ∧ 0 < μ₀ d ∧
        0 < cw d) ∧
      ∀ (ζ₀ ε δ γ ν : ℝ) (n₁ n₂ : ℕ), 2 ≤ n₁ → n₁ ≤ n₂ →
      (∀ (X : ℕ) (s : PrepStage X), 1 ≤ X → n₂ ≤ s.V.card → s.dim ≤ Dcap →
        ExcessiveStage ζ₀ s →
        StageIrreducible pkgs δ γ s →
        ∃ μ : ℝ,
          0 < μ ∧ μ < 1 ∧ μ < μ₀ s.dim ∧
          n₀ s.dim μ ≤ s.V.card ∧
          0 < γ ∧ 0 ≤ δ ∧ δ ≤ μ ^ ((1 : ℝ) + eps) ∧
          8 ≤ μ * (s.V.card : ℝ) ∧
          δ * (s.V.card : ℝ) ≤ (s.V.card : ℝ) - 1 ∧
          (∀ W : Finset (Fin s.dim → ℤ), W ⊆ s.V →
            δ * (s.V.card : ℝ) ≤ (W.card : ℝ) →
            Eligible β (pkgs s.dim).m₀ W s.M ∧
            1 ≤ External.structureScale W.card ∧
            1 ≤ (pkgs s.dim).c * External.structureScale W.card ∧
            K s.dim < External.structureScale W.card * γ) ∧
          1 < γ * ((coordinateBox s.M).card : ℝ) ∧
          (6 : ℝ) ^ s.dim < (pkgs s.dim).c ^ s.dim *
            (External.structureScale s.V.card * γ) ∧
          2 ≤ (pkgs s.dim).c * External.structureScale (s.V.card - 1) ∧
          (6 : ℝ) ^ s.dim < (pkgs s.dim).c ^ s.dim *
            (External.structureScale (s.V.card - 1) * γ) ∧
          Real.sqrt (s.dim * (s.V.card : ℝ)) * 3 ≤
            (pkgs s.dim).c * External.structureScale (s.V.card - 1) / 2 ∧
          (12 / min (pkgs s.dim).c 8) ^ s.dim * γ⁻¹ + 1 ≤
            μ * (s.V.card : ℝ) / 8 ∧
          0 < μ * (s.V.card : ℝ) / 24 - 1 -
            ((pkgs s.dim).c⁻¹ * ((s.V.card - 1 : ℕ) : ℝ) /
                Real.log ((s.V.card - 1 : ℕ) : ℝ) +
              External.structureScale (s.V.card - 1)) / 2 -
            2 * (δ * (s.V.card : ℝ)) ∧
          (12 / min (pkgs s.dim).c 8) ^ s.dim * γ⁻¹ + 1 +
            (((pkgs s.dim).c⁻¹ * ((s.V.card - 1 : ℕ) : ℝ) /
                Real.log ((s.V.card - 1 : ℕ) : ℝ) +
              External.structureScale (s.V.card - 1)) / 2 +
              External.structureScale (s.V.card - 1)) ≤
            cw s.dim * γ * (μ * (s.V.card : ℝ) / 24 - 1 -
              ((pkgs s.dim).c⁻¹ * ((s.V.card - 1 : ℕ) : ℝ) /
                  Real.log ((s.V.card - 1 : ℕ) : ℝ) +
                External.structureScale (s.V.card - 1)) / 2 -
              2 * (δ * (s.V.card : ℝ))) ∧
          (∀ η : ℝ, μ ≤ η → η ≤ μ ^ tau s.dim →
            C s.dim * η < 1 ∧
            (C s.dim * η) ^ (sigma s.dim + ζ₀ - ν) ≤
              η ^ (((s.dim : ℝ) - 2) / (s.dim : ℝ) + eps) ∧
            (n₁ : ℝ) ≤ η ^ (((s.dim : ℝ) - 2) / (s.dim : ℝ) + eps) *
              (s.V.card : ℝ))) →
      IrreducibleIncrementCapped pkgs Dcap ζ₀ ε δ γ ν n₁ n₂ := by
  classical
  obtain ⟨tau, K₁, C, μ₀, n₀, hpos, hmainIC⟩ :=
    irreducibleIncrement_of_convexPosition (β := β) pkgs eps heps Dcap
  have hconvAll := fun r : ℕ =>
    stage_convexPosition_of_thresholds (pkgs (r + 1)) (Nat.le_add_left 1 r)
  choose cw₀ K₂ hcw₀ hK₂ hconvmain using hconvAll
  refine ⟨tau, fun d => max (K₁ d) (K₂ (d - 1)), C, μ₀,
    fun d => cw₀ (d - 1), n₀, ?_, ?_⟩
  · intro d
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpos d
    exact ⟨h1, h2, lt_max_of_lt_left h3, h4, h5, hcw₀ _⟩
  · intro ζ₀ ε δ γ ν n₁ n₂ hn₁ hn₁₂ hsupnum
    refine hmainIC ζ₀ ε δ γ ν n₁ n₂ hn₁ hn₁₂ ?_
    intro X s hX hn hcap hexc hirr
    obtain ⟨d, V, M, lam, hsub, hshell⟩ := s
    obtain ⟨μ, hμ0, hμ1, hμμ₀, hn₀le, hγ, hδ0, hδμ, hμn8, hδn1, hWsup,
      hγB, h6dV, h2cs, h6d, hsqrt, hidx8, hgapT, hεκT, habs⟩ :=
      hsupnum X ⟨d, V, M, lam, hsub, hshell⟩ hX hn hcap hexc hirr
    rcases d with _ | r
    · -- Dimension 0: the box has one point, contradicting `n₁ ≥ 2`.
      exfalso
      have hbox1 : (coordinateBox M).card = 1 := by
        rw [card_coordinateBox]
        simp
      have hV1 : V.card ≤ 1 := hbox1 ▸ Finset.card_le_card hsub
      have hncard' : n₁ ≤ V.card := le_trans hn₁₂ hn
      omega
    · -- Dimension `r + 1`.
      set ℓ : Fin (r + 1) → ℤ := fun i => lam (Pi.single i 1) with hℓ_def
      have hlam : ∀ v, lam v = intFunctional ℓ v := fun v =>
        addMonoidHom_eq_intFunctional lam v
      have hirr' : UnshiftedIrreducible (pkgs (r + 1)) δ γ V M := hirr
      have hshell' : ShellNonDividing
          (fun v => (intFunctional ℓ v : ℤ)) X V := by
        have hfe : (fun v => lam v) = fun v => (intFunctional ℓ v : ℤ) :=
          funext hlam
        rwa [hfe] at hshell
      -- Eligibility and scales of the full stage set.
      have hδVn : δ * (V.card : ℝ) ≤ (V.card : ℝ) := by linarith
      obtain ⟨hE_V, hsV, hcsV, _⟩ := hWsup V Finset.Subset.rfl hδVn
      -- `δ ≤ 1` from the regime.
      have hδ1 : δ ≤ 1 := by
        have h1 : μ ^ ((1 : ℝ) + eps) < 1 :=
          Real.rpow_lt_one hμ0.le hμ1 (by linarith)
        linarith
      -- Span of the stage set.
      have hspan : integerRealSpan V = ⊤ :=
        stage_span_of_thresholds (pkgs (r + 1)) (Nat.le_add_left 1 r)
          hirr' hE_V hδ1 hγ hsV hcsV hγB h6dV
      -- μ-convex position from §7.
      have hconv : IndexedMuConvexPosition μ
          (fun v : {x // x ∈ V} => projNorm ℓ v.1) :=
        hconvmain r ℓ X V M δ γ μ hX hshell' hsub hirr' hγ hδ0 hμ1.le
          hμn8 hδn1
          (fun D hDV hDcard =>
            ⟨(hWsup D hDV hDcard).1,
              (hWsup D hDV hDcard).2.1,
              (hWsup D hDV hDcard).2.2.1,
              lt_of_le_of_lt (le_max_right (K₁ (r + 1)) (K₂ r))
                (hWsup D hDV hDcard).2.2.2⟩)
          h2cs hγB h6d hsqrt hidx8 hgapT hεκT
      exact ⟨ℓ, μ, hlam, hμ0, hμ1, hμμ₀, hn₀le, hγ, hδμ, hspan,
        (fun W hWV hWcard =>
          ⟨(hWsup W hWV hWcard).1, (hWsup W hWV hWcard).2.1,
            (hWsup W hWV hWcard).2.2.1,
            lt_of_le_of_lt (le_max_left (K₁ (r + 1)) (K₂ r))
              (hWsup W hWV hWcard).2.2.2⟩),
        hconv, habs⟩

end Nondividing
