module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

namespace DifferentialGeometry
namespace Analysis

open Filter Set
open scoped ContDiff

noncomputable section

theorem exists_contDiff_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ∞) (f : E → F) (c : E)
    (hf : ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ n f (Metric.ball c r)) :
    ∃ g : E → F, ContDiff ℝ n g ∧ g =ᶠ[nhds c] f := by
  rcases hf with ⟨r, hr, hfOn⟩
  let φ : ContDiffBump c :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g : E → F := fun x => φ x • f x
  have hφ0 : (φ : E → ℝ) =ᶠ[nhds c] (fun _ : E => (1 : ℝ)) := φ.eventuallyEq_one
  have hgEq : g =ᶠ[nhds c] f := by
    dsimp [g]
    filter_upwards [hφ0] with x hx
    simp [hx]
  have hgSmooth : ContDiff ℝ n g := by
    have hContDiffOn : ContDiffOn ℝ n g Set.univ := by
      rw [isOpen_univ.contDiffOn_iff]
      intro x hxuniv
      by_cases hx : x ∈ Metric.ball c r
      · have hφat : ContDiffAt ℝ n (fun y : E => (φ : E → ℝ) y) x :=
          ((φ.contDiff (n := n)) : ContDiff ℝ n (φ : E → ℝ)).contDiffAt
        have hfat : ContDiffAt ℝ n f x := by
          have hmp : ∀ ⦃a : E⦄, a ∈ Metric.ball c r → ContDiffAt ℝ n f a :=
            (IsOpen.contDiffOn_iff (Metric.isOpen_ball : IsOpen (Metric.ball c r))).mp hfOn
          exact hmp hx
        exact ContDiffAt.smul hφat hfat
      · have hxr : r ≤ dist x c := by
          have hnot : ¬ dist x c < r := by simpa [Metric.mem_ball, dist_comm] using hx
          exact not_lt.mp hnot
        have hdist : φ.rOut ≤ dist x c := by
          have hle : φ.rOut ≤ r := by dsimp [φ]; nlinarith [hr]
          exact le_trans hle hxr
        have hzero_near : ∀ᶠ y in nhds x, (φ : E → ℝ) y = 0 := by
          have hε : 0 < dist x c - φ.rOut := by
            dsimp [φ]
            nlinarith [hr, hxr]
          have hmem : Metric.ball x ((dist x c - φ.rOut) / 2) ∈ nhds x :=
            Metric.ball_mem_nhds x (by positivity)
          filter_upwards [hmem] with y hy
          apply (φ.zero_of_le_dist : φ.rOut ≤ dist y c → (φ : E → ℝ) y = 0)
          have hyx : dist y x < (dist x c - φ.rOut) / 2 := (Metric.mem_ball.mp hy)
          have htri : dist x c ≤ dist x y + dist y c := dist_triangle x y c
          linarith [htri, hyx, dist_comm y x]
        have hgzero : g =ᶠ[nhds x] (fun _ : E => (0 : F)) := by
          dsimp [g]
          filter_upwards [hzero_near] with y hy
          simp [hy]
        exact (contDiffAt_const : ContDiffAt ℝ n (fun _ : E => (0 : F)) x).congr_of_eventuallyEq hgzero
    exact (contDiffOn_univ (𝕜 := ℝ) (n := n) (f := g)).mp hContDiffOn
  exact ⟨g, hgSmooth, hgEq⟩

end

end Analysis
end DifferentialGeometry
