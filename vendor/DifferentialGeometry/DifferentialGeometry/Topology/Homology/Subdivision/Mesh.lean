module

public import DifferentialGeometry.Topology.Homology.Subdivision.AffinePieces
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

noncomputable section

open Finset

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem dist_vertexBarycenter_le (n : ℕ) (v : Fin (n + 1) → E) (j : Fin (n + 1)) {D : ℝ}
    (hv : ∀ i j, dist (v i) (v j) ≤ D) :
    dist (Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v) (v j) ≤
      (n : ℝ) / (n + 1) * D := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have he : Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v - v j =
      ((n : ℝ) + 1)⁻¹ • ∑ i, (v i - v j) := by
    simp only [Finset.centerMass, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, one_smul, Nat.cast_add, Nat.cast_one, nsmul_eq_mul, mul_one,
      Finset.sum_sub_distrib]
    rw [smul_sub]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hn]
  have hs : (∑ i, ‖v i - v j‖) ≤ (n : ℝ) * D := by
    calc
      _ = ∑ i ∈ Finset.univ.erase j, ‖v i - v j‖ := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
        simp
      _ ≤ ∑ _i ∈ Finset.univ.erase j, D := by
        apply Finset.sum_le_sum
        intro i _
        exact (dist_eq_norm (v i) (v j)) ▸ hv i j
      _ = _ := by simp
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((n : ℝ) + 1)⁻¹ * (∑ i, ‖v i - v j‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring


theorem dist_affineSimplex_le {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ}
    (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (affineSimplex v x) (affineSimplex v y) ≤ D := by
  have hy : ∀ i, affineSimplex v y ∈ Metric.closedBall (v i) D := fun i ↦
    range_affineSimplex_subset v (convex_closedBall (v i) D)
      (fun j ↦ hv j i) ⟨y, rfl⟩
  exact range_affineSimplex_subset v (convex_closedBall (affineSimplex v y) D)
    (fun i ↦ by simpa only [Metric.mem_closedBall, dist_comm] using hy i) ⟨x, rfl⟩


theorem dist_barycentricPieceVertices_le (n : ℕ) (v : Fin (n + 1) → E)
    (p : BarycentricFlag n) {D : ℝ} (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (i j : Fin (n + 1)) :
    dist (barycentricPieceVertices n v p i) (barycentricPieceVertices n v p j) ≤
      (n : ℝ) / (n + 1) * D := by
  induction n with
  | zero =>
    have hij : i = j := @Subsingleton.elim (Fin 1) inferInstance i j
    rw [hij, dist_self]
    simp
  | succ n hn =>
    have hD : 0 ≤ D := le_trans dist_nonneg (hv 0 0)
    have hface : ∀ a b, dist ((v ∘ p.1.succAbove) a) ((v ∘ p.1.succAbove) b) ≤ D :=
      fun a b ↦ hv _ _
    have hapex (a : Fin (n + 1)) :
        dist (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2 a)
            (Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v) ≤
          ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1) * D := by
      apply barycentricPieceVertices_mem n (v ∘ p.1.succAbove) p.2
        (convex_closedBall _ _) _ a
      intro b
      exact (dist_comm _ _).le.trans (dist_vertexBarycenter_le (n + 1) v _ hv)
    refine Fin.cases ?_ (fun a ↦ ?_) i
    · refine Fin.cases ?_ (fun b ↦ ?_) j
      · change dist _ _ ≤ _
        rw [dist_self]
        positivity
      · change dist (Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v)
          (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2 b) ≤ _
        rw [dist_comm]
        exact hapex b
    · refine Fin.cases ?_ (fun b ↦ ?_) j
      · exact hapex a
      · change dist (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2 a)
          (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2 b) ≤ _
        refine (hn (v ∘ p.1.succAbove) p.2 hface a b).trans ?_
        apply mul_le_mul_of_nonneg_right _ hD
        push_cast
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith


theorem dist_affineBarycentricPiece_le (n : ℕ) (v : Fin (n + 1) → E)
    (p : BarycentricFlag n) {D : ℝ} (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (affineSimplex (barycentricPieceVertices n v p) x)
        (affineSimplex (barycentricPieceVertices n v p) y) ≤
      (n : ℝ) / (n + 1) * D :=
  dist_affineSimplex_le _ (dist_barycentricPieceVertices_le n v p hv) x y

end DifferentialGeometry.Homology
