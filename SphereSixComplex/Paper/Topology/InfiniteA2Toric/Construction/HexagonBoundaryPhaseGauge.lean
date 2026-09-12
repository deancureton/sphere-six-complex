module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CompactPhaseCorrection

@[expose] public section

noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace Construction

public def hexagonVertexWeights (x : Fin 2 → ℝ) : Fin 6 → ℝ :=
  let a := (3 / 2 : ℝ) * x 0
  let b := (3 / 2 : ℝ) * x 1
  ![max 0 (min a (a - b)), max 0 (min a b), max 0 (min b (b - a)),
    max 0 (min (-a) (b - a)), max 0 (min (-a) (-b)), max 0 (min (-b) (a - b))]

public theorem continuous_hexagonVertexWeights :
    Continuous hexagonVertexWeights := by
  unfold hexagonVertexWeights
  fun_prop

private theorem hexagon_weights_edge_0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    hexagonVertexWeights
      ((1 - t) • planeVertexOffset 0 +
        t • planeNextVertexOffset 0) =
      fun j ↦ (if j = 0 then 1 - t else 0) +
        (if j = cellNextIndex 0 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [hexagonVertexWeights, planeVertexOffset,
      planeNextVertexOffset, cellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    hexagonVertexWeights
      ((1 - t) • planeVertexOffset 1 +
        t • planeNextVertexOffset 1) =
      fun j ↦ (if j = 1 then 1 - t else 0) +
        (if j = cellNextIndex 1 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [hexagonVertexWeights, planeVertexOffset,
      planeNextVertexOffset, cellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    hexagonVertexWeights
      ((1 - t) • planeVertexOffset 2 +
        t • planeNextVertexOffset 2) =
      fun j ↦ (if j = 2 then 1 - t else 0) +
        (if j = cellNextIndex 2 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [hexagonVertexWeights, planeVertexOffset,
      planeNextVertexOffset, cellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_3 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    hexagonVertexWeights
      ((1 - t) • planeVertexOffset 3 +
        t • planeNextVertexOffset 3) =
      fun j ↦ (if j = 3 then 1 - t else 0) +
        (if j = cellNextIndex 3 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [hexagonVertexWeights, planeVertexOffset,
      planeNextVertexOffset, cellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_4 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    hexagonVertexWeights
      ((1 - t) • planeVertexOffset 4 +
        t • planeNextVertexOffset 4) =
      fun j ↦ (if j = 4 then 1 - t else 0) +
        (if j = cellNextIndex 4 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [hexagonVertexWeights, planeVertexOffset,
      planeNextVertexOffset, cellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_5 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    hexagonVertexWeights
      ((1 - t) • planeVertexOffset 5 +
        t • planeNextVertexOffset 5) =
      fun j ↦ (if j = 5 then 1 - t else 0) +
        (if j = cellNextIndex 5 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [hexagonVertexWeights, planeVertexOffset,
      planeNextVertexOffset, cellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

public theorem hexagonVertexWeights_edge (i : Fin 6) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    hexagonVertexWeights
      ((1 - t) • planeVertexOffset i +
        t • planeNextVertexOffset i) =
      fun j ↦ (if j = i then 1 - t else 0) +
        (if j = cellNextIndex i then t else 0) := by
  fin_cases i
  · exact hexagon_weights_edge_0 t ht
  · exact hexagon_weights_edge_1 t ht
  · exact hexagon_weights_edge_2 t ht
  · exact hexagon_weights_edge_3 t ht
  · exact hexagon_weights_edge_4 t ht
  · exact hexagon_weights_edge_5 t ht

public def hexagonVertexInterpolation (v : Fin 6 → Fin 2 → ℝ)
    (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ∑ i, hexagonVertexWeights x i • v i

public theorem continuous_hexagonVertexInterpolation (v : Fin 6 → Fin 2 → ℝ) :
    Continuous (hexagonVertexInterpolation v) := by
  unfold hexagonVertexInterpolation
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_hexagonVertexWeights).smul
    continuous_const

public theorem hexagonVertexInterpolation_edge
    (v : Fin 6 → Fin 2 → ℝ) (i : Fin 6) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    hexagonVertexInterpolation v
      ((1 - t) • planeVertexOffset i +
        t • planeNextVertexOffset i) =
      (1 - t) • v i + t • v (cellNextIndex i) := by
  simp [hexagonVertexInterpolation,
    hexagonVertexWeights_edge i t ht, add_smul,
    Finset.sum_add_distrib, ite_smul]

public def boundaryAngleVertices (a b c d : ℝ) : Fin 6 → Fin 2 → ℝ :=
  ![![0, 0], ![0, a], ![a - b, b], ![c, b], ![c, d - c], ![d, 0]]

public def boundaryAngleGauge (a b c d : ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  hexagonVertexInterpolation (boundaryAngleVertices a b c d)

public def boundaryAngleCharacter (i : Fin 6) (v : Fin 2 → ℝ) : ℝ :=
  ![v 0, v 0 + v 1, v 1, v 0, v 0 + v 1, v 1] i

public theorem continuous_boundaryAngleGauge (a b c d : ℝ) :
    Continuous (boundaryAngleGauge a b c d) :=
  continuous_hexagonVertexInterpolation _

public theorem boundaryAngleGauge_edge (a b c d : ℝ) (i : Fin 6)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    boundaryAngleCharacter i
      (boundaryAngleGauge a b c d
        ((1 - t) • planeVertexOffset i +
          t • planeNextVertexOffset i)) = ![0, a, b, c, d, 0] i := by
  unfold boundaryAngleGauge
  rw [hexagonVertexInterpolation_edge _ i t ht]
  fin_cases i <;>
    dsimp [boundaryAngleCharacter, boundaryAngleVertices,
      cellNextIndex] <;> ring

open SphereSixComplex.Geometry.CuspLocalPhaseAction

public def boundaryCompactGauge (u v : CompactTorus)
    (x : Fin 2 → ℝ) : Fin 2 → Circle :=
  fun j ↦ Circle.exp (boundaryAngleGauge
    (-Complex.arg (u 0 * u 1 * (u 2)⁻¹)) (-Complex.arg (u 1))
    (-Complex.arg (v 0)) (-Complex.arg (v 0 * v 1 * (v 2)⁻¹)) x j)

public def boundaryCompactCharacter (i : Fin 6) (k : Fin 2 → Circle) : Circle :=
  ![k 0, k 0 * k 1, k 1, k 0, k 0 * k 1, k 1] i

public theorem continuous_boundaryCompactGauge (u v : CompactTorus) :
    Continuous (boundaryCompactGauge u v) := by
  apply continuous_pi
  intro j
  exact Circle.exp.continuous.comp
    ((continuous_apply j).comp (continuous_boundaryAngleGauge _ _ _ _))

public theorem boundaryCompactGauge_edge (u v : CompactTorus) (i : Fin 6)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    boundaryCompactCharacter i
      (boundaryCompactGauge u v
        ((1 - t) • planeVertexOffset i +
          t • planeNextVertexOffset i)) =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] i := by
  have hu : Circle.exp (Complex.arg (u 0 * u 1 * (u 2)⁻¹)) = u 0 * u 1 * (u 2)⁻¹ :=
    Circle.exp_arg (u 0 * u 1 * (u 2)⁻¹)
  have hv : Circle.exp (Complex.arg (v 0 * v 1 * (v 2)⁻¹)) = v 0 * v 1 * (v 2)⁻¹ :=
    Circle.exp_arg (v 0 * v 1 * (v 2)⁻¹)
  simp only [Circle.coe_inv] at hu hv
  have h := congrArg Circle.exp (boundaryAngleGauge_edge
    (-Complex.arg (u 0 * u 1 * (u 2)⁻¹)) (-Complex.arg (u 1))
    (-Complex.arg (v 0)) (-Complex.arg (v 0 * v 1 * (v 2)⁻¹)) i t ht)
  fin_cases i <;>
    simpa [boundaryCompactCharacter, boundaryCompactGauge,
      boundaryAngleCharacter, Circle.exp_add, Circle.exp_neg,
      Circle.exp_arg, hu, hv] using h

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
