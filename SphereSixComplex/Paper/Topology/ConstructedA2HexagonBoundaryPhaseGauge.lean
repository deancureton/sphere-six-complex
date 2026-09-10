module

public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCompactPhaseCorrection

@[expose] public section

noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

public def constructedA2HexagonVertexWeights (x : Fin 2 → ℝ) : Fin 6 → ℝ :=
  let a := (3 / 2 : ℝ) * x 0
  let b := (3 / 2 : ℝ) * x 1
  ![max 0 (min a (a - b)), max 0 (min a b), max 0 (min b (b - a)),
    max 0 (min (-a) (b - a)), max 0 (min (-a) (-b)), max 0 (min (-b) (a - b))]

public theorem constructedA2HexagonVertexWeights_continuous :
    Continuous constructedA2HexagonVertexWeights := by
  unfold constructedA2HexagonVertexWeights
  fun_prop

private theorem hexagon_weights_edge_0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2HexagonVertexWeights
      ((1 - t) • constructedA2PlaneVertexOffset 0 +
        t • constructedA2PlaneNextVertexOffset 0) =
      fun j ↦ (if j = 0 then 1 - t else 0) +
        (if j = constructedA2CellNextIndex 0 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [constructedA2HexagonVertexWeights, constructedA2PlaneVertexOffset,
      constructedA2PlaneNextVertexOffset, constructedA2CellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2HexagonVertexWeights
      ((1 - t) • constructedA2PlaneVertexOffset 1 +
        t • constructedA2PlaneNextVertexOffset 1) =
      fun j ↦ (if j = 1 then 1 - t else 0) +
        (if j = constructedA2CellNextIndex 1 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [constructedA2HexagonVertexWeights, constructedA2PlaneVertexOffset,
      constructedA2PlaneNextVertexOffset, constructedA2CellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2HexagonVertexWeights
      ((1 - t) • constructedA2PlaneVertexOffset 2 +
        t • constructedA2PlaneNextVertexOffset 2) =
      fun j ↦ (if j = 2 then 1 - t else 0) +
        (if j = constructedA2CellNextIndex 2 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [constructedA2HexagonVertexWeights, constructedA2PlaneVertexOffset,
      constructedA2PlaneNextVertexOffset, constructedA2CellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_3 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2HexagonVertexWeights
      ((1 - t) • constructedA2PlaneVertexOffset 3 +
        t • constructedA2PlaneNextVertexOffset 3) =
      fun j ↦ (if j = 3 then 1 - t else 0) +
        (if j = constructedA2CellNextIndex 3 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [constructedA2HexagonVertexWeights, constructedA2PlaneVertexOffset,
      constructedA2PlaneNextVertexOffset, constructedA2CellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_4 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2HexagonVertexWeights
      ((1 - t) • constructedA2PlaneVertexOffset 4 +
        t • constructedA2PlaneNextVertexOffset 4) =
      fun j ↦ (if j = 4 then 1 - t else 0) +
        (if j = constructedA2CellNextIndex 4 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [constructedA2HexagonVertexWeights, constructedA2PlaneVertexOffset,
      constructedA2PlaneNextVertexOffset, constructedA2CellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

private theorem hexagon_weights_edge_5 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2HexagonVertexWeights
      ((1 - t) • constructedA2PlaneVertexOffset 5 +
        t • constructedA2PlaneNextVertexOffset 5) =
      fun j ↦ (if j = 5 then 1 - t else 0) +
        (if j = constructedA2CellNextIndex 5 then t else 0) := by
  ext j
  fin_cases j
  all_goals
    dsimp [constructedA2HexagonVertexWeights, constructedA2PlaneVertexOffset,
      constructedA2PlaneNextVertexOffset, constructedA2CellNextIndex,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, ite_true, ite_false]
    simp only [min_def, max_def]
    split_ifs <;> linarith [ht.1, ht.2]

public theorem constructedA2HexagonVertexWeights_edge (i : Fin 6) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2HexagonVertexWeights
      ((1 - t) • constructedA2PlaneVertexOffset i +
        t • constructedA2PlaneNextVertexOffset i) =
      fun j ↦ (if j = i then 1 - t else 0) +
        (if j = constructedA2CellNextIndex i then t else 0) := by
  fin_cases i
  · exact hexagon_weights_edge_0 t ht
  · exact hexagon_weights_edge_1 t ht
  · exact hexagon_weights_edge_2 t ht
  · exact hexagon_weights_edge_3 t ht
  · exact hexagon_weights_edge_4 t ht
  · exact hexagon_weights_edge_5 t ht

public def constructedA2HexagonVertexInterpolation (v : Fin 6 → Fin 2 → ℝ)
    (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ∑ i, constructedA2HexagonVertexWeights x i • v i

public theorem constructedA2HexagonVertexInterpolation_continuous (v : Fin 6 → Fin 2 → ℝ) :
    Continuous (constructedA2HexagonVertexInterpolation v) := by
  unfold constructedA2HexagonVertexInterpolation
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp constructedA2HexagonVertexWeights_continuous).smul
    continuous_const

public theorem constructedA2HexagonVertexInterpolation_edge
    (v : Fin 6 → Fin 2 → ℝ) (i : Fin 6) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2HexagonVertexInterpolation v
      ((1 - t) • constructedA2PlaneVertexOffset i +
        t • constructedA2PlaneNextVertexOffset i) =
      (1 - t) • v i + t • v (constructedA2CellNextIndex i) := by
  simp [constructedA2HexagonVertexInterpolation,
    constructedA2HexagonVertexWeights_edge i t ht, add_smul,
    Finset.sum_add_distrib, ite_smul]

public def constructedA2BoundaryAngleVertices (a b c d : ℝ) : Fin 6 → Fin 2 → ℝ :=
  ![![0, 0], ![0, a], ![a - b, b], ![c, b], ![c, d - c], ![d, 0]]

public def constructedA2BoundaryAngleGauge (a b c d : ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  constructedA2HexagonVertexInterpolation (constructedA2BoundaryAngleVertices a b c d)

public def constructedA2BoundaryAngleCharacter (i : Fin 6) (v : Fin 2 → ℝ) : ℝ :=
  ![v 0, v 0 + v 1, v 1, v 0, v 0 + v 1, v 1] i

public theorem constructedA2BoundaryAngleGauge_continuous (a b c d : ℝ) :
    Continuous (constructedA2BoundaryAngleGauge a b c d) :=
  constructedA2HexagonVertexInterpolation_continuous _

public theorem constructedA2BoundaryAngleGauge_edge (a b c d : ℝ) (i : Fin 6)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2BoundaryAngleCharacter i
      (constructedA2BoundaryAngleGauge a b c d
        ((1 - t) • constructedA2PlaneVertexOffset i +
          t • constructedA2PlaneNextVertexOffset i)) = ![0, a, b, c, d, 0] i := by
  unfold constructedA2BoundaryAngleGauge
  rw [constructedA2HexagonVertexInterpolation_edge _ i t ht]
  fin_cases i <;>
    dsimp [constructedA2BoundaryAngleCharacter, constructedA2BoundaryAngleVertices,
      constructedA2CellNextIndex] <;> ring

open SphereSixComplex.Geometry.CuspLocalPhaseAction

public def constructedA2BoundaryCompactGauge (u v : CompactTorus)
    (x : Fin 2 → ℝ) : Fin 2 → Circle :=
  fun j ↦ Circle.exp (constructedA2BoundaryAngleGauge
    (-Complex.arg (u 0 * u 1 * (u 2)⁻¹)) (-Complex.arg (u 1))
    (-Complex.arg (v 0)) (-Complex.arg (v 0 * v 1 * (v 2)⁻¹)) x j)

public def constructedA2BoundaryCompactCharacter (i : Fin 6) (k : Fin 2 → Circle) : Circle :=
  ![k 0, k 0 * k 1, k 1, k 0, k 0 * k 1, k 1] i

public theorem constructedA2BoundaryCompactGauge_continuous (u v : CompactTorus) :
    Continuous (constructedA2BoundaryCompactGauge u v) := by
  apply continuous_pi
  intro j
  exact Circle.exp.continuous.comp
    ((continuous_apply j).comp (constructedA2BoundaryAngleGauge_continuous _ _ _ _))

public theorem constructedA2BoundaryCompactGauge_edge (u v : CompactTorus) (i : Fin 6)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    constructedA2BoundaryCompactCharacter i
      (constructedA2BoundaryCompactGauge u v
        ((1 - t) • constructedA2PlaneVertexOffset i +
          t • constructedA2PlaneNextVertexOffset i)) =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] i := by
  have hu : Circle.exp (Complex.arg (u 0 * u 1 * (u 2)⁻¹)) = u 0 * u 1 * (u 2)⁻¹ :=
    Circle.exp_arg (u 0 * u 1 * (u 2)⁻¹)
  have hv : Circle.exp (Complex.arg (v 0 * v 1 * (v 2)⁻¹)) = v 0 * v 1 * (v 2)⁻¹ :=
    Circle.exp_arg (v 0 * v 1 * (v 2)⁻¹)
  simp only [Circle.coe_inv] at hu hv
  have h := congrArg Circle.exp (constructedA2BoundaryAngleGauge_edge
    (-Complex.arg (u 0 * u 1 * (u 2)⁻¹)) (-Complex.arg (u 1))
    (-Complex.arg (v 0)) (-Complex.arg (v 0 * v 1 * (v 2)⁻¹)) i t ht)
  fin_cases i <;>
    simpa [constructedA2BoundaryCompactCharacter, constructedA2BoundaryCompactGauge,
      constructedA2BoundaryAngleCharacter, Circle.exp_add, Circle.exp_neg,
      Circle.exp_arg, hu, hv] using h

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
