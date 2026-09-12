module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HexagonBoundaryPhaseGauge
@[expose] public section

noncomputable section
open Function Set Topology Matrix
open SphereSixComplex.Geometry.CuspLocalPhaseAction
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
namespace Construction

public def cellPreviousIndex : Fin 6 → Fin 6 := ![5, 0, 1, 2, 3, 4]

public theorem correctedPlaneTile_zero_one (i : Fin 6)
    (p : CellSquare) (hp : p.1 1 = 0) :
    correctedPlaneTile 0 i p =
      (1 - p.1 0 / 2) • planeVertexOffset i +
        (p.1 0 / 2) • planeNextVertexOffset i := by
  have hle : p.1 1 ≤ p.1 0 := by rw [hp]; exact (p.2 0).1
  rw [correctedPlaneTile, planeTile_of_ge 0 i p hle]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [correctedPlaneCenter, planeVertexOffset,
      planeNextVertexOffset, planeNextMidpointOffset, hp] <;> ring

public theorem correctedPlaneTile_zero_zero (i : Fin 6)
    (p : CellSquare) (hp : p.1 0 = 0) :
    correctedPlaneTile 0 i p =
      (p.1 1 / 2) • planeVertexOffset (cellPreviousIndex i) +
        (1 - p.1 1 / 2) •
          planeNextVertexOffset (cellPreviousIndex i) := by
  have hle : p.1 0 ≤ p.1 1 := by rw [hp]; exact (p.2 1).1
  rw [correctedPlaneTile, planeTile_of_le 0 i p hle]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [correctedPlaneCenter, planeVertexOffset,
      planeNextVertexOffset, planeMidpointOffset,
      cellPreviousIndex, hp] <;> ring

public theorem boundaryCompactGauge_square_zero_one (u v : CompactTorus)
    (i : Fin 6) (p : CellSquare) (hp : p.1 1 = 0) :
    boundaryCompactCharacter i
      (boundaryCompactGauge u v (correctedPlaneTile 0 i p)) =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] i := by
  rw [correctedPlaneTile_zero_one i p hp]
  apply boundaryCompactGauge_edge
  constructor <;> linarith [(p.2 0).1, (p.2 0).2]

public theorem boundaryCompactGauge_square_zero_zero (u v : CompactTorus)
    (i : Fin 6) (p : CellSquare) (hp : p.1 0 = 0) :
    boundaryCompactCharacter (cellPreviousIndex i)
      (boundaryCompactGauge u v (correctedPlaneTile 0 i p)) =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] (cellPreviousIndex i) := by
  rw [correctedPlaneTile_zero_zero i p hp]
  have h := boundaryCompactGauge_edge u v (cellPreviousIndex i)
    (1 - p.1 1 / 2) (by constructor <;> linarith [(p.2 1).1, (p.2 1).2])
  simpa only [show 1 - (1 - p.1 1 / 2) = p.1 1 / 2 by ring] using h

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end Construction

open SphereSixComplex.Geometry.CuspCombinatorics

public theorem constructedCompactPhaseMonomial_mul (A : Matrix (Fin 3) (Fin 3) ℤ)
    (u v : CompactTorus) :
    constructedCompactPhaseMonomial A (u * v) =
      constructedCompactPhaseMonomial A u * constructedCompactPhaseMonomial A v := by
  ext i
  simp only [constructedCompactPhaseMonomial, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

namespace Construction

public def boundaryZeroOneTarget : Fin 6 → ChartIndex :=
  ![(false, 0), (true, 0), (false, 0), (true, -e₁), (false, 0), (true, -e₂)]

public def boundaryZeroOnePhase (u v : CompactTorus) : Fin 6 → CompactTorus :=
  ![1, u, u, v, v, 1]

public theorem boundaryZeroOnePhase_cancellation (u v : CompactTorus)
    (i : Fin 6) (k : Fin 2 → Circle)
    (hk : boundaryCompactCharacter i k =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] i) :
    constructedCompactPhaseMonomial (dualMatrix (boundaryZeroOneTarget i))
      (boundaryZeroOnePhase u v i * effectivePhaseSection k)
        (cellRemoveIndex i 0) = 1 := by
  rw [constructedCompactPhaseMonomial_mul]
  fin_cases i
  all_goals
    dsimp [boundaryCompactCharacter] at hk
    simp [constructedCompactPhaseMonomial, boundaryZeroOneTarget,
      boundaryZeroOnePhase, effectivePhaseSection,
      cellRemoveIndex, dualMatrix, a2DualCharacter, e₁, e₂,
      Fin.prod_univ_succ, hk, mul_assoc, mul_comm, mul_left_comm]
  · calc
      _ = (u 0 * (u 0)⁻¹) * (u 1 * (u 1)⁻¹) * ((u 2)⁻¹ * u 2) := by
        apply Circle.ext
        simp only [Circle.coe_mul, Circle.coe_inv]
        ring
      _ = 1 := by simp
  · calc
      _ = ((v 0 * v 1 * (v 2)⁻¹) * (k 0 * k 1))⁻¹ := by
        apply Circle.ext
        simp only [Circle.coe_mul, Circle.coe_inv, _root_.mul_inv_rev, inv_inv]
        ring
      _ = 1 := by rw [hk]; simp

public def boundaryZeroZeroTarget : Fin 6 → ChartIndex :=
  ![(false, 0), (true, -e₁), (false, 0), (true, -e₂), (false, 0), (true, 0)]

public def boundaryZeroZeroPhase (u v : CompactTorus) : Fin 6 → CompactTorus :=
  ![1, 1, u, u, v, v]

public theorem boundaryZeroZeroPhase_cancellation (u v : CompactTorus)
    (i : Fin 6) (k : Fin 2 → Circle)
    (hk : boundaryCompactCharacter (cellPreviousIndex i) k =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] (cellPreviousIndex i)) :
    constructedCompactPhaseMonomial (dualMatrix (boundaryZeroZeroTarget i))
      (boundaryZeroZeroPhase u v i * effectivePhaseSection k)
        (cellRemoveIndex i 1) = 1 := by
  rw [constructedCompactPhaseMonomial_mul]
  fin_cases i
  all_goals
    dsimp [boundaryCompactCharacter, cellPreviousIndex] at hk
    simp [constructedCompactPhaseMonomial, boundaryZeroZeroTarget,
      boundaryZeroZeroPhase, effectivePhaseSection,
      cellRemoveIndex, dualMatrix, a2DualCharacter, e₁, e₂,
      Fin.prod_univ_succ, hk, mul_assoc, mul_comm, mul_left_comm]
  · calc
      _ = ((u 0 * u 1 * (u 2)⁻¹) * (k 0 * k 1))⁻¹ := by
        apply Circle.ext
        simp only [Circle.coe_mul, Circle.coe_inv, _root_.mul_inv_rev, inv_inv]
        ring
      _ = 1 := by rw [hk]; simp
  · calc
      _ = (v 0 * (v 0)⁻¹) * (v 1 * (v 1)⁻¹) * ((v 2)⁻¹ * v 2) := by
        apply Circle.ext
        simp only [Circle.coe_mul, Circle.coe_inv]
        ring
      _ = 1 := by simp

open SphereSixComplex.Geometry.CuspCollar

public theorem compactPhase_singleAxis_eq_self
    (a : ChartIndex) (j : Fin 3) (z : ℂ) (k : CompactTorus)
    (hk : constructedCompactPhaseMonomial (dualMatrix a) k j = 1) :
    constructedModel.torusAction (compactTorusEmbedding k) (inclusion a (singleAxis j z)) =
      inclusion a (singleAxis j z) := by
  change carrierTorusActionFun _ _ = _
  rw [carrierTorusActionFun_inclusion]
  congr 1
  funext i
  by_cases hi : i = j
  · subst i
    have hc := congrFun (compactPhaseChartHomeomorph_coe a k) j
    change (constructedCompactPhaseMonomial (dualMatrix a) k j : ℂ) = _ at hc
    simp only [Pi.mul_apply, singleAxis, ite_true]
    rw [← hc, hk]
    simp
  · simp [singleAxis, hi]

public theorem boundaryGauge_zero_one_fixes_axis (u v : CompactTorus)
    (i : Fin 6) (p : CellSquare) (hp : p.1 1 = 0) (z : ℂ) :
    constructedModel.torusAction
      (compactTorusEmbedding (boundaryZeroOnePhase u v i *
        effectivePhaseSection (boundaryCompactGauge u v
          (correctedPlaneTile 0 i p))))
      (inclusion (boundaryZeroOneTarget i)
        (singleAxis (cellRemoveIndex i 0) z)) =
      inclusion (boundaryZeroOneTarget i)
        (singleAxis (cellRemoveIndex i 0) z) := by
  apply compactPhase_singleAxis_eq_self
  apply boundaryZeroOnePhase_cancellation
  exact boundaryCompactGauge_square_zero_one u v i p hp

public theorem boundaryGauge_zero_zero_fixes_axis (u v : CompactTorus)
    (i : Fin 6) (p : CellSquare) (hp : p.1 0 = 0) (z : ℂ) :
    constructedModel.torusAction
      (compactTorusEmbedding (boundaryZeroZeroPhase u v i *
        effectivePhaseSection (boundaryCompactGauge u v
          (correctedPlaneTile 0 i p))))
      (inclusion (boundaryZeroZeroTarget i)
        (singleAxis (cellRemoveIndex i 1) z)) =
      inclusion (boundaryZeroZeroTarget i)
        (singleAxis (cellRemoveIndex i 1) z) := by
  apply compactPhase_singleAxis_eq_self
  apply boundaryZeroZeroPhase_cancellation
  exact boundaryCompactGauge_square_zero_zero u v i p hp

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
