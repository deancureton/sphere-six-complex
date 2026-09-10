module

public import SphereSixComplex.Paper.Topology.ConstructedA2HexagonBoundaryPhaseGauge
@[expose] public section

noncomputable section
open Function Set Topology Matrix
open SphereSixComplex.Geometry.CuspLocalPhaseAction
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
public def constructedA2CellPreviousIndex : Fin 6 → Fin 6 := ![5, 0, 1, 2, 3, 4]

public theorem constructedA2CorrectedPlaneTile_zero_one (i : Fin 6)
    (p : ConstructedA2CellSquare) (hp : p.1 1 = 0) :
    constructedA2CorrectedPlaneTile 0 i p =
      (1 - p.1 0 / 2) • constructedA2PlaneVertexOffset i +
        (p.1 0 / 2) • constructedA2PlaneNextVertexOffset i := by
  have hle : p.1 1 ≤ p.1 0 := by rw [hp]; exact (p.2 0).1
  rw [constructedA2CorrectedPlaneTile, constructedA2PlaneTile_of_ge 0 i p hle]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [constructedA2CorrectedPlaneCenter, constructedA2PlaneVertexOffset,
      constructedA2PlaneNextVertexOffset, constructedA2PlaneNextMidpointOffset, hp] <;> ring

public theorem constructedA2CorrectedPlaneTile_zero_zero (i : Fin 6)
    (p : ConstructedA2CellSquare) (hp : p.1 0 = 0) :
    constructedA2CorrectedPlaneTile 0 i p =
      (p.1 1 / 2) • constructedA2PlaneVertexOffset (constructedA2CellPreviousIndex i) +
        (1 - p.1 1 / 2) •
          constructedA2PlaneNextVertexOffset (constructedA2CellPreviousIndex i) := by
  have hle : p.1 0 ≤ p.1 1 := by rw [hp]; exact (p.2 1).1
  rw [constructedA2CorrectedPlaneTile, constructedA2PlaneTile_of_le 0 i p hle]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [constructedA2CorrectedPlaneCenter, constructedA2PlaneVertexOffset,
      constructedA2PlaneNextVertexOffset, constructedA2PlaneMidpointOffset,
      constructedA2CellPreviousIndex, hp] <;> ring

public theorem constructedA2BoundaryCompactGauge_square_zero_one (u v : CompactTorus)
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 1 = 0) :
    constructedA2BoundaryCompactCharacter i
      (constructedA2BoundaryCompactGauge u v (constructedA2CorrectedPlaneTile 0 i p)) =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] i := by
  rw [constructedA2CorrectedPlaneTile_zero_one i p hp]
  apply constructedA2BoundaryCompactGauge_edge
  constructor <;> linarith [(p.2 0).1, (p.2 0).2]

public theorem constructedA2BoundaryCompactGauge_square_zero_zero (u v : CompactTorus)
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 0 = 0) :
    constructedA2BoundaryCompactCharacter (constructedA2CellPreviousIndex i)
      (constructedA2BoundaryCompactGauge u v (constructedA2CorrectedPlaneTile 0 i p)) =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] (constructedA2CellPreviousIndex i) := by
  rw [constructedA2CorrectedPlaneTile_zero_zero i p hp]
  have h := constructedA2BoundaryCompactGauge_edge u v (constructedA2CellPreviousIndex i)
    (1 - p.1 1 / 2) (by constructor <;> linarith [(p.2 1).1, (p.2 1).2])
  simpa only [show 1 - (1 - p.1 1 / 2) = p.1 1 / 2 by ring] using h

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedCompactPhaseMonomial_mul (A : Matrix (Fin 3) (Fin 3) ℤ)
    (u v : CompactTorus) :
    constructedCompactPhaseMonomial A (u * v) =
      constructedCompactPhaseMonomial A u * constructedCompactPhaseMonomial A v := by
  ext i
  simp only [constructedCompactPhaseMonomial, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

public def constructedA2BoundaryZeroOneTarget : Fin 6 → ChartIndex :=
  ![(false, 0), (true, 0), (false, 0), (true, -e₁), (false, 0), (true, -e₂)]

public def constructedA2BoundaryZeroOnePhase (u v : CompactTorus) : Fin 6 → CompactTorus :=
  ![1, u, u, v, v, 1]

public theorem constructedA2BoundaryZeroOnePhase_cancellation (u v : CompactTorus)
    (i : Fin 6) (k : Fin 2 → Circle)
    (hk : constructedA2BoundaryCompactCharacter i k =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] i) :
    constructedCompactPhaseMonomial (dualMatrix (constructedA2BoundaryZeroOneTarget i))
      (constructedA2BoundaryZeroOnePhase u v i * constructedA2EffectivePhaseSection k)
        (constructedA2CellRemoveIndex i 0) = 1 := by
  rw [constructedCompactPhaseMonomial_mul]
  fin_cases i
  all_goals
    dsimp [constructedA2BoundaryCompactCharacter] at hk
    simp [constructedCompactPhaseMonomial, constructedA2BoundaryZeroOneTarget,
      constructedA2BoundaryZeroOnePhase, constructedA2EffectivePhaseSection,
      constructedA2CellRemoveIndex, dualMatrix, a2DualCharacter, e₁, e₂,
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

public def constructedA2BoundaryZeroZeroTarget : Fin 6 → ChartIndex :=
  ![(false, 0), (true, -e₁), (false, 0), (true, -e₂), (false, 0), (true, 0)]

public def constructedA2BoundaryZeroZeroPhase (u v : CompactTorus) : Fin 6 → CompactTorus :=
  ![1, 1, u, u, v, v]

public theorem constructedA2BoundaryZeroZeroPhase_cancellation (u v : CompactTorus)
    (i : Fin 6) (k : Fin 2 → Circle)
    (hk : constructedA2BoundaryCompactCharacter (constructedA2CellPreviousIndex i) k =
      ![1, (u 0 * u 1 * (u 2)⁻¹)⁻¹, (u 1)⁻¹, (v 0)⁻¹,
        (v 0 * v 1 * (v 2)⁻¹)⁻¹, 1] (constructedA2CellPreviousIndex i)) :
    constructedCompactPhaseMonomial (dualMatrix (constructedA2BoundaryZeroZeroTarget i))
      (constructedA2BoundaryZeroZeroPhase u v i * constructedA2EffectivePhaseSection k)
        (constructedA2CellRemoveIndex i 1) = 1 := by
  rw [constructedCompactPhaseMonomial_mul]
  fin_cases i
  all_goals
    dsimp [constructedA2BoundaryCompactCharacter, constructedA2CellPreviousIndex] at hk
    simp [constructedCompactPhaseMonomial, constructedA2BoundaryZeroZeroTarget,
      constructedA2BoundaryZeroZeroPhase, constructedA2EffectivePhaseSection,
      constructedA2CellRemoveIndex, dualMatrix, a2DualCharacter, e₁, e₂,
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

open SphereSixComplex.Geometry.CuspPuncturedCollarBridge

public theorem constructedA2CompactPhase_singleAxis_eq_self
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
    have hc := congrFun (constructedCompactPhaseChartHomeomorph_coe a k) j
    change (constructedCompactPhaseMonomial (dualMatrix a) k j : ℂ) = _ at hc
    simp only [Pi.mul_apply, singleAxis, ite_true]
    rw [← hc, hk]
    simp
  · simp [singleAxis, hi]

public theorem constructedA2BoundaryGauge_zero_one_fixes_axis (u v : CompactTorus)
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 1 = 0) (z : ℂ) :
    constructedModel.torusAction
      (compactTorusEmbedding (constructedA2BoundaryZeroOnePhase u v i *
        constructedA2EffectivePhaseSection (constructedA2BoundaryCompactGauge u v
          (constructedA2CorrectedPlaneTile 0 i p))))
      (inclusion (constructedA2BoundaryZeroOneTarget i)
        (singleAxis (constructedA2CellRemoveIndex i 0) z)) =
      inclusion (constructedA2BoundaryZeroOneTarget i)
        (singleAxis (constructedA2CellRemoveIndex i 0) z) := by
  apply constructedA2CompactPhase_singleAxis_eq_self
  apply constructedA2BoundaryZeroOnePhase_cancellation
  exact constructedA2BoundaryCompactGauge_square_zero_one u v i p hp

public theorem constructedA2BoundaryGauge_zero_zero_fixes_axis (u v : CompactTorus)
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 0 = 0) (z : ℂ) :
    constructedModel.torusAction
      (compactTorusEmbedding (constructedA2BoundaryZeroZeroPhase u v i *
        constructedA2EffectivePhaseSection (constructedA2BoundaryCompactGauge u v
          (constructedA2CorrectedPlaneTile 0 i p))))
      (inclusion (constructedA2BoundaryZeroZeroTarget i)
        (singleAxis (constructedA2CellRemoveIndex i 1) z)) =
      inclusion (constructedA2BoundaryZeroZeroTarget i)
        (singleAxis (constructedA2CellRemoveIndex i 1) z) := by
  apply constructedA2CompactPhase_singleAxis_eq_self
  apply constructedA2BoundaryZeroZeroPhase_cancellation
  exact constructedA2BoundaryCompactGauge_square_zero_zero u v i p hp

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
