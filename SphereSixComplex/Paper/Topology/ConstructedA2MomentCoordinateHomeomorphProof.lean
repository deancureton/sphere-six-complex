/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositivePartContractibilityProof
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Moment coordinates for the constructed A₂ positive carrier

On the noncentral positive stratum the logarithmic position and the height have an explicit
inverse, obtained by taking positive real powers. Thus the global moment-coordinate problem is
the continuous proper extension of these coordinates across the central honeycomb.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Geometry.InfiniteA2Toric.QuantitativeRegions

public noncomputable def constructedA2PositiveRealUnit (x : ℝ) (hx : 0 < x) : ℂˣ :=
  Units.mk0 (x : ℂ) (by exact_mod_cast hx.ne')

/-- The positive dense-torus point with logarithmic position `(x₀,x₁)` and height `x₂`. -/
public noncomputable def constructedA2MomentTorusPoint
    (x : Fin 3 → ℝ) (hx : 0 < x 2) : DenseTorus :=
  ![constructedA2PositiveRealUnit (x 2 ^ x 0) (Real.rpow_pos_of_pos hx _),
    constructedA2PositiveRealUnit (x 2 ^ x 1) (Real.rpow_pos_of_pos hx _),
    constructedA2PositiveRealUnit (x 2) hx]

private theorem constructedA2MomentTorusPoint_positive
    (x : Fin 3 → ℝ) (hx : 0 < x 2) :
    ∀ i, 0 < ((constructedA2MomentTorusPoint x hx i : ℂˣ) : ℂ).re ∧
      ((constructedA2MomentTorusPoint x hx i : ℂˣ) : ℂ).im = 0 := by
  intro i
  fin_cases i
  · simp [constructedA2MomentTorusPoint, constructedA2PositiveRealUnit,
      Real.rpow_pos_of_pos hx]
  · simp [constructedA2MomentTorusPoint, constructedA2PositiveRealUnit,
      Real.rpow_pos_of_pos hx]
  · simpa [constructedA2MomentTorusPoint, constructedA2PositiveRealUnit] using hx

private theorem constructedA2MomentTorusPoint_modulus
    (x : Fin 3 → ℝ) (hx : 0 < x 2) :
    denseTorusModulus (constructedA2MomentTorusPoint x hx) =
      constructedA2MomentTorusPoint x hx :=
  denseTorusModulus_eq_self_of_positive _
    (constructedA2MomentTorusPoint_positive x hx)

private theorem carrierModulus_carrierTorusEmbedding (g : DenseTorus) :
    carrierModulus (carrierTorusEmbedding g) =
      carrierTorusEmbedding (denseTorusModulus g) := by
  rw [carrierTorusEmbedding_eq_inclusion_torusChartCoordinates baseChart,
    carrierTorusEmbedding_eq_inclusion_torusChartCoordinates baseChart,
    carrierModulus_inclusion, ← torusChartCoordinates_denseTorusModulus]

private theorem torusCoordinates_positive {r : ℝ}
    (q : constructedLocalPositivePart r)
    (ht : constructedModel.t (q : localCarrier constructedModel r) ≠ 0) :
    denseTorusModulus
      (torusCoordinates constructedModel (q : localCarrier constructedModel r)) =
      torusCoordinates constructedModel (q : localCarrier constructedModel r) := by
  let g := torusCoordinates constructedModel (q : localCarrier constructedModel r)
  have he : carrierTorusEmbedding g = (q.1.1 : Carrier) :=
    torusEmbedding_torusCoordinates constructedModel ht
  apply constructedModel.torus_openEmbedding.injective
  change carrierTorusEmbedding (denseTorusModulus g) = carrierTorusEmbedding g
  rw [← carrierModulus_carrierTorusEmbedding, he]
  rw [(mem_constructedLocalPositivePart_iff r q).mp q.property]

/-- The explicit inverse to logarithmic moment coordinates at positive height. -/
public noncomputable def constructedA2OffCentralMomentInverse {r : ℝ}
    (x : constructedPositiveMomentRegion r) (hx : 0 < x.1 2) :
    constructedLocalPositivePart r := by
  let g := constructedA2MomentTorusPoint x.1 hx
  let p : localCarrier constructedModel r := ⟨carrierTorusEmbedding g, by
    change carrierHeight (carrierTorusEmbedding g) ∈ Metric.ball 0 r
    rw [carrierHeight_torus]
    simpa [g, constructedA2MomentTorusPoint, constructedA2PositiveRealUnit, Metric.mem_ball,
      dist_zero_right, abs_of_pos hx] using x.2.2⟩
  exact ⟨p, (mem_constructedLocalPositivePart_iff r p).mpr (by
    change carrierModulus (carrierTorusEmbedding g) = carrierTorusEmbedding g
    rw [carrierModulus_carrierTorusEmbedding, constructedA2MomentTorusPoint_modulus])⟩

public theorem constructedA2OffCentralMomentInverse_coe {r : ℝ}
    (x : constructedPositiveMomentRegion r) (hx : 0 < x.1 2) :
    ((constructedA2OffCentralMomentInverse x hx).1.1 : Carrier) =
      carrierTorusEmbedding (constructedA2MomentTorusPoint x.1 hx) := by
  rfl

public theorem constructedA2OffCentralMomentInverse_t {r : ℝ}
    (x : constructedPositiveMomentRegion r) (hx : 0 < x.1 2) :
    constructedModel.t
      (constructedA2OffCentralMomentInverse x hx : localCarrier constructedModel r) =
      (x.1 2 : ℂ) := by
  change carrierHeight ((constructedA2OffCentralMomentInverse x hx).1.1 : Carrier) = _
  rw [constructedA2OffCentralMomentInverse_coe, carrierHeight_torus]
  rfl

/-- Logarithmic position together with the nonnegative real height. -/
public noncomputable def constructedA2OffCentralMomentCoordinate {r : ℝ}
    (q : constructedLocalPositivePart r) : Fin 3 → ℝ :=
  ![rescaledPosition constructedModel (q : localCarrier constructedModel r) 0,
    rescaledPosition constructedModel (q : localCarrier constructedModel r) 1,
    ‖constructedModel.t (q : localCarrier constructedModel r)‖]

/-- The logarithmic coordinate always lies in the height strip defining the moment region. -/
public noncomputable def constructedA2OffCentralMomentCoordinateTarget {r : ℝ}
    (q : constructedLocalPositivePart r) : constructedPositiveMomentRegion r :=
  ⟨constructedA2OffCentralMomentCoordinate q, norm_nonneg _,
    mem_ball_zero_iff.mp q.1.property⟩

/-- Positive real powers are a right inverse to the logarithmic coordinates. -/
public theorem constructedA2OffCentralMomentCoordinate_inverse
    {r : ℝ} (hr : r < 1) (x : constructedPositiveMomentRegion r) (hx : 0 < x.1 2) :
    constructedA2OffCentralMomentCoordinate
      (constructedA2OffCentralMomentInverse x hx) = x.1 := by
  have hx1 : x.1 2 < 1 := x.2.2.trans hr
  have hlog : Real.log (x.1 2) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hx (ne_of_lt hx1)
  have ht : constructedModel.t
      (constructedA2OffCentralMomentInverse x hx : localCarrier constructedModel r) ≠ 0 := by
    rw [constructedA2OffCentralMomentInverse_t]
    exact_mod_cast hx.ne'
  have htorus :
      torusCoordinates constructedModel
        (constructedA2OffCentralMomentInverse x hx : localCarrier constructedModel r) =
          constructedA2MomentTorusPoint x.1 hx := by
    exact torusCoordinates_unique constructedModel ht
      (constructedA2OffCentralMomentInverse_coe x hx).symm
  funext i
  fin_cases i
  · simp only [constructedA2OffCentralMomentCoordinate, rescaledPosition]
    rw [htorus, constructedA2OffCentralMomentInverse_t]
    simp [constructedA2MomentTorusPoint, constructedA2PositiveRealUnit, Real.log_rpow hx, hlog,
      Real.norm_of_nonneg hx.le]
  · simp only [constructedA2OffCentralMomentCoordinate, rescaledPosition]
    rw [htorus, constructedA2OffCentralMomentInverse_t]
    simp [constructedA2MomentTorusPoint, constructedA2PositiveRealUnit, Real.log_rpow hx, hlog,
      Real.norm_of_nonneg hx.le]
  · simp only [constructedA2OffCentralMomentCoordinate]
    rw [constructedA2OffCentralMomentInverse_t]
    simp [Real.norm_of_nonneg hx.le]

/-- Logarithmic coordinates recover every positive point away from the central fibre. -/
public theorem constructedA2OffCentralMomentInverse_coordinate
    {r : ℝ} (hr : r < 1) (q : constructedLocalPositivePart r)
    (ht : constructedModel.t (q : localCarrier constructedModel r) ≠ 0) :
    constructedA2OffCentralMomentInverse
      (constructedA2OffCentralMomentCoordinateTarget q)
      (show 0 < (constructedA2OffCentralMomentCoordinateTarget q).1 2 by
        change 0 < ‖constructedModel.t (q : localCarrier constructedModel r)‖
        exact norm_pos_iff.mpr ht) = q := by
  let g := torusCoordinates constructedModel (q : localCarrier constructedModel r)
  have he : carrierTorusEmbedding g = (q.1.1 : Carrier) :=
    torusEmbedding_torusCoordinates constructedModel ht
  have hmod : denseTorusModulus g = g := torusCoordinates_positive q ht
  have hgi (i : Fin 3) : (‖(g i : ℂ)‖ : ℂ) = (g i : ℂ) := by
    exact congrArg (fun u : ℂˣ ↦ (u : ℂ)) (congrFun hmod i)
  have htgi : (g 2 : ℂ) = constructedModel.t (q : localCarrier constructedModel r) :=
    torusCoordinates_last constructedModel ht
  have hbase : 0 < ‖constructedModel.t (q : localCarrier constructedModel r)‖ :=
    norm_pos_iff.mpr ht
  have hlocal : ‖constructedModel.t (q : localCarrier constructedModel r)‖ < r :=
    mem_ball_zero_iff.mp q.1.property
  have hbase1 : ‖constructedModel.t (q : localCarrier constructedModel r)‖ < 1 :=
    hlocal.trans hr
  have hlog : Real.log ‖constructedModel.t (q : localCarrier constructedModel r)‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hbase (ne_of_lt hbase1)
  let hx : 0 < (constructedA2OffCentralMomentCoordinateTarget q).1 2 := by
    change 0 < ‖constructedModel.t (q : localCarrier constructedModel r)‖
    exact hbase
  apply Subtype.ext
  apply Subtype.ext
  change ((constructedA2OffCentralMomentInverse
      (constructedA2OffCentralMomentCoordinateTarget q) hx).1.1 : Carrier) = (q.1.1 : Carrier)
  rw [constructedA2OffCentralMomentInverse_coe, ← he]
  refine congrArg carrierTorusEmbedding ?_
  change constructedA2MomentTorusPoint (constructedA2OffCentralMomentCoordinate q) hx = g
  funext i
  fin_cases i
  · apply Units.ext
    change ((show ℝ from ‖constructedModel.t (q : localCarrier constructedModel r)‖ ^
      (Real.log ‖(g 0 : ℂ)‖ /
        Real.log ‖constructedModel.t (q : localCarrier constructedModel r)‖)) : ℂ) =
      (g 0 : ℂ)
    rw [Real.rpow_def_of_pos hbase]
    rw [show Real.log ‖constructedModel.t (q : localCarrier constructedModel r)‖ *
        (Real.log ‖(g 0 : ℂ)‖ /
          Real.log ‖constructedModel.t (q : localCarrier constructedModel r)‖) =
        Real.log ‖(g 0 : ℂ)‖ by field_simp]
    rw [Real.exp_log (Units.norm_pos (g 0))]
    exact hgi 0
  · apply Units.ext
    change ((show ℝ from ‖constructedModel.t (q : localCarrier constructedModel r)‖ ^
      (Real.log ‖(g 1 : ℂ)‖ /
        Real.log ‖constructedModel.t (q : localCarrier constructedModel r)‖)) : ℂ) =
      (g 1 : ℂ)
    rw [Real.rpow_def_of_pos hbase]
    rw [show Real.log ‖constructedModel.t (q : localCarrier constructedModel r)‖ *
        (Real.log ‖(g 1 : ℂ)‖ /
          Real.log ‖constructedModel.t (q : localCarrier constructedModel r)‖) =
        Real.log ‖(g 1 : ℂ)‖ by field_simp]
    rw [Real.exp_log (Units.norm_pos (g 1))]
    exact hgi 1
  · apply Units.ext
    simp only [constructedA2MomentTorusPoint, Matrix.cons_val_two,
      constructedA2OffCentralMomentCoordinate]
    change (‖constructedModel.t (q : localCarrier constructedModel r)‖ : ℂ) = (g 2 : ℂ)
    rw [← htgi, hgi 2]



end SphereSixComplex.Geometry.InfiniteA2Toric

end
