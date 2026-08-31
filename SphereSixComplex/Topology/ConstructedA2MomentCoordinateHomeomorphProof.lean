/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Topology.ConstructedA2PositivePartContractibilityProof
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

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions

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
    (ht : constructedModel.t (q : LocalCarrier constructedModel r) ≠ 0) :
    denseTorusModulus
      (torusCoordinates constructedModel (q : LocalCarrier constructedModel r)) =
      torusCoordinates constructedModel (q : LocalCarrier constructedModel r) := by
  let g := torusCoordinates constructedModel (q : LocalCarrier constructedModel r)
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
  let p : LocalCarrier constructedModel r := ⟨carrierTorusEmbedding g, by
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
      (constructedA2OffCentralMomentInverse x hx : LocalCarrier constructedModel r) =
      (x.1 2 : ℂ) := by
  change carrierHeight ((constructedA2OffCentralMomentInverse x hx).1.1 : Carrier) = _
  rw [constructedA2OffCentralMomentInverse_coe, carrierHeight_torus]
  rfl

/-- Logarithmic position together with the nonnegative real height. -/
public noncomputable def constructedA2OffCentralMomentCoordinate {r : ℝ}
    (q : constructedLocalPositivePart r) : Fin 3 → ℝ :=
  ![rescaledPosition constructedModel (q : LocalCarrier constructedModel r) 0,
    rescaledPosition constructedModel (q : LocalCarrier constructedModel r) 1,
    ‖constructedModel.t (q : LocalCarrier constructedModel r)‖]

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
      (constructedA2OffCentralMomentInverse x hx : LocalCarrier constructedModel r) ≠ 0 := by
    rw [constructedA2OffCentralMomentInverse_t]
    exact_mod_cast hx.ne'
  have htorus :
      torusCoordinates constructedModel
        (constructedA2OffCentralMomentInverse x hx : LocalCarrier constructedModel r) =
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
    (ht : constructedModel.t (q : LocalCarrier constructedModel r) ≠ 0) :
    constructedA2OffCentralMomentInverse
      (constructedA2OffCentralMomentCoordinateTarget q)
      (show 0 < (constructedA2OffCentralMomentCoordinateTarget q).1 2 by
        change 0 < ‖constructedModel.t (q : LocalCarrier constructedModel r)‖
        exact norm_pos_iff.mpr ht) = q := by
  let g := torusCoordinates constructedModel (q : LocalCarrier constructedModel r)
  have he : carrierTorusEmbedding g = (q.1.1 : Carrier) :=
    torusEmbedding_torusCoordinates constructedModel ht
  have hmod : denseTorusModulus g = g := torusCoordinates_positive q ht
  have hgi (i : Fin 3) : (‖(g i : ℂ)‖ : ℂ) = (g i : ℂ) := by
    exact congrArg (fun u : ℂˣ ↦ (u : ℂ)) (congrFun hmod i)
  have htgi : (g 2 : ℂ) = constructedModel.t (q : LocalCarrier constructedModel r) :=
    torusCoordinates_last constructedModel ht
  have hbase : 0 < ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ :=
    norm_pos_iff.mpr ht
  have hlocal : ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ < r :=
    mem_ball_zero_iff.mp q.1.property
  have hbase1 : ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ < 1 :=
    hlocal.trans hr
  have hlog : Real.log ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hbase (ne_of_lt hbase1)
  let hx : 0 < (constructedA2OffCentralMomentCoordinateTarget q).1 2 := by
    change 0 < ‖constructedModel.t (q : LocalCarrier constructedModel r)‖
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
    change ((show ℝ from ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ ^
      (Real.log ‖(g 0 : ℂ)‖ /
        Real.log ‖constructedModel.t (q : LocalCarrier constructedModel r)‖)) : ℂ) =
      (g 0 : ℂ)
    rw [Real.rpow_def_of_pos hbase]
    rw [show Real.log ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ *
        (Real.log ‖(g 0 : ℂ)‖ /
          Real.log ‖constructedModel.t (q : LocalCarrier constructedModel r)‖) =
        Real.log ‖(g 0 : ℂ)‖ by field_simp]
    rw [Real.exp_log (Units.norm_pos (g 0))]
    exact hgi 0
  · apply Units.ext
    change ((show ℝ from ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ ^
      (Real.log ‖(g 1 : ℂ)‖ /
        Real.log ‖constructedModel.t (q : LocalCarrier constructedModel r)‖)) : ℂ) =
      (g 1 : ℂ)
    rw [Real.rpow_def_of_pos hbase]
    rw [show Real.log ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ *
        (Real.log ‖(g 1 : ℂ)‖ /
          Real.log ‖constructedModel.t (q : LocalCarrier constructedModel r)‖) =
        Real.log ‖(g 1 : ℂ)‖ by field_simp]
    rw [Real.exp_log (Units.norm_pos (g 1))]
    exact hgi 1
  · apply Units.ext
    simp only [constructedA2MomentTorusPoint, Matrix.cons_val_two,
      constructedA2OffCentralMomentCoordinate]
    change (‖constructedModel.t (q : LocalCarrier constructedModel r)‖ : ℂ) = (g 2 : ℂ)
    rw [← htgi, hgi 2]

private theorem constructedA2PositiveHeight_eq_norm {r : ℝ}
    (q : constructedLocalPositivePart r) :
    constructedModel.t (q : LocalCarrier constructedModel r) =
      (‖constructedModel.t (q : LocalCarrier constructedModel r)‖ : ℂ) := by
  have h := constructedLocalModulusRetraction_t r
    (q : LocalCarrier constructedModel r)
  rw [constructedLocalModulusRetraction_fixed r q] at h
  exact h

/-- A global extension certificate for the canonical logarithmic moment coordinate. It is pinned
on the dense stratum, on the central honeycomb, and in the height direction. -/
public structure ConstructedA2ProperMomentCoordinate
    (r : ℝ) (H : ConstructedHoneycombCellData r) where
  coordinate : constructedLocalPositivePart r → constructedPositiveMomentRegion r
  coordinate_height : ∀ q : constructedLocalPositivePart r,
    (coordinate q).1 2 = ‖constructedModel.t (q : LocalCarrier constructedModel r)‖
  coordinate_offCentral : ∀ q : constructedLocalPositivePart r,
    constructedModel.t (q : LocalCarrier constructedModel r) ≠ 0 →
      coordinate q = constructedA2OffCentralMomentCoordinateTarget q
  coordinate_central : ∀ (q : constructedLocalPositivePart r)
      (hq : constructedModel.t (q : LocalCarrier constructedModel r) = 0),
    (fun i : Fin 2 ↦ (coordinate q).1 i.castSucc) =
      H.honeycomb.symm ⟨q, hq⟩
  proper_coordinate : IsProperMap coordinate

namespace ConstructedA2ProperMomentCoordinate

/-- The pinned moment coordinate is injective; no bijectivity assumption is needed. -/
public theorem injective {r : ℝ} {H : ConstructedHoneycombCellData r}
    (hr : r < 1) (C : ConstructedA2ProperMomentCoordinate r H) :
    Injective C.coordinate := by
  intro q q' hqq'
  have hnorm :
      ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ =
        ‖constructedModel.t (q' : LocalCarrier constructedModel r)‖ := by
    rw [← C.coordinate_height q, ← C.coordinate_height q']
    exact congrArg (fun x : constructedPositiveMomentRegion r ↦ x.1 2) hqq'
  have ht : constructedModel.t (q : LocalCarrier constructedModel r) =
      constructedModel.t (q' : LocalCarrier constructedModel r) := by
    rw [constructedA2PositiveHeight_eq_norm q, constructedA2PositiveHeight_eq_norm q', hnorm]
  by_cases hq : constructedModel.t (q : LocalCarrier constructedModel r) = 0
  · have hq' : constructedModel.t (q' : LocalCarrier constructedModel r) = 0 := ht ▸ hq
    have hc := congrArg
      (fun x : constructedPositiveMomentRegion r ↦ fun i : Fin 2 ↦ x.1 i.castSucc) hqq'
    rw [C.coordinate_central q hq, C.coordinate_central q' hq'] at hc
    have hz : (⟨q, hq⟩ : constructedPositiveCentralFiber r) = ⟨q', hq'⟩ :=
      H.honeycomb.symm.injective hc
    exact congrArg Subtype.val hz
  · have hq' : constructedModel.t (q' : LocalCarrier constructedModel r) ≠ 0 := by
      rwa [← ht]
    rw [← constructedA2OffCentralMomentInverse_coordinate hr q hq,
      ← constructedA2OffCentralMomentInverse_coordinate hr q' hq']
    congr 1
    rw [← C.coordinate_offCentral q hq, ← C.coordinate_offCentral q' hq']
    exact hqq'

/-- The pinned moment coordinate is surjective; its inverse is explicit off the central fibre
and is the chosen honeycomb homeomorphism on the central fibre. -/
public theorem surjective {r : ℝ} {H : ConstructedHoneycombCellData r}
    (hr : r < 1) (C : ConstructedA2ProperMomentCoordinate r H) :
    Surjective C.coordinate := by
  intro x
  by_cases hx0 : x.1 2 = 0
  · let y : Fin 2 → ℝ := fun i ↦ x.1 i.castSucc
    let z : constructedPositiveCentralFiber r := H.honeycomb y
    let q : constructedLocalPositivePart r := z.1
    have hc : (fun i : Fin 2 ↦ (C.coordinate q).1 i.castSucc) = y := by
      rw [C.coordinate_central q z.property]
      exact H.honeycomb.symm_apply_apply y
    refine ⟨q, ?_⟩
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrFun hc 0
    · exact congrFun hc 1
    · change (C.coordinate q).1 2 = x.1 2
      rw [C.coordinate_height q, z.property, norm_zero, hx0]
  · have hx : 0 < x.1 2 := lt_of_le_of_ne x.2.1 (Ne.symm hx0)
    let q := constructedA2OffCentralMomentInverse x hx
    have hqt : constructedModel.t (q : LocalCarrier constructedModel r) ≠ 0 := by
      rw [constructedA2OffCentralMomentInverse_t]
      exact_mod_cast hx.ne'
    refine ⟨q, ?_⟩
    rw [C.coordinate_offCentral q hqt]
    apply Subtype.ext
    exact constructedA2OffCentralMomentCoordinate_inverse hr x hx

/-- A proper extension pinned to the dense and central coordinates is a homeomorphism. -/
public noncomputable def toHomeomorph {r : ℝ} {H : ConstructedHoneycombCellData r}
    (hr : r < 1) (C : ConstructedA2ProperMomentCoordinate r H) :
    constructedLocalPositivePart r ≃ₜ constructedPositiveMomentRegion r :=
  IsHomeomorph.homeomorph C.coordinate
    ((isHomeomorph_iff_continuous_isClosedMap_bijective).2
      ⟨C.proper_coordinate.continuous, C.proper_coordinate.isClosedMap,
        C.injective hr, C.surjective hr⟩)

@[simp]
public theorem toHomeomorph_apply {r : ℝ} {H : ConstructedHoneycombCellData r}
    (hr : r < 1) (C : ConstructedA2ProperMomentCoordinate r H)
    (q : constructedLocalPositivePart r) :
    C.toHomeomorph hr q = C.coordinate q :=
  rfl

/-- The resulting homeomorphism remembers the geometric height coordinate. -/
public theorem toHomeomorph_height {r : ℝ} {H : ConstructedHoneycombCellData r}
    (hr : r < 1) (C : ConstructedA2ProperMomentCoordinate r H)
    (q : constructedLocalPositivePart r) :
    (C.toHomeomorph hr q).1 2 =
      ‖constructedModel.t (q : LocalCarrier constructedModel r)‖ := by
  rw [toHomeomorph_apply]
  exact C.coordinate_height q

/-- Away from the central fibre, the resulting homeomorphism is exactly the logarithmic
position-height coordinate, not merely an unspecified homeomorphism. -/
public theorem toHomeomorph_offCentral {r : ℝ} {H : ConstructedHoneycombCellData r}
    (hr : r < 1) (C : ConstructedA2ProperMomentCoordinate r H)
    (q : constructedLocalPositivePart r)
    (hq : constructedModel.t (q : LocalCarrier constructedModel r) ≠ 0) :
    C.toHomeomorph hr q = constructedA2OffCentralMomentCoordinateTarget q := by
  rw [toHomeomorph_apply]
  exact C.coordinate_offCentral q hq

/-- On the central fibre, the resulting homeomorphism is exactly the inverse of the selected
constructed honeycomb chart. -/
public theorem toHomeomorph_central {r : ℝ} {H : ConstructedHoneycombCellData r}
    (hr : r < 1) (C : ConstructedA2ProperMomentCoordinate r H)
    (q : constructedLocalPositivePart r)
    (hq : constructedModel.t (q : LocalCarrier constructedModel r) = 0) :
    (fun i : Fin 2 ↦ (C.toHomeomorph hr q).1 i.castSucc) =
      H.honeycomb.symm ⟨q, hq⟩ := by
  simpa only [toHomeomorph_apply] using C.coordinate_central q hq

end ConstructedA2ProperMomentCoordinate

/-- The semantically pinned global extension gives component one of the constructed polar
honeycomb coordinate data. -/
public theorem constructedA2MomentCoordinateHomeomorph_of_properCoordinate
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (H : ConstructedHoneycombCellData W.localWitness.radius)
    (C : ConstructedA2ProperMomentCoordinate W.localWitness.radius H) :
    Nonempty (constructedLocalPositivePart W.localWitness.radius ≃ₜ
      constructedPositiveMomentRegion W.localWitness.radius) :=
  ⟨C.toHomeomorph W.localWitness.radius_lt_one⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
