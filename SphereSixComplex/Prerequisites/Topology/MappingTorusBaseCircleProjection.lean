module

public import SphereSixComplex.Prerequisites.Topology.IntervalClutchingQuotientCore
public import Mathlib.Topology.Instances.AddCircle.Real

@[expose] public section
open scoped ContinuousMap
namespace SphereSixComplex

/-- The interval coordinate respects the endpoint identifications of a circle mapping torus
after reduction modulo `ℤ`. -/
public theorem circleMappingTorusBaseCircleProjection_respects
    {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)
    (p q : Unit × unitInterval × F)
    (h : finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ φ) p q) :
    ((p.2.1 : ℝ) : UnitAddCircle) = ((q.2.1 : ℝ) : UnitAddCircle) := by
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy | hxy
      · rw [hxy.2]
      · rw [hxy.1, hxy.2.1]
      · rw [hxy.1, hxy.2.1]
        simp
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- The unconditional base-circle projection of a circle mapping torus. -/
public def circleMappingTorusBaseCircleProjection
    {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F) :
    C(CircleMappingTorus φ, UnitAddCircle) where
  toFun := Quotient.lift
    (fun p : Unit × unitInterval × F ↦ ((p.2.1 : ℝ) : UnitAddCircle))
    (circleMappingTorusBaseCircleProjection_respects φ)
  continuous_toFun := continuous_quot_lift
    (circleMappingTorusBaseCircleProjection_respects φ)
    (continuous_quotient_mk'.comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))

@[simp]
public theorem circleMappingTorusBaseCircleProjection_cylinderProjection
    {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F) (p : unitInterval × F) :
    circleMappingTorusBaseCircleProjection φ (circleMappingTorusCylinderProjection φ p) =
      ((p.1 : ℝ) : UnitAddCircle) :=
  rfl

@[simp]
public theorem circleMappingTorusBaseCircleProjection_fiberInclusion
    {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F) (x : F) :
    circleMappingTorusBaseCircleProjection φ
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ φ) x) = 0 :=
  rfl

end SphereSixComplex
