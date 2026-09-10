module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData

public def unitCircleExponential : C(UnitAddCircle, ℂˣ) where
  toFun z := Circle.toUnits (AddCircle.toCircle z)
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val.comp AddCircle.continuous_toCircle
    · change Continuous (fun z : UnitAddCircle ↦ ((AddCircle.toCircle z)⁻¹ : Circle).val)
      exact continuous_subtype_val.comp (AddCircle.continuous_toCircle.inv)

public theorem unitCircleExponential_real (t : ℝ) :
    (unitCircleExponential (t : UnitAddCircle) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  change ((AddCircle.toCircle (t : UnitAddCircle) : Circle) : ℂ) = _
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  push_cast
  ring

end SphereSixComplex.Geometry.PaperAnalyticData
