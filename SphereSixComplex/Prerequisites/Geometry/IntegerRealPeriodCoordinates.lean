module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum

public section
namespace SphereSixComplex.Geometry.ComplexTorus

/-- The group of integral coefficients for four periods. -/
public abbrev IntegerPeriods := Fin 4 → ℤ

/-- The real coefficient space underlying four periods. -/
public abbrev RealPeriods := Fin 4 → ℝ

/-- The standard inclusion of `ℤ⁴` into `ℝ⁴`. -/
@[expose] public def integerToReal (n : IntegerPeriods) : RealPeriods := fun i ↦ n i

/-- The standard inclusion of integral coefficients into real coefficients is injective. -/
public theorem integerToReal_injective : Function.Injective integerToReal := by
  intro a b h
  funext i
  have hi := congrFun h i
  change (a i : ℝ) = (b i : ℝ) at hi
  exact_mod_cast hi

end SphereSixComplex.Geometry.ComplexTorus
