module

public import SphereSixComplex.Paper.Geometry.EllipticVaryingFamilyQuotient
public import SphereSixComplex.Prerequisites.TriangleGroup.EstablishedFuchsianEllipticStabilizers
public import SphereSixComplex.Paper.TriangleGroup.FuchsianProperFreeness
public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianSmoothAction
import all SphereSixComplex.Paper.TriangleGroup.Representation
import all SphereSixComplex.Paper.Geometry.TorusFamily

/-!
# Separation for the affine global elliptic action

The affine free-product action covers the explicit Fuchsian source action.  Proper discontinuity
therefore lifts from the source.  The final collar separation is reduced to the exact source
stabilizer calculation at the two elliptic points.
-/

namespace SphereSixComplex.Geometry.EllipticAffineGlobalSeparation

open Complex
open Filter Set SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)













/-- Every open neighborhood of a Cayley center contains a positive radial Cayley ball. -/
public theorem exists_cayleyRadius_subset
    (a : UpperHalfPlane) {S : Set UpperHalfPlane}
    (hS : IsOpen S) (ha : a ∈ S) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ z : UpperHalfPlane, ‖(UpperHalfPlane.cayleyHomeomorph a z).1‖ < r → z ∈ S := by
  have hcenter : UpperHalfPlane.cayleyHomeomorph a a = ComplexUnitDisc.center := by
    apply Subtype.ext
    simp [UpperHalfPlane.cayleyHomeomorph, UpperHalfPlane.cayleyToDisc, UpperHalfPlane.cayley, ComplexUnitDisc.center]
  have hopen : IsOpen (UpperHalfPlane.cayleyHomeomorph a '' S) :=
    (UpperHalfPlane.cayleyHomeomorph a).isOpenMap S hS
  have hmem : ComplexUnitDisc.center ∈ UpperHalfPlane.cayleyHomeomorph a '' S :=
    ⟨a, ha, hcenter⟩
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) ComplexUnitDisc.center hmem
  let r := min ε (1 / 2 : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_right ε (1 / 2 : ℝ)) (by norm_num)
  refine ⟨r, hr, hr1, ?_⟩
  intro z hz
  have hzball : UpperHalfPlane.cayleyHomeomorph a z ∈ Metric.ball ComplexUnitDisc.center ε := by
    change dist (UpperHalfPlane.cayleyHomeomorph a z).1 (ComplexUnitDisc.center : ℂ) < ε
    change dist (UpperHalfPlane.cayleyHomeomorph a z).1 0 < ε
    rw [dist_zero_right]
    exact hz.trans_le (min_le_left _ _)
  obtain ⟨w, hw, hwz⟩ := hball hzball
  have hwz' : w = z := (UpperHalfPlane.cayleyHomeomorph a).injective hwz
  rwa [← hwz']





end

end SphereSixComplex.Geometry.EllipticAffineGlobalSeparation
