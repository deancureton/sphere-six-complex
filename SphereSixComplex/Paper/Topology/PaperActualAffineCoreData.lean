module

public import SphereSixComplex.Paper.Topology.PaperGeometricCentralCore

/-!
# Geometric affine-core fundamental-group data

The affine core is based at the actual cusp-overlap point. Its marking consists of literal cusp
period loops and the geometric finite meridians, with their proved monodromy and generation
relations. No auxiliary universal-cover choice is required.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

open ComplexTorus GlobalTorusFamily
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup

variable (A : AnalyticData)

/-- The affine core is based at the actual cusp-overlap point. -/
public def centralAffineBase : A.CentralFamily := A.cuspCentralBase

@[simp]
public theorem centralAffineBase_eq_cuspCentralBase :
    A.centralAffineBase = A.cuspCentralBase := rfl

/-- The two core markings use the same base point. -/
public noncomputable def cuspToCentralAffineBaseEquiv :
    FundamentalGroup A.CentralFamily A.cuspCentralBase ≃*
      FundamentalGroup A.CentralFamily A.centralAffineBase :=
  MulEquiv.refl _

/-- The geometric core data at the common cusp base point. -/
public noncomputable def centralAffineCorePiOneData :
    AffineTorusCorePiOneData (FundamentalGroup A.CentralFamily A.centralAffineBase)
      Lattice paperMonodromyOne paperMonodromyTwo :=
  A.cuspGeometricCorePiOneData

/-- The affine core's translation field is the corrected literal cusp marking transported to
the displayed affine base. -/
public theorem centralAffineCorePiOneData_translation (a : Lattice) :
    Additive.toMul (A.centralAffineCorePiOneData.translation a) =
      A.cuspToCentralAffineBaseEquiv
        (Additive.toMul (A.correctedActualCuspCentralTranslation a)) := by
  rfl

/-- The first core meridian is the transported first geometric meridian. -/
public theorem centralAffineCorePiOneData_rhoOne :
    A.centralAffineCorePiOneData.rhoOne =
      A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoOne := by
  rfl

/-- The second core meridian is the transported second geometric meridian. -/
public theorem centralAffineCorePiOneData_rhoTwo :
    A.centralAffineCorePiOneData.rhoTwo =
      A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoTwo := by
  rfl

end SphereSixComplex.Geometry.AnalyticData

end
