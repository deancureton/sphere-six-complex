module

public import SphereSixComplex.Paper.Topology.EstablishedEquivariantUniversalCover
public import SphereSixComplex.Paper.Topology.PaperVanKampenAlgebraAdapter
public import SphereSixComplex.Paper.Topology.PaperActualCuspCentralBaseMap
public import SphereSixComplex.Paper.Topology.PaperGeometricCentralCore

/-!
# The affine fundamental-group data of the paper's central family

The universal cover is retained for the filling-cover comparison.  The affine core marking itself
is built from the literal cusp period loops and the two geometric finite meridians, whose common
peripheral conjugator gives precisely the two integral monodromy matrices used by the final van
Kampen calculation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open ComplexTorus GlobalTorusFamily
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- The chosen affine universal cover of the paper's punctured central family. -/
public noncomputable def centralAffineUniversalCover :=
  establishedPuncturedGlobalFamilyEquivariantUniversalCover A

/-- A chosen point of the affine universal cover above the actual cusp-overlap base. -/
public noncomputable def centralAffineUniversalCoverPoint :
    A.centralAffineUniversalCover.Cover := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact Classical.choose (D.data.quotientCovering.surjective A.cuspCentralBase)

@[simp]
public theorem centralAffineUniversalCoverPoint_projects :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    D.data.projection A.centralAffineUniversalCoverPoint = A.cuspCentralBase := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose_spec
    (D.data.quotientCovering.surjective A.cuspCentralBase)

/-- The induced base point in the actual central family. -/
public noncomputable def centralAffineBase : A.CentralFamily := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact D.data.projection A.centralAffineUniversalCoverPoint

@[simp]
public theorem centralAffineBase_eq_actualCuspCentralBase :
    A.centralAffineBase = A.cuspCentralBase := by
  exact A.centralAffineUniversalCoverPoint_projects

/-- Equality transport from the literal actual cusp base to the displayed affine base. -/
public noncomputable def cuspToCentralAffineBaseEquiv :
    FundamentalGroup A.CentralFamily A.cuspCentralBase ≃*
      FundamentalGroup A.CentralFamily A.centralAffineBase :=
  SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq
    A.centralAffineBase_eq_actualCuspCentralBase.symm

/-- The actual geometric affine-core presentation, transported across the definitional affine
basepoint equality.  Its marking is therefore fixed by literal cusp loops rather than by an
arbitrary labelling of the chosen universal cover. -/
public noncomputable def centralAffineCorePiOneData :
    AffineTorusCorePiOneData (FundamentalGroup A.CentralFamily A.centralAffineBase)
      Lattice paperMonodromyOne paperMonodromyTwo :=
  A.cuspGeometricCorePiOneData.mapSurjective
    A.cuspToCentralAffineBaseEquiv.toMonoidHom
    A.cuspToCentralAffineBaseEquiv.surjective

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

end SphereSixComplex.Geometry.PaperAnalyticData

end
