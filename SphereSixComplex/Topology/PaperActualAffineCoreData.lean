module

public import SphereSixComplex.Topology.EstablishedEquivariantUniversalCover
public import SphereSixComplex.Topology.PaperVanKampenAlgebraAdapter
public import SphereSixComplex.Geometry.PaperAnalyticData

/-!
# The affine fundamental-group data of the paper's central family

The generic punctured-Fuchsian universal-cover classification specializes to the period family
selected by the paper.  Its free meridians have precisely the two integral monodromy matrices
used by the final van Kampen calculation.
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
  establishedPuncturedGlobalFamilyEquivariantUniversalCover A.periods

/-- A chosen point of the affine universal cover. -/
public noncomputable def centralAffineUniversalCoverPoint :
    A.centralAffineUniversalCover.Cover := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact Classical.arbitrary D.Cover

/-- The induced base point in the actual central family. -/
public noncomputable def centralAffineBase : A.CentralFamily := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact D.data.projection A.centralAffineUniversalCoverPoint

/-- The two free meridians and the period lattice give the actual central-family
fundamental-group presentation. -/
public noncomputable def centralAffineCorePiOneData :
    AffineTorusCorePiOneData (FundamentalGroup A.CentralFamily A.centralAffineBase)
      Lattice paperMonodromyOne paperMonodromyTwo := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let C := D.data.fundamentalGroupCorePiOneData A.centralAffineUniversalCoverPoint
  have hOne :
      firstFreeMonodromy
          (freeTwoMeridianMonodromy (twoMeridianOrbifoldMap g₁ g₂)
            integralOrbifoldPeriodMonodromy) =
        paperMonodromyOne := by
    apply AddMonoidHom.ext
    intro a
    simp [firstFreeMonodromy, freeTwoMeridianMonodromy,
      integralOrbifoldPeriodMonodromy, paperMonodromyOne]
  have hTwo :
      secondFreeMonodromy
          (freeTwoMeridianMonodromy (twoMeridianOrbifoldMap g₁ g₂)
            integralOrbifoldPeriodMonodromy) =
        paperMonodromyTwo := by
    apply AddMonoidHom.ext
    intro a
    simp [secondFreeMonodromy, freeTwoMeridianMonodromy,
      integralOrbifoldPeriodMonodromy, paperMonodromyTwo]
  rw [← hOne, ← hTwo]
  exact C

end SphereSixComplex.Geometry.PaperAnalyticData

end
