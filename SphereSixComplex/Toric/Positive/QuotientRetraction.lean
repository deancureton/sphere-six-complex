module

public import SphereSixComplex.Toric.Positive.HeightRetraction
public import SphereSixComplex.Prerequisites.Topology.Collar.Cofibration
public import SphereSixComplex.Prerequisites.Topology.Homotopy.StrongDeformationRetraction
public import TauCeti.Topology.Homotopy.Extension.DeformationRetract

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspCollar CuspPeriodExpansion

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def constructedPositiveQuotientRetraction
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    StrongDeformationRetraction (PositiveQuotient W) (positiveQuotientCore W) := by
  apply Classical.choice
  let _ : T2Space (PositiveQuotient W) := constructedPositiveDeck_quotient_t2 W
  have hHEP := (constructedPositiveQuotientCollar W).hasHomotopyExtensionProperty
    (isCompact_positiveQuotientCore W)
  obtain ⟨e, he⟩ := positiveQuotientCore_isHomotopyEquivalence W
  have he' : e.toFun = ContinuousMap.subtypeVal (positiveQuotientCore W) :=
    ContinuousMap.ext (congrFun he)
  obtain ⟨r, hr, ⟨H⟩⟩ := hHEP.exists_strong_deformation_retraction e.invFun
    (by simpa only [← he'] using e.left_inv)
    (by simpa only [← he'] using e.right_inv)
  exact
    ⟨{ retract := (ContinuousMap.subtypeVal (positiveQuotientCore W)).comp r
       homotopy := H.toHomotopy
       retract_mem := fun x ↦ (r x).2
       retract_fixed := fun x hx ↦ congrArg Subtype.val (hr ⟨x, hx⟩)
       homotopy_fixed := fun t x hx ↦ H.eq_fst t hx }⟩

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
