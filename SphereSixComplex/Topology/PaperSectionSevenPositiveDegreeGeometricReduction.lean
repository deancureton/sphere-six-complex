module

public import SphereSixComplex.Topology.PaperSectionSevenPositiveDegreeRealization

/-!
# Geometric reduction of the Section 7 positive-degree input

The regular central image can be assigned to both elliptic sides, so the allocation itself is
canonical.  The remaining radial input is the contraction and band-trivialization package.  Once
any two-disc cover and its marked cycles have been realized, they directly supply the production
positive-degree homology assembly.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Assign the whole regular central image to both elliptic sides. -/
public def duplicatedSectionSevenEllipticCentralAllocation :
    A.SectionSevenEllipticCentralAllocation where
  orderThreeCentral := A.sectionSevenEllipticCentralImage
  orderFourCentral := A.sectionSevenEllipticCentralImage
  orderThreeCentral_isOpen := A.sectionSevenEllipticCentralImage_isOpen
  orderFourCentral_isOpen := A.sectionSevenEllipticCentralImage_isOpen
  central_cover := fun _ hx ↦ Or.inl hx

/-- The canonical central allocation and a radial realization extend by exactly the dependent
marked-cycle package to the complete geometric realization. -/
public def SectionSevenPositiveDegreeGeometricRealization.ofDuplicatedCentralAllocation
    (R : A.duplicatedSectionSevenEllipticCentralAllocation.RadialRealization)
    (M : A.SectionSevenEllipticInteriorMarkedCycleData
      R.toSectionSevenEllipticTwoDiscCoverData) :
    A.SectionSevenPositiveDegreeGeometricRealization where
  allocation := A.duplicatedSectionSevenEllipticCentralAllocation
  radial := R
  markedCycles := M

/-- A realized two-disc cover with its marked cycles is sufficient for the production
positive-degree homology assembly; no further central-allocation data enters the calculation. -/
public theorem exists_positiveDegreeHomologyAssembly_of_exists_markedCycles
    (h : ∃ D : A.SectionSevenEllipticTwoDiscCoverData,
      Nonempty (A.SectionSevenEllipticInteriorMarkedCycleData D)) :
    Nonempty A.SectionSevenPositiveDegreeHomologyAssembly := by
  obtain ⟨D, ⟨M⟩⟩ := h
  exact ⟨M.positiveDegreeHomologyAssembly⟩

/-- Every complete geometric realization determines the weaker dependent marked-cycle witness
that is sufficient for the production homology assembly. -/
public theorem SectionSevenPositiveDegreeGeometricRealization.exists_markedCycles
    (R : A.SectionSevenPositiveDegreeGeometricRealization) :
    ∃ D : A.SectionSevenEllipticTwoDiscCoverData,
      Nonempty (A.SectionSevenEllipticInteriorMarkedCycleData D) :=
  ⟨R.radial.toSectionSevenEllipticTwoDiscCoverData, ⟨R.markedCycles⟩⟩

end SphereSixComplex.Geometry.PaperAnalyticData
