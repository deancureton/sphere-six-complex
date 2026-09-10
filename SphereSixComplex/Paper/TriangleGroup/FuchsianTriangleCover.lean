module

public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianTriangleGeometry
public import SphereSixComplex.Paper.Periods.FuchsianCompactCore

noncomputable section

namespace SphereSixComplex.Periods

open Set SphereSixComplex.TriangleGroup.FuchsianTriangleCover

/-- Compact quotient core obtained from the correct doubled orientation-preserving domain. -/
@[expose] public noncomputable def orientedFuchsianQuotientCompactCore
    (P : FuchsianModularParameter) : QuotientCompactCore P.toTriangleUniformization where
  carrier := orientedFuchsianCompactCore
  compact := orientedFuchsianCompactCore_isCompact
  cover z := by
    obtain ⟨g, hg⟩ := exists_smul_mem_orientedFundamentalRegion z
    exact ⟨g, orientedFundamentalRegion_mem_cusp_or_compactCore hg⟩

/-- The doubled chamber cover supplies the compact-core input without the false single-reflection-
triangle cover premise. -/
public theorem FuchsianPrePeriodData.theorem3_4Existence_of_orientedTriangleCover
    (D : FuchsianPrePeriodData) :
    Theorem3_4Existence D.toFuchsianModularParameter.toTriangleUniformization :=
  D.theorem3_4Existence
    (orientedFuchsianQuotientCompactCore D.toFuchsianModularParameter)

end SphereSixComplex.Periods
