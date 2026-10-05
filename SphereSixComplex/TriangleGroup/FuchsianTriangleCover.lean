module

public import SphereSixComplex.Prerequisites.TriangleGroup.Fuchsian.TriangleGeometry
public import SphereSixComplex.Periods.Uniformization
public import SphereSixComplex.Prerequisites.Periods.FuchsianCompactGeometry

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


end SphereSixComplex.Periods
