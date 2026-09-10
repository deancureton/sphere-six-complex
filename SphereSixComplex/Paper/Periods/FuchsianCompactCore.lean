module

public import SphereSixComplex.Paper.Periods.FuchsianUniformizationBridge
public import SphereSixComplex.Prerequisites.Periods.FuchsianCompactGeometry
import all SphereSixComplex.Prerequisites.Periods.FuchsianCompactGeometry

noncomputable section

namespace SphereSixComplex.Periods

open Set SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain

/-- A translate-covering theorem for the explicit triangle gives the compact quotient core used
by the Schur-bound argument. -/
@[expose] public noncomputable def fuchsianQuotientCompactCore
    (P : FuchsianModularParameter) (hcover : FuchsianFundamentalTriangleCovers) :
    QuotientCompactCore P.toTriangleUniformization where
  carrier := fuchsianFundamentalCompactCore
  compact := fuchsianFundamentalCompactCore_isCompact
  cover z := by
    obtain ⟨g, hg⟩ := hcover z
    refine ⟨g, ?_⟩
    exact fundamentalTriangle_mem_cusp_or_compactCore hg

/-- Once the explicit triangle covers the upper half-plane, Fuchsian pre-period data produces the
full nondegenerate period family. -/
public theorem FuchsianPrePeriodData.theorem3_4Existence_of_triangleCover
    (D : FuchsianPrePeriodData) (hcover : FuchsianFundamentalTriangleCovers) :
    Theorem3_4Existence D.toFuchsianModularParameter.toTriangleUniformization :=
  D.theorem3_4Existence (fuchsianQuotientCompactCore D.toFuchsianModularParameter hcover)

end SphereSixComplex.Periods
