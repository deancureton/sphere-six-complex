module

public import SphereSixComplex.Paper.Periods.OrbifoldAffineTorsorCuspFrameBounds

noncomputable section

namespace SphereSixComplex.Periods

namespace OrbifoldAffineDescentData

/-- The more concrete gluing package used by the cusp-bound modules also suffices for the full
analytic descent certificate. -/
public theorem nonempty_analyticDescentData_of_cechGluingData
    (P : OrbifoldAffineDescentData) (D : P.CechGluingData) :
    Nonempty P.AnalyticDescentData := by
  obtain ⟨C⟩ := P.nonempty_cuspBoundedCorrection_of_cechGluingData D
  exact P.nonempty_analyticDescentData_of_hasCuspBoundedSection
    (P.hasCuspBoundedSection_of_correction C)

end OrbifoldAffineDescentData

end SphereSixComplex.Periods
