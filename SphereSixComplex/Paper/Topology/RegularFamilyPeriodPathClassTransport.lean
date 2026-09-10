module
public import SphereSixComplex.Paper.Geometry.GlobalTorusFiberFundamentalGroup

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.TorusFamily

variable {U : TriangleUniformization} (F : PeriodFunctions U)

public theorem regularFamilyPeriodLoop_transport_map_of_pathClass
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    {p₀ p₁ : RegularBase (U := U) × ComplexTwoSpace}
    (W : Path.Homotopic.Quotient (regularFamilyCoverProjection F p₀)
      (regularFamilyCoverProjection F p₁))
    (a : IntegerPeriods)
    {Y : Type*} [TopologicalSpace Y] (f : C(RegularTotalSpace F, Y)) :
    Path.Homotopic.Quotient.mk ((regularFamilyPeriodLoop F p₀ a).map f.continuous) =
      (W.map f).trans
        ((Path.Homotopic.Quotient.mk ((regularFamilyPeriodLoop F p₁ a).map f.continuous)).trans
          (W.map f).symm) := by
  induction W using Quotient.ind with
  | _ W =>
    change Path.Homotopic.Quotient.mk ((regularFamilyPeriodLoop F p₀ a).map f.continuous) =
      ((Path.Homotopic.Quotient.mk W).map f).trans
        ((Path.Homotopic.Quotient.mk ((regularFamilyPeriodLoop F p₁ a).map f.continuous)).trans
          ((Path.Homotopic.Quotient.mk W).map f).symm)
    have h := regularFamilyPeriodLoop_transport_map_of_path F hproper W a f
    simpa only [whiskeredLoopClass, pathLoopClass,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.mk_map] using h

end SphereSixComplex.Geometry.GlobalTorusFamily
