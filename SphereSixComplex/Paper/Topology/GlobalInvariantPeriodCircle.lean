module
public import SphereSixComplex.Paper.Geometry.PaperMarkedPuncturedBase
public import SphereSixComplex.Paper.Topology.PaperCuspFourthPeriodInvariance

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
variable {U : TriangleUniformization} (F : PeriodFunctions U)

public noncomputable def regularPeriodRealOrbit (n : IntegerPeriods) :
    C(ℝ × RegularBase (U := U), RegularTotalSpace F) where
  toFun p := projection (regularParameterMap F)
    (p.2, p.1 • periodVector (regularParameterMap F p.2).1 n)
  continuous_toFun := continuous_quot_mk.comp
    (continuous_snd.prodMk (continuous_fst.smul
      ((periodSection_contMDiff F n 0).continuous.comp
        (continuous_subtype_val.comp continuous_snd))))

public theorem regularPeriodRealOrbit_add_int
    (n : IntegerPeriods) (t : ℝ) (k : ℤ) (b : RegularBase (U := U)) :
    regularPeriodRealOrbit F n (t + k, b) = regularPeriodRealOrbit F n (t, b) := by
  apply Quotient.sound
  change MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _
    (b, (t + k) • periodVector (regularParameterMap F b).1 n)
    (b, t • periodVector (regularParameterMap F b).1 n)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨(Multiplicative.ofAdd (k • n) : FamilyPeriodGroup (regularParameterMap F)), ?_⟩
  apply Prod.ext
  · rfl
  · change periodHom (regularParameterMap F b).1 (k • n) +
      t • periodVector (regularParameterMap F b).1 n = _
    rw [map_zsmul, add_smul]
    change k • periodVector (regularParameterMap F b).1 n +
      t • periodVector (regularParameterMap F b).1 n = _
    rw [Int.cast_smul_eq_zsmul]
    exact add_comm _ _

end SphereSixComplex.Geometry.GlobalTorusFamily
end
end

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open GlobalTorusFamily TriangleGroup SphereSixComplex.Topology

end SphereSixComplex.Geometry.AnalyticData
end
end
