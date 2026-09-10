module
public import SphereSixComplex.Paper.Topology.GlobalInvariantPeriodCircle
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
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

local instance transportRegularBaseDeckAction : MulAction Delta (RegularBase (U := U)) :=
  regularSourceMulAction U
local instance transportRegularTotalDeckAction : MulAction Delta (RegularTotalSpace F) :=
  regularFamilyDeckAction F

public def regularPeriodCircleProjection :
    C(ℝ × RegularBase (U := U), UnitAddCircle × RegularBase (U := U)) where
  toFun p := ((p.1 : UnitAddCircle), p.2)
  continuous_toFun := (AddCircle.continuous_mk' 1).prodMap continuous_id

public theorem regularPeriodCircleProjection_isQuotientMap :
    IsQuotientMap (regularPeriodCircleProjection (U := U)) :=
  (QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap

public theorem regularPeriodRealOrbit_factors (n : IntegerPeriods) :
    Function.FactorsThrough (regularPeriodRealOrbit F n)
      (regularPeriodCircleProjection (U := U)) := by
  rintro ⟨t, b⟩ ⟨u, c⟩ h
  have hb : b = c := congrArg Prod.snd h
  subst c
  have ht : (t : UnitAddCircle) = (u : UnitAddCircle) := congrArg Prod.fst h
  have hz : ((t - u : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, ht, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  have htu : t = u + k := by
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  rw [htu, regularPeriodRealOrbit_add_int]

public def regularPeriodCircle (n : IntegerPeriods) :
    C(UnitAddCircle × RegularBase (U := U), RegularTotalSpace F) :=
  regularPeriodCircleProjection_isQuotientMap.lift
    (regularPeriodRealOrbit F n) (regularPeriodRealOrbit_factors F n)

public theorem regularPeriodCircle_real (n : IntegerPeriods) (t : ℝ)
    (b : RegularBase (U := U)) :
    regularPeriodCircle F n ((t : UnitAddCircle), b) = regularPeriodRealOrbit F n (t, b) :=
  DFunLike.congr_fun (regularPeriodCircleProjection_isQuotientMap.lift_comp
    (regularPeriodRealOrbit F n) (regularPeriodRealOrbit_factors F n)) (t, b)

public theorem regularPeriodCircle_equivariant (n : IntegerPeriods)
    (g : Delta) (t : UnitAddCircle) (b : RegularBase (U := U)) :
    regularFamilyDeckMap F g (regularPeriodCircle F n (t, b)) =
      regularPeriodCircle F (rhoLambda g n) (t, regularSourceEquiv g b) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [regularPeriodCircle_real, regularPeriodCircle_real]
  change regularFamilyDeckMap F g
    (Quotient.mk _ (b, r • periodVector (regularParameterMap F b).1 n)) = _
  rw [regularFamilyDeckMap_mk]
  apply congrArg (projection (regularParameterMap F))
  apply Prod.ext
  · rfl
  · change periodTransport g (regularParameterMap F b)
      (r • periodVector (regularParameterMap F b).1 n) = _
    rw [map_smul, periodTransport_periodVector]
    change r • periodVector (rhoParameters g (parameterMap F b.1)).1 (rhoLambda g n) =
      r • periodVector (parameterMap F (U.sourceAction g • b.1)).1 (rhoLambda g n)
    rw [parameterMap_equivariant]

public def regularPeriodCircleInGlobal (n : IntegerPeriods) :
    C(UnitAddCircle × RegularBase (U := U), PuncturedGlobalFamily F) :=
  ⟨fun p ↦ quotientProjection (M := RegularTotalSpace F) (G := Delta)
    (regularPeriodCircle F n p), continuous_quot_mk.comp (regularPeriodCircle F n).continuous⟩

public theorem regularPeriodCircleInGlobal_equivariant (n : IntegerPeriods)
    (g : Delta) (t : UnitAddCircle) (b : RegularBase (U := U)) :
    regularPeriodCircleInGlobal F (rhoLambda g n) (t, regularSourceEquiv g b) =
      regularPeriodCircleInGlobal F n (t, b) := by
  change Quotient.mk _ (regularPeriodCircle F (rhoLambda g n)
    (t, regularSourceEquiv g b)) = Quotient.mk _ (regularPeriodCircle F n (t, b))
  rw [← regularPeriodCircle_equivariant]
  apply Quotient.sound
  change MulAction.orbitRel Delta (RegularTotalSpace F)
    (regularFamilyDeckMap F g (regularPeriodCircle F n (t, b)))
    (regularPeriodCircle F n (t, b))
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨g, rfl⟩


public def regularPeriodCircleFamily (n : IntegerPeriods) :
    C(RegularBase (U := U), C(UnitAddCircle, PuncturedGlobalFamily F)) :=
  ((regularPeriodCircleInGlobal F n).comp ⟨Prod.swap, continuous_swap⟩).curry

public theorem regularPeriodCircleFamily_deck (n : IntegerPeriods)
    (g : Delta) (b : RegularBase (U := U)) :
    regularPeriodCircleFamily F n (regularSourceEquiv g b) =
      regularPeriodCircleFamily F (rhoLambda g⁻¹ n) b := by
  ext t
  have h := regularPeriodCircleInGlobal_equivariant F (rhoLambda g⁻¹ n) g t b
  have he : rhoLambda g (rhoLambda g⁻¹ n) = n := by
    change (rhoLambda g * rhoLambda g⁻¹) n = n
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [he] at h
  exact h

public def regularPeriodCirclePath (n : IntegerPeriods)
    {b c : RegularBase (U := U)} (p : Path b c) :
    Path (regularPeriodCircleFamily F n b) (regularPeriodCircleFamily F n c) :=
  p.map (regularPeriodCircleFamily F n).continuous

public theorem regularPeriodCirclePath_apply (n : IntegerPeriods)
    {b c : RegularBase (U := U)} (p : Path b c) (u : unitInterval) (t : UnitAddCircle) :
    regularPeriodCirclePath F n p u t = regularPeriodCircleInGlobal F n (t, p u) := rfl

public theorem regularPeriodCirclePath_trans (n : IntegerPeriods)
    {b c d : RegularBase (U := U)} (p : Path b c) (q : Path c d) :
    regularPeriodCirclePath F n (p.trans q) =
      (regularPeriodCirclePath F n p).trans (regularPeriodCirclePath F n q) :=
  Path.map_trans p q (regularPeriodCircleFamily F n).continuous

public def regularPeriodCirclePath_homotopy (n : IntegerPeriods)
    {b c : RegularBase (U := U)} {p q : Path b c} (H : p.Homotopy q) :
    (regularPeriodCirclePath F n p).Homotopy (regularPeriodCirclePath F n q) :=
  H.map (regularPeriodCircleFamily F n)

public def regularPeriodCircleDeckPath (n : IntegerPeriods)
    (g : Delta) {b : RegularBase (U := U)} (p : Path b (regularSourceEquiv g b)) :
    Path (regularPeriodCircleFamily F n b) (regularPeriodCircleFamily F (rhoLambda g⁻¹ n) b) :=
  (regularPeriodCirclePath F n p).cast rfl (regularPeriodCircleFamily_deck F n g b).symm

end SphereSixComplex.Geometry.GlobalTorusFamily
end
end
