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

local instance orbitRegularBaseDeckAction : MulAction Delta (RegularBase (U := U)) :=
  regularSourceMulAction U
local instance orbitRegularTotalDeckAction : MulAction Delta (RegularTotalSpace F) :=
  regularFamilyDeckAction F

public noncomputable def regularPeriodRealOrbit (n : IntegerPeriods) :
    C(ℝ × RegularBase (U := U), RegularTotalSpace F) where
  toFun p := projection (regularParameterMap F)
    (p.2, p.1 • periodVector (regularParameterMap F p.2).1 n)
  continuous_toFun := continuous_quot_mk.comp
    (continuous_snd.prodMk (continuous_fst.smul
      ((periodSection_contMDiff F n 0).continuous.comp
        (continuous_subtype_val.comp continuous_snd))))

public theorem regularPeriodRealOrbit_equivariant
    (n : IntegerPeriods) (hn : ∀ g : Delta, rhoLambda g n = n)
    (g : Delta) (t : ℝ) (b : RegularBase (U := U)) :
    regularFamilyDeckMap F g (regularPeriodRealOrbit F n (t, b)) =
      regularPeriodRealOrbit F n (t, regularSourceEquiv g b) := by
  change regularFamilyDeckMap F g
    (Quotient.mk _ (b, t • periodVector (regularParameterMap F b).1 n) : RegularTotalSpace F) =
      projection (regularParameterMap F)
        (regularSourceEquiv g b, t • periodVector (regularParameterMap F (regularSourceEquiv g b)).1 n)
  rw [regularFamilyDeckMap_mk]
  apply congrArg (projection (regularParameterMap F))
  apply Prod.ext
  · rfl
  · change periodTransport g (regularParameterMap F b)
      (t • periodVector (regularParameterMap F b).1 n) = _
    rw [map_smul, periodTransport_periodVector, hn]
    change t • periodVector (rhoParameters g (parameterMap F b.1)).1 n =
      t • periodVector (parameterMap F (U.sourceAction g • b.1)).1 n
    rw [parameterMap_equivariant]

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

public noncomputable def invariantPeriodRealOrbit
    (n : IntegerPeriods) (hn : ∀ g : Delta, rhoLambda g n = n) :
    C(ℝ × PuncturedOrbifoldBase (U := U), PuncturedGlobalFamily F) where
  toFun p := Quotient.lift
    (fun b ↦ quotientProjection (M := RegularTotalSpace F) (G := Delta)
      (regularPeriodRealOrbit F n (p.1, b))) (by
        intro a b hab
        change MulAction.orbitRel Delta (RegularBase (U := U)) a b at hab
        apply Quotient.sound
        change MulAction.orbitRel Delta (RegularTotalSpace F)
          (regularPeriodRealOrbit F n (p.1, a)) (regularPeriodRealOrbit F n (p.1, b))
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
        obtain ⟨g, rfl⟩ := hab
        exact ⟨g, regularPeriodRealOrbit_equivariant F n hn g p.1 b⟩) p.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quot_mk.comp (regularPeriodRealOrbit F n).continuous

public theorem invariantPeriodRealOrbit_add_int
    (n : IntegerPeriods) (hn : ∀ g : Delta, rhoLambda g n = n)
    (t : ℝ) (k : ℤ) (b : PuncturedOrbifoldBase (U := U)) :
    invariantPeriodRealOrbit F n hn (t + k, b) =
      invariantPeriodRealOrbit F n hn (t, b) := by
  induction b using Quotient.inductionOn with
  | _ b =>
    change quotientProjection (M := RegularTotalSpace F) (G := Delta)
      (regularPeriodRealOrbit F n (t + k, b)) = _
    rw [regularPeriodRealOrbit_add_int]
    rfl

public def invariantPeriodCircleProjection :
    C(ℝ × PuncturedOrbifoldBase (U := U),
      UnitAddCircle × PuncturedOrbifoldBase (U := U)) where
  toFun p := ((p.1 : UnitAddCircle), p.2)
  continuous_toFun := (AddCircle.continuous_mk' 1).prodMap continuous_id

public theorem invariantPeriodCircleProjection_isQuotientMap :
    IsQuotientMap (invariantPeriodCircleProjection (U := U)) :=
  (QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap

public theorem invariantPeriodRealOrbit_factors
    (n : IntegerPeriods) (hn : ∀ g : Delta, rhoLambda g n = n) :
    Function.FactorsThrough (invariantPeriodRealOrbit F n hn)
      (invariantPeriodCircleProjection (U := U)) := by
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
  rw [htu, invariantPeriodRealOrbit_add_int]

public noncomputable def invariantPeriodCircle
    (n : IntegerPeriods) (hn : ∀ g : Delta, rhoLambda g n = n) :
    C(UnitAddCircle × PuncturedOrbifoldBase (U := U), PuncturedGlobalFamily F) :=
  invariantPeriodCircleProjection_isQuotientMap.lift
    (invariantPeriodRealOrbit F n hn) (invariantPeriodRealOrbit_factors F n hn)

public theorem invariantPeriodCircle_real
    (n : IntegerPeriods) (hn : ∀ g : Delta, rhoLambda g n = n)
    (t : ℝ) (b : PuncturedOrbifoldBase (U := U)) :
    invariantPeriodCircle F n hn ((t : UnitAddCircle), b) =
      invariantPeriodRealOrbit F n hn (t, b) :=
  DFunLike.congr_fun
    (invariantPeriodCircleProjection_isQuotientMap.lift_comp
      (invariantPeriodRealOrbit F n hn) (invariantPeriodRealOrbit_factors F n hn)) (t, b)

public theorem invariantPeriodCircle_baseProjection
    (n : IntegerPeriods) (hn : ∀ g : Delta, rhoLambda g n = n)
    (t : UnitAddCircle) (b : PuncturedOrbifoldBase (U := U)) :
    puncturedGlobalBaseProjection F (invariantPeriodCircle F n hn (t, b)) = b := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [invariantPeriodCircle_real]
  induction b using Quotient.inductionOn with
  | _ b => rfl

end SphereSixComplex.Geometry.GlobalTorusFamily
end
end

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open GlobalTorusFamily TriangleGroup SphereSixComplex.Topology

public noncomputable def centralFourthPeriodCircle (A : PaperAnalyticData) :
    C(UnitAddCircle × TwicePuncturedComplex, A.CentralFamily) :=
  (invariantPeriodCircle A.periods ![0, 0, 0, 1] rhoLambda_fourthBasis).comp
    ⟨fun p ↦ (p.1, A.puncturedBaseHomeomorphTwicePuncturedComplex.symm p.2),
      continuous_fst.prodMk
        (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm.continuous.comp continuous_snd)⟩

public theorem centralFourthPeriodCircle_coordinate (A : PaperAnalyticData)
    (t : UnitAddCircle) (b : TwicePuncturedComplex) :
    A.centralFamilyCoordinate (A.centralFourthPeriodCircle (t, b)) = b := by
  have hc : ∀ q : A.CentralFamily,
      A.centralFamilyCoordinate q = A.puncturedBaseHomeomorphTwicePuncturedComplex
        (puncturedGlobalBaseProjection A.periods q) := by
    intro q
    induction q using Quotient.inductionOn with
    | _ q =>
      induction q using Quotient.inductionOn with
      | _ q => rfl
  rw [hc]
  change A.puncturedBaseHomeomorphTwicePuncturedComplex
    (puncturedGlobalBaseProjection A.periods
      (invariantPeriodCircle A.periods ![0, 0, 0, 1] rhoLambda_fourthBasis
        (t, A.puncturedBaseHomeomorphTwicePuncturedComplex.symm b))) = b
  rw [invariantPeriodCircle_baseProjection, Homeomorph.apply_symm_apply]

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
