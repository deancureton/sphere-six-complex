module
public import SphereSixComplex.Topology.GlobalInvariantPeriodCircle

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open ComplexTorus TorusFamily AnalyticTorusFamily
variable {U : TriangleUniformization} (F : PeriodFunctions U)
local instance : MulAction Delta (RegularBase (U := U)) := regularSourceMulAction U
local instance : MulAction Delta (RegularTotalSpace F) := regularFamilyDeckAction F

public def regularPeriodTranslationCover (n : IntegerPeriods) :
    C(ℝ × (RegularBase (U := U) × ComplexTwoSpace), RegularBase (U := U) × ComplexTwoSpace) where
  toFun p := (p.2.1,p.1 • periodVector (regularParameterMap F p.2.1).1 n + p.2.2)
  continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
    ((continuous_fst.smul ((periodSection_contMDiff F n 0).continuous.comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).add
        (continuous_snd.comp continuous_snd))

public theorem regularPeriodTranslationCover_orbit (n : IntegerPeriods) (t : ℝ)
    (p q : RegularBase (U := U) × ComplexTwoSpace)
    (h : MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _ p q) :
    MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _
      (regularPeriodTranslationCover F n (t,p)) (regularPeriodTranslationCover F n (t,q)) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
  obtain ⟨g,hg⟩ := h
  refine ⟨g,?_⟩
  have hb : p.1 = q.1 := by simpa only [family_smul_fst] using congrArg Prod.fst hg.symm
  apply Prod.ext
  · exact hb.symm
  · have hs := congrArg Prod.snd hg
    simp only [family_smul_snd] at hs ⊢
    change periodVector (regularParameterMap F q.1).1 g.coeff + (t • periodVector (regularParameterMap F q.1).1 n + q.2) =
      t • periodVector (regularParameterMap F p.1).1 n + p.2
    rw [hb, ← hs]
    abel

public def regularPeriodTranslation (n : IntegerPeriods) :
    C(ℝ × RegularTotalSpace F, RegularTotalSpace F) where
  toFun p := Quotient.lift (fun q ↦ projection (regularParameterMap F)
    (regularPeriodTranslationCover F n (p.1,q)))
    (fun a b h ↦ Quotient.sound (regularPeriodTranslationCover_orbit F n p.1 a b h)) p.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quot_mk.comp (regularPeriodTranslationCover F n).continuous

public theorem regularPeriodTranslation_mk (n : IntegerPeriods) (t : ℝ)
    (p : RegularBase (U := U) × ComplexTwoSpace) :
    regularPeriodTranslation F n (t,Quotient.mk _ p) =
      projection (regularParameterMap F) (p.1,t • periodVector (regularParameterMap F p.1).1 n + p.2) := rfl

public theorem regularPeriodTranslation_equivariant (n : IntegerPeriods)
    (hn : ∀ g : Delta, rhoLambda g n = n) (g : Delta) (t : ℝ) (q : RegularTotalSpace F) :
    regularFamilyDeckMap F g (regularPeriodTranslation F n (t,q)) =
      regularPeriodTranslation F n (t,regularFamilyDeckMap F g q) := by
  induction q using Quotient.inductionOn with
  | _ p =>
    simp only [regularPeriodTranslation_mk, projection, regularFamilyDeckMap_mk]
    change projection (regularParameterMap F)
      (regularSourceEquiv g p.1,periodTransport g (regularParameterMap F p.1)
        (t • periodVector (regularParameterMap F p.1).1 n + p.2)) = _
    rw [map_add, map_smul, periodTransport_periodVector, hn]
    apply congrArg (projection (regularParameterMap F))
    apply Prod.ext
    · rfl
    · change t • periodVector (rhoParameters g (parameterMap F p.1.1)).1 n + _ =
      t • periodVector (parameterMap F (U.sourceAction g • p.1.1)).1 n + _
      rw [parameterMap_equivariant]
      rfl


public def invariantPeriodRealTranslation (n : IntegerPeriods)
    (hn : ∀ g : Delta, rhoLambda g n = n) :
    C(ℝ × PuncturedGlobalFamily F, PuncturedGlobalFamily F) where
  toFun p := Quotient.lift
    (fun q ↦ quotientProjection (M := RegularTotalSpace F) (G := Delta)
      (regularPeriodTranslation F n (p.1,q))) (by
        intro a b hab
        change MulAction.orbitRel Delta (RegularTotalSpace F) a b at hab
        apply Quotient.sound
        change MulAction.orbitRel Delta (RegularTotalSpace F) _ _
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
        obtain ⟨g,rfl⟩ := hab
        exact ⟨g, regularPeriodTranslation_equivariant F n hn g p.1 b⟩) p.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quot_mk.comp (regularPeriodTranslation F n).continuous

public theorem invariantPeriodRealTranslation_mk (n : IntegerPeriods)
    (hn : ∀ g : Delta, rhoLambda g n = n) (t : ℝ) (q : RegularTotalSpace F) :
    invariantPeriodRealTranslation F n hn (t,Quotient.mk _ q) =
      quotientProjection (M := RegularTotalSpace F) (G := Delta)
        (regularPeriodTranslation F n (t,q)) := rfl

public theorem regularPeriodTranslation_add_int (n : IntegerPeriods)
    (t : ℝ) (k : ℤ) (q : RegularTotalSpace F) :
    regularPeriodTranslation F n (t+k,q) = regularPeriodTranslation F n (t,q) := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [regularPeriodTranslation_mk, regularPeriodTranslation_mk]
    apply Quotient.sound
    change MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _ _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨(Multiplicative.ofAdd (k • n) : FamilyPeriodGroup (regularParameterMap F)), ?_⟩
    apply Prod.ext
    · rfl
    · change periodHom (regularParameterMap F p.1).1 (k • n) +
        (t • periodVector (regularParameterMap F p.1).1 n + p.2) = _
      rw [map_zsmul, add_smul]
      change k • periodVector (regularParameterMap F p.1).1 n + (t • periodVector _ n + p.2) = _
      rw [Int.cast_smul_eq_zsmul]
      abel

public theorem invariantPeriodRealTranslation_add_int (n : IntegerPeriods)
    (hn : ∀ g : Delta, rhoLambda g n = n) (t : ℝ) (k : ℤ) (q : PuncturedGlobalFamily F) :
    invariantPeriodRealTranslation F n hn (t+k,q) = invariantPeriodRealTranslation F n hn (t,q) := by
  induction q using Quotient.inductionOn with
  | _ q =>
    rw [invariantPeriodRealTranslation_mk, invariantPeriodRealTranslation_mk,
      regularPeriodTranslation_add_int]

public def invariantPeriodTranslationProjection :
    C(ℝ × PuncturedGlobalFamily F, UnitAddCircle × PuncturedGlobalFamily F) where
  toFun p := ((p.1 : UnitAddCircle),p.2)
  continuous_toFun := (AddCircle.continuous_mk' 1).prodMap continuous_id

public theorem invariantPeriodTranslationProjection_isQuotientMap :
    IsQuotientMap (invariantPeriodTranslationProjection F) :=
  (QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap

public theorem invariantPeriodRealTranslation_factors (n : IntegerPeriods)
    (hn : ∀ g : Delta, rhoLambda g n = n) :
    Function.FactorsThrough (invariantPeriodRealTranslation F n hn)
      (invariantPeriodTranslationProjection F) := by
  rintro ⟨t,b⟩ ⟨u,c⟩ h
  have hb : b = c := congrArg Prod.snd h
  subst c
  have ht : (t : UnitAddCircle) = (u : UnitAddCircle) := congrArg Prod.fst h
  have hz : ((t-u : ℝ) : UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,ht,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  have htu : t = u+k := by
    simp only [zsmul_eq_mul,mul_one] at hk
    linarith
  rw [htu,invariantPeriodRealTranslation_add_int]

public def invariantPeriodCircleTranslation (n : IntegerPeriods)
    (hn : ∀ g : Delta, rhoLambda g n = n) :
    C(UnitAddCircle × PuncturedGlobalFamily F, PuncturedGlobalFamily F) :=
  (invariantPeriodTranslationProjection_isQuotientMap F).lift
    (invariantPeriodRealTranslation F n hn) (invariantPeriodRealTranslation_factors F n hn)

public theorem invariantPeriodCircleTranslation_real (n : IntegerPeriods)
    (hn : ∀ g : Delta, rhoLambda g n = n) (t : ℝ) (q : PuncturedGlobalFamily F) :
    invariantPeriodCircleTranslation F n hn ((t : UnitAddCircle),q) =
      invariantPeriodRealTranslation F n hn (t,q) :=
  DFunLike.congr_fun ((invariantPeriodTranslationProjection_isQuotientMap F).lift_comp
    (invariantPeriodRealTranslation F n hn) (invariantPeriodRealTranslation_factors F n hn)) (t,q)

end SphereSixComplex.Geometry.GlobalTorusFamily
