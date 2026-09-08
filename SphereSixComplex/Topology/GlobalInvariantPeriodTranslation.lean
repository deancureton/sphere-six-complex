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


end SphereSixComplex.Geometry.GlobalTorusFamily
