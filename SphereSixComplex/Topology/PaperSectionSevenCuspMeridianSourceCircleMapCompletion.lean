module

public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianProjectionNaturality
public import SphereSixComplex.Topology.StandardCircleHomologyLiftDegree
public import SphereSixComplex.Topology.PaperCuspGeometricSpecialization

/-!
# A circle map carrying the full cusp source character

The first real period coordinate is fixed by the cusp monodromy.  Twelve times that coordinate
therefore descends together with the mapping-torus phase to a genuine circle-valued map.  Its
formula on the clutching cylinder is exactly `t + 12 q₀`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix Topology
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open Geometry.GlobalTorusFamily Geometry.CuspRadialClutchingConstruction
open Geometry.EllipticFixedPointCriterion
open Periods TriangleGroup LatticeData

/-- Twelve times the first standard real-period coordinate on a cusp fibre. -/
public noncomputable def cuspFiberTwelveFirstCoordinate
    (x : PeriodDomain) : C(AdditiveTorus x.1, UnitAddCircle) :=
  (StandardCircleHomologyLiftDegree.unitCirclePowerMap 12).comp
    ((StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph :
      C(StandardTorusHomology.StdTorus 1, UnitAddCircle)).comp
      ((StandardTorusHomology.standardFourTorusCoordinateProjection 0).comp
        ⟨StandardTorusHomology.additiveTorusStdMap x.1 (fullRankDomain x),
          (StandardTorusHomology.additiveTorusStdHomeomorph x.1
            (fullRankDomain x)).continuous⟩))

public theorem cuspFiberTwelveFirstCoordinate_projection
    (x : PeriodDomain) (z : ComplexTwoSpace) :
    cuspFiberTwelveFirstCoordinate x (additiveTorusProjection x.1 z) =
      (12 : ℤ) • (((periodCoordinates x z 0 : ℝ)) : UnitAddCircle) :=
  rfl

/-- The first real period coordinate is fixed by the real cusp monodromy. -/
public theorem rhoLambdaReal_gZero_firstCoordinate (u : RealPeriods) :
    rhoLambdaReal g₀ u 0 = u 0 := by
  let lhs : RealPeriods →ₗ[ℝ] ℝ :=
    (LinearMap.proj 0).comp (rhoLambdaReal g₀).toLinearMap
  let rhs : RealPeriods →ₗ[ℝ] ℝ := LinearMap.proj 0
  have hmaps : lhs = rhs := by
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro i
    rw [← integerToReal_integralBasisVector]
    change rhoLambdaReal g₀ (integerToReal (integralBasisVector i)) 0 =
      integerToReal (integralBasisVector i) 0
    rw [rhoLambdaReal_integer, rhoLambda_g₀_apply]
    have h := congrFun (M₀_sub_mulVec (integralBasisVector i)) (0 : Fin 4)
    change (M₀ *ᵥ integralBasisVector i) 0 - integralBasisVector i 0 = 0 at h
    rw [sub_eq_zero] at h
    simp only [Geometry.ComplexTorus.integerToReal.eq_def]
    exact_mod_cast h
  exact DFunLike.congr_fun hmaps u

/-- The twelvefold first-coordinate character is exactly clutching invariant. -/
public theorem cuspFiberTwelveFirstCoordinate_clutching
    (x : PeriodDomain) (y : AdditiveTorus x.1) :
    cuspFiberTwelveFirstCoordinate x (cuspFiberClutching x y) =
      cuspFiberTwelveFirstCoordinate x y := by
  induction y using Quotient.inductionOn with
  | _ z =>
      change cuspFiberTwelveFirstCoordinate x
          (additiveTorusProjection x.1 (cuspFiberLift x z)) =
        cuspFiberTwelveFirstCoordinate x (additiveTorusProjection x.1 z)
      rw [cuspFiberTwelveFirstCoordinate_projection,
        cuspFiberTwelveFirstCoordinate_projection]
      congr 2
      rw [cuspFiberLift_apply]
      unfold periodCoordinates
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact rhoLambdaReal_gZero_firstCoordinate ((fullRankDomain x).realEquiv.symm z)

/-- The cylinder formula respects the equivalence relation defining the cusp mapping torus. -/
public theorem cuspMeridianSourceCircleMap_respects
    (x : PeriodDomain) (p q : Unit × unitInterval × AdditiveTorus x.1)
    (h : finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ cuspFiberClutching x) p q) :
    ((p.2.1 : ℝ) : UnitAddCircle) + cuspFiberTwelveFirstCoordinate x p.2.2 =
      ((q.2.1 : ℝ) : UnitAddCircle) + cuspFiberTwelveFirstCoordinate x q.2.2 := by
  induction h with
  | rel a b hab =>
      rcases hab with hab | hab | hab
      · rw [hab.2]
      · rw [hab.1, hab.2.1, hab.2.2]
      · rw [hab.1, hab.2.1, hab.2.2, cuspFiberTwelveFirstCoordinate_clutching]
        simp
  | refl a => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

/-- The genuine circle-valued cusp source map with cylinder formula `t + 12 q₀`. -/
public noncomputable def cuspMeridianSourceCircleMap
    (x : PeriodDomain) :
    C(CircleMappingTorus (cuspFiberClutching x), UnitAddCircle) where
  toFun := Quotient.lift
    (fun p : Unit × unitInterval × AdditiveTorus x.1 ↦
      ((p.2.1 : ℝ) : UnitAddCircle) + cuspFiberTwelveFirstCoordinate x p.2.2)
    (cuspMeridianSourceCircleMap_respects x)
  continuous_toFun := by
    apply continuous_quot_lift (cuspMeridianSourceCircleMap_respects x)
    have hphase : Continuous (fun p : Unit × unitInterval × AdditiveTorus x.1 ↦
        ((p.2.1 : ℝ) : UnitAddCircle)) :=
      continuous_quotient_mk'.comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
    exact hphase.add ((cuspFiberTwelveFirstCoordinate x).continuous.comp
      (continuous_snd.comp continuous_snd))

@[simp]
public theorem cuspMeridianSourceCircleMap_cylinderProjection
    (x : PeriodDomain) (p : unitInterval × AdditiveTorus x.1) :
    cuspMeridianSourceCircleMap x
        (circleMappingTorusCylinderProjection (cuspFiberClutching x) p) =
      ((p.1 : ℝ) : UnitAddCircle) + cuspFiberTwelveFirstCoordinate x p.2 :=
  rfl

@[simp]
public theorem cuspMeridianSourceCircleMap_fiberInclusion
    (x : PeriodDomain) (y : AdditiveTorus x.1) :
    cuspMeridianSourceCircleMap x
        (finiteBouquetMappingTorusFiberInclusion
          (fun _ : Unit ↦ cuspFiberClutching x) y) =
      cuspFiberTwelveFirstCoordinate x y := by
  change (0 : UnitAddCircle) + cuspFiberTwelveFirstCoordinate x y = _
  rw [zero_add]

namespace Geometry.PaperAnalyticData

/-- The source circle map specialized to the actual cusp fibre and clutching datum. -/
public noncomputable def actualCuspMeridianSourceCircleMap (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, UnitAddCircle) :=
  cuspMeridianSourceCircleMap
    (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness))

end Geometry.PaperAnalyticData

end SphereSixComplex

end
