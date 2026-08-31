module

public import SphereSixComplex.Topology.PaperCuspFiniteFiberDegreeTwoKilledSection
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasis

/-!
# Explicit coordinate tori for the degree-two cusp specialization

The four degree-two fibre coinvariants are represented here by literal coordinate two-tori in
the marked period four-torus.  This reduces their specialization to four point-set maps into the
actual cusp filling, without invoking the established specialization matrix.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.StandardTorusHomology

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

namespace CuspFiberSpecializationNormalization

/-- The four retained pairs in the order used by `degreeTwoCoinvariantRepresentative`. -/
public def degreeTwoMarkedPairIndex : Fin 4 → Fin 6 := ![0, 2, 3, 1]

public theorem degreeTwoCoinvariantRepresentative_single (j : Fin 4) :
    ActualCuspRadialClutchingData.degreeTwoCoinvariantRepresentative (Pi.single j 1) =
      (Pi.single (degreeTwoMarkedPairIndex j) 1 : Fin 6 → ℤ) := by
  funext i
  fin_cases i <;> fin_cases j <;> rfl

/-- The literal coordinate two-torus representing a retained degree-two fibre coinvariant. -/
public def degreeTwoMarkedFiberCoordinateTorus
    (G : ActualCuspRadialClutchingData W) (j : Fin 4) :
    let _ := G.fiberTopology
    C(StandardTorusHomology.StdTorus 2, G.Fiber) := by
  let _ := G.fiberTopology
  exact (G.fiberHomeomorph.symm : C(AdditiveTorus G.fiberParameter, G.Fiber)).comp
    (((StandardTorusHomology.additiveTorusStdHomeomorph
      G.fiberParameter G.fiberFullRank).symm :
        C(StandardTorusHomology.StdTorus 4, AdditiveTorus G.fiberParameter)).comp
      (standardFourTorusCoordinateTwoTorus (degreeTwoMarkedPairIndex j)))

/-- The algebraically defined fibre generator is the fundamental class of its literal
coordinate two-torus. -/
public theorem degreeTwoFiberGenerator_eq_coordinateTorus
    (G : ActualCuspRadialClutchingData W) (j : Fin 4) :
    let _ := G.fiberTopology
    G.degreeTwoFiberGenerator j =
      integralSingularHomologyMap 2 (degreeTwoMarkedFiberCoordinateTorus G j)
        standardTwoTorusHomologyGenerator := by
  let _ := G.fiberTopology
  apply G.monodromyCoordinates.degreeTwo.injective
  rw [ActualCuspRadialClutchingData.degreeTwoFiberGenerator,
    G.monodromyCoordinates.degreeTwo.apply_symm_apply,
    ← G.fiberMarkingCompatibilityTwo]
  rw [degreeTwoCoinvariantRepresentative_single]
  let e := StandardTorusHomology.additiveTorusStdHomeomorph
    G.fiberParameter G.fiberFullRank
  have hfiber : (G.fiberHomeomorph : C(G.Fiber, AdditiveTorus G.fiberParameter)).comp
      (degreeTwoMarkedFiberCoordinateTorus G j) =
        (e.symm : C(StandardTorusHomology.StdTorus 4,
          AdditiveTorus G.fiberParameter)).comp
          (standardFourTorusCoordinateTwoTorus (degreeTwoMarkedPairIndex j)) := by
    ext z
    simp [degreeTwoMarkedFiberCoordinateTorus, e]
  rw [integralSingularHomologyMap_comp_wang, hfiber]
  rw [EstablishedTorusHomology.additiveTorusHomologyBasis_degreeTwo]
  change (Pi.single (degreeTwoMarkedPairIndex j) 1 : Fin 6 → ℤ) =
    standardFourTorusCoordinateTwoTorusHom
      (integralSingularHomologyMap 2
        (e : C(AdditiveTorus G.fiberParameter, StandardTorusHomology.StdTorus 4))
        (integralSingularHomologyMap 2
          ((e.symm : C(StandardTorusHomology.StdTorus 4,
            AdditiveTorus G.fiberParameter)).comp
            (standardFourTorusCoordinateTwoTorus (degreeTwoMarkedPairIndex j)))
          standardTwoTorusHomologyGenerator))
  rw [integralSingularHomologyMap_comp_wang]
  have he : (e : C(AdditiveTorus G.fiberParameter,
      StandardTorusHomology.StdTorus 4)).comp
      ((e.symm : C(StandardTorusHomology.StdTorus 4,
        AdditiveTorus G.fiberParameter)).comp
        (standardFourTorusCoordinateTwoTorus (degreeTwoMarkedPairIndex j))) =
      standardFourTorusCoordinateTwoTorus (degreeTwoMarkedPairIndex j) := by
    ext z
    simp [e]
  rw [he]
  exact (standardFourTorusCoordinateTwoTorusHom_coordinateHomologyClass _).symm

/-- The selected filling class corresponding to the `j`th labelled degree-two coordinate. -/
public noncomputable def degreeTwoCuspFillingCoordinateClass
    (G : ActualCuspRadialClutchingData W) (j : Fin 4) :
    IntegralSingularHomology 2 (actualLocalCuspFilling W) :=
  (degreeTwoCuspFillingCoordinates G).symm (Pi.single j 1)

/-- Point-set form of the remaining degree-two calculation: the four literal coordinate
two-tori have the four selected classes after inclusion into the cusp filling. -/
public def DegreeTwoMarkedCoordinateTorusImages
    (G : ActualCuspRadialClutchingData W) : Prop :=
  let _ := G.fiberTopology
  ∀ j : Fin 4,
    integralSingularHomologyMap 2
        (G.markedFiberToCuspFilling.comp (degreeTwoMarkedFiberCoordinateTorus G j))
        standardTwoTorusHomologyGenerator =
      degreeTwoCuspFillingCoordinateClass G j

/-- The residual basis-image assertion is exactly the four point-set coordinate-torus
equalities. -/
public theorem degreeTwoMarkedFiberBasisImages_iff_coordinateTorusImages
    (G : ActualCuspRadialClutchingData W) :
    DegreeTwoMarkedFiberBasisImages G ↔ DegreeTwoMarkedCoordinateTorusImages G := by
  let _ := G.fiberTopology
  constructor
  · intro h j
    calc
      integralSingularHomologyMap 2
          (G.markedFiberToCuspFilling.comp (degreeTwoMarkedFiberCoordinateTorus G j))
          standardTwoTorusHomologyGenerator =
        integralSingularHomologyMap 2 G.markedFiberToCuspFilling
          (integralSingularHomologyMap 2 (degreeTwoMarkedFiberCoordinateTorus G j)
            standardTwoTorusHomologyGenerator) := by
              rw [integralSingularHomologyMap_comp_wang]
      _ = integralSingularHomologyMap 2 G.markedFiberToCuspFilling
          (G.degreeTwoFiberGenerator j) := congrArg _
            (degreeTwoFiberGenerator_eq_coordinateTorus G j).symm
      _ = degreeTwoCuspFillingCoordinateClass G j := by
        apply (degreeTwoCuspFillingCoordinates G).injective
        rw [degreeTwoCuspFillingCoordinateClass,
          (degreeTwoCuspFillingCoordinates G).apply_symm_apply]
        exact h j
  · intro h j
    calc
      degreeTwoCuspFillingCoordinates G
          (integralSingularHomologyMap 2 G.markedFiberToCuspFilling
            (G.degreeTwoFiberGenerator j)) =
        degreeTwoCuspFillingCoordinates G
          (integralSingularHomologyMap 2 G.markedFiberToCuspFilling
            (integralSingularHomologyMap 2 (degreeTwoMarkedFiberCoordinateTorus G j)
              standardTwoTorusHomologyGenerator)) := congrArg _
                (congrArg (integralSingularHomologyMap 2 G.markedFiberToCuspFilling)
                  (degreeTwoFiberGenerator_eq_coordinateTorus G j))
      _ = degreeTwoCuspFillingCoordinates G
          (integralSingularHomologyMap 2
            (G.markedFiberToCuspFilling.comp (degreeTwoMarkedFiberCoordinateTorus G j))
            standardTwoTorusHomologyGenerator) := by
              rw [integralSingularHomologyMap_comp_wang]
      _ = degreeTwoCuspFillingCoordinates G
          (degreeTwoCuspFillingCoordinateClass G j) := congrArg _ (h j)
      _ = (Pi.single j 1 : Fin 4 → ℤ) := by
        rw [degreeTwoCuspFillingCoordinateClass,
          (degreeTwoCuspFillingCoordinates G).apply_symm_apply]

end CuspFiberSpecializationNormalization

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end

end
