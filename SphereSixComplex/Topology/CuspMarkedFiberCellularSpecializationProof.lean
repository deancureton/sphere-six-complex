module

public import SphereSixComplex.Topology.CuspFiniteFiberSpecializationMatrixProof

/-!
# The exact cellular comparison left by the marked cusp fibre

The marked-fibre specialization matrix is equivalent to two equalities of homomorphisms on the
Wang coinvariants.  This removes the choice of six generators from the residual and isolates the
missing compatibility between the marked period torus and the labelled cellular comparison.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Topology.PaperCuspSpecializationAlgebra
open WangHomologyPresentation

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

namespace ActualCuspRadialClutchingData

variable {W : ActualPuncturedCuspCollarWitness N M}

private theorem markedFiberToPuncturedCusp_homologyOne_eq_coinvariants
    (G : ActualCuspRadialClutchingData W)
    (x : let _ := G.fiberTopology; IntegralSingularHomology 1 G.Fiber) :
    let _ := G.fiberTopology
    let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
    e.symm
        ((circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal
          (Submodule.Quotient.mk x)) =
      integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp x := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
  let P := circleMappingTorusHOnePresentation G.clutching
  apply e.injective
  rw [e.apply_symm_apply]
  change P.coinvariantsToTotal (Submodule.Quotient.mk x) =
    integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun
      (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp x)
  rw [integralSingularHomologyMap_comp_wang]
  rw [G.totalHomotopyEquiv_comp_markedFiberToPuncturedCusp]
  rw [WangHomologyPresentation.coinvariantsToTotal, Submodule.liftQ_apply]
  rfl

private theorem markedFiberToPuncturedCusp_homologyTwo_eq_coinvariants
    (G : ActualCuspRadialClutchingData W)
    (x : let _ := G.fiberTopology; IntegralSingularHomology 2 G.Fiber) :
    let _ := G.fiberTopology
    let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
    e.symm
        ((circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal
          (Submodule.Quotient.mk x)) =
      integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp x := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let P := circleMappingTorusHTwoPresentation G.clutching
  apply e.injective
  rw [e.apply_symm_apply]
  change P.coinvariantsToTotal (Submodule.Quotient.mk x) =
    integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun
      (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp x)
  rw [integralSingularHomologyMap_comp_wang]
  rw [G.totalHomotopyEquiv_comp_markedFiberToPuncturedCusp]
  rw [WangHomologyPresentation.coinvariantsToTotal, Submodule.liftQ_apply]
  rfl

end ActualCuspRadialClutchingData

namespace EstablishedStandardA2CuspSpecialization

open Geometry.PaperAnalyticData

/-- Cellular specialization restricted to the degree-one Wang coinvariants. -/
public noncomputable def markedFiberCellularCoinvariantHomologyOneMap
    (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).Coinvariants →+
      cuspToricCellularChainComplex.homology 1 := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
  exact (standardA2CellularSpecializationHomologyMap A.starCuspWitness
    A.cuspCentralFiberRetractionData 1).comp
      (e.symm.toAddMonoidHom.comp
        (circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal.toAddMonoidHom)

/-- Cellular specialization restricted to the degree-two Wang coinvariants. -/
public noncomputable def markedFiberCellularCoinvariantHomologyTwoMap
    (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    (circleMappingTorusHTwoPresentation G.clutching).Coinvariants →+
      cuspToricCellularChainComplex.homology 2 := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  exact (standardA2CellularSpecializationHomologyMap A.starCuspWitness
    A.cuspCentralFiberRetractionData 2).comp
      (e.symm.toAddMonoidHom.comp
        (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal.toAddMonoidHom)

/-- The minimal cellular normalization left after all point-set and Wang algebra: the cellular
comparison carries the two coinvariant groups to the correspondingly labelled homology groups. -/
public structure MarkedFiberCellularCoinvariantNaturality (A : PaperAnalyticData) : Prop where
  degreeOne :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    cuspToricCellularChainComplex_homologyOneEquiv.toAddMonoidHom.comp
        (markedFiberCellularCoinvariantHomologyOneMap A) =
      G.degreeOneCoinvariantsEquiv.toAddMonoidHom
  degreeTwo :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    cuspToricCellularChainComplex_homologyTwoEquiv.toAddMonoidHom.comp
        (markedFiberCellularCoinvariantHomologyTwoMap A) =
      G.degreeTwoCoinvariantsEquiv.toAddMonoidHom

private theorem addMonoidHom_ext_of_equiv_pi_single_one
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (f g : G →+ H)
    (h : ∀ i, f (e.symm (Pi.single i 1)) = g (e.symm (Pi.single i 1))) :
    f = g := by
  apply AddMonoidHom.ext
  intro x
  let y := e x
  have hx : x = e.symm y := by simp [y]
  rw [hx]
  apply Pi.single_induction (M := fun _ : Fin n ↦ ℤ)
    (p := fun z ↦ f (e.symm z) = g (e.symm z)) y
  · simp
  · intro a b ha hb
    simpa using congrArg₂ (· + ·) ha hb
  · intro i z
    have hz : (Pi.single i z : Fin n → ℤ) =
        z • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      classical
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    calc
      f (e.symm (Pi.single i z)) =
          f (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by rw [hz]
      _ = z • f (e.symm (Pi.single i 1)) := by rw [map_zsmul, map_zsmul]
      _ = z • g (e.symm (Pi.single i 1)) := congrArg (z • ·) (h i)
      _ = g (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by rw [map_zsmul, map_zsmul]
      _ = g (e.symm (Pi.single i z)) := by rw [hz]

/-- The two coinvariant naturality squares imply the six marked-generator coefficients. -/
public theorem markedFiberCellularSpecializationMatrix_of_coinvariantNaturality
    (A : PaperAnalyticData) (h : MarkedFiberCellularCoinvariantNaturality A) :
    MarkedFiberCellularSpecializationMatrix A := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  constructor
  · intro j
    have hj := DFunLike.congr_fun h.degreeOne
      (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))
    change cuspToricCellularChainComplex_homologyOneEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 1
          ((integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv).symm
            ((circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal
              (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))))) =
        G.degreeOneCoinvariantsEquiv
          (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1)) at hj
    rw [G.degreeOneCoinvariantsEquiv.apply_symm_apply] at hj
    rw [G.degreeOneCoinvariantsEquiv_symm_single] at hj
    rw [G.markedFiberToPuncturedCusp_homologyOne_eq_coinvariants] at hj
    exact hj
  · intro j
    have hj := DFunLike.congr_fun h.degreeTwo
      (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))
    change cuspToricCellularChainComplex_homologyTwoEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 2
          ((integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv).symm
            ((circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal
              (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))))) =
        G.degreeTwoCoinvariantsEquiv
          (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1)) at hj
    rw [G.degreeTwoCoinvariantsEquiv.apply_symm_apply] at hj
    rw [G.degreeTwoCoinvariantsEquiv_symm_single] at hj
    rw [G.markedFiberToPuncturedCusp_homologyTwo_eq_coinvariants] at hj
    exact hj

/-- The six marked-generator coefficients determine both coinvariant naturality squares. -/
public theorem coinvariantNaturality_of_markedFiberCellularSpecializationMatrix
    (A : PaperAnalyticData) (h : MarkedFiberCellularSpecializationMatrix A) :
    MarkedFiberCellularCoinvariantNaturality A := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  constructor
  · apply addMonoidHom_ext_of_equiv_pi_single_one G.degreeOneCoinvariantsEquiv.toAddEquiv
    intro j
    change cuspToricCellularChainComplex_homologyOneEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 1
          ((integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv).symm
            ((circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal
              (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))))) =
        G.degreeOneCoinvariantsEquiv
          (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))
    rw [G.degreeOneCoinvariantsEquiv.apply_symm_apply]
    rw [G.degreeOneCoinvariantsEquiv_symm_single]
    rw [G.markedFiberToPuncturedCusp_homologyOne_eq_coinvariants]
    exact h.degreeOne j
  · apply addMonoidHom_ext_of_equiv_pi_single_one G.degreeTwoCoinvariantsEquiv.toAddEquiv
    intro j
    change cuspToricCellularChainComplex_homologyTwoEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 2
          ((integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv).symm
            ((circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal
              (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))))) =
        G.degreeTwoCoinvariantsEquiv
          (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))
    rw [G.degreeTwoCoinvariantsEquiv.apply_symm_apply]
    rw [G.degreeTwoCoinvariantsEquiv_symm_single]
    rw [G.markedFiberToPuncturedCusp_homologyTwo_eq_coinvariants]
    exact h.degreeTwo j

/-- The six generator equations are exactly the two labelled cellular naturality squares on
Wang coinvariants. -/
public theorem markedFiberCellularSpecializationMatrix_iff_coinvariantNaturality
    (A : PaperAnalyticData) :
    MarkedFiberCellularSpecializationMatrix A ↔
      MarkedFiberCellularCoinvariantNaturality A :=
  ⟨coinvariantNaturality_of_markedFiberCellularSpecializationMatrix A,
    markedFiberCellularSpecializationMatrix_of_coinvariantNaturality A⟩

end EstablishedStandardA2CuspSpecialization

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end

end
