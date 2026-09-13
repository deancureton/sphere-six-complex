module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralFiberHomology
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryHomology
public import SphereSixComplex.Paper.Topology.CuspCentralFillingHomologyComparison

/-! # Integral coordinates from the radial central-fiber attachment -/

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralFiberHomology
open SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def homologyTwoSplit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IntegralSingularHomology 2 (ActualLocalCuspCentralOrbitQuotient W) ≃+
      (IntegralSingularHomology 2 (centralBoundary W) × ℤ) :=
  (exists_homologyTwo_split W (1 / 3) (2 / 3)
    (by norm_num) (by norm_num) (by norm_num)).choose

private theorem homologyTwoSplit_boundaryInclusion
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (y : IntegralSingularHomology 2 (centralBoundary W)) :
    homologyTwoSplit W (integralSingularHomologyMap 2 (boundaryInclusion W) y) = (y, 0) :=
  (exists_homologyTwo_split W (1 / 3) (2 / 3)
    (by norm_num) (by norm_num) (by norm_num)).choose_spec y

/-- Coordinate zero is complementary to the boundary; the last three coordinates are its windings. -/
def homologyTwoEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IntegralSingularHomology 2 (ActualLocalCuspCentralOrbitQuotient W) ≃+ (Fin 4 → ℤ) :=
  (homologyTwoSplit W).trans
    (((CentralBoundary.actualHomologyTwoEquiv W).prodCongr (AddEquiv.refl ℤ)).trans
      (AddEquiv.prodComm.trans (Fin.consLinearEquiv ℤ (fun _ : Fin 4 ↦ ℤ)).toAddEquiv))

@[simp] theorem homologyTwoEquiv_boundaryInclusion
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (y : IntegralSingularHomology 2 (centralBoundary W)) :
    homologyTwoEquiv W
      (integralSingularHomologyMap 2 (boundaryInclusion W) y) =
      Fin.cons 0 (CentralBoundary.actualHomologyTwoEquiv W y) := by
  change (Fin.cons ((homologyTwoSplit W
      (integralSingularHomologyMap 2 (boundaryInclusion W) y)).2)
    (CentralBoundary.actualHomologyTwoEquiv W ((homologyTwoSplit W
      (integralSingularHomologyMap 2 (boundaryInclusion W) y)).1)) : Fin 4 → ℤ) = _
  rw [homologyTwoSplit_boundaryInclusion]

/-- Transport the attachment coordinates to the actual cusp filling. -/
def fillingHomologyTwoEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 2 (ActualLocalCuspFilling W) ≃+ (Fin 4 → ℤ) :=
  (actualCuspCentralOrbitFillingHomologyEquiv W R 2).symm.trans
    (homologyTwoEquiv W)

theorem fillingHomologyTwoEquiv_boundaryInclusion
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (y : IntegralSingularHomology 2 (centralBoundary W)) :
    fillingHomologyTwoEquiv W R
      (integralSingularHomologyMap 2
        ((⟨actualLocalCuspCentralOrbitMap W,
          (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩ : C(_, _)).comp
          (boundaryInclusion W)) y) =
      Fin.cons 0 (CentralBoundary.actualHomologyTwoEquiv W y) := by
  rw [← integralSingularHomologyMap_comp_wang,
    ← actualCuspCentralOrbitFillingHomologyEquiv_apply W R 2]
  change homologyTwoEquiv W
    ((actualCuspCentralOrbitFillingHomologyEquiv W R 2).symm
      (actualCuspCentralOrbitFillingHomologyEquiv W R 2 _)) = _
  rw [AddEquiv.symm_apply_apply, homologyTwoEquiv_boundaryInclusion]

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralFiberHomology
