module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepEdgeEvaluation
public import SphereSixComplex.Paper.Topology.CuspMixedTorusCellularSweeps
public import SphereSixComplex.Paper.Topology.CuspPhaseSweepFillingCoordinates
public import SphereSixComplex.Paper.Topology.PhaseSweepSkeletalHomology
public import SphereSixComplex.Paper.Topology.CuspPhaseSweepGraphCoordinates
public import SphereSixComplex.Paper.Topology.CuspCentralNormalizedSweepComparison

@[expose] public section
noncomputable section
open CategoryTheory HomologicalComplex Matrix
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex SphereSixComplex.Periods StandardCircleHomologyLiftDegree
open CuspFilling CuspPeriodExpansion InfiniteA2Toric
open InfiniteA2Toric InfiniteA2Toric.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def phaseSweepRelativeEdgeVector
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (j : Fin 2) (k : Fin 3) : Fin 4 → ℤ := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  exact fun l : Fin 4 ↦ (T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm
    (closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W j) 0
      (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single k 1))) l

theorem phaseSweepRelativeEdgeVector_active
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (k : Fin 3) :
    ∃ u : ℤ, (u = 1 ∨ u = -1) ∧
      phaseSweepRelativeEdgeVector W T (phaseSweepPeriod k) k =
        Pi.single (phaseSweepCellIndex k) u := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  obtain ⟨u, hu, h⟩ := phaseSweepRelativePrism_edge_unit T W k
  refine ⟨u, hu, ?_⟩
  ext j
  change ((T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm
    (closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W (phaseSweepPeriod k)) 0
      (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single k 1)))) j = _
  rw [h, map_zsmul, AddEquiv.symm_apply_apply]
  change u * (Finsupp.single (phaseSweepCellIndex k) (1 : ℤ)) j =
    (Pi.single (phaseSweepCellIndex k) u : Fin 4 → ℤ) j
  by_cases hj : j = phaseSweepCellIndex k
  · subst j
    simp
  · simp [Finsupp.single_eq_of_ne hj, Pi.single_eq_of_ne hj]

theorem phaseSweepRelativeEdgeVector_fixed
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (j : Fin 2) :
    phaseSweepRelativeEdgeVector W T j (if j = 0 then 2 else 1) = 0 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  ext k
  change ((T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm
    (closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W j) 0
      (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1
        (Finsupp.single (if j = 0 then (2 : Fin 3) else (1 : Fin 3)) 1)))) k = 0
  erw [phaseSweepRelativePrism_fixed_edge T W j, map_zero]
  rfl

theorem phaseSweepRelativeEdgeVector_edgeZero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) :
    phaseSweepRelativeEdgeVector W T 1 0 = phaseSweepRelativeEdgeVector W T 0 0 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  ext l
  exact congrArg (fun q : IntegralCWRelativeCellObject (ActualLocalCuspCentralOrbitQuotient W) 2 ↦
    (T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm q l)
      (phaseSweepRelativePrism_edgeZero_equal T W)

theorem phaseSweepRelativeEdgeVector_table
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) :
    ∃ a b c : ℤ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ (c = 1 ∨ c = -1) ∧
      phaseSweepRelativeEdgeVector W T 0 0 = ![0,a,0,0] ∧
      phaseSweepRelativeEdgeVector W T 1 0 = ![0,a,0,0] ∧
      phaseSweepRelativeEdgeVector W T 0 1 = ![0,0,b,0] ∧
      phaseSweepRelativeEdgeVector W T 1 1 = 0 ∧
      phaseSweepRelativeEdgeVector W T 0 2 = 0 ∧
      phaseSweepRelativeEdgeVector W T 1 2 = ![0,0,0,c] := by
  obtain ⟨a, ha, h0⟩ := phaseSweepRelativeEdgeVector_active W T 0
  obtain ⟨b, hb, h1⟩ := phaseSweepRelativeEdgeVector_active W T 1
  obtain ⟨c, hc, h2⟩ := phaseSweepRelativeEdgeVector_active W T 2
  have h0' : phaseSweepRelativeEdgeVector W T 0 0 = ![0,a,0,0] := by
    refine h0.trans ?_
    ext i
    fin_cases i <;> simp [phaseSweepCellIndex]
  have h1' : phaseSweepRelativeEdgeVector W T 0 1 = ![0,0,b,0] := by
    refine h1.trans ?_
    ext i
    fin_cases i <;> simp [phaseSweepCellIndex]
  have h2' : phaseSweepRelativeEdgeVector W T 1 2 = ![0,0,0,c] := by
    refine h2.trans ?_
    ext i
    fin_cases i <;> simp [phaseSweepCellIndex]
  exact ⟨a,b,c,ha,hb,hc,h0', (phaseSweepRelativeEdgeVector_edgeZero W T).trans h0', h1',
    phaseSweepRelativeEdgeVector_fixed W T 1, phaseSweepRelativeEdgeVector_fixed W T 0, h2'⟩

theorem phaseSweepFillingGraph_coordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (T : CellularHomology.IntegralComparison) (n : ℤ) (hn : n = 1 ∨ n = -1)
    (hgen : universalCirclePrismClass = n • StandardTorusHomology.standardTwoTorusHomologyGenerator)
    (i : Fin 2) (j k : Fin 3) :
    phaseSweepFillingHomologyTwoEquiv W R T
      (integralSingularHomologyMap 2 (cuspFillingPeriodCircle W i)
        (SphereSixComplex.Topology.CircleProductIdentityMappingTorus.normalizedCircleCross 1
          (loopHomologyClass (constructedCellularLoopInFilling W j k)))) =
      n • (phaseSweepRelativeEdgeVector W T i j - phaseSweepRelativeEdgeVector W T i k) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  have hg := phaseSweepGraphPrism_cellCoordinates W T i j k
  dsimp only at hg
  rw [phaseSweepCellularEdgeLoop_homologyToCentral] at hg
  have hs := constructedA2GraphPrism_normalized_of_sign n hgen W i j k
  dsimp only at hs
  have hh := congrArg (phaseSweepFillingHomologyTwoEquiv W R T) hs
  erw [phaseSweepFillingHomologyTwoEquiv_central, map_zsmul] at hh
  have he : phaseSweepRelativeEdgeVector W T i j - phaseSweepRelativeEdgeVector W T i k =
      n • phaseSweepFillingHomologyTwoEquiv W R T
        (integralSingularHomologyMap 2 (cuspFillingPeriodCircle W i)
          (SphereSixComplex.Topology.CircleProductIdentityMappingTorus.normalizedCircleCross 1
            (loopHomologyClass (constructedCellularLoopInFilling W j k)))) := by
    rw [← hh]
    refine Eq.trans ?_ hg.symm
    ext l
    change ((T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm
      (closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W i) 0
        (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single j 1)))) l -
      ((T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm
        (closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W i) 0
          (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single k 1)))) l = _
    erw [map_sub, map_sub, map_sub, Finsupp.sub_apply]
    rfl
  have hnn : n * n = 1 := by rcases hn with rfl | rfl <;> norm_num
  calc
    _ = n • (n • phaseSweepFillingHomologyTwoEquiv W R T
      (integralSingularHomologyMap 2 (cuspFillingPeriodCircle W i)
        (SphereSixComplex.Topology.CircleProductIdentityMappingTorus.normalizedCircleCross 1
          (loopHomologyClass (constructedCellularLoopInFilling W j k))))) := by
      rw [smul_smul, hnn, one_zsmul]
    _ = _ := congrArg (fun v ↦ n • v) he.symm

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Periods StandardCircleHomologyLiftDegree
open StandardTorusHomology CuspPuncturedCollarBridge CuspFilling CuspPeriodExpansion

local instance (A : PaperAnalyticData) :
    T2Space (ActualLocalCuspCentralOrbitQuotient A.starCuspWitness) := by
  let _ := actualLocalCuspFilling_t2 A.starCuspWitness
  exact (actualLocalCuspCentralOrbitMap_isEmbedding A.starCuspWitness).t2Space

def cuspMixedSourceColumn (A : PaperAnalyticData)
    (T : CellularHomology.IntegralComparison) (j : Fin 4) : Fin 4 → ℤ :=
  phaseSweepFillingHomologyTwoEquiv A.starCuspWitness A.cuspCentralFiberRetractionData T
    (integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling j)
      standardTwoTorusHomologyGenerator)

theorem cuspMixedSourceColumns_of_graphReadout (A : PaperAnalyticData)
    (T : CellularHomology.IntegralComparison) (n : ℤ) (hn : n = 1 ∨ n = -1)
    (hread : ∀ (i : Fin 2) (j k : Fin 3),
      phaseSweepFillingHomologyTwoEquiv A.starCuspWitness A.cuspCentralFiberRetractionData T
        (A.cuspFillingPhaseSweep i
          (loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness j k))) =
        n • (phaseSweepRelativeEdgeVector A.starCuspWitness T i j -
          phaseSweepRelativeEdgeVector A.starCuspWitness T i k)) :
    ∃ a b c : ℤ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ (c = 1 ∨ c = -1) ∧
      A.cuspMixedSourceColumn T 1 = ![0,a,0,-c] ∧
      A.cuspMixedSourceColumn T 2 = ![0,-a,b,0] ∧
      A.cuspMixedSourceColumn T 3 = ![0,a,0,0] := by
  obtain ⟨a,b,c,ha,hb,hc,h00,h10,h01,h11,h02,h12⟩ :=
    phaseSweepRelativeEdgeVector_table A.starCuspWitness T
  have hu (x : ℤ) (hx : x = 1 ∨ x = -1) : n * x = 1 ∨ n * x = -1 := by
    rcases hn with rfl | rfl <;> rcases hx with rfl | rfl <;> norm_num
  refine ⟨n*a,n*b,n*c,hu a ha,hu b hb,hu c hc,?_,?_,?_⟩
  · unfold cuspMixedSourceColumn
    rw [cuspMixedFourthTorus_cellularSweep, hread, h10, h12]
    ext l
    fin_cases l <;> simp
  · unfold cuspMixedSourceColumn
    rw [cuspMixedThirdSecondTorus_cellularSweeps, map_add, map_neg, hread, hread,
      h00, h02, h01]
    ext l
    fin_cases l <;> simp
  · unfold cuspMixedSourceColumn
    rw [cuspMixedThirdFirstTorus_cellularSweep, hread, h00, h02]
    ext l
    fin_cases l <;> simp

theorem cuspMixedSourceColumns (A : PaperAnalyticData)
    (T : CellularHomology.IntegralComparison) :
    ∃ a b c : ℤ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ (c = 1 ∨ c = -1) ∧
      A.cuspMixedSourceColumn T 1 = ![0,a,0,-c] ∧
      A.cuspMixedSourceColumn T 2 = ![0,-a,b,0] ∧
      A.cuspMixedSourceColumn T 3 = ![0,a,0,0] := by
  rcases universalCirclePrismClass_eq_generator_or_neg_generator with h | h
  · apply A.cuspMixedSourceColumns_of_graphReadout T 1 (Or.inl rfl)
    intro i j k
    exact phaseSweepFillingGraph_coordinates A.starCuspWitness A.cuspCentralFiberRetractionData
      T 1 (Or.inl rfl) (by simpa using h) i j k
  · apply A.cuspMixedSourceColumns_of_graphReadout T (-1) (Or.inr rfl)
    intro i j k
    exact phaseSweepFillingGraph_coordinates A.starCuspWitness A.cuspCentralFiberRetractionData
      T (-1) (Or.inr rfl) (by simpa using h) i j k

end SphereSixComplex.Geometry.PaperAnalyticData
