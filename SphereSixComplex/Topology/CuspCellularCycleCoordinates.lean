module

public import SphereSixComplex.Topology.CuspToricCellularHomologyBridge
public import SphereSixComplex.Topology.CellularSkeletalComparison

@[expose] public section
noncomputable section
open CategoryTheory
namespace SphereSixComplex

public theorem cuspToricCellular_homologyOne_cycle
    (z : cuspToricCellularChainComplex.cycles 1) :
    cuspToricCellularChainComplex_homologyOneEquiv
        ((cuspToricCellularChainComplex.homologyπ 1).hom z) =
      fun i : Fin 2 ↦ (cuspToricCellularChainComplex.iCycles 1).hom z i.castSucc := by
  let K := cuspToricCellularChainComplex
  let S := K.sc' 2 1 0
  have hrange : AddMonoidHom.range S.abToCycles = ⊥ := by
    rw [AddMonoidHom.range_eq_bot_iff]
    ext x
    rfl
  let hi := (ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 2 1 (by omega))
  let hk := (ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 1 0 (by omega))
  change cuspToricCellularDegreeOneEquiv (QuotientAddGroup.quotientBot
    (QuotientAddGroup.quotientAddEquivOfEq hrange
      (((K.homologyIsoSc' 2 1 0 hi hk).hom ≫ S.abHomologyIso.hom).hom
        ((K.homologyπ 1).hom z)))) = _
  simp only [← ConcreteCategory.comp_apply, HomologicalComplex.π_homologyIsoSc'_hom_assoc]

  erw [show S.abHomologyIso = S.abLeftHomologyData.homologyIso from rfl,
    S.abLeftHomologyData.homologyπ_comp_homologyIso_hom]
  change cuspToricCellularDegreeOneEquiv
    (QuotientAddGroup.quotientBot (QuotientAddGroup.quotientAddEquivOfEq hrange
      (QuotientAddGroup.mk
        ((S.abCyclesIso.hom).hom ((K.cyclesIsoSc' 2 1 0 hi hk).hom.hom z))))) = _
  simp only [QuotientAddGroup.quotientAddEquivOfEq_mk]
  have h := ConcreteCategory.congr_hom
    (S.abLeftHomologyData.cyclesIso_hom_comp_i) ((K.cyclesIsoSc' 2 1 0 hi hk).hom.hom z)
  have h' := ConcreteCategory.congr_hom (K.cyclesIsoSc'_hom_iCycles 2 1 0 hi hk) z
  funext i
  fin_cases i <;>
    change ((S.abCyclesIso.hom).hom ((K.cyclesIsoSc' 2 1 0 hi hk).hom.hom z)).val _ = _
  · exact congrFun (h.trans h') (0 : Fin 3)
  · exact congrFun (h.trans h') (1 : Fin 3)

public theorem StandardA2ToricCellularIncidenceData.homology_cycle
    {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
    {e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n}
    {M : IntegralCWCellularHomologyModel Y}
    (I : StandardA2ToricCellularIncidenceData e M) (n : ℕ) (z : M.chainComplex.cycles n) :
    I.integralSingularHomologyEquiv n
      (M.homologyEquiv n ((M.chainComplex.homologyπ n).hom z)) =
      (cuspToricCellularChainComplex.homologyπ n).hom
        ((HomologicalComplex.cyclesMap I.chainIso.inv n).hom z) := by
  let w := (HomologicalComplex.cyclesMap I.chainIso.inv n).hom z
  let E := (asIso (HomologicalComplex.homologyMap I.chainIso.hom n)).addCommGroupIsoToAddEquiv
  change E.symm ((M.homologyEquiv n).symm
    (M.homologyEquiv n ((M.chainComplex.homologyπ n).hom z))) = _
  rw [AddEquiv.symm_apply_apply]
  apply E.injective
  rw [E.apply_symm_apply]
  change (M.chainComplex.homologyπ n).hom z =
    ((cuspToricCellularChainComplex.homologyπ n) ≫
      HomologicalComplex.homologyMap I.chainIso.hom n).hom w
  rw [HomologicalComplex.homologyπ_naturality]
  change (M.chainComplex.homologyπ n).hom z =
    (M.chainComplex.homologyπ n).hom ((HomologicalComplex.cyclesMap I.chainIso.hom n).hom w)
  apply congrArg (M.chainComplex.homologyπ n).hom
  change z = ((HomologicalComplex.cyclesMap I.chainIso.inv n) ≫
    HomologicalComplex.cyclesMap I.chainIso.hom n).hom z
  rw [← HomologicalComplex.cyclesMap_comp, I.chainIso.inv_hom_id,
    HomologicalComplex.cyclesMap_id]
  rfl

public theorem StandardA2ToricCellularIncidenceData.homologyOne_cycle
    {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
    {e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n}
    {M : IntegralCWCellularHomologyModel Y}
    (I : StandardA2ToricCellularIncidenceData e M) (z : M.chainComplex.cycles 1) :
    I.integralSingularHomologyOneEquiv
        (M.homologyEquiv 1 ((M.chainComplex.homologyπ 1).hom z)) =
      fun i : Fin 2 ↦ (labelledA2CellBasis e M 1).symm
        ((M.chainComplex.iCycles 1).hom z) i.castSucc := by
  let w := (HomologicalComplex.cyclesMap I.chainIso.inv 1).hom z
  have h := I.homology_cycle 1 z
  change cuspToricCellularChainComplex_homologyOneEquiv
    (I.integralSingularHomologyEquiv 1 _) = _
  rw [h, cuspToricCellular_homologyOne_cycle]
  have h' := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i I.chainIso.inv 1) z
  funext i
  exact congrFun h' i.castSucc

public theorem StandardA2ToricCellularIncidenceData.homologyOne_skeletal
    (T : IntegralCWCellularHomologyFoundation)
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]
    (e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n)
    (I : StandardA2ToricCellularIncidenceData e (T.objectwiseModel Y))
    (x : IntegralSingularHomology 1 (IntegralCWSkeletonLT Y 2)) :
    I.integralSingularHomologyOneEquiv
      ((HomologicalComplex.homologyMap
        (cwIntegralSingularChainMapObj (integralCWSkeletonToSpace Y 2)) 1).hom x) =
      fun i : Fin 2 ↦ (labelledA2CellBasis e (T.objectwiseModel Y) 1).symm
        ((HomologicalComplex.homologyMap
          (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion Y 1)) 1).hom x)
        i.castSucc := by
  rw [← T.homologyEquiv_skeletal_apply Y 1 x]
  let K := integralCWSkeletalChainComplex Y (integralCWRelativeBoundary_comp_self Y)
  let p : (CWIntegralSingularChainComplexObj (TopCat.of (IntegralCWSkeletonLT Y 2))).homology 1 ⟶ K.X 1 :=
    HomologicalComplex.homologyMap
    (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion Y 1)) 1
  let z := (K.liftCycles p ((ComplexShape.down ℕ).next 1) rfl (integralCWSkeletalProjection_cycle Y 1)).hom x
  change I.integralSingularHomologyOneEquiv
    ((T.objectwiseModel Y).homologyEquiv 1 ((K.homologyπ 1).hom z)) = _
  refine (I.homologyOne_cycle z).trans ?_
  have h := ConcreteCategory.congr_hom
    (K.liftCycles_i p ((ComplexShape.down ℕ).next 1) rfl (integralCWSkeletalProjection_cycle Y 1)) x
  funext i
  exact congrArg (fun a ↦ (labelledA2CellBasis e (T.objectwiseModel Y) 1).symm a i.castSucc) h

public theorem labelledA2CellBasis_symm_apply
    {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
    (e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n)
    (M : IntegralCWCellularHomologyModel Y) (n : ℕ) (x : M.chainComplex.X n)
    (i : cuspWCellIndex n) :
    (labelledA2CellBasis e M n).symm x i = (M.cellBasis n).symm x ((e n).symm i) := rfl

public theorem cuspToricCellular_homologyTwo_cycle
    (z : cuspToricCellularChainComplex.cycles 2) :
    cuspToricCellularChainComplex_homologyTwoEquiv
        ((cuspToricCellularChainComplex.homologyπ 2).hom z) =
      (cuspToricCellularChainComplex.iCycles 2).hom z := by
  let K := cuspToricCellularChainComplex
  let S := K.sc' 3 2 1
  have hf : S.f = 0 := rfl
  have hg : S.g = 0 := rfl
  let H := ShortComplex.HomologyData.ofZeros S hf hg
  let hi := (ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 3 2 (by omega))
  let hk := (ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 2 1 (by omega))
  change (((K.homologyIsoSc' 3 2 1 hi hk).hom ≫ H.left.homologyIso.hom).hom
    ((K.homologyπ 2).hom z)) = _
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    H.left.homologyπ_comp_homologyIso_hom]
  have h := ConcreteCategory.congr_hom H.left.cyclesIso_hom_comp_i
    ((K.cyclesIsoSc' 3 2 1 hi hk).hom.hom z)
  have h' := ConcreteCategory.congr_hom (K.cyclesIsoSc'_hom_iCycles 3 2 1 hi hk) z
  exact h.trans h'

public theorem StandardA2ToricCellularIncidenceData.homologyTwo_cycle
    {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
    {e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n}
    {M : IntegralCWCellularHomologyModel Y}
    (I : StandardA2ToricCellularIncidenceData e M) (z : M.chainComplex.cycles 2) :
    I.integralSingularHomologyTwoEquiv
        (M.homologyEquiv 2 ((M.chainComplex.homologyπ 2).hom z)) =
      (labelledA2CellBasis e M 2).symm ((M.chainComplex.iCycles 2).hom z) := by
  change cuspToricCellularChainComplex_homologyTwoEquiv
    (I.integralSingularHomologyEquiv 2 _) = _
  rw [I.homology_cycle, cuspToricCellular_homologyTwo_cycle]
  exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i I.chainIso.inv 2) z

public theorem StandardA2ToricCellularIncidenceData.homologyTwo_skeletal
    (T : IntegralCWCellularHomologyFoundation)
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]
    (e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n)
    (I : StandardA2ToricCellularIncidenceData e (T.objectwiseModel Y))
    (x : IntegralSingularHomology 2 (IntegralCWSkeletonLT Y 3)) :
    I.integralSingularHomologyTwoEquiv
      ((HomologicalComplex.homologyMap
        (cwIntegralSingularChainMapObj (integralCWSkeletonToSpace Y 3)) 2).hom x) =
      (labelledA2CellBasis e (T.objectwiseModel Y) 2).symm
        ((HomologicalComplex.homologyMap
          (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion Y 2)) 2).hom x) := by
  rw [← T.homologyEquiv_skeletal_apply Y 2 x]
  let K := integralCWSkeletalChainComplex Y (integralCWRelativeBoundary_comp_self Y)
  let p : (CWIntegralSingularChainComplexObj (TopCat.of (IntegralCWSkeletonLT Y 3))).homology 2 ⟶ K.X 2 :=
    HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion Y 2)) 2
  let z := (K.liftCycles p ((ComplexShape.down ℕ).next 2) rfl
    (integralCWSkeletalProjection_cycle Y 2)).hom x
  change I.integralSingularHomologyTwoEquiv
    ((T.objectwiseModel Y).homologyEquiv 2 ((K.homologyπ 2).hom z)) = _
  refine (I.homologyTwo_cycle z).trans ?_
  exact congrArg (labelledA2CellBasis e (T.objectwiseModel Y) 2).symm
    (ConcreteCategory.congr_hom
      (K.liftCycles_i p ((ComplexShape.down ℕ).next 2) rfl
        (integralCWSkeletalProjection_cycle Y 2)) x)

end SphereSixComplex
