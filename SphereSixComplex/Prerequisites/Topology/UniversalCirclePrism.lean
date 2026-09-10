module

public import SphereSixComplex.Prerequisites.Topology.SingularPrismSimplex
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
public import SphereSixComplex.Prerequisites.Topology.SingularPrismNaturality
public import SphereSixComplex.Prerequisites.Topology.ClosedPrismHomology
public import SphereSixComplex.Prerequisites.Topology.StandardTorusHomology
import all SphereSixComplex.Prerequisites.Topology.StandardTorusHomology

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SimplexCategory Simplicial MonoidalCategory
namespace SphereSixComplex
open StandardCircleHomologyLiftDegree StandardTorusHomology

private theorem intervalAdjunctionSimplex (n : SimplexCategory) (f : n ⟶ ⦋1⦌)
    (s : stdSimplex ℝ (Fin (n.len + 1))) :
    TopCat.I.toSSetObjEquiv (Opposite.op n)
      (SSet.stdSimplex.toSSetObjI.app (Opposite.op n)
        (SSet.stdSimplex.objEquiv.symm f)) s =
      TopCat.stdSimplexHomeomorphI (stdSimplex.map f s) := by
  simp only [SSet.stdSimplex.toSSetObjI, Adjunction.homEquiv_unit]
  change (((sSetTopAdj.unit.app (SSet.stdSimplex.obj ⦋1⦌)).app (Opposite.op n)
    (SSet.stdSimplex.objEquiv.symm f)).down ≫ SSet.stdSimplex.toTopObjIsoI.hom).hom (ULift.up s) = _
  rw [sSetTopAdj_unit_app_app_down]
  have hf : SSet.yonedaEquiv.symm (SSet.stdSimplex.objEquiv.symm f) = SSet.stdSimplex.map f := rfl
  rw [hf]
  change TopCat.stdSimplexHomeomorphI (⦋1⦌.toTopHomeo
    (SSet.toTop.map (SSet.stdSimplex.map f) (n.toTopHomeo.symm s))) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply]

public def universalCirclePrismBase : TopCat.of UnitAddCircle ⟶ TopCat.of (StdTorus 2) :=
  TopCat.ofHom ⟨fun x => ![0, x], by fun_prop⟩

public def universalCirclePrismHomotopy :
    TopCat.Homotopy universalCirclePrismBase universalCirclePrismBase where
  toFun p := ![((p.1 : ℝ) : UnitAddCircle), p.2]
  continuous_toFun := by fun_prop
  map_zero_left x := by ext i; fin_cases i <;> simp [universalCirclePrismBase]
  map_one_left x := by ext i; fin_cases i <;> simp [universalCirclePrismBase]

private theorem universalCirclePrism_component_zero :
    universalCirclePrismHomotopy.toSSet.toSimplicialObjectHomotopy.h 0
      (simplexIndex UnitAddCircle 1 (pathSimplex (unitCircleIntegerLoop 1))) =
      simplexIndex (StdTorus 2) 2 standardTwoTorusTriangleA := by
  apply ((TopCat.of (StdTorus 2)).toSSetObjEquiv (Opposite.op ⦋2⦌)).injective
  ext s : 1
  change universalCirclePrismHomotopy.h.hom
    (((TopCat.of UnitAddCircle) ⊗ TopCat.I).toSSetObjEquiv (Opposite.op ⦋2⦌)
      ((Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of UnitAddCircle) TopCat.I).app
        (Opposite.op ⦋2⦌)
        ((TopCat.toSSet.obj (TopCat.of UnitAddCircle)).σ 0
          (simplexIndex UnitAddCircle 1 (pathSimplex (unitCircleIntegerLoop 1))),
          SSet.stdSimplex.toSSetObjI.app (Opposite.op ⦋2⦌)
            (SSet.stdSimplex.objMk₁ (1 : Fin 4)))) s) = _
  rw [toSSet_product_simplex, TopCat.toSSetObjEquiv_σ_apply]
  simp only [SSet.stdSimplex.objMk₁, intervalAdjunctionSimplex]
  simp only [pathSimplex, unitCircleIntegerLoop, Int.cast_one, mul_one]
  change ![(((stdSimplex.map (fun j : Fin 3 => if j.castSucc < (1 : Fin 4) then (0 : Fin 2) else 1) s) 1 : ℝ) : UnitAddCircle),
    (((stdSimplex.map (Fin.predAbove (0 : Fin 2)) s) 1 : ℝ) : UnitAddCircle)] =
      ![((s 1 + s 2 : ℝ) : UnitAddCircle), ((s 2 : ℝ) : UnitAddCircle)]
  ext i
  fin_cases i
  · change ((FunOnFinite.linearMap ℝ ℝ (fun j : Fin 3 => if j.castSucc < (1 : Fin 4) then (0 : Fin 2) else 1) s.1 1 : ℝ) : UnitAddCircle) = _
    simp [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_three]
    rfl
  · change ((FunOnFinite.linearMap ℝ ℝ (Fin.predAbove (0 : Fin 2)) s.1 1 : ℝ) : UnitAddCircle) = _
    simp [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_three]
    rfl

private theorem universalCirclePrism_component_one :
    universalCirclePrismHomotopy.toSSet.toSimplicialObjectHomotopy.h 1
      (simplexIndex UnitAddCircle 1 (pathSimplex (unitCircleIntegerLoop 1))) =
      simplexIndex (StdTorus 2) 2 standardTwoTorusTriangleB := by
  apply ((TopCat.of (StdTorus 2)).toSSetObjEquiv (Opposite.op ⦋2⦌)).injective
  ext s : 1
  change universalCirclePrismHomotopy.h.hom
    (((TopCat.of UnitAddCircle) ⊗ TopCat.I).toSSetObjEquiv (Opposite.op ⦋2⦌)
      ((Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of UnitAddCircle) TopCat.I).app
        (Opposite.op ⦋2⦌)
        ((TopCat.toSSet.obj (TopCat.of UnitAddCircle)).σ 1
          (simplexIndex UnitAddCircle 1 (pathSimplex (unitCircleIntegerLoop 1))),
          SSet.stdSimplex.toSSetObjI.app (Opposite.op ⦋2⦌)
            (SSet.stdSimplex.objMk₁ (2 : Fin 4)))) s) = _
  rw [toSSet_product_simplex, TopCat.toSSetObjEquiv_σ_apply]
  simp only [SSet.stdSimplex.objMk₁, intervalAdjunctionSimplex]
  simp only [pathSimplex, unitCircleIntegerLoop, Int.cast_one, mul_one]
  change ![(((stdSimplex.map (fun j : Fin 3 => if j.castSucc < (2 : Fin 4) then (0 : Fin 2) else 1) s) 1 : ℝ) : UnitAddCircle),
    (((stdSimplex.map (Fin.predAbove (1 : Fin 2)) s) 1 : ℝ) : UnitAddCircle)] =
      ![((s 2 : ℝ) : UnitAddCircle), ((s 1 + s 2 : ℝ) : UnitAddCircle)]
  ext i
  fin_cases i
  · change ((FunOnFinite.linearMap ℝ ℝ (fun j : Fin 3 => if j.castSucc < (2 : Fin 4) then (0 : Fin 2) else 1) s.1 1 : ℝ) : UnitAddCircle) = _
    simp [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_three]
    rfl
  · change ((FunOnFinite.linearMap ℝ ℝ (Fin.predAbove (1 : Fin 2)) s.1 1 : ℝ) : UnitAddCircle) = _
    simp [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_three]
    rfl

private theorem universalCirclePrism_fundamentalCycle :
    (universalCirclePrismHomotopy.singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom 1 2
      (simplexChain UnitAddCircle 1 (pathSimplex (unitCircleIntegerLoop 1))) =
      -standardTwoTorusFundamentalCycle := by
  have h := sSetPrism_one_simplex universalCirclePrismHomotopy.toSSet
    (simplexIndex UnitAddCircle 1 (pathSimplex (unitCircleIntegerLoop 1)))
  rw [universalCirclePrism_component_zero, universalCirclePrism_component_one] at h
  have hh := ConcreteCategory.congr_hom h (1 : ℤ)
  change _ = simplexChain (StdTorus 2) 2 standardTwoTorusTriangleB -
    simplexChain (StdTorus 2) 2 standardTwoTorusTriangleA at hh
  exact hh.trans (by simp only [standardTwoTorusFundamentalCycle, neg_sub])

public def universalCirclePrismClass : IntegralSingularHomology 2 (StdTorus 2) :=
  closedPrismHomology (universalCirclePrismHomotopy.singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)) 0 (loopHomologyClass (unitCircleIntegerLoop 1))

private theorem universalCirclePrismClass_eq :
    universalCirclePrismClass = -standardTwoTorusFundamentalClass := by
  have h := closedPrismHomology_on_cycle
    (universalCirclePrismHomotopy.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ))
    0 (loopCycle (unitCircleIntegerLoop 1)) (loopCycle_isCycle _)
  have hc : loopCycle (unitCircleIntegerLoop 1) ≫
      (universalCirclePrismHomotopy.singularChainComplexFunctorObjMap
        (AddCommGrpCat.of ℤ)).hom 1 2 = -degreeTwoCycleMap standardTwoTorusFundamentalCycle := by
    apply AddCommGrpCat.int_hom_ext
    change (universalCirclePrismHomotopy.singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom 1 2 ((AddCommGrpCat.asHom (pathChain (unitCircleIntegerLoop 1))) 1) =
        -((AddCommGrpCat.asHom standardTwoTorusFundamentalCycle) 1)
    simpa only [AddCommGrpCat.asHom_hom_apply, one_zsmul, pathChain] using universalCirclePrism_fundamentalCycle
  have hl : (IntegralChains (StdTorus 2)).liftCycles
      (loopCycle (unitCircleIntegerLoop 1) ≫
        (universalCirclePrismHomotopy.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)).hom 1 2)
      1 (by simp) (closedPrism_cycle _ 0 _ (loopCycle_isCycle _)) =
      -(IntegralChains (StdTorus 2)).liftCycles
        (degreeTwoCycleMap standardTwoTorusFundamentalCycle) 1 (by simp)
        (degreeTwoCycleMap_isCycle _ standardTwoTorusFundamentalCycle_isCycle) := by
    apply (cancel_mono ((IntegralChains (StdTorus 2)).iCycles 2)).mp
    simp only [HomologicalComplex.liftCycles_i, Preadditive.neg_comp]
    erw [HomologicalComplex.liftCycles_i]
    exact hc
  have hh := ConcreteCategory.congr_hom h (1 : ℤ)
  change universalCirclePrismClass = _ at hh
  exact hh.trans (by
    change ((IntegralChains (StdTorus 2)).liftCycles (A := AddCommGrpCat.of ℤ) _ _ _ _ ≫ _) 1 = _
    erw [hl, Preadditive.neg_comp]
    rfl)

public theorem universalCirclePrismClass_generates
    (x : IntegralSingularHomology 2 (StdTorus 2)) :
    ∃ n : ℤ, x = n • universalCirclePrismClass := by
  refine ⟨-standardTwoTorusHomologyArea x, ?_⟩
  rw [universalCirclePrismClass_eq, neg_smul, smul_neg, neg_neg]
  exact standardTwoTorus_eq_area_smul_fundamentalClass x

public theorem universalCirclePrismClass_primitive :
    ∃ r : IntegralSingularHomology 2 (StdTorus 2) →+ ℤ,
      r universalCirclePrismClass = 1 := by
  refine ⟨-standardTwoTorusHomologyArea, ?_⟩
  rw [universalCirclePrismClass_eq]
  simp only [AddMonoidHom.neg_apply, map_neg, neg_neg,
    standardTwoTorusHomologyArea_fundamentalClass]

private theorem standardTwoTorus_eq_coordinate_smul_generator
    (x : IntegralSingularHomology 2 (StdTorus 2)) :
    x = (stdTorusHomologyTwo 2 x) standardTwoTorusDegreeTwoIndex •
      standardTwoTorusHomologyGenerator := by
  apply (stdTorusHomologyTwo 2).injective
  rw [map_zsmul]
  simp only [standardTwoTorusHomologyGenerator, AddEquiv.apply_symm_apply]
  funext i
  have hi : i = standardTwoTorusDegreeTwoIndex := by
    apply Fin.ext
    have h := i.isLt
    simp [stdTorusTwoRank] at h
    simpa [standardTwoTorusDegreeTwoIndex] using h
  subst i
  simp

public theorem universalCirclePrismClass_eq_generator_or_neg_generator :
    universalCirclePrismClass = standardTwoTorusHomologyGenerator ∨
      universalCirclePrismClass = -standardTwoTorusHomologyGenerator := by
  obtain ⟨r, hr⟩ := universalCirclePrismClass_primitive
  have hx := standardTwoTorus_eq_coordinate_smul_generator universalCirclePrismClass
  have hu : ((stdTorusHomologyTwo 2 universalCirclePrismClass) standardTwoTorusDegreeTwoIndex) *
      r standardTwoTorusHomologyGenerator = 1 := by
    have hh := congrArg r hx
    simpa only [map_zsmul, zsmul_eq_mul, Int.cast_id, hr] using hh.symm
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
  · exact Or.inl (by simpa [h] using hx)
  · exact Or.inr (by simpa [h] using hx)

open Topology.PositiveCircleCross Topology.CircleProductIdentityMappingTorus

public def circleSweepBase {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (sweep : C(UnitAddCircle × X, Y)) : TopCat.of X ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨fun x ↦ sweep (0, x), by fun_prop⟩

public def circleSweepHomotopy {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (sweep : C(UnitAddCircle × X, Y)) :
    TopCat.Homotopy (circleSweepBase sweep) (circleSweepBase sweep) where
  toFun p := sweep (((p.1 : ℝ) : UnitAddCircle), p.2)
  continuous_toFun := by fun_prop
  map_zero_left x := rfl
  map_one_left x := by
    change sweep (((1 : ℝ) : UnitAddCircle), x) = sweep (0, x)
    rw [AddCircle.coe_period]

public theorem universalCirclePrism_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (sweep : C(UnitAddCircle × X, Y)) (c : C(StdTorus 1, X)) :
    closedPrismHomology ((circleSweepHomotopy sweep).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0
      (integralSingularHomologyMap 1 c standardCircleHomologyGenerator) =
    integralSingularHomologyMap 2
      (sweep.comp ((circleProductMap c).comp
        ⟨circleProdStandardCircleHomeomorph.symm, circleProdStandardCircleHomeomorph.symm.continuous⟩)) universalCirclePrismClass := by
  let u : C(UnitAddCircle, X) := c.comp ⟨stdTorusOneHomeomorph.symm, stdTorusOneHomeomorph.symm.continuous⟩
  let v : C(StdTorus 2, Y) := sweep.comp ((circleProductMap c).comp
    ⟨circleProdStandardCircleHomeomorph.symm, circleProdStandardCircleHomeomorph.symm.continuous⟩)
  have hn := closedPrismHomology_naturality
    (universalCirclePrismHomotopy.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) 0
    ((circleSweepHomotopy sweep).singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ))
    (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom u))
    (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom v))
    (fun p q ↦ topologicalPrism_naturality universalCirclePrismHomotopy
      (circleSweepHomotopy sweep) (TopCat.ofHom u) (TopCat.ofHom v)
      (by
        ext p
        apply congrArg sweep
        apply Prod.ext
        · rfl
        · apply congrArg c
          ext i
          fin_cases i
          rfl) (AddCommGrpCat.of ℤ) p q)
  have hh := ConcreteCategory.congr_hom hn (loopHomologyClass (unitCircleIntegerLoop 1))
  change closedPrismHomology _ 0 (integralSingularHomologyMap 1 u _) =
    integralSingularHomologyMap 2 v universalCirclePrismClass at hh
  have hu : integralSingularHomologyMap 1 u (loopHomologyClass (unitCircleIntegerLoop 1)) =
      integralSingularHomologyMap 1 c standardCircleHomologyGenerator := by
    rw [show u = c.comp ⟨stdTorusOneHomeomorph.symm, stdTorusOneHomeomorph.symm.continuous⟩ from rfl,
      ← integralSingularHomologyMap_comp_wang,
      integralSingularHomologyMap_loopHomologyClass]
    rfl
  rw [hu] at hh
  exact hh

public theorem circleSweepPrism_eq_of_universal_sign
    (n : ℤ) (hn : universalCirclePrismClass = n • standardTwoTorusHomologyGenerator)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (sweep : C(UnitAddCircle × X, Y)) (c : C(StdTorus 1, X)) :
    closedPrismHomology ((circleSweepHomotopy sweep).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0
      (integralSingularHomologyMap 1 c standardCircleHomologyGenerator) =
    n • integralSingularHomologyMap 2 sweep
      (normalizedCircleCross 1 (integralSingularHomologyMap 1 c standardCircleHomologyGenerator)) := by
  rw [universalCirclePrism_naturality, hn, map_zsmul,
    ← positiveCircleCross_eq_normalized]
  congr 1
  rw [← integralSingularHomologyMap_comp_wang, ← integralSingularHomologyMap_comp_wang]
  rfl

public theorem circleSweepPrism_eq_on_homology_of_universal_sign
    (n : ℤ) (hn : universalCirclePrismClass = n • standardTwoTorusHomologyGenerator)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (sweep : C(UnitAddCircle × X, Y)) (x : IntegralSingularHomology 1 X) :
    closedPrismHomology ((circleSweepHomotopy sweep).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0 x =
    n • integralSingularHomologyMap 2 sweep (normalizedCircleCross 1 x) := by
  let b : X := Classical.choice inferInstance
  let H := Topology.FirstHurewiczProof.establishedFirstHurewiczData_proof X b
  obtain ⟨p, hp⟩ := Topology.EstablishedFirstHurewicz.loopClass_surjective (H.equiv.symm x)
  have hx : loopHomologyClass p = x := by
    rw [← H.equiv_loopClass, hp, H.equiv.apply_symm_apply]
  rw [← hx, ← pathCircleMap_homology p]
  exact circleSweepPrism_eq_of_universal_sign n hn sweep (pathCircleMap p)

public theorem exists_circleSweepPrism_uniform_sign :
    ∃ n : ℤ, (n = 1 ∨ n = -1) ∧
      ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
        (sweep : C(UnitAddCircle × X, Y)) (x : IntegralSingularHomology 1 X),
      closedPrismHomology ((circleSweepHomotopy sweep).singularChainComplexFunctorObjMap
        (AddCommGrpCat.of ℤ)) 0 x =
      n • integralSingularHomologyMap 2 sweep (normalizedCircleCross 1 x) := by
  rcases universalCirclePrismClass_eq_generator_or_neg_generator with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro X Y _ _ _ sweep x
    exact circleSweepPrism_eq_on_homology_of_universal_sign 1 (by simpa using h) sweep x
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro X Y _ _ _ sweep x
    exact circleSweepPrism_eq_on_homology_of_universal_sign (-1) (by simpa using h) sweep x

end SphereSixComplex
