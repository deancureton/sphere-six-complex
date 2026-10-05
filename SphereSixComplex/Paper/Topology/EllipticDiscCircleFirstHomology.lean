module

public import SphereSixComplex.Paper.Topology.EllipticDiscCircleRelation
public import SphereSixComplex.Paper.Topology.EllipticDiscPeriodHomology
public import SphereSixComplex.Paper.Topology.EllipticDiscCircleBase

@[expose] public section
noncomputable section
open scoped ContinuousMap
open SphereSixComplex.StandardCircleHomologyLiftDegree
namespace SphereSixComplex.Geometry.EllipticDiscCircle
open Hurewicz.Chains LatticeData AnalyticData ComplexTorus AnalyticTorusFamily GlobalTorusFamily

theorem orderThree_star_relation_of_base_homology (A : AnalyticData)
    {b : ComplexUnitDisc} (hb : (b : ℂ) ≠ 0) (p : Path b b)
    (hp : ∀ t, (p t : ℂ) ≠ 0) (c : C(unitInterval, ℂ)) (hc : c 1 = c 0 + 1)
    (hlog : ∀ t, Complex.exp ((2 * Real.pi * Complex.I) * c t) =
      (discBallScale A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one (p t)).val.val)
    (hbase : loopHomologyClass
      (((scaledPuncturedLoop A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one hb p hp).prod (Path.refl 0)).map
          (orderThreeProductToCentral A).continuous) =
        3 • hurewiczFunction A.cuspCentralBase A.geometricCentralRhoOne)
    (q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    3 • integralSingularHomologyMap 1 (centralInclusion A)
        (hurewiczFunction A.cuspCentralBase A.geometricCentralRhoOne) =
      -integralSingularHomologyMap 1 (centralInclusion A)
        (loopHomologyClass ((regularFamilyPeriodLoop A.periods q epsilon).map
          (regularFamilyQuotientMap A.periods).continuous)) := by
  let bp := scaledPuncturedLoop A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one hb p hp
  let z := (orderThreeSourceLoop A hb p hp).toContinuousMap
  let z₀ := A.modular.modularParameter.toTriangleUniformization.zOne
  let v := fixedGaugeLift A.periods z₀ z c epsilon 0
  let fc := orderThreeProductToCentral A
  let J := integralSingularHomologyMap 1 (centralInclusion A)
  have hs : 0 =
      J (loopHomologyClass (((Path.refl (scaledPuncturedPoint
        A.starSeparation.orderThree.radius_pos A.starSeparation.orderThree.radius_lt_one b hb)).prod
          (fixedPeriodLoop A.periods z₀ epsilon v)).map fc.continuous)) +
      J (loopHomologyClass ((bp.prod (Path.refl (Quotient.mk _ v))).map fc.continuous)) := by
    simpa only [J, fc, bp, v, z₀, z, integralSingularHomologyMap_loopHomologyClass,
      Path.map_map] using
      orderThree_disc_loop_homology_split A hb p hp c hc hlog
  rw [orderThreeProductToCentral_fixedPeriodLoop_homology A _ epsilon v q,
    baseLoop_homology_zeroFiber A.periods z₀ bp v fc, hbase, map_nsmul] at hs
  exact eq_neg_of_add_eq_zero_right hs.symm


theorem orderFour_star_relation_of_base_homology (A : AnalyticData)
    {b : ComplexUnitDisc} (hb : (b : ℂ) ≠ 0) (p : Path b b)
    (hp : ∀ t, (p t : ℂ) ≠ 0) (c : C(unitInterval, ℂ)) (hc : c 1 = c 0 + 1)
    (hlog : ∀ t, Complex.exp ((2 * Real.pi * Complex.I) * c t) =
      (discBallScale A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one (p t)).val.val)
    (hbase : loopHomologyClass
      (((scaledPuncturedLoop A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one hb p hp).prod (Path.refl 0)).map
          (orderFourProductToCentral A).continuous) =
        4 • hurewiczFunction A.cuspCentralBase A.geometricCentralRhoTwo)
    (q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    4 • integralSingularHomologyMap 1 (centralInclusion A)
        (hurewiczFunction A.cuspCentralBase A.geometricCentralRhoTwo) =
      -integralSingularHomologyMap 1 (centralInclusion A)
        (loopHomologyClass ((regularFamilyPeriodLoop A.periods q (-epsilon')).map
          (regularFamilyQuotientMap A.periods).continuous)) := by
  let bp := scaledPuncturedLoop A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one hb p hp
  let z := (orderFourSourceLoop A hb p hp).toContinuousMap
  let z₀ := A.modular.modularParameter.toTriangleUniformization.zTwo
  let v := fixedGaugeLift A.periods z₀ z c (-epsilon') 0
  let fc := orderFourProductToCentral A
  let J := integralSingularHomologyMap 1 (centralInclusion A)
  have hs : 0 =
      J (loopHomologyClass (((Path.refl (scaledPuncturedPoint
        A.starSeparation.orderFour.radius_pos A.starSeparation.orderFour.radius_lt_one b hb)).prod
          (fixedPeriodLoop A.periods z₀ (-epsilon') v)).map fc.continuous)) +
      J (loopHomologyClass ((bp.prod (Path.refl (Quotient.mk _ v))).map fc.continuous)) := by
    simpa only [J, fc, bp, v, z₀, z, integralSingularHomologyMap_loopHomologyClass,
      Path.map_map] using
      orderFour_disc_loop_homology_split A hb p hp c hc hlog
  rw [orderFourProductToCentral_fixedPeriodLoop_homology A _ (-epsilon') v q,
    baseLoop_homology_zeroFiber A.periods z₀ bp v fc, hbase, map_nsmul] at hs
  exact eq_neg_of_add_eq_zero_right hs.symm


theorem orderThree_star_homology_relation (A : AnalyticData)
    (q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    (3 : ℕ) • integralSingularHomologyMap 1 (centralInclusion A)
        (hurewiczFunction A.cuspCentralBase A.geometricCentralRhoOne) =
      -integralSingularHomologyMap 1 (centralInclusion A)
        (loopHomologyClass ((regularFamilyPeriodLoop A.periods q epsilon).map
          (regularFamilyQuotientMap A.periods).continuous)) := by
  obtain ⟨u, r, hr, hrR, hu, hune, hf, hb⟩ :=
    exists_orderThree_positive_factorization_radius A
  let hR := A.starSeparation.orderThree.radius_pos
  let hR1 := A.starSeparation.orderThree.radius_lt_one
  let p := smallDiscCircle hR r hr hrR
  let hp := smallDiscCircle_ne_zero hR r hr hrR
  exact orderThree_star_relation_of_base_homology A (hp 0) p hp
    (ComplexUnitDisc.circleLogScalar r) (ComplexUnitDisc.circleLogScalar_one r)
    (smallDiscCircle_log hR hR1 r hr hrR)
    (orderThree_smallDiscCircle_base_homology A u r hr hrR hu hune hf hb) q

theorem orderFour_star_homology_relation (A : AnalyticData)
    (q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    (4 : ℕ) • integralSingularHomologyMap 1 (centralInclusion A)
        (hurewiczFunction A.cuspCentralBase A.geometricCentralRhoTwo) =
      -integralSingularHomologyMap 1 (centralInclusion A)
        (loopHomologyClass ((regularFamilyPeriodLoop A.periods q (-epsilon')).map
          (regularFamilyQuotientMap A.periods).continuous)) := by
  obtain ⟨u, r, hr, hrR, hu, hune, hf, hb⟩ :=
    exists_orderFour_positive_factorization_radius A
  let hR := A.starSeparation.orderFour.radius_pos
  let hR1 := A.starSeparation.orderFour.radius_lt_one
  let p := smallDiscCircle hR r hr hrR
  let hp := smallDiscCircle_ne_zero hR r hr hrR
  exact orderFour_star_relation_of_base_homology A (hp 0) p hp
    (ComplexUnitDisc.circleLogScalar r) (ComplexUnitDisc.circleLogScalar_one r)
    (smallDiscCircle_log hR hR1 r hr hrR)
    (orderFour_smallDiscCircle_base_homology A u r hr hrR hu hune hf hb) q

end SphereSixComplex.Geometry.EllipticDiscCircle
