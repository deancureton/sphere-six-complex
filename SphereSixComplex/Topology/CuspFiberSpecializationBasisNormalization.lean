module

public import SphereSixComplex.Topology.PaperCuspGeometricSpecialization

/-!
# Basis-free cusp fibre specialization

The specialization matrix currently mixes two logically different facts: the fibre-coinvariant
part of specialization is an isomorphism, and the independently selected cellular homology
coordinates agree with that isomorphism.  This file separates them.  Once the target coordinates
are normalized through the specialization isomorphism, every matrix entry is formal.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low L C : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L] [AddCommGroup C]

/-- Target coordinates normalized by a bijective restriction to Wang coinvariants. -/
public noncomputable def normalizedTargetCoordinates
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (r : P.Coinvariants →ₗ[ℤ] L) (hr : Function.Bijective r)
    (c : P.Coinvariants ≃ₗ[ℤ] C) : L ≃ₗ[ℤ] C :=
  (LinearEquiv.ofBijective r hr).symm.trans c

/-- In normalized target coordinates, restriction to Wang coinvariants is the chosen
coinvariant coordinate equivalence. -/
public theorem normalizedTargetCoordinates_comp
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (r : P.Coinvariants →ₗ[ℤ] L) (hr : Function.Bijective r)
    (c : P.Coinvariants ≃ₗ[ℤ] C) :
    (normalizedTargetCoordinates P r hr c).toLinearMap.comp r = c.toLinearMap := by
  apply LinearMap.ext
  intro x
  change c ((LinearEquiv.ofBijective r hr).symm (r x)) = c x
  rw [LinearEquiv.ofBijective_symm_apply_apply]

/-- If a surjective map out of a Wang total group has kernel exactly one chosen invariant
section, then its restriction to coinvariants is bijective. -/
public theorem coinvariantsRestriction_bijective_of_kernel_eq_section
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (f : Total →ₗ[ℤ] L) (hf : Function.Surjective f)
    (hker : LinearMap.ker f = LinearMap.range S.lift) :
    Function.Bijective (f.comp P.coinvariantsToTotal) := by
  constructor
  · intro x y hxy
    change f (P.coinvariantsToTotal x) = f (P.coinvariantsToTotal y) at hxy
    have hdiff : f (P.coinvariantsToTotal (x - y)) = 0 := by
      rw [map_sub, map_sub, hxy, sub_self]
    have hix : P.coinvariantsToTotal (x - y) ∈ LinearMap.ker f :=
      LinearMap.mem_ker.mpr hdiff
    rw [hker] at hix
    obtain ⟨z, hz⟩ := hix
    have hz0 : z = 0 := by
      have hp := congrArg P.totalToInvariants hz
      rw [P.exact_coinvariantsToTotal_totalToInvariants.apply_apply_eq_zero] at hp
      have hs := DFunLike.congr_fun S.rightInverse z
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
      rw [hs] at hp
      exact hp
    have hxy0 : x - y = 0 := by
      apply P.coinvariantsToTotal_injective
      rw [← hz, hz0, map_zero]
      exact (P.coinvariantsToTotal.map_zero).symm
    exact sub_eq_zero.mp hxy0
  · intro y
    obtain ⟨t, ht⟩ := hf y
    let z := P.totalToInvariants t
    let t₀ := t - S.lift z
    have ht₀ : P.totalToInvariants t₀ = 0 := by
      change P.totalToInvariants (t - S.lift (P.totalToInvariants t)) = 0
      rw [map_sub]
      have hs := DFunLike.congr_fun S.rightInverse (P.totalToInvariants t)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
      rw [hs, sub_self]
    obtain ⟨x, hx⟩ := (P.exact_coinvariantsToTotal_totalToInvariants t₀).mp ht₀
    refine ⟨x, ?_⟩
    change f (P.coinvariantsToTotal x) = y
    rw [hx]
    change f (t - S.lift z) = y
    rw [map_sub, ht]
    have hsKer : S.lift z ∈ LinearMap.ker f := by
      rw [hker]
      exact ⟨z, rfl⟩
    rw [LinearMap.mem_ker.mp hsKer, sub_zero]

/-- If total specialization is onto, kills a Wang section, and source coinvariants and target
have the same finite free coordinates, then restriction to coinvariants is bijective. -/
public theorem coinvariantsRestriction_bijective_of_surjective_of_section_eq_zero
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (f : Total →ₗ[ℤ] L) (hf : Function.Surjective f)
    (hsection : f.comp S.lift = 0) [Module.Free ℤ C] [Module.Finite ℤ C]
    (cP : P.Coinvariants ≃ₗ[ℤ] C) (cL : L ≃ₗ[ℤ] C) :
    Function.Bijective (f.comp P.coinvariantsToTotal) := by
  let r := f.comp P.coinvariantsToTotal
  have hrSurjective : Function.Surjective r := by
    intro y
    obtain ⟨t, ht⟩ := hf y
    let z := P.totalToInvariants t
    let t₀ := t - S.lift z
    have ht₀ : P.totalToInvariants t₀ = 0 := by
      change P.totalToInvariants (t - S.lift (P.totalToInvariants t)) = 0
      rw [map_sub]
      have hs := DFunLike.congr_fun S.rightInverse (P.totalToInvariants t)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
      rw [hs, sub_self]
    obtain ⟨x, hx⟩ := (P.exact_coinvariantsToTotal_totalToInvariants t₀).mp ht₀
    refine ⟨x, ?_⟩
    change f (P.coinvariantsToTotal x) = y
    rw [hx]
    change f (t - S.lift z) = y
    rw [map_sub, ht]
    have hs := DFunLike.congr_fun hsection z
    change f (S.lift z) = 0 at hs
    rw [hs, sub_zero]
  let e : Module.End ℤ C :=
    cL.toLinearMap.comp (r.comp cP.symm.toLinearMap)
  have heSurjective : Function.Surjective e :=
    cL.surjective.comp (hrSurjective.comp cP.symm.surjective)
  have heInjective : Function.Injective e :=
    Module.End.injective_of_surjective ℤ C heSurjective
  refine ⟨?_, hrSurjective⟩
  intro x y hxy
  apply cP.injective
  apply heInjective
  have hex : e (cP x) = cL (r x) := by
    simp only [e, LinearMap.coe_comp, Function.comp_apply]
    have hs : cP.symm.toLinearMap (cP x) = x := cP.symm_apply_apply x
    rw [hs]
    rfl
  have hey : e (cP y) = cL (r y) := by
    simp only [e, LinearMap.coe_comp, Function.comp_apply]
    have hs : cP.symm.toLinearMap (cP y) = y := cP.symm_apply_apply y
    rw [hs]
    rfl
  rw [hex, hey]
  exact congrArg cL hxy

end WangHomologyPresentation

namespace Geometry.CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

/-- The basis-free degree-one map from the radial mapping torus to the cusp filling. -/
public noncomputable def rawDegreeOneTotalSpecialization
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    IntegralSingularHomology 1 (CircleMappingTorus G.clutching) →ₗ[ℤ]
      IntegralSingularHomology 1 (actualLocalCuspFilling W) := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1
    G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv
  exact ((integralSingularHomologyMap 1
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩).comp
        e.symm.toAddMonoidHom).toIntLinearMap

/-- The basis-free degree-two map from the radial mapping torus to the cusp filling. -/
public noncomputable def rawDegreeTwoTotalSpecialization
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    IntegralSingularHomology 2 (CircleMappingTorus G.clutching) →ₗ[ℤ]
      IntegralSingularHomology 2 (actualLocalCuspFilling W) := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2
    G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv
  exact ((integralSingularHomologyMap 2
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩).comp
        e.symm.toAddMonoidHom).toIntLinearMap

/-- The basis-free degree-one map from Wang coinvariants to the cusp filling. -/
public noncomputable def rawDegreeOneFiberSpecialization
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).Coinvariants →ₗ[ℤ]
      IntegralSingularHomology 1 (actualLocalCuspFilling W) := by
  let _ := G.fiberTopology
  exact (rawDegreeOneTotalSpecialization G).comp
    (circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal

/-- The basis-free degree-two map from Wang coinvariants to the cusp filling. -/
public noncomputable def rawDegreeTwoFiberSpecialization
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    (circleMappingTorusHTwoPresentation G.clutching).Coinvariants →ₗ[ℤ]
      IntegralSingularHomology 2 (actualLocalCuspFilling W) := by
  let _ := G.fiberTopology
  exact (rawDegreeTwoTotalSpecialization G).comp
    (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal

/-- The basis-free geometric content of the former twenty-entry specialization matrix. -/
public structure FiberCoinvariantSpecializationIsomorphisms
    (G : ActualCuspRadialClutchingData W) : Prop where
  degreeOne : Function.Bijective (rawDegreeOneFiberSpecialization G)
  degreeTwo : Function.Bijective (rawDegreeTwoFiberSpecialization G)

/-- Exactness formulation of the geometric specialization calculation: filling kills exactly
the invariant Wang section and no fibre-coinvariant class. -/
public structure TotalSpecializationExactness
    (G : ActualCuspRadialClutchingData W) : Prop where
  degreeOne_surjective : Function.Surjective (rawDegreeOneTotalSpecialization G)
  degreeOne_kernel :
    let _ := G.fiberTopology
    LinearMap.ker (rawDegreeOneTotalSpecialization G) =
      LinearMap.range
        (EstablishedCircleMappingTorusGeometricSections.sections
          G.monodromyCoordinates).degreeOne.lift
  degreeTwo_surjective : Function.Surjective (rawDegreeTwoTotalSpecialization G)
  degreeTwo_kernel :
    let _ := G.fiberTopology
    LinearMap.ker (rawDegreeTwoTotalSpecialization G) =
      LinearMap.range
      (EstablishedCircleMappingTorusGeometricSections.sections
          G.monodromyCoordinates).degreeTwo.lift

/-- A weaker and more geometric criterion: total specialization is onto and specified geometric
Wang sections vanish. Equal finite-free ranks then force the fibre restrictions to be
isomorphisms. -/
public structure TotalSpecializationSurjectivityAndSectionVanishing
    (G : ActualCuspRadialClutchingData W) : Prop where
  degreeOne_surjective : Function.Surjective (rawDegreeOneTotalSpecialization G)
  degreeOne_section :
    let _ := G.fiberTopology
    ∃ S : (circleMappingTorusHOnePresentation G.clutching).GeometricSection,
      (rawDegreeOneTotalSpecialization G).comp S.lift = 0
  degreeTwo_surjective : Function.Surjective (rawDegreeTwoTotalSpecialization G)
  degreeTwo_section :
    let _ := G.fiberTopology
    ∃ S : (circleMappingTorusHTwoPresentation G.clutching).GeometricSection,
      (rawDegreeTwoTotalSpecialization G).comp S.lift = 0

/-- Exactness of total specialization implies the two basis-free fibre specialization
isomorphisms. -/
public theorem fiberCoinvariantSpecializationIsomorphisms_of_totalExactness
    (G : ActualCuspRadialClutchingData W) (h : TotalSpecializationExactness G) :
    FiberCoinvariantSpecializationIsomorphisms G := by
  let _ := G.fiberTopology
  exact {
    degreeOne := WangHomologyPresentation.coinvariantsRestriction_bijective_of_kernel_eq_section
      (circleMappingTorusHOnePresentation G.clutching)
      (EstablishedCircleMappingTorusGeometricSections.sections
        G.monodromyCoordinates).degreeOne
      (rawDegreeOneTotalSpecialization G) h.degreeOne_surjective h.degreeOne_kernel
    degreeTwo := WangHomologyPresentation.coinvariantsRestriction_bijective_of_kernel_eq_section
      (circleMappingTorusHTwoPresentation G.clutching)
      (EstablishedCircleMappingTorusGeometricSections.sections
        G.monodromyCoordinates).degreeTwo
      (rawDegreeTwoTotalSpecialization G) h.degreeTwo_surjective h.degreeTwo_kernel
  }

/-- Surjectivity plus vanishing of the invariant Wang sections proves both basis-free
specialization isomorphisms. -/
public theorem fiberCoinvariantSpecializationIsomorphisms_of_surjective_of_section_eq_zero
    (G : ActualCuspRadialClutchingData W)
    (h : TotalSpecializationSurjectivityAndSectionVanishing G)
    (cOne : IntegralSingularHomology 1 (actualLocalCuspFilling W) ≃ₗ[ℤ] (Fin 2 → ℤ))
    (cTwo : IntegralSingularHomology 2 (actualLocalCuspFilling W) ≃ₗ[ℤ] (Fin 4 → ℤ)) :
    FiberCoinvariantSpecializationIsomorphisms G := by
  let _ := G.fiberTopology
  obtain ⟨SOne, hSOne⟩ := h.degreeOne_section
  obtain ⟨STwo, hSTwo⟩ := h.degreeTwo_section
  exact {
    degreeOne :=
      WangHomologyPresentation.coinvariantsRestriction_bijective_of_surjective_of_section_eq_zero
        (circleMappingTorusHOnePresentation G.clutching)
        SOne
        (rawDegreeOneTotalSpecialization G) h.degreeOne_surjective hSOne
        G.degreeOneCoinvariantsEquiv cOne
    degreeTwo :=
      WangHomologyPresentation.coinvariantsRestriction_bijective_of_surjective_of_section_eq_zero
        (circleMappingTorusHTwoPresentation G.clutching)
        STwo
        (rawDegreeTwoTotalSpecialization G) h.degreeTwo_surjective hSTwo
        G.degreeTwoCoinvariantsEquiv cTwo
  }

/-- Degree-one filling coordinates normalized by the fibre specialization isomorphism. -/
public noncomputable def normalizedCuspFillingHomologyOneEquiv
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) :
    IntegralSingularHomology 1 (actualLocalCuspFilling W) ≃+ (Fin 2 → ℤ) := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  exact (WangHomologyPresentation.normalizedTargetCoordinates P
    (rawDegreeOneFiberSpecialization G) h.degreeOne G.degreeOneCoinvariantsEquiv).toAddEquiv

/-- Degree-two filling coordinates normalized by the fibre specialization isomorphism. -/
public noncomputable def normalizedCuspFillingHomologyTwoEquiv
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) :
    IntegralSingularHomology 2 (actualLocalCuspFilling W) ≃+ (Fin 4 → ℤ) := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  exact (WangHomologyPresentation.normalizedTargetCoordinates P
    (rawDegreeTwoFiberSpecialization G) h.degreeTwo G.degreeTwoCoinvariantsEquiv).toAddEquiv

/-- Degree-one specialization written in its normalized target coordinates. -/
public noncomputable def normalizedDegreeOneTotalSpecialization
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) :
    let _ := G.fiberTopology
    IntegralSingularHomology 1 (CircleMappingTorus G.clutching) →ₗ[ℤ] (Fin 2 → ℤ) := by
  let _ := G.fiberTopology
  exact (normalizedCuspFillingHomologyOneEquiv G h).toIntLinearEquiv.toLinearMap.comp
    (rawDegreeOneTotalSpecialization G)

/-- Degree-two specialization written in its normalized target coordinates. -/
public noncomputable def normalizedDegreeTwoTotalSpecialization
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) :
    let _ := G.fiberTopology
    IntegralSingularHomology 2 (CircleMappingTorus G.clutching) →ₗ[ℤ] (Fin 4 → ℤ) := by
  let _ := G.fiberTopology
  exact (normalizedCuspFillingHomologyTwoEquiv G h).toIntLinearEquiv.toLinearMap.comp
    (rawDegreeTwoTotalSpecialization G)

/-- The normalized degree-one coordinates identify the raw fibre specialization with the
chosen coinvariant coordinates. -/
public theorem normalizedCuspFillingHomologyOneEquiv_rawFiberSpecialization
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) (x :
      let _ := G.fiberTopology
      (circleMappingTorusHOnePresentation G.clutching).Coinvariants) :
    normalizedCuspFillingHomologyOneEquiv G h (rawDegreeOneFiberSpecialization G x) =
      G.degreeOneCoinvariantsEquiv x := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  exact DFunLike.congr_fun
    (WangHomologyPresentation.normalizedTargetCoordinates_comp
      P (rawDegreeOneFiberSpecialization G) h.degreeOne G.degreeOneCoinvariantsEquiv) x

/-- The normalized degree-two coordinates identify the raw fibre specialization with the
chosen coinvariant coordinates. -/
public theorem normalizedCuspFillingHomologyTwoEquiv_rawFiberSpecialization
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) (x :
      let _ := G.fiberTopology
      (circleMappingTorusHTwoPresentation G.clutching).Coinvariants) :
    normalizedCuspFillingHomologyTwoEquiv G h (rawDegreeTwoFiberSpecialization G x) =
      G.degreeTwoCoinvariantsEquiv x := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  exact DFunLike.congr_fun
    (WangHomologyPresentation.normalizedTargetCoordinates_comp
      P (rawDegreeTwoFiberSpecialization G) h.degreeTwo G.degreeTwoCoinvariantsEquiv) x

/-- Normalized degree-one specialization restricts to the standard coinvariant coordinates. -/
public theorem normalizedDegreeOneTotalSpecialization_comp_coinvariantsToTotal
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) :
    let _ := G.fiberTopology
    (normalizedDegreeOneTotalSpecialization G h).comp
        (circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal =
      G.degreeOneCoinvariantsEquiv.toLinearMap := by
  let _ := G.fiberTopology
  apply LinearMap.ext
  intro x
  change normalizedCuspFillingHomologyOneEquiv G h
      (rawDegreeOneFiberSpecialization G x) = G.degreeOneCoinvariantsEquiv x
  exact normalizedCuspFillingHomologyOneEquiv_rawFiberSpecialization G h x

/-- Normalized degree-two specialization restricts to the standard coinvariant coordinates. -/
public theorem normalizedDegreeTwoTotalSpecialization_comp_coinvariantsToTotal
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) :
    let _ := G.fiberTopology
    (normalizedDegreeTwoTotalSpecialization G h).comp
        (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal =
      G.degreeTwoCoinvariantsEquiv.toLinearMap := by
  let _ := G.fiberTopology
  apply LinearMap.ext
  intro x
  change normalizedCuspFillingHomologyTwoEquiv G h
      (rawDegreeTwoFiberSpecialization G x) = G.degreeTwoCoinvariantsEquiv x
  exact normalizedCuspFillingHomologyTwoEquiv_rawFiberSpecialization G h x

/-- Wang sections normalized intrinsically by the basis-free filling specialization. -/
public noncomputable def normalizedGeometricWangSections
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) :
    let _ := G.fiberTopology
    CuspGeometricWangSections G.monodromyCoordinates := by
  let _ := G.fiberTopology
  let S := EstablishedCircleMappingTorusGeometricSections.sections G.monodromyCoordinates
  exact {
    degreeOne := UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel
      (circleMappingTorusHOnePresentation G.clutching) S.degreeOne
      G.degreeOneCoinvariantsEquiv (normalizedDegreeOneTotalSpecialization G h)
    degreeTwo := UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel
      (circleMappingTorusHTwoPresentation G.clutching) S.degreeTwo
      G.degreeTwoCoinvariantsEquiv (normalizedDegreeTwoTotalSpecialization G h)
  }

/-- In the intrinsically normalized Wang splitting, degree-one specialization is projection to
the first two coordinates. -/
public theorem normalizedDegreeOneTotalSpecialization_eq_projection
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) :
    let _ := G.fiberTopology
    (normalizedDegreeOneTotalSpecialization G h).toAddMonoidHom =
      EstablishedStandardA2CuspSpecialization.degreeOneFiberProjection.comp
          (normalizedGeometricWangSections G h).circleMappingTorusHOneAddEquiv.toAddMonoidHom := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  let S := EstablishedCircleMappingTorusGeometricSections.sections G.monodromyCoordinates
  let c := G.degreeOneCoinvariantsEquiv
  let f := normalizedDegreeOneTotalSpecialization G h
  apply AddMonoidHom.ext
  intro x
  have hx := UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel_map_eq_coinvariant
    P S.degreeOne c f
      (normalizedDegreeOneTotalSpecialization_comp_coinvariantsToTotal G h) x
  change f x = _
  rw [hx]
  unfold normalizedGeometricWangSections
  change c _ = EstablishedStandardA2CuspSpecialization.degreeOneFiberProjection
      (CircleMappingTorusHomologyBases.finTwoProdIntLinearEquiv (c _, _))
  funext i
  fin_cases i <;> rfl

/-- In the intrinsically normalized Wang splitting, degree-two specialization is projection to
the first four coordinates. -/
public theorem normalizedDegreeTwoTotalSpecialization_eq_projection
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) :
    let _ := G.fiberTopology
    (normalizedDegreeTwoTotalSpecialization G h).toAddMonoidHom =
      EstablishedStandardA2CuspSpecialization.degreeTwoFiberProjection.comp
          (normalizedGeometricWangSections G h).circleMappingTorusHTwoAddEquiv.toAddMonoidHom := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  let S := EstablishedCircleMappingTorusGeometricSections.sections G.monodromyCoordinates
  let c := G.degreeTwoCoinvariantsEquiv
  let f := normalizedDegreeTwoTotalSpecialization G h
  apply AddMonoidHom.ext
  intro x
  have hx := UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel_map_eq_coinvariant
    P S.degreeTwo c f
      (normalizedDegreeTwoTotalSpecialization_comp_coinvariantsToTotal G h) x
  change f x = _
  rw [hx]
  unfold normalizedGeometricWangSections
  change c _ = EstablishedStandardA2CuspSpecialization.degreeTwoFiberProjection
      (CircleMappingTorusHomologyBases.finFourProdFinTwoLinearEquiv (c _, _))
  funext i
  fin_cases i <;> rfl

/-- Every degree-one generator has the identity matrix in the normalized coordinates. -/
public theorem normalizedDegreeOneFiberGeneratorSpecialization
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) (j i : Fin 2) :
    normalizedCuspFillingHomologyOneEquiv G h
        (rawDegreeOneFiberSpecialization G
          (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))) i =
      (Pi.single j 1 : Fin 2 → ℤ) i := by
  simpa using congrFun
    (normalizedCuspFillingHomologyOneEquiv_rawFiberSpecialization G h
      (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))) i

/-- Every degree-two generator has the identity matrix in the normalized coordinates. -/
public theorem normalizedDegreeTwoFiberGeneratorSpecialization
    (G : ActualCuspRadialClutchingData W)
    (h : FiberCoinvariantSpecializationIsomorphisms G) (j i : Fin 4) :
    normalizedCuspFillingHomologyTwoEquiv G h
        (rawDegreeTwoFiberSpecialization G
          (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))) i =
      (Pi.single j 1 : Fin 4 → ℤ) i := by
  simpa using congrFun
    (normalizedCuspFillingHomologyTwoEquiv_rawFiberSpecialization G h
      (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))) i

end Geometry.CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization

end SphereSixComplex

end

end
