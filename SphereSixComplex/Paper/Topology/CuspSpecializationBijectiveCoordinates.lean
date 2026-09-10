module

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationTypes

@[expose] public section

noncomputable section
open AlgebraicTopology Matrix Topology
open scoped ContinuousMap
namespace SphereSixComplex

namespace WangHomologyPresentation
open Geometry.CuspPuncturedCollarBridge.UnnormalizedCuspRadialClutchingData
variable {HighRelations High Total LowRelations Low L : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]

def specializationSplitEquiv
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (f : Total →ₗ[ℤ] L)
    (h : Function.Bijective (f.comp P.coinvariantsToTotal)) :
    Total ≃ₗ[ℤ] L × P.Invariants :=
  let c := LinearEquiv.ofBijective (f.comp P.coinvariantsToTotal) h
  (P.totalLinearEquivCoinvariantsProdInvariantsOfSection
    (geometricSectionInMapKernel P S c f)).trans (c.prodCongr (LinearEquiv.refl ℤ _))

theorem specializationSplitEquiv_fst
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (f : Total →ₗ[ℤ] L)
    (h : Function.Bijective (f.comp P.coinvariantsToTotal)) (x : Total) :
    (specializationSplitEquiv P S f h x).1 = f x := by
  exact (geometricSectionInMapKernel_map_eq_coinvariant P S
    (LinearEquiv.ofBijective (f.comp P.coinvariantsToTotal) h) f rfl x).symm

theorem specializationSplitEquiv_snd
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (f : Total →ₗ[ℤ] L)
    (h : Function.Bijective (f.comp P.coinvariantsToTotal)) (x : Total) :
    (specializationSplitEquiv P S f h x).2 = P.totalToInvariants x := rfl

end WangHomologyPresentation

namespace CircleMappingTorusHomologyBases
open LatticeData LatticeWangAlgebra SphereSixComplex.Topology.PaperCuspSpecializationAlgebra
variable {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}

def specializationHTwoLinearEquiv
    (B : CuspMonodromyCoordinates phi) (S : CuspGeometricWangSections B)
    (f : IntegralSingularHomology 2 (CircleMappingTorus phi) →ₗ[ℤ] (Fin 4 → ℤ))
    (h : Function.Bijective (f.comp (circleMappingTorusHTwoPresentation phi).coinvariantsToTotal)) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  let inv := (invariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
    (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
    B.degreeOneDifference_conjugacy).trans mZeroInvariantsEquivIntSquared
  ((circleMappingTorusHTwoPresentation phi).specializationSplitEquiv S.degreeTwo f h).trans
    (((LinearEquiv.refl ℤ (Fin 4 → ℤ)).prodCongr inv).trans finFourProdFinTwoLinearEquiv)

theorem specializationHTwoLinearEquiv_first
    (B : CuspMonodromyCoordinates phi) (S : CuspGeometricWangSections B)
    (f : IntegralSingularHomology 2 (CircleMappingTorus phi) →ₗ[ℤ] (Fin 4 → ℤ))
    (h : Function.Bijective (f.comp (circleMappingTorusHTwoPresentation phi).coinvariantsToTotal))
    (x : IntegralSingularHomology 2 (CircleMappingTorus phi)) (i : Fin 4) :
    specializationHTwoLinearEquiv B S f h x (Fin.castAdd 2 i) = f x i := by
  have he := (circleMappingTorusHTwoPresentation phi).specializationSplitEquiv_fst S.degreeTwo f h x
  fin_cases i <;> exact congrFun he _

theorem specializationHTwoLinearEquiv_last
    (B : CuspMonodromyCoordinates phi) (S : CuspGeometricWangSections B)
    (f : IntegralSingularHomology 2 (CircleMappingTorus phi) →ₗ[ℤ] (Fin 4 → ℤ))
    (h : Function.Bijective (f.comp (circleMappingTorusHTwoPresentation phi).coinvariantsToTotal))
    (x : IntegralSingularHomology 2 (CircleMappingTorus phi)) (i : Fin 2) :
    specializationHTwoLinearEquiv B S f h x (Fin.natAdd 4 i) =
      S.circleMappingTorusHTwoLinearEquiv x (Fin.natAdd 4 i) := by
  fin_cases i <;> rfl

end CircleMappingTorusHomologyBases
namespace Geometry.PaperAnalyticData
open CuspPuncturedCollarBridge CircleMappingTorusHomologyBases

def CuspFiberSpecializationTwoBijective (A : PaperAnalyticData) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  Function.Bijective (G.specializationHomologyTwoMap.comp
    (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal)

def bijectiveCuspRawHomologyTwoEquiv (A : PaperAnalyticData)
    (h : A.CuspFiberSpecializationTwoBijective) :
    IntegralSingularHomology 2 (puncturedLocalCuspQuotient A.starCuspWitness) ≃+ (Fin 6 → ℤ) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv).trans
    (specializationHTwoLinearEquiv G.monodromyCoordinates G.geometricWangSections
      G.specializationHomologyTwoMap h).toAddEquiv

theorem bijectiveCuspRawHomologyTwoEquiv_last (A : PaperAnalyticData)
    (h : A.CuspFiberSpecializationTwoBijective)
    (x : IntegralSingularHomology 2 (puncturedLocalCuspQuotient A.starCuspWitness)) (i : Fin 2) :
    A.bijectiveCuspRawHomologyTwoEquiv h x (Fin.natAdd 4 i) =
      A.actualCuspRadialClutchingData.geometricHomologyTwoEquiv x (Fin.natAdd 4 i) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact specializationHTwoLinearEquiv_last G.monodromyCoordinates G.geometricWangSections
    G.specializationHomologyTwoMap h _ i

theorem bijectiveCuspRawHomologyTwoEquiv_first (A : PaperAnalyticData)
    (h : A.CuspFiberSpecializationTwoBijective)
    (x : IntegralSingularHomology 2 (puncturedLocalCuspQuotient A.starCuspWitness)) (i : Fin 4) :
    A.bijectiveCuspRawHomologyTwoEquiv h x (Fin.castAdd 2 i) =
      actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) i := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  have he := specializationHTwoLinearEquiv_first G.monodromyCoordinates G.geometricWangSections
    G.specializationHomologyTwoMap h (e x) i
  change A.bijectiveCuspRawHomologyTwoEquiv h x (Fin.castAdd 2 i) =
    actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
      (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData A.starCuspWitness)
      (integralSingularHomologyMap 2
        ⟨puncturedLocalCuspToFilling A.starCuspWitness,
          puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ (e.symm (e x))) i at he
  rw [e.symm_apply_apply] at he
  exact he

end Geometry.PaperAnalyticData
end SphereSixComplex
