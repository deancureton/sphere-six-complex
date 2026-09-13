module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CompactPhaseCorrection
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.CuspCollar

open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric

public theorem componentSupport_inclusion_eq_zeroCoordinates
    (a : ChartIndex) (z : RawCoordinates) :
    componentSupport constructedModel (inclusion a z) =
      (a2Triangle a.1 a.2) '' {i : Fin 3 | z i = 0} := by
  let _ := chartedSpace
  have hchart : inclusion a z ∈ (toricChart a).source := by
    rw [toricChart_source]
    exact Set.mem_range_self z
  ext v
  constructor
  · intro hv
    have hin : v ∈ Set.range (a2Triangle a.1 a.2) := by
      by_contra hn
      exact Set.disjoint_left.mp (otherCarrierCentralComponent_disjoint_chart a v hn) hv hchart
    obtain ⟨i, rfl⟩ := hin
    refine ⟨i, ?_, rfl⟩
    have hz := (carrierCentralComponent_in_chart a i _ hchart).mp hv
    simpa [toricChart_inclusion, rawToComplexModel] using hz
  · rintro ⟨i, hi, rfl⟩
    exact ⟨a, i, z, rfl, hi, rfl⟩

/-- A point on at least two toric components is a single coordinate-axis point in every
affine chart containing it. -/
public theorem exists_singleAxis_of_componentSupport_ncard_ge_two
    (a : ChartIndex) (z : RawCoordinates)
    (hz : 2 ≤ (componentSupport constructedModel (inclusion a z)).ncard) :
    ∃ j : Fin 3, z = singleAxis j (z j) := by
  by_cases h0 : z 0 = 0 <;> by_cases h1 : z 1 = 0 <;> by_cases h2 : z 2 = 0
  all_goals solve
    | refine ⟨0, ?_⟩; funext i; fin_cases i <;> simp_all [singleAxis]
    | refine ⟨1, ?_⟩; funext i; fin_cases i <;> simp_all [singleAxis]
    | refine ⟨2, ?_⟩; funext i; fin_cases i <;> simp_all [singleAxis]
    | have hs : {i : Fin 3 | z i = 0} = {0} := by
        ext i; fin_cases i <;> simp_all; done
      rw [componentSupport_inclusion_eq_zeroCoordinates, hs,
        Set.image_singleton, Set.ncard_singleton] at hz
      omega
    | have hs : {i : Fin 3 | z i = 0} = {1} := by
        ext i; fin_cases i <;> simp_all; done
      rw [componentSupport_inclusion_eq_zeroCoordinates, hs,
        Set.image_singleton, Set.ncard_singleton] at hz
      omega
    | have hs : {i : Fin 3 | z i = 0} = {2} := by
        ext i; fin_cases i <;> simp_all; done
      rw [componentSupport_inclusion_eq_zeroCoordinates, hs,
        Set.image_singleton, Set.ncard_singleton] at hz
      omega
    | have hs : {i : Fin 3 | z i = 0} = ∅ := by
        ext i; fin_cases i <;> simp_all
      rw [componentSupport_inclusion_eq_zeroCoordinates, hs, Set.image_empty, Set.ncard_empty] at hz
      omega

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem exists_actualCentral_deck_translate_singleAxis
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W)
    (a : ChartIndex) (j : Fin 3) (z : ℂ)
    (hp : (p.1.1 : Carrier) = inclusion a (singleAxis j z)) (v : ToricLattice) :
    ∃ (q : actualLocalCuspCentralSubMulAction W) (w : ℂ),
      Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
        (actualLocalCuspCentralSubMulAction W)) q = Quotient.mk _ p ∧
        (q.1.1 : Carrier) = inclusion (a.1, v) (singleAxis j w) := by
  let _ := actualLocalCuspQuotientAction W
  obtain ⟨lambda, hlambda⟩ := shearVector_surjective (v - a.2)
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let g := Multiplicative.ofAdd lambda
  let q : actualLocalCuspCentralSubMulAction W := g • p
  let c := CuspToricPhaseAction.phaseEmbedding (C.phase lambda (constructedModel.t p.1))
  refine ⟨q, torusChartCoordinates (a.1, v) c j * z, ?_, ?_⟩
  · apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) q p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨g, rfl⟩
  · have hchart : translateChartIndex lambda a = (a.1, v) := by
      simp [translateChartIndex, hlambda]
    change (((C.toCuspActionData (M := constructedModel)).psiMap lambda p.1).1 : Carrier) = _
    rw [← C.psiMap_eq_generic, C.psiMap_coe]
    change carrierTorusActionFun c (carrierFanShearFun lambda (p.1.1 : Carrier)) = _
    rw [hp, carrierFanShearFun_inclusion, hchart, carrierTorusActionFun_inclusion]
    congr 1
    funext i
    by_cases hi : i = j <;> simp [singleAxis, hi]

end SphereSixComplex.Geometry.CuspCollar

end
