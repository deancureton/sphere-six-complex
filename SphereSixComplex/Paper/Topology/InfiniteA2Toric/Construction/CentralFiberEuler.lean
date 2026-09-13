module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralFiberHigherHomology
public import SphereSixComplex.Paper.Topology.CuspCentralFillingHomologyComparison
public import SphereSixComplex.Paper.Topology.CuspDeckHomologyOne

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralFiberHomology
open SphereSixComplex.Periods CuspCollar CuspPeriodExpansion CuspFilling CuspLocalPhaseAction
open StandardTorusHomology

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

theorem finite_homology_and_euler_eq_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralHomologyFiniteSix (ActualLocalCuspCentralOrbitQuotient W) ∧
      integralHomologyEulerCharacteristicSix (ActualLocalCuspCentralOrbitQuotient W) = 2 := by
  let _ := actualLocalCuspQuotientAction W
  let _ : SimplyConnectedSpace (localCarrier constructedModel W.localWitness.radius) :=
    constructedModel.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
  let p : C(localCarrier constructedModel W.localWitness.radius, ActualLocalCuspFilling W) :=
    ⟨Quotient.mk _, continuous_quot_mk⟩
  have hp : IsQuotientCoveringMap p (Multiplicative ParameterLattice) :=
    W.localWitness.quotient_isQuotientCoveringMap
  let _ : PathConnectedSpace (ActualLocalCuspFilling W) :=
    hp.surjective.pathConnectedSpace hp.continuous
  let d : ℕ → ℕ := fun n => match n with
    | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 2 | 4 => 1 | _ => 0
  have he (n : ℕ) : Nonempty
      (IntegralSingularHomology n (ActualLocalCuspCentralOrbitQuotient W) ≃+ (Fin (d n) → ℤ)) := by
    rcases n with _ | _ | _ | _ | _ | n
    · exact ⟨((actualCuspCentralOrbitFillingHomologyEquiv W R 0).trans
        (pathConnectedIntegralHomologyZeroEquivInteger _)).trans intEquivFinOne⟩
    · exact ⟨(actualCuspCentralOrbitFillingHomologyEquiv W R 1).trans
        (actualCuspDeckHomologyOneEquiv W)⟩
    · obtain ⟨e, _⟩ := exists_homologyTwo_split
        W (1 / 3) (2 / 3) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨e.trans (((CentralBoundary.actualHomologyTwoEquiv W).prodCongr
        intEquivFinOne).trans (finArrowProdAddEquiv 3 1))⟩
    · exact exists_homologyThreeEquiv W (1 / 3) (2 / 3)
        (by norm_num) (by norm_num) (by norm_num)
    · obtain ⟨e⟩ := exists_higherHomologyEquiv W (1 / 3) (2 / 3)
        (by norm_num) (by norm_num) (by norm_num) 3 (by omega)
      exact ⟨e.trans (stdTorusHomology 3 3)⟩
    · let _ := subsingleton_homology W (1 / 3) (2 / 3)
        (by norm_num) (by norm_num) (by norm_num) (n + 5) (by omega)
      change Nonempty (IntegralSingularHomology (n + 5)
        (ActualLocalCuspCentralOrbitQuotient W) ≃+ (Fin 0 → ℤ))
      exact ⟨addEquivOfSubsingleton⟩
  have hf (n : ℕ) : Module.Finite ℤ
      (IntegralSingularHomology n (ActualLocalCuspCentralOrbitQuotient W)) := by
    obtain ⟨e⟩ := he n
    exact Module.Finite.equiv e.symm.toIntLinearEquiv
  have hr (n : ℕ) : Module.finrank ℤ
      (IntegralSingularHomology n (ActualLocalCuspCentralOrbitQuotient W)) = d n := by
    obtain ⟨e⟩ := he n
    rw [e.toIntLinearEquiv.finrank_eq]
    simp
  refine ⟨⟨hf, fun n hn => subsingleton_homology W (1 / 3) (2 / 3)
    (by norm_num) (by norm_num) (by norm_num) n (by omega)⟩, ?_⟩
  simp [integralHomologyEulerCharacteristicSix, hr, d]

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralFiberHomology
