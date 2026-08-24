module

public import SphereSixComplex.Periods.Uniformization.SolutionGermModularDeck
import all SphereSixComplex.Periods.Uniformization.SolutionGermModularDeck

@[expose] public section

/-!
# A punctured-local criterion for global normalized-modular-J continuation

This file closes the global topology of the lifting problem.  It reduces deck transitivity of the
solution-germ étalé space to one local source statement: two representatives over the same point
must share a connected, frequently accumulating punctured neighbourhood on which their values
are ordinary.  Exact modular fibers choose one deck element at one point; covering uniqueness
makes that element constant, and the identity theorem fills the puncture.
-/

noncomputable section

namespace SphereSixComplex.Periods.NormalizedModularJContinuationCriterion

open Filter Set Topology UpperHalfPlane
open SphereSixComplex.TriangleGroup
open SolutionGermDeckTransitivity SolutionGermModularDeck
open TauCeti

variable {C f₀ : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}

/-- The precise source-local input needed to compare two modular solution germs over one point.
The set `V` is normally a small punctured coordinate disc. -/
def HasPuncturedRegularComparison
    (p q : ModularSolutionEtale C U) : Prop :=
  ∃ (V : Set ℂ) (w₀ : ℂ),
    IsPreconnected V ∧ w₀ ∈ V ∧
    ContinuousOn (solutionRepresentative p) V ∧
    ContinuousOn (solutionRepresentative q) V ∧
    (∀ w ∈ V,
      normalizedModularJCoordinate (solutionRepresentative p w) ∈
        modularRegularValueSet) ∧
    (∀ w ∈ V,
      normalizedModularJCoordinate (solutionRepresentative q w) ∈
        modularRegularValueSet) ∧
    (∀ w ∈ V,
      normalizedModularJCoordinate (solutionRepresentative p w) =
        normalizedModularJCoordinate (solutionRepresentative q w)) ∧
    (∃ᶠ w in 𝓝[≠] p.1.base, w ∈ V)

/-- Exact modular fibers and regular-covering uniqueness turn a punctured regular comparison into
a single modular deck element identifying the two solution germs. -/
theorem exists_modularSolutionDeckHomeomorph_eq
    (J : ExactNormalizedModularJUniformization)
    {p q : ModularSolutionEtale C U}
    (hbase : upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate C U p =
      upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate C U q)
    (hcompare : HasPuncturedRegularComparison p q) :
    ∃ g : Delta, modularSolutionDeckHomeomorph g p = q := by
  have hpqbase : p.1.base = q.1.base := congrArg Subtype.val hbase
  obtain ⟨V, w₀, hVpre, hw₀, hpcont, hqcont, hpreg, hqreg, heq, hfreq⟩ :=
    hcompare
  obtain ⟨g, hmatch⟩ := exists_delta_modularDeck_eq J (heq w₀ hw₀)
  have hpan : AnalyticAt ℂ (fun w ↦ (solutionRepresentative p w : ℂ)) p.1.base :=
    (HolomorphicPresheaf.analyticAt_repFun p.1).congr
      (solutionRepresentative_coe_eventuallyEq p).symm
  have hqan : AnalyticAt ℂ (fun w ↦ (solutionRepresentative q w : ℂ)) p.1.base := by
    rw [hpqbase]
    exact (HolomorphicPresheaf.analyticAt_repFun q.1).congr
      (solutionRepresentative_coe_eventuallyEq q).symm
  have hdeckeq := eventuallyEq_modularDeck_of_regular_covering_lifts
    J g hVpre hw₀ hpcont hqcont hpreg hqreg heq hmatch hfreq hpan hqan
  have hqrep : (fun w ↦ (solutionRepresentative q w : ℂ)) =ᶠ[𝓝 p.1.base]
      HolomorphicPresheaf.repFun q.1 := by
    rw [hpqbase]
    exact solutionRepresentative_coe_eventuallyEq q
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change modularDeckEtalePoint g p = q.1
  calc
    modularDeckEtalePoint g p =
        HolomorphicPresheaf.germPoint (modularTransformRepresentative g p) p.1.base := rfl
    _ = HolomorphicPresheaf.germPoint (HolomorphicPresheaf.repFun q.1) p.1.base :=
      HolomorphicPresheaf.germPoint_congr (hdeckeq.trans hqrep)
    _ = HolomorphicPresheaf.germPoint (HolomorphicPresheaf.repFun q.1) q.1.base := by
      rw [hpqbase]
    _ = q.1 := HolomorphicPresheaf.germPoint_repFun q.1

/-- The global relation-preserving continuation theorem obtained from local analytic solutions
and the punctured-regular comparison property.  All covering-space and monodromy topology is
discharged here; applications only need to build the local source neighbourhoods. -/
theorem continuesInsideWith_of_punctured_regular_comparison
    (J : ExactNormalizedModularJUniformization)
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hf₀ : AnalyticAt ℂ f₀ z₀)
    (hP₀ : IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate C z₀ f₀)
    (hlocal : ∀ z ∈ U, ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧
      IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate C z f)
    (hcompare : ∀ p q : ModularSolutionEtale C U,
      upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate C U p =
        upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate C U q →
      HasPuncturedRegularComparison p q) :
    ContinuesInsideWith f₀ U z₀
      (IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate C) := by
  apply UpperHalfPlaneSolutionEtale.continuesInsideWith_of_deck_transitive
    hU hz₀ hf₀ hP₀ hlocal
    (modularSolutionDeckHomeomorph : Delta →
      ModularSolutionEtale C U ≃ₜ ModularSolutionEtale C U)
  · exact fun g p ↦ modularSolutionDeck_base g p
  · intro p q hpq
    exact exists_modularSolutionDeckHomeomorph_eq J hpq (hcompare p q hpq)


end SphereSixComplex.Periods.NormalizedModularJContinuationCriterion
