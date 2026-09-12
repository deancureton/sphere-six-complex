module

public import SphereSixComplex.Prerequisites.Topology.EstablishedFirstHurewicz

@[expose] public section
noncomputable section

namespace SphereSixComplex
open Hurewicz.Chains

public theorem Hurewicz.Chains.hurewiczPi1_surjective {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (b : X) : Function.Surjective (hurewiczPi1 b) := by
  intro a
  let e := Hurewicz.Chains.abelianizationComparison X b
  obtain ⟨p, hp⟩ := Hurewicz.loopClass_surjective (e.equiv.symm a.toAdd)
  refine ⟨Path.Homotopic.Quotient.mk p, ?_⟩
  apply Multiplicative.toAdd.injective
  change StandardCircleHomologyLiftDegree.loopHomologyClass p = a.toAdd
  rw [← e.equiv_loopClass p, hp, e.equiv.apply_symm_apply]

end SphereSixComplex
