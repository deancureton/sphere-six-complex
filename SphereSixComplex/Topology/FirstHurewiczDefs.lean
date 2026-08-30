module

public import SphereSixComplex.Topology.StandardCircleHomologyLiftDegree
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Definitions for the first Hurewicz theorem

Shared declarations used by both the chain-level proof and its downstream applications.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Topology.EstablishedFirstHurewicz

/-- The additive abelianization of the fundamental group of `X` at `b`. -/
public abbrev AbelianPi1 (X : Type) [TopologicalSpace X] (b : X) :=
  Additive (Abelianization (FundamentalGroup X b))

/-- The class in the abelianized fundamental group represented by a based loop. -/
public def loopClass {X : Type} [TopologicalSpace X] {b : X}
    (p : Path b b) : AbelianPi1 X b :=
  Additive.ofMul (Abelianization.of (Path.Homotopic.Quotient.mk p))

/-- Every class in the abelianized fundamental group is represented by a based loop. -/
public theorem loopClass_surjective {X : Type} [TopologicalSpace X] {b : X} :
    Function.Surjective (loopClass (b := b)) := by
  intro a
  obtain ⟨g, hg⟩ := Quotient.exists_rep a.toMul
  change Abelianization.of g = a.toMul at hg
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective g
  refine ⟨p, ?_⟩
  rw [loopClass, hp, hg]
  rfl

/-- The first Hurewicz equivalence, packaged with its canonical value on represented loops. -/
public structure FirstHurewiczData (X : Type) [TopologicalSpace X] (b : X) where
  equiv : AbelianPi1 X b ≃ₗ[ℤ] IntegralSingularHomology 1 X
  equiv_loopClass : ∀ p : Path b b,
    equiv (loopClass p) =
      StandardCircleHomologyLiftDegree.loopHomologyClass p

end SphereSixComplex.Topology.EstablishedFirstHurewicz
