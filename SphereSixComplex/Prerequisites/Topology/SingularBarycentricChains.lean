module

public import SphereSixComplex.Prerequisites.Topology.SingularExcision
public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision

/-!
# Low-dimensional barycentric fundamental chains

This file constructs the first actual components of the barycentric subdivision chain operator.
The construction starts from the vertex of `sd Δ[0]` represented by the singleton chain and
uses Yoneda naturality to associate a subdivided vertex to every vertex of a simplicial set.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace SphereSixComplex













section OneSimplex

/-- A specified nonempty finset in a linear order, regarded as a finite chain. -/
public noncomputable def nonemptyFiniteChainOfFinset
    {X : Type*} [LinearOrder X] (s : Finset X) (hs : s.Nonempty) :
    NonemptyFiniteChains X where
  finset := s
  nonempty := hs
  comparable a b := le_total a b

















end OneSimplex













end SphereSixComplex
