module

public import SphereSixComplex.Topology.SmoothRecognition
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible

/-!
# Discarding a contractible factor

The collars of the star are described as a radial interval times a mapping torus.  The interval
factor carries no homology of its own, so it can be dropped before any homology of the collar is
computed.  Both statements below are about an arbitrary contractible factor; the radial interval
is the instance that gets used.
-/

@[expose] public section

noncomputable section

open Set ContinuousMap

namespace SphereSixComplex

/-- A contractible factor can be discarded up to homotopy equivalence. -/
public theorem nonempty_homotopyEquiv_prod_of_contractible
    (C X : Type) [TopologicalSpace C] [TopologicalSpace X] [ContractibleSpace C] :
    Nonempty ((C × X) ≃ₕ X) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit C
  exact ⟨(e.prodCongr (ContinuousMap.HomotopyEquiv.refl X)).trans
    (Homeomorph.punitProd X).toHomotopyEquiv⟩

/-- Homology of a product with a contractible factor is the homology of the other factor. -/
public theorem subsingleton_homology_prod_of_contractible
    (C X : Type) [TopologicalSpace C] [TopologicalSpace X] [ContractibleSpace C] (n : ℕ)
    (h : Subsingleton (IntegralSingularHomology n X)) :
    Subsingleton (IntegralSingularHomology n (C × X)) := by
  obtain ⟨e⟩ := nonempty_homotopyEquiv_prod_of_contractible C X
  exact ⟨fun _ _ => (integralSingularHomologyEquivOfHomotopyEquiv n e).injective
    (Subsingleton.elim _ _)⟩

/-- An open real interval is contractible: it is convex and, being nonempty, not the empty
convex set.  This is the radial factor of the star's collars, written as the subtype the collar
realizations use. -/
public theorem contractibleSpace_openInterval {a b : ℝ} (h : a < b) :
    ContractibleSpace {x : ℝ // a < x ∧ x < b} := by
  have hne : ((a + b) / 2) ∈ Set.Ioo a b := by constructor <;> linarith
  exact (convex_Ioo a b).contractibleSpace ⟨_, hne⟩

end SphereSixComplex

end

end
