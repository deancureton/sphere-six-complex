module

public import SphereSixComplex.Prerequisites.Topology.CellularChainModel

@[expose] public section
noncomputable section
namespace SphereSixComplex
variable (Y : Type) [TopologicalSpace Y] [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]

/-- A space homeomorphic to a CW complex with no `n`-cells has no `n`-th integral singular
homology.  The collars of Section 7 are described analytically and only then identified with a
model, so the transported form is the one that gets used. -/
public theorem subsingleton_integralSingularHomology_of_homeomorph_cwComplex
    {Z : Type} [TopologicalSpace Z] (e : Z ≃ₜ Y) (n : ℕ)
    [IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) n)] :
    Subsingleton (IntegralSingularHomology n Z) :=
  ⟨fun _ _ => (integralSingularHomologyEquiv n e).injective
    (@Subsingleton.elim _ (subsingleton_integralSingularHomology_of_isEmpty_cell Y n) _ _)⟩

end SphereSixComplex
end
end
