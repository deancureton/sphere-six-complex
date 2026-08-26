module

public import SphereSixComplex.Topology.CuspToricCellularHomologyBridge

/-!
# Vanishing singular homology in degrees carrying no cells

A CW complex has no homology in a degree with no cells, because its cellular chain group there is
already zero.  This is the dimension argument the Section 7 collar obligations reduce to: a space
built from cells of dimension at most five has no sixth homology, whatever its cells look like.

The cellular-to-singular comparison itself is the established
`EstablishedCellularHomology.integralCWCellularChainModel`; everything below is bookkeeping on top
of it.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

variable (Y : Type) [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]

/-- The cellular chain group of a degree carrying no cells is a zero object. -/
public theorem isZero_cellularChain_of_isEmpty_cell
    (M : IntegralCWCellularChainModel Y) (n : ℕ)
    [IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) n)] :
    IsZero (M.chainComplex.X n) := by
  have : Subsingleton (M.chainComplex.X n) := (M.cellBasis n).symm.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- A CW complex has no `n`-th integral singular homology once it has no `n`-cells. -/
public theorem subsingleton_integralSingularHomology_of_isEmpty_cell (n : ℕ)
    [IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) n)] :
    Subsingleton (IntegralSingularHomology n Y) := by
  obtain M := EstablishedCellularHomology.integralCWCellularChainModel Y
  have hcell : IsZero (M.chainComplex.homology n) :=
    (HomologicalComplex.ExactAt.of_isZero
      (isZero_cellularChain_of_isEmpty_cell Y M n)).isZero_homology
  have hiso : IsIso (M.chainComplex.homologyMap M.comparison n) := M.comparison_homology_isIso n
  have : IsZero ((IntegralSingularChainComplex Y).homology n) :=
    hcell.of_iso (asIso (M.chainComplex.homologyMap M.comparison n)).symm
  exact AddCommGrpCat.subsingleton_of_isZero this

/-- A space homeomorphic to a CW complex with no `n`-cells has no `n`-th integral singular
homology.  The collars of Section 7 are described analytically and only then identified with a
model, so the transported form is the one that gets used. -/
public theorem subsingleton_integralSingularHomology_of_homeomorph_cwComplex
    {Z : Type} [TopologicalSpace Z] (e : Z ≃ₜ Y) (n : ℕ)
    [IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) n)] :
    Subsingleton (IntegralSingularHomology n Z) :=
  ⟨fun _ _ => (integralSingularHomologyEquiv n e).injective
    (@Subsingleton.elim _ (subsingleton_integralSingularHomology_of_isEmpty_cell Y n) _ _)⟩

/-- A space carrying the standard `A₂` toric cell labelling has no integral singular homology
above degree four: that labelling has no cells there. -/
public theorem subsingleton_integralSingularHomology_of_labelledA2Cells
    (e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n)
    (n : ℕ) (hn : 4 < n) :
    Subsingleton (IntegralSingularHomology n Y) :=
  letI : IsEmpty (cuspWCellIndex n) := cuspWCellIndex_isEmpty n hn
  letI : IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) n) := Function.isEmpty (e n)
  subsingleton_integralSingularHomology_of_isEmpty_cell Y n

end SphereSixComplex

end

end
