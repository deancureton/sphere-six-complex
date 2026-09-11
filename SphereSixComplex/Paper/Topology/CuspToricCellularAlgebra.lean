module

public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberCWModel

/-!
# Cellular algebra of the cusp toric fibre

The source CW decomposition has two vertices, three edges joining them, four two-cells, two
three-cells, and one four-cell.  Its only nonzero cellular differential is the incidence map from
the three oriented edges to the two vertices.  This module proves the resulting integral algebra;
it does not identify these groups with the homology of the actual cusp fibre.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

/-- The cellular incidence map of three parallel oriented edges from the first vertex to the
second. -/
public def cuspToricCellularBoundaryOne : (Fin 3 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![-(x 0 + x 1 + x 2), x 0 + x 1 + x 2]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring



/-- With zero differential out of the four two-cells, cellular degree two is free of rank four. -/
public def cuspToricCellularDegreeTwoEquiv : (Fin 4 → ℤ) ≃+ (Fin 4 → ℤ) :=
  AddEquiv.refl _



end SphereSixComplex
