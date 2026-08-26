module

public import SphereSixComplex.Topology.CellularDimensionVanishing
public import SphereSixComplex.Topology.SectionSevenLocalEulerModels

/-!
# Vanishing from a finite CW model's cell counts

A `FiniteCWModelSix` records a genuine CW structure on a homotopy-equivalent carrier, so a degree
whose cell count is zero carries no cells at all and hence no homology.  For a `FourTorusCellModel`
that is degrees five and six, which is exactly what the Section 7 collar obligation asks of a
four-torus fibre.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

variable {X : Type} [TopologicalSpace X]

/-- A degree with no cells in the chosen finite model carries no integral singular homology. -/
public theorem FiniteCWModelSix.subsingleton_homology_of_cellCount_eq_zero
    (M : FiniteCWModelSix X) (n : ℕ) (h : M.cellCount n = 0) :
    Subsingleton (IntegralSingularHomology n X) := by
  let _ := M.topology
  let _ := M.t2
  let _ := M.cwComplex
  let _ := M.finite
  have hfin : Finite (Topology.CWComplex.cell (Set.univ : Set M.Carrier) n) :=
    Topology.CWComplex.FiniteType.finite_cell (C := (Set.univ : Set M.Carrier)) n
  have hempty : IsEmpty (Topology.CWComplex.cell (Set.univ : Set M.Carrier) n) := by
    rcases Nat.card_eq_zero.mp h with hx | hx
    · exact hx
    · exact absurd hx (not_infinite_iff_finite.mpr hfin)
  have hcarrier : Subsingleton (IntegralSingularHomology n M.Carrier) :=
    subsingleton_integralSingularHomology_of_isEmpty_cell M.Carrier n
  exact ⟨fun _ _ => (integralSingularHomologyEquivOfHomotopyEquiv n M.homotopyEquiv).injective
    (Subsingleton.elim _ _)⟩

/-- A four-torus cell model has no fifth or sixth integral singular homology. -/
public theorem FourTorusCellModel.subsingleton_homology_five
    (M : FourTorusCellModel X) : Subsingleton (IntegralSingularHomology 5 X) :=
  M.toFiniteCWModelSix.subsingleton_homology_of_cellCount_eq_zero 5 M.cellsFive

/-- A four-torus cell model has no sixth integral singular homology. -/
public theorem FourTorusCellModel.subsingleton_homology_six
    (M : FourTorusCellModel X) : Subsingleton (IntegralSingularHomology 6 X) :=
  M.toFiniteCWModelSix.subsingleton_homology_of_cellCount_eq_zero 6 M.cellsSix

end SphereSixComplex

end

end
