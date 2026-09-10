module

public import SphereSixComplex.Prerequisites.Topology.CellularChainModel

@[expose] public section
noncomputable section
open CategoryTheory
namespace SphereSixComplex

/-- Integer cellular chains in degree `n`, indexed by the cells of a classical CW complex. -/
public abbrev IntegralCWCellularChains
    (Y : Type) [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)] (n : ℕ) :=
  Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ

/-- A candidate cellular boundary in the cell basis.  Geometrically, its coefficients should
be the degrees of the collapsed characteristic attaching maps. -/
public abbrev IntegralCWCellularBoundaryCandidate
    (Y : Type) [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)] :=
  (n : ℕ) → IntegralCWCellularChains Y (n + 1) →+ IntegralCWCellularChains Y n

/-- Compatibility between a cellular-homology model and a candidate attaching-incidence
boundary.  This is independent of any particular finite cell labelling. -/
public structure IntegralCWCellularBoundaryCompatibility
    {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
    (M : IntegralCWCellularHomologyModel Y)
    (boundary : IntegralCWCellularBoundaryCandidate Y) : Prop where
  boundary_eq : ∀ (n : ℕ) (x : IntegralCWCellularChains Y (n + 1)),
    ConcreteCategory.hom (M.chainComplex.d (n + 1) n) (M.cellBasis (n + 1) x) =
      M.cellBasis n (boundary n x)

namespace IntegralCWCellularBoundaryCompatibility

variable {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
  {M : IntegralCWCellularHomologyModel Y}
  {boundary : IntegralCWCellularBoundaryCandidate Y}

/-- Any boundary compatible with a genuine chain complex squares to zero. -/
public theorem boundary_comp_zero
    (C : IntegralCWCellularBoundaryCompatibility M boundary)
    (n : ℕ) (x : IntegralCWCellularChains Y (n + 2)) :
    boundary n (boundary (n + 1) x) = 0 := by
  apply (M.cellBasis n).injective
  rw [map_zero, ← C.boundary_eq]
  rw [← C.boundary_eq]
  have h := ConcreteCategory.congr_hom
    (M.chainComplex.d_comp_d (n + 2) (n + 1) n) (M.cellBasis (n + 2) x)
  rw [AddCommGrpCat.comp_apply] at h
  rw [h]
  rfl

/-- Compatibility is equivalently equality of the differential after conjugating by the cell
bases. -/
public theorem boundary_eq_conjugated
    (C : IntegralCWCellularBoundaryCompatibility M boundary) (n : ℕ) :
    (M.cellBasis n).symm.toAddMonoidHom.comp
        ((ConcreteCategory.hom (M.chainComplex.d (n + 1) n)).comp
          (M.cellBasis (n + 1)).toAddMonoidHom) = boundary n := by
  apply AddMonoidHom.ext
  intro x
  change (M.cellBasis n).symm
    (ConcreteCategory.hom (M.chainComplex.d (n + 1) n) (M.cellBasis (n + 1) x)) =
      boundary n x
  rw [C.boundary_eq, AddEquiv.symm_apply_apply]

end IntegralCWCellularBoundaryCompatibility

end SphereSixComplex
