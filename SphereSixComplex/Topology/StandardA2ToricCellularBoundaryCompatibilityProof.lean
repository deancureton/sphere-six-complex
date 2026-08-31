module

public import SphereSixComplex.Topology.StandardA2ToricCentralFiberIndependentIncidenceProof

/-!
# Cellular-boundary compatibility

Mathlib's CW API supplies characteristic maps and skeleta, but currently no cellular chain
complex or attaching-degree formula.  This file isolates the general algebraic compatibility
that a classical cellular-boundary construction must satisfy and proves its chain condition.
-/

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

/-- The full labelled boundary formula needed for the standard `A₂` atlas.  Unlike the
twenty-four-entry residual, this states the usual cellular-boundary theorem on every cellular
chain and in every degree. -/
public def StandardA2ToricCentralFiberSelectedBoundaryCompatibility
    {X : Type} [TopologicalSpace X] [T2Space X]
    (A : StandardA2ToricCentralFiberCellAtlas X) : Prop :=
  let D := A.toCWDecomposition
  let _ := D.topology
  let _ := D.cwComplex
  ∀ (n : ℕ) (x : cuspWCellIndex (n + 1) → ℤ),
    D.integralCellularChainModel.chainComplex.d (n + 1) n
        (D.labelledCellBasis (n + 1) x) =
      D.labelledCellBasis n (standardA2ToricCellularBoundary n x)

private theorem labelledCellBasis_coordinateBoundary
    {X : Type} [TopologicalSpace X]
    (D : StandardA2ToricCentralFiberCWDecomposition X) (n : ℕ)
    (x : cuspWCellIndex n.succ → ℤ) :
    let _ := D.topology
    let _ := D.cwComplex
    D.labelledCellBasis n (standardA2ToricCellularCoordinateBoundary D n x) =
      D.integralCellularChainModel.chainComplex.d n.succ n
        (D.labelledCellBasis n.succ x) := by
  let _ := D.topology
  let _ := D.cwComplex
  change D.labelledCellBasis n
      ((D.labelledCellBasis n).symm
        (ConcreteCategory.hom
          (D.integralCellularChainModel.chainComplex.d n.succ n)
          (D.labelledCellBasis n.succ x))) = _
  rw [AddEquiv.apply_symm_apply]

namespace StandardA2ToricCentralFiberSelectedBoundaryCompatibility

variable {X : Type} [TopologicalSpace X] [T2Space X]
  {A : StandardA2ToricCentralFiberCellAtlas X}

/-- The general labelled cellular-boundary formula implies the twenty-four independent
incidence values. -/
public theorem incidenceValues
    (C : StandardA2ToricCentralFiberSelectedBoundaryCompatibility A) :
    StandardA2ToricCentralFiberIndependentIncidenceValues A := by
  classical
  let _ := A.toCWDecomposition.topology
  let _ := A.toCWDecomposition.cwComplex
  apply StandardA2ToricCentralFiberIndependentIncidenceValues.ofResidual
  refine {
    boundaryZero := ?_
    boundaryOneIndependent := ?_
    boundaryTwo := ?_
    boundaryThree := ?_ }
  · dsimp only
    intro j i
    have h := C 0 (Pi.single j 1 : Fin 3 → ℤ)
    have hall : standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 0
        (Pi.single j 1 : Fin 3 → ℤ) =
      standardA2ToricCellularBoundary 0 (Pi.single j 1 : Fin 3 → ℤ) := by
      apply (A.toCWDecomposition.labelledCellBasis 0).injective
      exact (labelledCellBasis_coordinateBoundary A.toCWDecomposition 0
        (show cuspWCellIndex 1 → ℤ from (Pi.single j 1 : Fin 3 → ℤ))).trans h
    exact congrFun hall i
  · dsimp only
    intro j i
    have h := C 1 (Pi.single j 1 : Fin 4 → ℤ)
    have hall : standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 1
        (Pi.single j 1 : Fin 4 → ℤ) =
      standardA2ToricCellularBoundary 1 (Pi.single j 1 : Fin 4 → ℤ) := by
      apply (A.toCWDecomposition.labelledCellBasis 1).injective
      exact (labelledCellBasis_coordinateBoundary A.toCWDecomposition 1
        (show cuspWCellIndex 2 → ℤ from (Pi.single j 1 : Fin 4 → ℤ))).trans h
    exact congrFun hall i.castSucc
  · dsimp only
    intro j i
    have h := C 2 (Pi.single j 1 : Fin 2 → ℤ)
    have hall : standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 2
        (Pi.single j 1 : Fin 2 → ℤ) =
      standardA2ToricCellularBoundary 2 (Pi.single j 1 : Fin 2 → ℤ) := by
      apply (A.toCWDecomposition.labelledCellBasis 2).injective
      exact (labelledCellBasis_coordinateBoundary A.toCWDecomposition 2
        (show cuspWCellIndex 3 → ℤ from (Pi.single j 1 : Fin 2 → ℤ))).trans h
    exact congrFun hall i
  · dsimp only
    intro j i
    have h := C 3 (Pi.single j 1 : Fin 1 → ℤ)
    have hall : standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 3
        (Pi.single j 1 : Fin 1 → ℤ) =
      standardA2ToricCellularBoundary 3 (Pi.single j 1 : Fin 1 → ℤ) := by
      apply (A.toCWDecomposition.labelledCellBasis 3).injective
      exact (labelledCellBasis_coordinateBoundary A.toCWDecomposition 3
        (show cuspWCellIndex 4 → ℤ from (Pi.single j 1 : Fin 1 → ℤ))).trans h
    exact congrFun hall i

/-- Consequently, the full classical boundary formula implies the unchanged independent
incidence residual. -/
public theorem incidenceResidual
    (C : StandardA2ToricCentralFiberSelectedBoundaryCompatibility A) :
    StandardA2ToricCentralFiberIndependentIncidenceResidual A :=
  C.incidenceValues.toResidual

end StandardA2ToricCentralFiberSelectedBoundaryCompatibility

end SphereSixComplex

end

end
