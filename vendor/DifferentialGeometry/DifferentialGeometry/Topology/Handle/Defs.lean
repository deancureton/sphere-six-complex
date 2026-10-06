module

public import DifferentialGeometry.Topology.Attachment.Defs

@[expose] public section

namespace DifferentialGeometry.Topology.Handle

universe u

abbrev StandardHandle (k l : ℕ) : Type := ClosedCell k × ClosedCell l

abbrev AttachingRegion (k l : ℕ) : Type := CellBoundary k × ClosedCell l

abbrev BeltRegion (k l : ℕ) : Type := ClosedCell k × CellBoundary l

abbrev Corner (k l : ℕ) : Type := CellBoundary k × CellBoundary l

def attachingInclusion (k l : ℕ) : AttachingRegion k l → StandardHandle k l :=
  Prod.map (cellBoundaryInclusion k) (id : ClosedCell l → ClosedCell l)

def beltInclusion (k l : ℕ) : BeltRegion k l → StandardHandle k l :=
  Prod.map (id : ClosedCell k → ClosedCell k) (cellBoundaryInclusion l)

def cornerInclusion (k l : ℕ) : Corner k l → StandardHandle k l :=
  Prod.map (cellBoundaryInclusion k) (cellBoundaryInclusion l)

def attachingCornerInclusion (k l : ℕ) : Corner k l → AttachingRegion k l :=
  Prod.map (id : CellBoundary k → CellBoundary k) (cellBoundaryInclusion l)

def beltCornerInclusion (k l : ℕ) : Corner k l → BeltRegion k l :=
  Prod.map (cellBoundaryInclusion k) (id : CellBoundary l → CellBoundary l)

def coreDiskInclusion (k l : ℕ) : ClosedCell k → StandardHandle k l :=
  fun x => (x, closedCellCenter l)

def cocoreDiskInclusion (k l : ℕ) : ClosedCell l → StandardHandle k l :=
  fun y => (closedCellCenter k, y)

def attachingSphereInclusion (k l : ℕ) : CellBoundary k → StandardHandle k l :=
  fun x => (cellBoundaryInclusion k x, closedCellCenter l)

def beltSphereInclusion (k l : ℕ) : CellBoundary l → StandardHandle k l :=
  fun y => (closedCellCenter k, cellBoundaryInclusion l y)

def attachingSphereInclusionAttachingRegion (k l : ℕ) : CellBoundary k → AttachingRegion k l :=
  fun u => (u, closedCellCenter l)

def beltSphereInclusionBeltRegion (k l : ℕ) : CellBoundary l → BeltRegion k l :=
  fun v => (closedCellCenter k, v)

def attachingRegion (k l : ℕ) : Set (StandardHandle k l) :=
  {p | ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1}

def beltRegion (k l : ℕ) : Set (StandardHandle k l) :=
  {p | ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1}

def corner (k l : ℕ) : Set (StandardHandle k l) :=
  {p | ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1}

def coreDisk (k l : ℕ) : Set (StandardHandle k l) :=
  {p | p.2 = closedCellCenter l}

def cocoreDisk (k l : ℕ) : Set (StandardHandle k l) :=
  {p | p.1 = closedCellCenter k}

def attachingSphere (k l : ℕ) : Set (StandardHandle k l) :=
  {p | ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ p.2 = closedCellCenter l}

def beltSphere (k l : ℕ) : Set (StandardHandle k l) :=
  {p | p.1 = closedCellCenter k ∧ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1}

def handleSet (k l : ℕ) : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1

def attachingSet (k l : ℕ) : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1

def beltSet (k l : ℕ) : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1

def cornerSet (k l : ℕ) : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1

def toAmbient {k l : ℕ} (p : StandardHandle k l) :
    EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l) :=
  ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin l)))

abbrev AdjunctionSpace {X : Type u} (k l : ℕ) (φ : AttachingRegion k l → X) : Type u :=
  DifferentialGeometry.Topology.AdjunctionSpace (attachingInclusion k l) φ

def lower {X : Type u} {k l : ℕ} (φ : AttachingRegion k l → X) : X → AdjunctionSpace k l φ :=
  DifferentialGeometry.Topology.adjunctionLower (i := attachingInclusion k l) φ

def cell {X : Type u} {k l : ℕ} (φ : AttachingRegion k l → X) :
    StandardHandle k l → AdjunctionSpace k l φ :=
  DifferentialGeometry.Topology.adjunctionCell (attachingInclusion k l) φ

end DifferentialGeometry.Topology.Handle
