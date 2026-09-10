module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- A homotopy model by a finite Hausdorff CW complex, with no dimension bound. -/
public structure FiniteCWModel (X : Type) [TopologicalSpace X] where
  Carrier : Type
  topology : TopologicalSpace Carrier
  t2 : let _ := topology; T2Space Carrier
  homotopyEquiv : let _ := topology; X ≃ₕ Carrier
  cwComplex : let _ := topology; Topology.CWComplex (Set.univ : Set Carrier)
  finite : let _ := topology; let _ := cwComplex
    Topology.CWComplex.Finite (Set.univ : Set Carrier)

namespace FiniteCWModel

variable {X : Type} [TopologicalSpace X]

/-- Number of cells in one degree of the chosen finite CW model. -/
public noncomputable def cellCount (M : FiniteCWModel X) (n : ℕ) : ℕ := by
  let _ := M.topology
  let _ := M.cwComplex
  let _ := M.finite
  exact Nat.card (Topology.CWComplex.cell (Set.univ : Set M.Carrier) n)

end FiniteCWModel

end SphereSixComplex

end

end
