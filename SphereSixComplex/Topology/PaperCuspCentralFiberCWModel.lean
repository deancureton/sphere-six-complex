module

public import SphereSixComplex.Topology.SectionSevenLocalEulerModels

/-!
# The finite CW model of the cusp central fibre

The quotient of the standard periodic `A₂` toric central fibre has the cell orbits described in
Section 7: two vertices, three edges, four two-cells, two three-cells, and one four-cell.  This file
isolates the precise standard toric-CW realization theorem missing from Mathlib, then derives the
`CuspToricCellModel` and the Euler calculation used by the analytic cusp filling.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- Cell-orbit indices in a fundamental domain for the periodic `A₂` toric central fibre. -/
public def cuspWCellIndex : ℕ → Type
  | 0 => Fin 2
  | 1 => Fin 3
  | 2 => Fin 4
  | 3 => Fin 2
  | 4 => Fin 1
  | _ => Empty

public theorem cuspWCellIndex_isEmpty (n : ℕ) (hn : 4 < n) :
    IsEmpty (cuspWCellIndex n) := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  change IsEmpty Empty
  infer_instance

/-- A geometric CW realization whose cells are the orbit strata of the standard periodic `A₂`
toric central fibre.  This structure contains no homology groups or Euler characteristic. -/
public structure StandardA2ToricCentralFiberCWDecomposition
    (X : Type) [TopologicalSpace X] where
  Carrier : Type
  topology : TopologicalSpace Carrier
  homotopyEquiv : let _ := topology; X ≃ₕ Carrier
  cwComplex : let _ := topology; Topology.CWComplex (Set.univ : Set Carrier)
  finite : let _ := topology; let _ := cwComplex
    Topology.CWComplex.Finite (Set.univ : Set Carrier)
  cellEquiv : let _ := topology; let _ := cwComplex
    ∀ n, Topology.CWComplex.cell (Set.univ : Set Carrier) n ≃ cuspWCellIndex n

namespace StandardA2ToricCentralFiberCWDecomposition

variable {X : Type} [TopologicalSpace X]

/-- Forget the exact orbit labels and retain a finite CW model supported below degree seven. -/
public noncomputable def toFiniteCWModelSix
    (D : StandardA2ToricCentralFiberCWDecomposition X) : FiniteCWModelSix X where
  Carrier := D.Carrier
  topology := D.topology
  homotopyEquiv := D.homotopyEquiv
  cwComplex := D.cwComplex
  finite := D.finite
  cellsAboveSix n hn := by
    let _ := D.topology
    let _ := D.cwComplex
    let e := D.cellEquiv n
    let _ : IsEmpty (cuspWCellIndex n) := cuspWCellIndex_isEmpty n (by omega)
    exact Equiv.isEmpty e

private theorem cellCount_eq_natCard
    (D : StandardA2ToricCentralFiberCWDecomposition X) (n : ℕ) :
    D.toFiniteCWModelSix.cellCount n = Nat.card (cuspWCellIndex n) := by
  let _ := D.topology
  let _ := D.cwComplex
  let _ := D.finite
  unfold FiniteCWModelSix.cellCount
  exact Nat.card_congr (D.cellEquiv n)

/-- The standard periodic toric decomposition gives the exact cusp cell model. -/
public noncomputable def toCuspToricCellModel
    (D : StandardA2ToricCentralFiberCWDecomposition X) : CuspToricCellModel X where
  toFiniteCWModelSix := D.toFiniteCWModelSix
  cellsZero := by rw [D.cellCount_eq_natCard]; simp [cuspWCellIndex]
  cellsOne := by rw [D.cellCount_eq_natCard]; simp [cuspWCellIndex]
  cellsTwo := by rw [D.cellCount_eq_natCard]; simp [cuspWCellIndex]
  cellsThree := by rw [D.cellCount_eq_natCard]; simp [cuspWCellIndex]
  cellsFour := by rw [D.cellCount_eq_natCard]; simp [cuspWCellIndex]
  cellsFive := by rw [D.cellCount_eq_natCard]; simp [cuspWCellIndex]
  cellsSix := by rw [D.cellCount_eq_natCard]; simp [cuspWCellIndex]

end StandardA2ToricCentralFiberCWDecomposition

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-- Standard toric-orbit CW decomposition for the compact quotient of the periodic `A₂` central
fibre.  This is the exact general toric-topology boundary absent from Mathlib: it supplies a CW
realization and labels its cells by the orbit strata, but asserts no homology or Euler value.
This is a paper-specific geometric boundary, not a classical citation.  The orbit-cone
correspondence [Ful93, Section 3.1], [Oda88, Section 1.3] gives the torus-orbit stratification, but
that is not by itself a CW decomposition: a positive-dimensional orbit is a torus `(C*)^k`, not an
open cell.  Producing cells and attaching maps from the stratification is the content of the source
paper's appendix for this particular periodic `A₂` fibre, and is what is assumed here. -/
public axiom establishedStandardA2ToricCentralFiberCWDecomposition
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    StandardA2ToricCentralFiberCWDecomposition (R.quotientCentralFiber W)

/-- The actual quotient central fibre has the cusp toric cell model required by the local Euler
calculation. -/
public noncomputable def actualCuspCentralFiberCellModel
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    CuspToricCellModel (R.quotientCentralFiber W) :=
  (establishedStandardA2ToricCentralFiberCWDecomposition W R).toCuspToricCellModel

/-- Consequently the actual quotient central fibre has Euler characteristic two. -/
public theorem actualCuspCentralFiber_euler_eq_two
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    integralHomologyEulerCharacteristicSix (R.quotientCentralFiber W) = 2 :=
  (actualCuspCentralFiberCellModel W R).euler_eq_two

end Geometry.CuspPuncturedCollarBridge

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The actual cusp filling has Euler characteristic two once equipped with the independently
constructed equivariant central-fibre retraction. -/
public theorem actualCuspFilling_euler_eq_two
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    integralHomologyEulerCharacteristicSix (A.openEmbeddingStarData.filling 0) = 2 :=
  A.cuspFilling_euler_eq_of_centralFiberRetraction R
    (actualCuspCentralFiber_euler_eq_two A.starCuspWitness R)

end Geometry.PaperAnalyticData

end SphereSixComplex
