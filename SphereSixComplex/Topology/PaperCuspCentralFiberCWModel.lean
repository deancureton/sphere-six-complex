module

public import SphereSixComplex.Topology.SectionSevenLocalEulerModels
public import SphereSixComplex.Topology.CellularChainModel
public import SphereSixComplex.Topology.PaperCuspCentralFiberCWConstruction
public import SphereSixComplex.Geometry.PaperStarPieceHausdorff

/-!
# The finite CW model of the cusp central fibre

The quotient of the standard periodic `A₂` toric central fibre has the cell orbits described in
Section 7: two vertices, three edges, four two-cells, two three-cells, and one four-cell.  This file
isolates the precise standard toric-CW realization theorem missing from Mathlib, then derives the
`CuspToricCellModel` and the Euler calculation used by the analytic cusp filling.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
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

public theorem cuspWCellIndex_finite (n : ℕ) : Finite (cuspWCellIndex n) := by
  rcases n with (_ | _ | _ | _ | _ | n)
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 2))
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 3))
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 4))
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 2))
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 1))
  · simpa [cuspWCellIndex] using (inferInstance : Finite Empty)

public theorem cuspWCellIndex_eventually_isEmpty :
    ∀ᶠ n in Filter.atTop, IsEmpty (cuspWCellIndex n) := by
  rw [Filter.eventually_atTop]
  exact ⟨5, fun n hn ↦ cuspWCellIndex_isEmpty n (by omega)⟩

/-- The oriented edge-incidence map in the standard toric cell coordinates. -/
public def standardA2ToricCellularBoundaryOne : (Fin 3 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![-(x 0 + x 1 + x 2), x 0 + x 1 + x 2]
  map_zero' := by funext i; fin_cases i <;> simp
  map_add' := by intro x y; funext i; fin_cases i <;> simp <;> ring

/-- The cellular boundary formula of the standard periodic `A₂` toric central fibre. -/
public def standardA2ToricCellularBoundary :
    (n : ℕ) → (cuspWCellIndex n.succ → ℤ) →+ (cuspWCellIndex n → ℤ)
  | 0 => standardA2ToricCellularBoundaryOne
  | _ + 1 => 0

/-- A geometric CW realization whose cells are the orbit strata of the standard periodic `A₂`
toric central fibre.  This structure contains no homology groups or Euler characteristic. -/
public structure StandardA2ToricCentralFiberCWDecomposition
    (X : Type) [TopologicalSpace X] where
  Carrier : Type
  topology : TopologicalSpace Carrier
  /-- The carrier is Hausdorff.  `Topology.CWComplex` carries no separation axiom, and the
  cellular chain model is false without one; see
  `SphereSixComplex.isEmpty_forall_integralCWCellularChainModel`. -/
  t2 : let _ := topology; T2Space Carrier
  homotopyEquiv : let _ := topology; X ≃ₕ Carrier
  cwComplex : let _ := topology; Topology.CWComplex (Set.univ : Set Carrier)
  finite : let _ := topology; let _ := cwComplex
    Topology.CWComplex.Finite (Set.univ : Set Carrier)
  cellEquiv : let _ := topology; let _ := cwComplex
    ∀ n, Topology.CWComplex.cell (Set.univ : Set Carrier) n ≃ cuspWCellIndex n

namespace StandardA2ToricCentralFiberCWDecomposition

variable {X : Type} [TopologicalSpace X]

/-- The standard integral cellular chain model selected for the carrier. -/
public noncomputable def integralCellularChainModel
    (D : StandardA2ToricCentralFiberCWDecomposition X) :
    let _ := D.topology
    let _ := D.cwComplex
    IntegralCWCellularChainModel D.Carrier := by
  letI := D.topology
  letI := D.t2
  letI := D.cwComplex
  exact EstablishedCellularHomology.integralCWCellularChainModel D.Carrier

/-- Reindex integer coordinates along the labelled orbit-cell equivalence. -/
public def standardIntegerFunctionReindexAddEquiv {I J : Type} (e : I ≃ J) :
    (J → ℤ) ≃+ (I → ℤ) where
  toFun x i := x (e i)
  invFun x j := x (e.symm j)
  left_inv x := by funext j; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl

/-- The cellular basis in the standard orbit-cell coordinates. -/
public noncomputable def labelledCellBasis
    (D : StandardA2ToricCentralFiberCWDecomposition X) (n : ℕ) :
    let _ := D.topology
    let _ := D.cwComplex
    (cuspWCellIndex n → ℤ) ≃+ D.integralCellularChainModel.chainComplex.X n := by
  letI := D.topology
  letI := D.cwComplex
  letI : Finite (cuspWCellIndex n) := cuspWCellIndex_finite n
  letI : Finite (Topology.CWComplex.cell (Set.univ : Set D.Carrier) n) :=
    Finite.of_equiv _ (D.cellEquiv n).symm
  exact
    (standardIntegerFunctionReindexAddEquiv (D.cellEquiv n)).trans
      Finsupp.addEquivFunOnFinite.symm |>.trans (D.integralCellularChainModel.cellBasis n)

/-- Forget the exact orbit labels and retain a finite CW model supported below degree seven. -/
public noncomputable def toFiniteCWModelSix
    (D : StandardA2ToricCentralFiberCWDecomposition X) : FiniteCWModelSix X where
  Carrier := D.Carrier
  topology := D.topology
  t2 := D.t2
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

/-- A standard toric CW realization together with its exact attaching-incidence calculation.
This is the single geometric-combinatorial input needed from the periodic `A₂` quotient. -/
public structure StandardA2ToricCentralFiberCellularRealization
    (X : Type) [TopologicalSpace X] where
  decomposition : StandardA2ToricCentralFiberCWDecomposition X
  boundary_eq :
    let D := decomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (n : ℕ) (x : cuspWCellIndex n.succ → ℤ),
      D.integralCellularChainModel.chainComplex.d n.succ n (D.labelledCellBasis n.succ x) =
        D.labelledCellBasis n (standardA2ToricCellularBoundary n x)

/-- The genuine cellular differential, transported into the labelled orbit-cell coordinates. -/
public noncomputable def standardA2ToricCellularCoordinateBoundary
    {X : Type} [TopologicalSpace X]
    (D : StandardA2ToricCentralFiberCWDecomposition X) (n : ℕ) :
    (cuspWCellIndex n.succ → ℤ) →+ (cuspWCellIndex n → ℤ) := by
  letI := D.topology
  letI := D.cwComplex
  let d := ConcreteCategory.hom
    (D.integralCellularChainModel.chainComplex.d n.succ n)
  exact (D.labelledCellBasis n).symm.toAddMonoidHom.comp
    (d.comp (D.labelledCellBasis n.succ).toAddMonoidHom)

/-- Characteristic maps for the labelled cells of the standard periodic `A₂` quotient,
stated directly on the actual quotient carrier.  The fields are precisely the hypotheses of
Mathlib's finite-CW constructor; no CW structure, finiteness result, or homotopy equivalence is
included. -/
public structure StandardA2ToricCentralFiberCellAtlas
    (X : Type) [TopologicalSpace X] where
  cellMap : (n : ℕ) → cuspWCellIndex n → PartialEquiv (Fin n → ℝ) X
  source_eq : ∀ (n : ℕ) (i : cuspWCellIndex n),
    (cellMap n i).source = Metric.ball 0 1
  continuousOn : ∀ (n : ℕ) (i : cuspWCellIndex n),
    ContinuousOn (cellMap n i) (Metric.closedBall 0 1)
  continuousOn_symm : ∀ (n : ℕ) (i : cuspWCellIndex n),
    ContinuousOn (cellMap n i).symm (cellMap n i).target
  pairwiseDisjoint : (Set.univ : Set (Σ n, cuspWCellIndex n)).PairwiseDisjoint
    (fun ni ↦ cellMap ni.1 ni.2 '' Metric.ball 0 1)
  mapsTo : ∀ (n : ℕ) (i : cuspWCellIndex n),
    MapsTo (cellMap n i) (Metric.sphere 0 1)
      (⋃ (m < n) (j : cuspWCellIndex m), cellMap m j '' Metric.closedBall 0 1)
  union_eq : (⋃ (n : ℕ), ⋃ (j : cuspWCellIndex n),
    cellMap n j '' Metric.closedBall 0 1) = Set.univ

namespace StandardA2ToricCentralFiberCellAtlas

variable {X : Type} [TopologicalSpace X]

/-- The CW structure constructed from the explicit characteristic-map atlas. -/
@[instance_reducible]
public noncomputable def cwComplex (A : StandardA2ToricCentralFiberCellAtlas X) :
    Topology.CWComplex (Set.univ : Set X) :=
  Topology.CWComplex.mkFinite (Set.univ : Set X) cuspWCellIndex A.cellMap
    cuspWCellIndex_eventually_isEmpty cuspWCellIndex_finite A.source_eq A.continuousOn
      A.continuousOn_symm A.pairwiseDisjoint A.mapsTo A.union_eq

/-- Mathlib's finite-CW constructor proves that the characteristic-map atlas is finite. -/
public theorem finite (A : StandardA2ToricCentralFiberCellAtlas X) :
    let _ := A.cwComplex
    Topology.CWComplex.Finite (Set.univ : Set X) :=
  Topology.CWComplex.finite_mkFinite (Set.univ : Set X) cuspWCellIndex A.cellMap
    cuspWCellIndex_eventually_isEmpty cuspWCellIndex_finite A.source_eq A.continuousOn
      A.continuousOn_symm A.pairwiseDisjoint A.mapsTo A.union_eq

/-- The atlas gives a decomposition on the original carrier, with the identity homotopy
equivalence and definitionally labelled cells. -/
public noncomputable def toCWDecomposition [T2Space X]
    (A : StandardA2ToricCentralFiberCellAtlas X) :
    StandardA2ToricCentralFiberCWDecomposition X where
  Carrier := X
  topology := inferInstance
  t2 := inferInstance
  homotopyEquiv := ContinuousMap.HomotopyEquiv.refl X
  cwComplex := A.cwComplex
  finite := A.finite
  cellEquiv := fun _ ↦ Equiv.refl _

end StandardA2ToricCentralFiberCellAtlas

/-- The unresolved incidence calculation after constructing the CW structure through Mathlib:
exactly twenty-eight scalar entries in the characteristic-map coordinates. -/
public structure StandardA2ToricCentralFiberIncidenceResidual
    {X : Type} [TopologicalSpace X] [T2Space X]
    (atlas : StandardA2ToricCentralFiberCellAtlas X) where
  boundaryZero :
    let D := atlas.toCWDecomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 3) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 0
          (Pi.single j 1 : Fin 3 → ℤ) i =
        standardA2ToricCellularBoundary 0 (Pi.single j 1 : Fin 3 → ℤ) i
  boundaryOne :
    let D := atlas.toCWDecomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 4) (i : Fin 3),
      standardA2ToricCellularCoordinateBoundary D 1
          (Pi.single j 1 : Fin 4 → ℤ) i =
        standardA2ToricCellularBoundary 1 (Pi.single j 1 : Fin 4 → ℤ) i
  boundaryTwo :
    let D := atlas.toCWDecomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 2) (i : Fin 4),
      standardA2ToricCellularCoordinateBoundary D 2
          (Pi.single j 1 : Fin 2 → ℤ) i =
        standardA2ToricCellularBoundary 2 (Pi.single j 1 : Fin 2 → ℤ) i
  boundaryThree :
    let D := atlas.toCWDecomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 1) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 3
          (Pi.single j 1 : Fin 1 → ℤ) i =
        standardA2ToricCellularBoundary 3 (Pi.single j 1 : Fin 1 → ℤ) i

/-- A labelled standard `A₂` CW decomposition together with the complete finite incidence
matrix.  There are exactly twenty-eight scalar entries: `3 × 2`, `4 × 3`, `2 × 4`, and
`1 × 2` in boundary degrees zero through three.  Higher source cell sets are empty. -/
public structure StandardA2ToricCentralFiberFiniteCellularRealization
    (X : Type) [TopologicalSpace X] where
  decomposition : StandardA2ToricCentralFiberCWDecomposition X
  boundaryZero :
    let D := decomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 3) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 0
          (Pi.single j 1 : Fin 3 → ℤ) i =
        standardA2ToricCellularBoundary 0 (Pi.single j 1 : Fin 3 → ℤ) i
  boundaryOne :
    let D := decomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 4) (i : Fin 3),
      standardA2ToricCellularCoordinateBoundary D 1
          (Pi.single j 1 : Fin 4 → ℤ) i =
        standardA2ToricCellularBoundary 1 (Pi.single j 1 : Fin 4 → ℤ) i
  boundaryTwo :
    let D := decomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 2) (i : Fin 4),
      standardA2ToricCellularCoordinateBoundary D 2
          (Pi.single j 1 : Fin 2 → ℤ) i =
        standardA2ToricCellularBoundary 2 (Pi.single j 1 : Fin 2 → ℤ) i
  boundaryThree :
    let D := decomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 1) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 3
          (Pi.single j 1 : Fin 1 → ℤ) i =
        standardA2ToricCellularBoundary 3 (Pi.single j 1 : Fin 1 → ℤ) i

private theorem addMonoidHom_ext_pi_single_one
    {H : Type*} [AddCommGroup H] {n : ℕ} (f g : (Fin n → ℤ) →+ H)
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply AddMonoidHom.ext
  intro x
  apply Pi.single_induction (M := fun _ : Fin n ↦ ℤ) (p := fun z ↦ f z = g z) x
  · simp
  · intro a b ha hb
    simpa using congrArg₂ (· + ·) ha hb
  · intro i z
    have hz : (Pi.single i z : Fin n → ℤ) =
        z • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      classical
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    rw [hz, map_zsmul, map_zsmul, h i]

namespace StandardA2ToricCentralFiberFiniteCellularRealization

variable {X : Type} [TopologicalSpace X]

/-- Construct the bundled finite realization from the characteristic-map and incidence
residual. -/
public noncomputable def ofAtlasAndIncidence [T2Space X]
    (A : StandardA2ToricCentralFiberCellAtlas X)
    (T : StandardA2ToricCentralFiberIncidenceResidual A) :
    StandardA2ToricCentralFiberFiniteCellularRealization X where
  decomposition := A.toCWDecomposition
  boundaryZero := T.boundaryZero
  boundaryOne := T.boundaryOne
  boundaryTwo := T.boundaryTwo
  boundaryThree := T.boundaryThree

/-- Additive extension of the finite incidence matrix gives the genuine cellular boundary on
every chain.  Above degree four the assertion is automatic because there are no source cells. -/
public noncomputable def toCellularRealization
    (T : StandardA2ToricCentralFiberFiniteCellularRealization X) :
    StandardA2ToricCentralFiberCellularRealization X where
  decomposition := T.decomposition
  boundary_eq := by
    dsimp only
    intro n x
    let D := T.decomposition
    let _ := D.topology
    let _ := D.cwComplex
    apply (T.decomposition.labelledCellBasis n).symm.injective
    rw [AddEquiv.symm_apply_apply]
    change standardA2ToricCellularCoordinateBoundary T.decomposition n x =
      standardA2ToricCellularBoundary n x
    rcases n with _ | _ | _ | _ | n
    · have h : standardA2ToricCellularCoordinateBoundary D 0 =
          standardA2ToricCellularBoundary 0 := by
        apply addMonoidHom_ext_pi_single_one
        intro j
        funext i
        exact T.boundaryZero j i
      exact DFunLike.congr_fun h x
    · have h : standardA2ToricCellularCoordinateBoundary D 1 =
          standardA2ToricCellularBoundary 1 := by
        apply addMonoidHom_ext_pi_single_one
        intro j
        funext i
        exact T.boundaryOne j i
      exact DFunLike.congr_fun h x
    · have h : standardA2ToricCellularCoordinateBoundary D 2 =
          standardA2ToricCellularBoundary 2 := by
        apply addMonoidHom_ext_pi_single_one
        intro j
        funext i
        exact T.boundaryTwo j i
      exact DFunLike.congr_fun h x
    · have h : standardA2ToricCellularCoordinateBoundary D 3 =
          standardA2ToricCellularBoundary 3 := by
        apply addMonoidHom_ext_pi_single_one
        intro j
        funext i
        exact T.boundaryThree j i
      exact DFunLike.congr_fun h x
    · let _ : IsEmpty (cuspWCellIndex (n + 1 + 1 + 1 + 1).succ) :=
          cuspWCellIndex_isEmpty _ (by omega)
      have hx : x = 0 := by
        funext i
        exact isEmptyElim i
      rw [hx, map_zero, map_zero]

end StandardA2ToricCentralFiberFiniteCellularRealization

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-- The remaining geometric input: characteristic maps on the actual compact periodic `A₂`
quotient.  Mathlib constructs the CW structure and its finiteness from these maps. -/
public axiom establishedStandardA2ToricCentralFiberCellAtlas
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let _ : T2Space (actualLocalCuspFilling W) :=
      SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
    let _ : T2Space (R.quotientCentralFiber W) := inferInstance
    StandardA2ToricCentralFiberCellAtlas (R.quotientCentralFiber W)

/-- The remaining combinatorial input: the twenty-eight scalar cellular-incidence entries in
the atlas coordinates. -/
public axiom establishedStandardA2ToricCentralFiberIncidenceResidual
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let _ : T2Space (actualLocalCuspFilling W) :=
      SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
    let _ : T2Space (R.quotientCentralFiber W) := inferInstance
    StandardA2ToricCentralFiberIncidenceResidual
      (establishedStandardA2ToricCentralFiberCellAtlas W R)

/-- The actual quotient carrier, equipped with the CW structure constructed from the residual
characteristic maps and with the verified finite incidence table. -/
public noncomputable def establishedStandardA2ToricCentralFiberFiniteCellularRealization
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    StandardA2ToricCentralFiberFiniteCellularRealization (R.quotientCentralFiber W) := by
  letI : T2Space (actualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  letI : T2Space (R.quotientCentralFiber W) := inferInstance
  exact StandardA2ToricCentralFiberFiniteCellularRealization.ofAtlasAndIncidence
    (establishedStandardA2ToricCentralFiberCellAtlas W R)
    (establishedStandardA2ToricCentralFiberIncidenceResidual W R)

/-- The compact periodic `A₂` central fibre has its standard labelled CW realization and exact
attaching-incidence formula. -/
public noncomputable def establishedStandardA2ToricCentralFiberCellularRealization
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    StandardA2ToricCentralFiberCellularRealization (R.quotientCentralFiber W)
  := (establishedStandardA2ToricCentralFiberFiniteCellularRealization W R).toCellularRealization

/-- Standard toric-orbit CW decomposition for the compact quotient of the periodic `A₂` central
fibre.  This is the exact general toric-topology boundary absent from Mathlib: it supplies a CW
realization and labels its cells by the orbit strata, but asserts no homology or Euler value. -/
public noncomputable def establishedStandardA2ToricCentralFiberCWDecomposition
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    StandardA2ToricCentralFiberCWDecomposition (R.quotientCentralFiber W) := by
  letI : T2Space (actualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  letI : T2Space (R.quotientCentralFiber W) := inferInstance
  exact (establishedStandardA2ToricCentralFiberCellAtlas W R).toCWDecomposition

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
