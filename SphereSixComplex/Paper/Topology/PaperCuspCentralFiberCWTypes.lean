module

public import SphereSixComplex.Paper.Topology.SectionSevenLocalEulerModels
public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberCWConstruction
public import SphereSixComplex.Paper.Geometry.PaperStarPieceHausdorff

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
public def CuspWCellIndex : ℕ → Type
  | 0 => Fin 2
  | 1 => Fin 3
  | 2 => Fin 4
  | 3 => Fin 2
  | 4 => Fin 1
  | _ => Empty

public theorem cuspWCellIndex_isEmpty (n : ℕ) (hn : 4 < n) :
    IsEmpty (CuspWCellIndex n) := by
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

public theorem cuspWCellIndex_finite (n : ℕ) : Finite (CuspWCellIndex n) := by
  rcases n with (_ | _ | _ | _ | _ | n)
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 2))
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 3))
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 4))
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 2))
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 1))
  · simpa [CuspWCellIndex] using (inferInstance : Finite Empty)

public theorem cuspWCellIndex_eventually_isEmpty :
    ∀ᶠ n in Filter.atTop, IsEmpty (CuspWCellIndex n) := by
  rw [Filter.eventually_atTop]
  exact ⟨5, fun n hn ↦ cuspWCellIndex_isEmpty n (by omega)⟩

/-- The oriented edge-incidence map in the standard toric cell coordinates. -/
public def standardA2ToricCellularBoundaryOne : (Fin 3 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![-(x 0 + x 1 + x 2), x 0 + x 1 + x 2]
  map_zero' := by funext i; fin_cases i <;> simp
  map_add' := by intro x y; funext i; fin_cases i <;> simp <;> ring

/-- The cellular boundary formula of the standard periodic `A₂` toric central fibre. -/
public def standardA2ToricCellularBoundary :
    (n : ℕ) → (CuspWCellIndex n.succ → ℤ) →+ (CuspWCellIndex n → ℤ)
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
    ∀ n, Topology.CWComplex.cell (Set.univ : Set Carrier) n ≃ CuspWCellIndex n

namespace StandardA2ToricCentralFiberCWDecomposition

variable {X : Type} [TopologicalSpace X]

/-- The standard integral cellular chain model selected for the carrier. -/
public noncomputable def integralCellularChainModel
    (D : StandardA2ToricCentralFiberCWDecomposition X) :
    let _ := D.topology
    let _ := D.cwComplex
    IntegralCWCellularHomologyModel D.Carrier := by
  letI := D.topology
  letI := D.t2
  letI := D.cwComplex
  exact CellularHomology.normalizedModel D.Carrier

/-- The cellular basis in the standard orbit-cell coordinates. -/
public noncomputable def labelledCellBasis
    (D : StandardA2ToricCentralFiberCWDecomposition X) (n : ℕ) :
    let _ := D.topology
    let _ := D.cwComplex
    (CuspWCellIndex n → ℤ) ≃+ D.integralCellularChainModel.chainComplex.X n := by
  letI := D.topology
  letI := D.cwComplex
  letI : Finite (CuspWCellIndex n) := cuspWCellIndex_finite n
  letI : Finite (Topology.CWComplex.cell (Set.univ : Set D.Carrier) n) :=
    Finite.of_equiv _ (D.cellEquiv n).symm
  exact
    (AddEquiv.arrowCongr (D.cellEquiv n).symm (AddEquiv.refl ℤ)).trans
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
    let _ : IsEmpty (CuspWCellIndex n) := cuspWCellIndex_isEmpty n (by omega)
    exact Equiv.isEmpty e

private theorem cellCount_eq_natCard
    (D : StandardA2ToricCentralFiberCWDecomposition X) (n : ℕ) :
    D.toFiniteCWModelSix.cellCount n = Nat.card (CuspWCellIndex n) := by
  let _ := D.topology
  let _ := D.cwComplex
  let _ := D.finite
  unfold FiniteCWModelSix.cellCount
  exact Nat.card_congr (D.cellEquiv n)

/-- The standard periodic toric decomposition gives the exact cusp cell model. -/
public noncomputable def toCuspToricCellModel
    (D : StandardA2ToricCentralFiberCWDecomposition X) : CuspToricCellModel X where
  toFiniteCWModelSix := D.toFiniteCWModelSix
  cellsZero := by rw [D.cellCount_eq_natCard]; simp [CuspWCellIndex]
  cellsOne := by rw [D.cellCount_eq_natCard]; simp [CuspWCellIndex]
  cellsTwo := by rw [D.cellCount_eq_natCard]; simp [CuspWCellIndex]
  cellsThree := by rw [D.cellCount_eq_natCard]; simp [CuspWCellIndex]
  cellsFour := by rw [D.cellCount_eq_natCard]; simp [CuspWCellIndex]
  cellsFive := by rw [D.cellCount_eq_natCard]; simp [CuspWCellIndex]
  cellsSix := by rw [D.cellCount_eq_natCard]; simp [CuspWCellIndex]

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
    ∀ (n : ℕ) (x : CuspWCellIndex n.succ → ℤ),
      D.integralCellularChainModel.chainComplex.d n.succ n (D.labelledCellBasis n.succ x) =
        D.labelledCellBasis n (standardA2ToricCellularBoundary n x)

/-- The genuine cellular differential, transported into the labelled orbit-cell coordinates. -/
public noncomputable def standardA2ToricCellularCoordinateBoundary
    {X : Type} [TopologicalSpace X]
    (D : StandardA2ToricCentralFiberCWDecomposition X) (n : ℕ) :
    (CuspWCellIndex n.succ → ℤ) →+ (CuspWCellIndex n → ℤ) := by
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
  cellMap : (n : ℕ) → CuspWCellIndex n → PartialEquiv (Fin n → ℝ) X
  source_eq : ∀ (n : ℕ) (i : CuspWCellIndex n),
    (cellMap n i).source = Metric.ball 0 1
  continuousOn : ∀ (n : ℕ) (i : CuspWCellIndex n),
    ContinuousOn (cellMap n i) (Metric.closedBall 0 1)
  continuousOn_symm : ∀ (n : ℕ) (i : CuspWCellIndex n),
    ContinuousOn (cellMap n i).symm (cellMap n i).target
  pairwiseDisjoint : (Set.univ : Set (Σ n, CuspWCellIndex n)).PairwiseDisjoint
    (fun ni ↦ cellMap ni.1 ni.2 '' Metric.ball 0 1)
  mapsTo : ∀ (n : ℕ) (i : CuspWCellIndex n),
    MapsTo (cellMap n i) (Metric.sphere 0 1)
      (⋃ (m < n) (j : CuspWCellIndex m), cellMap m j '' Metric.closedBall 0 1)
  union_eq : (⋃ (n : ℕ), ⋃ (j : CuspWCellIndex n),
    cellMap n j '' Metric.closedBall 0 1) = Set.univ

namespace StandardA2ToricCentralFiberCellAtlas

variable {X : Type} [TopologicalSpace X]

/-- The CW structure constructed from the explicit characteristic-map atlas. -/
@[instance_reducible]
public noncomputable def cwComplex (A : StandardA2ToricCentralFiberCellAtlas X) :
    Topology.CWComplex (Set.univ : Set X) :=
  Topology.CWComplex.mkFinite (Set.univ : Set X) CuspWCellIndex A.cellMap
    cuspWCellIndex_eventually_isEmpty cuspWCellIndex_finite A.source_eq A.continuousOn
      A.continuousOn_symm A.pairwiseDisjoint A.mapsTo A.union_eq

/-- Mathlib's finite-CW constructor proves that the characteristic-map atlas is finite. -/
public theorem finite (A : StandardA2ToricCentralFiberCellAtlas X) :
    let _ := A.cwComplex
    Topology.CWComplex.Finite (Set.univ : Set X) :=
  Topology.CWComplex.finite_mkFinite (Set.univ : Set X) CuspWCellIndex A.cellMap
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

/-- Transport a labelled characteristic-map atlas across a homeomorphism. -/
public noncomputable def transport {Y : Type} [TopologicalSpace Y]
    (A : StandardA2ToricCentralFiberCellAtlas X) (e : X ≃ₜ Y) :
    StandardA2ToricCentralFiberCellAtlas Y where
  cellMap n i := (A.cellMap n i).trans e.toEquiv.toPartialEquiv
  source_eq := by
    intro n i
    simp [PartialEquiv.trans_source, A.source_eq]
  continuousOn := by
    intro n i
    rw [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply]
    exact e.continuous.continuousOn.comp (A.continuousOn n i) (fun _ _ ↦ Set.mem_univ _)
  continuousOn_symm := by
    intro n i
    rw [PartialEquiv.coe_trans_symm]
    apply (A.continuousOn_symm n i).comp e.symm.continuous.continuousOn
    intro y hy
    simpa [PartialEquiv.trans_target] using hy.2
  pairwiseDisjoint := by
    intro a _ b _ hab
    change Disjoint _ _
    simp only [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply]
    rw [Set.disjoint_left]
    intro y ⟨za, hza, hya⟩ ⟨zb, hzb, hyb⟩
    have hzab :
        (A.cellMap a.1 a.2) za = (A.cellMap b.1 b.2) zb :=
      e.injective (hya.trans hyb.symm)
    apply Set.disjoint_left.mp
      (A.pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ b) hab)
      (show (A.cellMap a.1 a.2) za ∈
        (A.cellMap a.1 a.2) '' Metric.ball 0 1 from ⟨za, hza, rfl⟩)
    exact ⟨zb, hzb, hzab.symm⟩
  mapsTo := by
    intro n i x hx
    rw [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply]
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ((A.mapsTo n i) hx)
    obtain ⟨hmn, hm⟩ := Set.mem_iUnion.mp hm
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hm
    refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hmn, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩⟩
    rw [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply]
    obtain ⟨z, hz, hzEq⟩ := hj
    exact ⟨z, hz, congrArg e hzEq⟩
  union_eq := by
    rw [← e.surjective.range_eq]
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hn
      rw [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply] at hj
      obtain ⟨x, hx, rfl⟩ := hj
      exact Set.mem_range_self _
    · rintro ⟨x, rfl⟩
      have hx : x ∈ (Set.univ : Set X) := Set.mem_univ x
      rw [← A.union_eq] at hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hn
      refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩
      rw [PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply]
      obtain ⟨z, hz, hzEq⟩ := hj
      exact ⟨z, hz, congrArg e hzEq⟩

end StandardA2ToricCentralFiberCellAtlas

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

private theorem standardA2ToricCellularCoordinateBoundary_comp
    {X : Type} [TopologicalSpace X]
    (D : StandardA2ToricCentralFiberCWDecomposition X) (n : ℕ)
    (x : CuspWCellIndex (n + 2) → ℤ) :
    standardA2ToricCellularCoordinateBoundary D n
        (standardA2ToricCellularCoordinateBoundary D (n + 1) x) = 0 := by
  let _ := D.topology
  let _ := D.cwComplex
  change (D.labelledCellBasis n).symm
    (ConcreteCategory.hom (D.integralCellularChainModel.chainComplex.d (n + 1) n)
      (D.labelledCellBasis (n + 1)
        ((D.labelledCellBasis (n + 1)).symm
          (ConcreteCategory.hom
            (D.integralCellularChainModel.chainComplex.d (n + 2) (n + 1))
            (D.labelledCellBasis (n + 2) x))))) = 0
  rw [AddEquiv.apply_symm_apply]
  have h := ConcreteCategory.congr_hom
    (D.integralCellularChainModel.chainComplex.d_comp_d (n + 2) (n + 1) n)
    (D.labelledCellBasis (n + 2) x)
  rw [AddCommGrpCat.comp_apply] at h
  rw [h]
  simp

namespace StandardA2ToricCentralFiberCWDecomposition

variable {X : Type} [TopologicalSpace X]

/-- The first two rows determine the two-cell boundary, by the chain-complex identity. -/
public theorem coordinateBoundary_one_eq_of_independent
    (D : StandardA2ToricCentralFiberCWDecomposition X)
    (h0 : ∀ (j : Fin 3) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 0 (Pi.single j 1 : Fin 3 → ℤ) i =
        standardA2ToricCellularBoundary 0 (Pi.single j 1 : Fin 3 → ℤ) i)
    (h1 : ∀ (j : Fin 4) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 1 (Pi.single j 1 : Fin 4 → ℤ) i.castSucc =
        standardA2ToricCellularBoundary 1 (Pi.single j 1 : Fin 4 → ℤ) i.castSucc) :
    standardA2ToricCellularCoordinateBoundary D 1 = standardA2ToricCellularBoundary 1 := by
  apply addMonoidHom_ext_pi_single_one (H := Fin 3 → ℤ)
  intro j
  funext i
  let _ := D.topology
  let _ := D.cwComplex
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact h1 j 0
  · exact h1 j 1
  · have hzero := standardA2ToricCellularCoordinateBoundary_comp D 0
        (Pi.single j 1 : Fin 4 → ℤ)
    have hzero0 := congr_fun hzero (show CuspWCellIndex 0 from (0 : Fin 2))
    have hboundaryZero :
        standardA2ToricCellularCoordinateBoundary D 0 =
          standardA2ToricCellularBoundary 0 := by
      apply addMonoidHom_ext_pi_single_one
      intro k
      funext i
      exact h0 k i
    rw [hboundaryZero] at hzero0
    have h0 := h1 j 0
    change standardA2ToricCellularCoordinateBoundary D 1
        (Pi.single j 1 : Fin 4 → ℤ)
          (show CuspWCellIndex 1 from (0 : Fin 3)) = 0 at h0
    have h1 := h1 j 1
    change standardA2ToricCellularCoordinateBoundary D 1
        (Pi.single j 1 : Fin 4 → ℤ)
          (show CuspWCellIndex 1 from (1 : Fin 3)) = 0 at h1
    change -(standardA2ToricCellularCoordinateBoundary D 1
        (Pi.single j 1 : Fin 4 → ℤ) (show CuspWCellIndex 1 from (0 : Fin 3)) +
      standardA2ToricCellularCoordinateBoundary D 1
        (Pi.single j 1 : Fin 4 → ℤ) (show CuspWCellIndex 1 from (1 : Fin 3)) +
      standardA2ToricCellularCoordinateBoundary D 1
        (Pi.single j 1 : Fin 4 → ℤ) (show CuspWCellIndex 1 from (2 : Fin 3))) = 0
      at hzero0
    rw [h0, h1] at hzero0
    simp at hzero0
    change standardA2ToricCellularCoordinateBoundary D 1
      (Pi.single j 1 : Fin 4 → ℤ) (show CuspWCellIndex 1 from (2 : Fin 3)) = 0
    exact hzero0

/-- The independent finite incidences determine every cellular differential. -/
public theorem coordinateBoundary_eq_of_independent
    (D : StandardA2ToricCentralFiberCWDecomposition X)
    (h0 : ∀ (j : Fin 3) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 0 (Pi.single j 1 : Fin 3 → ℤ) i =
        standardA2ToricCellularBoundary 0 (Pi.single j 1 : Fin 3 → ℤ) i)
    (h1 : ∀ (j : Fin 4) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 1 (Pi.single j 1 : Fin 4 → ℤ) i.castSucc =
        standardA2ToricCellularBoundary 1 (Pi.single j 1 : Fin 4 → ℤ) i.castSucc)
    (h2 : ∀ (j : Fin 2) (i : Fin 4),
      standardA2ToricCellularCoordinateBoundary D 2 (Pi.single j 1 : Fin 2 → ℤ) i =
        standardA2ToricCellularBoundary 2 (Pi.single j 1 : Fin 2 → ℤ) i)
    (h3 : ∀ (j : Fin 1) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 3 (Pi.single j 1 : Fin 1 → ℤ) i =
        standardA2ToricCellularBoundary 3 (Pi.single j 1 : Fin 1 → ℤ) i)
    (n : ℕ) :
    standardA2ToricCellularCoordinateBoundary D n = standardA2ToricCellularBoundary n := by
  rcases n with _ | _ | _ | _ | n
  · apply addMonoidHom_ext_pi_single_one
    intro j
    funext i
    exact h0 j i
  · exact D.coordinateBoundary_one_eq_of_independent h0 h1
  · apply addMonoidHom_ext_pi_single_one
    intro j
    funext i
    exact h2 j i
  · apply addMonoidHom_ext_pi_single_one
    intro j
    funext i
    exact h3 j i
  · let _ : IsEmpty (CuspWCellIndex (n + 1 + 1 + 1 + 1).succ) :=
        cuspWCellIndex_isEmpty _ (by omega)
    apply AddMonoidHom.ext
    intro x
    have hx : x = 0 := by
      funext i
      exact isEmptyElim i
    rw [hx, map_zero, map_zero]

public noncomputable def toCellularRealization
    (D : StandardA2ToricCentralFiberCWDecomposition X)
    (h : ∀ n, standardA2ToricCellularCoordinateBoundary D n =
      standardA2ToricCellularBoundary n) :
    StandardA2ToricCentralFiberCellularRealization X where
  decomposition := D
  boundary_eq := by
    dsimp only
    intro n x
    let _ := D.topology
    let _ := D.cwComplex
    apply (D.labelledCellBasis n).symm.injective
    rw [AddEquiv.symm_apply_apply]
    change standardA2ToricCellularCoordinateBoundary D n x =
      standardA2ToricCellularBoundary n x
    exact DFunLike.congr_fun (h n) x

end StandardA2ToricCentralFiberCWDecomposition

end SphereSixComplex
