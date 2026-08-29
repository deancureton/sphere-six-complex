module

public import SphereSixComplex.Topology.CellularChainModel
public import SphereSixComplex.Topology.SectionSevenLocalEulerCalculation
public import SphereSixComplex.Topology.SectionSevenLocalEulerModelsProof
public import SphereSixComplex.Topology.StandardFourTorusHomologicalModel
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Finite CW models for the Section 7 local Euler calculation

This file states the missing general Euler--Poincaré, fibre-bundle, and finite-cover theorems at
their natural finite-CW level.  It then reduces the seven local values to geometric CW, bundle, and
covering models.  The resulting Section 7 contract contains no homology ranks and no Euler values.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- A homotopy model by a finite CW complex of dimension at most six. -/
public structure FiniteCWModelSix (X : Type) [TopologicalSpace X] where
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
  cellsAboveSix : let _ := topology; let _ := cwComplex
    ∀ n, 6 < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Carrier) n)

namespace FiniteCWModelSix

variable {X : Type} [TopologicalSpace X]

/-- Number of cells in one degree of the chosen finite CW model. -/
public noncomputable def cellCount (M : FiniteCWModelSix X) (n : ℕ) : ℕ := by
  let _ := M.topology
  let _ := M.cwComplex
  let _ := M.finite
  exact Nat.card (Topology.CWComplex.cell (Set.univ : Set M.Carrier) n)

/-- Cellular Euler--Poincaré over the integers.

Reference: [Hat02, Theorem 2.44] (the Euler characteristic equals the alternating sum of the cell
counts).  Truncating the sum at degree six is sound because `FiniteCWModelSix` records that there
are no cells above degree six.  The proof is the rank bookkeeping of
`CellularEulerPoincare.integralHomologyEulerCharacteristicSix_eq_cellSum` on the cellular chain
complex of the chosen carrier. -/
public theorem establishedIntegralCellularEulerPoincareSix (M : FiniteCWModelSix X) :
    integralHomologyEulerCharacteristicSix X =
      (M.cellCount 0 : ℤ) - M.cellCount 1 + M.cellCount 2 - M.cellCount 3 +
        M.cellCount 4 - M.cellCount 5 + M.cellCount 6 := by
  let _ := M.topology
  let _ := M.t2
  let _ := M.cwComplex
  let _ := M.finite
  exact CellularEulerPoincare.integralHomologyEulerCharacteristicSix_eq_cellSum
    M.homotopyEquiv M.cellsAboveSix

/-- Finite generation and the dimension bound are consequences of the cellular chain model, not
extra assumptions: the chain groups are free on finitely many cells, homology is a subquotient of
them, and there are no cells above degree six. -/
public theorem integralHomologyFiniteSix (M : FiniteCWModelSix X) :
    IntegralHomologyFiniteSix X where
  finiteHomology k := by
    let _ := M.topology
    let _ := M.t2
    let _ := M.cwComplex
    let _ := M.finite
    let CM := EstablishedCellularHomology.integralCWCellularChainModel M.Carrier
    have hfin : Finite (Topology.CWComplex.cell (Set.univ : Set M.Carrier) k) :=
      Topology.CWComplex.FiniteType.finite_cell (C := (Set.univ : Set M.Carrier)) k
    have hX : Module.Finite ℤ (CM.chainComplex.X k) :=
      Module.Finite.equiv (CM.cellBasis k).toIntLinearEquiv
    have hhom : Module.Finite ℤ (CM.chainComplex.homology k) :=
      module_finite_homology _ k hX
    have hiso := CM.comparison_homology_isIso k
    have hcar : Module.Finite ℤ (IntegralSingularHomology k M.Carrier) :=
      Module.Finite.equiv (asIso (CM.chainComplex.homologyMap CM.comparison k)
        |>.addCommGroupIsoToAddEquiv).toIntLinearEquiv
    exact Module.Finite.equiv
      (integralSingularHomologyEquivOfHomotopyEquiv k M.homotopyEquiv).symm.toIntLinearEquiv
  homologyAboveDimension k hk := by
    let _ := M.topology
    let _ := M.t2
    let _ := M.cwComplex
    have _hempty : IsEmpty (Topology.CWComplex.cell (Set.univ : Set M.Carrier) k) :=
      M.cellsAboveSix k hk
    have _hcar := subsingleton_integralSingularHomology_of_isEmpty_cell M.Carrier k
    exact ⟨fun _ _ =>
      (integralSingularHomologyEquivOfHomotopyEquiv k M.homotopyEquiv).injective
        (Subsingleton.elim _ _)⟩

end FiniteCWModelSix

private structure FiniteDiscreteCellModel (d : ℕ) where
  model : FiniteCWModelSix (Fin d)
  cellsZero : model.cellCount 0 = d
  cellsOne : model.cellCount 1 = 0
  cellsTwo : model.cellCount 2 = 0
  cellsThree : model.cellCount 3 = 0
  cellsFour : model.cellCount 4 = 0
  cellsFive : model.cellCount 5 = 0
  cellsSix : model.cellCount 6 = 0

private noncomputable def finiteDiscreteCellModel (d : ℕ) : FiniteDiscreteCellModel d := by
  let C : Topology.CWComplex (Set.univ : Set (Fin d)) :=
    Topology.CWComplex.OfDiscreteClosed IsDiscrete.univ isClosed_univ
  letI : Topology.CWComplex (Set.univ : Set (Fin d)) := C
  have F : Topology.CWComplex.Finite (Set.univ : Set (Fin d)) := by
    refine { eventually_isEmpty_cell := ?_, finite_cell := ?_ }
    · rw [Filter.eventually_atTop]
      refine ⟨1, fun n hn ↦ ?_⟩
      change IsEmpty (Topology.CWComplex.cell (Set.univ : Set (Fin d)) n)
      rw [Topology.CWComplex.OfDiscreteClosed_cell IsDiscrete.univ isClosed_univ]
      cases n with
      | zero => omega
      | succ n => infer_instance
    · intro n
      change Finite (Topology.CWComplex.cell (Set.univ : Set (Fin d)) n)
      rw [Topology.CWComplex.OfDiscreteClosed_cell IsDiscrete.univ isClosed_univ]
      cases n <;> infer_instance
  let model : FiniteCWModelSix (Fin d) :=
    { Carrier := Fin d
      topology := inferInstance
      t2 := by dsimp; infer_instance
      homotopyEquiv := by dsimp; exact (Homeomorph.refl (Fin d)).toHomotopyEquiv
      cwComplex := C
      finite := F
      cellsAboveSix := by
        dsimp
        intro n hn
        change IsEmpty (Topology.CWComplex.cell (Set.univ : Set (Fin d)) n)
        rw [Topology.CWComplex.OfDiscreteClosed_cell IsDiscrete.univ isClosed_univ]
        cases n with
        | zero => omega
        | succ n => infer_instance }
  refine ⟨model, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp [FiniteCWModelSix.cellCount, model]
    rw [Topology.CWComplex.OfDiscreteClosed_cell IsDiscrete.univ isClosed_univ]
    simp

private theorem finiteDiscreteEuler (d : ℕ) :
    integralHomologyEulerCharacteristicSix (Fin d) = (d : ℤ) := by
  let M := finiteDiscreteCellModel d
  rw [M.model.establishedIntegralCellularEulerPoincareSix, M.cellsZero, M.cellsOne, M.cellsTwo,
    M.cellsThree, M.cellsFour, M.cellsFive, M.cellsSix]
  norm_num

namespace IntegralHomologyFiniteSix

/-- Homological finiteness and the dimension bound transport through a homotopy equivalence. -/
public theorem homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IntegralHomologyFiniteSix X) (e : X ≃ₕ Y) : IntegralHomologyFiniteSix Y where
  finiteHomology k := by
    let _ : Module.Finite ℤ (IntegralSingularHomology k X) := hX.finiteHomology k
    exact Module.Finite.equiv
      (integralSingularHomologyEquivOfHomotopyEquiv k e).toIntLinearEquiv
  homologyAboveDimension k hk := by
    let h := hX.homologyAboveDimension k hk
    let eH := integralSingularHomologyEquivOfHomotopyEquiv k e
    exact ⟨fun x y ↦ eH.symm.injective (@Subsingleton.elim _ h _ _)⟩

end IntegralHomologyFiniteSix

/-- A finite-CW locally trivial bundle model for a space. -/
public structure FiniteCWBundleModelSix (X : Type) [TopologicalSpace X] where
  Base : Type
  Fiber : Type
  baseTopology : TopologicalSpace Base
  fiberTopology : TopologicalSpace Fiber
  family : Base → Type
  familyTopology : ∀ b, TopologicalSpace (family b)
  totalTopology : TopologicalSpace (Bundle.TotalSpace Fiber family)
  fiberBundle : @FiberBundle Base Fiber baseTopology fiberTopology family totalTopology
    familyTopology
  totalHomotopyEquiv : let _ := baseTopology; let _ := fiberTopology
    let _ := familyTopology; let _ := totalTopology
    X ≃ₕ Bundle.TotalSpace Fiber family
  baseFiniteCW : @FiniteCWModelSix Base baseTopology
  fiberFiniteCW : @FiniteCWModelSix Fiber fiberTopology
  totalHomologyFiniteSix : @IntegralHomologyFiniteSix
    (Bundle.TotalSpace Fiber family) totalTopology

namespace FiniteCWBundleModelSix

variable {X : Type} [TopologicalSpace X]

/-- Euler characteristic is multiplicative for a locally trivial bundle of finite CW complexes.
This is the standard Serre-spectral-sequence Euler theorem missing from Mathlib. -/
public axiom establishedEulerMultiplicativity (M : FiniteCWBundleModelSix X) :
    let _ := M.baseTopology
    let _ := M.fiberTopology
    integralHomologyEulerCharacteristicSix X =
      integralHomologyEulerCharacteristicSix M.Base *
        integralHomologyEulerCharacteristicSix M.Fiber

public theorem integralHomologyFiniteSix (M : FiniteCWBundleModelSix X) :
    IntegralHomologyFiniteSix X := by
  let _ := M.baseTopology
  let _ := M.fiberTopology
  let _ := M.familyTopology
  let _ := M.totalTopology
  exact M.totalHomologyFiniteSix.homotopyEquiv M.totalHomotopyEquiv.symm

end FiniteCWBundleModelSix

/-- A finite-CW bundle whose model fibre has the standard four-torus CW structure. -/
public structure FourTorusBundleModel (X : Type) [TopologicalSpace X] where
  toFiniteCWBundleModelSix : FiniteCWBundleModelSix X
  fiberHomology : @FourTorusHomologicalModel toFiniteCWBundleModelSix.Fiber
    toFiniteCWBundleModelSix.fiberTopology

namespace FourTorusBundleModel

variable {X : Type} [TopologicalSpace X]

public theorem integralHomologyFiniteSix (M : FourTorusBundleModel X) :
    IntegralHomologyFiniteSix X :=
  M.toFiniteCWBundleModelSix.integralHomologyFiniteSix

/-- Every finite-CW bundle with four-torus fibre has Euler characteristic zero. -/
public theorem euler_eq_zero (M : FourTorusBundleModel X) :
    integralHomologyEulerCharacteristicSix X = 0 := by
  let _ := M.toFiniteCWBundleModelSix.baseTopology
  let _ := M.toFiniteCWBundleModelSix.fiberTopology
  rw [M.toFiniteCWBundleModelSix.establishedEulerMultiplicativity,
    M.fiberHomology.euler_eq_zero, mul_zero]

end FourTorusBundleModel

/-- A constant-degree finite covering between finite CW-type spaces. -/
public structure FiniteCoverModelSix (X : Type) [TopologicalSpace X] where
  Cover : Type
  coverTopology : TopologicalSpace Cover
  projection : let _ := coverTopology; C(Cover, X)
  isCovering : let _ := coverTopology; IsCoveringMap projection
  degree : ℕ
  degree_pos : 0 < degree
  fiberCardinality : let _ := coverTopology
    ∀ x, Nat.card {y : Cover // projection y = x} = degree
  coverHomologyFiniteSix : @IntegralHomologyFiniteSix Cover coverTopology
  quotientFiniteCW : FiniteCWModelSix X

namespace FiniteCoverModelSix

variable {X : Type} [TopologicalSpace X]

private abbrev coverFiber (M : FiniteCoverModelSix X) (x : X) : Type :=
  ↥(M.projection ⁻¹' ({x} : Set X))

private noncomputable def coverFiberEquivEq (M : FiniteCoverModelSix X) (x : X) :
    coverFiber M x ≃ {y : M.Cover // M.projection y = x} :=
  Equiv.setCongr (show M.projection ⁻¹' ({x} : Set X) =
    {y : M.Cover | M.projection y = x} by ext y; simp)

private noncomputable def fiberHomeomorphFin (M : FiniteCoverModelSix X) (x : X) :
    let _ := M.coverTopology
    coverFiber M x ≃ₜ Fin M.degree := by
  let _ := M.coverTopology
  have hcardNat : Nat.card (coverFiber M x) = M.degree := by
    rw [Nat.card_congr (coverFiberEquivEq M x), M.fiberCardinality x]
  have hpos : 0 < Nat.card (coverFiber M x) := hcardNat.symm ▸ M.degree_pos
  letI : Nonempty (coverFiber M x) := (Nat.card_pos_iff.mp hpos).1
  letI : Finite (coverFiber M x) := (Nat.card_pos_iff.mp hpos).2
  letI : Fintype (coverFiber M x) := Fintype.ofFinite _
  have hcard : Fintype.card (coverFiber M x) = M.degree := by
    rw [← Nat.card_eq_fintype_card, hcardNat]
  haveI : DiscreteTopology (coverFiber M x) :=
    (M.isCovering x).discreteTopology_fiber
  exact ((Fintype.equivFin (coverFiber M x)).trans
    (Fin.castOrderIso hcard).toEquiv).toHomeomorphOfDiscrete

private noncomputable def coverTotalEquiv (M : FiniteCoverModelSix X) :
    Bundle.TotalSpace (Fin M.degree) (coverFiber M) ≃ M.Cover where
  toFun z := z.2.1
  invFun y := ⟨M.projection y, ⟨y, by simp⟩⟩
  left_inv z := by
    rcases z with ⟨x, ⟨y, hy⟩⟩
    have h : M.projection y = x := by simpa using hy
    subst x
    rfl
  right_inv _ := rfl

private noncomputable def coverAsBundleModel (M : FiniteCoverModelSix X) :
    let _ := M.coverTopology
    FiniteCWBundleModelSix M.Cover := by
  let _ := M.coverTopology
  let family := coverFiber M
  let familyTopology : ∀ x, TopologicalSpace (family x) := fun _ ↦ inferInstance
  letI : ∀ x, TopologicalSpace (family x) := familyTopology
  let totalEquiv : Bundle.TotalSpace (Fin M.degree) family ≃ M.Cover := coverTotalEquiv M
  let totalTopology : TopologicalSpace (Bundle.TotalSpace (Fin M.degree) family) :=
    TopologicalSpace.induced totalEquiv inferInstance
  letI : TopologicalSpace (Bundle.TotalSpace (Fin M.degree) family) := totalTopology
  let totalHomeomorph : Bundle.TotalSpace (Fin M.degree) family ≃ₜ M.Cover :=
    totalEquiv.toHomeomorphOfIsInducing (Topology.IsInducing.induced _)
  let trivAtData (x : X) :
      {t : Bundle.Trivialization (Fin M.degree)
          (fun z : Bundle.TotalSpace (Fin M.degree) family ↦ z.proj) //
        x ∈ t.baseSet} := by
    have hcardNat : Nat.card (coverFiber M x) = M.degree := by
      rw [Nat.card_congr (coverFiberEquivEq M x), M.fiberCardinality x]
    have hpos : 0 < Nat.card (coverFiber M x) := hcardNat.symm ▸ M.degree_pos
    letI : Nonempty (coverFiber M x) := (Nat.card_pos_iff.mp hpos).1
    letI : DiscreteTopology (coverFiber M x) :=
      (M.isCovering x).discreteTopology_fiber
    let t := ((M.isCovering x).toTrivialization.transFiberHomeomorph
      (fiberHomeomorphFin M x)).compHomeomorph totalHomeomorph
    have hproj :
        M.projection ∘ (totalHomeomorph : Bundle.TotalSpace (Fin M.degree) family → M.Cover) =
          (fun z : Bundle.TotalSpace (Fin M.degree) family ↦ z.proj) := by
      funext z
      change M.projection z.2.1 = z.proj
      exact Set.mem_singleton_iff.mp z.2.2
    let t' : Bundle.Trivialization (Fin M.degree)
        (fun z : Bundle.TotalSpace (Fin M.degree) family ↦ z.proj) :=
      { t with
        source_eq := calc
          t.source = (M.projection ∘ totalHomeomorph) ⁻¹' t.baseSet := t.source_eq
          _ = (fun z : Bundle.TotalSpace (Fin M.degree) family ↦ z.proj) ⁻¹' t.baseSet := by
            ext z
            change (M.projection ∘ totalHomeomorph) z ∈ t.baseSet ↔ z.proj ∈ t.baseSet
            rw [congrFun hproj z]
        proj_toFun := fun z hz ↦ (t.proj_toFun z hz).trans (congrFun hproj z) }
    refine ⟨t', ?_⟩
    change x ∈ t.baseSet
    change x ∈ (M.isCovering x).toTrivialization.baseSet
    exact (M.isCovering x).mem_toTrivialization_baseSet
  let trivAt (x : X) := (trivAtData x).1
  let bundle : FiberBundle (Fin M.degree) family :=
    { totalSpaceMk_isInducing' := fun x ↦ by
        refine (totalHomeomorph.isInducing.of_comp_iff).mp ?_
        have hs : @Topology.IsInducing (family x) M.Cover (familyTopology x)
            inferInstance Subtype.val := by
          dsimp [familyTopology, family]
          exact Topology.IsInducing.subtypeVal
        have hfun :
            (totalHomeomorph : Bundle.TotalSpace (Fin M.degree) family → M.Cover) ∘
                (Bundle.TotalSpace.mk x) =
              (Subtype.val : family x → M.Cover) := rfl
        rw [hfun]
        exact hs
      trivializationAtlas' := Set.range trivAt
      trivializationAt' := trivAt
      mem_baseSet_trivializationAt' := fun x ↦ (trivAtData x).2
      trivialization_mem_atlas' := fun x ↦ ⟨x, rfl⟩ }
  exact
    { Base := X
      Fiber := Fin M.degree
      baseTopology := inferInstance
      fiberTopology := inferInstance
      family := family
      familyTopology := familyTopology
      totalTopology := totalTopology
      fiberBundle := bundle
      totalHomotopyEquiv := totalHomeomorph.symm.toHomotopyEquiv
      baseFiniteCW := M.quotientFiniteCW
      fiberFiniteCW := (finiteDiscreteCellModel M.degree).model
      totalHomologyFiniteSix :=
        M.coverHomologyFiniteSix.homotopyEquiv totalHomeomorph.symm.toHomotopyEquiv }

/-- Euler characteristic multiplies by the degree of a finite covering. -/
public theorem establishedEulerMultiplicativity (M : FiniteCoverModelSix X) :
    let _ := M.coverTopology
    integralHomologyEulerCharacteristicSix M.Cover =
      (M.degree : ℤ) * integralHomologyEulerCharacteristicSix X := by
  let _ := M.coverTopology
  have h := (coverAsBundleModel M).establishedEulerMultiplicativity
  dsimp only at h
  change integralHomologyEulerCharacteristicSix M.Cover =
    integralHomologyEulerCharacteristicSix X *
      integralHomologyEulerCharacteristicSix (Fin M.degree) at h
  rw [finiteDiscreteEuler] at h
  simpa [mul_comm] using h

end FiniteCoverModelSix

/-- A finite quotient of a four-torus, expressed by its actual finite covering projection. -/
public structure FiniteFourTorusCoverModel (X : Type) [TopologicalSpace X] where
  toFiniteCoverModelSix : FiniteCoverModelSix X
  coverHomology : @FourTorusHomologicalModel toFiniteCoverModelSix.Cover
    toFiniteCoverModelSix.coverTopology

namespace FiniteFourTorusCoverModel

variable {X : Type} [TopologicalSpace X]

public theorem integralHomologyFiniteSix (M : FiniteFourTorusCoverModel X) :
    IntegralHomologyFiniteSix X :=
  M.toFiniteCoverModelSix.quotientFiniteCW.integralHomologyFiniteSix

/-- A finite free quotient of a four-torus has Euler characteristic zero. -/
public theorem euler_eq_zero (M : FiniteFourTorusCoverModel X) :
    integralHomologyEulerCharacteristicSix X = 0 := by
  let _ := M.toFiniteCoverModelSix.coverTopology
  have h := M.toFiniteCoverModelSix.establishedEulerMultiplicativity
  dsimp only at h
  rw [M.coverHomology.euler_eq_zero] at h
  have hdegree : (M.toFiniteCoverModelSix.degree : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt M.toFiniteCoverModelSix.degree_pos)
  exact (mul_eq_zero.mp h.symm).resolve_left hdegree

end FiniteFourTorusCoverModel

/-- The source CW decomposition of the cusp fibre: the three rational curves in the double locus
share two vertices and contribute three edges and three faces; the complement contributes one
relative 2-cell, two relative 3-cells, and one relative 4-cell. -/
public structure CuspToricCellModel (X : Type) [TopologicalSpace X] where
  toFiniteCWModelSix : FiniteCWModelSix X
  cellsZero : toFiniteCWModelSix.cellCount 0 = 2
  cellsOne : toFiniteCWModelSix.cellCount 1 = 3
  cellsTwo : toFiniteCWModelSix.cellCount 2 = 4
  cellsThree : toFiniteCWModelSix.cellCount 3 = 2
  cellsFour : toFiniteCWModelSix.cellCount 4 = 1
  cellsFive : toFiniteCWModelSix.cellCount 5 = 0
  cellsSix : toFiniteCWModelSix.cellCount 6 = 0

namespace CuspToricCellModel

variable {X : Type} [TopologicalSpace X]

public theorem integralHomologyFiniteSix (M : CuspToricCellModel X) :
    IntegralHomologyFiniteSix X :=
  M.toFiniteCWModelSix.integralHomologyFiniteSix

/-- The toric cusp cell decomposition has Euler characteristic two. -/
public theorem euler_eq_two (M : CuspToricCellModel X) :
    integralHomologyEulerCharacteristicSix X = 2 := by
  rw [M.toFiniteCWModelSix.establishedIntegralCellularEulerPoincareSix,
    M.cellsZero, M.cellsOne, M.cellsTwo, M.cellsThree, M.cellsFour,
    M.cellsFive, M.cellsSix]
  norm_num

end CuspToricCellModel

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open Topology.PaperEllipticFillingRadialRetraction

variable (A : PaperAnalyticData)

/-- Exact geometric models still required for the seven local Section 7 spaces.  The fields are
CW decompositions, locally trivial bundles, finite covering projections, and the already stated
deformation retractions; no field stores a homology rank or Euler characteristic. -/
public structure SectionSevenLocalEulerModels where
  cuspRetraction : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness
  orderThreeRadialChart : OrderThreeAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderThree.radius
  orderFourRadialChart : OrderFourAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderFour.radius
  centralBundle : FourTorusBundleModel A.openEmbeddingStarData.central
  cuspCells : CuspToricCellModel
    (cuspRetraction.quotientCentralFiber A.starCuspWitness)
  orderThreeCover : FiniteFourTorusCoverModel
    (OrderThreeReducedCentralFiber A.periods)
  orderFourCover : FiniteFourTorusCoverModel
    (OrderFourReducedCentralFiber A.periods)
  collarBundle : ∀ i : Fin 3, FourTorusBundleModel
    (A.openEmbeddingStarData.collarSource i)

namespace SectionSevenLocalEulerModels

/-- All seven local spaces have finite integral homology supported in degrees at most six. -/
public theorem localIntegralHomologyFiniteSix (M : SectionSevenLocalEulerModels A) :
    IntegralHomologyFiniteSix A.openEmbeddingStarData.central ∧
    (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.filling i)) ∧
    (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.collarSource i)) := by
  refine ⟨M.centralBundle.integralHomologyFiniteSix, ?_, fun i ↦
    (M.collarBundle i).integralHomologyFiniteSix⟩
  intro i
  fin_cases i
  · change IntegralHomologyFiniteSix (actualLocalCuspFilling A.starCuspWitness)
    exact M.cuspCells.integralHomologyFiniteSix.homotopyEquiv
      (M.cuspRetraction.quotientCentralFiberHomotopyEquiv A.starCuspWitness).symm
  · change IntegralHomologyFiniteSix
      (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)
    exact M.orderThreeCover.integralHomologyFiniteSix.homotopyEquiv
      (orderThreeVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
        A.starSeparation.orderThree.radius M.orderThreeRadialChart).symm
  · change IntegralHomologyFiniteSix
      (A.OrderFourVaryingFilling A.starSeparation.orderFour.radius)
    exact M.orderFourCover.integralHomologyFiniteSix.homotopyEquiv
      (orderFourVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
        A.starSeparation.orderFour.radius M.orderFourRadialChart).symm

/-- The exact Section 7 local Euler calculation, derived from geometric models. -/
public theorem sectionSevenLocalEulerExpression_eq_two (M : SectionSevenLocalEulerModels A) :
    A.openEmbeddingStarData.sectionSevenLocalEulerExpression = 2 :=
  A.sectionSevenLocalEulerExpression_eq_two_of_modelCalculations
    M.cuspRetraction M.orderThreeRadialChart M.orderFourRadialChart
    M.centralBundle.euler_eq_zero M.cuspCells.euler_eq_two
    M.orderThreeCover.euler_eq_zero M.orderFourCover.euler_eq_zero
    (fun i ↦ (M.collarBundle i).euler_eq_zero)

end SectionSevenLocalEulerModels

end Geometry.PaperAnalyticData

end SphereSixComplex
