module

public import SphereSixComplex.Topology.MayerVietoris
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Classical integral cellular homology

The trusted statement in this module is the standard skeletal-relative construction. Its
degree-`n` cellular group is `H_n(X^n, X^{n-1}; ℤ)`, its differential is the connecting map of
successive skeleta, and its basis vectors are the relative fundamental classes carried by the
chosen characteristic maps. Cellular maps act on the relative groups, and cellular homology is
naturally isomorphic to integral singular homology.

This fixes both choices left open by a merely objectwise chain complex: the differential is the
attaching-degree differential in the characteristic-cell basis, and the comparison with singular
homology is natural. The final accessor retains the old objectwise API for downstream code.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open Topology

namespace SphereSixComplex

public noncomputable abbrev CWIntegralSingularChainComplexObj (X : TopCat) :
    ChainComplex AddCommGrpCat ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj X

public noncomputable def cwIntegralSingularChainMapObj {X Y : TopCat} (f : X ⟶ Y) :
    CWIntegralSingularChainComplexObj X ⟶ CWIntegralSingularChainComplexObj Y :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map f

/-- Relative integral singular chains, defined as a cokernel. -/
public noncomputable def CWRelativeIntegralSingularChainComplex {X Y : TopCat} (i : X ⟶ Y) :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel (cwIntegralSingularChainMapObj i)

public noncomputable def cwRelativeIntegralSingularChainProjection {X Y : TopCat} (i : X ⟶ Y) :
    CWIntegralSingularChainComplexObj Y ⟶ CWRelativeIntegralSingularChainComplex i :=
  cokernel.π (cwIntegralSingularChainMapObj i)

public noncomputable def cwRelativeIntegralSingularShortComplex {X Y : TopCat} (i : X ⟶ Y) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (cwIntegralSingularChainMapObj i)
    (cwRelativeIntegralSingularChainProjection i)
    (cokernel.condition (cwIntegralSingularChainMapObj i))

public theorem cwRelativeIntegralSingularShortComplex_shortExact
    {X Y : TopCat} (i : X ⟶ Y) [Mono i] :
    (cwRelativeIntegralSingularShortComplex i).ShortExact := by
  let _ : Mono (cwIntegralSingularChainMapObj i) := by
    dsimp [cwIntegralSingularChainMapObj]
    infer_instance
  exact
    { exact := ShortComplex.exact_cokernel (cwIntegralSingularChainMapObj i)
      mono_f := by
        dsimp [cwRelativeIntegralSingularShortComplex]
        infer_instance
      epi_g := by
        dsimp [cwRelativeIntegralSingularShortComplex,
          cwRelativeIntegralSingularChainProjection]
        constructor
        intro Z g h w
        exact Cofork.IsColimit.hom_ext
          (cokernelIsCokernel (cwIntegralSingularChainMapObj i)) w }

public noncomputable def cwRelativeIntegralSingularBoundary
    {X Y : TopCat} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (CWRelativeIntegralSingularChainComplex i).homology (n + 1) ⟶
      (CWIntegralSingularChainComplexObj X).homology n :=
  (cwRelativeIntegralSingularShortComplex_shortExact i).δ (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by omega))

/-- A map of topological pairs. -/
public structure CWTopologicalPairMap {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y) where
  left : A ⟶ B
  right : X ⟶ Y
  comm : i ≫ right = left ≫ j

public noncomputable def cwRelativeIntegralSingularChainMapOfPair
    {A X B Y : TopCat} {i : A ⟶ X} {j : B ⟶ Y}
    (f : CWTopologicalPairMap i j) :
    CWRelativeIntegralSingularChainComplex i ⟶ CWRelativeIntegralSingularChainComplex j :=
  cokernel.desc (cwIntegralSingularChainMapObj i)
    (cwIntegralSingularChainMapObj f.right ≫ cwRelativeIntegralSingularChainProjection j) (by
      have hmap :
          cwIntegralSingularChainMapObj i ≫ cwIntegralSingularChainMapObj f.right =
            cwIntegralSingularChainMapObj f.left ≫ cwIntegralSingularChainMapObj j := by
        dsimp only [cwIntegralSingularChainMapObj]
        rw [← Functor.map_comp, f.comm, Functor.map_comp]
      rw [← Category.assoc, hmap, Category.assoc]
      change cwIntegralSingularChainMapObj f.left ≫
        (cwIntegralSingularChainMapObj j ≫
          cokernel.π (cwIntegralSingularChainMapObj j)) = 0
      rw [cokernel.condition, comp_zero])

/-- The closed coordinate disk used by Mathlib's CW characteristic maps. -/
public abbrev CWCharacteristicClosedBall (n : ℕ) :=
  ↥(Metric.closedBall (0 : Fin n → ℝ) 1)

/-- The boundary sphere of the coordinate disk. -/
public abbrev CWCharacteristicBoundarySphere (n : ℕ) :=
  ↥(Metric.sphere (0 : Fin n → ℝ) 1)

public def cwCharacteristicBoundaryInclusion (n : ℕ) :
    TopCat.of (CWCharacteristicBoundarySphere n) ⟶
      TopCat.of (CWCharacteristicClosedBall n) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, le_of_eq x.2⟩, by fun_prop⟩

public instance (n : ℕ) : Mono (cwCharacteristicBoundaryInclusion n) := by
  rw [TopCat.mono_iff_injective]
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : CWCharacteristicClosedBall n ↦ z.1) h

/-- The union of cells of dimension strictly below `n`. -/
public abbrev IntegralCWSkeletonLT
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :=
  {x : X // x ∈
    (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X)}

public def integralCWSkeletonInclusion
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    TopCat.of (IntegralCWSkeletonLT X n) ⟶ TopCat.of (IntegralCWSkeletonLT X (n + 1)) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, Topology.RelCWComplex.skeletonLT_mono
      (by exact_mod_cast Nat.le_succ n) x.2⟩, by fun_prop⟩

public instance (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Mono (integralCWSkeletonInclusion X n) := by
  rw [TopCat.mono_iff_injective]
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : IntegralCWSkeletonLT X (n + 1) ↦ z.1) h

/-- The canonical relative group `H_n(X^n, X^{n-1}; ℤ)`. -/
public abbrev IntegralCWRelativeCellObject
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : AddCommGrpCat :=
  (CWRelativeIntegralSingularChainComplex (integralCWSkeletonInclusion X n)).homology n

/-- The canonical cellular differential through successive relative-homology groups. -/
public noncomputable def integralCWRelativeBoundary
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    IntegralCWRelativeCellObject X (n + 1) ⟶ IntegralCWRelativeCellObject X n :=
  cwRelativeIntegralSingularBoundary (integralCWSkeletonInclusion X (n + 1)) n ≫
    HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X n)) n

/-- A characteristic map regarded as a map of the disk pair into consecutive skeleta. -/
public structure IntegralCWCharacteristicPairMap
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) n) where
  boundaryMap : TopCat.of (CWCharacteristicBoundarySphere n) ⟶
    TopCat.of (IntegralCWSkeletonLT X n)
  diskMap : TopCat.of (CWCharacteristicClosedBall n) ⟶
    TopCat.of (IntegralCWSkeletonLT X (n + 1))
  comm : cwCharacteristicBoundaryInclusion n ≫ diskMap =
    boundaryMap ≫ integralCWSkeletonInclusion X n
  disk_apply : ∀ x, (diskMap x).1 = Topology.CWComplex.map n e x.1
  boundary_apply : ∀ x, (boundaryMap x).1 = Topology.CWComplex.map n e x.1

namespace IntegralCWCharacteristicPairMap

public noncomputable def relativeChainMap
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] {n : ℕ}
    {e : Topology.CWComplex.cell (Set.univ : Set X) n}
    (P : IntegralCWCharacteristicPairMap X n e) :
    CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion n) ⟶
      CWRelativeIntegralSingularChainComplex (integralCWSkeletonInclusion X n) :=
  cwRelativeIntegralSingularChainMapOfPair
    { left := P.boundaryMap
      right := P.diskMap
      comm := P.comm }

end IntegralCWCharacteristicPairMap

/-- A cellular map preserves every stage of the skeletal filtration. -/
public def IsIntegralCWCellularMap
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] (f : C(X, Y)) : Prop :=
  ∀ n : ℕ, Set.MapsTo f
    (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X)
    (Topology.RelCWComplex.skeletonLT (Set.univ : Set Y) (n : ℕ∞) : Set Y)

public theorem isIntegralCWCellularMap_id
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    IsIntegralCWCellularMap (ContinuousMap.id X) := by
  intro n x hx
  exact hx

public theorem IsIntegralCWCellularMap.comp
    {X Y Z : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    [TopologicalSpace Z] [T2Space Z]
    [Topology.CWComplex (Set.univ : Set Z)]
    {f : C(X, Y)} {g : C(Y, Z)}
    (hg : IsIntegralCWCellularMap g) (hf : IsIntegralCWCellularMap f) :
    IsIntegralCWCellularMap (g.comp f) := by
  intro n x hx
  exact hg n (hf n hx)

public def integralCWSkeletonMap
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsIntegralCWCellularMap f) (n : ℕ) :
    TopCat.of (IntegralCWSkeletonLT X n) ⟶ TopCat.of (IntegralCWSkeletonLT Y n) :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x.1, hf n x.2⟩, by fun_prop⟩

public noncomputable def integralCWRelativeCellMap
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsIntegralCWCellularMap f) (n : ℕ) :
    IntegralCWRelativeCellObject X n ⟶ IntegralCWRelativeCellObject Y n :=
  HomologicalComplex.homologyMap
    (cwRelativeIntegralSingularChainMapOfPair
      { left := integralCWSkeletonMap f hf n
        right := integralCWSkeletonMap f hf (n + 1)
        comm := by ext x; rfl }) n

public noncomputable def integralCWSkeletalChainComplex
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h : ∀ n, integralCWRelativeBoundary X (n + 1) ≫ integralCWRelativeBoundary X n = 0) :
    ChainComplex AddCommGrpCat ℕ :=
  ChainComplex.of (fun n ↦ IntegralCWRelativeCellObject X n)
    (fun n ↦ integralCWRelativeBoundary X n) (by
      intro n
      exact h n)

/-- A dimension-independent, characteristic-map-normalized, functorial form of the classical
integral cellular-homology theorem for Hausdorff CW complexes. -/
public structure IntegralCWCellularHomologyFoundation where
  diskOrientation : ∀ n,
    (CWRelativeIntegralSingularChainComplex
      (cwCharacteristicBoundaryInclusion n)).homology n ≃+ ℤ
  characteristicPair : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) n),
      IntegralCWCharacteristicPairMap X n e
  boundary_comp_zero : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ),
      integralCWRelativeBoundary X (n + 1) ≫ integralCWRelativeBoundary X n = 0
  cellBasis : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ),
      (Topology.CWComplex.cell (Set.univ : Set X) n →₀ ℤ) ≃+
        IntegralCWRelativeCellObject X n
  cellBasis_single : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) n),
      cellBasis X n (Finsupp.single e 1) =
        ConcreteCategory.hom
          ((CWRelativeIntegralSingularChainComplex
            (cwCharacteristicBoundaryInclusion n)).homologyMap
              (characteristicPair X n e).relativeChainMap n)
          ((diskOrientation n).symm 1)
  boundary_coefficient_eq_attaching_degree :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set X) n),
      ((cellBasis X n).symm
        (ConcreteCategory.hom (integralCWRelativeBoundary X n)
          (cellBasis X (n + 1) (Finsupp.single e 1)))) e' =
      ((cellBasis X n).symm
        (ConcreteCategory.hom
          (HomologicalComplex.homologyMap
              (cwIntegralSingularChainMapObj
                (characteristicPair X (n + 1) e).boundaryMap) n ≫
            HomologicalComplex.homologyMap
              (cwRelativeIntegralSingularChainProjection
                (integralCWSkeletonInclusion X n)) n)
          (ConcreteCategory.hom
            (cwRelativeIntegralSingularBoundary
              (cwCharacteristicBoundaryInclusion (n + 1)) n)
            ((diskOrientation (n + 1)).symm 1)))) e'
  homologyEquiv : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ),
      (integralCWSkeletalChainComplex X (boundary_comp_zero X)).homology n ≃+
        IntegralSingularHomology n X
  cellularChainMap : ∀ {X Y : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (_hf : IsIntegralCWCellularMap f),
      integralCWSkeletalChainComplex X (boundary_comp_zero X) ⟶
        integralCWSkeletalChainComplex Y (boundary_comp_zero Y)
  cellularChainMap_f : ∀ {X Y : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsIntegralCWCellularMap f) (n : ℕ),
      (cellularChainMap f hf).f n = integralCWRelativeCellMap f hf n
  homologyEquiv_natural : ∀ {X Y : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsIntegralCWCellularMap f) (n : ℕ),
      (integralCWSkeletalChainComplex X (boundary_comp_zero X)).homologyMap
          (cellularChainMap f hf) n ≫ (homologyEquiv Y n).toAddCommGrpIso.hom =
        (homologyEquiv X n).toAddCommGrpIso.hom ≫
          ((singularHomologyFunctor AddCommGrpCat n).obj
            (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)
  cellularChainMap_id : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)],
      cellularChainMap (ContinuousMap.id X) (isIntegralCWCellularMap_id X) =
        𝟙 (integralCWSkeletalChainComplex X (boundary_comp_zero X))
  cellularChainMap_comp : ∀ {X Y Z : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    [TopologicalSpace Z] [T2Space Z]
    [Topology.CWComplex (Set.univ : Set Z)]
    (f : C(X, Y)) (g : C(Y, Z))
    (hf : IsIntegralCWCellularMap f) (hg : IsIntegralCWCellularMap g),
      cellularChainMap (g.comp f) (hg.comp hf) =
        cellularChainMap f hf ≫ cellularChainMap g hg

/-- The exact accepted classical theorem. It is independent of dimension, finite type, and the
application to the toric cusp or six-sphere. -/
public axiom integralCWCellularHomologyFoundation :
  IntegralCWCellularHomologyFoundation

/-- The objectwise content retained for existing consumers. -/
public structure IntegralCWCellularHomologyModel
    (Y : Type) [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)] where
  chainComplex : ChainComplex AddCommGrpCat ℕ
  cellBasis : ∀ n,
    (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ) ≃+ chainComplex.X n
  homologyEquiv : ∀ n,
    chainComplex.homology n ≃+ IntegralSingularHomology n Y

namespace IntegralCWCellularHomologyFoundation

public noncomputable def objectwiseModel
    (T : IntegralCWCellularHomologyFoundation)
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] :
    IntegralCWCellularHomologyModel Y where
  chainComplex := integralCWSkeletalChainComplex Y
    (IntegralCWCellularHomologyFoundation.boundary_comp_zero T Y)
  cellBasis := IntegralCWCellularHomologyFoundation.cellBasis T Y
  homologyEquiv := IntegralCWCellularHomologyFoundation.homologyEquiv T Y

/-- The coefficient of one cell in the boundary of the positively oriented characteristic class
of a cell one dimension higher. -/
public noncomputable def attachingDegree
    (T : IntegralCWCellularHomologyFoundation)
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set Y) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set Y) n) : ℤ :=
  (IntegralCWCellularHomologyFoundation.cellBasis T Y n).symm
    (ConcreteCategory.hom (integralCWRelativeBoundary Y n)
      (IntegralCWCellularHomologyFoundation.cellBasis T Y (n + 1)
        (Finsupp.single e 1))) e'

/-- The homological degree of the actual attaching-sphere map, read in the oriented coordinate
of a target cell. -/
public noncomputable def homologicalAttachingMapDegree
    (T : IntegralCWCellularHomologyFoundation)
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set Y) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set Y) n) : ℤ :=
  (IntegralCWCellularHomologyFoundation.cellBasis T Y n).symm
    (ConcreteCategory.hom
      (HomologicalComplex.homologyMap
          (cwIntegralSingularChainMapObj
            (IntegralCWCellularHomologyFoundation.characteristicPair
              T Y (n + 1) e).boundaryMap) n ≫
        HomologicalComplex.homologyMap
          (cwRelativeIntegralSingularChainProjection
            (integralCWSkeletonInclusion Y n)) n)
      (ConcreteCategory.hom
        (cwRelativeIntegralSingularBoundary
          (cwCharacteristicBoundaryInclusion (n + 1)) n)
        ((IntegralCWCellularHomologyFoundation.diskOrientation T (n + 1)).symm 1))) e'

public theorem attachingDegree_eq_homologicalAttachingMapDegree
    (T : IntegralCWCellularHomologyFoundation)
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set Y) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set Y) n) :
    T.attachingDegree Y n e e' = T.homologicalAttachingMapDegree Y n e e' :=
  IntegralCWCellularHomologyFoundation.boundary_coefficient_eq_attaching_degree
    T Y n e e'

end IntegralCWCellularHomologyFoundation

namespace EstablishedCellularHomology

/-- The old accessor, now derived from the single functorial skeletal-relative foundation. -/
public noncomputable def integralCWCellularHomologyModel
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] :
    IntegralCWCellularHomologyModel Y :=
  IntegralCWCellularHomologyFoundation.objectwiseModel
    integralCWCellularHomologyFoundation Y

end EstablishedCellularHomology

end SphereSixComplex

end

end
