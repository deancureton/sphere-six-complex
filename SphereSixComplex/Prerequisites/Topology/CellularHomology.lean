module

public import SphereSixComplex.Prerequisites.Topology.MayerVietoris
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Classical integral cellular homology

The trusted statement in this module is the standard skeletal-relative construction. Its
degree-`n` cellular group is `H_n(X^n, X^{n-1}; ℤ)`, its differential is the connecting map of
successive skeleta, and its basis vectors are the relative fundamental classes carried by the
chosen characteristic maps. Cellular maps act on the relative groups, and cellular homology is
naturally isomorphic to integral singular homology. The comparison agrees with the inclusion
of each skeleton on its absolute homology, through the relative cycle map.

This fixes both choices left open by a merely objectwise chain complex: the differential is the
attaching-degree differential in the characteristic-cell basis, and the comparison with singular
homology is normalized on skeletal cycles, as in Hatcher, Theorem 2.35 and its proof (p. 140).
Naturality alone would allow negating every comparison isomorphism. The final accessor retains
the old objectwise API for downstream code.

Source: https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open Topology

namespace SphereSixComplex

public noncomputable abbrev cwIntegralSingularChainComplexObj (X : TopCat) :
    ChainComplex AddCommGrpCat ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj X

public noncomputable def cwIntegralSingularChainMapObj {X Y : TopCat} (f : X ⟶ Y) :
    cwIntegralSingularChainComplexObj X ⟶ cwIntegralSingularChainComplexObj Y :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map f

/-- Relative integral singular chains, defined as a cokernel. -/
public noncomputable def cwRelativeIntegralSingularChainComplex {X Y : TopCat} (i : X ⟶ Y) :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel (cwIntegralSingularChainMapObj i)

public noncomputable def cwRelativeIntegralSingularChainProjection {X Y : TopCat} (i : X ⟶ Y) :
    cwIntegralSingularChainComplexObj Y ⟶ cwRelativeIntegralSingularChainComplex i :=
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
    (cwRelativeIntegralSingularChainComplex i).homology (n + 1) ⟶
      (cwIntegralSingularChainComplexObj X).homology n :=
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
    cwRelativeIntegralSingularChainComplex i ⟶ cwRelativeIntegralSingularChainComplex j :=
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
public abbrev integralCWRelativeCellObject
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : AddCommGrpCat :=
  (cwRelativeIntegralSingularChainComplex (integralCWSkeletonInclusion X n)).homology n

/-- The canonical cellular differential through successive relative-homology groups. -/
public noncomputable def integralCWRelativeBoundary
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    integralCWRelativeCellObject X (n + 1) ⟶ integralCWRelativeCellObject X n :=
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
    cwRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion n) ⟶
      cwRelativeIntegralSingularChainComplex (integralCWSkeletonInclusion X n) :=
  cwRelativeIntegralSingularChainMapOfPair
    { left := P.boundaryMap
      right := P.diskMap
      comm := P.comm }

end IntegralCWCharacteristicPairMap

public def integralCWCharacteristicPairMap
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) n) :
    IntegralCWCharacteristicPairMap X n e where
  boundaryMap := TopCat.ofHom
    ⟨fun x : CWCharacteristicBoundarySphere n ↦ ⟨Topology.CWComplex.map n e x.1,
      Topology.RelCWComplex.cellFrontier_subset_skeletonLT n e ⟨x.1, x.2, rfl⟩⟩,
      by
        apply Continuous.subtype_mk
        exact ((Topology.CWComplex.continuousOn n e).mono
          Metric.sphere_subset_closedBall).domRestrict⟩
  diskMap := TopCat.ofHom
    ⟨fun x : CWCharacteristicClosedBall n ↦ ⟨Topology.CWComplex.map n e x.1,
      by
        have h := Topology.CWComplex.closedCell_subset_skeletonLT
          (C := (Set.univ : Set X)) n e ⟨x.1, x.2, rfl⟩
        rw [show ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 by simp]
        exact h⟩,
      by
        apply Continuous.subtype_mk
        exact (Topology.CWComplex.continuousOn n e).domRestrict⟩
  comm := by rfl
  disk_apply := fun _ ↦ rfl
  boundary_apply := fun _ ↦ rfl

public theorem integralCWRelativeBoundary_comp_self
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    integralCWRelativeBoundary X (n + 1) ≫ integralCWRelativeBoundary X n = 0 := by
  have h : HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainProjection
        (integralCWSkeletonInclusion X (n + 1))) (n + 1) ≫
      cwRelativeIntegralSingularBoundary (integralCWSkeletonInclusion X (n + 1)) n = 0 :=
    ShortComplex.ShortExact.comp_δ
      (cwRelativeIntegralSingularShortComplex_shortExact
        (integralCWSkeletonInclusion X (n + 1))) (n + 1) n
      (ComplexShape.down_mk (n + 1) n (by omega))
  unfold integralCWRelativeBoundary
  rw [Category.assoc, ← Category.assoc (HomologicalComplex.homologyMap _ _) _ _,
    h, zero_comp, comp_zero]

public def cwRelativeIntegralSingularShortComplexMap
    {A X B Y : TopCat} {i : A ⟶ X} {j : B ⟶ Y}
    (f : CWTopologicalPairMap i j) :
    cwRelativeIntegralSingularShortComplex i ⟶ cwRelativeIntegralSingularShortComplex j where
  τ₁ := cwIntegralSingularChainMapObj f.left
  τ₂ := cwIntegralSingularChainMapObj f.right
  τ₃ := cwRelativeIntegralSingularChainMapOfPair f
  comm₁₂ := by
    symm
    change cwIntegralSingularChainMapObj i ≫ cwIntegralSingularChainMapObj f.right =
      cwIntegralSingularChainMapObj f.left ≫ cwIntegralSingularChainMapObj j
    dsimp only [cwIntegralSingularChainMapObj]
    rw [← Functor.map_comp, f.comm, Functor.map_comp]
  comm₂₃ := by
    symm
    change cwRelativeIntegralSingularChainProjection i ≫
      cwRelativeIntegralSingularChainMapOfPair f =
      cwIntegralSingularChainMapObj f.right ≫ cwRelativeIntegralSingularChainProjection j
    exact cokernel.π_desc _ _ _

public theorem cwIntegralSingularChainMapObj_id (X : TopCat) :
    cwIntegralSingularChainMapObj (𝟙 X) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

public theorem cwIntegralSingularChainMapObj_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cwIntegralSingularChainMapObj (f ≫ g) =
      cwIntegralSingularChainMapObj f ≫ cwIntegralSingularChainMapObj g :=
  Functor.map_comp _ _ _

public theorem cwRelativeIntegralSingularChainProjection_natural
    {A X B Y : TopCat} {i : A ⟶ X} {j : B ⟶ Y} (f : CWTopologicalPairMap i j) :
    cwRelativeIntegralSingularChainProjection i ≫ cwRelativeIntegralSingularChainMapOfPair f =
      cwIntegralSingularChainMapObj f.right ≫ cwRelativeIntegralSingularChainProjection j :=
  (cwRelativeIntegralSingularShortComplexMap f).comm₂₃.symm

public theorem cwRelativeIntegralSingularChainMapOfPair_id
    {A X : TopCat} (i : A ⟶ X) :
    cwRelativeIntegralSingularChainMapOfPair
      (show CWTopologicalPairMap i i from ⟨𝟙 A, 𝟙 X, by simp⟩) = 𝟙 _ := by
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel (cwIntegralSingularChainMapObj i))
  change cwRelativeIntegralSingularChainProjection i ≫ _ =
    cwRelativeIntegralSingularChainProjection i ≫ _
  rw [cwRelativeIntegralSingularChainProjection_natural]
  change cwIntegralSingularChainMapObj (𝟙 X) ≫ _ = _
  rw [cwIntegralSingularChainMapObj_id, Category.id_comp, Category.comp_id]

public theorem cwRelativeIntegralSingularChainMapOfPair_comp
    {A X B Y C Z : TopCat} {i : A ⟶ X} {j : B ⟶ Y} {k : C ⟶ Z}
    (f : CWTopologicalPairMap i j) (g : CWTopologicalPairMap j k) :
    cwRelativeIntegralSingularChainMapOfPair
      (show CWTopologicalPairMap i k from ⟨f.left ≫ g.left, f.right ≫ g.right, by
        rw [← Category.assoc, f.comm, Category.assoc, g.comm, Category.assoc]⟩) =
      cwRelativeIntegralSingularChainMapOfPair f ≫ cwRelativeIntegralSingularChainMapOfPair g := by
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel (cwIntegralSingularChainMapObj i))
  change cwRelativeIntegralSingularChainProjection i ≫ _ =
    cwRelativeIntegralSingularChainProjection i ≫ _
  rw [cwRelativeIntegralSingularChainProjection_natural, ← Category.assoc,
    cwRelativeIntegralSingularChainProjection_natural f, Category.assoc,
    cwRelativeIntegralSingularChainProjection_natural g]
  change cwIntegralSingularChainMapObj (f.right ≫ g.right) ≫ _ = _
  rw [cwIntegralSingularChainMapObj_comp, Category.assoc]

public theorem cwRelativeIntegralSingularBoundary_natural
    {A X B Y : TopCat} {i : A ⟶ X} {j : B ⟶ Y} [Mono i] [Mono j]
    (f : CWTopologicalPairMap i j) (n : ℕ) :
    cwRelativeIntegralSingularBoundary i n ≫
        HomologicalComplex.homologyMap (cwIntegralSingularChainMapObj f.left) n =
      HomologicalComplex.homologyMap (cwRelativeIntegralSingularChainMapOfPair f) (n + 1) ≫
        cwRelativeIntegralSingularBoundary j n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (cwRelativeIntegralSingularShortComplexMap f)
    (cwRelativeIntegralSingularShortComplex_shortExact i)
    (cwRelativeIntegralSingularShortComplex_shortExact j)
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))

public theorem integralCWCharacteristicBoundary_natural
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) (n + 1)) :
    cwRelativeIntegralSingularBoundary (cwCharacteristicBoundaryInclusion (n + 1)) n ≫
        HomologicalComplex.homologyMap
          (cwIntegralSingularChainMapObj (integralCWCharacteristicPairMap X (n + 1) e).boundaryMap) n =
      HomologicalComplex.homologyMap
          (integralCWCharacteristicPairMap X (n + 1) e).relativeChainMap (n + 1) ≫
        cwRelativeIntegralSingularBoundary (integralCWSkeletonInclusion X (n + 1)) n :=
  cwRelativeIntegralSingularBoundary_natural
    { left := (integralCWCharacteristicPairMap X (n + 1) e).boundaryMap
      right := (integralCWCharacteristicPairMap X (n + 1) e).diskMap
      comm := (integralCWCharacteristicPairMap X (n + 1) e).comm } n

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
    integralCWRelativeCellObject X n ⟶ integralCWRelativeCellObject Y n :=
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
  ChainComplex.of (fun n ↦ integralCWRelativeCellObject X n)
    (fun n ↦ integralCWRelativeBoundary X n) (by
      intro n
      exact h n)

section SkeletalComparison

variable (X : Type) [TopologicalSpace X] [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]

public def integralCWSkeletonToSpace (n : ℕ) :
    TopCat.of (IntegralCWSkeletonLT X n) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

public theorem integralCWSkeletalProjection_cycle (n : ℕ) :
    HomologicalComplex.homologyMap
        (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X n)) n ≫
      (integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)).d n
        ((ComplexShape.down ℕ).next n) = 0 := by
  cases n with
  | zero =>
    simp [integralCWSkeletalChainComplex]
    rfl
  | succ n =>
    rw [(ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk (n + 1) n rfl)]
    simp only [integralCWSkeletalChainComplex, ChainComplex.of_d]
    change HomologicalComplex.homologyMap
        (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X (n + 1)))
        (n + 1) ≫ integralCWRelativeBoundary X n = 0
    have h : HomologicalComplex.homologyMap
        (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X (n + 1)))
        (n + 1) ≫
        cwRelativeIntegralSingularBoundary (integralCWSkeletonInclusion X (n + 1)) n = 0 :=
      (cwRelativeIntegralSingularShortComplex_shortExact
        (integralCWSkeletonInclusion X (n + 1))).comp_δ _ _ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ HomologicalComplex.homologyMap
        (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X n)) n) h).trans
        (zero_comp))

public def integralCWSkeletalHomologyToCellular (n : ℕ) :
    (cwIntegralSingularChainComplexObj (TopCat.of (IntegralCWSkeletonLT X (n + 1)))).homology n ⟶
      (integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)).homology n :=
  (integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)).liftCycles
      (HomologicalComplex.homologyMap
        (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X n)) n)
      _ rfl (integralCWSkeletalProjection_cycle X n) ≫
    (integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)).homologyπ n

end SkeletalComparison

/-- A dimension-independent, characteristic-map-normalized, functorial form of the classical
integral cellular-homology theorem for Hausdorff CW complexes. -/
public structure CellularHomology.IntegralComparison where
  diskOrientation : ∀ n,
    (cwRelativeIntegralSingularChainComplex
      (cwCharacteristicBoundaryInclusion n)).homology n ≃+ ℤ
  cellBasis : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ),
      (Topology.CWComplex.cell (Set.univ : Set X) n →₀ ℤ) ≃+
        integralCWRelativeCellObject X n
  cellBasis_single : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) n),
      cellBasis X n (Finsupp.single e 1) =
        ConcreteCategory.hom
          ((cwRelativeIntegralSingularChainComplex
            (cwCharacteristicBoundaryInclusion n)).homologyMap
              (integralCWCharacteristicPairMap X n e).relativeChainMap n)
          ((diskOrientation n).symm 1)
  homologyEquiv : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ),
      (integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)).homology n ≃+
        IntegralSingularHomology n X
  homologyEquiv_skeletal : ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ),
      integralCWSkeletalHomologyToCellular X n ≫ (homologyEquiv X n).toAddCommGrpIso.hom =
        HomologicalComplex.homologyMap
          (cwIntegralSingularChainMapObj (integralCWSkeletonToSpace X (n + 1))) n
  cellularChainMap : ∀ {X Y : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (_hf : IsIntegralCWCellularMap f),
      integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X) ⟶
        integralCWSkeletalChainComplex Y (integralCWRelativeBoundary_comp_self Y)
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
      (integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)).homologyMap
          (cellularChainMap f hf) n ≫ (homologyEquiv Y n).toAddCommGrpIso.hom =
        (homologyEquiv X n).toAddCommGrpIso.hom ≫
          ((singularHomologyFunctor AddCommGrpCat n).obj
            (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)

namespace CellularHomology.IntegralComparison

public theorem cellularChainMap_id (T : CellularHomology.IntegralComparison)
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
      T.cellularChainMap (ContinuousMap.id X) (isIntegralCWCellularMap_id X) =
        𝟙 (integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [T.cellularChainMap_f]
  change integralCWRelativeCellMap _ _ n = 𝟙 _
  unfold integralCWRelativeCellMap
  change HomologicalComplex.homologyMap
    (cwRelativeIntegralSingularChainMapOfPair
      (show CWTopologicalPairMap (integralCWSkeletonInclusion X n)
        (integralCWSkeletonInclusion X n) from ⟨𝟙 _, 𝟙 _, by simp⟩)) n = _
  rw [cwRelativeIntegralSingularChainMapOfPair_id, HomologicalComplex.homologyMap_id]

public theorem cellularChainMap_comp (T : CellularHomology.IntegralComparison)
    {X Y Z : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    [TopologicalSpace Z] [T2Space Z]
    [Topology.CWComplex (Set.univ : Set Z)]
    (f : C(X, Y)) (g : C(Y, Z))
    (hf : IsIntegralCWCellularMap f) (hg : IsIntegralCWCellularMap g) :
      T.cellularChainMap (g.comp f) (hg.comp hf) =
        T.cellularChainMap f hf ≫ T.cellularChainMap g hg := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, T.cellularChainMap_f]
  change integralCWRelativeCellMap (g.comp f) (hg.comp hf) n =
    integralCWRelativeCellMap f hf n ≫ integralCWRelativeCellMap g hg n
  unfold integralCWRelativeCellMap
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  exact cwRelativeIntegralSingularChainMapOfPair_comp
    (show CWTopologicalPairMap (integralCWSkeletonInclusion X n)
      (integralCWSkeletonInclusion Y n) from
      ⟨integralCWSkeletonMap f hf n, integralCWSkeletonMap f hf (n + 1), by ext x; rfl⟩)
    (show CWTopologicalPairMap (integralCWSkeletonInclusion Y n)
      (integralCWSkeletonInclusion Z n) from
      ⟨integralCWSkeletonMap g hg n, integralCWSkeletonMap g hg (n + 1), by ext x; rfl⟩)

public def characteristicPair (_T : CellularHomology.IntegralComparison)
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) n) :
    IntegralCWCharacteristicPairMap X n e :=
  integralCWCharacteristicPairMap X n e

public theorem boundary_comp_zero (_T : CellularHomology.IntegralComparison)
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    integralCWRelativeBoundary X (n + 1) ≫ integralCWRelativeBoundary X n = 0 :=
  integralCWRelativeBoundary_comp_self X n

end CellularHomology.IntegralComparison

/-- The exact accepted classical theorem. It is independent of dimension, finite type, and the
application to the toric cusp or six-sphere. -/
public axiom CellularHomology.integralComparison :
  CellularHomology.IntegralComparison

/-- The objectwise content retained for existing consumers. -/
public structure IntegralCWCellularHomologyModel
    (Y : Type) [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)] where
  chainComplex : ChainComplex AddCommGrpCat ℕ
  cellBasis : ∀ n,
    (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ) ≃+ chainComplex.X n
  homologyEquiv : ∀ n,
    chainComplex.homology n ≃+ IntegralSingularHomology n Y

namespace CellularHomology.IntegralComparison

public noncomputable def objectwiseModel
    (T : CellularHomology.IntegralComparison)
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] :
    IntegralCWCellularHomologyModel Y where
  chainComplex := integralCWSkeletalChainComplex Y
    (CellularHomology.IntegralComparison.boundary_comp_zero T Y)
  cellBasis := CellularHomology.IntegralComparison.cellBasis T Y
  homologyEquiv := CellularHomology.IntegralComparison.homologyEquiv T Y

/-- The coefficient of one cell in the boundary of the positively oriented characteristic class
of a cell one dimension higher. -/
public noncomputable def attachingDegree
    (T : CellularHomology.IntegralComparison)
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set Y) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set Y) n) : ℤ :=
  (CellularHomology.IntegralComparison.cellBasis T Y n).symm
    (ConcreteCategory.hom (integralCWRelativeBoundary Y n)
      (CellularHomology.IntegralComparison.cellBasis T Y (n + 1)
        (Finsupp.single e 1))) e'

/-- The homological degree of the actual attaching-sphere map, read in the oriented coordinate
of a target cell. -/
public noncomputable def homologicalAttachingMapDegree
    (T : CellularHomology.IntegralComparison)
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set Y) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set Y) n) : ℤ :=
  (CellularHomology.IntegralComparison.cellBasis T Y n).symm
    (ConcreteCategory.hom
      (HomologicalComplex.homologyMap
          (cwIntegralSingularChainMapObj
            (CellularHomology.IntegralComparison.characteristicPair
              T Y (n + 1) e).boundaryMap) n ≫
        HomologicalComplex.homologyMap
          (cwRelativeIntegralSingularChainProjection
            (integralCWSkeletonInclusion Y n)) n)
      (ConcreteCategory.hom
        (cwRelativeIntegralSingularBoundary
          (cwCharacteristicBoundaryInclusion (n + 1)) n)
        ((CellularHomology.IntegralComparison.diskOrientation T (n + 1)).symm 1))) e'

public theorem attachingDegree_eq_homologicalAttachingMapDegree
    (T : CellularHomology.IntegralComparison)
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set Y) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set Y) n) :
    T.attachingDegree Y n e e' = T.homologicalAttachingMapDegree Y n e e' := by
  unfold CellularHomology.IntegralComparison.attachingDegree
    CellularHomology.IntegralComparison.homologicalAttachingMapDegree
  apply congrArg (fun y ↦ (T.cellBasis Y n).symm y e')
  rw [T.cellBasis_single]
  change ConcreteCategory.hom
      (HomologicalComplex.homologyMap
          (integralCWCharacteristicPairMap Y (n + 1) e).relativeChainMap (n + 1) ≫
        (cwRelativeIntegralSingularBoundary (integralCWSkeletonInclusion Y (n + 1)) n ≫
          HomologicalComplex.homologyMap
            (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion Y n)) n))
      ((T.diskOrientation (n + 1)).symm 1) = _
  rw [← Category.assoc, ← integralCWCharacteristicBoundary_natural, Category.assoc]
  rfl

end CellularHomology.IntegralComparison


end SphereSixComplex

end

end
