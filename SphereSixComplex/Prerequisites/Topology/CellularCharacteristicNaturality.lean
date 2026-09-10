module

public import SphereSixComplex.Prerequisites.Topology.CellularHomologyClassicalBoundary

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

namespace SphereSixComplex

@[ext] public theorem CWTopologicalPairMap.ext
    {A X B Y : TopCat} {i : A ⟶ X} {j : B ⟶ Y}
    {f g : CWTopologicalPairMap i j} (hl : f.left = g.left) (hr : f.right = g.right) :
    f = g := by
  cases f
  cases g
  cases hl
  cases hr
  rfl

variable {X Y : Type} [TopologicalSpace X] [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  [TopologicalSpace Y] [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]

public theorem isIntegralCWCellularMap_of_characteristic
    (f : C(X, Y))
    (c : ∀ n, Topology.CWComplex.cell (Set.univ : Set X) n →
      Topology.CWComplex.cell (Set.univ : Set Y) n)
    (hc : ∀ n e x, x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 →
      f (Topology.CWComplex.map n e x) = Topology.CWComplex.map n (c n e) x) :
    IsIntegralCWCellularMap f := by
  intro n x hx
  obtain ⟨m, hm, e, z, hz, rfl⟩ := Topology.CWComplex.mem_skeletonLT_iff.mp hx
  apply Topology.CWComplex.mem_skeletonLT_iff.mpr
  exact ⟨m, hm, c m e, z, hz, (hc m e z (Metric.ball_subset_closedBall hz)).symm⟩

public theorem integralCWCharacteristicPairMap_natural
    (f : C(X, Y)) (hf : IsIntegralCWCellularMap f) (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) n)
    (e' : Topology.CWComplex.cell (Set.univ : Set Y) n)
    (he : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1,
      f (Topology.CWComplex.map n e x) = Topology.CWComplex.map n e' x) :
    (integralCWCharacteristicPairMap X n e).relativeChainMap ≫
        cwRelativeIntegralSingularChainMapOfPair
          (show CWTopologicalPairMap (integralCWSkeletonInclusion X n)
            (integralCWSkeletonInclusion Y n) from
            ⟨integralCWSkeletonMap f hf n, integralCWSkeletonMap f hf (n + 1),
              by ext x; rfl⟩) =
      (integralCWCharacteristicPairMap Y n e').relativeChainMap := by
  unfold IntegralCWCharacteristicPairMap.relativeChainMap
  rw [← cwRelativeIntegralSingularChainMapOfPair_comp]
  congr 1
  apply CWTopologicalPairMap.ext
  · ext x
    exact he x.1 (le_of_eq x.2)
  · ext x
    exact he x.1 x.2

public theorem IntegralCWCellularHomologyFoundation.cellBasis_single_natural
    (T : IntegralCWCellularHomologyFoundation)
    (f : C(X, Y)) (hf : IsIntegralCWCellularMap f) (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) n)
    (e' : Topology.CWComplex.cell (Set.univ : Set Y) n)
    (he : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1,
      f (Topology.CWComplex.map n e x) = Topology.CWComplex.map n e' x) :
    ConcreteCategory.hom (integralCWRelativeCellMap f hf n)
      (T.cellBasis X n (Finsupp.single e 1)) = T.cellBasis Y n (Finsupp.single e' 1) := by
  rw [T.cellBasis_single, T.cellBasis_single]
  change ConcreteCategory.hom
    (HomologicalComplex.homologyMap (integralCWCharacteristicPairMap X n e).relativeChainMap n ≫
      integralCWRelativeCellMap f hf n) ((T.diskOrientation n).symm 1) = _
  unfold integralCWRelativeCellMap
  rw [← HomologicalComplex.homologyMap_comp, integralCWCharacteristicPairMap_natural f hf n e e' he]

public theorem IntegralCWCellularHomologyFoundation.cellBasis_natural
    (T : IntegralCWCellularHomologyFoundation)
    (f : C(X, Y)) (hf : IsIntegralCWCellularMap f) (n : ℕ)
    (c : Topology.CWComplex.cell (Set.univ : Set X) n →
      Topology.CWComplex.cell (Set.univ : Set Y) n)
    (hc : ∀ e x, x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 →
      f (Topology.CWComplex.map n e x) = Topology.CWComplex.map n (c e) x)
    (v : Topology.CWComplex.cell (Set.univ : Set X) n →₀ ℤ) :
    ConcreteCategory.hom (integralCWRelativeCellMap f hf n) (T.cellBasis X n v) =
      T.cellBasis Y n (Finsupp.mapDomain c v) := by
  have h : (ConcreteCategory.hom (integralCWRelativeCellMap f hf n)).comp
      (T.cellBasis X n).toAddMonoidHom =
      (T.cellBasis Y n).toAddMonoidHom.comp (Finsupp.mapDomain.addMonoidHom c) := by
    apply Finsupp.addHom_ext'
    intro e
    apply AddMonoidHom.ext_int
    simpa using T.cellBasis_single_natural f hf n e (c e) (hc e)
  exact DFunLike.congr_fun h v

public theorem IntegralCWCellularHomologyFoundation.coordinateBoundary_natural
    (T : IntegralCWCellularHomologyFoundation)
    (f : C(X, Y)) (hf : IsIntegralCWCellularMap f)
    (c : ∀ n, Topology.CWComplex.cell (Set.univ : Set X) n →
      Topology.CWComplex.cell (Set.univ : Set Y) n)
    (hc : ∀ n e x, x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 →
      f (Topology.CWComplex.map n e x) = Topology.CWComplex.map n (c n e) x)
    (n : ℕ) (v : Topology.CWComplex.cell (Set.univ : Set X) (n + 1) →₀ ℤ) :
    Finsupp.mapDomain (c n) ((T.cellBasis X n).symm
      (ConcreteCategory.hom (integralCWRelativeBoundary X n) (T.cellBasis X (n + 1) v))) =
    (T.cellBasis Y n).symm (ConcreteCategory.hom (integralCWRelativeBoundary Y n)
      (T.cellBasis Y (n + 1) (Finsupp.mapDomain (c (n + 1)) v))) := by
  apply (T.cellBasis Y n).injective
  rw [AddEquiv.apply_symm_apply, ← T.cellBasis_natural f hf n (c n) (hc n),
    AddEquiv.apply_symm_apply, ← T.cellBasis_natural f hf (n + 1) (c (n + 1)) (hc (n + 1))]
  have h := (T.cellularChainMap f hf).comm (n + 1) n
  simp only [T.cellularChainMap_f, integralCWSkeletalChainComplex, ChainComplex.of_d] at h
  exact (ConcreteCategory.congr_hom h (T.cellBasis X (n + 1) v)).symm

public theorem IntegralCWCellularHomologyFoundation.attachingDegree_natural
    (T : IntegralCWCellularHomologyFoundation)
    (f : C(X, Y)) (hf : IsIntegralCWCellularMap f)
    (c : ∀ n, Topology.CWComplex.cell (Set.univ : Set X) n →
      Topology.CWComplex.cell (Set.univ : Set Y) n)
    (hc : ∀ n e x, x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 →
      f (Topology.CWComplex.map n e x) = Topology.CWComplex.map n (c n e) x)
    (n : ℕ) (hi : Function.Injective (c n))
    (e : Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set X) n) :
    T.attachingDegree X n e e' = T.attachingDegree Y n (c (n + 1) e) (c n e') := by
  have h := congrArg (fun v ↦ v (c n e'))
    (T.coordinateBoundary_natural f hf c hc n (Finsupp.single e 1))
  simpa only [Finsupp.mapDomain_apply hi, Finsupp.mapDomain_single,
    attachingDegree] using h

end SphereSixComplex
