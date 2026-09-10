module
public import SphereSixComplex.Paper.Topology.ToricCellAtlasRechart

@[expose] public section
noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex.StandardA2ToricCentralFiberCellAtlas
variable {X : Type} [TopologicalSpace X] [T2Space X]

public def skeletalComplex (A : StandardA2ToricCentralFiberCellAtlas X) :
    ChainComplex AddCommGrpCat ℕ := by
  let _ := A.cwComplex
  exact integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)

public theorem cellularIdentity_of_closedCell_eq
    (A B : StandardA2ToricCentralFiberCellAtlas X)
    (h : ∀ n i, A.cellMap n i '' Metric.closedBall 0 1 =
      B.cellMap n i '' Metric.closedBall 0 1) :
    @IsIntegralCWCellularMap X X _ _ A.cwComplex _ _ B.cwComplex
      (ContinuousMap.id X) := by
  intro n
  change MapsTo (ContinuousMap.id X) (A.skeletalSet n) (B.skeletalSet n)
  rw [skeleton_eq_of_closedCell_eq A B h]
  exact fun _ hx ↦ hx

public def rechartSkeletalChainMap
    (T : IntegralCWCellularHomologyFoundation)
    (A B : StandardA2ToricCentralFiberCellAtlas X)
    (h : ∀ n i, A.cellMap n i '' Metric.closedBall 0 1 =
      B.cellMap n i '' Metric.closedBall 0 1) :
    A.skeletalComplex ⟶ B.skeletalComplex :=
  @T.cellularChainMap X X _ _ A.cwComplex _ _ B.cwComplex
    (ContinuousMap.id X) (cellularIdentity_of_closedCell_eq A B h)

public theorem rechartSkeletalChainMap_comp
    (T : IntegralCWCellularHomologyFoundation)
    (A B C : StandardA2ToricCentralFiberCellAtlas X)
    (hAB : ∀ n i, A.cellMap n i '' Metric.closedBall 0 1 =
      B.cellMap n i '' Metric.closedBall 0 1)
    (hBC : ∀ n i, B.cellMap n i '' Metric.closedBall 0 1 =
      C.cellMap n i '' Metric.closedBall 0 1) :
    rechartSkeletalChainMap T A B hAB ≫ rechartSkeletalChainMap T B C hBC =
      rechartSkeletalChainMap T A C (fun n i ↦ (hAB n i).trans (hBC n i)) := by
  exact (@T.cellularChainMap_comp X X X _ _ A.cwComplex _ _ B.cwComplex _ _ C.cwComplex
    (ContinuousMap.id X) (ContinuousMap.id X)
    (cellularIdentity_of_closedCell_eq A B hAB)
    (cellularIdentity_of_closedCell_eq B C hBC)).symm

public theorem rechartSkeletalChainMap_self
    (T : IntegralCWCellularHomologyFoundation)
    (A : StandardA2ToricCentralFiberCellAtlas X)
    (h : ∀ n i, A.cellMap n i '' Metric.closedBall 0 1 =
      A.cellMap n i '' Metric.closedBall 0 1) :
    rechartSkeletalChainMap T A A h = 𝟙 A.skeletalComplex :=
  @T.cellularChainMap_id X _ _ A.cwComplex

public def rechartSkeletalChainIso
    (T : IntegralCWCellularHomologyFoundation)
    (A B : StandardA2ToricCentralFiberCellAtlas X)
    (h : ∀ n i, A.cellMap n i '' Metric.closedBall 0 1 =
      B.cellMap n i '' Metric.closedBall 0 1) :
    A.skeletalComplex ≅ B.skeletalComplex where
  hom := rechartSkeletalChainMap T A B h
  inv := rechartSkeletalChainMap T B A (fun n i ↦ (h n i).symm)
  hom_inv_id := by rw [rechartSkeletalChainMap_comp, rechartSkeletalChainMap_self]
  inv_hom_id := by rw [rechartSkeletalChainMap_comp, rechartSkeletalChainMap_self]

public theorem rechartSkeletal_d_zero
    (T : IntegralCWCellularHomologyFoundation)
    (A B : StandardA2ToricCentralFiberCellAtlas X)
    (h : ∀ n i, A.cellMap n i '' Metric.closedBall 0 1 =
      B.cellMap n i '' Metric.closedBall 0 1) (n m : ℕ)
    (hz : A.skeletalComplex.d n m = 0) : B.skeletalComplex.d n m = 0 := by
  let e := rechartSkeletalChainIso T A B h
  apply (cancel_epi (e.hom.f n)).mp
  rw [comp_zero, e.hom.comm, hz, zero_comp]

end SphereSixComplex.StandardA2ToricCentralFiberCellAtlas

namespace SphereSixComplex.IntegralCWCellularHomologyFoundation

public theorem relativeBoundary_eq_zero_of_attachingDegree_eq_zero
    (T : IntegralCWCellularHomologyFoundation)
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (h : ∀ e e', T.attachingDegree X n e e' = 0) :
    integralCWRelativeBoundary X n = 0 := by
  have hsingle : ∀ e, (integralCWRelativeBoundary X n).hom
      (T.cellBasis X (n + 1) (Finsupp.single e 1)) = 0 := by
    intro e
    apply (T.cellBasis X n).symm.injective
    rw [map_zero]
    ext e'
    exact h e e'
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change (integralCWRelativeBoundary X n).hom x = 0
  obtain ⟨z, rfl⟩ := (T.cellBasis X (n + 1)).surjective x
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | single e z =>
    have hs : Finsupp.single e z = z • (Finsupp.single e 1 : _ →₀ ℤ) := by simp
    rw [hs, map_zsmul, map_zsmul, hsingle, zsmul_zero]

end SphereSixComplex.IntegralCWCellularHomologyFoundation

namespace SphereSixComplex

public def homologyIsoOfAdjacentZeros (K : ChainComplex AddCommGrpCat ℕ) (n : ℕ)
    (hf : K.d (n + 2) (n + 1) = 0) (hg : K.d (n + 1) n = 0) :
    K.homology (n + 1) ≅ K.X (n + 1) :=
  (K.homologyIsoSc' (n + 2) (n + 1) n
    ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk (n + 2) (n + 1) (by omega)))
    ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk (n + 1) n (by omega)))).trans
      (ShortComplex.HomologyData.ofZeros (K.sc' (n + 2) (n + 1) n) hf hg).left.homologyIso

public theorem homologyIsoOfAdjacentZeros_π (K : ChainComplex AddCommGrpCat ℕ) (n : ℕ)
    (hf : K.d (n + 2) (n + 1) = 0) (hg : K.d (n + 1) n = 0) :
    K.homologyπ (n + 1) ≫ (homologyIsoOfAdjacentZeros K n hf hg).hom = K.iCycles (n + 1) := by
  let S := K.sc' (n + 2) (n + 1) n
  let h := ShortComplex.HomologyData.ofZeros S hf hg
  have hc : h.left.cyclesIso.hom = S.iCycles := by
    simpa only [h, ShortComplex.HomologyData.ofZeros,
      ShortComplex.LeftHomologyData.ofZeros, Category.comp_id] using
      h.left.cyclesIso_hom_comp_i
  change K.homologyπ (n + 1) ≫
    ((K.homologyIsoSc' (n + 2) (n + 1) n
      ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk (n + 2) (n + 1) (by omega)))
      ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk (n + 1) n (by omega)))).hom ≫
        h.left.homologyIso.hom) = _
  rw [← Category.assoc, HomologicalComplex.π_homologyIsoSc'_hom, Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  change _ ≫ h.left.cyclesIso.hom ≫ 𝟙 _ = _
  rw [Category.comp_id, hc]
  exact K.cyclesIsoSc'_hom_iCycles (n + 2) (n + 1) n _ _

end SphereSixComplex
