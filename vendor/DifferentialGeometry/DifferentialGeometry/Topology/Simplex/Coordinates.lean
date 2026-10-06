module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

@[expose] public section

noncomputable section

namespace Convexity.StdSimplex

variable {R I : Type*}

def coordinateSet (R I : Type*) [Semiring R] [PartialOrder R] [Fintype I] : Set (I → R) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem range_weights_eq_coordinateSet [Semiring R] [PartialOrder R] [Fintype I] :
    Set.range (fun t : StdSimplex R I => (t.weights : I → R)) = coordinateSet R I := by
  rw [range_toFun_comp_weights]
  ext x
  simp only [coordinateSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

def coordinateEquiv (R I : Type*) [Semiring R] [PartialOrder R] [Fintype I] :
    StdSimplex R I ≃ coordinateSet R I where
  toFun x := ⟨x.weights, x.weights_nonneg, x.total_of_fintype⟩
  invFun x :=
    { weights := Finsupp.equivFunOnFinite.symm x.val
      nonneg i := by simpa using x.property.1 i
      total := by simpa [Finsupp.sum_fintype] using x.property.2 }
  left_inv x := by ext i; simp
  right_inv x := by apply Subtype.ext; simp

@[simp]
theorem coordinateEquiv_apply [Semiring R] [PartialOrder R] [Fintype I]
    (x : StdSimplex R I) : (coordinateEquiv R I x).val = x.weights := rfl

@[simp]
theorem coordinateEquiv_symm_weights [Semiring R] [PartialOrder R] [Fintype I]
    (x : coordinateSet R I) : ((coordinateEquiv R I).symm x).weights =
      Finsupp.equivFunOnFinite.symm x.val := rfl

def coordinateHomeomorph (R I : Type*) [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Fintype I] :
    StdSimplex R I ≃ₜ coordinateSet R I where
  toEquiv := coordinateEquiv R I
  continuous_toFun := Continuous.subtype_mk
    (isEmbedding_toFun_comp_weights R I).continuous _
  continuous_invFun := by
    rw [(isEmbedding_toFun_comp_weights R I).continuous_iff]
    simpa [Function.comp_def, coordinateEquiv] using
      (continuous_subtype_val : Continuous (Subtype.val : coordinateSet R I → I → R))

@[simp]
theorem coordinateHomeomorph_apply [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Fintype I] (x : StdSimplex R I) :
    (coordinateHomeomorph R I x).val = x.weights := rfl

instance metricSpace [Fintype I] : MetricSpace (StdSimplex ℝ I) :=
  (isEmbedding_toFun_comp_weights ℝ I).comapMetricSpace
    (fun t : StdSimplex ℝ I => (t.weights : I → ℝ))

theorem convex_coordinateSet (R I : Type*) [Semiring R] [PartialOrder R]
    [IsOrderedRing R] [Fintype I] : Convex R (coordinateSet R I) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib,
      smul_eq_mul, ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

theorem single_mem_coordinateSet (R : Type*) [Semiring R] [PartialOrder R]
    [ZeroLEOneClass R] [Fintype I] [DecidableEq I] (i : I) :
    Pi.single i 1 ∈ coordinateSet R I := by
  refine ⟨?_, by simp⟩
  intro j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

theorem isCompact_coordinateSet (R I : Type*) [Semiring R] [PartialOrder R]
    [TopologicalSpace R] [ContinuousAdd R] [OrderClosedTopology R]
    [CompactIccSpace R] [IsOrderedAddMonoid R] [Fintype I] :
    IsCompact (coordinateSet R I) := by
  have hclosed : IsClosed (coordinateSet R I) := by
    have heq : coordinateSet R I =
        (⋂ i, {x : I → R | 0 ≤ x i}) ∩ {x | ∑ i, x i = 1} := by
      ext x
      simp only [coordinateSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    apply IsClosed.inter
    · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq
        (continuous_finsetSum Finset.univ fun i _ => continuous_apply i) continuous_const
  apply IsCompact.of_isClosed_subset (s := Set.Icc (0 : I → R) 1) isCompact_Icc hclosed
  intro x hx
  change (∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ 1
  refine ⟨hx.1, fun i => ?_⟩
  rw [← hx.2]
  exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)

instance coordinateSetCompactSpace [Semiring R] [PartialOrder R] [TopologicalSpace R]
    [ContinuousAdd R] [OrderClosedTopology R] [CompactIccSpace R] [IsOrderedAddMonoid R]
    [Fintype I] : CompactSpace (coordinateSet R I) :=
  isCompact_iff_compactSpace.mp (isCompact_coordinateSet R I)

theorem convexHull_basis_eq_coordinateSet (R I : Type*) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [Fintype I] [DecidableEq I] :
    convexHull R (Set.range fun i j : I => if i = j then (1 : R) else 0) =
      coordinateSet R I := by
  refine Set.Subset.antisymm (convexHull_min ?_ (convex_coordinateSet R I)) ?_
  · rintro _ ⟨i, rfl⟩
    simpa only [@eq_comm _ i, ← Pi.single_apply] using single_mem_coordinateSet R i
  · rintro w ⟨hw, hsum⟩
    rw [pi_eq_sum_univ w, ← Finset.univ.centerMass_eq_of_sum_1 _ hsum]
    exact Finset.univ.centerMass_mem_convexHull (fun i _ => hw i)
      (hsum.symm ▸ zero_lt_one) fun i _ => Set.mem_range_self i

theorem convexHull_range_single_eq_coordinateSet (R I : Type*) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [Fintype I] [DecidableEq I] :
    convexHull R (Set.range fun i : I => Pi.single i 1) = coordinateSet R I := by
  convert! convexHull_basis_eq_coordinateSet R I
  aesop

def coordinateBarycenter {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [Fintype I] [Nonempty I] : coordinateSet 𝕜 I :=
  ⟨fun _ => (Fintype.card I : 𝕜)⁻¹, by simp [coordinateSet]⟩

@[simp]
theorem coordinateBarycenter_apply {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Fintype I] [Nonempty I] (i : I) :
    (coordinateBarycenter : coordinateSet 𝕜 I).val i = (Fintype.card I : 𝕜)⁻¹ := rfl

section CoordinateMaps

variable {S X Y Z : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]
  [Fintype X] [Fintype Y] [Fintype Z]

instance coordinateSetFunLike : FunLike (coordinateSet S X) X S where
  coe x := x.val
  coe_injective := Subtype.val_injective

def coordinateMap (f : X → Y) (x : coordinateSet S X) : coordinateSet S Y :=
  ⟨FunOnFinite.linearMap S S f x.val, by
    classical
    constructor
    · intro y
      rw [FunOnFinite.linearMap_apply_apply]
      exact Finset.sum_nonneg fun i _ => x.property.1 i
    · rw [← x.property.2]
      simpa only [FunOnFinite.linearMap_apply_apply] using
        Finset.sum_fiberwise Finset.univ f x.val⟩

@[simp]
theorem coordinateMap_coe (f : X → Y) (x : coordinateSet S X) :
    (coordinateMap f x).val = FunOnFinite.linearMap S S f x.val := rfl

theorem coordinateMap_comp_apply (f : X → Y) (g : Y → Z) (x : coordinateSet S X) :
    coordinateMap g (coordinateMap f x) = coordinateMap (g.comp f) x := by
  apply Subtype.ext
  simp only [coordinateMap_coe, FunOnFinite.linearMap_comp, LinearMap.comp_apply]

@[simp]
theorem coordinateMap_id_apply (x : coordinateSet S X) : coordinateMap id x = x := by
  apply Subtype.ext
  simp [coordinateMap]

abbrev coordinateSingle [DecidableEq X] (i : X) : coordinateSet S X :=
  ⟨Pi.single i 1, single_mem_coordinateSet S i⟩

@[simp]
theorem coordinateMap_single [DecidableEq X] [DecidableEq Y] (f : X → Y) (i : X) :
    coordinateMap (S := S) f (coordinateSingle i) = coordinateSingle (f i) := by
  apply Subtype.ext
  simp [coordinateMap]

theorem continuous_coordinateMap [TopologicalSpace S] [IsTopologicalSemiring S]
    (f : X → Y) : Continuous (coordinateMap (S := S) f) :=
  Continuous.subtype_mk
    ((FunOnFinite.continuous_linearMap S S f).comp continuous_subtype_val) _

omit [IsOrderedRing S] in
@[simp]
theorem coordinate_add_eq_one (x : coordinateSet S (Fin 2)) : x.val 0 + x.val 1 = 1 := by
  simpa only [Fin.sum_univ_two] using x.property.2

end CoordinateMaps

theorem coordinateEquiv_map [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Fintype I] {J : Type*} [Fintype J] (f : I → J) (x : StdSimplex R I) :
    coordinateEquiv R J (map f x) = coordinateMap f (coordinateEquiv R I x) := by
  classical
  apply Subtype.ext
  ext j
  simp [coordinateMap, weights_map, Finsupp.mapDomain_fintype,
    FunOnFinite.linearMap_apply_apply, Finsupp.single_apply, Finset.sum_filter]

def coordinateEquivIcc (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] :
    coordinateSet R (Fin 2) ≃ Set.Icc (0 : R) 1 where
  toFun x := ⟨x.val 1, x.property.1 1, x.property.2 ▸
    Finset.single_le_sum (fun i _ => x.property.1 i) (Finset.mem_univ 1)⟩
  invFun x := ⟨![1 - x, x], Fin.forall_fin_two.2 ⟨sub_nonneg.2 x.property.2,
    x.property.1⟩, by simp⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i
    · change 1 - x.val 1 = x.val 0
      rw [sub_eq_iff_eq_add]
      exact (coordinate_add_eq_one x).symm
    · rfl

def coordinateHomeomorphI : coordinateSet ℝ (Fin 2) ≃ₜ unitInterval where
  toEquiv := coordinateEquivIcc ℝ
  continuous_toFun := Continuous.subtype_mk
    ((continuous_apply 1).comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

instance contractibleSpace [Finite I] [Nonempty I] : ContractibleSpace (StdSimplex ℝ I) := by
  let := Fintype.ofFinite I
  have hne : (coordinateSet ℝ I).Nonempty :=
    ⟨(coordinateEquiv ℝ I (.single (Classical.arbitrary I))).val,
      (coordinateEquiv ℝ I (.single (Classical.arbitrary I))).property⟩
  exact (coordinateHomeomorph ℝ I).contractibleSpace_iff.mpr
    ((convex_coordinateSet ℝ I).contractibleSpace hne)

instance locallyPathConnectedSpace [Finite I] : LocallyPathConnectedSpace (StdSimplex ℝ I) := by
  let := Fintype.ofFinite I
  let := (convex_coordinateSet ℝ I).locallyPathConnectedSpace
  exact (coordinateHomeomorph ℝ I).symm.locallyPathConnectedSpace

end Convexity.StdSimplex
