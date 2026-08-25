/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import SphereSixComplex.Topology.ConnectedMayerVietorisDegreeZero
public import SphereSixComplex.Topology.EstablishedMayerVietoris
public import SphereSixComplex.Topology.MayerVietorisDegreeZeroBridge
public import SphereSixComplex.Topology.StandardSpherePositiveHomology
public import SphereSixComplex.Topology.StandardSpherePunctures
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-!
# The standard sphere Mayer--Vietoris calculation

The standard sphere `S^(d+1)` is covered by the complements of two antipodal points. Both pieces
are contractible by stereographic projection, and their intersection is the punctured Euclidean
space `ℝ^(d+1) ∖ {0}`, which is homotopy equivalent to `S^d`. Feeding this cover into the
established binary open-cover Mayer--Vietoris sequence proves every output recorded in
`StandardSphereMayerVietorisInputs`:

* the positive-degree suspension shift `H_(k+1)(S^(d+1)) ≃ H_k(S^d)` for `k ≠ 0`;
* the vanishing of `H_1(S^d)` for `d ≥ 2`, from the degree-zero augmentation normal form of the
  Mayer--Vietoris difference map for a path-connected intersection;
* the circle class `H_1(S^1) ≃ ℤ`, from the reduced degree-zero homology of the two-component
  intersection `ℝ ∖ {0}`.

The only external input is `establishedIntegralMayerVietorisExactSequence`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Metric Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

/-! ## The degree-zero augmentation -/

/-- The degree-zero singular-homology augmentation, as an additive map to `ℤ`. -/
public def integralAugmentation (X : Type) [TopologicalSpace X] :
    IntegralSingularHomology 0 X →+ ℤ :=
  ConcreteCategory.hom ((TopCat.of X).singularHomology₀ε (AddCommGrpCat.of ℤ))

/-- Naturality of the degree-zero augmentation. -/
public theorem integralAugmentation_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : IntegralSingularHomology 0 X) :
    integralAugmentation Y (integralSingularHomologyMap 0 f x) = integralAugmentation X x :=
  ConcreteCategory.congr_hom
    (TopCat.singularHomology₀ε_naturality (TopCat.ofHom f) (AddCommGrpCat.of ℤ)) x

/-- The augmentation of a path-connected space is injective. -/
public theorem integralAugmentation_injective (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : Function.Injective (integralAugmentation X) :=
  (ConcreteCategory.bijective_of_isIso
    ((TopCat.of X).singularHomology₀ε (AddCommGrpCat.of ℤ))).injective

/-- The canonical augmentation basis of a path-connected space is the augmentation. -/
public theorem pathConnectedIntegralHomologyZeroEquivInteger_apply (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] (x : IntegralSingularHomology 0 X) :
    pathConnectedIntegralHomologyZeroEquivInteger X x = integralAugmentation X x :=
  rfl

/-- Transport the kernel of a map to `ℤ` along a compatible additive equivalence. -/
public def kerAddEquivOfComp {M N : Type*} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N)
    (f : M →+ ℤ) (g : N →+ ℤ) (h : ∀ x, g (e x) = f x) : f.ker ≃+ g.ker where
  toFun x := ⟨e x, by rw [AddMonoidHom.mem_ker, h]; exact x.2⟩
  invFun y := ⟨e.symm y, by rw [AddMonoidHom.mem_ker, ← h, e.apply_symm_apply]; exact y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)

/-- The augmentation kernel transports along a homeomorphism. -/
public def kerAddEquivOfHomeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : (integralAugmentation X).ker ≃+ (integralAugmentation Y).ker :=
  kerAddEquivOfComp (integralSingularHomologyEquiv 0 h) _ _
    fun x ↦ integralAugmentation_map (h : C(X, Y)) x

/-- The kernel of the sum map `ℤ × ℤ → ℤ` is infinite cyclic. -/
public def integerSumKerEquiv : (AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ).ker ≃+ ℤ where
  toFun x := x.1.1
  invFun n := ⟨(n, -n), by simp [AddMonoidHom.mem_ker]⟩
  left_inv x := by
    have hx : x.1.1 + x.1.2 = 0 := x.2
    exact Subtype.ext (Prod.ext rfl (show -x.1.1 = x.1.2 by omega))
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Degree-zero integral homology of an empty space is trivial. -/
public theorem subsingleton_integralSingularHomology_zero_of_isEmpty (Y : Type)
    [TopologicalSpace Y] [IsEmpty Y] : Subsingleton (IntegralSingularHomology 0 Y) := by
  let ι := ZerothHomotopy (TopCat.of Y)
  have : IsEmpty ι := ⟨fun q ↦ Quotient.inductionOn q fun (y : Y) ↦ isEmptyElim y⟩
  have : Fintype ι := Fintype.ofIsEmpty
  let e : IntegralSingularHomology 0 Y ≃+ (ι → ℤ) :=
    (((TopCat.of Y).singularHomology₀Iso (AddCommGrpCat.of ℤ)).trans
      ((biproduct.isoCoproduct fun _ : ι ↦ AddCommGrpCat.of ℤ).symm.trans
        (AddCommGrpCat.biproductIsoPi fun _ : ι ↦ AddCommGrpCat.of ℤ))).addCommGroupIsoToAddEquiv
  exact ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩

/-! ## Algebraic consequences of an exact Mayer--Vietoris sequence -/

namespace IntegralMayerVietoris

variable {X : Type} [TopologicalSpace X] {A B : Set X}

private theorem boundary_injective
    {boundary : ∀ k : ℕ, IntegralSingularHomology (k + 1) (A ∪ B : Set X) →+
      IntegralSingularHomology k (A ∩ B : Set X)} {k : ℕ}
    (h : Function.Exact (sumMap A B (k + 1)) (boundary k))
    [Subsingleton (IntegralSingularHomology (k + 1) A)]
    [Subsingleton (IntegralSingularHomology (k + 1) B)] :
    Function.Injective (boundary k) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨z, rfl⟩ := (h y).mp hy
  rw [Subsingleton.elim z 0, map_zero]

/-- When the two pieces have trivial homology in two consecutive degrees, the Mayer--Vietoris
boundary is an isomorphism from the union to the intersection. -/
public theorem exists_boundary_addEquiv (hMV : ExactSequence A B) (k : ℕ)
    [Subsingleton (IntegralSingularHomology (k + 1) A)]
    [Subsingleton (IntegralSingularHomology (k + 1) B)]
    [Subsingleton (IntegralSingularHomology k A)]
    [Subsingleton (IntegralSingularHomology k B)] :
    Nonempty (IntegralSingularHomology (k + 1) (A ∪ B : Set X) ≃+
      IntegralSingularHomology k (A ∩ B : Set X)) := by
  obtain ⟨boundary, hb⟩ := hMV
  obtain ⟨h₁, h₂, -⟩ := hb k
  refine ⟨AddEquiv.ofBijective (boundary k) ⟨boundary_injective h₁, fun x ↦ ?_⟩⟩
  exact (h₂ x).mp (Subsingleton.elim _ _)

/-- In the canonical augmentation, the degree-zero difference map of two path-connected pieces
vanishes exactly on the augmentation kernel of the intersection. -/
private theorem differenceMap_zero_eq_zero_iff [PathConnectedSpace A] [PathConnectedSpace B]
    (x : IntegralSingularHomology 0 (A ∩ B : Set X)) :
    differenceMap A B 0 x = 0 ↔ integralAugmentation (A ∩ B : Set X) x = 0 := by
  constructor
  · intro hx
    have h := congrArg Prod.fst hx
    change integralSingularHomologyMap 0 (interToLeft A B) x = 0 at h
    rw [← integralAugmentation_map (interToLeft A B) x, h, map_zero]
  · intro hx
    have hi : integralSingularHomologyMap 0 (interToLeft A B) x = 0 :=
      integralAugmentation_injective A (by rw [integralAugmentation_map, hx, map_zero])
    have hj : integralSingularHomologyMap 0 (interToRight A B) x = 0 :=
      integralAugmentation_injective B (by rw [integralAugmentation_map, hx, map_zero])
    change (integralSingularHomologyMap 0 (interToLeft A B) x,
      -(integralSingularHomologyMap 0 (interToRight A B) x)) = (0, 0)
    rw [hi, hj, neg_zero]

/-- When the two pieces are path-connected with trivial first homology, the first homology of the
union is the reduced degree-zero homology of the intersection. -/
public theorem exists_degreeOne_addEquiv_ker (hMV : ExactSequence A B)
    [Subsingleton (IntegralSingularHomology 1 A)] [Subsingleton (IntegralSingularHomology 1 B)]
    [PathConnectedSpace A] [PathConnectedSpace B] :
    Nonempty (IntegralSingularHomology 1 (A ∪ B : Set X) ≃+
      (integralAugmentation (A ∩ B : Set X)).ker) := by
  obtain ⟨boundary, hb⟩ := hMV
  obtain ⟨h₁, h₂, -⟩ := hb 0
  have hmem : ∀ y, boundary 0 y ∈ (integralAugmentation (A ∩ B : Set X)).ker := fun y ↦
    AddMonoidHom.mem_ker.mpr ((differenceMap_zero_eq_zero_iff _).mp ((h₂ _).mpr ⟨y, rfl⟩))
  refine ⟨AddEquiv.ofBijective ((boundary 0).codRestrict _ hmem) ⟨fun y y' hyy' ↦ ?_, ?_⟩⟩
  · exact boundary_injective h₁ (congrArg Subtype.val hyy')
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ :=
      (h₂ x).mp ((differenceMap_zero_eq_zero_iff x).mpr (AddMonoidHom.mem_ker.mp hx))
    exact ⟨y, Subtype.ext hy⟩

/-- A cover by two path-connected pieces with trivial first homology and path-connected
intersection has trivial first homology. -/
public theorem subsingleton_degreeOne_of_pathConnected (hMV : ExactSequence A B)
    [Subsingleton (IntegralSingularHomology 1 A)] [Subsingleton (IntegralSingularHomology 1 B)]
    [PathConnectedSpace A] [PathConnectedSpace B] [PathConnectedSpace (A ∩ B : Set X)] :
    Subsingleton (IntegralSingularHomology 1 (A ∪ B : Set X)) := by
  obtain ⟨e⟩ := exists_degreeOne_addEquiv_ker hMV
  have : Subsingleton (integralAugmentation (A ∩ B : Set X)).ker :=
    ⟨fun x y ↦ Subtype.ext (integralAugmentation_injective _
      ((AddMonoidHom.mem_ker.mp x.2).trans (AddMonoidHom.mem_ker.mp y.2).symm))⟩
  exact ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩

/-- For a disjoint open cover, the degree-zero sum map is bijective. -/
public theorem sumMap_zero_bijective (hA : IsOpen A) (hB : IsOpen B)
    [IsEmpty (A ∩ B : Set X)] : Function.Bijective (sumMap A B 0) := by
  refine ⟨?_, sumMap_zero_surjective A B hA hB⟩
  obtain ⟨boundary, hb⟩ := establishedIntegralMayerVietorisExactSequence A B hA hB
  obtain ⟨-, -, h₃⟩ := hb 0
  have := subsingleton_integralSingularHomology_zero_of_isEmpty (A ∩ B : Set X)
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨z, rfl⟩ := (h₃ y).mp hy
  rw [Subsingleton.elim z 0, map_zero]

/-- The augmentation of the union, in terms of the augmentations of the pieces. -/
public theorem integralAugmentation_sumMap_zero
    (u : IntegralSingularHomology 0 A) (v : IntegralSingularHomology 0 B) :
    integralAugmentation (A ∪ B : Set X) (sumMap A B 0 (u, v)) =
      integralAugmentation A u + integralAugmentation B v := by
  change integralAugmentation (A ∪ B : Set X)
    (integralSingularHomologyMap 0 (leftToUnion A B) u +
      integralSingularHomologyMap 0 (rightToUnion A B) v) = _
  rw [map_add, integralAugmentation_map, integralAugmentation_map]

/-- The reduced degree-zero homology of a disjoint open union of two path-connected pieces is
infinite cyclic. -/
public def augmentationKerEquivInteger_of_disjoint (hA : IsOpen A) (hB : IsOpen B)
    [IsEmpty (A ∩ B : Set X)] [PathConnectedSpace A] [PathConnectedSpace B] :
    (integralAugmentation (A ∪ B : Set X)).ker ≃+ ℤ :=
  (kerAddEquivOfComp (AddEquiv.ofBijective (sumMap A B 0) (sumMap_zero_bijective hA hB))
      ((integralAugmentation A).comp
          (AddMonoidHom.fst (IntegralSingularHomology 0 A) (IntegralSingularHomology 0 B)) +
        (integralAugmentation B).comp
          (AddMonoidHom.snd (IntegralSingularHomology 0 A) (IntegralSingularHomology 0 B)))
      (integralAugmentation (A ∪ B : Set X))
      fun x ↦ integralAugmentation_sumMap_zero x.1 x.2).symm.trans
    ((kerAddEquivOfComp
      ((pathConnectedIntegralHomologyZeroEquivInteger A).prodCongr
        (pathConnectedIntegralHomologyZeroEquivInteger B)) _
      (AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ) fun _ ↦ rfl).trans integerSumKerEquiv)

end IntegralMayerVietoris

/-! ## The punctured line -/

namespace PuncturedLine

/-- The coordinate functional on the Euclidean line. -/
abbrev coord : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 1)

/-- The positive open half-line. -/
public def posRay : Set (EuclideanSpace ℝ (Fin 1)) := {x | 0 < coord x}

/-- The negative open half-line. -/
public def negRay : Set (EuclideanSpace ℝ (Fin 1)) := {x | coord x < 0}

public theorem isOpen_posRay : IsOpen posRay := isOpen_lt continuous_const coord.continuous

public theorem isOpen_negRay : IsOpen negRay := isOpen_lt coord.continuous continuous_const

public instance : IsEmpty (posRay ∩ negRay : Set (EuclideanSpace ℝ (Fin 1))) :=
  ⟨fun x ↦ lt_asymm (show (0 : ℝ) < coord x.1 from x.2.1) (show coord x.1 < 0 from x.2.2)⟩

private theorem eq_zero_of_coord_eq_zero {x : EuclideanSpace ℝ (Fin 1)} (hx : coord x = 0) :
    x = 0 := by
  ext i
  fin_cases i
  simpa using hx

public theorem posRay_union_negRay :
    (posRay ∪ negRay : Set (EuclideanSpace ℝ (Fin 1))) = {0}ᶜ := by
  ext x
  constructor
  · rintro (h | h) hx <;> rw [mem_singleton_iff] at hx <;> subst hx <;> simp [posRay, negRay] at h
  · intro hx
    rcases lt_or_gt_of_ne (fun h0 ↦ hx (mem_singleton_iff.mpr (eq_zero_of_coord_eq_zero h0)))
      with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

public instance : PathConnectedSpace posRay :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_halfSpace_gt coord.toLinearMap.isLinear 0).isPathConnected
      ⟨EuclideanSpace.single 0 1, by simp⟩)

public instance : PathConnectedSpace negRay :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_halfSpace_lt coord.toLinearMap.isLinear 0).isPathConnected
      ⟨EuclideanSpace.single 0 (-1), by simp⟩)

/-- The reduced degree-zero homology of the punctured line is infinite cyclic. -/
public def augmentationKerEquivInteger :
    (integralAugmentation ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1)))).ker ≃+ ℤ :=
  (kerAddEquivOfHomeomorph (Homeomorph.setCongr posRay_union_negRay)).symm.trans
    (IntegralMayerVietoris.augmentationKerEquivInteger_of_disjoint isOpen_posRay isOpen_negRay)

end PuncturedLine

/-! ## The two-puncture cover of a standard sphere -/

/-- Punctured Euclidean space retracts onto the unit sphere. -/
public def puncturedEuclideanHomotopyEquivSphere (n : ℕ) :
    ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≃ₕ StandardSphere n :=
  haveI : ContractibleSpace (Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, Set.mem_Ioi.mpr one_pos⟩
  (homeomorphUnitSphereProd _).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.prodCongr (ContinuousMap.HomotopyEquiv.refl _)
      (ContractibleSpace.hequiv_unit (Ioi (0 : ℝ))).some).trans
      (Homeomorph.prodUnique (StandardSphere n) Unit).toHomotopyEquiv)

/-- Punctured Euclidean space of dimension at least two is path-connected. -/
public theorem pathConnectedSpace_puncturedEuclidean (n : ℕ) (hn : 1 ≤ n) :
    PathConnectedSpace ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast Nat.lt_succ_of_le hn

variable (d : ℕ) (v : StandardSphere (d + 1))

/-- The antipode of a point of the sphere lies in the complement of that point. -/
public theorem neg_mem_compl_singleton : -v ∈ ({v}ᶜ : Set (StandardSphere (d + 1))) :=
  fun h ↦ ne_neg_of_mem_unit_sphere ℝ v (mem_singleton_iff.mp h).symm

/-- Stereographic projection from `v` sends the antipode `-v` to the origin. -/
public theorem puncturedStandardSphereHomeomorph_neg :
    puncturedStandardSphereHomeomorph d v ⟨-v, neg_mem_compl_singleton d v⟩ = 0 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + 1))) = (d + 1) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  change (stereographic' (d + 1) v) (-v) = 0
  simp [stereographic']

/-- The complement of an antipodal pair in a standard sphere is homeomorphic to punctured
Euclidean space of one dimension lower, by stereographic projection from one of the points. -/
public def doublyPuncturedStandardSphereHomeomorph :
    ({v}ᶜ ∩ {-v}ᶜ : Set (StandardSphere (d + 1))) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))) where
  toFun x := ⟨puncturedStandardSphereHomeomorph d v ⟨x.1, x.2.1⟩, fun h ↦ x.2.2 (by
    have h' := (puncturedStandardSphereHomeomorph d v).injective
      ((mem_singleton_iff.mp h).trans (puncturedStandardSphereHomeomorph_neg d v).symm)
    exact congrArg Subtype.val h')⟩
  invFun y := ⟨((puncturedStandardSphereHomeomorph d v).symm y.1).1,
    ((puncturedStandardSphereHomeomorph d v).symm y.1).2, fun h ↦ y.2 (by
      have h' : (puncturedStandardSphereHomeomorph d v).symm y.1 =
          ⟨-v, neg_mem_compl_singleton d v⟩ := Subtype.ext h
      rw [mem_singleton_iff, ← (puncturedStandardSphereHomeomorph d v).apply_symm_apply y.1, h']
      exact puncturedStandardSphereHomeomorph_neg d v)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun :=
    ((puncturedStandardSphereHomeomorph d v).continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp
      ((puncturedStandardSphereHomeomorph d v).symm.continuous.comp continuous_subtype_val))
      |>.subtype_mk _

/-- The two-puncture cover of the sphere. -/
public theorem compl_union_compl_neg :
    ({v}ᶜ ∪ {-v}ᶜ : Set (StandardSphere (d + 1))) = univ := by
  ext x
  simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
  exact not_and_or.mp fun h ↦ ne_neg_of_mem_unit_sphere ℝ v (h.1.symm.trans h.2)

/-- The union of the two punctured spheres is the whole sphere. -/
public def twoPunctureUnionHomeomorph :
    ({v}ᶜ ∪ {-v}ᶜ : Set (StandardSphere (d + 1))) ≃ₜ StandardSphere (d + 1) :=
  (Homeomorph.setCongr (compl_union_compl_neg d v)).trans (Homeomorph.Set.univ _)

/-- The intersection of the two punctured spheres is homotopy equivalent to the sphere of one
dimension lower. -/
public def twoPunctureIntersectionHomotopyEquiv :
    ({v}ᶜ ∩ {-v}ᶜ : Set (StandardSphere (d + 1))) ≃ₕ StandardSphere d :=
  (doublyPuncturedStandardSphereHomeomorph d v).toHomotopyEquiv.trans
    (puncturedEuclideanHomotopyEquivSphere d)

/-- The established Mayer--Vietoris sequence of the two-puncture cover. -/
public theorem twoPunctureExactSequence :
    IntegralMayerVietoris.ExactSequence ({v}ᶜ : Set (StandardSphere (d + 1))) {-v}ᶜ :=
  establishedIntegralMayerVietorisExactSequence _ _ isOpen_compl_singleton isOpen_compl_singleton

/-- A punctured standard sphere has trivial integral homology in every positive degree. -/
public theorem subsingleton_puncturedStandardSphere_homology (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (IntegralSingularHomology k ({v}ᶜ : Set (StandardSphere (d + 1)))) :=
  have := puncturedStandardSphere_contractible d v
  subsingleton_integralSingularHomology_of_contractible k hk

/-- Every standard sphere of positive dimension is nonempty. -/
public theorem standardSphere_nonempty : Nonempty (StandardSphere (d + 1)) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

/-! ## The sphere calculation -/

/-- The positive-degree suspension shift for standard spheres. -/
public theorem standardSphere_suspensionShift (k : ℕ) (hk : k ≠ 0) :
    Nonempty (IntegralSingularHomology (k + 1) (StandardSphere (d + 1)) ≃+
      IntegralSingularHomology k (StandardSphere d)) := by
  obtain ⟨v⟩ := standardSphere_nonempty d
  have := subsingleton_puncturedStandardSphere_homology d v (k + 1) k.succ_ne_zero
  have := subsingleton_puncturedStandardSphere_homology d (-v) (k + 1) k.succ_ne_zero
  have := subsingleton_puncturedStandardSphere_homology d v k hk
  have := subsingleton_puncturedStandardSphere_homology d (-v) k hk
  obtain ⟨e⟩ := IntegralMayerVietoris.exists_boundary_addEquiv (twoPunctureExactSequence d v) k
  exact ⟨((integralSingularHomologyEquiv (k + 1) (twoPunctureUnionHomeomorph d v)).symm.trans
    e).trans (integralSingularHomologyEquivOfHomotopyEquiv k
      (twoPunctureIntersectionHomotopyEquiv d v))⟩

/-- First homology of a standard sphere of dimension at least two vanishes. -/
public theorem standardSphere_degreeOneVanishing (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (IntegralSingularHomology 1 (StandardSphere n)) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  obtain ⟨v⟩ := standardSphere_nonempty d
  have := puncturedStandardSphere_contractible d v
  have := puncturedStandardSphere_contractible d (-v)
  have := subsingleton_puncturedStandardSphere_homology d v 1 one_ne_zero
  have := subsingleton_puncturedStandardSphere_homology d (-v) 1 one_ne_zero
  have := pathConnectedSpace_puncturedEuclidean d (by omega)
  have : PathConnectedSpace ({v}ᶜ ∩ {-v}ᶜ : Set (StandardSphere (d + 1))) :=
    pathConnectedSpace_of_homeomorph (doublyPuncturedStandardSphereHomeomorph d v).symm
  have := IntegralMayerVietoris.subsingleton_degreeOne_of_pathConnected
    (twoPunctureExactSequence d v)
  exact ⟨fun x y ↦
    (integralSingularHomologyEquiv 1 (twoPunctureUnionHomeomorph d v)).symm.injective
      (Subsingleton.elim _ _)⟩

/-- First homology of the circle is infinite cyclic. -/
public theorem standardSphere_circleTop :
    Nonempty (IntegralSingularHomology 1 (StandardSphere 1) ≃+ ℤ) := by
  obtain ⟨v⟩ := standardSphere_nonempty 0
  have := puncturedStandardSphere_contractible 0 v
  have := puncturedStandardSphere_contractible 0 (-v)
  have := subsingleton_puncturedStandardSphere_homology 0 v 1 one_ne_zero
  have := subsingleton_puncturedStandardSphere_homology 0 (-v) 1 one_ne_zero
  obtain ⟨e⟩ := IntegralMayerVietoris.exists_degreeOne_addEquiv_ker (twoPunctureExactSequence 0 v)
  exact ⟨((integralSingularHomologyEquiv 1 (twoPunctureUnionHomeomorph 0 v)).symm.trans e).trans
    ((kerAddEquivOfHomeomorph (doublyPuncturedStandardSphereHomeomorph 0 v)).trans
      PuncturedLine.augmentationKerEquivInteger)⟩

/-- The standard hemisphere Mayer--Vietoris outputs, derived from the established binary
open-cover Mayer--Vietoris theorem alone. -/
public theorem standardSphereMayerVietorisInputs : StandardSphereMayerVietorisInputs where
  suspensionShift d k _ hk := standardSphere_suspensionShift d k hk
  degreeOneVanishing d hd _ := standardSphere_degreeOneVanishing d hd
  circleTop := standardSphere_circleTop

end SphereSixComplex
