module

public import SphereSixComplex.Prerequisites.Topology.AdjunctionCollar
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex

/-! # The outer collar of a ball attachment retracts onto the attached space -/

@[expose] public section

open scoped unitInterval
open ContinuousMap

namespace SphereSixComplex.AdjunctionSpace

variable {E T B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace T] [TopologicalSpace B]

/-- Include the attached space in the outer collar. -/
def radialCollarInclusion (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr1 : r < 1) : C(B, radialCollar g r) where
  toFun b := ⟨inr ballBoundary g b, hr1⟩
  continuous_toFun := (continuous_inr ballBoundary g).subtype_mk _

/-- Radial expansion to time one, read in the embedded attached space. -/
noncomputable def radialCollarRetraction (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hB : Topology.IsEmbedding (inr ballBoundary g)) : C(radialCollar g r, B) where
  toFun x := hB.toHomeomorph.symm
    ⟨radialExpansion g r hr hr1.le (1, x.1),
      radialExpansion_one_mem_range_inr g r hr hr1.le x.1 x.2⟩
  continuous_toFun := hB.toHomeomorph.symm.continuous.comp
    (((radialExpansion g r hr hr1.le).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).subtype_mk _)

@[simp] theorem inr_radialCollarRetraction
    (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hB : Topology.IsEmbedding (inr ballBoundary g)) (x : radialCollar g r) :
    inr ballBoundary g (radialCollarRetraction g r hr hr1 hB x) =
      radialExpansion g r hr hr1.le (1, x.1) := by
  exact congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)

@[simp] theorem radialCollarRetraction_inclusion
    (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hB : Topology.IsEmbedding (inr ballBoundary g)) (b : B) :
    radialCollarRetraction g r hr hr1 hB (radialCollarInclusion g r hr1 b) = b := by
  apply hB.injective
  rw [inr_radialCollarRetraction]
  exact radialExpansion_inr g r hr hr1.le 1 b

/-- The radial deformation, restricted to the outer collar. -/
noncomputable def radialCollarHomotopy
    (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hB : Topology.IsEmbedding (inr ballBoundary g)) :
    ContinuousMap.Homotopy (ContinuousMap.id (radialCollar g r))
      ((radialCollarInclusion g r hr1).comp (radialCollarRetraction g r hr hr1 hB)) where
  toFun p := ⟨radialExpansion g r hr hr1.le (p.1, p.2.1),
    radialExpansion_mem_radialCollar g r hr hr1.le p.1 p.2.1 p.2.2⟩
  continuous_toFun := ((radialExpansion g r hr hr1.le).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (radialExpansion_zero g r hr hr1.le x.1)
  map_one_left x := Subtype.ext (inr_radialCollarRetraction g r hr hr1 hB x).symm

/-- The outer collar is homotopy equivalent to the embedded attached space. -/
noncomputable def radialCollarHomotopyEquiv
    (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hB : Topology.IsEmbedding (inr ballBoundary g)) :
    radialCollar g r ≃ₕ B where
  toFun := radialCollarRetraction g r hr hr1 hB
  invFun := radialCollarInclusion g r hr1
  left_inv := ⟨(radialCollarHomotopy g r hr hr1 hB).symm⟩
  right_inv := by
    have h : (radialCollarRetraction g r hr hr1 hB).comp
        (radialCollarInclusion g r hr1) = ContinuousMap.id B := by
      ext b
      exact radialCollarRetraction_inclusion g r hr hr1 hB b
    rw [h]

theorem radialCollarRetraction_inl
    (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hB : Topology.IsEmbedding (inr ballBoundary g))
    (k : Metric.closedBall (0 : E) 1 × T) (hk : r < ‖k.1.1‖) :
    radialCollarRetraction g r hr hr1 hB ⟨inl ballBoundary g k, hk⟩ =
      g ⟨(ballRadialExpansion r hr (1, k.1), k.2),
        norm_ballRadialExpansion_one r hr k.1 hk.le⟩ := by
  apply hB.injective
  rw [inr_radialCollarRetraction]
  exact inl_eq_inr ballBoundary g
    ⟨(ballRadialExpansion r hr (1, k.1), k.2),
      norm_ballRadialExpansion_one r hr k.1 hk.le⟩

end SphereSixComplex.AdjunctionSpace

namespace SphereSixComplex

/-- Remove the redundant unit-ball condition from a product with prescribed radii. -/
def closedBallProductNormPreimageHomeomorph (E T : Type*) [NormedAddCommGroup E]
    [TopologicalSpace T] (S : Set ℝ) (hS : S ⊆ Set.Iic 1) :
    {p : Metric.closedBall (0 : E) 1 × T | ‖p.1.1‖ ∈ S} ≃ₜ
      {x : E | ‖x‖ ∈ S} × T where
  toFun p := (⟨p.1.1.1, p.2⟩, p.1.2)
  invFun p := ⟨(⟨p.1.1, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (show ‖p.1.1‖ ≤ 1 from hS p.1.2)⟩, p.2), p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp (continuous_subtype_val.fst)).subtype_mk _).prodMk
      continuous_subtype_val.snd
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
      continuous_snd).subtype_mk _

/-- The inner ball product contracts in its ball factor. -/
noncomputable def ballProdHomotopyEquiv (E T : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace T] (s : ℝ) (hs : 0 < s) :
    Metric.ball (0 : E) s × T ≃ₕ T := by
  letI : ContractibleSpace (Metric.ball (0 : E) s) :=
    (convex_ball (0 : E) s).contractibleSpace ⟨0, by simpa using hs⟩
  exact ((Classical.choice (ContractibleSpace.hequiv_unit (Metric.ball (0 : E) s))).prodCongr
    (HomotopyEquiv.refl T)).trans (Homeomorph.uniqueProd Unit T).toHomotopyEquiv

/-- An annulus with a convex nonempty set of positive radii has the homotopy type of its sphere. -/
noncomputable def normPreimageProdHomotopyEquiv (E T : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace T] (S : Set ℝ) (hS : S ⊆ Set.Ioi 0)
    (hconv : Convex ℝ S) (hne : S.Nonempty) :
    {x : E | ‖x‖ ∈ S} × T ≃ₕ Metric.sphere (0 : E) 1 × T := by
  letI : ContractibleSpace S := hconv.contractibleSpace hne
  let e : (Metric.sphere (0 : E) 1 × S) ≃ₕ Metric.sphere (0 : E) 1 :=
    ((HomotopyEquiv.refl _).prodCongr
      (Classical.choice (ContractibleSpace.hequiv_unit S))).trans
      (Homeomorph.prodUnique _ Unit).toHomotopyEquiv
  exact ((normPreimageHomeomorph E S hS).prodCongr (Homeomorph.refl T)).toHomotopyEquiv.trans
    (e.prodCongr (HomotopyEquiv.refl T))

end SphereSixComplex

namespace ContinuousMap

open SphereSixComplex

/-- A compact ball-product parametrization gives exact coordinates wherever its radius is below one. -/
noncomputable def radialPreimageHomeomorph
    {E T X : Type*} [NormedAddCommGroup E] [TopologicalSpace T] [TopologicalSpace X]
    [CompactSpace (Metric.closedBall (0 : E) 1)] [CompactSpace T] [T2Space X]
    (f : C(Metric.closedBall (0 : E) 1 × T, X)) (hf : Function.Surjective f)
    (ρ : X → ℝ) (hρ : ∀ p, ρ (f p) = ‖p.1.1‖)
    (hinj : Set.InjOn f {p | ‖p.1.1‖ < 1})
    (S : Set ℝ) (hS : S ⊆ Set.Iio 1) :
    ({x : E | ‖x‖ ∈ S} × T) ≃ₜ {x : X | ρ x ∈ S} := by
  have he : f ⁻¹' {x | ρ x ∈ S} = {p | ‖p.1.1‖ ∈ S} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hρ]
  have hi : Set.InjOn f (f ⁻¹' {x | ρ x ∈ S}) := by
    intro p hp q hq hpq
    apply hinj _ _ hpq
    · exact hS (by simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hρ] using hp)
    · exact hS (by simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hρ] using hq)
  exact (closedBallProductNormPreimageHomeomorph E T S (by
    intro a ha
    change a ≤ 1
    exact (show a < 1 from hS ha).le)).symm.trans
    ((Homeomorph.setCongr he.symm).trans
      (IsHomeomorph.homeomorph (f.restrictPreimage {x | ρ x ∈ S})
        (f.isHomeomorph_restrictPreimage_of_injOn hf _ hi)))

end ContinuousMap
