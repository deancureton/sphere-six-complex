module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalStarConvex
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeZero
public import Mathlib.Tactic.Abel

@[expose] public section

noncomputable section

open CategoryTheory Set Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem closedBall_complement_subset_point_complement {r : ℝ} (hr : 0 ≤ r) :
    (closedBall (0 : E) r)ᶜ ⊆ ({0}ᶜ : Set E) :=
  compl_subset_compl.mpr (singleton_subset_iff.mpr (mem_closedBall_self hr))

def LocalBallHomology.integralClosedBallToLocalHomologyIso (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    integralRelativeHomology n ((closedBall (0 : E) r)ᶜ) ≅ integralLocalHomology n (0 : E) :=
  integralBoundedStarConvexLocalHomologyIso n (mem_closedBall_self hr)
    ((convex_closedBall (0 : E) r).starConvex (mem_closedBall_self hr)) isBounded_closedBall

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory ContinuousMap Set Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E]

theorem LocalBallHomology.closedBall_shift_complement_mapsTo (c : E) (r : ℝ) :
    MapsTo (Homeomorph.subRight c) ((closedBall c r)ᶜ) ((closedBall (0 : E) r)ᶜ) := by
  intro x hx hball
  change x - c ∈ closedBall (0 : E) r at hball
  rw [mem_closedBall_zero_iff] at hball
  apply hx
  simpa only [mem_closedBall, dist_eq_norm] using hball

theorem LocalBallHomology.closedBall_shift_symm_complement_mapsTo (c : E) (r : ℝ) :
    MapsTo (Homeomorph.subRight c).symm ((closedBall (0 : E) r)ᶜ) ((closedBall c r)ᶜ) := by
  intro x hx hball
  change x + c ∈ closedBall c r at hball
  apply hx
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hball

def LocalBallHomology.integralClosedBallTranslateIso (n : ℕ) (c : E) (r : ℝ) :
    integralRelativeHomology n ((closedBall c r)ᶜ) ≅
      integralRelativeHomology n ((closedBall (0 : E) r)ᶜ) :=
  integralRelativeHomologyHomeomorphIso n (Homeomorph.subRight c)
    ((closedBall c r)ᶜ) ((closedBall (0 : E) r)ᶜ)
    (LocalBallHomology.closedBall_shift_complement_mapsTo c r) (LocalBallHomology.closedBall_shift_symm_complement_mapsTo c r)

def LocalBallHomology.integralLocalTranslateToZeroIso (n : ℕ) (c : E) :
    integralLocalHomology n c ≅ integralLocalHomology n (0 : E) :=
  integralRelativeHomologyHomeomorphIso n (Homeomorph.subRight c) ({c}ᶜ) ({0}ᶜ)
    (fun _ hx => sub_ne_zero.mpr hx)
    (fun x hx h => hx (by
      change x + c = c at h
      exact add_right_cancel (h.trans (zero_add c).symm)))

variable [NormedSpace ℝ E]

def integralClosedBallLocalHomologyIso (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) :
    integralRelativeHomology n ((closedBall c r)ᶜ) ≅ integralLocalHomology n c :=
  LocalBallHomology.integralClosedBallTranslateIso n c r ≪≫ LocalBallHomology.integralClosedBallToLocalHomologyIso n r hr ≪≫
    (LocalBallHomology.integralLocalTranslateToZeroIso n c).symm

theorem integralClosedBallLocalHomologyIso_hom (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) :
    (integralClosedBallLocalHomologyIso n c r hr).hom.hom =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (show (closedBall c r)ᶜ ⊆ ({c}ᶜ : Set E) from
          fun _ hx h => hx (h.symm ▸ mem_closedBall_self hr)) := by
  let B := LocalBallHomology.integralClosedBallTranslateIso (E := E) n c r
  let I := LocalBallHomology.integralClosedBallToLocalHomologyIso (E := E) n r hr
  let L := LocalBallHomology.integralLocalTranslateToZeroIso (E := E) n c
  have hcenter : MapsTo (ContinuousMap.id E) ((closedBall c r)ᶜ) ({c}ᶜ : Set E) :=
    fun _ hx h => hx (h.symm ▸ mem_closedBall_self hr)
  have hB : MapsTo (toContinuousMap (Homeomorph.subRight c))
      ((closedBall c r)ᶜ) ((closedBall (0 : E) r)ᶜ) := LocalBallHomology.closedBall_shift_complement_mapsTo c r
  have hL : MapsTo (toContinuousMap (Homeomorph.subRight c)) ({c}ᶜ : Set E) ({0}ᶜ : Set E) :=
    fun _ hx => sub_ne_zero.mpr hx
  have hI : MapsTo (ContinuousMap.id E) ((closedBall (0 : E) r)ᶜ) ({0}ᶜ : Set E) :=
    closedBall_complement_subset_point_complement hr
  change (integralClosedBallLocalHomologyIso n c r hr).hom.hom =
    integralRelativeHomologyMap n (ContinuousMap.id E) hcenter
  have hcomm : I.hom.hom.comp B.hom.hom =
      L.hom.hom.comp (integralRelativeHomologyMap n (ContinuousMap.id E) hcenter) := by
    change (integralRelativeHomologyMap n (ContinuousMap.id E) hI).comp
        (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.subRight c)) hB) =
      (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.subRight c)) hL).comp
        (integralRelativeHomologyMap n (ContinuousMap.id E) hcenter)
    rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
    rfl
  apply LinearMap.ext
  intro a
  change L.inv.hom (I.hom.hom (B.hom.hom a)) = _
  have hpoint := LinearMap.congr_fun hcomm a
  change I.hom.hom (B.hom.hom a) =
    L.hom.hom (integralRelativeHomologyMap n (ContinuousMap.id E) hcenter a) at hpoint
  rw [hpoint]
  exact congrArg (fun f => f.hom (integralRelativeHomologyMap n (ContinuousMap.id E) hcenter a))
    L.hom_inv_id

private theorem closedBall_center_map_bijective (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) :
    Function.Bijective (integralRelativeHomologyMap n (ContinuousMap.id E)
      (show (closedBall c r)ᶜ ⊆ ({c}ᶜ : Set E) from
        fun _ hx h => hx (h.symm ▸ mem_closedBall_self hr))) := by
  rw [← integralClosedBallLocalHomologyIso_hom n c r hr]
  exact (integralClosedBallLocalHomologyIso n c r hr).toLinearEquiv.bijective

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory ContinuousMap Set Metric
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem closedBall_complement_subset_point_complement_at
    {c y : E} {r : ℝ} (hy : y ∈ closedBall c r) :
    (closedBall c r)ᶜ ⊆ ({y}ᶜ : Set E) := by
  intro x hx h
  exact hx (h.symm ▸ hy)

omit [NormedSpace ℝ E] in
theorem point_complement_center_translation_mapsTo (c y : E) :
    MapsTo (Homeomorph.addRight (c - y)) ({y}ᶜ : Set E) ({c}ᶜ : Set E) := by
  intro x hx h
  apply hx
  apply (Homeomorph.addRight (c - y)).injective
  have hy : Homeomorph.addRight (c - y) y = c := by
    change y + (c - y) = c
    abel
  exact h.trans hy.symm

omit [NormedSpace ℝ E] in
private theorem closedBall_center_translation_mapsTo
    {c y : E} {r : ℝ} (hy : y ∈ closedBall c r) :
    MapsTo (toContinuousMap (Homeomorph.addRight (c - y)))
      ((closedBall c r)ᶜ) ({c}ᶜ : Set E) :=
  fun _ hx => point_complement_center_translation_mapsTo c y
    (closedBall_complement_subset_point_complement_at hy hx)

private theorem closedBall_center_translation_homotopy_ne_center
    {c y : E} {r : ℝ} (hy : y ∈ closedBall c r)
    (t : unitInterval) (x : ((closedBall c r)ᶜ : Set E)) :
    x.val + t.val • (c - y) ≠ c := by
  have hx : r < ‖x.val - c‖ := by
    simpa only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] using x.property
  have ht : ‖t.val • (c - y)‖ ≤ ‖y - c‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1, norm_sub_rev c y]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg (y - c))
  intro heq
  have hxc : x.val - c = -(t.val • (c - y)) := by
    calc
      x.val - c = x.val - (x.val + t.val • (c - y)) :=
        congrArg (fun z : E => x.val - z) heq.symm
      _ = -(t.val • (c - y)) := by abel
  have hnorm : ‖x.val - c‖ ≤ r := by
    rw [hxc, norm_neg]
    exact ht.trans (by simpa only [mem_closedBall, dist_eq_norm] using hy)
  exact (not_le_of_gt hx) hnorm

private def closedBallCenterTranslationHomotopy
    (c : E) (r : ℝ) (hr : 0 ≤ r) (y : E) (hy : y ∈ closedBall c r) :
    (singularPairRestriction (ContinuousMap.id E)
      (closedBall_complement_subset_point_complement_at (mem_closedBall_self hr))).Homotopy
      (singularPairRestriction (toContinuousMap (Homeomorph.addRight (c - y)))
        (closedBall_center_translation_mapsTo hy)) where
  toFun p := ⟨p.2.val + p.1.val • (c - y),
    closedBall_center_translation_homotopy_ne_center hy p.1 p.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  map_zero_left x := by
    apply Subtype.ext
    simp [singularPairRestriction]
  map_one_left x := by
    apply Subtype.ext
    simp [singularPairRestriction]

private theorem integralClosedBall_center_translation_map_eq
    (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) (y : E) (hy : y ∈ closedBall c r) :
    integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y)))
        (closedBall_center_translation_mapsTo hy) =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (closedBall_complement_subset_point_complement_at (mem_closedBall_self hr)) := by
  cases n with
  | zero =>
    exact integralRelativeHomologyMap_zero_eq_of_joined _ _ _ _ _ _
      (fun x => ⟨PathConnectedSpace.somePath (x + (c - y)) x⟩)
  | succ n =>
    let := integralSingularHomology_subsingleton_of_contractible (n + 1) (Nat.succ_ne_zero n) E
    exact (integralRelativeHomologyMap_eq_of_restriction_homotopic n
      (ContinuousMap.id E) (toContinuousMap (Homeomorph.addRight (c - y)))
      ((closedBall c r)ᶜ) ({c}ᶜ : Set E) _ _
      ⟨closedBallCenterTranslationHomotopy c r hr y hy⟩).symm

theorem integralRelativeHomologyMap_closedBall_translation
    (n : ℕ) (c : E) (r : ℝ) (y : E) (hy : y ∈ closedBall c r) :
    (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y)))
        (point_complement_center_translation_mapsTo c y)).comp
        (integralRelativeHomologyMap n (ContinuousMap.id E)
          (closedBall_complement_subset_point_complement_at hy)) =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (closedBall_complement_subset_point_complement_at
          (mem_closedBall_self (dist_nonneg.trans (mem_closedBall.mp hy)))) := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp hy)
  have hT : MapsTo (toContinuousMap (Homeomorph.addRight (c - y)))
      ({y}ᶜ : Set E) ({c}ᶜ : Set E) := point_complement_center_translation_mapsTo c y
  have hR : MapsTo (ContinuousMap.id E) ((closedBall c r)ᶜ) ({y}ᶜ : Set E) :=
    closedBall_complement_subset_point_complement_at hy
  change (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y))) hT).comp
    (integralRelativeHomologyMap n (ContinuousMap.id E) hR) = _
  rw [← integralRelativeHomologyMap_comp]
  exact integralClosedBall_center_translation_map_eq n c r hr y hy

theorem existsUnique_closedBall_class_with_normalized_local_maps
    (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) (ζ : integralLocalHomology n c) :
    ∃! a : integralRelativeHomology n ((closedBall c r)ᶜ),
      ∀ (y : E) (hy : y ∈ closedBall c r),
        integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y)))
          (point_complement_center_translation_mapsTo c y)
          (integralRelativeHomologyMap n (ContinuousMap.id E)
            (closedBall_complement_subset_point_complement_at hy) a) = ζ := by
  let e := integralClosedBallLocalHomologyIso n c r hr
  have he : e.hom.hom = integralRelativeHomologyMap n (ContinuousMap.id E)
      (closedBall_complement_subset_point_complement_at (mem_closedBall_self hr)) :=
    integralClosedBallLocalHomologyIso_hom n c r hr
  have ha : ∀ (y : E) (hy : y ∈ closedBall c r),
      integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y)))
        (point_complement_center_translation_mapsTo c y)
        (integralRelativeHomologyMap n (ContinuousMap.id E)
          (closedBall_complement_subset_point_complement_at hy) (e.inv.hom ζ)) = ζ := by
    intro y hy
    have h := LinearMap.congr_fun
      (integralRelativeHomologyMap_closedBall_translation n c r y hy) (e.inv.hom ζ)
    exact h.trans ((LinearMap.congr_fun he (e.inv.hom ζ)).symm.trans
      (congrArg (fun f => f.hom ζ) e.inv_hom_id))
  refine ⟨e.inv.hom ζ, ha, ?_⟩
  intro b hb
  have hmapcenter : (toContinuousMap (Homeomorph.addRight (c - c)) : C(E, E)) =
      ContinuousMap.id E := by
    ext x
    simp
  have hba := hb c (mem_closedBall_self hr)
  have haa := ha c (mem_closedBall_self hr)
  simp only [hmapcenter, integralRelativeHomologyMap_id, LinearMap.id_apply] at hba haa
  exact (closedBall_center_map_bijective (E := E) n c r hr).injective (hba.trans haa.symm)

end DifferentialGeometry.Topology

end
