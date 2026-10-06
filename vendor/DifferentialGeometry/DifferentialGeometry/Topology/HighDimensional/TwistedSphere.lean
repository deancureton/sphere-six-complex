module

public import DifferentialGeometry.Topology.ClosedBall.UnitDisk
public import DifferentialGeometry.Topology.ClosedBall.AlexanderTrick
public import Mathlib.Geometry.Manifold.Instances.Sphere

@[expose] public section

namespace DifferentialGeometry.Topology

open Metric Set _root_.Topology

noncomputable def euclidSnoc {m : ℕ} (x : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin (m + 2)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp x) t)

noncomputable def euclidInit {m : ℕ} (z : EuclideanSpace ℝ (Fin (m + 2))) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.init (α := fun _ => ℝ) (WithLp.ofLp z))

theorem euclidSnoc_apply_castSucc {m : ℕ} (x : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ)
    (i : Fin (m + 1)) : euclidSnoc x t i.castSucc = x i := by
  simp [euclidSnoc]

theorem euclidSnoc_apply_last {m : ℕ} (x : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    euclidSnoc x t (Fin.last (m + 1)) = t := by
  simp [euclidSnoc]

theorem euclidInit_apply {m : ℕ} (z : EuclideanSpace ℝ (Fin (m + 2))) (i : Fin (m + 1)) :
    euclidInit z i = z i.castSucc := by
  simp [euclidInit, Fin.init]

theorem euclidInit_euclidSnoc {m : ℕ} (x : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    euclidInit (euclidSnoc x t) = x := by
  ext i
  rw [euclidInit_apply, euclidSnoc_apply_castSucc]

theorem euclidSnoc_euclidInit {m : ℕ} (z : EuclideanSpace ℝ (Fin (m + 2))) :
    euclidSnoc (euclidInit z) (z (Fin.last (m + 1))) = z := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [euclidSnoc_apply_last]
  · rw [euclidSnoc_apply_castSucc, euclidInit_apply]

theorem norm_euclidSnoc_sq {m : ℕ} (x : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    ‖euclidSnoc x t‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp [euclidSnoc_apply_castSucc, euclidSnoc_apply_last]

theorem euclidSnoc_inj {m : ℕ} {x y : EuclideanSpace ℝ (Fin (m + 1))} {t s : ℝ} :
    euclidSnoc x t = euclidSnoc y s ↔ x = y ∧ t = s := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← euclidInit_euclidSnoc x t, h, euclidInit_euclidSnoc]
    · rw [← euclidSnoc_apply_last x t, h, euclidSnoc_apply_last]
  · rintro ⟨rfl, rfl⟩; rfl

theorem continuous_euclidSnoc {m : ℕ} {X : Type*} [TopologicalSpace X]
    {f : X → EuclideanSpace ℝ (Fin (m + 1))} {g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => euclidSnoc (f a) (g a) := by
  unfold euclidSnoc
  exact (PiLp.continuous_toLp 2 _).comp
    (Continuous.finSnoc (A := fun _ => ℝ) ((PiLp.continuous_ofLp 2 _).comp hf) hg)

theorem continuous_euclidInit {m : ℕ} : Continuous (euclidInit (m := m)) := by
  unfold euclidInit
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (PiLp.continuous_apply 2 _ _))

noncomputable def diskHeight {m : ℕ} (x : Disk (m + 1)) : ℝ :=
  √(1 - ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2)

theorem diskHeight_nonneg {m : ℕ} (x : Disk (m + 1)) : 0 ≤ diskHeight x := Real.sqrt_nonneg _

theorem one_sub_norm_sq_nonneg {m : ℕ} (x : Disk (m + 1)) :
    0 ≤ 1 - ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := mem_closedBall_zero_iff.1 x.2
  have := norm_nonneg (x : EuclideanSpace ℝ (Fin (m + 1)))
  nlinarith

theorem diskHeight_sq {m : ℕ} (x : Disk (m + 1)) :
    diskHeight x ^ 2 = 1 - ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 :=
  Real.sq_sqrt (one_sub_norm_sq_nonneg x)

theorem diskHeight_eq_zero_iff {m : ℕ} (x : Disk (m + 1)) :
    diskHeight x = 0 ↔ x ∈ diskSphere (m + 1) := by
  rw [mem_diskSphere, diskHeight, Real.sqrt_eq_zero (one_sub_norm_sq_nonneg x), sub_eq_zero]
  have := norm_nonneg (x : EuclideanSpace ℝ (Fin (m + 1)))
  constructor
  · intro h
    nlinarith [sq_nonneg (‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ - 1),
      sq_nonneg (‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ + 1)]
  · intro h; rw [h]; norm_num

theorem continuous_diskHeight {m : ℕ} : Continuous (diskHeight (m := m)) :=
  Real.continuous_sqrt.comp (continuous_const.sub (continuous_subtype_val.norm.pow 2))

theorem euclidSnoc_mem_sphere {m : ℕ} (x : Disk (m + 1)) {t : ℝ}
    (ht : t ^ 2 = 1 - ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2) :
    euclidSnoc (x : EuclideanSpace ℝ (Fin (m + 1))) t ∈
      sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h : ‖euclidSnoc (x : EuclideanSpace ℝ (Fin (m + 1))) t‖ ^ 2 = 1 := by
    rw [norm_euclidSnoc_sq, ht]; ring
  have := norm_nonneg (euclidSnoc (x : EuclideanSpace ℝ (Fin (m + 1))) t)
  nlinarith [sq_nonneg (‖euclidSnoc (x : EuclideanSpace ℝ (Fin (m + 1))) t‖ - 1)]

noncomputable def lowerHemisphere (m : ℕ) (x : Disk (m + 1)) :
    sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 :=
  ⟨euclidSnoc (x : EuclideanSpace ℝ (Fin (m + 1))) (-diskHeight x),
    euclidSnoc_mem_sphere x (by rw [neg_sq, diskHeight_sq])⟩

noncomputable def upperHemisphere (m : ℕ) (x : Disk (m + 1)) :
    sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 :=
  ⟨euclidSnoc (x : EuclideanSpace ℝ (Fin (m + 1))) (diskHeight x),
    euclidSnoc_mem_sphere x (diskHeight_sq x)⟩

theorem lowerHemisphere_coe (m : ℕ) (x : Disk (m + 1)) :
    (lowerHemisphere m x : EuclideanSpace ℝ (Fin (m + 2))) =
      euclidSnoc (x : EuclideanSpace ℝ (Fin (m + 1))) (-diskHeight x) := rfl

theorem upperHemisphere_coe (m : ℕ) (x : Disk (m + 1)) :
    (upperHemisphere m x : EuclideanSpace ℝ (Fin (m + 2))) =
      euclidSnoc (x : EuclideanSpace ℝ (Fin (m + 1))) (diskHeight x) := rfl

theorem continuous_lowerHemisphere (m : ℕ) : Continuous (lowerHemisphere m) := by
  apply Continuous.subtype_mk
  exact continuous_euclidSnoc continuous_subtype_val continuous_diskHeight.neg

theorem continuous_upperHemisphere (m : ℕ) : Continuous (upperHemisphere m) := by
  apply Continuous.subtype_mk
  exact continuous_euclidSnoc continuous_subtype_val continuous_diskHeight

theorem lowerHemisphere_injective (m : ℕ) : Function.Injective (lowerHemisphere m) := by
  intro x y h
  have h' := congrArg Subtype.val h
  rw [lowerHemisphere_coe, lowerHemisphere_coe, euclidSnoc_inj] at h'
  exact Subtype.ext h'.1

theorem upperHemisphere_injective (m : ℕ) : Function.Injective (upperHemisphere m) := by
  intro x y h
  have h' := congrArg Subtype.val h
  rw [upperHemisphere_coe, upperHemisphere_coe, euclidSnoc_inj] at h'
  exact Subtype.ext h'.1

theorem range_lowerHemisphere_union_range_upperHemisphere (m : ℕ) :
    range (lowerHemisphere m) ∪ range (upperHemisphere m) = univ := by
  apply eq_univ_of_forall
  intro z
  have hz : ‖(z : EuclideanSpace ℝ (Fin (m + 2)))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  set t := (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) with ht
  set x := euclidInit (z : EuclideanSpace ℝ (Fin (m + 2))) with hxdef
  have hzx : euclidSnoc x t = z := euclidSnoc_euclidInit _
  have hsq : ‖x‖ ^ 2 + t ^ 2 = 1 := by
    rw [← norm_euclidSnoc_sq, hzx, hz]; norm_num
  have hxle : ‖x‖ ≤ 1 := by
    have := norm_nonneg x
    nlinarith [sq_nonneg t]
  let xd : Disk (m + 1) := ⟨x, mem_closedBall_zero_iff.mpr hxle⟩
  have hh : diskHeight xd = |t| := by
    rw [diskHeight, ← Real.sqrt_sq_eq_abs]
    congr 1
    change 1 - ‖x‖ ^ 2 = t ^ 2
    linarith
  rcases le_or_gt t 0 with htle | htpos
  · refine Or.inl ⟨xd, Subtype.ext ?_⟩
    rw [lowerHemisphere_coe, hh, abs_of_nonpos htle, neg_neg]
    exact hzx
  · refine Or.inr ⟨xd, Subtype.ext ?_⟩
    rw [upperHemisphere_coe, hh, abs_of_pos htpos]
    exact hzx

theorem lowerHemisphere_eq_upperHemisphere_iff (m : ℕ) (x y : Disk (m + 1)) :
    lowerHemisphere m x = upperHemisphere m y ↔ x = y ∧ x ∈ diskSphere (m + 1) := by
  rw [Subtype.ext_iff, lowerHemisphere_coe, upperHemisphere_coe, euclidSnoc_inj,
    ← Subtype.ext_iff]
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, (diskHeight_eq_zero_iff x).mp ?_⟩
    linarith
  · rintro ⟨rfl, h⟩
    rw [(diskHeight_eq_zero_iff x).mpr h]
    simp

theorem twisted_sphere_homeomorph {m : ℕ} {X : Type*} [TopologicalSpace X]
    {e₀ e₁ : Disk (m + 1) → X} (h₀ : IsClosedEmbedding e₀) (h₁ : IsClosedEmbedding e₁)
    (hcover : range e₀ ∪ range e₁ = univ)
    (hinter : range e₀ ∩ range e₁ = e₀ '' diskSphere (m + 1))
    (hbdry : e₀ '' diskSphere (m + 1) = e₁ '' diskSphere (m + 1)) :
    Nonempty (X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) := by
  classical
  have : CompactSpace X := by
    rw [← isCompact_univ_iff, ← hcover]
    exact (isCompact_range h₀.continuous).union (isCompact_range h₁.continuous)
  let φ₀ : diskSphere (m + 1) ≃ₜ (e₀ '' diskSphere (m + 1) : Set X) :=
    h₀.isEmbedding.homeomorphImage (diskSphere (m + 1))
  let φ₁ : diskSphere (m + 1) ≃ₜ (e₁ '' diskSphere (m + 1) : Set X) :=
    h₁.isEmbedding.homeomorphImage (diskSphere (m + 1))
  let ψ : diskSphere (m + 1) ≃ₜ diskSphere (m + 1) :=
    φ₀.trans ((Homeomorph.setCongr hbdry).trans φ₁.symm)
  have hψ : ∀ s : diskSphere (m + 1), e₁ (ψ s) = e₀ s := by
    intro s
    have h1 : ∀ t : diskSphere (m + 1), (φ₁ t : X) = e₁ t := fun t => rfl
    have h0 : ∀ t : diskSphere (m + 1), (φ₀ t : X) = e₀ t := fun t => rfl
    rw [← h1, ← h0]
    simp only [ψ, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
    rfl
  let D := diskSphereHomeomorph (m + 1)
  let h : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := D.symm.trans (ψ.trans D)
  obtain ⟨G, hG⟩ := alexander_trick h.symm
  have hGψ : ∀ t : diskSphere (m + 1), G (t : Disk (m + 1)) = (ψ.symm t : Disk (m + 1)) := by
    intro t
    have hD : ∀ u : diskSphere (m + 1), ((D u : EuclideanSpace ℝ (Fin (m + 1)))) =
      ((u : Disk (m + 1)) : EuclideanSpace ℝ (Fin (m + 1))) := fun u => rfl
    have ht : (t : Disk (m + 1)) = ⟨D t, sphere_subset_closedBall (D t).2⟩ := Subtype.ext rfl
    rw [ht, hG (D t)]
    apply Subtype.ext
    change ((h.symm (D t) : EuclideanSpace ℝ (Fin (m + 1)))) = _
    have : h.symm (D t) = D (ψ.symm t) := by
      simp only [h, Homeomorph.symm_trans_apply, Homeomorph.symm_symm, Homeomorph.symm_apply_apply]
    rw [this, hD]
  have hGψ' : ∀ t : diskSphere (m + 1), G (ψ t : Disk (m + 1)) = (t : Disk (m + 1)) := by
    intro t
    rw [hGψ, Homeomorph.symm_apply_apply]
  let E₀ : Disk (m + 1) ≃ₜ range e₀ := h₀.isEmbedding.toHomeomorph
  let E₁ : Disk (m + 1) ≃ₜ range e₁ := h₁.isEmbedding.toHomeomorph
  have hmem₁ : ∀ x : X, x ∉ range e₀ → x ∈ range e₁ := by
    intro x hx
    have : x ∈ range e₀ ∪ range e₁ := by rw [hcover]; exact mem_univ x
    exact this.resolve_left hx
  let F : X → sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 := fun x =>
    if hx : x ∈ range e₀ then lowerHemisphere m (E₀.symm ⟨x, hx⟩)
    else upperHemisphere m (G (E₁.symm ⟨x, hmem₁ x hx⟩))
  have hE₀ : ∀ (d : Disk (m + 1)) (hx : e₀ d ∈ range e₀), E₀.symm ⟨e₀ d, hx⟩ = d := by
    intro d hx
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext rfl
  have hE₁ : ∀ (d : Disk (m + 1)) (hx : e₁ d ∈ range e₁), E₁.symm ⟨e₁ d, hx⟩ = d := by
    intro d hx
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext rfl
  have hF₀ : ∀ (x : X) (hx : x ∈ range e₀), F x = lowerHemisphere m (E₀.symm ⟨x, hx⟩) := by
    intro x hx
    simp only [F, dite_eq_left hx]
  have hF₁ : ∀ (x : X) (hx : x ∈ range e₁), F x = upperHemisphere m (G (E₁.symm ⟨x, hx⟩)) := by
    intro x hx
    by_cases hx₀ : x ∈ range e₀
    · rw [hF₀ x hx₀]
      have hx' : x ∈ e₀ '' diskSphere (m + 1) := by rw [← hinter]; exact ⟨hx₀, hx⟩
      obtain ⟨s, hs, rfl⟩ := hx'
      rw [hE₀ s hx₀]
      have : e₀ s = e₁ (ψ ⟨s, hs⟩) := (hψ ⟨s, hs⟩).symm
      have h2 : E₁.symm ⟨e₀ s, hx⟩ = (ψ ⟨s, hs⟩ : Disk (m + 1)) := by
        rw [Homeomorph.symm_apply_eq]
        exact Subtype.ext this
      rw [h2, hGψ']
      exact (lowerHemisphere_eq_upperHemisphere_iff m s s).mpr ⟨rfl, hs⟩
    · simp only [F, dite_eq_right hx₀]
  have hF : Continuous F := by
    rw [← continuousOn_univ, ← hcover]
    refine ContinuousOn.union_of_isClosed ?_ ?_ h₀.isClosed_range h₁.isClosed_range
    · rw [continuousOn_iff_continuous_domRestrict]
      have : (range e₀).domRestrict F = fun y => lowerHemisphere m (E₀.symm y) := by
        funext y
        rw [Set.domRestrict_apply, hF₀ y y.2]
      rw [this]
      exact (continuous_lowerHemisphere m).comp E₀.symm.continuous
    · rw [continuousOn_iff_continuous_domRestrict]
      have : (range e₁).domRestrict F = fun y => upperHemisphere m (G (E₁.symm y)) := by
        funext y
        rw [Set.domRestrict_apply, hF₁ y y.2]
      rw [this]
      exact (continuous_upperHemisphere m).comp (G.continuous.comp E₁.symm.continuous)
  have hinj₀ : ∀ x y : X, x ∈ range e₀ → y ∈ range e₀ → F x = F y → x = y := by
    intro x y hx hy hxy
    rw [hF₀ x hx, hF₀ y hy] at hxy
    have := E₀.symm.injective (lowerHemisphere_injective m hxy)
    exact congrArg Subtype.val this
  have hinj₁ : ∀ x y : X, x ∈ range e₁ → y ∈ range e₁ → F x = F y → x = y := by
    intro x y hx hy hxy
    rw [hF₁ x hx, hF₁ y hy] at hxy
    have := E₁.symm.injective (G.injective (upperHemisphere_injective m hxy))
    exact congrArg Subtype.val this
  have hmixed : ∀ x y : X, x ∈ range e₀ → y ∉ range e₀ → F x = F y → x ∈ range e₁ := by
    intro x y hx hy hxy
    rw [hF₀ x hx] at hxy
    simp only [F, dite_eq_right hy] at hxy
    obtain ⟨-, hs⟩ := (lowerHemisphere_eq_upperHemisphere_iff m _ _).mp hxy
    have : x ∈ e₀ '' diskSphere (m + 1) := ⟨E₀.symm ⟨x, hx⟩, hs, by
      have := congrArg Subtype.val (E₀.apply_symm_apply ⟨x, hx⟩)
      exact this⟩
    rw [← hinter] at this
    exact this.2
  have hinj : Function.Injective F := by
    intro x y hxy
    by_cases hx₀ : x ∈ range e₀
    · by_cases hy₀ : y ∈ range e₀
      · exact hinj₀ x y hx₀ hy₀ hxy
      · exact hinj₁ x y (hmixed x y hx₀ hy₀ hxy) (hmem₁ y hy₀) hxy
    · by_cases hy₀ : y ∈ range e₀
      · exact hinj₁ x y (hmem₁ x hx₀) (hmixed y x hy₀ hx₀ hxy.symm) hxy
      · exact hinj₁ x y (hmem₁ x hx₀) (hmem₁ y hy₀) hxy
  have hsurj : Function.Surjective F := by
    intro z
    have hz : z ∈ range (lowerHemisphere m) ∪ range (upperHemisphere m) := by
      rw [range_lowerHemisphere_union_range_upperHemisphere]; exact mem_univ z
    rcases hz with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨e₀ d, ?_⟩
      rw [hF₀ (e₀ d) (mem_range_self d), hE₀]
    · refine ⟨e₁ (G.symm d), ?_⟩
      rw [hF₁ (e₁ (G.symm d)) (mem_range_self _), hE₁, Homeomorph.apply_symm_apply]
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hinj, hsurj⟩) hF⟩

end DifferentialGeometry.Topology
