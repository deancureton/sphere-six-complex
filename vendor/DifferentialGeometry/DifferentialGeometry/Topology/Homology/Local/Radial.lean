module

public import DifferentialGeometry.Topology.Homology.Spheres.SphereTopology

@[expose] public section

open Metric Set unitInterval
open scoped ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

abbrev EU (n : ℕ) : Type u := ULift.{u} (EuclideanSpace ℝ (Fin n))

namespace Radial

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def retr (x : E) (ρ : ℝ) (y : E) : E := x + (ρ * ‖y - x‖⁻¹) • (y - x)

lemma retr_sub (x : E) (ρ : ℝ) (y : E) : retr x ρ y - x = (ρ * ‖y - x‖⁻¹) • (y - x) := by
  simp [retr]

lemma norm_retr_sub {x y : E} (hy : y ≠ x) {ρ : ℝ} (hρ : 0 ≤ ρ) : ‖retr x ρ y - x‖ = ρ := by
  have h : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hy)
  rw [retr_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc,
    inv_mul_cancel₀ h, mul_one]

lemma retr_ne {x y : E} (hy : y ≠ x) {ρ : ℝ} (hρ : 0 < ρ) : retr x ρ y ≠ x := by
  intro h
  have := norm_retr_sub hy hρ.le
  rw [h, sub_self, norm_zero] at this
  exact hρ.ne this

lemma retr_add_of_norm_eq_one (x : E) {u : E} (hu : ‖u‖ = 1) : retr x 1 (x + u) = x + u := by
  simp [retr, hu]

lemma continuous_retr (x : E) (ρ : ℝ) :
    Continuous fun y : ({x}ᶜ : Set E) => retr x ρ (y : E) := by
  have h1 : Continuous fun y : ({x}ᶜ : Set E) => (y : E) - x :=
    continuous_subtype_val.sub continuous_const
  have h2 : Continuous fun y : ({x}ᶜ : Set E) => ‖(y : E) - x‖⁻¹ :=
    h1.norm.inv₀ fun y => norm_ne_zero_iff.2 (sub_ne_zero.2 (mem_compl_singleton_iff.1 y.2))
  exact continuous_const.add ((continuous_const.mul h2).smul h1)

variable {X : Type*} [TopologicalSpace X] {A : Set E}

def lineHomotopy (f₀ f₁ : C(X, A))
    (h : ∀ (t : I) (p : X), (f₀ p : E) + (t : ℝ) • ((f₁ p : E) - f₀ p) ∈ A) :
    f₀.Homotopy f₁ where
  toFun tp := ⟨(f₀ tp.2 : E) + (tp.1 : ℝ) • ((f₁ tp.2 : E) - f₀ tp.2), h tp.1 tp.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hf₀ : Continuous fun tp : I × X => (f₀ tp.2 : E) :=
      continuous_subtype_val.comp (f₀.continuous.comp continuous_snd)
    have hf₁ : Continuous fun tp : I × X => (f₁ tp.2 : E) :=
      continuous_subtype_val.comp (f₁.continuous.comp continuous_snd)
    have ht : Continuous fun tp : I × X => (tp.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact hf₀.add (ht.smul (hf₁.sub hf₀))
  map_zero_left p := by ext; simp
  map_one_left p := by ext; simp

lemma line_retr_sub (x : E) (ρ t : ℝ) (y : E) :
    (y + t • (retr x ρ y - y)) - x = ((1 - t) + t * (ρ * ‖y - x‖⁻¹)) • (y - x) := by
  rw [retr]
  module

lemma line_retr_ne {x y : E} (hy : y ≠ x) {ρ : ℝ} (hρ : 0 < ρ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : y + t • (retr x ρ y - y) ≠ x := by
  intro h
  have h0 := sub_eq_zero.2 h
  rw [line_retr_sub] at h0
  rcases smul_eq_zero.1 h0 with h0 | h0
  · have hv : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
    have hpos : 0 < (1 - t) + t * (ρ * ‖y - x‖⁻¹) := by
      rcases eq_or_lt_of_le ht1 with rfl | ht1
      · simp only [sub_self, one_mul, zero_add]
        positivity
      · have : 0 ≤ t * (ρ * ‖y - x‖⁻¹) := by positivity
        linarith
    exact hpos.ne' h0
  · exact hy (sub_eq_zero.1 h0)

lemma line_retr_notMem {C : Set E} (hC : Convex ℝ C) {x : E} (hx : x ∈ C) {R : ℝ}
    (hCR : C ⊆ closedBall x R) {ρ : ℝ} (hρ : R < ρ) {y : E} (hy : y ∉ C) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : y + t • (retr x ρ y - y) ∉ C := by
  intro hmem
  have hyx : y ≠ x := fun h => hy (h ▸ hx)
  have hv : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  have hR0 : 0 ≤ R := by simpa using hCR hx
  have hρ0 : 0 < ρ := hR0.trans_lt hρ
  set s : ℝ := (1 - t) + t * (ρ * ‖y - x‖⁻¹) with hs
  have hs0 : 0 ≤ s := by
    have : 0 ≤ t * (ρ * ‖y - x‖⁻¹) := by positivity
    linarith
  have hpt : y + t • (retr x ρ y - y) = x + s • (y - x) := by
    rw [← line_retr_sub]; abel
  have hR : s * ‖y - x‖ ≤ R := by
    have := hCR hmem
    rw [mem_closedBall, dist_eq_norm, hpt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs0] at this
    exact this
  have hsv : s * ‖y - x‖ = (1 - t) * ‖y - x‖ + t * ρ := by
    rw [hs]
    field_simp
  have hvρ : ‖y - x‖ < ρ := by
    by_contra hcon
    have hcon := not_lt.1 hcon
    nlinarith [mul_le_mul_of_nonneg_left hcon (sub_nonneg.2 ht1)]
  have hs1 : 1 ≤ s := by
    have h1 : 1 < ρ * ‖y - x‖⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (one_lt_div hv).2 hvρ
    have : 0 ≤ t * (ρ * ‖y - x‖⁻¹ - 1) := mul_nonneg ht0 (sub_nonneg.2 h1.le)
    rw [hs]
    linarith
  have hmem' : x + s⁻¹ • (s • (y - x)) ∈ C :=
    hC.add_smul_mem hx (hpt ▸ hmem) ⟨inv_nonneg.2 hs0, inv_le_one_of_one_le₀ hs1⟩
  rw [smul_smul, inv_mul_cancel₀ (by linarith), one_smul, add_sub_cancel] at hmem'
  exact hy hmem'

section Convex

variable {C : Set E} {x : E}

def inclCompl (hx : x ∈ C) : C((Cᶜ : Set E), ({x}ᶜ : Set E)) :=
  ⟨fun y => ⟨y, fun h => y.2 (mem_singleton_iff.1 h ▸ hx)⟩, continuous_subtype_val.subtype_mk _⟩

omit [NormedSpace ℝ E] in
@[simp] lemma inclCompl_apply (hx : x ∈ C) (y : (Cᶜ : Set E)) : (inclCompl hx y : E) = y := rfl

def retrCompl (hx : x ∈ C) {R : ℝ} (hCR : C ⊆ closedBall x R) {ρ : ℝ} (hρ : R < ρ) :
    C(({x}ᶜ : Set E), (Cᶜ : Set E)) :=
  ⟨fun y => ⟨retr x ρ y, fun h => by
    have hR0 : 0 ≤ R := by simpa using hCR hx
    have := hCR h
    rw [mem_closedBall, dist_eq_norm,
      norm_retr_sub (mem_compl_singleton_iff.1 y.2) (le_of_lt (lt_of_le_of_lt hR0 hρ))] at this
    exact absurd hρ (not_lt.2 this)⟩,
    (continuous_retr x ρ).subtype_mk _⟩

@[simp] lemma retrCompl_apply (hx : x ∈ C) {R : ℝ} (hCR : C ⊆ closedBall x R) {ρ : ℝ}
    (hρ : R < ρ) (y : ({x}ᶜ : Set E)) : (retrCompl hx hCR hρ y : E) = retr x ρ y := rfl

def homotopyEquivComplOfSubsetClosedBall (hC : Convex ℝ C) (hx : x ∈ C) {R : ℝ}
    (hCR : C ⊆ closedBall x R) {ρ : ℝ} (hρ : R < ρ) :
    (Cᶜ : Set E) ≃ₕ ({x}ᶜ : Set E) where
  toFun := inclCompl hx
  invFun := retrCompl hx hCR hρ
  left_inv :=
    ⟨(lineHomotopy (ContinuousMap.id _) ((retrCompl hx hCR hρ).comp (inclCompl hx)) fun t y =>
      line_retr_notMem hC hx hCR hρ y.2 t.2.1 t.2.2).symm⟩
  right_inv := by
    have hR0 : 0 ≤ R := by simpa using hCR hx
    exact ⟨(lineHomotopy (ContinuousMap.id _) ((inclCompl hx).comp (retrCompl hx hCR hρ)) fun t y =>
      line_retr_ne (mem_compl_singleton_iff.1 y.2) (hR0.trans_lt hρ) t.2.1 t.2.2).symm⟩

@[simp] lemma homotopyEquivComplOfSubsetClosedBall_toFun_apply (hC : Convex ℝ C) (hx : x ∈ C)
    {R : ℝ} (hCR : C ⊆ closedBall x R) {ρ : ℝ} (hρ : R < ρ) (y : (Cᶜ : Set E)) :
    ((homotopyEquivComplOfSubsetClosedBall hC hx hCR hρ).toFun y : E) = y := rfl

end Convex

end Radial

open Radial

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def homotopyEquivComplConvexSingleton {C : Set E} (hC : Convex ℝ C) (hCb : Bornology.IsBounded C)
    {x : E} (hx : x ∈ C) : (Cᶜ : Set E) ≃ₕ ({x}ᶜ : Set E) :=
  homotopyEquivComplOfSubsetClosedBall hC hx (hCb.subset_closedBall x).choose_spec
    (lt_add_one (hCb.subset_closedBall x).choose)

@[simp] lemma homotopyEquivComplConvexSingleton_toFun_apply {C : Set E} (hC : Convex ℝ C)
    (hCb : Bornology.IsBounded C) {x : E} (hx : x ∈ C) (y : (Cᶜ : Set E)) :
    ((homotopyEquivComplConvexSingleton hC hCb hx).toFun y : E) = y := rfl

theorem exists_homotopyEquiv_compl_convex_singleton {C : Set E} (hC : Convex ℝ C)
    (hCb : Bornology.IsBounded C) {x : E} (hx : x ∈ C) :
    ∃ e : (Cᶜ : Set E) ≃ₕ ({x}ᶜ : Set E), ∀ y, (e.toFun y : E) = y :=
  ⟨homotopyEquivComplConvexSingleton hC hCb hx, fun _ => rfl⟩

namespace Radial

variable (x : E)

def toSphere : C(({x}ᶜ : Set E), sphere (0 : E) 1) :=
  ⟨fun y => ⟨retr x 1 y - x,
    mem_sphere_zero_iff_norm.2 (norm_retr_sub (mem_compl_singleton_iff.1 y.2) zero_le_one)⟩,
    ((continuous_retr x 1).sub continuous_const).subtype_mk _⟩

def ofSphere : C(sphere (0 : E) 1, ({x}ᶜ : Set E)) :=
  ⟨fun u => ⟨x + u, fun h => by
    have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
    have : (u : E) = 0 := by simpa using (mem_singleton_iff.1 h)
    simp [this] at hu⟩,
    (continuous_const.add continuous_subtype_val).subtype_mk _⟩

end Radial

def homotopyEquivComplSingletonSphere (x : E) : ({x}ᶜ : Set E) ≃ₕ sphere (0 : E) 1 where
  toFun := toSphere x
  invFun := ofSphere x
  left_inv :=
    ⟨(lineHomotopy (ContinuousMap.id _) ((ofSphere x).comp (toSphere x)) fun t y => by
      change (y : E) + (t : ℝ) • ((x + (retr x 1 y - x)) - y) ∈ ({x}ᶜ : Set E)
      rw [add_sub_cancel]
      exact line_retr_ne (mem_compl_singleton_iff.1 y.2) one_pos t.2.1 t.2.2).symm⟩
  right_inv := by
    have : (toSphere x).comp (ofSphere x) = ContinuousMap.id _ := by
      ext u
      change retr x 1 (x + u) - x = u
      rw [retr_add_of_norm_eq_one x (mem_sphere_zero_iff_norm.1 u.2), add_sub_cancel_left]
    rw [this]

lemma image_ulift_compl_singleton {n : ℕ} (x : EU.{u} n) :
    (Homeomorph.ulift.{u} (X := EuclideanSpace ℝ (Fin n))) '' ({x}ᶜ : Set (EU n)) =
      ({x.down}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩ h
    exact hz (ULift.ext h)
  · intro h
    exact ⟨⟨y⟩, fun h' => h (congrArg ULift.down h'), rfl⟩

def puncturedEUHomotopyEquivSph (n : ℕ) (x : EU.{u} (n + 1)) :
    ({x}ᶜ : Set (EU (n + 1))) ≃ₕ unitSphere n :=
  ((Homeomorph.ulift.{u}.image ({x}ᶜ : Set (EU (n + 1)))).trans
    (Homeomorph.setCongr (image_ulift_compl_singleton x))).toHomotopyEquiv.trans
    (homotopyEquivComplSingletonSphere x.down)

end DifferentialGeometry.Topology.SingularPair
