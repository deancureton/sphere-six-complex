module

public import DifferentialGeometry.Topology.Morse.Strip.StripFlow

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter DifferentialGeometry
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split)

noncomputable section

theorem eq_of_eventually_eq_of_isPreconnected {X α : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {cls : X → α} (hloc : ∀ x ∈ s, ∀ᶠ y in 𝓝 x, cls y = cls x)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : cls x = cls y := by
  have hlc : IsLocallyConstant (fun z : s => cls z) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    exact continuousAt_subtype_val.eventually (hloc z z.2)
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.1 hs
  exact hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

theorem eq_of_eventually_eq_of_connectedSpace {X α : Type*} [TopologicalSpace X] {s : Set X}
    (hs : ConnectedSpace s) {cls : X → α} (hloc : ∀ x ∈ s, ∀ᶠ y in 𝓝 x, cls y = cls x)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : cls x = cls y :=
  eq_of_eventually_eq_of_isPreconnected (isConnected_iff_connectedSpace.2 hs).isPreconnected
    hloc hx hy

namespace ModifiedWithin

variable {M : Type*} {f g : M → ℝ} {a b : ℝ}

theorem connectedSpace_preimage_Icc_iff [TopologicalSpace M] (h : ModifiedWithin f a b g) :
    ConnectedSpace (g ⁻¹' Icc a b) ↔ ConnectedSpace (f ⁻¹' Icc a b) := by
  rw [h.preimage_Icc]

theorem nonempty_preimage_singleton_left_iff (h : ModifiedWithin f a b g) :
    (g ⁻¹' {a}).Nonempty ↔ (f ⁻¹' {a}).Nonempty := by
  rw [h.preimage_singleton_left]

theorem nonempty_preimage_singleton_right_iff (h : ModifiedWithin f a b g) :
    (g ⁻¹' {b}).Nonempty ↔ (f ⁻¹' {b}).Nonempty := by
  rw [h.preimage_singleton_right]

end ModifiedWithin

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem strip_constant_of_locallyConstant {f : M → ℝ} {a b : ℝ}
    (hconn : ConnectedSpace (f ⁻¹' Icc a b)) {α : Type*} {cls : M → α}
    (hloc : ∀ x, f x ∈ Icc a b → ∀ᶠ y in 𝓝 x, cls y = cls x) :
    ∀ x y, f x ∈ Icc a b → f y ∈ Icc a b → cls x = cls y := fun _ _ hx hy =>
  eq_of_eventually_eq_of_connectedSpace hconn (fun z hz => hloc z hz) hx hy

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ}
  {crit : Finset M}

namespace GradientLikeStrip

variable (D : GradientLikeStrip I f a b crit)

theorem constant_of_locallyConstant (hconn : ConnectedSpace (f ⁻¹' Icc a b)) {α : Type*}
    {cls : M → α} (hloc : ∀ x, f x ∈ Icc a b → ∀ᶠ y in 𝓝 x, cls y = cls x) :
    ∀ x y, f x ∈ Icc a b → f y ∈ Icc a b → cls x = cls y :=
  strip_constant_of_locallyConstant hconn hloc

theorem notMem_smallBall_of_notMem_Ioo {z : M} (hz : f z ∉ Ioo a b) (p : M) (hp : p ∈ crit) :
    z ∉ D.smallBall p hp := fun h =>
  hz (D.inStrip p hp (D.smallBall_subset_image_ball p hp h))

theorem dfV_eq_neg_one_of_f_eq_a (hab : a ≤ b) {z : M} (hz : f z = a) : dfV I f D.V z = -1 :=
  D.unit z ⟨hz.ge, hz.le.trans hab⟩ fun p hp =>
    D.notMem_smallBall_of_notMem_Ioo (by rw [hz]; exact fun h => lt_irrefl a h.1) p hp

theorem dfV_eq_neg_one_of_f_eq_b (hab : a ≤ b) {z : M} (hz : f z = b) : dfV I f D.V z = -1 :=
  D.unit z ⟨hab.trans hz.ge, hz.le⟩ fun p hp =>
    D.notMem_smallBall_of_notMem_Ioo (by rw [hz]; exact fun h => lt_irrefl b h.2) p hp

variable [T2Space M] [I.Boundaryless]
variable {D}

theorem eventually_f_flow_lt_of_dfV_eq_neg_one (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {z : M}
    (hz : dfV I f D.V z = -1) : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (D.flow t z) < f z := by
  have hd : HasDerivAt (fun s => f (D.flow s z)) (-1) 0 := by
    have := hasDerivAt_f_flow (D := D) hf z 0
    rwa [flow_zero, hz] at this
  have hs := hd.hasDerivWithinAt.limsup_slope_le' (s := Ioi 0) (fun h => lt_irrefl _ (mem_Ioi.1 h))
    (by norm_num : (-1 : ℝ) < 0)
  filter_upwards [hs, eventually_mem_nhdsWithin] with t ht ht0
  rw [slope_def_field, flow_zero, sub_zero] at ht
  have ht0' : (0 : ℝ) < t := ht0
  by_contra h
  rw [not_lt] at h
  exact absurd ht (not_lt.2 (div_nonneg (sub_nonneg.2 h) ht0'.le))

theorem eventually_lt_f_flow_of_dfV_eq_neg_one (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {z : M}
    (hz : dfV I f D.V z = -1) : ∀ᶠ t in 𝓝[<] (0 : ℝ), f z < f (D.flow t z) := by
  have hd : HasDerivAt (fun s => f (D.flow s z)) (-1) 0 := by
    have := hasDerivAt_f_flow (D := D) hf z 0
    rwa [flow_zero, hz] at this
  have hs := hd.hasDerivWithinAt.limsup_slope_le' (s := Iio 0) (fun h => lt_irrefl _ (mem_Iio.1 h))
    (by norm_num : (-1 : ℝ) < 0)
  filter_upwards [hs, eventually_mem_nhdsWithin] with t ht ht0
  rw [slope_def_field, flow_zero, sub_zero] at ht
  have ht0' : t < (0 : ℝ) := ht0
  by_contra h
  rw [not_lt] at h
  exact absurd ht (not_lt.2 (div_nonneg_of_nonpos (sub_nonpos.2 h) ht0'.le))

variable (D)

theorem eventually_f_flow_lt_of_f_eq_a (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a ≤ b) {z : M}
    (hz : f z = a) : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (D.flow t z) < a :=
  hz ▸ eventually_f_flow_lt_of_dfV_eq_neg_one hf (D.dfV_eq_neg_one_of_f_eq_a hab hz)

theorem eventually_lt_f_flow_of_f_eq_a (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a ≤ b) {z : M}
    (hz : f z = a) : ∀ᶠ t in 𝓝[<] (0 : ℝ), a < f (D.flow t z) :=
  hz ▸ eventually_lt_f_flow_of_dfV_eq_neg_one hf (D.dfV_eq_neg_one_of_f_eq_a hab hz)

theorem eventually_f_flow_lt_of_f_eq_b (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a ≤ b) {z : M}
    (hz : f z = b) : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (D.flow t z) < b :=
  hz ▸ eventually_f_flow_lt_of_dfV_eq_neg_one hf (D.dfV_eq_neg_one_of_f_eq_b hab hz)

theorem eventually_lt_f_flow_of_f_eq_b (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a ≤ b) {z : M}
    (hz : f z = b) : ∀ᶠ t in 𝓝[<] (0 : ℝ), b < f (D.flow t z) :=
  hz ▸ eventually_lt_f_flow_of_dfV_eq_neg_one hf (D.dfV_eq_neg_one_of_f_eq_b hab hz)

theorem exists_bottom_near_level (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (ha : (f ⁻¹' {a}).Nonempty) {η : ℝ} (hη : 0 < η) :
    ∃ x, f x ∈ Ioo a b ∧ f x < a + η ∧ ∃ t, 0 ≤ t ∧ f (D.flow t x) < a := by
  obtain ⟨z, hz⟩ := ha
  have hz : f z = a := hz
  have hm : 0 < min η (b - a) := lt_min hη (sub_pos.2 hab)
  obtain ⟨s, hs, hs'⟩ := ((D.eventually_lt_f_flow_of_f_eq_a hf hab.le hz).and
    (Ioo_mem_nhdsLT (by linarith : -min η (b - a) < 0))).exists
  obtain ⟨u, hu, hu'⟩ := ((D.eventually_f_flow_lt_of_f_eq_a hf hab.le hz).and
    (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have hsub := f_flow_le_sub_of_nonpos (D := D) hf z hs'.2.le
  rw [hz] at hsub
  refine ⟨D.flow s z, ⟨hs, ?_⟩, ?_, u - s, by linarith [hu'.1, hs'.2], ?_⟩
  · linarith [min_le_right η (b - a), hs'.1]
  · linarith [min_le_left η (b - a), hs'.1]
  · rw [flow_flow, add_sub_cancel]
    exact hu

theorem exists_bottom_point (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (ha : (f ⁻¹' {a}).Nonempty) :
    ∃ x, f x ∈ Ioo a b ∧ ∃ t, 0 ≤ t ∧ f (D.flow t x) < a := by
  obtain ⟨x, hx, -, ht⟩ := D.exists_bottom_near_level hf hab ha zero_lt_one
  exact ⟨x, hx, ht⟩

theorem exists_top_near_level (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hb : (f ⁻¹' {b}).Nonempty) {η : ℝ} (hη : 0 < η) :
    ∃ x, f x ∈ Ioo a b ∧ b - η < f x ∧ ∃ t, 0 ≤ t ∧ b < f (D.flow (-t) x) := by
  obtain ⟨z, hz⟩ := hb
  have hz : f z = b := hz
  have hm : 0 < min η (b - a) := lt_min hη (sub_pos.2 hab)
  obtain ⟨s, hs, hs'⟩ := ((D.eventually_f_flow_lt_of_f_eq_b hf hab.le hz).and
    (Ioo_mem_nhdsGT hm)).exists
  obtain ⟨u, hu, hu'⟩ := ((D.eventually_lt_f_flow_of_f_eq_b hf hab.le hz).and
    (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 0))).exists
  have hsub := sub_le_f_flow (D := D) hf z hs'.1.le
  rw [hz] at hsub
  refine ⟨D.flow s z, ⟨?_, hs⟩, ?_, s - u, by linarith [hu'.2, hs'.1], ?_⟩
  · linarith [min_le_right η (b - a), hs'.2]
  · linarith [min_le_left η (b - a), hs'.2]
  · rw [flow_flow, show s + -(s - u) = u by ring]
    exact hu

theorem exists_top_point (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hb : (f ⁻¹' {b}).Nonempty) :
    ∃ x, f x ∈ Ioo a b ∧ ∃ t, 0 ≤ t ∧ b < f (D.flow (-t) x) := by
  obtain ⟨x, hx, -, ht⟩ := D.exists_top_near_level hf hab hb zero_lt_one
  exact ⟨x, hx, ht⟩

def collarRetract (a' b' : ℝ) (x : M) : M :=
  D.flow (f x - max a' (min b' (f x))) x

theorem continuous_collarRetract (hf : Continuous f) (a' b' : ℝ) :
    Continuous (D.collarRetract a' b') := by
  have h1 : Continuous fun x => f x - max a' (min b' (f x)) :=
    hf.sub (continuous_const.max (continuous_const.min hf))
  exact D.continuous_flow_joint.comp (h1.prodMk continuous_id)

theorem collarRetract_of_mem {a' b' : ℝ} {x : M} (hx : f x ∈ Icc a' b') :
    D.collarRetract a' b' x = x := by
  unfold collarRetract
  rw [min_eq_right hx.2, max_eq_right hx.1, sub_self, flow_zero]

theorem f_collarRetract (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a' b' : ℝ} (ha' : a ≤ a')
    (hab' : a' ≤ b') (hb' : b' ≤ b)
    (hU₁ : ∀ y, f y ∈ Icc a a' → ∀ p hp, y ∉ D.smallBall p hp)
    (hU₂ : ∀ y, f y ∈ Icc b' b → ∀ p hp, y ∉ D.smallBall p hp) {x : M} (hx : f x ∈ Icc a b) :
    f (D.collarRetract a' b' x) = max a' (min b' (f x)) := by
  rcases lt_or_ge (f x) a' with h₁ | h₁
  · have hmin : min b' (f x) = f x := min_eq_right (h₁.le.trans hab')
    have hmax : max a' (f x) = a' := max_eq_left h₁.le
    unfold collarRetract
    rw [hmin, hmax]
    have := (flow_level_transport (D := D) hf (c' := f x) (c := a') hx.1 h₁.le
      (hab'.trans hb') fun y hy => hU₁ y ⟨hx.1.trans hy.1, hy.2⟩).2 x rfl
    exact this.1
  rcases le_or_gt (f x) b' with h₂ | h₂
  · rw [D.collarRetract_of_mem ⟨h₁, h₂⟩, min_eq_right h₂, max_eq_right h₁]
  · have hmin : min b' (f x) = b' := min_eq_left h₂.le
    have hmax : max a' b' = b' := max_eq_right hab'
    unfold collarRetract
    rw [hmin, hmax]
    have := (flow_level_transport (D := D) hf (c' := b') (c := f x) (ha'.trans hab') h₂.le
      hx.2 fun y hy => hU₂ y ⟨hy.1, hy.2.trans hx.2⟩).1 x rfl
    exact this.1

theorem collarRetract_mem (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a' b' : ℝ} (ha' : a ≤ a')
    (hab' : a' ≤ b') (hb' : b' ≤ b)
    (hU₁ : ∀ y, f y ∈ Icc a a' → ∀ p hp, y ∉ D.smallBall p hp)
    (hU₂ : ∀ y, f y ∈ Icc b' b → ∀ p hp, y ∉ D.smallBall p hp) {x : M} (hx : f x ∈ Icc a b) :
    f (D.collarRetract a' b' x) ∈ Icc a' b' := by
  rw [D.f_collarRetract hf ha' hab' hb' hU₁ hU₂ hx]
  exact ⟨le_max_left _ _, max_le hab' (min_le_left _ _)⟩

theorem image_collarRetract (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a' b' : ℝ} (ha' : a ≤ a')
    (hab' : a' ≤ b') (hb' : b' ≤ b)
    (hU₁ : ∀ y, f y ∈ Icc a a' → ∀ p hp, y ∉ D.smallBall p hp)
    (hU₂ : ∀ y, f y ∈ Icc b' b → ∀ p hp, y ∉ D.smallBall p hp) :
    D.collarRetract a' b' '' (f ⁻¹' Icc a b) = f ⁻¹' Icc a' b' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact D.collarRetract_mem hf ha' hab' hb' hU₁ hU₂ hx
  · intro hy
    exact ⟨y, ⟨ha'.trans hy.1, hy.2.trans hb'⟩, D.collarRetract_of_mem hy⟩

theorem isConnected_substrip (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hconn : IsConnected (f ⁻¹' Icc a b)) {a' b' : ℝ} (ha' : a ≤ a') (hab' : a' ≤ b')
    (hb' : b' ≤ b) (hU₁ : ∀ y, f y ∈ Icc a a' → ∀ p hp, y ∉ D.smallBall p hp)
    (hU₂ : ∀ y, f y ∈ Icc b' b → ∀ p hp, y ∉ D.smallBall p hp) :
    IsConnected (f ⁻¹' Icc a' b') := by
  rw [← D.image_collarRetract hf ha' hab' hb' hU₁ hU₂]
  exact hconn.image _ (D.continuous_collarRetract hf.continuous a' b').continuousOn

theorem connectedSpace_substrip (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hconn : ConnectedSpace (f ⁻¹' Icc a b)) {a' b' : ℝ} (ha' : a ≤ a') (hab' : a' ≤ b')
    (hb' : b' ≤ b) (hU₁ : ∀ y, f y ∈ Icc a a' → ∀ p hp, y ∉ D.smallBall p hp)
    (hU₂ : ∀ y, f y ∈ Icc b' b → ∀ p hp, y ∉ D.smallBall p hp) :
    ConnectedSpace (f ⁻¹' Icc a' b') :=
  isConnected_iff_connectedSpace.1
    (D.isConnected_substrip hf (isConnected_iff_connectedSpace.2 hconn) ha' hab' hb' hU₁ hU₂)

variable {D}

omit [T2Space M] [I.Boundaryless] in
theorem abs_f_sub_lt_of_mem_smallBall {p : M} (hp : p ∈ crit) {x : M}
    (hx : x ∈ D.smallBall p hp) :
    |f x - f p| < (D.chart p hp).r₀ ^ 2 / 2 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : morseNorm n y < (D.chart p hp).r₀ := hy
  have hR : morseNorm n y ≤ (D.chart p hp).R := hy'.le.trans (D.r₀_lt_R p hp).le
  rw [(D.chart p hp).hnorm y hR, morseNormalForm_split]
  have hsq := morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk y
  have h0 : 0 ≤ morseNorm n y := ModelField.morseNorm_nonneg y
  have hlt : morseNorm n y ^ 2 < (D.chart p hp).r₀ ^ 2 := by
    have := (D.chart p hp).hr₀
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (‖negPart (D.chart p hp).hk y‖),
    sq_nonneg (‖posPart (D.chart p hp).hk y‖)]

end GradientLikeStrip

omit [IsManifold I ∞ M] in
theorem exists_critical_gap (I : ModelWithCorners ℝ (Fin n → ℝ) H) {a' b' : ℝ} {crit : Finset M}
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hcol : ∀ x, f x ∈ Icc a b → (f x ≤ a' ∨ b' ≤ f x) → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) :
    ∃ g > 0, ∀ p ∈ crit, g ≤ f p - a' ∧ g ≤ b' - f p := by
  classical
  have hpos : ∀ p ∈ crit, 0 < min (f p - a') (b' - f p) := by
    intro p hp
    obtain ⟨hpo, hpc⟩ := (hcrit p).1 hp
    have h := hcol p (Ioo_subset_Icc_self hpo)
    refine lt_min (sub_pos.2 (lt_of_not_ge fun h' => h (Or.inl h') hpc))
      (sub_pos.2 (lt_of_not_ge fun h' => h (Or.inr h') hpc))
  rcases crit.eq_empty_or_nonempty with hne | hne
  · exact ⟨1, one_pos, fun p hp => by simp [hne] at hp⟩
  · refine ⟨crit.inf' hne fun p => min (f p - a') (b' - f p), (Finset.lt_inf'_iff hne).2 hpos,
      fun p hp => ?_⟩
    have := Finset.inf'_le (fun p => min (f p - a') (b' - f p)) hp
    exact ⟨this.trans (min_le_left _ _), this.trans (min_le_right _ _)⟩

theorem MorseStrip.connectedSpace_substrip [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]
    (hf : MorseStrip I f a b) (hconn : ConnectedSpace (f ⁻¹' Icc a b)) {a' b' : ℝ}
    (ha' : a ≤ a') (hab' : a' ≤ b') (hb' : b' ≤ b)
    (hcol : ∀ x, f x ∈ Icc a b → (f x ≤ a' ∨ b' ≤ f x) → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) :
    ConnectedSpace (f ⁻¹' Icc a' b') := by
  classical
  set crit : Finset M := (hf.finite_critical.subset fun x hx => ⟨Ioo_subset_Icc_self hx.1, hx.2⟩ :
    {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}.Finite).toFinset with hcritdef
  have hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := fun x => by
    rw [hcritdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  obtain ⟨g, hg, hgap⟩ := exists_critical_gap I hcrit hcol
  have hR₀ : 0 < min 1 g := lt_min one_pos hg
  obtain ⟨D, hR, -, -⟩ := exists_gradientLikeStrip hf le_rfl hf.lt le_rfl hf.regular crit hcrit hR₀
  have hsmall : ∀ p hp, ∀ y ∈ D.smallBall p hp, |f y - f p| < g := by
    intro p hp y hy
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hp hy
    have h2 : (D.chart p hp).r₀ < (D.chart p hp).R := D.r₀_lt_R p hp
    have h3 : (D.chart p hp).R ≤ min 1 g := hR p hp
    have h4 : 0 < (D.chart p hp).r₀ := (D.chart p hp).hr₀
    have h5 : (D.chart p hp).r₀ ^ 2 ≤ (D.chart p hp).r₀ := by
      have : (D.chart p hp).r₀ ≤ 1 := by linarith [min_le_left (1 : ℝ) g]
      nlinarith
    linarith [min_le_right (1 : ℝ) g]
  have hU₁ : ∀ y, f y ∈ Icc a a' → ∀ p hp, y ∉ D.smallBall p hp := by
    intro y hy p hp hmem
    have := hsmall p hp y hmem
    have := (hgap p hp).1
    rw [abs_lt] at *
    linarith [hy.2]
  have hU₂ : ∀ y, f y ∈ Icc b' b → ∀ p hp, y ∉ D.smallBall p hp := by
    intro y hy p hp hmem
    have := hsmall p hp y hmem
    have := (hgap p hp).2
    rw [abs_lt] at *
    linarith [hy.1]
  exact D.connectedSpace_substrip hf.smooth hconn ha' hab' hb' hU₁ hU₂

end

end DifferentialGeometry.Topology
