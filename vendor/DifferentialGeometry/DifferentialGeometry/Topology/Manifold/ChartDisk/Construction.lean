module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import DifferentialGeometry.Topology.Morse.Strip.Defs
public import DifferentialGeometry.Topology.ClosedBall.UnitDisk
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff
open Metric Set _root_.Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

def isChartDisk (e : Disk n → M) : Prop :=
  ∃ (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n)) (r : ℝ),
    φ ∈ atlas (EuclideanSpace ℝ (Fin n)) M ∧ 0 < r ∧ closedBall c r ⊆ φ.target ∧
      ∀ x : Disk n, e x = φ.symm (c + r • (x : EuclideanSpace ℝ (Fin n)))

theorem add_smul_mem_closedBall {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (x : Disk n) :
    c + r • (x : EuclideanSpace ℝ (Fin n)) ∈ closedBall c r := by
  rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  calc r * ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ r * 1 := by
        gcongr; exact mem_closedBall_zero_iff.1 x.2
    _ = r := mul_one r

theorem inv_smul_mem_closedBall_iff {v : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) :
    r⁻¹ • v ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ↔ ‖v‖ ≤ r := by
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr,
    inv_mul_le_iff₀ hr, mul_one]

theorem inv_smul_mem_ball_iff {v : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) :
    r⁻¹ • v ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 ↔ ‖v‖ < r := by
  rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr,
    inv_mul_lt_iff₀ hr, mul_one]

theorem inv_smul_mem_sphere_iff {v : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) :
    r⁻¹ • v ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↔ ‖v‖ = r := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
  constructor
  · intro h
    have := congrArg (r * ·) h
    simpa [mul_inv_cancel_left₀ hr.ne'] using this
  · intro h
    rw [h, inv_mul_cancel₀ hr.ne']

section NoChartedSpace

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem mem_image_chartDisk_iff {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ φ.target)
    {e : Disk n → M} (he : ∀ x : Disk n, e x = φ.symm (c + r • (x : EuclideanSpace ℝ (Fin n))))
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : T ⊆ closedBall 0 1) {z : M} :
    z ∈ e '' (Subtype.val ⁻¹' T) ↔ z ∈ φ.source ∧ r⁻¹ • (φ z - c) ∈ T := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hmem : c + r • (x : EuclideanSpace ℝ (Fin n)) ∈ φ.target :=
      hsub (add_smul_mem_closedBall hr x)
    rw [he x]
    refine ⟨φ.map_target hmem, ?_⟩
    rw [φ.right_inv hmem, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    exact hx
  · rintro ⟨hz, hT'⟩
    refine ⟨⟨r⁻¹ • (φ z - c), hT hT'⟩, hT', ?_⟩
    rw [he]
    simp only
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel, φ.left_inv hz]

theorem mem_range_chartDisk_iff {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ φ.target)
    {e : Disk n → M} (he : ∀ x : Disk n, e x = φ.symm (c + r • (x : EuclideanSpace ℝ (Fin n))))
    {z : M} : z ∈ range e ↔ z ∈ φ.source ∧ ‖φ z - c‖ ≤ r := by
  rw [← image_univ, ← Subtype.coe_preimage_self (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
    mem_image_chartDisk_iff hr hsub he subset_rfl, inv_smul_mem_closedBall_iff hr]

theorem mem_image_diskInterior_iff {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ φ.target)
    {e : Disk n → M} (he : ∀ x : Disk n, e x = φ.symm (c + r • (x : EuclideanSpace ℝ (Fin n))))
    {z : M} : z ∈ e '' diskInterior n ↔ z ∈ φ.source ∧ ‖φ z - c‖ < r := by
  rw [diskInterior, mem_image_chartDisk_iff hr hsub he ball_subset_closedBall,
    inv_smul_mem_ball_iff hr]

theorem mem_image_diskSphere_iff {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ φ.target)
    {e : Disk n → M} (he : ∀ x : Disk n, e x = φ.symm (c + r • (x : EuclideanSpace ℝ (Fin n))))
    {z : M} : z ∈ e '' diskSphere n ↔ z ∈ φ.source ∧ ‖φ z - c‖ = r := by
  rw [diskSphere, mem_image_chartDisk_iff hr hsub he sphere_subset_closedBall,
    inv_smul_mem_sphere_iff hr]

end NoChartedSpace

theorem isChartDisk.continuous {e : Disk n → M} (he : isChartDisk e) : Continuous e := by
  obtain ⟨φ, c, r, -, hr, hsub, he⟩ := he
  have hfun : e = fun x : Disk n => φ.symm (c + r • (x : EuclideanSpace ℝ (Fin n))) := funext he
  rw [hfun]
  exact φ.continuousOn_symm.comp_continuous
    (continuous_const.add (continuous_subtype_val.const_smul r))
    fun x => hsub (add_smul_mem_closedBall hr x)

theorem isChartDisk.injective {e : Disk n → M} (he : isChartDisk e) : Function.Injective e := by
  obtain ⟨φ, c, r, -, hr, hsub, he⟩ := he
  intro x y hxy
  rw [he x, he y] at hxy
  have h := congrArg φ hxy
  rw [φ.right_inv (hsub (add_smul_mem_closedBall hr x)),
    φ.right_inv (hsub (add_smul_mem_closedBall hr y))] at h
  exact Subtype.ext (smul_right_injective _ hr.ne' (add_left_cancel h))

theorem isChartDisk.isClosedEmbedding [T2Space M] {e : Disk n → M} (he : isChartDisk e) :
    IsClosedEmbedding e :=
  he.continuous.isClosedEmbedding he.injective

theorem isChartDisk.isOpen_image_diskInterior {e : Disk n → M} (he : isChartDisk e) :
    IsOpen (e '' diskInterior n) := by
  obtain ⟨φ, c, r, -, hr, hsub, he⟩ := he
  have hball : ball c r ⊆ φ.target := ball_subset_closedBall.trans hsub
  have : e '' diskInterior n = φ.symm '' ball c r := by
    ext z
    rw [mem_image_diskInterior_iff hr hsub he, φ.symm_image_eq_source_inter_preimage hball,
      mem_inter_iff, mem_preimage, mem_ball_iff_norm]
  rw [this]
  exact φ.isOpen_image_symm_of_subset_target isOpen_ball hball

theorem isChartDisk.nonempty_homeomorph_image_diskSphere [T2Space M] {e : Disk n → M}
    (he : isChartDisk e) :
    Nonempty (e '' diskSphere n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ⟨(he.isClosedEmbedding.isEmbedding.homeomorphImage (diskSphere n)).symm.trans
    (diskSphereHomeomorph n)⟩

theorem smoothTransition_hasDerivAt (x : ℝ) :
    HasDerivAt Real.smoothTransition
      ((expNegInvGlue x * expNegInvGlue (1 - x) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2)) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x := by
  have hE : ∀ y : ℝ, HasDerivAt expNegInvGlue (expNegInvGlue y * y⁻¹ ^ 2) y := by
    intro y
    have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (p := (1 : Polynomial ℝ)) y
    simpa [pow_two, Polynomial.derivative_one, mul_comm, mul_left_comm, mul_assoc] using h
  have h2 : HasDerivAt (fun y : ℝ => expNegInvGlue (1 - y))
      (-(expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2)) x := by
    have h3 := hE (1 - x)
    have hneg : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := (hasDerivAt_id x).const_sub 1
    have := h3.comp x hneg
    simpa [Function.comp_def] using this
  have hden : HasDerivAt (fun y : ℝ => expNegInvGlue y + expNegInvGlue (1 - y))
      (expNegInvGlue x * x⁻¹ ^ 2 + -(expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2)) x :=
    (hE x).add h2
  have hden_ne : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  have hτ := (hE x).div hden hden_ne
  have hτ' : HasDerivAt Real.smoothTransition
      (((expNegInvGlue x * x⁻¹ ^ 2) * (expNegInvGlue x + expNegInvGlue (1 - x)) -
        expNegInvGlue x * (expNegInvGlue x * x⁻¹ ^ 2 + -(expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2))) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x :=
    hτ.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)
  convert hτ' using 1
  ring

theorem smoothTransition_deriv_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < deriv Real.smoothTransition x := by
  rw [(smoothTransition_hasDerivAt x).deriv]
  have hE1 : 0 < expNegInvGlue x := expNegInvGlue.pos_of_pos hx0
  have hE2 : 0 < expNegInvGlue (1 - x) := expNegInvGlue.pos_of_pos (by linarith)
  have hx2 : 0 < x⁻¹ ^ 2 := by positivity
  have hx3 : 0 < (1 - x)⁻¹ ^ 2 := by
    have : 0 < 1 - x := by linarith
    positivity
  positivity

theorem smoothTransition_strictMonoOn : StrictMonoOn Real.smoothTransition (Icc 0 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    Real.smoothTransition.continuous.continuousOn fun x hx => ?_
  rw [interior_Icc] at hx
  exact smoothTransition_deriv_pos hx.1 hx.2

theorem smoothTransition_half : Real.smoothTransition (1 / 2) = 1 / 2 := by
  unfold Real.smoothTransition
  have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [this]
  have h := expNegInvGlue.pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  field_simp
  ring

noncomputable def diskProfile (R t : ℝ) : ℝ := Real.smoothTransition ((3 / 2 * R - t) / R)

theorem diskProfile_contDiff (R : ℝ) : ContDiff ℝ ∞ (diskProfile R) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.sub contDiff_id).div_const R)

theorem diskProfile_nonneg (R t : ℝ) : 0 ≤ diskProfile R t := Real.smoothTransition.nonneg _

theorem diskProfile_le_one (R t : ℝ) : diskProfile R t ≤ 1 := Real.smoothTransition.le_one _

theorem diskProfile_eq_one {R t : ℝ} (hR : 0 < R) (ht : t ≤ R / 2) : diskProfile R t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hR]
  linarith

theorem diskProfile_eq_zero {R t : ℝ} (hR : 0 < R) (ht : 3 / 2 * R ≤ t) : diskProfile R t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hR.le

theorem diskProfile_lt_half_iff {R t : ℝ} (hR : 0 < R) : diskProfile R t < 1 / 2 ↔ R < t := by
  by_cases h1 : t ≤ R / 2
  · rw [diskProfile_eq_one hR h1]
    constructor
    · intro h; norm_num at h
    · intro h; linarith
  by_cases h2 : 3 / 2 * R ≤ t
  · rw [diskProfile_eq_zero hR h2]
    constructor
    · intro _; linarith
    · intro _; norm_num
  rw [not_le] at h1 h2
  have hu0 : 0 ≤ (3 / 2 * R - t) / R := div_nonneg (by linarith) hR.le
  have hu1 : (3 / 2 * R - t) / R ≤ 1 := by rw [div_le_iff₀ hR]; linarith
  have key : diskProfile R t < 1 / 2 ↔ (3 / 2 * R - t) / R < 1 / 2 := by
    conv_lhs => rw [← smoothTransition_half]
    exact smoothTransition_strictMonoOn.lt_iff_lt ⟨hu0, hu1⟩ (by norm_num)
  rw [key, div_lt_iff₀ hR]
  constructor <;> intro h <;> linarith

theorem half_lt_diskProfile_iff {R t : ℝ} (hR : 0 < R) : 1 / 2 < diskProfile R t ↔ t < R := by
  by_cases h1 : t ≤ R / 2
  · rw [diskProfile_eq_one hR h1]
    constructor
    · intro _; linarith
    · intro _; norm_num
  by_cases h2 : 3 / 2 * R ≤ t
  · rw [diskProfile_eq_zero hR h2]
    constructor
    · intro h; norm_num at h
    · intro h; linarith
  rw [not_le] at h1 h2
  have hu0 : 0 ≤ (3 / 2 * R - t) / R := div_nonneg (by linarith) hR.le
  have hu1 : (3 / 2 * R - t) / R ≤ 1 := by rw [div_le_iff₀ hR]; linarith
  have key : 1 / 2 < diskProfile R t ↔ 1 / 2 < (3 / 2 * R - t) / R := by
    conv_lhs => rw [← smoothTransition_half]
    exact smoothTransition_strictMonoOn.lt_iff_lt (by norm_num) ⟨hu0, hu1⟩
  rw [key, lt_div_iff₀ hR]
  constructor <;> intro h <;> linarith

theorem diskProfile_eq_half_iff {R t : ℝ} (hR : 0 < R) : diskProfile R t = 1 / 2 ↔ t = R := by
  constructor
  · intro h
    have h1 : ¬ R < t := by rw [← diskProfile_lt_half_iff hR, h]; exact lt_irrefl _
    have h2 : ¬ t < R := by rw [← half_lt_diskProfile_iff hR, h]; exact lt_irrefl _
    exact le_antisymm (not_lt.1 h1) (not_lt.1 h2)
  · intro h
    have h1 : ¬ diskProfile R t < 1 / 2 := by rw [diskProfile_lt_half_iff hR, h]; exact lt_irrefl _
    have h2 : ¬ 1 / 2 < diskProfile R t := by
      rw [half_lt_diskProfile_iff hR, h]; exact lt_irrefl _
    exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)

theorem half_le_diskProfile_iff {R t : ℝ} (hR : 0 < R) : 1 / 2 ≤ diskProfile R t ↔ t ≤ R := by
  rw [← not_lt, diskProfile_lt_half_iff hR, not_lt]

theorem diskProfile_le_half_iff {R t : ℝ} (hR : 0 < R) : diskProfile R t ≤ 1 / 2 ↔ R ≤ t := by
  rw [← not_lt, half_lt_diskProfile_iff hR, not_lt]

theorem diskProfile_hasDerivAt_neg {R : ℝ} (hR : 0 < R) :
    ∃ d : ℝ, d < 0 ∧ HasDerivAt (diskProfile R) d R := by
  have hlin : HasDerivAt (fun t : ℝ => (3 / 2 * R - t) / R) ((-1) / R) R :=
    ((hasDerivAt_id R).const_sub (3 / 2 * R)).div_const R
  have hpt : (3 / 2 * R - R) / R = 1 / 2 := by field_simp; ring
  have hD := smoothTransition_hasDerivAt (1 / 2 : ℝ)
  have hDpos : 0 < deriv Real.smoothTransition (1 / 2) :=
    smoothTransition_deriv_pos (by norm_num) (by norm_num)
  rw [hD.deriv] at hDpos
  have hD' : HasDerivAt Real.smoothTransition
      ((expNegInvGlue (1 / 2) * expNegInvGlue (1 - 1 / 2) *
        ((1 / 2 : ℝ)⁻¹ ^ 2 + (1 - 1 / 2)⁻¹ ^ 2)) /
        (expNegInvGlue (1 / 2) + expNegInvGlue (1 - 1 / 2)) ^ 2)
      ((fun t : ℝ => (3 / 2 * R - t) / R) R) := by
    simp only [hpt]
    exact hD
  refine ⟨_, ?_, HasDerivAt.comp (h := fun t : ℝ => (3 / 2 * R - t) / R) R hD' hlin⟩
  have : (-1 : ℝ) / R < 0 := by
    rw [div_neg_iff]; right; exact ⟨by norm_num, hR⟩
  exact mul_neg_of_pos_of_neg hDpos this

noncomputable def radialBump (c : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  diskProfile R ‖y - c‖

theorem radialBump_nonneg (c : EuclideanSpace ℝ (Fin n)) (R : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    0 ≤ radialBump c R y := diskProfile_nonneg _ _

theorem radialBump_eq_zero {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    {y : EuclideanSpace ℝ (Fin n)} (hy : 3 / 2 * R ≤ ‖y - c‖) : radialBump c R y = 0 :=
  diskProfile_eq_zero hR hy

theorem radialBump_contDiff (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (radialBump c R) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = c
  · have hev : radialBump c R =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
      have hmem : ball c (R / 2) ∈ 𝓝 y := by
        rw [hy]; exact ball_mem_nhds c (by linarith)
      filter_upwards [hmem] with z hz
      exact diskProfile_eq_one hR (mem_ball_iff_norm.1 hz).le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hne : y - c ≠ 0 := sub_ne_zero.2 hy
    exact (diskProfile_contDiff R).contDiffAt.comp y
      ((contDiffAt_norm ℝ hne).comp y (contDiffAt_id.sub contDiffAt_const))

noncomputable def twoBump (c₀ c₁ : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  radialBump c₁ R y - radialBump c₀ R y

theorem twoBump_contDiff (c₀ c₁ : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (twoBump c₀ c₁ R) :=
  (radialBump_contDiff c₁ hR).sub (radialBump_contDiff c₀ hR)

theorem twoBump_swap (c₀ c₁ : EuclideanSpace ℝ (Fin n)) (R : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    twoBump c₁ c₀ R y = -twoBump c₀ c₁ R y := by
  simp only [twoBump]; ring

theorem twoBump_cases {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hsep : 3 * R ≤ ‖c₀ - c₁‖) (y : EuclideanSpace ℝ (Fin n)) :
    (‖y - c₀‖ ≤ 3 / 2 * R ∧ twoBump c₀ c₁ R y = -diskProfile R ‖y - c₀‖) ∨
      (3 / 2 * R < ‖y - c₀‖ ∧ 0 ≤ twoBump c₀ c₁ R y) := by
  by_cases h : ‖y - c₀‖ ≤ 3 / 2 * R
  · left
    refine ⟨h, ?_⟩
    have htri := norm_sub_le_norm_sub_add_norm_sub c₀ y c₁
    rw [norm_sub_rev c₀ y] at htri
    have h1 : radialBump c₁ R y = 0 := radialBump_eq_zero hR (by linarith)
    rw [twoBump, h1, zero_sub, radialBump]
  · right
    rw [not_le] at h
    refine ⟨h, ?_⟩
    have h0 : radialBump c₀ R y = 0 := radialBump_eq_zero hR h.le
    simp only [twoBump, h0, sub_zero]
    exact radialBump_nonneg _ _ _

theorem twoBump_le_neg_half_iff {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hsep : 3 * R ≤ ‖c₀ - c₁‖) (y : EuclideanSpace ℝ (Fin n)) :
    twoBump c₀ c₁ R y ≤ -1/2 ↔ ‖y - c₀‖ ≤ R := by
  rcases twoBump_cases hR hsep y with ⟨_, h⟩ | ⟨h, h'⟩
  · rw [h, ← half_le_diskProfile_iff hR]
    constructor <;> intro h <;> linarith
  · constructor
    · intro h''; linarith
    · intro h''; linarith

theorem twoBump_lt_neg_half_iff {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hsep : 3 * R ≤ ‖c₀ - c₁‖) (y : EuclideanSpace ℝ (Fin n)) :
    twoBump c₀ c₁ R y < -1/2 ↔ ‖y - c₀‖ < R := by
  rcases twoBump_cases hR hsep y with ⟨_, h⟩ | ⟨h, h'⟩
  · rw [h, ← half_lt_diskProfile_iff hR]
    constructor <;> intro h <;> linarith
  · constructor
    · intro h''; linarith
    · intro h''; linarith

theorem twoBump_eq_neg_half_iff {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hsep : 3 * R ≤ ‖c₀ - c₁‖) (y : EuclideanSpace ℝ (Fin n)) :
    twoBump c₀ c₁ R y = -1/2 ↔ ‖y - c₀‖ = R := by
  rcases twoBump_cases hR hsep y with ⟨_, h⟩ | ⟨h, h'⟩
  · rw [h, ← diskProfile_eq_half_iff hR]
    constructor <;> intro h <;> linarith
  · constructor
    · intro h''; linarith
    · intro h''; linarith

theorem half_le_twoBump_iff {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hsep : 3 * R ≤ ‖c₀ - c₁‖) (y : EuclideanSpace ℝ (Fin n)) :
    1/2 ≤ twoBump c₀ c₁ R y ↔ ‖y - c₁‖ ≤ R := by
  rw [← twoBump_le_neg_half_iff hR (by rwa [norm_sub_rev]) y, twoBump_swap]
  constructor <;> intro h <;> linarith

theorem half_lt_twoBump_iff {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hsep : 3 * R ≤ ‖c₀ - c₁‖) (y : EuclideanSpace ℝ (Fin n)) :
    1/2 < twoBump c₀ c₁ R y ↔ ‖y - c₁‖ < R := by
  rw [← twoBump_lt_neg_half_iff hR (by rwa [norm_sub_rev]) y, twoBump_swap]
  constructor <;> intro h <;> linarith

theorem twoBump_eq_half_iff {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hsep : 3 * R ≤ ‖c₀ - c₁‖) (y : EuclideanSpace ℝ (Fin n)) :
    twoBump c₀ c₁ R y = 1/2 ↔ ‖y - c₁‖ = R := by
  rw [← twoBump_eq_neg_half_iff hR (by rwa [norm_sub_rev]) y, twoBump_swap]
  constructor <;> intro h <;> linarith

theorem twoBump_eq_zero {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∉ closedBall c₀ (3 / 2 * R) ∪ closedBall c₁ (3 / 2 * R)) :
    twoBump c₀ c₁ R y = 0 := by
  simp only [mem_union, mem_closedBall_iff_norm, not_or, not_le] at hy
  simp only [twoBump, radialBump_eq_zero hR hy.1.le, radialBump_eq_zero hR hy.2.le, sub_zero]

theorem twoBump_not_hasFDerivAt_zero {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hsep : 3 * R ≤ ‖c₀ - c₁‖) {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y - c₀‖ = R) :
    ¬ HasFDerivAt (twoBump c₀ c₁ R) (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y := by
  intro hg
  set u : EuclideanSpace ℝ (Fin n) := R⁻¹ • (y - c₀) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, hy, inv_mul_cancel₀ hR.ne']
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := fun s => c₀ + (R + s) • u with hγ_def
  have hγ0 : γ 0 = y := by
    simp only [hγ_def, hu_def, add_zero, smul_smul, mul_inv_cancel₀ hR.ne', one_smul,
      add_sub_cancel]
  have hγ : HasDerivAt γ u 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_add R).smul_const u).const_add c₀
    simpa [hγ_def] using this
  have hg' : HasFDerivAt (twoBump c₀ c₁ R) (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (γ 0) :=
    hγ0.symm ▸ hg
  have hcomp : HasDerivAt (twoBump c₀ c₁ R ∘ γ) 0 0 := by
    have := hg'.comp_hasDerivAt 0 hγ
    simpa using this
  have hev : (fun s : ℝ => -diskProfile R (R + s)) =ᶠ[𝓝 0] twoBump c₀ c₁ R ∘ γ := by
    filter_upwards [Ioo_mem_nhds (show -R < (0 : ℝ) by linarith) (show (0 : ℝ) < R / 2 by linarith)]
      with s hs
    have hn0 : ‖γ s - c₀‖ = R + s := by
      simp only [hγ_def, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs]
      exact abs_of_pos (by linarith [hs.1])
    have htri := norm_sub_le_norm_sub_add_norm_sub c₀ (γ s) c₁
    rw [norm_sub_rev c₀ (γ s), hn0] at htri
    have h1 : radialBump c₁ R (γ s) = 0 := radialBump_eq_zero hR (by linarith [hs.2])
    change -diskProfile R (R + s) = twoBump c₀ c₁ R (γ s)
    rw [twoBump, h1, zero_sub, radialBump, hn0]
  have hcomp' : HasDerivAt (fun s : ℝ => -diskProfile R (R + s)) 0 0 :=
    hcomp.congr_of_eventuallyEq hev
  obtain ⟨d, hd, hDd⟩ := diskProfile_hasDerivAt_neg hR
  have hDd' : HasDerivAt (diskProfile R) d ((fun s : ℝ => R + s) 0) := by simpa using hDd
  have hother : HasDerivAt (fun s : ℝ => -diskProfile R (R + s)) (-(d * 1)) 0 := by
    have := (hDd'.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add R)).neg
    exact this
  have := hcomp'.unique hother
  linarith

section NoChartedSpace

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

noncomputable def chartTwoBump (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (c₀ c₁ : EuclideanSpace ℝ (Fin n)) (R : ℝ) : M → ℝ :=
  φ.source.indicator (twoBump c₀ c₁ R ∘ φ)

theorem chartTwoBump_apply_of_mem {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} {x : M} (hx : x ∈ φ.source) :
    chartTwoBump φ c₀ c₁ R x = twoBump c₀ c₁ R (φ x) :=
  Set.indicator_of_mem hx _

theorem chartTwoBump_apply_of_notMem {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} {x : M} (hx : x ∉ φ.source) :
    chartTwoBump φ c₀ c₁ R x = 0 :=
  Set.indicator_of_notMem hx _

theorem chartTwoBump_symm_apply {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ φ.target) :
    chartTwoBump φ c₀ c₁ R (φ.symm y) = twoBump c₀ c₁ R y := by
  rw [chartTwoBump_apply_of_mem (φ.map_target hy), φ.right_inv hy]

theorem chartTwoBump_pred_iff {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} {P : ℝ → Prop} (hP : ¬ P 0) (x : M) :
    P (chartTwoBump φ c₀ c₁ R x) ↔ x ∈ φ.source ∧ P (twoBump c₀ c₁ R (φ x)) := by
  by_cases hx : x ∈ φ.source
  · rw [chartTwoBump_apply_of_mem hx]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  · rw [chartTwoBump_apply_of_notMem hx]
    exact ⟨fun h => absurd h hP, fun h => absurd h.1 hx⟩

theorem chartTwoBump_support_subset {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R) :
    Function.support (chartTwoBump φ c₀ c₁ R) ⊆
      φ.symm '' (closedBall c₀ (3 / 2 * R) ∪ closedBall c₁ (3 / 2 * R)) := by
  intro x hx
  rw [Function.mem_support] at hx
  by_cases hxs : x ∈ φ.source
  · rw [chartTwoBump_apply_of_mem hxs] at hx
    by_contra hK
    apply hx
    apply twoBump_eq_zero hR
    intro hmem
    exact hK ⟨φ x, hmem, φ.left_inv hxs⟩
  · exact absurd (chartTwoBump_apply_of_notMem hxs) hx

end NoChartedSpace

theorem chartTwoBump_contMDiff [T2Space M] [IsManifold (𝓡 n) ∞ M]
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hφ : φ ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    {c₀ c₁ : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hsub : closedBall c₀ (3 / 2 * R) ∪ closedBall c₁ (3 / 2 * R) ⊆ φ.target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (chartTwoBump φ c₀ c₁ R) := by
  set K := φ.symm '' (closedBall c₀ (3 / 2 * R) ∪ closedBall c₁ (3 / 2 * R)) with hK_def
  have hKc : IsCompact K :=
    ((isCompact_closedBall _ _).union (isCompact_closedBall _ _)).image_of_continuousOn
      (φ.continuousOn_symm.mono hsub)
  have hKs : K ⊆ φ.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact φ.map_target (hsub hy)
  have hts : tsupport (chartTwoBump φ c₀ c₁ R) ⊆ φ.source :=
    (closure_minimal (chartTwoBump_support_subset hR) hKc.isClosed).trans hKs
  refine contMDiff_of_tsupport fun x hx => ?_
  have hxs : x ∈ φ.source := hts hx
  have hev : chartTwoBump φ c₀ c₁ R =ᶠ[𝓝 x] twoBump c₀ c₁ R ∘ φ := by
    filter_upwards [φ.open_source.mem_nhds hxs] with z hz
    exact chartTwoBump_apply_of_mem hz
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
  exact ((twoBump_contDiff c₀ c₁ hR).contMDiff.contMDiffAt).comp x
    ((contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hφ)).contMDiffAt
      (φ.open_source.mem_nhds hxs))

theorem not_isCriticalPointAt_of_chart [IsManifold (𝓡 n) ∞ M]
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hφ : φ ∈ atlas (EuclideanSpace ℝ (Fin n)) M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hfg : ∀ y ∈ φ.target, f (φ.symm y) = g y) {x : M} (hx : x ∈ φ.source)
    (hg : ¬ HasFDerivAt g (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (φ x)) :
    ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) f x := by
  intro h
  unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt at h
  have hf' : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) f x (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x) :=
    (hf.mdifferentiableAt (by simp)).hasMFDerivAt
  rw [h] at hf'
  have hx' : φ.symm (φ x) = x := φ.left_inv hx
  have hf'' : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) f (φ.symm (φ x)) 0 := by
    rw [hx']; exact hf'
  have hsymm : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) φ.symm (φ x)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) φ.symm (φ x)) :=
    (mdifferentiableAt_atlas_symm hφ (φ.map_source hx)).hasMFDerivAt
  have hcomp := hf''.comp (φ x) hsymm
  rw [ContinuousLinearMap.zero_comp] at hcomp
  have hF : HasFDerivAt (f ∘ φ.symm) (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (φ x) :=
    hasMFDerivAt_iff_hasFDerivAt.1 hcomp
  apply hg
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [φ.open_target.mem_nhds (φ.map_source hx)] with y hy
  exact (hfg y hy).symm

theorem exists_chartDisks_and_strip [T2Space M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]
    (hn : 1 ≤ n) :
    ∃ (e₀ e₁ : Disk n → M) (f : M → ℝ),
      isChartDisk e₀ ∧ isChartDisk e₁ ∧ Disjoint (range e₀) (range e₁) ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      f ⁻¹' Iic (-1/2) = range e₀ ∧ f ⁻¹' Ici (1/2) = range e₁ ∧
      f ⁻¹' Iio (-1/2) = e₀ '' diskInterior n ∧ f ⁻¹' Ioi (1/2) = e₁ '' diskInterior n ∧
      f ⁻¹' {-1/2} = e₀ '' diskSphere n ∧ f ⁻¹' {1/2} = e₁ '' diskSphere n ∧
      (∀ x, f x = -1/2 ∨ f x = 1/2 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) f x) := by
  obtain ⟨p⟩ := ‹Nonempty M›
  set φ := chartAt (EuclideanSpace ℝ (Fin n)) p with hφ_def
  have hφ : φ ∈ atlas (EuclideanSpace ℝ (Fin n)) M := chart_mem_atlas _ p
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.mem_nhds_iff.1 (φ.open_target.mem_nhds (mem_chart_target (EuclideanSpace ℝ (Fin n)) p))
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 :=
    ⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ), by simp⟩
  set R : ℝ := ρ / 8 with hR_def
  have hR : 0 < R := by positivity
  set c₀ : EuclideanSpace ℝ (Fin n) := φ p + (4 * R) • v with hc₀_def
  set c₁ : EuclideanSpace ℝ (Fin n) := φ p - (4 * R) • v with hc₁_def
  have hsep : ‖c₀ - c₁‖ = 8 * R := by
    have : c₀ - c₁ = (8 * R) • v := by
      rw [hc₀_def, hc₁_def]
      rw [show (8 * R) • v = (4 * R) • v + (4 * R) • v by rw [← add_smul]; ring_nf]
      abel
    rw [this, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsep' : 3 * R ≤ ‖c₀ - c₁‖ := by rw [hsep]; linarith
  have hc₀p : ‖c₀ - φ p‖ = 4 * R := by
    rw [hc₀_def, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hc₁p : ‖c₁ - φ p‖ = 4 * R := by
    rw [hc₁_def, sub_sub_cancel_left, norm_neg, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hsub : closedBall c₀ (3 / 2 * R) ∪ closedBall c₁ (3 / 2 * R) ⊆ φ.target := by
    intro y hy
    apply hball
    rw [mem_ball_iff_norm]
    rcases hy with hy | hy
    · rw [mem_closedBall_iff_norm] at hy
      have := norm_sub_le_norm_sub_add_norm_sub y c₀ (φ p)
      linarith
    · rw [mem_closedBall_iff_norm] at hy
      have := norm_sub_le_norm_sub_add_norm_sub y c₁ (φ p)
      linarith
  have hsub₀ : closedBall c₀ R ⊆ φ.target :=
    (closedBall_subset_closedBall (by linarith)).trans (subset_union_left.trans hsub)
  have hsub₁ : closedBall c₁ R ⊆ φ.target :=
    (closedBall_subset_closedBall (by linarith)).trans (subset_union_right.trans hsub)
  set e₀ : Disk n → M := fun x => φ.symm (c₀ + R • (x : EuclideanSpace ℝ (Fin n))) with he₀_def
  set e₁ : Disk n → M := fun x => φ.symm (c₁ + R • (x : EuclideanSpace ℝ (Fin n))) with he₁_def
  have he₀ : ∀ x : Disk n, e₀ x = φ.symm (c₀ + R • (x : EuclideanSpace ℝ (Fin n))) := fun _ => rfl
  have he₁ : ∀ x : Disk n, e₁ x = φ.symm (c₁ + R • (x : EuclideanSpace ℝ (Fin n))) := fun _ => rfl
  set f := chartTwoBump φ c₀ c₁ R with hf_def
  have hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := chartTwoBump_contMDiff hφ hR hsub
  refine ⟨e₀, e₁, f, ⟨φ, c₀, R, hφ, hR, hsub₀, he₀⟩, ⟨φ, c₁, R, hφ, hR, hsub₁, he₁⟩, ?_,
    hsmooth, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx₀ hx₁
    rw [mem_range_chartDisk_iff hR hsub₀ he₀] at hx₀
    rw [mem_range_chartDisk_iff hR hsub₁ he₁] at hx₁
    have := norm_sub_le_norm_sub_add_norm_sub c₀ (φ x) c₁
    rw [norm_sub_rev c₀ (φ x), hsep] at this
    linarith [hx₀.2, hx₁.2]
  · ext x
    rw [mem_preimage, mem_Iic, mem_range_chartDisk_iff hR hsub₀ he₀, hf_def,
      chartTwoBump_pred_iff (P := fun t => t ≤ -1/2) (by norm_num),
      twoBump_le_neg_half_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_Ici, mem_range_chartDisk_iff hR hsub₁ he₁, hf_def,
      chartTwoBump_pred_iff (P := fun t => 1/2 ≤ t) (by norm_num),
      half_le_twoBump_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_Iio, mem_image_diskInterior_iff hR hsub₀ he₀, hf_def,
      chartTwoBump_pred_iff (P := fun t => t < -1/2) (by norm_num),
      twoBump_lt_neg_half_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_Ioi, mem_image_diskInterior_iff hR hsub₁ he₁, hf_def,
      chartTwoBump_pred_iff (P := fun t => 1/2 < t) (by norm_num),
      half_lt_twoBump_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_singleton_iff, mem_image_diskSphere_iff hR hsub₀ he₀, hf_def,
      chartTwoBump_pred_iff (P := fun t => t = -1/2) (by norm_num),
      twoBump_eq_neg_half_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_singleton_iff, mem_image_diskSphere_iff hR hsub₁ he₁, hf_def,
      chartTwoBump_pred_iff (P := fun t => t = 1/2) (by norm_num),
      twoBump_eq_half_iff hR hsep']
  · intro x hx
    have hfg : ∀ y ∈ φ.target, f (φ.symm y) = twoBump c₀ c₁ R y := fun y hy =>
      chartTwoBump_symm_apply hy
    rcases hx with hx | hx
    · rw [hf_def, chartTwoBump_pred_iff (P := fun t => t = -1/2) (by norm_num),
        twoBump_eq_neg_half_iff hR hsep'] at hx
      exact not_isCriticalPointAt_of_chart hφ hsmooth hfg hx.1
        (twoBump_not_hasFDerivAt_zero hR hsep' hx.2)
    · rw [hf_def, chartTwoBump_pred_iff (P := fun t => t = 1/2) (by norm_num),
        twoBump_eq_half_iff hR hsep'] at hx
      refine not_isCriticalPointAt_of_chart hφ hsmooth hfg hx.1 ?_
      intro hg
      have hg' : HasFDerivAt (twoBump c₁ c₀ R) (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (φ x) := by
        have := hg.neg
        rw [neg_zero] at this
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        exact twoBump_swap c₀ c₁ R y
      exact twoBump_not_hasFDerivAt_zero hR (by rwa [norm_sub_rev]) hx.2 hg'

end DifferentialGeometry.Topology
