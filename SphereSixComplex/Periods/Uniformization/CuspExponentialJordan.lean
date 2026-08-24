module

public import SphereSixComplex.Periods.Uniformization.SourceChamberTopology
import all SphereSixComplex.Periods.Uniformization.SourceChamberTopology
public import TauCeti.Topology.JordanCurve.Path
import all TauCeti.Topology.JordanCurve.Path

@[expose] public section

open Complex Set Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

/-! A compactified polar-coordinate model for the cusp-exponential chambers. -/

def cuspPolar (width : ℝ) (h : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  (p.2 : ℂ) * cuspExponential width ((p.1 : ℂ) + (h p.1 : ℂ) * Complex.I)

theorem cuspPolar_continuous {width : ℝ} {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (cuspPolar width h) := by
  unfold cuspPolar
  apply Continuous.mul
  · fun_prop
  · apply (cuspExponential_continuous width).comp
    fun_prop

theorem cuspExponential_eq_cuspPolar (width : ℝ) (hwidth : width ≠ 0)
    (h : ℝ → ℝ) (x y : ℝ) :
    cuspExponential width ((x : ℂ) + (y : ℂ) * Complex.I) =
      cuspPolar width h (x, Real.exp (-2 * Real.pi * (y - h x) / width)) := by
  rw [cuspPolar, cuspExponential, cuspExponential]
  simp only [Prod.snd, Prod.fst, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  have hw : (width : ℂ) ≠ 0 := by exact_mod_cast hwidth
  field_simp [hw]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  have hcancel : (Real.pi : ℂ) * width * h x * (width : ℂ)⁻¹ * 2 =
      (Real.pi : ℂ) * h x * 2 := by
    field_simp [hw]
  have hycancel : (Real.pi : ℂ) * y * width * (width : ℂ)⁻¹ * 2 =
      (Real.pi : ℂ) * y * 2 := by
    field_simp [hw]
  rw [hcancel, hycancel]
  ring

theorem cuspPolar_eq_cuspExponential (width : ℝ) (hwidth : width ≠ 0)
    (h : ℝ → ℝ) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    cuspPolar width h (x, t) =
      cuspExponential width
        ((x : ℂ) + (h x - width * Real.log t / (2 * Real.pi) : ℂ) * Complex.I) := by
  rw [cuspPolar, cuspExponential, cuspExponential]
  rw [show (t : ℂ) = Complex.exp (Real.log t : ℂ) by
    calc
      (t : ℂ) = (Real.exp (Real.log t) : ℝ) := by rw [Real.exp_log ht]
      _ = Complex.exp (Real.log t : ℂ) := Complex.ofReal_exp _]
  rw [← Complex.exp_add]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [show (width : ℂ) ≠ 0 by exact_mod_cast hwidth, hpi]
  push_cast
  ring_nf
  simp [Complex.I_sq]

def openCuspRectangle (l r : ℝ) : Set (ℝ × ℝ) :=
  Ioo l r ×ˢ Ioo 0 1

def closedCuspRectangle (l r : ℝ) : Set (ℝ × ℝ) :=
  Icc l r ×ˢ Icc 0 1

theorem closure_openCuspRectangle {l r : ℝ} (hlr : l ≠ r) :
    closure (openCuspRectangle l r) = closedCuspRectangle l r := by
  simp only [openCuspRectangle, closedCuspRectangle, closure_prod_eq, closure_Ioo hlr,
    closure_Ioo zero_ne_one]

theorem closure_cuspPolar_image {width l r : ℝ} {h : ℝ → ℝ}
    (hlr : l ≠ r) (hh : Continuous h) :
    closure (cuspPolar width h '' openCuspRectangle l r) =
      cuspPolar width h '' closedCuspRectangle l r := by
  have hc : IsCompact (closure (openCuspRectangle l r)) := by
    rw [closure_openCuspRectangle hlr]
    exact isCompact_Icc.prod isCompact_Icc
  have hi := image_closure_of_isCompact (f := cuspPolar width h) hc
    (cuspPolar_continuous hh).continuousOn
  rw [closure_openCuspRectangle hlr] at hi
  exact hi.symm

def positiveClosedCuspStrip (l r : ℝ) : Set (ℝ × ℝ) :=
  {p | l ≤ p.1 ∧ p.1 ≤ r ∧ 0 < p.2}

def cuspRectangleBoundary (l r : ℝ) : Set (ℝ × ℝ) :=
  ({l} ×ˢ Icc 0 1) ∪ (Icc l r ×ˢ {1}) ∪ ({r} ×ˢ Icc 0 1)

theorem mem_cuspRectangleBoundary_iff {l r : ℝ} (hlr : l ≤ r) (p : ℝ × ℝ) :
    p ∈ cuspRectangleBoundary l r ↔
      p ∈ closedCuspRectangle l r ∧ (p.1 = l ∨ p.1 = r ∨ p.2 = 1) := by
  rcases p with ⟨x, t⟩
  simp only [cuspRectangleBoundary, closedCuspRectangle, mem_union, mem_prod, mem_singleton_iff,
    mem_Icc, Prod.fst, Prod.snd]
  aesop

theorem cuspPolar_injOn_positiveClosedCuspStrip {width l r : ℝ} (hwidth : width ≠ 0)
    (h : ℝ → ℝ)
    (hinj : InjOn (cuspExponential width) {z : ℂ | l ≤ z.re ∧ z.re ≤ r}) :
    InjOn (cuspPolar width h) (positiveClosedCuspStrip l r) := by
  rintro ⟨x, t⟩ ⟨hxl, hxr, ht⟩ ⟨x', t'⟩ ⟨hxl', hxr', ht'⟩ heq
  let y : ℝ := h x - width * Real.log t / (2 * Real.pi)
  let y' : ℝ := h x' - width * Real.log t' / (2 * Real.pi)
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  let z' : ℂ := (x' : ℂ) + (y' : ℂ) * Complex.I
  have hf : cuspPolar width h (x, t) = cuspExponential width z := by
    simpa [z, y] using cuspPolar_eq_cuspExponential width hwidth h x ht
  have hf' : cuspPolar width h (x', t') = cuspExponential width z' := by
    simpa [z', y'] using cuspPolar_eq_cuspExponential width hwidth h x' ht'
  have hzmem : z ∈ {w : ℂ | l ≤ w.re ∧ w.re ≤ r} := by
    simpa [z] using And.intro hxl hxr
  have hzmem' : z' ∈ {w : ℂ | l ≤ w.re ∧ w.re ≤ r} := by
    simpa [z'] using And.intro hxl' hxr'
  have hzz' : z = z' := hinj hzmem hzmem' (hf.symm.trans (heq.trans hf'))
  have hxx' : x = x' := by
    have := congrArg Complex.re hzz'
    simpa [z, z'] using this
  subst x'
  apply Prod.ext
  · rfl
  · apply Complex.ofReal_injective
    apply mul_right_cancel₀ (cuspExponential_ne_zero width ((x : ℂ) + (h x : ℂ) * I))
    simpa [cuspPolar] using heq

theorem frontier_cuspPolar_image {width l r : ℝ} {h : ℝ → ℝ}
    (hwidth : width ≠ 0) (hlr : l < r) (hh : Continuous h)
    (hopen : IsOpen (cuspPolar width h '' openCuspRectangle l r))
    (hinj : InjOn (cuspExponential width) {z : ℂ | l ≤ z.re ∧ z.re ≤ r}) :
    frontier (cuspPolar width h '' openCuspRectangle l r) =
      cuspPolar width h '' cuspRectangleBoundary l r := by
  rw [frontier, hopen.interior_eq, closure_cuspPolar_image hlr.ne hh]
  ext q
  constructor
  · rintro ⟨⟨⟨x, t⟩, hp, rfl⟩, hnot⟩
    change (x ∈ Icc l r) ∧ t ∈ Icc 0 1 at hp
    rcases hp with ⟨⟨hxl, hxr⟩, ht0, ht1⟩
    by_cases htz : t = 0
    · refine ⟨(l, 0), ?_, ?_⟩
      · apply (mem_cuspRectangleBoundary_iff hlr.le _).2
        exact ⟨⟨⟨le_rfl, hlr.le⟩, le_rfl, zero_le_one⟩, Or.inl rfl⟩
      · simp [cuspPolar, htz]
    by_cases hxl' : x = l
    · exact ⟨(x, t), (mem_cuspRectangleBoundary_iff hlr.le _).2
        ⟨⟨⟨hxl, hxr⟩, ht0, ht1⟩, Or.inl hxl'⟩, rfl⟩
    by_cases hxr' : x = r
    · exact ⟨(x, t), (mem_cuspRectangleBoundary_iff hlr.le _).2
        ⟨⟨⟨hxl, hxr⟩, ht0, ht1⟩, Or.inr (Or.inl hxr')⟩, rfl⟩
    by_cases ht1' : t = 1
    · exact ⟨(x, t), (mem_cuspRectangleBoundary_iff hlr.le _).2
        ⟨⟨⟨hxl, hxr⟩, ht0, ht1⟩, Or.inr (Or.inr ht1')⟩, rfl⟩
    exfalso
    apply hnot
    refine ⟨(x, t), ?_, rfl⟩
    exact ⟨⟨lt_of_le_of_ne hxl (Ne.symm hxl'), lt_of_le_of_ne hxr hxr'⟩,
      lt_of_le_of_ne ht0 (Ne.symm htz), lt_of_le_of_ne ht1 ht1'⟩
  · rintro ⟨⟨x, t⟩, hbdy, rfl⟩
    have hb := (mem_cuspRectangleBoundary_iff hlr.le (x, t)).1 hbdy
    rcases hb.1 with ⟨⟨hxl, hxr⟩, ht0, ht1⟩
    refine ⟨⟨(x, t), ⟨⟨hxl, hxr⟩, ht0, ht1⟩, rfl⟩, ?_⟩
    rintro ⟨⟨x', t'⟩, hp', heq⟩
    change (x' ∈ Ioo l r) ∧ t' ∈ Ioo 0 1 at hp'
    rcases hp' with ⟨⟨hxl', hxr'⟩, ht0', ht1'⟩
    by_cases htz : t = 0
    · have hzero : cuspPolar width h (x, t) = 0 := by simp [cuspPolar, htz]
      have hnzero : cuspPolar width h (x', t') ≠ 0 := by
        unfold cuspPolar
        exact mul_ne_zero (by exact_mod_cast ht0'.ne') (cuspExponential_ne_zero _ _)
      exact hnzero (heq.trans hzero)
    have hpair : (x', t') = (x, t) := by
      apply cuspPolar_injOn_positiveClosedCuspStrip hwidth h hinj
      · exact ⟨hxl'.le, hxr'.le, ht0'⟩
      · exact ⟨hxl, hxr, lt_of_le_of_ne ht0 (Ne.symm htz)⟩
      · exact heq
    have hbdy' : (x', t') ∈ cuspRectangleBoundary l r := by
      rw [hpair]
      exact hbdy
    rcases ((mem_cuspRectangleBoundary_iff hlr.le (x', t')).1 hbdy').2 with
      hxlEq | hxrEq | htEq
    · exact hxl'.ne' hxlEq
    · exact hxr'.ne hxrEq
    · exact ht1'.ne htEq

theorem Path.trans_injective_of_inter_range_eq_singleton {X : Type*} [TopologicalSpace X]
    {x y z : X} {alpha : Path x y} {beta : Path y z}
    (halpha : Function.Injective alpha) (hbeta : Function.Injective beta)
    (hmeet : range alpha ∩ range beta = {y}) : Function.Injective (alpha.trans beta) := by
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have h : (2 : ℝ) * s = 2 * t := congrArg Subtype.val (halpha hst)
    exact Subtype.ext (by linarith)
  · have hmem : alpha ⟨2 * s, unitInterval.mul_pos_mem_iff zero_lt_two |>.2 ⟨s.2.1, hs⟩⟩ ∈
        range alpha ∩ range beta := ⟨mem_range_self _, hst ▸ mem_range_self _⟩
    have hy : alpha ⟨2 * s, unitInterval.mul_pos_mem_iff zero_lt_two |>.2 ⟨s.2.1, hs⟩⟩ = y := by
      simpa [hmeet] using hmem
    have ha := halpha (hy.trans alpha.target.symm)
    have hb := hbeta ((hst.symm.trans hy).trans beta.source.symm)
    have ha' : (2 : ℝ) * s = 1 := congrArg Subtype.val ha
    have hb' : (2 : ℝ) * t - 1 = 0 := congrArg Subtype.val hb
    exact Subtype.ext (by linarith)
  · have hmem : alpha ⟨2 * t, unitInterval.mul_pos_mem_iff zero_lt_two |>.2 ⟨t.2.1, ht⟩⟩ ∈
        range alpha ∩ range beta := ⟨mem_range_self _, hst.symm ▸ mem_range_self _⟩
    have hy : alpha ⟨2 * t, unitInterval.mul_pos_mem_iff zero_lt_two |>.2 ⟨t.2.1, ht⟩⟩ = y := by
      simpa [hmeet] using hmem
    have ha := halpha (hy.trans alpha.target.symm)
    have hb := hbeta ((hst.trans hy).trans beta.source.symm)
    have ha' : (2 : ℝ) * t = 1 := congrArg Subtype.val ha
    have hb' : (2 : ℝ) * s - 1 = 0 := congrArg Subtype.val hb
    exact Subtype.ext (by linarith)
  · have h : (2 : ℝ) * s - 1 = 2 * t - 1 := congrArg Subtype.val (hbeta hst)
    exact Subtype.ext (by linarith)

def cuspRadialPath (width : ℝ) (h : ℝ → ℝ) (x : ℝ) :
    Path 0 (cuspPolar width h (x, 1)) where
  toFun t := cuspPolar width h (x, (t : ℝ))
  continuous_toFun := by
    change Continuous fun t : unitInterval =>
      ((t : ℝ) : ℂ) * cuspExponential width ((x : ℂ) + (h x : ℂ) * I)
    fun_prop
  source' := by simp [cuspPolar]
  target' := rfl

@[simp] theorem cuspRadialPath_apply (width : ℝ) (h : ℝ → ℝ) (x : ℝ)
    (t : unitInterval) :
    cuspRadialPath width h x t = cuspPolar width h (x, (t : ℝ)) := rfl

def cuspOuterPath (width : ℝ) (h : ℝ → ℝ) (l r : ℝ) (hh : Continuous h) :
    Path (cuspPolar width h (l, 1)) (cuspPolar width h (r, 1)) :=
  (Path.segment l r).map ((cuspPolar_continuous hh).comp (by fun_prop :
    Continuous fun x : ℝ => (x, (1 : ℝ))))

@[simp] theorem cuspOuterPath_apply (width : ℝ) (h : ℝ → ℝ) (l r : ℝ)
    (hh : Continuous h) (t : unitInterval) :
    cuspOuterPath width h l r hh t =
      cuspPolar width h (Path.segment l r t, 1) := rfl

theorem cuspRadialPath_injective (width : ℝ) (h : ℝ → ℝ) (x : ℝ) :
    Function.Injective (cuspRadialPath width h x) := by
  intro s t hst
  apply Subtype.ext
  apply Complex.ofReal_injective
  apply mul_right_cancel₀ (cuspExponential_ne_zero width ((x : ℂ) + (h x : ℂ) * I))
  change ((s : ℝ) : ℂ) * cuspExponential width ((x : ℂ) + (h x : ℂ) * I) =
    ((t : ℝ) : ℂ) * cuspExponential width ((x : ℂ) + (h x : ℂ) * I) at hst
  exact hst

theorem cuspOuterPath_injective {width l r : ℝ} (hwidth : width ≠ 0) (h : ℝ → ℝ)
    (hh : Continuous h) (hlr : l < r)
    (hinj : InjOn (cuspExponential width) {z : ℂ | l ≤ z.re ∧ z.re ≤ r}) :
    Function.Injective (cuspOuterPath width h l r hh) := by
  intro s t hst
  have hsx : Path.segment l r s ∈ Icc l r := by
    rw [← segment_eq_Icc hlr.le, ← Path.range_segment]
    exact mem_range_self s
  have htx : Path.segment l r t ∈ Icc l r := by
    rw [← segment_eq_Icc hlr.le, ← Path.range_segment]
    exact mem_range_self t
  have hp := cuspPolar_injOn_positiveClosedCuspStrip hwidth h hinj
    (show (Path.segment l r s, 1) ∈ positiveClosedCuspStrip l r from
      ⟨hsx.1, hsx.2, one_pos⟩)
    (show (Path.segment l r t, 1) ∈ positiveClosedCuspStrip l r from
      ⟨htx.1, htx.2, one_pos⟩) hst
  exact (Path.segment_injective_of_ne hlr.ne) (congrArg Prod.fst hp)

theorem range_cuspRadialPath_inter_range_cuspOuterPath_left {width l r : ℝ}
    (hwidth : width ≠ 0) (h : ℝ → ℝ) (hh : Continuous h) (hlr : l < r)
    (hinj : InjOn (cuspExponential width) {z : ℂ | l ≤ z.re ∧ z.re ≤ r}) :
    range (cuspRadialPath width h l) ∩ range (cuspOuterPath width h l r hh) =
      {cuspPolar width h (l, 1)} := by
  ext q
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have htx : Path.segment l r t ∈ Icc l r := by
      rw [← segment_eq_Icc hlr.le, ← Path.range_segment]
      exact mem_range_self t
    by_cases hs0 : s = 0
    · have hnzero : cuspOuterPath width h l r hh t ≠ 0 := by
        rw [cuspOuterPath_apply]
        simpa [cuspPolar] using cuspExponential_ne_zero width
          (((Path.segment l r t : ℝ) : ℂ) +
            (h (Path.segment l r t) : ℂ) * I)
      have hzero : cuspRadialPath width h l s = 0 := by
        rw [hs0]
        exact (cuspRadialPath width h l).source
      exact (hnzero (ht.trans (hs.symm.trans hzero))).elim
    have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm (Subtype.coe_ne_coe.2 hs0))
    have hp := cuspPolar_injOn_positiveClosedCuspStrip hwidth h hinj
      (show (l, (s : ℝ)) ∈ positiveClosedCuspStrip l r from
        ⟨le_rfl, hlr.le, hspos⟩)
      (show (Path.segment l r t, 1) ∈ positiveClosedCuspStrip l r from
        ⟨htx.1, htx.2, one_pos⟩)
      (by simpa only [cuspRadialPath_apply, cuspOuterPath_apply] using hs.trans ht.symm)
    have hs1 : (s : ℝ) = 1 := congrArg Prod.snd hp
    calc
      q = cuspRadialPath width h l s := hs.symm
      _ = cuspRadialPath width h l 1 := congrArg _ (Subtype.ext hs1)
      _ = cuspPolar width h (l, 1) := Path.target _
  · rintro rfl
    exact ⟨by simpa using mem_range_self (f := cuspRadialPath width h l) (1 : unitInterval),
      by simpa using mem_range_self (f := cuspOuterPath width h l r hh) (0 : unitInterval)⟩

theorem range_cuspOuterPath_inter_range_cuspRadialPath_right {width l r : ℝ}
    (hwidth : width ≠ 0) (h : ℝ → ℝ) (hh : Continuous h) (hlr : l < r)
    (hinj : InjOn (cuspExponential width) {z : ℂ | l ≤ z.re ∧ z.re ≤ r}) :
    range (cuspOuterPath width h l r hh) ∩ range (cuspRadialPath width h r) =
      {cuspPolar width h (r, 1)} := by
  ext q
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hsx : Path.segment l r s ∈ Icc l r := by
      rw [← segment_eq_Icc hlr.le, ← Path.range_segment]
      exact mem_range_self s
    by_cases ht0 : t = 0
    · have hnzero : cuspOuterPath width h l r hh s ≠ 0 := by
        rw [cuspOuterPath_apply]
        simpa [cuspPolar] using cuspExponential_ne_zero width
          (((Path.segment l r s : ℝ) : ℂ) +
            (h (Path.segment l r s) : ℂ) * I)
      have hzero : cuspRadialPath width h r t = 0 := by
        rw [ht0]
        exact (cuspRadialPath width h r).source
      exact (hnzero (hs.trans (ht.symm.trans hzero))).elim
    have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm (Subtype.coe_ne_coe.2 ht0))
    have hp := cuspPolar_injOn_positiveClosedCuspStrip hwidth h hinj
      (show (Path.segment l r s, 1) ∈ positiveClosedCuspStrip l r from
        ⟨hsx.1, hsx.2, one_pos⟩)
      (show (r, (t : ℝ)) ∈ positiveClosedCuspStrip l r from
        ⟨hlr.le, le_rfl, htpos⟩)
      (by simpa only [cuspOuterPath_apply, cuspRadialPath_apply] using hs.trans ht.symm)
    have ht1 : (t : ℝ) = 1 := (congrArg Prod.snd hp).symm
    calc
      q = cuspRadialPath width h r t := ht.symm
      _ = cuspRadialPath width h r 1 := congrArg _ (Subtype.ext ht1)
      _ = cuspPolar width h (r, 1) := Path.target _
  · rintro rfl
    exact ⟨by simpa using mem_range_self (f := cuspOuterPath width h l r hh) (1 : unitInterval),
      by simpa using mem_range_self (f := cuspRadialPath width h r) (1 : unitInterval)⟩

theorem range_cuspRadialPath_left_inter_right {width l r : ℝ}
    (hwidth : width ≠ 0) (h : ℝ → ℝ) (hlr : l < r)
    (hinj : InjOn (cuspExponential width) {z : ℂ | l ≤ z.re ∧ z.re ≤ r}) :
    range (cuspRadialPath width h l) ∩ range (cuspRadialPath width h r) = {0} := by
  ext q
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    by_cases hs0 : s = 0
    · calc
        q = cuspRadialPath width h l s := hs.symm
        _ = 0 := by rw [hs0]; exact (cuspRadialPath width h l).source
    by_cases ht0 : t = 0
    · calc
        q = cuspRadialPath width h r t := ht.symm
        _ = 0 := by rw [ht0]; exact (cuspRadialPath width h r).source
    have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm (Subtype.coe_ne_coe.2 hs0))
    have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm (Subtype.coe_ne_coe.2 ht0))
    have hp := cuspPolar_injOn_positiveClosedCuspStrip hwidth h hinj
      (show (l, (s : ℝ)) ∈ positiveClosedCuspStrip l r from
        ⟨le_rfl, hlr.le, hspos⟩)
      (show (r, (t : ℝ)) ∈ positiveClosedCuspStrip l r from
        ⟨hlr.le, le_rfl, htpos⟩)
      (by simpa only [cuspRadialPath_apply] using hs.trans ht.symm)
    exact (hlr.ne (congrArg Prod.fst hp)).elim
  · rintro rfl
    exact ⟨by simpa using mem_range_self (f := cuspRadialPath width h l) (0 : unitInterval),
      by simpa using mem_range_self (f := cuspRadialPath width h r) (0 : unitInterval)⟩

theorem range_cuspRadialPath (width : ℝ) (h : ℝ → ℝ) (x : ℝ) :
    range (cuspRadialPath width h x) = cuspPolar width h '' ({x} ×ˢ Icc 0 1) := by
  ext q
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(x, (t : ℝ)), ⟨rfl, t.2⟩, rfl⟩
  · rintro ⟨⟨x', t⟩, ⟨hx, ht⟩, rfl⟩
    simp only [mem_singleton_iff] at hx
    subst x'
    exact ⟨⟨t, ht⟩, rfl⟩

theorem range_cuspOuterPath {width l r : ℝ} (h : ℝ → ℝ) (hh : Continuous h)
    (hlr : l ≤ r) :
    range (cuspOuterPath width h l r hh) = cuspPolar width h '' (Icc l r ×ˢ {1}) := by
  ext q
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(Path.segment l r t, 1), ?_, rfl⟩
    refine ⟨?_, rfl⟩
    rw [← segment_eq_Icc hlr, ← Path.range_segment]
    exact mem_range_self t
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    simp only [mem_singleton_iff] at ht
    subst t
    have hxrange : x ∈ range (Path.segment l r) := by
      rw [Path.range_segment, segment_eq_Icc hlr]
      exact hx
    obtain ⟨s, hs⟩ := hxrange
    exact ⟨s, by simp only [cuspOuterPath_apply, hs]⟩

theorem range_cuspLeftOuterPath_inter_range_cuspRadialPath_right {width l r : ℝ}
    (hwidth : width ≠ 0) (h : ℝ → ℝ) (hh : Continuous h) (hlr : l < r)
    (hinj : InjOn (cuspExponential width) {z : ℂ | l ≤ z.re ∧ z.re ≤ r}) :
    range ((cuspRadialPath width h l).trans (cuspOuterPath width h l r hh)) ∩
        range (cuspRadialPath width h r) =
      {0, cuspPolar width h (r, 1)} := by
  rw [Path.trans_range]
  ext q
  simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hl | ho, hr⟩
    · left
      have hm : q ∈ ({0} : Set ℂ) := by
        rw [← range_cuspRadialPath_left_inter_right hwidth h hlr hinj]
        exact ⟨hl, hr⟩
      simpa using hm
    · right
      have hm : q ∈ ({cuspPolar width h (r, 1)} : Set ℂ) := by
        rw [← range_cuspOuterPath_inter_range_cuspRadialPath_right hwidth h hh hlr hinj]
        exact ⟨ho, hr⟩
      simpa using hm
  · rintro (rfl | rfl)
    · exact ⟨Or.inl (by simpa using
          mem_range_self (f := cuspRadialPath width h l) (0 : unitInterval)),
        by simpa using mem_range_self (f := cuspRadialPath width h r) (0 : unitInterval)⟩
    · exact ⟨Or.inr (by simpa using
          mem_range_self (f := cuspOuterPath width h l r hh) (1 : unitInterval)),
        by simpa using mem_range_self (f := cuspRadialPath width h r) (1 : unitInterval)⟩

theorem isJordanCurve_cuspPolar_boundary {width l r : ℝ}
    (hwidth : width ≠ 0) (h : ℝ → ℝ) (hh : Continuous h) (hlr : l < r)
    (hinj : InjOn (cuspExponential width) {z : ℂ | l ≤ z.re ∧ z.re ≤ r}) :
    TauCeti.IsJordanCurve (cuspPolar width h '' cuspRectangleBoundary l r) := by
  let left := cuspRadialPath width h l
  let outer := cuspOuterPath width h l r hh
  let right := cuspRadialPath width h r
  have hleft : Function.Injective left := cuspRadialPath_injective width h l
  have houter : Function.Injective outer := cuspOuterPath_injective hwidth h hh hlr hinj
  have hright : Function.Injective right := cuspRadialPath_injective width h r
  have hleftOuter : Function.Injective (left.trans outer) := by
    apply Path.trans_injective_of_inter_range_eq_singleton hleft houter
    exact range_cuspRadialPath_inter_range_cuspOuterPath_left hwidth h hh hlr hinj
  have hmeet : range (left.trans outer) ∩ range right =
      {0, cuspPolar width h (r, 1)} :=
    range_cuspLeftOuterPath_inter_range_cuspRadialPath_right hwidth h hh hlr hinj
  have hJ := TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair
    hleftOuter hright hmeet
  have hrange : range (left.trans outer) ∪ range right =
      cuspPolar width h '' cuspRectangleBoundary l r := by
    simp only [left, outer, right, Path.trans_range, range_cuspRadialPath,
      range_cuspOuterPath h hh hlr.le, cuspRectangleBoundary, image_union]
  rwa [hrange] at hJ

/-! The cusp origin has a basis of connected approach regions. -/

def openStripEpigraph (l r : ℝ) (phi : ℝ → ℝ) : Set ℂ :=
  {z | l < z.re ∧ z.re < r ∧ phi z.re < z.im}

def flatOpenStrip (l r : ℝ) : Set ℂ :=
  {z | l < z.re ∧ z.re < r ∧ 0 < z.im}

theorem verticalShear_image_openStripEpigraph {l r : ℝ} {phi : ℝ → ℝ}
    (hphi : Continuous phi) :
    verticalShear phi hphi '' openStripEpigraph l r phi = flatOpenStrip l r := by
  ext w
  constructor
  · rintro ⟨z, ⟨hl, hr, hi⟩, rfl⟩
    change l < (verticalShear phi hphi z).re ∧
      (verticalShear phi hphi z).re < r ∧ 0 < (verticalShear phi hphi z).im
    simpa only [verticalShear_re, verticalShear_im] using
      (show l < z.re ∧ z.re < r ∧ 0 < z.im - phi z.re from
        ⟨hl, hr, sub_pos.mpr hi⟩)
  · rintro ⟨hl, hr, hi⟩
    let z : ℂ := (verticalShear phi hphi).symm w
    refine ⟨z, ?_, (verticalShear phi hphi).apply_symm_apply w⟩
    have hzre : z.re = w.re := by simp [z, verticalShear]
    have hzim : z.im = w.im + phi w.re := by simp [z, verticalShear]
    exact ⟨by simpa [hzre] using hl, by simpa [hzre] using hr, by rw [hzim, hzre]; linarith⟩

theorem flatOpenStrip_convex (l r : ℝ) : Convex ℝ (flatOpenStrip l r) := by
  rw [show flatOpenStrip l r =
      {z : ℂ | l < z.re} ∩ ({z : ℂ | z.re < r} ∩ {z : ℂ | 0 < z.im}) by
    ext z
    simp [flatOpenStrip]]
  exact (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_gt _))

theorem openStripEpigraph_isPreconnected {l r : ℝ} {phi : ℝ → ℝ}
    (hphi : Continuous phi) : IsPreconnected (openStripEpigraph l r phi) := by
  have himage : IsPreconnected (verticalShear phi hphi '' openStripEpigraph l r phi) := by
    rw [verticalShear_image_openStripEpigraph hphi]
    exact (flatOpenStrip_convex l r).isPreconnected
  exact ((verticalShear phi hphi).isPreconnected_image).mp himage

def cuspBallHeight (width epsilon : ℝ) : ℝ :=
  -width * Real.log epsilon / (2 * Real.pi)

theorem norm_cuspExponential_lt_iff_height {width epsilon : ℝ}
    (hwidth : 0 < width) (hepsilon : 0 < epsilon) (z : ℂ) :
    ‖cuspExponential width z‖ < epsilon ↔ cuspBallHeight width epsilon < z.im := by
  rw [norm_cuspExponential width hwidth.ne' z]
  rw [← Real.lt_log_iff_exp_lt hepsilon]
  unfold cuspBallHeight
  constructor
  · intro h
    apply (div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)).2
    have h' := (div_lt_iff₀ hwidth).1 h
    nlinarith
  · intro h
    apply (div_lt_iff₀ hwidth).2
    have h' := (div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)).1 h
    nlinarith

theorem sourceOpenChamber_eq_heightEpigraph :
    sourceOpenChamber =
      {z : ℂ | -Real.sqrt 2 / 2 < z.re ∧ z.re < 1 / 2 ∧ semicircleHeight z.re < z.im} := by
  ext z
  simp only [sourceOpenChamber, mem_setOf_eq]
  constructor
  · rintro ⟨hl, hr, hi, hn⟩
    exact ⟨hl, hr, (source_normSq_iff_height hl hr hi).mp hn⟩
  · rintro ⟨hl, hr, hh⟩
    have hs0 : 0 ≤ semicircleHeight z.re := by
      unfold semicircleHeight
      positivity
    have hi : 0 < z.im := lt_of_le_of_lt hs0 hh
    exact ⟨hl, hr, hi, (source_normSq_iff_height hl hr hi).mpr hh⟩

theorem targetOpenChamber_eq_heightEpigraph :
    targetOpenChamber =
      {z : ℂ | 0 < z.re ∧ z.re < 1 / 2 ∧ semicircleHeight z.re < z.im} := by
  ext z
  simp only [targetOpenChamber, mem_setOf_eq]
  constructor
  · rintro ⟨hl, hr, hi, hn⟩
    exact ⟨hl, hr, (target_normSq_iff_height hl hr hi).mp hn⟩
  · rintro ⟨hl, hr, hh⟩
    have hs0 : 0 ≤ semicircleHeight z.re := by
      unfold semicircleHeight
      positivity
    have hi : 0 < z.im := lt_of_le_of_lt hs0 hh
    exact ⟨hl, hr, hi, (target_normSq_iff_height hl hr hi).mpr hh⟩

private theorem re_add_im_mul_I (z : ℂ) :
    (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := by
  apply Complex.ext <;> simp

theorem sourceBoundedChamber_eq_cuspPolar_image :
    sourceBoundedChamber =
      cuspPolar (1 + Real.sqrt 2) semicircleHeight ''
        openCuspRectangle (-Real.sqrt 2 / 2) (1 / 2) := by
  rw [sourceBoundedChamber]
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [sourceOpenChamber_eq_heightEpigraph] at hz
    let t : ℝ := Real.exp
      (-2 * Real.pi * (z.im - semicircleHeight z.re) / (1 + Real.sqrt 2))
    refine ⟨(z.re, t), ?_, ?_⟩
    · refine ⟨⟨hz.1, hz.2.1⟩, Real.exp_pos _, ?_⟩
      apply Real.exp_lt_one_iff.mpr
      have hd : 0 < z.im - semicircleHeight z.re := sub_pos.mpr hz.2.2
      have hpi : 0 < Real.pi := Real.pi_pos
      have hw : 0 < 1 + Real.sqrt 2 := by positivity
      exact div_neg_of_neg_of_pos (by nlinarith) hw
    · simpa [t, re_add_im_mul_I z] using
        (cuspExponential_eq_cuspPolar (1 + Real.sqrt 2)
          (ne_of_gt (by positivity : 0 < 1 + Real.sqrt 2))
          semicircleHeight z.re z.im).symm
  · rintro ⟨p, hp, rfl⟩
    rcases p with ⟨x, t⟩
    change (x ∈ Ioo (-Real.sqrt 2 / 2) (1 / 2)) ∧ t ∈ Ioo 0 1 at hp
    rcases hp with ⟨⟨hl, hr⟩, ht0, ht1⟩
    let y : ℝ := semicircleHeight x -
      (1 + Real.sqrt 2) * Real.log t / (2 * Real.pi)
    refine ⟨(x : ℂ) + (y : ℂ) * Complex.I, ?_, ?_⟩
    · rw [sourceOpenChamber_eq_heightEpigraph]
      simp only [mem_ofPred_eq, Complex.add_re, ofReal_re, Complex.mul_re, Complex.mul_im, ofReal_im,
        I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, mul_one, zero_add]
      refine ⟨hl, hr, ?_⟩
      dsimp [y]
      have hlog : Real.log t < 0 := Real.log_neg ht0 ht1
      have hw : 0 < 1 + Real.sqrt 2 := by positivity
      have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
      have : (1 + Real.sqrt 2) * Real.log t / (2 * Real.pi) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hw hlog) hpi
      linarith
    · simpa [y] using (cuspPolar_eq_cuspExponential _
        (ne_of_gt (by positivity : 0 < 1 + Real.sqrt 2)) _ x ht0).symm

theorem targetBoundedChamber_eq_cuspPolar_image :
    targetBoundedChamber =
      cuspPolar 1 semicircleHeight '' openCuspRectangle 0 (1 / 2) := by
  rw [targetBoundedChamber]
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [targetOpenChamber_eq_heightEpigraph] at hz
    let t : ℝ := Real.exp (-2 * Real.pi * (z.im - semicircleHeight z.re))
    refine ⟨(z.re, t), ?_, ?_⟩
    · refine ⟨⟨hz.1, hz.2.1⟩, Real.exp_pos _, ?_⟩
      apply Real.exp_lt_one_iff.mpr
      have hd : 0 < z.im - semicircleHeight z.re := sub_pos.mpr hz.2.2
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    · simpa [t, re_add_im_mul_I z] using
        (cuspExponential_eq_cuspPolar 1 one_ne_zero semicircleHeight z.re z.im).symm
  · rintro ⟨p, hp, rfl⟩
    rcases p with ⟨x, t⟩
    change (x ∈ Ioo 0 (1 / 2)) ∧ t ∈ Ioo 0 1 at hp
    rcases hp with ⟨⟨hl, hr⟩, ht0, ht1⟩
    let y : ℝ := semicircleHeight x - Real.log t / (2 * Real.pi)
    refine ⟨(x : ℂ) + (y : ℂ) * Complex.I, ?_, ?_⟩
    · rw [targetOpenChamber_eq_heightEpigraph]
      simp only [mem_ofPred_eq, Complex.add_re, ofReal_re, Complex.mul_re, Complex.mul_im, ofReal_im,
        I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, mul_one, zero_add]
      refine ⟨hl, hr, ?_⟩
      dsimp [y]
      have hlog : Real.log t < 0 := Real.log_neg ht0 ht1
      have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
      have : Real.log t / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos hlog hpi
      linarith
    · simpa [y] using (cuspPolar_eq_cuspExponential 1 one_ne_zero
        semicircleHeight x ht0).symm

theorem closure_sourceBoundedChamber :
    closure sourceBoundedChamber =
      cuspPolar (1 + Real.sqrt 2) semicircleHeight ''
        closedCuspRectangle (-Real.sqrt 2 / 2) (1 / 2) := by
  rw [sourceBoundedChamber_eq_cuspPolar_image]
  apply closure_cuspPolar_image
  · have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  · exact continuous_semicircleHeight

theorem closure_targetBoundedChamber :
    closure targetBoundedChamber =
      cuspPolar 1 semicircleHeight '' closedCuspRectangle 0 (1 / 2) := by
  rw [targetBoundedChamber_eq_cuspPolar_image]
  exact closure_cuspPolar_image (by norm_num) continuous_semicircleHeight

theorem frontier_sourceBoundedChamber_eq_cuspPolar_boundary :
    frontier sourceBoundedChamber =
      cuspPolar (1 + Real.sqrt 2) semicircleHeight ''
        cuspRectangleBoundary (-Real.sqrt 2 / 2) (1 / 2) := by
  rw [sourceBoundedChamber_eq_cuspPolar_image]
  apply frontier_cuspPolar_image
  · exact (ne_of_gt (by positivity : 0 < 1 + Real.sqrt 2))
  · have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  · exact continuous_semicircleHeight
  · rw [← sourceBoundedChamber_eq_cuspPolar_image]
    exact sourceBoundedChamber_isOpen
  · exact source_cuspExponential_injOn_closedStrip

theorem frontier_targetBoundedChamber_eq_cuspPolar_boundary :
    frontier targetBoundedChamber =
      cuspPolar 1 semicircleHeight '' cuspRectangleBoundary 0 (1 / 2) := by
  rw [targetBoundedChamber_eq_cuspPolar_image]
  apply frontier_cuspPolar_image one_ne_zero (by norm_num) continuous_semicircleHeight
  · rw [← targetBoundedChamber_eq_cuspPolar_image]
    exact targetBoundedChamber_isOpen
  · exact target_cuspExponential_injOn_closedStrip

theorem sourceBoundedChamber_frontier_isJordanCurve :
    TauCeti.IsJordanCurve (frontier sourceBoundedChamber) := by
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  apply isJordanCurve_cuspPolar_boundary
  · exact (ne_of_gt (by positivity : 0 < 1 + Real.sqrt 2))
  · exact continuous_semicircleHeight
  · have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  · exact source_cuspExponential_injOn_closedStrip

theorem targetBoundedChamber_frontier_isJordanCurve :
    TauCeti.IsJordanCurve (frontier targetBoundedChamber) := by
  rw [frontier_targetBoundedChamber_eq_cuspPolar_boundary]
  exact isJordanCurve_cuspPolar_boundary one_ne_zero semicircleHeight
    continuous_semicircleHeight (by norm_num) target_cuspExponential_injOn_closedStrip

theorem sourceOpenChamber_inter_cuspExponential_preimage_ball {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    sourceOpenChamber ∩ cuspExponential (1 + Real.sqrt 2) ⁻¹' Metric.ball 0 epsilon =
      openStripEpigraph (-Real.sqrt 2 / 2) (1 / 2)
        (fun x => max (semicircleHeight x) (cuspBallHeight (1 + Real.sqrt 2) epsilon)) := by
  ext z
  rw [sourceOpenChamber_eq_heightEpigraph]
  change ((-Real.sqrt 2 / 2 < z.re ∧ z.re < 1 / 2 ∧
      semicircleHeight z.re < z.im) ∧
      cuspExponential (1 + Real.sqrt 2) z ∈ Metric.ball 0 epsilon) ↔
    -Real.sqrt 2 / 2 < z.re ∧ z.re < 1 / 2 ∧
      max (semicircleHeight z.re) (cuspBallHeight (1 + Real.sqrt 2) epsilon) < z.im
  have hw : 0 < 1 + Real.sqrt 2 := by positivity
  have hball : cuspExponential (1 + Real.sqrt 2) z ∈ Metric.ball 0 epsilon ↔
      cuspBallHeight (1 + Real.sqrt 2) epsilon < z.im := by
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_cuspExponential_lt_iff_height hw hepsilon z
  rw [hball, max_lt_iff]
  tauto

theorem targetOpenChamber_inter_cuspExponential_preimage_ball {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    targetOpenChamber ∩ cuspExponential 1 ⁻¹' Metric.ball 0 epsilon =
      openStripEpigraph 0 (1 / 2)
        (fun x => max (semicircleHeight x) (cuspBallHeight 1 epsilon)) := by
  ext z
  rw [targetOpenChamber_eq_heightEpigraph]
  change ((0 < z.re ∧ z.re < 1 / 2 ∧ semicircleHeight z.re < z.im) ∧
      cuspExponential 1 z ∈ Metric.ball 0 epsilon) ↔
    0 < z.re ∧ z.re < 1 / 2 ∧
      max (semicircleHeight z.re) (cuspBallHeight 1 epsilon) < z.im
  have hball : cuspExponential 1 z ∈ Metric.ball 0 epsilon ↔
      cuspBallHeight 1 epsilon < z.im := by
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_cuspExponential_lt_iff_height one_pos hepsilon z
  rw [hball, max_lt_iff]
  tauto

theorem sourceBoundedChamber_inter_ball_isPreconnected {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    IsPreconnected (sourceBoundedChamber ∩ Metric.ball 0 epsilon) := by
  rw [sourceBoundedChamber, ← image_inter_preimage]
  apply IsPreconnected.image (f := cuspExponential (1 + Real.sqrt 2))
  · rw [sourceOpenChamber_inter_cuspExponential_preimage_ball hepsilon]
    apply openStripEpigraph_isPreconnected
    exact continuous_semicircleHeight.max continuous_const
  · exact (cuspExponential_continuous _).continuousOn

theorem targetBoundedChamber_inter_ball_isPreconnected {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    IsPreconnected (targetBoundedChamber ∩ Metric.ball 0 epsilon) := by
  rw [targetBoundedChamber, ← image_inter_preimage]
  apply IsPreconnected.image (f := cuspExponential 1)
  · rw [targetOpenChamber_inter_cuspExponential_preimage_ball hepsilon]
    apply openStripEpigraph_isPreconnected
    exact continuous_semicircleHeight.max continuous_const
  · exact (cuspExponential_continuous _).continuousOn

theorem sourceBoundedChamber_isPreconnectedApproachAt_zero :
    ∀ s ∈ 𝓝 (0 : ℂ), ∃ t ∈ 𝓝 (0 : ℂ),
      t ⊆ s ∧ IsPreconnected (sourceBoundedChamber ∩ t) := by
  intro s hs
  obtain ⟨epsilon, hepsilon, hepsilons⟩ := Metric.mem_nhds_iff.mp hs
  exact ⟨Metric.ball 0 epsilon, Metric.ball_mem_nhds 0 hepsilon, hepsilons,
    sourceBoundedChamber_inter_ball_isPreconnected hepsilon⟩

theorem targetBoundedChamber_isPreconnectedApproachAt_zero :
    ∀ s ∈ 𝓝 (0 : ℂ), ∃ t ∈ 𝓝 (0 : ℂ),
      t ⊆ s ∧ IsPreconnected (targetBoundedChamber ∩ t) := by
  intro s hs
  obtain ⟨epsilon, hepsilon, hepsilons⟩ := Metric.mem_nhds_iff.mp hs
  exact ⟨Metric.ball 0 epsilon, Metric.ball_mem_nhds 0 hepsilon, hepsilons,
    targetBoundedChamber_inter_ball_isPreconnected hepsilon⟩


end SphereSixComplex.Periods.SourceChamberTopology
