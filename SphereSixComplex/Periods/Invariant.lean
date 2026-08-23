module

public import SphereSixComplex.Periods.Nondegeneracy
public import SphereSixComplex.Periods.Transformations
import all SphereSixComplex.Periods.Matrix

/-!
# Invariance of the period-domain inequalities

The algebraic invariance asserted in Lemma 3.14.
-/

namespace SphereSixComplex.Periods

@[expose] public noncomputable def schurQuantity (x : Parameters) : ℝ :=
  x.beta.im - 6 * x.mu.im ^ 2 / x.tau.im

public theorem transformOne_tau_im (x : Parameters) :
    (transformOne x).tau.im = x.tau.im / Complex.normSq x.tau := by
  simp [SphereSixComplex.Periods.transformOne.eq_def, Complex.div_im]
  ring

public theorem transformTwo_tau_im (x : Parameters) :
    (transformTwo x).tau.im = x.tau.im / Complex.normSq x.tau := by
  simp [SphereSixComplex.Periods.transformTwo.eq_def, Complex.div_im]
  ring

public theorem transformCusp_tau_im (x : Parameters) :
    (transformCusp x).tau.im = x.tau.im := by
  simp [SphereSixComplex.Periods.transformCusp.eq_def]

public theorem schurQuantity_transformOne (x : Parameters) (him : x.tau.im ≠ 0) :
    schurQuantity (transformOne x) = schurQuantity x := by
  have htau : x.tau ≠ 0 := by
    intro hzero
    exact him (congrArg Complex.im hzero)
  have hnorm : Complex.normSq x.tau ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr htau)
  simp [schurQuantity, SphereSixComplex.Periods.transformOne.eq_def, Complex.div_im,
    Complex.add_im, Complex.sub_im, Complex.sub_re, Complex.mul_im,
    Complex.mul_re, Complex.normSq_apply, pow_two]
  field_simp [him, hnorm]
  ring

public theorem schurQuantity_transformTwo (x : Parameters) (him : x.tau.im ≠ 0) :
    schurQuantity (transformTwo x) = schurQuantity x := by
  have htau : x.tau ≠ 0 := by
    intro hzero
    exact him (congrArg Complex.im hzero)
  have hnorm : Complex.normSq x.tau ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr htau)
  simp [schurQuantity, SphereSixComplex.Periods.transformTwo.eq_def, Complex.div_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.mul_re, Complex.normSq_apply, pow_two]
  field_simp [him, hnorm]
  ring

public theorem schurQuantity_transformCusp (x : Parameters) :
    schurQuantity (transformCusp x) = schurQuantity x := by
  simp [schurQuantity, SphereSixComplex.Periods.transformCusp.eq_def]

public theorem setupInequalities_transformOne (x : Parameters) (h : SetupInequalities x) :
    SetupInequalities (transformOne x) := by
  have htau : x.tau ≠ 0 := by
    intro hzero
    simpa [hzero] using h.tau_im_pos.ne'
  constructor
  · rw [transformOne_tau_im]
    exact div_pos h.tau_im_pos (Complex.normSq_pos.mpr htau)
  · change schurQuantity (transformOne x) < 0
    rw [schurQuantity_transformOne x h.tau_im_pos.ne']
    exact h.schur_im_neg

public theorem setupInequalities_transformTwo (x : Parameters) (h : SetupInequalities x) :
    SetupInequalities (transformTwo x) := by
  have htau : x.tau ≠ 0 := by
    intro hzero
    simpa [hzero] using h.tau_im_pos.ne'
  constructor
  · rw [transformTwo_tau_im]
    exact div_pos h.tau_im_pos (Complex.normSq_pos.mpr htau)
  · change schurQuantity (transformTwo x) < 0
    rw [schurQuantity_transformTwo x h.tau_im_pos.ne']
    exact h.schur_im_neg

public theorem setupInequalities_transformCusp (x : Parameters) (h : SetupInequalities x) :
    SetupInequalities (transformCusp x) := by
  constructor
  · rw [transformCusp_tau_im]
    exact h.tau_im_pos
  · change schurQuantity (transformCusp x) < 0
    rw [schurQuantity_transformCusp]
    exact h.schur_im_neg

end SphereSixComplex.Periods
