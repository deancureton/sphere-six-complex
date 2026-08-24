module

public import SphereSixComplex.Periods.Uniformization.ChamberMarkedEquivalence
import all SphereSixComplex.Periods.Uniformization.ChamberMarkedEquivalence

@[expose] public section

open Complex Metric Set Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup

/-! A normalized scalar Schwarz-triangle seed.  Its target is one of the two open half-planes;
the sign is determined by the cyclic order of the two finite marked boundary points. -/

def signedHalfPlane (d : ℝ) : Set ℂ := {w | 0 < d * w.im}

theorem signedHalfPlane_isOpen (d : ℝ) : IsOpen (signedHalfPlane d) := by
  exact isOpen_lt continuous_const
    (continuous_const.mul Complex.continuous_im)

/-- A real affine coordinate identifies the upper half-plane with the half-plane selected by a
nonzero real sign `d`. -/
noncomputable def upperHalfPlaneSignedAffineEquiv (a d : ℝ) (hd : d ≠ 0) :
    UpperHalfPlane ≃ signedHalfPlane d where
  toFun w := ⟨((w : ℂ) - (a : ℂ)) / (d : ℂ), by
    have him : (((w : ℂ) - (a : ℂ)) / (d : ℂ)).im = w.im / d := by
      rw [Complex.div_im]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        sub_zero, mul_zero, Complex.normSq_ofReal]
      field_simp [hd]
      rw [sub_zero, UpperHalfPlane.coe_im]
      exact mul_comm _ _
    change 0 < d * (((w : ℂ) - (a : ℂ)) / (d : ℂ)).im
    rw [him]
    have heq : d * (w.im / d) = w.im := by field_simp [hd]
    rw [heq]
    exact w.im_pos⟩
  invFun w := ⟨(a : ℂ) + (d : ℂ) * (w : ℂ), by
    have hw : 0 < d * (w : ℂ).im := w.2
    simpa [Complex.mul_im] using hw⟩
  left_inv w := by
    apply UpperHalfPlane.coe_injective
    change (a : ℂ) + d * (((w : ℂ) - a) / d) = w
    field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast hd]
    ring
  right_inv w := by
    apply Subtype.ext
    change (((a : ℂ) + d * (w : ℂ) - a) / d) = w
    field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast hd]
    ring

@[simp] theorem coe_upperHalfPlaneSignedAffineEquiv_apply
    (a d : ℝ) (hd : d ≠ 0) (w : UpperHalfPlane) :
    (upperHalfPlaneSignedAffineEquiv a d hd w : ℂ) =
      ((w : ℂ) - (a : ℂ)) / (d : ℂ) := rfl

/-- Difference of the finite Cayley coordinates used to normalize them to `0` and `1`. -/
def scalarTriangleDenominator (pole first second : Circle) : ℝ :=
  circleCayleyCoord pole second - circleCayleyCoord pole first

theorem scalarTriangleDenominator_ne_zero
    {pole first second : Circle} (hfirst : first ≠ pole) (hsecond : second ≠ pole)
    (hfinite : first ≠ second) :
    scalarTriangleDenominator pole first second ≠ 0 := by
  exact sub_ne_zero.mpr
    (circleCayleyCoord_ne hsecond hfirst hfinite.symm)

/-- The rational scalar coordinate on the disc, normalized at the two finite marked points. -/
def scalarTriangleDiscMap (pole first second : Circle) (z : ℂ) : ℂ :=
  (boundaryCayley pole z - circleCayleyCoord pole first) /
    scalarTriangleDenominator pole first second

/-- The corresponding equivalence of the open unit disc with a signed half-plane. -/
noncomputable def scalarTriangleUnitDiscEquiv
    (pole first second : Circle) (hfirst : first ≠ pole) (hsecond : second ≠ pole)
    (hfinite : first ≠ second) : Complex.UnitDisc ≃
      signedHalfPlane (scalarTriangleDenominator pole first second) :=
  (unitDiscEquivUpperHalfPlane pole).trans
    (upperHalfPlaneSignedAffineEquiv
      (circleCayleyCoord pole first)
      (scalarTriangleDenominator pole first second)
      (scalarTriangleDenominator_ne_zero hfirst hsecond hfinite))

@[simp] theorem coe_scalarTriangleUnitDiscEquiv_apply
    (pole first second : Circle) (hfirst : first ≠ pole) (hsecond : second ≠ pole)
    (hfinite : first ≠ second) (z : Complex.UnitDisc) :
    (scalarTriangleUnitDiscEquiv pole first second hfirst hsecond hfinite z : ℂ) =
      scalarTriangleDiscMap pole first second z := rfl

theorem scalarTriangleDiscMap_bijOn
    (pole first second : Circle) (hfirst : first ≠ pole) (hsecond : second ≠ pole)
    (hfinite : first ≠ second) :
    BijOn (scalarTriangleDiscMap pole first second) (ball (0 : ℂ) 1)
      (signedHalfPlane (scalarTriangleDenominator pole first second)) := by
  let E := scalarTriangleUnitDiscEquiv pole first second hfirst hsecond hfinite
  have mem : ∀ z : Complex.UnitDisc, (z : ℂ) ∈ ball (0 : ℂ) 1 := fun z => by
    simpa [mem_ball_zero_iff] using z.norm_lt_one
  have exists_coe : ∀ w ∈ ball (0 : ℂ) 1, ∃ z : Complex.UnitDisc, (z : ℂ) = w :=
    fun w hw => ⟨Complex.UnitDisc.mk w (by simpa [mem_ball_zero_iff] using hw), rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, rfl⟩ := exists_coe w hw
    have hE := (E z).2
    simpa only [E, coe_scalarTriangleUnitDiscEquiv_apply] using hE
  · intro w₁ h₁ w₂ h₂ h
    obtain ⟨z₁, rfl⟩ := exists_coe w₁ h₁
    obtain ⟨z₂, rfl⟩ := exists_coe w₂ h₂
    have hE : E z₁ = E z₂ := by
      apply Subtype.ext
      simpa only [E, coe_scalarTriangleUnitDiscEquiv_apply] using h
    exact congrArg ((↑) : Complex.UnitDisc → ℂ) (E.injective hE)
  · intro v hv
    let v' : signedHalfPlane (scalarTriangleDenominator pole first second) := ⟨v, hv⟩
    refine ⟨(E.symm v' : ℂ), mem _, ?_⟩
    rw [← coe_scalarTriangleUnitDiscEquiv_apply
      pole first second hfirst hsecond hfinite]
    exact congrArg Subtype.val (E.apply_symm_apply v')

theorem scalarTriangleDiscMap_differentiableOn
    (pole first second : Circle) (hfirst : first ≠ pole) (hsecond : second ≠ pole)
    (hfinite : first ≠ second) :
    DifferentiableOn ℂ (scalarTriangleDiscMap pole first second) (ball (0 : ℂ) 1) := by
  intro z hz
  have hnorm : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hpole : (pole : ℂ) - z ≠ 0 := by
    intro h
    have heq : (pole : ℂ) = z := sub_eq_zero.mp h
    have hn := congrArg norm heq
    rw [Circle.norm_coe] at hn
    linarith
  have hcayley : DifferentiableAt ℂ (boundaryCayley pole) z :=
    differentiableAt_boundaryCayley hpole
  have hden : (scalarTriangleDenominator pole first second : ℂ) ≠ 0 := by
    exact_mod_cast scalarTriangleDenominator_ne_zero hfirst hsecond hfinite
  exact ((hcayley.sub_const _).div_const _).differentiableWithinAt

theorem scalarTriangleDiscMap_differentiableOn_ne_pole
    (pole first second : Circle) (hfirst : first ≠ pole) (hsecond : second ≠ pole)
    (hfinite : first ≠ second) :
    DifferentiableOn ℂ (scalarTriangleDiscMap pole first second)
      {z : ℂ | z ≠ pole} := by
  intro z hz
  have hpole : (pole : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hcayley : DifferentiableAt ℂ (boundaryCayley pole) z :=
    differentiableAt_boundaryCayley hpole
  exact ((hcayley.sub_const _).div_const _).differentiableWithinAt

theorem scalarTriangleDiscMap_im_eq_zero
    (pole first second z : Circle) :
    (scalarTriangleDiscMap pole first second z).im = 0 := by
  rw [scalarTriangleDiscMap, Complex.div_im]
  have hc := boundaryCayley_im_eq_zero (Circle.norm_coe pole) (Circle.norm_coe z)
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, mul_zero, zero_mul, Complex.normSq_ofReal, hc, zero_mul, zero_sub]
  simp

theorem scalarTriangleDiscMap_first
    {pole first second : Circle} (hfirst : first ≠ pole) :
    scalarTriangleDiscMap pole first second first = 0 := by
  rw [scalarTriangleDiscMap, boundaryCayley_circle_eq_ofReal]
  simp

theorem scalarTriangleDiscMap_second
    {pole first second : Circle} (hfirst : first ≠ pole) (hsecond : second ≠ pole)
    (hfinite : first ≠ second) :
    scalarTriangleDiscMap pole first second second = 1 := by
  rw [scalarTriangleDiscMap, boundaryCayley_circle_eq_ofReal]
  have hden := scalarTriangleDenominator_ne_zero hfirst hsecond hfinite
  rw [← Complex.ofReal_sub]
  change (((circleCayleyCoord pole second - circleCayleyCoord pole first : ℝ) : ℂ) /
    (scalarTriangleDenominator pole first second : ℂ)) = 1
  rw [show circleCayleyCoord pole second - circleCayleyCoord pole first =
    scalarTriangleDenominator pole first second by rfl]
  exact div_self (by exact_mod_cast hden)

/-! ## The inverse Carathéodory map on a chamber closure -/

/-- The scalar-valued inverse of the closed-disc Carathéodory homeomorphism, extended arbitrarily
off the chamber closure. -/
def chamberClosureDiscInverse {Ω : Set ℂ} (S : ChamberCaratheodorySeed Ω) (q : ℂ) : ℂ :=
  by
    classical
    exact if hq : q ∈ closure Ω then (S.closureEquiv.symm ⟨q, hq⟩ : ℂ) else 0

theorem chamberClosureDiscInverse_apply_of_mem {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) {q : ℂ} (hq : q ∈ closure Ω) :
    chamberClosureDiscInverse S q = (S.closureEquiv.symm ⟨q, hq⟩ : ℂ) := by
  simp only [chamberClosureDiscInverse, dif_pos hq]

theorem chamberClosureDiscInverse_mem_closedBall {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) {q : ℂ} (hq : q ∈ closure Ω) :
    chamberClosureDiscInverse S q ∈ closedBall (0 : ℂ) 1 := by
  rw [chamberClosureDiscInverse_apply_of_mem S hq]
  exact (S.closureEquiv.symm ⟨q, hq⟩).2

theorem chamberClosureDiscInverse_continuousOn {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) :
    ContinuousOn (chamberClosureDiscInverse S) (closure Ω) := by
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous fun q : closure Ω ↦
      ((S.closureEquiv.symm q : closedBall (0 : ℂ) 1) : ℂ) :=
    continuous_subtype_val.comp S.closureEquiv.symm.continuous
  apply hc.congr
  intro q
  exact (chamberClosureDiscInverse_apply_of_mem S q.2).symm

theorem chamberClosureDiscInverse_eq_invFunOn {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) {q : ℂ} (hq : q ∈ Ω) :
    chamberClosureDiscInverse S q = Function.invFunOn S.map (ball (0 : ℂ) 1) q := by
  obtain ⟨u, hu, huq⟩ := S.bijOn.surjOn hq
  have huclosed : u ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hu
  have hsymm : S.closureEquiv.symm ⟨q, subset_closure hq⟩ =
      (⟨u, huclosed⟩ : closedBall (0 : ℂ) 1) := by
    apply S.closureEquiv.injective
    rw [S.closureEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [S.closureEquiv_apply]
    exact huq.symm
  calc
    chamberClosureDiscInverse S q =
        (S.closureEquiv.symm ⟨q, subset_closure hq⟩ : ℂ) :=
      chamberClosureDiscInverse_apply_of_mem S (subset_closure hq)
    _ = u := congrArg Subtype.val hsymm
    _ = Function.invFunOn S.map (ball (0 : ℂ) 1) q := by
      rw [← huq]
      exact (S.bijOn.injOn.leftInvOn_invFunOn hu).symm

theorem chamberClosureDiscInverse_boundaryPreimage {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) (hΩo : IsOpen Ω) (v : ℂ)
    (hv : v ∈ frontier Ω) :
    chamberClosureDiscInverse S v = S.boundaryPreimage hΩo v hv := by
  rw [chamberClosureDiscInverse_apply_of_mem S (frontier_subset_closure hv),
    S.coe_boundaryPreimage]

/-! ## The scalar seed on the bounded and original source chambers -/

private theorem sourceSeed_invFunOn_bijOn_scalar
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    BijOn (Function.invFunOn S.map (ball (0 : ℂ) 1))
      sourceBoundedChamber (ball 0 1) :=
  BijOn.symm S.bijOn.invOn_invFunOn.symm S.bijOn

def sourceScalarBoundedChamberMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℂ → ℂ :=
  scalarTriangleDiscMap (sourceCuspCircle S) (sourceOrderThreeCircle S)
      (sourceOtherEllipticCircle S) ∘
    Function.invFunOn S.map (ball (0 : ℂ) 1)

/-- The boundary-aware version of the scalar chamber coordinate.  At the completed cusp its
totalized Cayley formula has an arbitrary finite value; all analytic uses exclude that one point. -/
def sourceScalarClosureMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℂ → ℂ :=
  scalarTriangleDiscMap (sourceCuspCircle S) (sourceOrderThreeCircle S)
      (sourceOtherEllipticCircle S) ∘ chamberClosureDiscInverse S

theorem sourceScalarClosureMap_eq_bounded_of_mem
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {q : ℂ}
    (hq : q ∈ sourceBoundedChamber) :
    sourceScalarClosureMap S q = sourceScalarBoundedChamberMap S q := by
  rw [sourceScalarClosureMap, sourceScalarBoundedChamberMap, Function.comp_apply,
    Function.comp_apply, chamberClosureDiscInverse_eq_invFunOn S hq]

theorem sourceScalarClosureMap_orderThree
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceScalarClosureMap S sourceOrderThreeVertex = 0 := by
  rw [sourceScalarClosureMap, Function.comp_apply,
    chamberClosureDiscInverse_boundaryPreimage S sourceBoundedChamber_isOpen _
      sourceOrderThreeVertex_mem_frontier]
  exact scalarTriangleDiscMap_first (sourceOrderThreeCircle_ne_cusp S)

theorem sourceScalarClosureMap_otherElliptic
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceScalarClosureMap S sourceOtherEllipticVertex = 1 := by
  rw [sourceScalarClosureMap, Function.comp_apply,
    chamberClosureDiscInverse_boundaryPreimage S sourceBoundedChamber_isOpen _
      sourceOtherEllipticVertex_mem_frontier]
  exact scalarTriangleDiscMap_second
    (sourceOrderThreeCircle_ne_cusp S) (sourceOtherEllipticCircle_ne_cusp S)
    (sourceOrderThreeCircle_ne_otherElliptic S)

theorem sourceScalarClosureMap_im_eq_zero_of_frontier
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {q : ℂ}
    (hq : q ∈ frontier sourceBoundedChamber) :
    (sourceScalarClosureMap S q).im = 0 := by
  rw [sourceScalarClosureMap, Function.comp_apply,
    chamberClosureDiscInverse_boundaryPreimage S sourceBoundedChamber_isOpen q hq]
  exact scalarTriangleDiscMap_im_eq_zero _ _ _ _

private theorem chamberClosureDiscInverse_ne_sourceCuspCircle
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {q : ℂ}
    (hq : q ∈ closure sourceBoundedChamber) (hne : q ≠ sourceCuspVertex) :
    chamberClosureDiscInverse S q ≠ sourceCuspCircle S := by
  intro heq
  let pole : closedBall (0 : ℂ) 1 :=
    ⟨sourceCuspCircle S, by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩
  have hinv : S.closureEquiv.symm ⟨q, hq⟩ = pole := by
    apply Subtype.ext
    simpa [pole, chamberClosureDiscInverse_apply_of_mem S hq] using heq
  have himage := congrArg S.closureEquiv hinv
  have hpole : S.closureEquiv pole =
      ⟨sourceCuspVertex, frontier_subset_closure sourceCuspVertex_mem_frontier⟩ := by
    simpa [pole, sourceCuspCircle] using
      S.closureEquiv_boundaryPreimage sourceBoundedChamber_isOpen sourceCuspVertex
        sourceCuspVertex_mem_frontier
  rw [S.closureEquiv.apply_symm_apply, hpole] at himage
  exact hne (congrArg Subtype.val himage)

theorem sourceScalarClosureMap_continuousOn_away_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousOn (sourceScalarClosureMap S)
      (closure sourceBoundedChamber \ {sourceCuspVertex}) := by
  have hout := (scalarTriangleDiscMap_differentiableOn_ne_pole
    (sourceCuspCircle S) (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S)
    (sourceOrderThreeCircle_ne_cusp S) (sourceOtherEllipticCircle_ne_cusp S)
    (sourceOrderThreeCircle_ne_otherElliptic S)).continuousOn
  exact hout.comp (chamberClosureDiscInverse_continuousOn S |>.mono diff_subset)
    (fun q hq ↦ chamberClosureDiscInverse_ne_sourceCuspCircle S hq.1 (by simpa using hq.2))

def sourceScalarOpenChamberMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℂ → ℂ :=
  sourceScalarBoundedChamberMap S ∘ cuspExponential (1 + Real.sqrt 2)

/-- The boundary-aware scalar seed pulled back to the original upper-half-plane chamber. -/
def sourceScalarTriangleMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℂ → ℂ :=
  sourceScalarClosureMap S ∘ cuspExponential (1 + Real.sqrt 2)

theorem sourceScalarTriangleMap_eq_open_of_mem
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceOpenChamber) :
    sourceScalarTriangleMap S z = sourceScalarOpenChamberMap S z := by
  rw [sourceScalarTriangleMap, sourceScalarOpenChamberMap, Function.comp_apply,
    Function.comp_apply, sourceScalarClosureMap_eq_bounded_of_mem S]
  exact ⟨z, hz, rfl⟩

private theorem semicircleHeight_one_half :
    semicircleHeight (1 / 2 : ℝ) = Real.sqrt 3 / 2 := by
  rw [semicircleHeight, max_eq_right (by norm_num : (0 : ℝ) ≤ 1 - (1 / 2) ^ 2)]
  have h3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsnonneg : 0 ≤ Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) := Real.sqrt_nonneg _
  have hssq : (Real.sqrt (1 - (1 / 2 : ℝ) ^ 2)) ^ 2 =
      1 - (1 / 2 : ℝ) ^ 2 := Real.sq_sqrt (by norm_num)
  nlinarith

private theorem semicircleHeight_neg_sqrt_two_half :
    semicircleHeight (-Real.sqrt 2 / 2) = Real.sqrt 2 / 2 := by
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [semicircleHeight, max_eq_right]
  · have hsnonneg : 0 ≤ Real.sqrt (1 - (-Real.sqrt 2 / 2) ^ 2) := Real.sqrt_nonneg _
    have hssq : (Real.sqrt (1 - (-Real.sqrt 2 / 2) ^ 2)) ^ 2 =
        1 - (-Real.sqrt 2 / 2) ^ 2 := Real.sq_sqrt (by nlinarith)
    nlinarith
  · nlinarith

theorem cuspExponential_fuchsianOneFixedPoint :
    cuspExponential (1 + Real.sqrt 2) (fuchsianOneFixedPoint : ℂ) =
      sourceOrderThreeVertex := by
  rw [sourceOrderThreeVertex, cuspPolar]
  simp only [Complex.ofReal_one, one_mul]
  congr 1
  apply Complex.ext
  · norm_num [fuchsianOneFixedPoint]
  · simpa [fuchsianOneFixedPoint] using semicircleHeight_one_half.symm

theorem cuspExponential_fuchsianTwoFixedPoint :
    cuspExponential (1 + Real.sqrt 2) (fuchsianTwoFixedPoint : ℂ) =
      sourceOtherEllipticVertex := by
  rw [sourceOtherEllipticVertex, cuspPolar]
  simp only [Complex.ofReal_one, one_mul]
  congr 1
  apply Complex.ext
  · simp [fuchsianTwoFixedPoint]
  · simp [fuchsianTwoFixedPoint, semicircleHeight_neg_sqrt_two_half]

theorem sourceScalarTriangleMap_fuchsianOne
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceScalarTriangleMap S fuchsianOneFixedPoint = 0 := by
  rw [sourceScalarTriangleMap, Function.comp_apply,
    cuspExponential_fuchsianOneFixedPoint, sourceScalarClosureMap_orderThree]

theorem sourceScalarTriangleMap_fuchsianTwo
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceScalarTriangleMap S fuchsianTwoFixedPoint = 1 := by
  rw [sourceScalarTriangleMap, Function.comp_apply,
    cuspExponential_fuchsianTwoFixedPoint, sourceScalarClosureMap_otherElliptic]

theorem sourceScalarOpenChamberMap_bijOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hfinite : sourceOrderThreeCircle S ≠ sourceOtherEllipticCircle S) :
    BijOn (sourceScalarOpenChamberMap S) sourceOpenChamber
      (signedHalfPlane (scalarTriangleDenominator (sourceCuspCircle S)
        (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S))) := by
  exact (scalarTriangleDiscMap_bijOn _ _ _
      (sourceOrderThreeCircle_ne_cusp S) (sourceOtherEllipticCircle_ne_cusp S) hfinite).comp
    (sourceSeed_invFunOn_bijOn_scalar S |>.comp
      (by rw [sourceBoundedChamber]; exact source_cuspExponential_injOn.bijOn_image))

theorem sourceScalarOpenChamberMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hfinite : sourceOrderThreeCircle S ≠ sourceOtherEllipticCircle S) :
    DifferentiableOn ℂ (sourceScalarOpenChamberMap S) sourceOpenChamber := by
  have hexp : DifferentiableOn ℂ (cuspExponential (1 + Real.sqrt 2)) sourceOpenChamber :=
    (cuspExponential_differentiable _ (by positivity)).differentiableOn
  have hInv : DifferentiableOn ℂ
      (Function.invFunOn S.map (ball (0 : ℂ) 1)) sourceBoundedChamber := by
    have h := TauCeti.DifferentiableOn.invFunOn
      S.differentiableOn isOpen_ball S.bijOn.injOn
    rwa [S.bijOn.image_eq] at h
  have hmiddle := hInv.comp hexp (by
    rw [sourceBoundedChamber]
    exact fun z hz ↦ ⟨z, hz, rfl⟩)
  exact (scalarTriangleDiscMap_differentiableOn _ _ _
      (sourceOrderThreeCircle_ne_cusp S) (sourceOtherEllipticCircle_ne_cusp S) hfinite).comp
    hmiddle ((sourceSeed_invFunOn_bijOn_scalar S).mapsTo.comp (by
      rw [sourceBoundedChamber]
      exact fun z hz ↦ ⟨z, hz, rfl⟩))


end SphereSixComplex.Periods.SourceChamberTopology
