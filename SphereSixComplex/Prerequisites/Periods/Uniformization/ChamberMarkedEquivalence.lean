module

public import SphereSixComplex.Prerequisites.Periods.Uniformization.ChamberCaratheodory
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ChamberCaratheodory
public import SphereSixComplex.Prerequisites.Periods.Uniformization.DiscBoundaryTriple
import SphereSixComplex.Prerequisites.Periods.Uniformization.DiscBoundaryTriple
import all SphereSixComplex.Prerequisites.Periods.Uniformization.DiscBoundaryTriple

@[expose] public section

open Complex Metric Set Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

-- Pin the canonical complex normed-space instance.  `UpperHalfPlane.Basic`, imported by the
-- Cayley-coordinate file, also exposes the scalar-self module instance and otherwise leaves a
-- downstream instance diamond in `DifferentiableOn.comp`.

/-! ## Closed-disc Riemann-map seeds and their marked boundary preimages -/

/-- A Riemann map together with its Carathéodory homeomorphism of closures. -/
structure ChamberCaratheodorySeed (Ω : Set ℂ) where
  map : ℂ → ℂ
  closureEquiv : closedBall (0 : ℂ) 1 ≃ₜ closure Ω
  differentiableOn : DifferentiableOn ℂ map (ball 0 1)
  bijOn : BijOn map (ball 0 1) Ω
  closureEquiv_apply : ∀ z, (closureEquiv z : ℂ) = map z

theorem exists_sourceChamberCaratheodorySeed :
    Nonempty (ChamberCaratheodorySeed sourceBoundedChamber) := by
  obtain ⟨g, e, hgd, hgbij, he⟩ := exists_sourceChamber_closureHomeomorph
  exact ⟨⟨g, e, hgd, hgbij, he⟩⟩


/-- The circle point at which a closed-disc Riemann-map seed takes a prescribed frontier value. -/
def ChamberCaratheodorySeed.boundaryPreimage {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) (hΩo : IsOpen Ω) (v : ℂ)
    (hv : v ∈ frontier Ω) : Circle := by
  let z : closedBall (0 : ℂ) 1 := S.closureEquiv.symm ⟨v, frontier_subset_closure hv⟩
  have hzle : ‖(z : ℂ)‖ ≤ 1 := by
    have hzdist : dist (z : ℂ) 0 ≤ 1 := mem_closedBall.mp z.2
    simpa only [dist_zero_right] using hzdist
  have hnorm : ‖(z : ℂ)‖ = 1 := by
    apply le_antisymm hzle
    by_contra hnot
    have hzlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hnot
    have hzball : (z : ℂ) ∈ ball (0 : ℂ) 1 := by
      exact mem_ball.mpr (by simpa only [dist_zero_right] using hzlt)
    have hmap : S.map z ∈ Ω := S.bijOn.mapsTo hzball
    have heq : S.map z = v := by
      rw [← S.closureEquiv_apply z]
      exact congrArg Subtype.val
        (S.closureEquiv.apply_symm_apply ⟨v, frontier_subset_closure hv⟩)
    exact (hΩo.frontier_eq.subset hv).2 (heq ▸ hmap)
  exact ⟨z, (show (z : ℂ) ∈ sphere 0 1 from mem_sphere_zero_iff_norm.mpr hnorm)⟩

theorem ChamberCaratheodorySeed.coe_boundaryPreimage {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) (hΩo : IsOpen Ω) (v : ℂ)
    (hv : v ∈ frontier Ω) :
    (S.boundaryPreimage hΩo v hv : ℂ) =
      (S.closureEquiv.symm ⟨v, frontier_subset_closure hv⟩ : ℂ) := by
  unfold boundaryPreimage
  rfl

theorem ChamberCaratheodorySeed.closureEquiv_boundaryPreimage {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) (hΩo : IsOpen Ω) (v : ℂ)
    (hv : v ∈ frontier Ω) :
    S.closureEquiv
      ⟨S.boundaryPreimage hΩo v hv,
        by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ =
      ⟨v, frontier_subset_closure hv⟩ := by
  apply Subtype.ext
  simp only [ChamberCaratheodorySeed.coe_boundaryPreimage]
  exact congrArg Subtype.val
    (S.closureEquiv.apply_symm_apply ⟨v, frontier_subset_closure hv⟩)

theorem ChamberCaratheodorySeed.boundaryPreimage_ne {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) (hΩo : IsOpen Ω)
    {v w : ℂ} (hv : v ∈ frontier Ω) (hw : w ∈ frontier Ω) (hvw : v ≠ w) :
    S.boundaryPreimage hΩo v hv ≠ S.boundaryPreimage hΩo w hw := by
  intro h
  apply hvw
  have hcoe : (S.boundaryPreimage hΩo v hv : ℂ) =
      (S.boundaryPreimage hΩo w hw : ℂ) := congrArg (fun z : Circle ↦ (z : ℂ)) h
  have hclosed :
      (⟨S.boundaryPreimage hΩo v hv,
          by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ :
          closedBall (0 : ℂ) 1) =
        ⟨S.boundaryPreimage hΩo w hw,
          by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ := Subtype.ext hcoe
  have he := congrArg S.closureEquiv hclosed
  rw [S.closureEquiv_boundaryPreimage hΩo v hv,
    S.closureEquiv_boundaryPreimage hΩo w hw] at he
  exact congrArg Subtype.val he

/-! ## The three distinguished vertices -/

def sourceCuspVertex : ℂ := 0

/-- The source order-three vertex, at the right endpoint of the circular side. -/
def sourceOrderThreeVertex : ℂ :=
  cuspPolar (1 + Real.sqrt 2) semicircleHeight ((1 / 2 : ℝ), 1)

/-- The source order-four vertex, at the left endpoint of the circular side. -/
def sourceOtherEllipticVertex : ℂ :=
  cuspPolar (1 + Real.sqrt 2) semicircleHeight (-Real.sqrt 2 / 2, 1)




theorem sourceCuspVertex_mem_frontier : sourceCuspVertex ∈ frontier sourceBoundedChamber := by
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨(-Real.sqrt 2 / 2, 0), ?_, by simp [sourceCuspVertex, cuspPolar]⟩
  apply (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) _).2
  exact ⟨⟨⟨le_rfl, by
    have hs := Real.sqrt_nonneg 2
    linarith⟩, le_rfl, zero_le_one⟩, Or.inl rfl⟩

theorem sourceOrderThreeVertex_mem_frontier :
    sourceOrderThreeVertex ∈ frontier sourceBoundedChamber := by
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨((1 / 2 : ℝ), 1), ?_, rfl⟩
  apply (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) _).2
  exact ⟨⟨⟨by
    have hs := Real.sqrt_nonneg 2
    linarith, le_rfl⟩, zero_le_one, le_rfl⟩, Or.inr (Or.inl rfl)⟩

theorem sourceOtherEllipticVertex_mem_frontier :
    sourceOtherEllipticVertex ∈ frontier sourceBoundedChamber := by
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨(-Real.sqrt 2 / 2, 1), ?_, rfl⟩
  apply (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) _).2
  exact ⟨⟨⟨le_rfl, by
    have hs := Real.sqrt_nonneg 2
    linarith⟩, zero_le_one, le_rfl⟩, Or.inl rfl⟩




theorem sourceCuspVertex_ne_orderThree : sourceCuspVertex ≠ sourceOrderThreeVertex := by
  rw [sourceCuspVertex, sourceOrderThreeVertex, cuspPolar]
  simpa only [Complex.ofReal_one, one_mul] using (cuspExponential_ne_zero
    (1 + Real.sqrt 2) ((1 / 2 : ℝ) + (semicircleHeight (1 / 2) : ℂ) * I)).symm

theorem sourceCuspVertex_ne_otherElliptic :
    sourceCuspVertex ≠ sourceOtherEllipticVertex := by
  rw [sourceCuspVertex, sourceOtherEllipticVertex, cuspPolar]
  simpa only [Complex.ofReal_one, one_mul] using (cuspExponential_ne_zero
    (1 + Real.sqrt 2)
      ((-Real.sqrt 2 / 2 : ℝ) + (semicircleHeight (-Real.sqrt 2 / 2) : ℂ) * I)).symm



theorem sourceOrderThreeVertex_ne_otherElliptic :
    sourceOrderThreeVertex ≠ sourceOtherEllipticVertex := by
  intro h
  have hlr : -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) := by
    have hs := Real.sqrt_nonneg 2
    linarith
  have hp := cuspPolar_injOn_positiveClosedCuspStrip
    (show (1 + Real.sqrt 2 : ℝ) ≠ 0 by positivity) semicircleHeight
    source_cuspExponential_injOn_closedStrip
    (show ((1 / 2 : ℝ), 1) ∈
      positiveClosedCuspStrip (-Real.sqrt 2 / 2) (1 / 2) from
        ⟨hlr, le_rfl, one_pos⟩)
    (show (-Real.sqrt 2 / 2, (1 : ℝ)) ∈
      positiveClosedCuspStrip (-Real.sqrt 2 / 2) (1 / 2) from
        ⟨le_rfl, hlr, one_pos⟩)
    (by simpa only [sourceOrderThreeVertex, sourceOtherEllipticVertex] using h)
  have hx := congrArg Prod.fst hp
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  norm_num only [Prod.fst] at hx
  nlinarith


/-! ## The marked triples selected by a pair of Carathéodory seeds -/

def sourceCuspCircle (S : ChamberCaratheodorySeed sourceBoundedChamber) : Circle :=
  S.boundaryPreimage sourceBoundedChamber_isOpen sourceCuspVertex
    sourceCuspVertex_mem_frontier

def sourceOrderThreeCircle (S : ChamberCaratheodorySeed sourceBoundedChamber) : Circle :=
  S.boundaryPreimage sourceBoundedChamber_isOpen sourceOrderThreeVertex
    sourceOrderThreeVertex_mem_frontier

def sourceOtherEllipticCircle (S : ChamberCaratheodorySeed sourceBoundedChamber) : Circle :=
  S.boundaryPreimage sourceBoundedChamber_isOpen sourceOtherEllipticVertex
    sourceOtherEllipticVertex_mem_frontier




theorem sourceOrderThreeCircle_ne_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceOrderThreeCircle S ≠ sourceCuspCircle S :=
  S.boundaryPreimage_ne sourceBoundedChamber_isOpen
    sourceOrderThreeVertex_mem_frontier sourceCuspVertex_mem_frontier
    sourceCuspVertex_ne_orderThree.symm

theorem sourceOtherEllipticCircle_ne_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceOtherEllipticCircle S ≠ sourceCuspCircle S :=
  S.boundaryPreimage_ne sourceBoundedChamber_isOpen
    sourceOtherEllipticVertex_mem_frontier sourceCuspVertex_mem_frontier
    sourceCuspVertex_ne_otherElliptic.symm



theorem sourceOrderThreeCircle_ne_otherElliptic
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceOrderThreeCircle S ≠ sourceOtherEllipticCircle S :=
  S.boundaryPreimage_ne sourceBoundedChamber_isOpen
    sourceOrderThreeVertex_mem_frontier sourceOtherEllipticVertex_mem_frontier
    sourceOrderThreeVertex_ne_otherElliptic











/-! ## The induced marked biholomorphism of the open chambers -/







/-! ## Lifting the bounded equivalence back to the original open chambers -/










/-! An orientation-free seed is also useful: it provides the biholomorphic open-chamber map while
deliberately making no claim about which elliptic vertex is reached. -/









/-! ## Closure packaging -/









/-! The rational closed-disc theorem discharges the two auxiliary closure hypotheses. -/







end SphereSixComplex.Periods.SourceChamberTopology
