module

public import SphereSixComplex.Periods.Uniformization.ScalarSeedInjective
import all SphereSixComplex.Periods.Uniformization.ScalarSeedInjective

@[expose] public section

/-!
# Real boundary values of the scalar chamber coordinate

The normalized Cayley map sends the unit circle minus its pole bijectively to the real line.
Transporting this through the Carathéodory closure homeomorphism shows that every finite real
value occurs exactly on the finite frontier of the bounded source chamber.  This is the boundary
piece of surjectivity for the doubled fundamental region.
-/

open Complex Metric Set Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

/-- Every real scalar value has a unique finite preimage on the unit circle.  Only existence and
exclusion of the Cayley pole are packaged here. -/
theorem exists_circle_scalarTriangleDiscMap_eq_real
    (pole first second : Circle)
    (hfirst : first ≠ pole) (hsecond : second ≠ pole) (hfinite : first ≠ second)
    (x : ℝ) :
    ∃ u : Circle, u ≠ pole ∧ scalarTriangleDiscMap pole first second u = (x : ℂ) := by
  let a : ℝ := circleCayleyCoord pole first
  let d : ℝ := scalarTriangleDenominator pole first second
  let w : ℂ := (a : ℂ) + (d : ℂ) * (x : ℂ)
  have hwim : w.im = 0 := by simp [w]
  have hwadd : w + I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [Complex.add_im, hwim, I_im] at him
    norm_num at him
  have hwnegI : w ≠ -I := by
    simpa [eq_neg_iff_add_eq_zero] using hwadd
  let u : ℂ := boundaryCayleyInv pole w
  have hnormparts : ‖w - I‖ = ‖w + I‖ := by
    have hsq : ‖w - I‖ ^ 2 = ‖w + I‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.sub_re, I_re, sub_zero,
        Complex.sub_im, I_im, Complex.add_re, add_zero, Complex.add_im, hwim]
      ring
    nlinarith [norm_nonneg (w - I), norm_nonneg (w + I)]
  have hnorm : ‖u‖ = 1 := by
    dsimp [u, boundaryCayleyInv]
    rw [norm_div, norm_mul, Circle.norm_coe, one_mul,
      hnormparts, div_self]
    exact norm_ne_zero_iff.mpr hwadd
  let uc : Circle := ⟨u,
    (show u ∈ sphere 0 1 from mem_sphere_zero_iff_norm.mpr hnorm)⟩
  have hucne : uc ≠ pole := by
    intro heq
    have hueq : u = (pole : ℂ) := congrArg ((↑) : Circle → ℂ) heq
    have hparts : w - I = w + I := by
      dsimp [u, boundaryCayleyInv] at hueq
      field_simp [hwadd] at hueq
      exact hueq
    have him := congrArg Complex.im hparts
    norm_num [w] at him
  refine ⟨uc, hucne, ?_⟩
  have hcayley : boundaryCayley pole u = w := by
    exact boundaryCayley_boundaryCayleyInv pole.coe_ne_zero hwnegI
  have hdR : d ≠ 0 := by
    exact scalarTriangleDenominator_ne_zero hfirst hsecond hfinite
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast hdR
  rw [scalarTriangleDiscMap, show (uc : ℂ) = u by rfl, hcayley]
  dsimp [w, a, d]
  apply (div_eq_iff hd).2
  ring

private theorem closureEquiv_circle_mem_frontier {Omega : Set ℂ}
    (S : ChamberCaratheodorySeed Omega) (hOmega : IsOpen Omega) (u : Circle) :
    (S.closureEquiv
      ⟨u, by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ : ℂ) ∈ frontier Omega := by
  let ub : closedBall (0 : ℂ) 1 :=
    ⟨u, by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩
  let q : closure Omega := S.closureEquiv ub
  have hqnot : (q : ℂ) ∉ Omega := by
    intro hq
    obtain ⟨v, hv, hvq⟩ := S.bijOn.surjOn hq
    let vb : closedBall (0 : ℂ) 1 := ⟨v, ball_subset_closedBall hv⟩
    have heq : ub = vb := by
      apply S.closureEquiv.injective
      apply Subtype.ext
      simpa [q, vb, S.closureEquiv_apply] using hvq.symm
    have hcoe := congrArg (fun y : closedBall (0 : ℂ) 1 ↦ (y : ℂ)) heq
    have hnormEq : (1 : ℝ) = ‖v‖ := by
      simpa [ub, vb, Circle.norm_coe] using congrArg norm hcoe
    have hvnorm : ‖v‖ < 1 := by simpa [mem_ball_zero_iff] using hv
    exact (ne_of_gt hvnorm) hnormEq
  rw [hOmega.frontier_eq]
  exact ⟨q.2, hqnot⟩

/-- Every finite real value occurs on the source chamber frontier away from the completed cusp. -/
theorem exists_sourceFrontier_scalarClosureMap_eq_real
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (x : ℝ) :
    ∃ q : ℂ, q ∈ frontier sourceBoundedChamber ∧ q ≠ sourceCuspVertex ∧
      sourceScalarClosureMap S q = (x : ℂ) := by
  obtain ⟨u, hupole, huval⟩ := exists_circle_scalarTriangleDiscMap_eq_real
    (sourceCuspCircle S) (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S)
    (sourceOrderThreeCircle_ne_cusp S) (sourceOtherEllipticCircle_ne_cusp S)
    (sourceOrderThreeCircle_ne_otherElliptic S) x
  let ub : closedBall (0 : ℂ) 1 :=
    ⟨u, by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩
  let qs : closure sourceBoundedChamber := S.closureEquiv ub
  let q : ℂ := qs
  have hqfront : q ∈ frontier sourceBoundedChamber := by
    exact closureEquiv_circle_mem_frontier S sourceBoundedChamber_isOpen u
  have hqne : q ≠ sourceCuspVertex := by
    intro hq
    let pole : closedBall (0 : ℂ) 1 :=
      ⟨sourceCuspCircle S,
        by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩
    have hpole : S.closureEquiv pole =
        ⟨sourceCuspVertex, frontier_subset_closure sourceCuspVertex_mem_frontier⟩ := by
      simpa [pole, sourceCuspCircle] using
        S.closureEquiv_boundaryPreimage sourceBoundedChamber_isOpen sourceCuspVertex
          sourceCuspVertex_mem_frontier
    have heq : S.closureEquiv ub = S.closureEquiv pole := by
      rw [hpole]
      apply Subtype.ext
      simpa [q, qs] using hq
    have hubpole := S.closureEquiv.injective heq
    exact hupole (Circle.coe_injective
      (congrArg (fun y : closedBall (0 : ℂ) 1 ↦ (y : ℂ)) hubpole))
  refine ⟨q, hqfront, hqne, ?_⟩
  have hinv : chamberClosureDiscInverse S q = (u : ℂ) := by
    rw [chamberClosureDiscInverse_apply_of_mem S qs.2]
    have hsymm : S.closureEquiv.symm qs = ub := S.closureEquiv.symm_apply_apply ub
    exact congrArg Subtype.val hsymm
  rw [sourceScalarClosureMap, Function.comp_apply, hinv]
  exact huval


end SphereSixComplex.Periods.SourceChamberTopology
