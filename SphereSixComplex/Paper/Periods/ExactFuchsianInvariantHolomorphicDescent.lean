module

public import SphereSixComplex.Prerequisites.Periods.Uniformization.EstablishedExactFuchsianOrbifoldCoordinate
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
import all SphereSixComplex.Paper.Periods.FuchsianModularLift.Ramification

/-!
# Holomorphic descent through the exact Fuchsian quotient

The exact quotient is a local homeomorphism away from its two branch values.  A holomorphic
invariant source function therefore descends holomorphically there by the complex inverse
function theorem.  Continuity of the descended function then removes both branch singularities.
-/

open Filter Set
open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

public theorem ExactFuchsianOrbifoldCoordinate.differentiableAt_of_mdifferentiableAt_comp_regular
    (C : ExactFuchsianOrbifoldCoordinate) (F : ℂ → ℂ) (z : UpperHalfPlane)
    (hf : MDiffAt (F ∘ C.coordinate) z)
    (hzregular : C.coordinate z ∈ ({0, 1} : Set ℂ)ᶜ) :
    DifferentiableAt ℂ F (C.coordinate z) := by
  let f := F ∘ C.coordinate
  obtain ⟨e, hze, he⟩ := C.regular_covering.isLocalHomeomorphOn z hzregular
  let φ : ℂ → ℂ := C.coordinate ∘ UpperHalfPlane.ofComplex
  have hφdiff : DifferentiableOn ℂ φ UpperHalfPlane.upperHalfPlaneSet := by
    intro w hw
    let zw : UpperHalfPlane := ⟨w, hw⟩
    have hcoord : DifferentiableAt ℂ (C.coordinate ∘ UpperHalfPlane.ofComplex) (zw : ℂ) :=
      UpperHalfPlane.mdifferentiableAt_iff.mp (C.coordinate_holomorphic zw)
    simpa only [φ, zw] using hcoord.differentiableWithinAt
  have hφanalytic : AnalyticAt ℂ φ (z : ℂ) :=
    hφdiff.analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hofcont : ContinuousAt UpperHalfPlane.ofComplex (z : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_ofComplex z.im_pos).continuousAt
  have hsource : UpperHalfPlane.ofComplex ⁻¹' e.source ∈ nhds (z : ℂ) :=
    hofcont (e.open_source.mem_nhds (by simpa using hze))
  have hupper : UpperHalfPlane.upperHalfPlaneSet ∈ nhds (z : ℂ) :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp (inter_mem hupper hsource)
  have hφinj : U.InjOn φ := by
    intro x hx y hy hxy
    have hxupper : x ∈ UpperHalfPlane.upperHalfPlaneSet := (hUsub hx).1
    have hyupper : y ∈ UpperHalfPlane.upperHalfPlaneSet := (hUsub hy).1
    have hxsource : UpperHalfPlane.ofComplex x ∈ e.source := (hUsub hx).2
    have hysource : UpperHalfPlane.ofComplex y ∈ e.source := (hUsub hy).2
    have hexy : e (UpperHalfPlane.ofComplex x) = e (UpperHalfPlane.ofComplex y) := by
      rw [← he]
      simpa only [φ, Function.comp_apply] using hxy
    have hofeq := e.injOn hxsource hysource hexy
    have hxcoe := congrArg ((↑) : UpperHalfPlane → ℂ)
      (UpperHalfPlane.ofComplex_apply_of_im_pos hxupper)
    have hycoe := congrArg ((↑) : UpperHalfPlane → ℂ)
      (UpperHalfPlane.ofComplex_apply_of_im_pos hyupper)
    calc
      x = (UpperHalfPlane.ofComplex x : ℂ) := hxcoe.symm
      _ = (UpperHalfPlane.ofComplex y : ℂ) := congrArg ((↑) : UpperHalfPlane → ℂ) hofeq
      _ = y := hycoe
  have hφderiv : deriv φ (z : ℂ) ≠ 0 :=
    AnalyticLocalHomeo.AnalyticAt.deriv_ne_zero_of_exists_open_injOn hφanalytic
      ⟨U, hUopen, hzU, hφinj⟩
  let ψ : ℂ → ℂ := hφanalytic.hasStrictDerivAt.localInverse φ
    (deriv φ (z : ℂ)) (z : ℂ) hφderiv
  have hψanalytic : AnalyticAt ℂ ψ (φ (z : ℂ)) := by
    simpa only [ψ] using hφanalytic.analyticAt_localInverse hφderiv
  have hψvalue : ψ (φ (z : ℂ)) = (z : ℂ) := by
    simp [ψ]
  have hright : ∀ᶠ w in nhds (φ (z : ℂ)), φ (ψ w) = w := by
    simpa only [ψ] using hφanalytic.hasStrictDerivAt.eventually_right_inverse hφderiv
  have hfof : DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp hf
  have hlocal : DifferentiableAt ℂ ((f ∘ UpperHalfPlane.ofComplex) ∘ ψ)
      (φ (z : ℂ)) := by
    have hfof' : DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) (ψ (φ (z : ℂ))) := by
      rwa [hψvalue]
    exact hfof'.comp (φ (z : ℂ)) hψanalytic.differentiableAt
  have heventual : F =ᶠ[nhds (φ (z : ℂ))] (f ∘ UpperHalfPlane.ofComplex) ∘ ψ := by
    filter_upwards [hright] with w hwright
    exact congrArg F hwright.symm
  have hφz : φ (z : ℂ) = C.coordinate z := by
    simp [φ]
  rw [hφz] at hlocal heventual
  exact hlocal.congr_of_eventuallyEq heventual

public theorem ExactFuchsianOrbifoldCoordinate.exists_regular_holomorphic_descent
    (C : ExactFuchsianOrbifoldCoordinate) {W : Set ℂ} (hW : IsOpen W)
    (hregular : W ⊆ ({0, 1} : Set ℂ)ᶜ) (f : UpperHalfPlane → ℂ)
    (hf : ∀ z, C.coordinate z ∈ W → MDiffAt f z)
    (hinvariant : ∀ g z, C.coordinate z ∈ W → f (fuchsianSourceAction g • z) = f z) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F W ∧
      ∀ z, C.coordinate z ∈ W → F (C.coordinate z) = f z := by
  classical
  let lift (q : ℂ) := (C.coordinate_isQuotientMap.surjective q).choose
  have hlift (q : ℂ) : C.coordinate (lift q) = q :=
    (C.coordinate_isQuotientMap.surjective q).choose_spec
  let F := f ∘ lift
  have hcomp (z : UpperHalfPlane) (hz : C.coordinate z ∈ W) :
      F (C.coordinate z) = f z := by
    obtain ⟨g, hg⟩ := (C.coordinate_eq_iff_orbit z (lift (C.coordinate z))).mp
      (hlift _).symm
    change f (lift (C.coordinate z)) = f z
    rw [← hg]
    exact hinvariant g z hz
  refine ⟨F, ?_, hcomp⟩
  intro q hq
  let z := lift q
  have hzq : C.coordinate z = q := hlift q
  have hz : C.coordinate z ∈ W := hzq ▸ hq
  have hlocal : MDiffAt (F ∘ C.coordinate) z := by
    apply (hf z hz).congr_of_eventuallyEq
    have hn := C.coordinate_holomorphic.continuous.continuousAt (hW.mem_nhds hz)
    filter_upwards [hn] with w hw
    exact hcomp w hw
  have hd := C.differentiableAt_of_mdifferentiableAt_comp_regular F z hlocal
    (hregular hz)
  rw [hzq] at hd
  exact hd.differentiableWithinAt





end SphereSixComplex.Periods
