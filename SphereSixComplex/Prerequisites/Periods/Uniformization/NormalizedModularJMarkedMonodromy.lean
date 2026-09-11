module

public import SphereSixComplex.Prerequisites.Periods.Uniformization.GlobalModularDeckComparison
import all SphereSixComplex.Prerequisites.Periods.Uniformization.GlobalModularDeckComparison
public import SphereSixComplex.Prerequisites.Periods.Uniformization.FiniteCornerReflection
import all SphereSixComplex.Prerequisites.Periods.Uniformization.FiniteCornerReflection
import all SphereSixComplex.Prerequisites.Periods.FuchsianModularParameter

@[expose] public section

/-!
# From marked local modular-J germs to the normalized global lift

This file isolates the last purely global step in the normalized modular-J lifting theorem.
Once the two desired generator identities are known as germs at any two points of the upper
half-plane, holomorphicity and the identity theorem promote them to global identities.  The
result then packages the global solution as `NormalizedFuchsianModularJLift`.

The local hypotheses are intentionally stated for the ambient-complex representatives.  This is
the form produced by local power charts and by Tau Ceti's branched-power action lemma.
-/

noncomputable section

namespace SphereSixComplex.Periods.NormalizedModularJMarkedMonodromy

open Complex Filter Set Topology UpperHalfPlane
open scoped Manifold
open SphereSixComplex.TriangleGroup
open GlobalModularDeckComparison
open SolutionGermDeckTransitivity

/-- A local ambient-complex generator identity between holomorphic upper-half-plane maps extends
to the whole upper half-plane. -/
theorem fuchsianTauEquivariant_of_eventuallyEq
    (tau : UpperHalfPlane → UpperHalfPlane) (htau : MDiff tau)
    (g : Delta) (z₀ : UpperHalfPlane)
    (hlocal :
      (fun w : ℂ ↦
        (tau (fuchsianSourceAction g • UpperHalfPlane.ofComplex w) : ℂ))
        =ᶠ[nhds (z₀ : ℂ)]
      (fun w : ℂ ↦
        ((rhoTauReal g • tau (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ))) :
    FuchsianTauEquivariant tau g := by
  have hsource : MDiff (fun z : UpperHalfPlane ↦ fuchsianSourceAction g • z) :=
    (fuchsianSourceAction_contMDiff g 1).mdifferentiable (by norm_num)
  have hleftMD : MDiff
      (fun z : UpperHalfPlane ↦ tau (fuchsianSourceAction g • z)) :=
    htau.comp hsource
  have htarget : MDiff (fun z : UpperHalfPlane ↦ rhoTauReal g • z) :=
    UpperHalfPlane.mdifferentiable_smul (by simp [rhoTauReal, modularToReal])
  have hrightMD : MDiff
      (fun z : UpperHalfPlane ↦ rhoTauReal g • tau z) :=
    htarget.comp htau
  have hleft : AnalyticOnNhd ℂ
      (fun w : ℂ ↦
        (tau (fuchsianSourceAction g • UpperHalfPlane.ofComplex w) : ℂ))
      UpperHalfPlane.upperHalfPlaneSet :=
    coe_comp_ofComplex_analyticOnNhd hleftMD
  have hright : AnalyticOnNhd ℂ
      (fun w : ℂ ↦
        ((rhoTauReal g • tau (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ))
      UpperHalfPlane.upperHalfPlaneSet :=
    coe_comp_ofComplex_analyticOnNhd hrightMD
  have hglobal := hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (convex_halfSpace_im_gt 0).isPreconnected z₀.im_pos hlocal
  intro z
  apply UpperHalfPlane.coe_injective
  have hz := hglobal (x := (z : ℂ)) z.im_pos
  simpa only [UpperHalfPlane.ofComplex_apply] using hz

/-- Package a global normalized modular-J solution once its two generator laws are known as
local germs. -/
def normalizedLiftOfLocalGeneratorGerms
    (C : ExactFuchsianOrbifoldCoordinate)
    (tau : UpperHalfPlane → UpperHalfPlane)
    (htau : MDiff tau)
    (hJ : ∀ z, normalizedJ (tau z) = 1728 * C.coordinate z)
    (z₁ z₂ : UpperHalfPlane)
    (hone :
      (fun w : ℂ ↦
        (tau (fuchsianSourceAction g₁ • UpperHalfPlane.ofComplex w) : ℂ))
        =ᶠ[nhds (z₁ : ℂ)]
      (fun w : ℂ ↦
        ((rhoTauReal g₁ • tau (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ)))
    (htwo :
      (fun w : ℂ ↦
        (tau (fuchsianSourceAction g₂ • UpperHalfPlane.ofComplex w) : ℂ))
        =ᶠ[nhds (z₂ : ℂ)]
      (fun w : ℂ ↦
        ((rhoTauReal g₂ • tau (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ))) :
    NormalizedFuchsianModularJLift C.toFuchsianOrbifoldCoordinate where
  tau := tau
  tau_holomorphic := htau
  modularJ_equation := hJ
  monodromy_one := fuchsianTauEquivariant_of_eventuallyEq tau htau g₁ z₁ hone
  monodromy_two := fuchsianTauEquivariant_of_eventuallyEq tau htau g₂ z₂ htwo

/-- Existence wrapper for the final local-to-global assembly. -/
theorem nonempty_normalizedLift_of_local_generator_germs
    (C : ExactFuchsianOrbifoldCoordinate)
    (tau : UpperHalfPlane → UpperHalfPlane)
    (htau : MDiff tau)
    (hJ : ∀ z, normalizedJ (tau z) = 1728 * C.coordinate z)
    (z₁ z₂ : UpperHalfPlane)
    (hone :
      (fun w : ℂ ↦
        (tau (fuchsianSourceAction g₁ • UpperHalfPlane.ofComplex w) : ℂ))
        =ᶠ[nhds (z₁ : ℂ)]
      (fun w : ℂ ↦
        ((rhoTauReal g₁ • tau (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ)))
    (htwo :
      (fun w : ℂ ↦
        (tau (fuchsianSourceAction g₂ • UpperHalfPlane.ofComplex w) : ℂ))
        =ᶠ[nhds (z₂ : ℂ)]
      (fun w : ℂ ↦
        ((rhoTauReal g₂ • tau (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ))) :
    Nonempty (NormalizedFuchsianModularJLift C.toFuchsianOrbifoldCoordinate) :=
  ⟨normalizedLiftOfLocalGeneratorGerms C tau htau hJ z₁ z₂ hone htwo⟩







end SphereSixComplex.Periods.NormalizedModularJMarkedMonodromy
