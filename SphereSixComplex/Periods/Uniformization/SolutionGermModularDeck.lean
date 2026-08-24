module

public import SphereSixComplex.Periods.Uniformization.SolutionGermDeckTransitivity
import all SphereSixComplex.Periods.Uniformization.SolutionGermDeckTransitivity

@[expose] public section

/-!
# Modular deck transformations on the solution-germ étalé space

This file packages postcomposition by the modular action on the upper half-plane as an honest
homeomorphism of the étalé space of local solutions.  The definition uses an arbitrary
upper-half-plane representative carried by each solution germ; equality of holomorphic germs
makes the result independent of that representative.
-/

noncomputable section

namespace SphereSixComplex.Periods.SolutionGermModularDeck

open Filter Metric Set Topology UpperHalfPlane
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods.SolutionGermDeckTransitivity
open TauCeti

variable {C : ℂ → ℂ} {U : Set ℂ}

abbrev ModularSolutionEtale (C : ℂ → ℂ) (U : Set ℂ) :=
  UpperHalfPlaneSolutionEtale normalizedModularJCoordinate C U

/-- A chosen upper-half-plane-valued representative of a modular solution germ. -/
def solutionRepresentative (p : ModularSolutionEtale C U) : ℂ → UpperHalfPlane :=
  p.2.2.choose

theorem solutionRepresentative_coe_eventuallyEq
    (p : ModularSolutionEtale C U) :
    (fun w ↦ (solutionRepresentative p w : ℂ)) =ᶠ[𝓝 p.1.base]
      HolomorphicPresheaf.repFun p.1 :=
  p.2.2.choose_spec.1

theorem solutionRepresentative_equation_eventuallyEq
    (p : ModularSolutionEtale C U) :
    (fun w ↦ normalizedModularJCoordinate (solutionRepresentative p w)) =ᶠ[𝓝 p.1.base]
      C :=
  p.2.2.choose_spec.2

/-- The complex representative obtained by postcomposing a solution representative with a
modular deck transformation. -/
def modularTransformRepresentative (g : Delta) (p : ModularSolutionEtale C U) : ℂ → ℂ :=
  fun w ↦ (modularDeckHomeomorph g (solutionRepresentative p w) : ℂ)

theorem analyticAt_modularTransformRepresentative (g : Delta)
    (p : ModularSolutionEtale C U) :
    AnalyticAt ℂ (modularTransformRepresentative g p) p.1.base := by
  apply analyticAt_modularDeck_coe g
  exact (HolomorphicPresheaf.analyticAt_repFun p.1).congr
    (solutionRepresentative_coe_eventuallyEq p).symm

/-- The underlying holomorphic germ obtained by a modular deck transformation. -/
def modularDeckEtalePoint (g : Delta) (p : ModularSolutionEtale C U) :
    (holomorphicPresheaf ℂ).EtaleSpace :=
  HolomorphicPresheaf.germPoint (modularTransformRepresentative g p) p.1.base

@[simp]
theorem modularDeckEtalePoint_base (g : Delta) (p : ModularSolutionEtale C U) :
    (modularDeckEtalePoint g p).base = p.1.base := rfl

theorem modularDeckEtalePoint_repFun_eventuallyEq (g : Delta)
    (p : ModularSolutionEtale C U) :
    HolomorphicPresheaf.repFun (modularDeckEtalePoint g p) =ᶠ[𝓝 p.1.base]
      modularTransformRepresentative g p := by
  apply (HolomorphicPresheaf.germAt_eq_iff
    (HolomorphicPresheaf.analyticAt_repFun (modularDeckEtalePoint g p))
    (analyticAt_modularTransformRepresentative g p)).mp
  rw [HolomorphicPresheaf.germAt_repFun]
  rfl

/-- Modular postcomposition preserves the local solution relation. -/
theorem modularDeckEtalePoint_isSolution (g : Delta)
    (p : ModularSolutionEtale C U) :
    IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate C p.1.base
      (HolomorphicPresheaf.repFun (modularDeckEtalePoint g p)) := by
  refine ⟨fun w ↦ modularDeckHomeomorph g (solutionRepresentative p w), ?_, ?_⟩
  · exact (modularDeckEtalePoint_repFun_eventuallyEq g p).symm
  · filter_upwards [solutionRepresentative_equation_eventuallyEq p] with w hw
    rw [normalizedModularJCoordinate_modularDeck]
    exact hw

/-- Modular postcomposition as a self-map of the solution-germ space. -/
def modularSolutionDeck (g : Delta) (p : ModularSolutionEtale C U) :
    ModularSolutionEtale C U :=
  ⟨modularDeckEtalePoint g p, p.2.1, modularDeckEtalePoint_isSolution g p⟩

@[simp]
theorem modularSolutionDeck_base (g : Delta) (p : ModularSolutionEtale C U) :
    upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate C U
      (modularSolutionDeck g p) =
    upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate C U p := by
  apply Subtype.ext
  rfl

/-- The inverse matrix acts by the inverse upper-half-plane homeomorphism. -/
theorem modularDeckHomeomorph_inv (g : Delta) :
    modularDeckHomeomorph g⁻¹ = (modularDeckHomeomorph g).symm := by
  ext τ
  have hτ : (modularTargetAction g⁻¹) τ = (modularTargetAction g).symm τ := by
    simpa using DFunLike.congr_fun (map_inv modularTargetAction g) τ
  exact congrArg ((↑) : UpperHalfPlane → ℂ) hτ

/-- Applying `g⁻¹` after `g` recovers the original solution germ. -/
theorem modularSolutionDeck_inv_apply (g : Delta) (p : ModularSolutionEtale C U) :
    modularSolutionDeck g⁻¹ (modularSolutionDeck g p) = p := by
  apply Subtype.ext
  rw [← HolomorphicPresheaf.germPoint_repFun p.1]
  apply HolomorphicPresheaf.germPoint_congr
  have hchosen :
      (fun w ↦ (solutionRepresentative (modularSolutionDeck g p) w : ℂ)) =ᶠ[𝓝 p.1.base]
        modularTransformRepresentative g p := by
    exact (solutionRepresentative_coe_eventuallyEq (modularSolutionDeck g p)).trans
      (modularDeckEtalePoint_repFun_eventuallyEq g p)
  apply Filter.EventuallyEq.trans _ (solutionRepresentative_coe_eventuallyEq p)
  filter_upwards [hchosen] with w hw
  have hτ : solutionRepresentative (modularSolutionDeck g p) w =
      modularDeckHomeomorph g (solutionRepresentative p w) :=
    UpperHalfPlane.coe_injective hw
  change (modularDeckHomeomorph g⁻¹
    (solutionRepresentative (modularSolutionDeck g p) w) : ℂ) = _
  rw [hτ, modularDeckHomeomorph_inv]
  exact congrArg ((↑) : UpperHalfPlane → ℂ)
    ((modularDeckHomeomorph g).symm_apply_apply (solutionRepresentative p w))

/-- The modular transformation of solution germs varies continuously in the étalé topology.
Locally, every nearby germ is represented by one common holomorphic section; postcomposing that
section with the fixed modular transformation gives a common local section for all their images. -/
theorem continuous_modularDeckEtalePoint (g : Delta) :
    Continuous (fun p : ModularSolutionEtale C U ↦ modularDeckEtalePoint g p) := by
  rw [continuous_iff_continuousAt]
  intro p
  let f : ℂ → ℂ := fun w ↦ (solutionRepresentative p w : ℂ)
  let tf : ℂ → ℂ := modularTransformRepresentative g p
  have hfan : AnalyticAt ℂ f p.1.base :=
    (HolomorphicPresheaf.analyticAt_repFun p.1).congr
      (solutionRepresentative_coe_eventuallyEq p).symm
  have htfan : AnalyticAt ℂ tf p.1.base := analyticAt_modularTransformRepresentative g p
  obtain ⟨rf, hrf, hfball⟩ := hfan.exists_ball_analyticOnNhd
  obtain ⟨rt, hrt, htfball⟩ := htfan.exists_ball_analyticOnNhd
  let W : TopologicalSpace.Opens (TopCat.of ℂ) :=
    ⟨ball p.1.base rf ∩ ball p.1.base rt, isOpen_ball.inter isOpen_ball⟩
  have hpW : p.1.base ∈ W := ⟨mem_ball_self hrf, mem_ball_self hrt⟩
  have hfW : AnalyticOnNhd ℂ f W := hfball.mono inter_subset_left
  have htfW : AnalyticOnNhd ℂ tf W := htfball.mono inter_subset_right
  let sec := HolomorphicPresheaf.toSection W f hfW
  let S := TopCat.Presheaf.EtaleSpace.sectionRange (holomorphicPresheaf ℂ) W sec
  have hpS : p.1 ∈ S := by
    apply TopCat.Presheaf.EtaleSpace.mem_sectionRange_iff.mpr
    refine ⟨hpW, ?_⟩
    have hfsec : HolomorphicPresheaf.sectionFun sec =ᶠ[𝓝 p.1.base] f :=
      Filter.eventuallyEq_of_mem (W.isOpen.mem_nhds hpW)
        (HolomorphicPresheaf.sectionFun_toSection hfW)
    have hfgerm : HolomorphicPresheaf.germAt f p.1.base =
        (holomorphicPresheaf ℂ).germ W p.1.base hpW sec :=
      HolomorphicPresheaf.germAt_eq_germ_of_eventuallyEq hpW sec hfsec
    have hpgerm : HolomorphicPresheaf.germAt f p.1.base = p.1.germ :=
      (HolomorphicPresheaf.germAt_congr
        (solutionRepresentative_coe_eventuallyEq p)).trans
        (HolomorphicPresheaf.germAt_repFun p.1)
    exact hpgerm.symm.trans hfgerm
  have hSopen : IsOpen S :=
    TopCat.Presheaf.EtaleSpace.isOpen_sectionRange (F := holomorphicPresheaf ℂ) W sec
  have hnear : {q : ModularSolutionEtale C U | q.1 ∈ S} ∈ 𝓝 p :=
    (hSopen.preimage continuous_subtype_val).mem_nhds hpS
  have hbasecont : Continuous
      (TopCat.Presheaf.EtaleSpace.base : (holomorphicPresheaf ℂ).EtaleSpace → ℂ) :=
    TopCat.Presheaf.EtaleSpace.continuous_base (holomorphicPresheaf ℂ)
  have hlocalFull : ContinuousAt
      (fun q : (holomorphicPresheaf ℂ).EtaleSpace ↦
        HolomorphicPresheaf.germPoint tf q.base) p.1 :=
    ((HolomorphicPresheaf.continuousOn_germPoint htfW).continuousAt
      (W.isOpen.mem_nhds hpW)).comp' hbasecont.continuousAt
  have hlocal : ContinuousAt
      (fun q : ModularSolutionEtale C U ↦ HolomorphicPresheaf.germPoint tf q.1.base) p :=
    hlocalFull.comp' continuous_subtype_val.continuousAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hnear] with q hqS
  obtain ⟨hqW, hqgerm⟩ :=
    (TopCat.Presheaf.EtaleSpace.mem_sectionRange_iff.mp hqS)
  have hqan : AnalyticAt ℂ (fun w ↦ (solutionRepresentative q w : ℂ)) q.1.base :=
    (HolomorphicPresheaf.analyticAt_repFun q.1).congr
      (solutionRepresentative_coe_eventuallyEq q).symm
  have hsecf : HolomorphicPresheaf.sectionFun sec =ᶠ[𝓝 q.1.base] f :=
    Filter.eventuallyEq_of_mem (W.isOpen.mem_nhds hqW)
      (HolomorphicPresheaf.sectionFun_toSection hfW)
  have hqfGerm :
      HolomorphicPresheaf.germAt (fun w ↦ (solutionRepresentative q w : ℂ)) q.1.base =
        HolomorphicPresheaf.germAt f q.1.base := by
    calc
      HolomorphicPresheaf.germAt (fun w ↦ (solutionRepresentative q w : ℂ)) q.1.base =
          HolomorphicPresheaf.germAt (HolomorphicPresheaf.repFun q.1) q.1.base :=
        HolomorphicPresheaf.germAt_congr (solutionRepresentative_coe_eventuallyEq q)
      _ = q.1.germ := HolomorphicPresheaf.germAt_repFun q.1
      _ = (holomorphicPresheaf ℂ).germ W q.1.base hqW sec := hqgerm
      _ = HolomorphicPresheaf.germAt f q.1.base :=
        (HolomorphicPresheaf.germAt_eq_germ_of_eventuallyEq hqW sec hsecf).symm
  have hqf : (fun w ↦ (solutionRepresentative q w : ℂ)) =ᶠ[𝓝 q.1.base] f :=
    (HolomorphicPresheaf.germAt_eq_iff hqan (hfW q.1.base hqW)).mp hqfGerm
  have htqf : modularTransformRepresentative g q =ᶠ[𝓝 q.1.base] tf := by
    filter_upwards [hqf] with w hw
    have hτ : solutionRepresentative q w = solutionRepresentative p w :=
      UpperHalfPlane.coe_injective hw
    exact congrArg (fun τ : UpperHalfPlane ↦
      (modularDeckHomeomorph g τ : ℂ)) hτ
  exact HolomorphicPresheaf.germPoint_congr htqf

theorem continuous_modularSolutionDeck (g : Delta) :
    Continuous (modularSolutionDeck g : ModularSolutionEtale C U →
      ModularSolutionEtale C U) :=
  (continuous_modularDeckEtalePoint (C := C) (U := U) g).subtype_mk _

/-- Every modular group element acts by a fiber-preserving homeomorphism of the solution-germ
space. -/
def modularSolutionDeckHomeomorph (g : Delta) :
    ModularSolutionEtale C U ≃ₜ ModularSolutionEtale C U where
  toEquiv :=
    { toFun := modularSolutionDeck g
      invFun := modularSolutionDeck g⁻¹
      left_inv := modularSolutionDeck_inv_apply g
      right_inv := fun p ↦ by
        simpa using modularSolutionDeck_inv_apply (C := C) (U := U) g⁻¹ p }
  continuous_toFun := continuous_modularSolutionDeck g
  continuous_invFun := continuous_modularSolutionDeck g⁻¹


end SphereSixComplex.Periods.SolutionGermModularDeck
