module

public import SphereSixComplex.Periods.Uniformization.UpperHalfPlaneSolutionGerm
import all SphereSixComplex.Periods.Uniformization.UpperHalfPlaneSolutionGerm
public import TauCeti.Analysis.Complex.Conformal.Continuation.Etale
import all TauCeti.Analysis.Complex.Conformal.Continuation.Etale
public import Mathlib.Topology.Homotopy.Lifting
import all Mathlib.Topology.Homotopy.Lifting
public import SphereSixComplex.Topology.HomogeneousCovering
import all SphereSixComplex.Topology.HomogeneousCovering

@[expose] public section

noncomputable section

namespace TauCeti

open Filter Set Topology unitInterval

/-- The subset of the holomorphic étalé space consisting of germs which locally land in the
upper half-plane and solve `j ∘ τ = C`, restricted over a source domain `U`. -/
def upperHalfPlaneSolutionEtaleSet (j : UpperHalfPlane → ℂ) (C : ℂ → ℂ)
    (U : Set ℂ) : Set (holomorphicPresheaf ℂ).EtaleSpace :=
  {p | p.base ∈ U ∧
    IsUpperHalfPlaneSolutionGerm j C p.base (HolomorphicPresheaf.repFun p)}

/-- The holomorphic germs which locally land in the upper half-plane and solve `j ∘ τ = C`,
restricted over a source domain `U`. -/
abbrev UpperHalfPlaneSolutionEtale (j : UpperHalfPlane → ℂ) (C : ℂ → ℂ)
    (U : Set ℂ) :=
  upperHalfPlaneSolutionEtaleSet j C U

/-- Projection of the solution-germ space to its source domain. -/
def upperHalfPlaneSolutionEtaleBase
    (j : UpperHalfPlane → ℂ) (C : ℂ → ℂ) (U : Set ℂ) :
    UpperHalfPlaneSolutionEtale j C U → U :=
  fun p ↦ ⟨p.1.base, p.2.1⟩

namespace UpperHalfPlaneSolutionEtale

variable {j : UpperHalfPlane → ℂ} {C f₀ : ℂ → ℂ}
  {U : Set ℂ} {z₀ : ℂ}

/-- The solution condition cuts out an open subset of the full holomorphic étalé space.  This
uses only that it is a germ-local condition and that `U` is open; no continuation or monodromy
hypothesis is needed. -/
theorem isOpen_upperHalfPlaneSolutionEtaleSet (hU : IsOpen U) :
    IsOpen (upperHalfPlaneSolutionEtaleSet j C U) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨τ, hτp, hjτ⟩ := hp.2
  have hall : {z | z ∈ U ∧ (τ z : ℂ) = HolomorphicPresheaf.repFun p z ∧
      j (τ z) = C z} ∈ 𝓝 p.base := by
    filter_upwards [hU.mem_nhds hp.1, hτp, hjτ] with z hz hτ hj
    exact ⟨hz, hτ, hj⟩
  obtain ⟨V, hVsub, hVopen, hpV⟩ := mem_nhds_iff.mp hall
  obtain ⟨r, hr, hball⟩ :=
    (HolomorphicPresheaf.analyticAt_repFun p).exists_ball_analyticOnNhd
  let W : TopologicalSpace.Opens (TopCat.of ℂ) :=
    ⟨V ∩ Metric.ball p.base r, hVopen.inter Metric.isOpen_ball⟩
  have hpW : p.base ∈ W := ⟨hpV, Metric.mem_ball_self hr⟩
  have hWan : AnalyticOnNhd ℂ (HolomorphicPresheaf.repFun p) W :=
    hball.mono fun _ hz ↦ hz.2
  let sec := HolomorphicPresheaf.toSection W (HolomorphicPresheaf.repFun p) hWan
  let S := TopCat.Presheaf.EtaleSpace.sectionRange (holomorphicPresheaf ℂ) W sec
  refine ⟨S, ?_, ?_, ?_⟩
  · intro q hqS
    obtain ⟨hqW, hqgerm⟩ :=
      (TopCat.Presheaf.EtaleSpace.mem_sectionRange_iff.mp hqS)
    have hqV : q.base ∈ V := hqW.1
    have hqall := hVsub hqV
    refine ⟨hqall.1, ?_⟩
    have hsec_q : HolomorphicPresheaf.sectionFun sec =ᶠ[𝓝 q.base]
        HolomorphicPresheaf.repFun p :=
      Filter.eventuallyEq_of_mem (W.isOpen.mem_nhds hqW)
        (HolomorphicPresheaf.sectionFun_toSection hWan)
    have hrepgerm : HolomorphicPresheaf.germAt (HolomorphicPresheaf.repFun p) q.base =
        (holomorphicPresheaf ℂ).germ W q.base hqW sec :=
      HolomorphicPresheaf.germAt_eq_germ_of_eventuallyEq hqW sec hsec_q
    have hgermeq : HolomorphicPresheaf.germAt (HolomorphicPresheaf.repFun q) q.base =
        HolomorphicPresheaf.germAt (HolomorphicPresheaf.repFun p) q.base := by
      calc
        HolomorphicPresheaf.germAt (HolomorphicPresheaf.repFun q) q.base = q.germ :=
          HolomorphicPresheaf.germAt_repFun q
        _ = (holomorphicPresheaf ℂ).germ W q.base hqW sec := hqgerm
        _ = HolomorphicPresheaf.germAt (HolomorphicPresheaf.repFun p) q.base :=
          hrepgerm.symm
    have hqp : HolomorphicPresheaf.repFun q =ᶠ[𝓝 q.base]
        HolomorphicPresheaf.repFun p :=
      (HolomorphicPresheaf.germAt_eq_iff
        (HolomorphicPresheaf.analyticAt_repFun q) (hball q.base hqW.2)).mp hgermeq
    have hτp_q : (fun z ↦ (τ z : ℂ)) =ᶠ[𝓝 q.base]
        HolomorphicPresheaf.repFun p :=
      Filter.eventuallyEq_of_mem (hVopen.mem_nhds hqV)
        fun z hz ↦ (hVsub hz).2.1
    have hjτ_q : (fun z ↦ j (τ z)) =ᶠ[𝓝 q.base] C :=
      Filter.eventuallyEq_of_mem (hVopen.mem_nhds hqV)
        fun z hz ↦ (hVsub hz).2.2
    exact ⟨τ, hτp_q.trans hqp.symm, hjτ_q⟩
  · simpa [S] using
      (TopCat.Presheaf.EtaleSpace.isOpen_sectionRange
        (F := holomorphicPresheaf ℂ) W sec)
  · apply TopCat.Presheaf.EtaleSpace.mem_sectionRange_iff.mpr
    refine ⟨hpW, ?_⟩
    have hsec_p : HolomorphicPresheaf.sectionFun sec =ᶠ[𝓝 p.base]
        HolomorphicPresheaf.repFun p :=
      Filter.eventuallyEq_of_mem (W.isOpen.mem_nhds hpW)
        (HolomorphicPresheaf.sectionFun_toSection hWan)
    have hrepgerm : HolomorphicPresheaf.germAt (HolomorphicPresheaf.repFun p) p.base =
        (holomorphicPresheaf ℂ).germ W p.base hpW sec :=
      HolomorphicPresheaf.germAt_eq_germ_of_eventuallyEq hpW sec hsec_p
    exact (HolomorphicPresheaf.germAt_repFun p).symm.trans hrepgerm

/-- The projection from solution germs to an open source domain is a local homeomorphism.  Thus
the only extra content in a covering assertion is the uniform/evenly-covered control of all
sheets over one common neighbourhood. -/
theorem isLocalHomeomorph_upperHalfPlaneSolutionEtaleBase (hU : IsOpen U) :
    IsLocalHomeomorph (upperHalfPlaneSolutionEtaleBase j C U) := by
  have hsub : IsLocalHomeomorph
      (Subtype.val : UpperHalfPlaneSolutionEtale j C U →
        (holomorphicPresheaf ℂ).EtaleSpace) :=
    (isOpen_upperHalfPlaneSolutionEtaleSet (j := j) (C := C) hU)
      |>.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hfull : IsLocalHomeomorph
      (TopCat.Presheaf.EtaleSpace.base (F := holomorphicPresheaf ℂ) ∘
        (Subtype.val : UpperHalfPlaneSolutionEtale j C U →
          (holomorphicPresheaf ℂ).EtaleSpace)) :=
    (TopCat.Presheaf.EtaleSpace.isLocalHomeomorph_base (holomorphicPresheaf ℂ)).comp hsub
  have hcomp : IsLocalHomeomorph
      ((Subtype.val : U → ℂ) ∘ upperHalfPlaneSolutionEtaleBase j C U) := by
    simpa [Function.comp_def, upperHalfPlaneSolutionEtaleBase] using hfull
  have hbase_cont : Continuous (upperHalfPlaneSolutionEtaleBase j C U) := by
    have hmk := hcomp.continuous.subtype_mk
      (fun p ↦ (upperHalfPlaneSolutionEtaleBase j C U p).2)
    convert hmk using 1
    funext p
    exact Subtype.ext rfl
  exact hcomp.of_comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph hbase_cont

/-- The solution-germ projection is separated.  This is inherited from the full holomorphic
étalé projection, whose separatedness is the identity theorem. -/
theorem isSeparatedMap_upperHalfPlaneSolutionEtaleBase :
    IsSeparatedMap (upperHalfPlaneSolutionEtaleBase j C U) := by
  have hfull : IsSeparatedMap
      (TopCat.Presheaf.EtaleSpace.base (F := holomorphicPresheaf ℂ) ∘
        (Subtype.val : UpperHalfPlaneSolutionEtale j C U →
          (holomorphicPresheaf ℂ).EtaleSpace)) :=
    HolomorphicPresheaf.isSeparatedMap_base.comp_right
      continuous_subtype_val Subtype.val_injective
  intro p q hpq hpne
  apply hfull p q _ hpne
  exact congrArg Subtype.val hpq

/-- Pointwise existence of analytic solution germs makes the solution-germ projection
surjective.  Together with the preceding theorem this gives a surjective local homeomorphism;
the remaining step to a covering map is genuinely the uniform control of its sheets. -/
theorem surjective_upperHalfPlaneSolutionEtaleBase_of_local_solutions
    (hlocal : ∀ z ∈ U, ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧
      IsUpperHalfPlaneSolutionGerm j C z f) :
    Function.Surjective (upperHalfPlaneSolutionEtaleBase j C U) := by
  intro z
  obtain ⟨f, hf, hPf⟩ := hlocal (z : ℂ) z.2
  let p : (holomorphicPresheaf ℂ).EtaleSpace :=
    HolomorphicPresheaf.germPoint f (z : ℂ)
  have hrep : HolomorphicPresheaf.repFun p =ᶠ[𝓝 (z : ℂ)]
      f := by
    apply (HolomorphicPresheaf.germAt_eq_iff
      (HolomorphicPresheaf.analyticAt_repFun p) hf).mp
    simpa [p] using HolomorphicPresheaf.germAt_repFun p
  have hPp : IsUpperHalfPlaneSolutionGerm j C (z : ℂ)
      (HolomorphicPresheaf.repFun p) :=
    hPf.congr hrep.symm
  let q : UpperHalfPlaneSolutionEtale j C U := ⟨p, z.2, hPp⟩
  refine ⟨q, ?_⟩
  exact Subtype.ext rfl

/-- A covering theorem for the étalé space of solution germs supplies exactly the
relation-preserving continuation hypothesis consumed by Tau Ceti's global branch theorem. -/
theorem continuesInsideWith_of_isCoveringMap
    (hz₀ : z₀ ∈ U) (hf₀ : AnalyticAt ℂ f₀ z₀)
    (hP₀ : IsUpperHalfPlaneSolutionGerm j C z₀ f₀)
    (hcov : IsCoveringMap (upperHalfPlaneSolutionEtaleBase j C U)) :
    ContinuesInsideWith f₀ U z₀ (IsUpperHalfPlaneSolutionGerm j C) := by
  let p₀ : (holomorphicPresheaf ℂ).EtaleSpace :=
    HolomorphicPresheaf.germPoint f₀ z₀
  have hrep : HolomorphicPresheaf.repFun p₀ =ᶠ[𝓝 z₀] f₀ := by
    apply (HolomorphicPresheaf.germAt_eq_iff
      (HolomorphicPresheaf.analyticAt_repFun p₀) hf₀).mp
    simpa [p₀] using HolomorphicPresheaf.germAt_repFun p₀
  have hp₀P : IsUpperHalfPlaneSolutionGerm j C z₀
      (HolomorphicPresheaf.repFun p₀) :=
    hP₀.congr hrep.symm
  let e₀ : UpperHalfPlaneSolutionEtale j C U := ⟨p₀, hz₀, hp₀P⟩
  refine ⟨fun c hc hcU hc0 ↦ ?_⟩
  let γ : C(I, U) := ⟨fun t ↦ ⟨c t, hcU t⟩, hc.subtype_mk hcU⟩
  have hγ0 : γ 0 = upperHalfPlaneSolutionEtaleBase j C U e₀ := by
    apply Subtype.ext
    exact hc0
  let Γ : C(I, UpperHalfPlaneSolutionEtale j C U) := hcov.liftPath γ e₀ hγ0
  let f : I → ℂ → ℂ := fun t ↦ HolomorphicPresheaf.repFun (Γ t).1
  have hΓbase : (fun t ↦ (Γ t).1.base) = c := by
    funext t
    have hlift := congrFun (hcov.liftPath_lifts γ e₀ hγ0) t
    exact congrArg Subtype.val hlift
  have hfcont : IsAnalyticContinuationAlong f c Set.univ := by
    have hΓcont : Continuous (fun t ↦ (Γ t).1) :=
      continuous_subtype_val.comp Γ.continuous
    have h := isAnalyticContinuationAlong_repFun
      (Γ := fun t ↦ (Γ t).1) (s := Set.univ) hΓcont.continuousOn
    rw [hΓbase] at h
    exact h
  have hΓ0 : Γ 0 = e₀ := hcov.liftPath_zero γ e₀ hγ0
  refine ⟨f, hfcont, ?_, fun t ↦ ?_⟩
  · simpa [f, hΓ0, e₀, p₀, hc0] using hrep
  · have ht := (Γ t).2.2
    have hbt := congrFun hΓbase t
    simpa [f, hbt] using ht

/-- A directly usable continuation theorem from local solutions and modular-style deck
homogeneity.  The preceding general covering theorem turns the transitive fiberwise action into
uniformly transported sheets; Tau Ceti then lifts every path through those sheets. -/
theorem continuesInsideWith_of_deck_transitive
    {ι : Type*} (hU : IsOpen U)
    (hz₀ : z₀ ∈ U) (hf₀ : AnalyticAt ℂ f₀ z₀)
    (hP₀ : IsUpperHalfPlaneSolutionGerm j C z₀ f₀)
    (hlocal : ∀ z ∈ U, ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧
      IsUpperHalfPlaneSolutionGerm j C z f)
    (deck : ι → UpperHalfPlaneSolutionEtale j C U ≃ₜ
      UpperHalfPlaneSolutionEtale j C U)
    (hdeck : ∀ i p, upperHalfPlaneSolutionEtaleBase j C U (deck i p) =
      upperHalfPlaneSolutionEtaleBase j C U p)
    (htrans : ∀ p q,
      upperHalfPlaneSolutionEtaleBase j C U p =
        upperHalfPlaneSolutionEtaleBase j C U q →
      ∃ i, deck i p = q) :
    ContinuesInsideWith f₀ U z₀ (IsUpperHalfPlaneSolutionGerm j C) := by
  letI : LocallyConnectedSpace U := hU.locallyConnectedSpace
  have hcov : IsCoveringMap (upperHalfPlaneSolutionEtaleBase j C U) :=
    Topology.isCoveringMap_of_deck_transitive
      (upperHalfPlaneSolutionEtaleBase j C U)
      (isLocalHomeomorph_upperHalfPlaneSolutionEtaleBase (j := j) (C := C) hU)
      (isSeparatedMap_upperHalfPlaneSolutionEtaleBase (j := j) (C := C) (U := U))
      (surjective_upperHalfPlaneSolutionEtaleBase_of_local_solutions hlocal)
      deck hdeck htrans
  exact continuesInsideWith_of_isCoveringMap hz₀ hf₀ hP₀ hcov


end UpperHalfPlaneSolutionEtale

end TauCeti
