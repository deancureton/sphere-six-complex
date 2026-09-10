module

public import TauCeti.Analysis.Complex.Conformal.GlobalBranch
import all TauCeti.Analysis.Complex.Conformal.GlobalBranch

@[expose] public section

noncomputable section

namespace TauCeti

open Filter Set Topology unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Analytic continuation inside a domain, with an additional germ-local predicate carried by
every chosen continuation.  This is the relation-preserving input needed for implicit-function
applications of the monodromy theorem. -/
structure ContinuesInsideWith (f₀ : ℂ → E) (U : Set ℂ) (z₀ : ℂ)
    (P : ℂ → (ℂ → E) → Prop) : Prop where
  exists_continuation :
    ∀ c : I → ℂ, Continuous c → (∀ t, c t ∈ U) → c 0 = z₀ →
      ∃ f : I → ℂ → E,
        IsAnalyticContinuationAlong f c Set.univ ∧
          f 0 =ᶠ[𝓝 z₀] f₀ ∧ ∀ t, P (c t) (f t)

namespace ContinuesInsideWith

variable {f₀ : ℂ → E} {U : Set ℂ} {z₀ : ℂ} {P : ℂ → (ℂ → E) → Prop}

/-- Forgetting the preserved relation gives Tau Ceti's ordinary continuability hypothesis. -/
theorem toContinuesInside (H : ContinuesInsideWith f₀ U z₀ P) :
    ContinuesInside f₀ U z₀ := by
  apply ContinuesInside.of_forall
  intro c hc hcU hc0
  obtain ⟨f, hf, hf0, -⟩ := H.exists_continuation c hc hcU hc0
  refine (continuesAlong_iff_exists).2 ⟨f, hf, ?_⟩
  simpa [hc0] using hf0

/-- Relation-preserving monodromy theorem.  If a germ-local predicate is stable under germ
equality and can be carried along every path, the global branch on a simply connected domain
satisfies that predicate at every point. -/
theorem exists_analyticOnNhd_and_forall
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hz₀ : z₀ ∈ U)
    (H : ContinuesInsideWith f₀ U z₀ P)
    (hPcongr : ∀ z {f g : ℂ → E}, f =ᶠ[𝓝 z] g → P z f → P z g) :
    ∃ F : ℂ → E,
      AnalyticOnNhd ℂ F U ∧ F =ᶠ[𝓝 z₀] f₀ ∧ ∀ z ∈ U, P z F := by
  obtain ⟨F, hF, hF0⟩ :=
    H.toContinuesInside.exists_analyticOnNhd hUo hUc hz₀
  refine ⟨F, hF, hF0, fun z hz ↦ ?_⟩
  have hj := hUc.isPathConnected.joinedIn z₀ hz₀ z hz
  let c : Path z₀ z := hj.somePath
  have hcU : ∀ t, c t ∈ U := hj.somePath_mem
  obtain ⟨f, hf, hf0, hPf⟩ :=
    H.exists_continuation c c.continuous hcU c.source
  have hFc : IsAnalyticContinuationAlong (fun _ : I => F) c Set.univ :=
    .const c.continuous.continuousOn fun t _ ↦ hF (c t) (hcU t)
  have hstart : f 0 =ᶠ[𝓝 (c 0)] F := by
    simpa using hf0.trans hF0.symm
  have hend : f 1 =ᶠ[𝓝 (c 1)] F :=
    hf.eventuallyEq hFc isPreconnected_univ (mem_univ 0) (mem_univ 1) hstart
  have hend' : f 1 =ᶠ[𝓝 z] F := by simpa using hend
  exact hPcongr z hend' (by simpa using hPf 1)


end ContinuesInsideWith

end TauCeti
