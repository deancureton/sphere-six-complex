module

public import JordanCurveTheorem.PlaneSeparationBridge
import all JordanCurveTheorem.PlaneSeparationBridge
public import TauCeti.Analysis.Normed.Module.FilledHull
import all TauCeti.Analysis.Normed.Module.FilledHull
public import TauCeti.Topology.JordanCurve.Basic
import all TauCeti.Topology.JordanCurve.Basic
public import Mathlib.Analysis.Normed.Module.Connected
import all Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import all Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homeomorph.Lemmas
import all Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

open Bornology Metric Set Topology

noncomputable section

namespace SphereSixComplex.Periods.JordanFilledHullSeparation

open AddCircle JordanCurveTheorem TauCeti

/-- Tau Ceti's homeomorphism-based Jordan-curve predicate implies the parametrized predicate
used by the EPFL Jordan-curve theorem. -/
theorem isSimpleClosedCurve_of_isJordanCurve {C : Set E2'}
    (hC : TauCeti.IsJordanCurve C) : IsSimpleClosedCurve C := by
  obtain ⟨e⟩ := hC
  let e' : C ≃ₜ UnitAddCircle :=
    e.trans (AddCircle.homeomorphCircle one_ne_zero).symm
  refine ⟨fun t => ↑(e'.symm (↑t : UnitAddCircle)), ?_, ?_, ?_, ?_⟩
  · ext c
    simp only [mem_image]
    constructor
    · intro hc
      set q : UnitAddCircle := e' ⟨c, hc⟩
      have ht := (equivIco 1 0 q).2
      refine ⟨(equivIco 1 0 q).1, Ico_subset_Icc_self (by simpa using ht), ?_⟩
      change (e'.symm (↑(equivIco 1 0 q).1 : UnitAddCircle) : E2') = c
      have hcircle : (↑(equivIco 1 0 q).1 : UnitAddCircle) = q := by
        apply (equivIco 1 0).injective
        rw [equivIco_coe_eq ht]
      calc
        (e'.symm (↑(equivIco 1 0 q).1 : UnitAddCircle) : E2') =
            (e'.symm q : E2') := congrArg (fun u => (e'.symm u : E2')) hcircle
        _ = c := congrArg Subtype.val (e'.symm_apply_apply ⟨c, hc⟩)
    · rintro ⟨t, _, rfl⟩
      exact (e'.symm (↑t : UnitAddCircle)).2
  · exact continuous_subtype_val.comp
      (e'.symm.continuous.comp (AddCircle.continuous_mk' 1))
  · intro a ha b hb hab
    exact (coe_eq_coe_iff_of_mem_Ico
      ⟨ha.1, by linarith [ha.2]⟩ ⟨hb.1, by linarith [hb.2]⟩).mp
      (e'.symm.injective (Subtype.val_injective hab))
  · change (e'.symm (↑(0 : ℝ) : UnitAddCircle) : E2') =
      (e'.symm (↑(1 : ℝ) : UnitAddCircle) : E2')
    exact congrArg (fun x => (e'.symm x : E2')) (by simp [coe_period])

/-- Plane separation in exactly the filled-hull form used by Tau Ceti's Carathéodory theorem,
first stated on the Euclidean plane used by the EPFL development. -/
theorem isJordanCurve_subset_closure_filledHull_diff_e2 {J : Set E2'}
    (hJ : TauCeti.IsJordanCurve J) :
    J ⊆ closure (filledHull J \ J) := by
  have hJsimple : IsSimpleClosedCurve J := isSimpleClosedCurve_of_isJordanCurve hJ
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hAJ, hBJ, hcover⟩ :=
    jordan_curve_theorem hJsimple
  obtain ⟨v, hvA⟩ := hAc.nonempty
  obtain ⟨w, hwB⟩ := hBc.nonempty
  have hvJ : v ∉ J := fun hv => Set.disjoint_left.mp hAJ hvA hv
  have hwJ : w ∉ J := fun hw => Set.disjoint_left.mp hBJ hwB hw
  have hvcomp : v ∈ connectedComponentIn Jᶜ v :=
    mem_connectedComponentIn (mem_compl hvJ)
  have hcompAB : connectedComponentIn Jᶜ v ⊆ A ∪ B := by
    intro x hx
    have hxJ : x ∉ J := connectedComponentIn_subset Jᶜ v hx
    have hxuniv : x ∈ A ∪ B ∪ J := by rw [hcover]; exact mem_univ x
    rcases hxuniv with hxAB | hxJ'
    · exact hxAB
    · exact absurd hxJ' hxJ
  have hdich : connectedComponentIn Jᶜ v ⊆ A ∨
      connectedComponentIn Jᶜ v ⊆ B :=
    isPreconnected_connectedComponentIn.subset_or_subset hAo hBo hAB hcompAB
  have hcompA : connectedComponentIn Jᶜ v ⊆ A :=
    hdich.resolve_right fun hcompB =>
      Set.disjoint_left.mp hAB hvA (hcompB hvcomp)
  have hwcomp : w ∉ connectedComponentIn Jᶜ v := fun hw =>
    Set.disjoint_left.mp hAB (hcompA hw) hwB
  have hrank : 1 < Module.rank ℝ E2' := by
    have hrankeq : Module.rank ℝ E2' = 2 :=
      (Module.rank_eq_ofNat_iff_finrank_eq_ofNat 2).2 (by
        simpa [E2', E2] using
          (finrank_euclideanSpace_fin (n := 2) (𝕜 := ℝ)))
    rw [hrankeq]
    norm_num
  have hbounded : IsBounded J := isSimpleClosedCurve_isCompact hJsimple |>.isBounded
  rcases TauCeti.mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn
      hrank hbounded hwcomp with hvfill | hwfill
  · have hcompfill : connectedComponentIn Jᶜ v ⊆ filledHull J \ J := by
      intro y hy
      constructor
      · rw [mem_filledHull_iff, ← connectedComponentIn_eq hy]
        exact mem_filledHull_iff.mp hvfill
      · exact connectedComponentIn_subset Jᶜ v hy
    exact (isSimpleClosedCurve_subset_closure_connectedComponentIn_compl hJsimple hvJ).trans
      (closure_mono hcompfill)
  · have hcompfill : connectedComponentIn Jᶜ w ⊆ filledHull J \ J := by
      intro y hy
      constructor
      · rw [mem_filledHull_iff, ← connectedComponentIn_eq hy]
        exact mem_filledHull_iff.mp hwfill
      · exact connectedComponentIn_subset Jᶜ w hy
    exact (isSimpleClosedCurve_subset_closure_connectedComponentIn_compl hJsimple hwJ).trans
      (closure_mono hcompfill)

/-- A real linear isometry equivalence carries a filled hull to the filled hull of the image. -/
theorem mem_filledHull_image_iff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (K : Set E) (x : E) :
    x ∈ filledHull K ↔ e x ∈ filledHull (e '' K) := by
  by_cases hxK : x ∈ K
  · exact ⟨fun _ => subset_filledHull ⟨x, hxK, rfl⟩,
      fun _ => subset_filledHull hxK⟩
  have hxcompl : x ∈ Kᶜ := mem_compl hxK
  have hexcompl : e x ∈ (e '' K)ᶜ := by
    intro hexK
    obtain ⟨y, hyK, hey⟩ := hexK
    exact hxK (e.injective hey ▸ hyK)
  have hforward : e '' connectedComponentIn Kᶜ x =
      connectedComponentIn (e '' K)ᶜ (e x) := by
    have h := e.toHomeomorph.image_connectedComponentIn hxcompl
    rw [e.toHomeomorph.image_compl] at h
    simpa only [LinearIsometryEquiv.coe_toHomeomorph] using h
  have hbackward : e.symm '' connectedComponentIn (e '' K)ᶜ (e x) =
      connectedComponentIn Kᶜ x := by
    have h := e.symm.toHomeomorph.image_connectedComponentIn hexcompl
    rw [e.symm.toHomeomorph.image_compl] at h
    simp only [LinearIsometryEquiv.coe_toHomeomorph, e.symm_apply_apply] at h
    have himage : e.symm '' (e '' K) = K := e.toEquiv.symm_image_image K
    rw [himage] at h
    exact h
  constructor
  · intro hx
    rw [mem_filledHull_iff]
    rw [← hforward]
    exact e.lipschitz.isBounded_image (mem_filledHull_iff.mp hx)
  · intro hx
    rw [mem_filledHull_iff]
    rw [← hbackward]
    exact e.symm.lipschitz.isBounded_image (mem_filledHull_iff.mp hx)

/-- The plane-separation hypothesis consumed by Tau Ceti's Carathéodory theorem, on `ℂ`. -/
theorem isJordanCurve_subset_closure_filledHull_diff_complex
    {J : Set ℂ} (hJ : TauCeti.IsJordanCurve J) :
    J ⊆ closure (filledHull J \ J) := by
  let e : ℂ ≃ₗᵢ[ℝ] E2' := Complex.orthonormalBasisOneI.repr
  let J2 : Set E2' := e '' J
  have hJ2 : TauCeti.IsJordanCurve J2 :=
    hJ.image_homeomorph e.toHomeomorph
  have hsep2 : J2 ⊆ closure (filledHull J2 \ J2) :=
    isJordanCurve_subset_closure_filledHull_diff_e2 hJ2
  intro z hz
  have hez : e z ∈ closure (filledHull J2 \ J2) :=
    hsep2 ⟨z, hz, rfl⟩
  have hpre : z ∈ e.symm '' closure (filledHull J2 \ J2) :=
    ⟨e z, hez, e.symm_apply_apply z⟩
  have himageClosure := e.symm.toHomeomorph.image_closure (filledHull J2 \ J2)
  change e.symm '' closure (filledHull J2 \ J2) =
    closure (e.symm '' (filledHull J2 \ J2)) at himageClosure
  rw [himageClosure] at hpre
  apply closure_mono _ hpre
  rintro x ⟨y, ⟨hyfill, hyJ2⟩, rfl⟩
  constructor
  · apply (mem_filledHull_image_iff e J (e.symm y)).2
    simpa only [e.apply_symm_apply, J2] using hyfill
  · intro hmemJ
    apply hyJ2
    exact ⟨e.symm y, hmemJ, e.apply_symm_apply y⟩


end SphereSixComplex.Periods.JordanFilledHullSeparation
