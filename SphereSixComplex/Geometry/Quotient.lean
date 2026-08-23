module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Complex-manifold quotients

This file isolates the smooth compatibility condition missing from mathlib's charted-space
construction for quotients by free properly discontinuous actions. Once that condition is proved,
the quotient is a manifold. If the group acts by diffeomorphisms, the quotient projection is a
local diffeomorphism.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry

public noncomputable section

section Basic

variable {M G : Type*} [Group G] [MulAction G M]

/-- The orbit quotient of a group action. -/
public abbrev OrbitQuotient := MulAction.orbitRel.Quotient G M

/-- The projection to the orbit quotient. -/
public def quotientProjection : M → OrbitQuotient (M := M) (G := G) :=
  Quotient.mk _

/-- The orbit projection is surjective. -/
public theorem quotientProjection_surjective :
    Function.Surjective (quotientProjection (M := M) (G := G)) :=
  Quotient.mk_surjective

/-- A chosen representative of each orbit. -/
public noncomputable def quotientSection : OrbitQuotient (M := M) (G := G) → M :=
  quotientProjection_surjective.hasRightInverse.choose

/-- The chosen representative maps back to its orbit. -/
public theorem quotientProjection_section (q : OrbitQuotient (M := M) (G := G)) :
    quotientProjection (quotientSection q) = q :=
  quotientProjection_surjective.hasRightInverse.choose_spec q

end Basic

section Topological

variable {M G : Type*} [TopologicalSpace M] [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]

/-- The projection for a free properly discontinuous action is a local homeomorphism. -/
public theorem quotientProjection_isLocalHomeomorph :
    IsLocalHomeomorph (quotientProjection (M := M) (G := G)) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap.isLocalHomeomorph

/-- Two convergent local lifts of the same orbit-valued map differ locally by the unique group
element relating their limiting values. -/
public theorem eventuallyEq_const_smul_of_tendsto
    {X : Type*} [TopologicalSpace X] {l : Filter X} {f₁ f₂ : X → M} {x₁ x₂ : M}
    (g : G) (hf₁ : Filter.Tendsto f₁ l (nhds x₁)) (hf₂ : Filter.Tendsto f₂ l (nhds x₂))
    (hx : x₂ = g • x₁)
    (hproj : quotientProjection (M := M) (G := G) ∘ f₁ =ᶠ[l]
      quotientProjection (M := M) (G := G) ∘ f₂) :
    f₂ =ᶠ[l] fun y ↦ g • f₁ y := by
  let hp : IsQuotientCoveringMap (quotientProjection (M := M) (G := G)) G :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  obtain ⟨U, hx₁U, hU⟩ := hp.disjoint x₁
  have hf₂' : Filter.Tendsto (fun y ↦ g⁻¹ • f₂ y) l (nhds x₁) := by
    change Filter.Tendsto ((fun x : M ↦ g⁻¹ • x) ∘ f₂) l (nhds x₁)
    simpa only [hx, inv_smul_smul] using
      (continuous_const_smul g⁻¹).continuousAt.tendsto.comp hf₂
  filter_upwards [hf₁.eventually hx₁U, hf₂'.eventually hx₁U, hproj] with y hy₁ hy₂ hyproj
  have horbit : f₂ y ∈ MulAction.orbit G (f₁ y) :=
    hp.apply_eq_iff_mem_orbit.mp hyproj.symm
  obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp horbit
  have hkg : g⁻¹ * k = 1 := hU (g⁻¹ * k) ⟨g⁻¹ • f₂ y, ⟨f₁ y, hy₁, by
    change (g⁻¹ * k) • f₁ y = g⁻¹ • f₂ y
    rw [mul_smul, hk]⟩, hy₂⟩
  calc
    f₂ y = k • f₁ y := hk.symm
    _ = g • f₁ y := congrArg (fun a ↦ a • f₁ y) (inv_mul_eq_one.mp hkg).symm

end Topological

section Charts

variable {M G H : Type*} [TopologicalSpace M] [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [TopologicalSpace H] [ChartedSpace H M]

/-- The quotient chart centered at an orbit, using its chosen representative. -/
public noncomputable def quotientChart (q : OrbitQuotient (M := M) (G := G)) :
    OpenPartialHomeomorph (OrbitQuotient (M := M) (G := G)) H :=
  ((quotientProjection_isLocalHomeomorph (M := M) (G := G)).localInverseAt
    (quotientSection q)).trans (chartAt H (quotientSection q))

/-- The atlas supplied by `MulAction.instChartedSpaceQuotient` consists precisely of the canonical
quotient charts. -/
public theorem quotient_atlas :
    atlas H (OrbitQuotient (M := M) (G := G)) =
      Set.range (quotientChart (M := M) (G := G) (H := H)) := by
  rfl

/-- The canonical quotient chart is definitionally the preferred chart at its center. -/
public theorem quotientChart_eq_chartAt (q : OrbitQuotient (M := M) (G := G)) :
    quotientChart (M := M) (G := G) (H := H) q = chartAt H q := by
  rfl

/-- At its center, a quotient chart agrees with the chart at the chosen representative. -/
public theorem quotientChart_apply_self (q : OrbitQuotient (M := M) (G := G)) :
    quotientChart (M := M) (G := G) (H := H) q q =
      chartAt H (quotientSection q) (quotientSection q) := by
  simp only [quotientChart, OpenPartialHomeomorph.trans_apply]
  congr 1
  let hp := quotientProjection_isLocalHomeomorph (M := M) (G := G)
  let s := quotientSection (M := M) (G := G) q
  change hp.localInverseAt s q = s
  calc
    hp.localInverseAt s q =
        hp.localInverseAt s (quotientProjection (M := M) (G := G) s) :=
      congrArg (hp.localInverseAt s) (quotientProjection_section q).symm
    _ = s := hp.localInverseAt_apply_self

/-- On a source chart, the inverse quotient chart followed by coordinates is the orbit
projection. -/
public theorem quotientChart_symm_apply_chart (q : OrbitQuotient (M := M) (G := G))
    {x : M} (hx : x ∈ (chartAt H (quotientSection q)).source) :
    (quotientChart (M := M) (G := G) (H := H) q).symm
        (chartAt H (quotientSection q) x) =
      quotientProjection (M := M) (G := G) x := by
  let hp := quotientProjection_isLocalHomeomorph (M := M) (G := G)
  let s := quotientSection (M := M) (G := G) q
  change ((hp.localInverseAt s).trans (chartAt H s)).symm (chartAt H s x) =
    quotientProjection (M := M) (G := G) x
  change (hp.localInverseAt s).symm ((chartAt H s).symm (chartAt H s x)) =
    quotientProjection (M := M) (G := G) x
  rw [(chartAt H s).left_inv hx]
  exact congrFun (hp.localInverseAt_symm s) x

end Charts

section Manifold

variable {M G H 𝕜 E : Type*} [TopologicalSpace M] [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [TopologicalSpace H] [ChartedSpace H M]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The exact smooth-compatibility obligation for the canonical quotient charts. -/
public def QuotientChartContDiff (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) : Prop :=
  ∀ q q' : OrbitQuotient (M := M) (G := G),
    ContDiffOn 𝕜 n
      (I ∘
        (quotientChart (M := M) (G := G) (H := H) q).symm ≫ₕ
          quotientChart (M := M) (G := G) (H := H) q' ∘ I.symm)
      (I.symm ⁻¹'
        ((quotientChart (M := M) (G := G) (H := H) q).symm ≫ₕ
          quotientChart (M := M) (G := G) (H := H) q').source ∩ Set.range I)

/-- Smooth translations make the canonical quotient charts smoothly compatible. -/
public theorem quotientChartContDiff_of_contMDiff_smul
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n M]
    (hsmul : ∀ g : G, ContMDiff I I n (fun x : M ↦ g • x)) :
    QuotientChartContDiff (M := M) (G := G) I n := by
  intro q q' z hz
  let s := quotientSection (M := M) (G := G) q
  let s' := quotientSection (M := M) (G := G) q'
  let e := quotientChart (M := M) (G := G) (H := H) q
  let e' := quotientChart (M := M) (G := G) (H := H) q'
  let t := e.symm.trans e'
  let T := I.symm ⁻¹' t.source ∩ Set.range I
  let u : E → M := (chartAt H s).symm ∘ I.symm
  let v : E → M := (chartAt H s').symm ∘ t ∘ I.symm
  change z ∈ T at hz
  change ContDiffWithinAt 𝕜 n (I ∘ t ∘ I.symm) T z
  have hdata (y : E) (hy : y ∈ T) :
      u y ∈ (chartAt H s).source ∧ v y ∈ (chartAt H s').source ∧
        chartAt H s (u y) = I.symm y ∧ chartAt H s' (v y) = t (I.symm y) ∧
          quotientProjection (M := M) (G := G) (u y) =
            quotientProjection (M := M) (G := G) (v y) := by
    have hyt : I.symm y ∈ t.source := hy.1
    have hytrans : I.symm y ∈ e.symm.source ∧ e.symm (I.symm y) ∈ e'.source := by
      exact hyt
    have hyetarget : I.symm y ∈ e.target := hytrans.1
    have hycharttarget : I.symm y ∈ (chartAt H s).target := by
      exact hyetarget.1
    have hutarget : u y ∈ (chartAt H s).source := by
      exact (chartAt H s).symm.map_source hycharttarget
    have huchart : chartAt H s (u y) = I.symm y := by
      exact (chartAt H s).right_inv hycharttarget
    have htytarget : t (I.symm y) ∈ e'.target := by
      exact e'.map_source hytrans.2
    have hvcharttarget : t (I.symm y) ∈ (chartAt H s').target := by
      exact htytarget.1
    have hvsource : v y ∈ (chartAt H s').source := by
      exact (chartAt H s').symm.map_source hvcharttarget
    have hvchart : chartAt H s' (v y) = t (I.symm y) := by
      exact (chartAt H s').right_inv hvcharttarget
    have hpu : quotientProjection (M := M) (G := G) (u y) = e.symm (I.symm y) := by
      rw [← huchart]
      exact (quotientChart_symm_apply_chart q hutarget).symm
    have hpv : quotientProjection (M := M) (G := G) (v y) = e.symm (I.symm y) := by
      rw [← quotientChart_symm_apply_chart q' hvsource, hvchart]
      exact e'.left_inv hytrans.2
    exact ⟨hutarget, hvsource, huchart, hvchart, hpu.trans hpv.symm⟩
  have hucont : ContinuousOn u T := by
    change ContinuousOn ((chartAt H s).symm ∘ I.symm) T
    exact (chartAt H s).symm.continuousOn.comp I.continuous_symm.continuousOn fun y hy ↦ by
      rw [← (hdata y hy).2.2.1]
      exact (chartAt H s).map_source (hdata y hy).1
  have htcont : ContinuousOn (t ∘ I.symm) T :=
    t.continuousOn.comp I.continuous_symm.continuousOn fun _ hy ↦ hy.1
  have hvcont : ContinuousOn v T := by
    change ContinuousOn ((chartAt H s').symm ∘ t ∘ I.symm) T
    exact (chartAt H s').symm.continuousOn.comp htcont fun y hy ↦ by
      change t (I.symm y) ∈ (chartAt H s').target
      rw [← (hdata y hy).2.2.2.1]
      exact (chartAt H s').map_source (hdata y hy).2.1
  let hp : IsQuotientCoveringMap (quotientProjection (M := M) (G := G)) G :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  have horbit : v z ∈ MulAction.orbit G (u z) :=
    hp.apply_eq_iff_mem_orbit.mp (hdata z hz).2.2.2.2.symm
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
  have hproj : quotientProjection (M := M) (G := G) ∘ u =ᶠ[nhdsWithin z T]
      quotientProjection (M := M) (G := G) ∘ v := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hdata y hy).2.2.2.2
  have huv : v =ᶠ[nhdsWithin z T] fun y ↦ g • u y :=
    eventuallyEq_const_smul_of_tendsto g (hucont z hz).tendsto
      (hvcont z hz).tendsto hg.symm hproj
  have hzcoord : extChartAt I s (u z) = z := by
    change I (chartAt H s (u z)) = z
    rw [(hdata z hz).2.2.1]
    exact I.right_inv hz.2
  have hgsource : g • u z ∈ (chartAt H s').source := by
    rw [hg]
    exact (hdata z hz).2.1
  have hsmooth : ContDiffWithinAt 𝕜 n
      (extChartAt I s' ∘ (fun x : M ↦ g • x) ∘ (extChartAt I s).symm)
      (Set.range I) z := by
    rw [← hzcoord]
    exact ((contMDiffAt_iff_of_mem_source (hdata z hz).1 hgsource).mp
      ((hsmul g) (u z))).2
  have heq : I ∘ t ∘ I.symm =ᶠ[nhdsWithin z T]
      extChartAt I s' ∘ (fun x : M ↦ g • x) ∘ (extChartAt I s).symm := by
    filter_upwards [huv, self_mem_nhdsWithin] with y hyuv hy
    change I (t (I.symm y)) = I (chartAt H s' (g • u y))
    rw [← (hdata y hy).2.2.2.1, hyuv]
  exact (hsmooth.mono fun _ hy ↦ hy.2).congr_of_eventuallyEq heq
    (heq.self_of_nhdsWithin hz)

/-- Smooth compatibility of the canonical quotient charts gives the quotient its manifold
structure. This reduces the arbitrary-atlas obligation in `isManifold_of_contDiffOn` to the
specific charts produced by `MulAction.instChartedSpaceQuotient`. -/
public theorem isManifold_orbitQuotient_of_quotientChartContDiff
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (h : QuotientChartContDiff (M := M) (G := G) I n) :
    IsManifold I n (OrbitQuotient (M := M) (G := G)) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rw [quotient_atlas] at he he'
  rcases he with ⟨q, rfl⟩
  rcases he' with ⟨q', rfl⟩
  exact h q q'

/-- A free properly discontinuous action by `C^n` translations gives the orbit quotient a
manifold structure. -/
public theorem isManifold_orbitQuotient_of_contMDiff_smul
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n M]
    (hsmul : ∀ g : G, ContMDiff I I n (fun x : M ↦ g • x)) :
    IsManifold I n (OrbitQuotient (M := M) (G := G)) :=
  isManifold_orbitQuotient_of_quotientChartContDiff I n
    (quotientChartContDiff_of_contMDiff_smul I n hsmul)

variable (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n M]
  [IsManifold I n (OrbitQuotient (M := M) (G := G))]

/-- At a chosen orbit representative, the quotient projection is a local diffeomorphism. -/
public theorem quotientProjection_isLocalDiffeomorphAt_section
    (q : OrbitQuotient (M := M) (G := G)) :
    IsLocalDiffeomorphAt I I n (quotientProjection (M := M) (G := G))
      (quotientSection q) := by
  let s := quotientSection (M := M) (G := G) q
  let b : OpenPartialHomeomorph (OrbitQuotient (M := M) (G := G)) M :=
    (chartAt H q).trans (chartAt H s).symm
  have hb : ContMDiffOn I I n b b.source := by
    change ContMDiffOn I I n ((chartAt H s).symm ∘ chartAt H q)
      ((chartAt H q).source ∩ chartAt H q ⁻¹' (chartAt H s).target)
    exact contMDiffOn_chart_symm.comp
      (contMDiffOn_chart.mono Set.inter_subset_left) Set.inter_subset_right
  have hbsymm : ContMDiffOn I I n b.symm b.target := by
    change ContMDiffOn I I n ((chartAt H q).symm ∘ chartAt H s)
      ((chartAt H s).source ∩ chartAt H s ⁻¹' (chartAt H q).target)
    exact contMDiffOn_chart_symm.comp
      (contMDiffOn_chart.mono Set.inter_subset_left) Set.inter_subset_right
  have heq : Set.EqOn (quotientProjection (M := M) (G := G)) b.symm b.target := by
    intro x hx
    change quotientProjection (M := M) (G := G) x =
      (chartAt H q).symm (chartAt H s x)
    rw [← quotientChart_eq_chartAt]
    exact (quotientChart_symm_apply_chart q hx.1).symm
  let φ : PartialDiffeomorph I I M (OrbitQuotient (M := M) (G := G)) n :=
    { toFun := quotientProjection (M := M) (G := G)
      invFun := b
      source := b.target
      target := b.source
      map_source' := fun x hx ↦ by
        rw [heq hx]
        exact b.symm.map_source hx
      map_target' := fun _ hx ↦ b.map_source hx
      left_inv' := fun x hx ↦ by
        rw [heq hx]
        exact b.right_inv hx
      right_inv' := fun x hx ↦ by
        rw [heq (b.map_source hx)]
        exact b.left_inv hx
      open_source := b.open_target
      open_target := b.open_source
      contMDiffOn_toFun := hbsymm.congr heq
      contMDiffOn_invFun := hb }
  apply φ.isLocalDiffeomorphAt
  change s ∈ b.target
  have hqsource : q ∈ b.source := by
    change q ∈ (chartAt H q).source ∧ chartAt H q q ∈ (chartAt H s).target
    refine ⟨ChartedSpace.mem_chart_source q, ?_⟩
    rw [← quotientChart_eq_chartAt, quotientChart_apply_self]
    exact (chartAt H s).map_source (ChartedSpace.mem_chart_source s)
  have hbq : b q = s := by
    change (chartAt H s).symm (chartAt H q q) = s
    rw [← quotientChart_eq_chartAt, quotientChart_apply_self]
    exact (chartAt H s).left_inv (ChartedSpace.mem_chart_source s)
  rw [← hbq]
  exact b.map_source hqsource

/-- If every group element acts by a `C^n` diffeomorphism, the quotient projection is a local
diffeomorphism everywhere. -/
public theorem quotientProjection_isLocalDiffeomorph
    (hsmul : ∀ g : G, ContMDiff I I n (fun x : M ↦ g • x)) :
    IsLocalDiffeomorph I I n (quotientProjection (M := M) (G := G)) := by
  intro x
  let q := quotientProjection (M := M) (G := G) x
  let s := quotientSection (M := M) (G := G) q
  have hpxs : quotientProjection (M := M) (G := G) x =
      quotientProjection (M := M) (G := G) s := by
    rw [quotientProjection_section]
  have horbit : x ∈ MulAction.orbit G s := by
    rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
    exact hpxs
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
  let Φ : Diffeomorph I I M M n :=
    Diffeomorph.mk (Homeomorph.smul (g⁻¹)).toEquiv (hsmul g⁻¹) (by
      convert hsmul g using 1
      funext y
      simp)
  have hΦ : IsLocalDiffeomorphAt I I n Φ x := Φ.isLocalDiffeomorph x
  have hΦx : Φ x = s := by
    dsimp only [Φ]
    change g⁻¹ • x = s
    rw [← hg]
    simp
  have hlocal : IsLocalDiffeomorphAt I I n
      (quotientProjection (M := M) (G := G) ∘ Φ) x := by
    apply hΦ.comp I (OrbitQuotient (M := M) (G := G))
    rw [hΦx]
    exact quotientProjection_isLocalDiffeomorphAt_section I n q
  have heq : quotientProjection (M := M) (G := G) ∘ Φ =
      quotientProjection (M := M) (G := G) := by
    funext y
    apply Quotient.sound
    change (MulAction.orbitRel G M) (Φ y) y
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨g⁻¹, rfl⟩
  rw [← heq]
  exact hlocal

/-- For nonzero differentiability order, the quotient projection is manifold-differentiable. -/
public theorem quotientProjection_mdifferentiable (hn : n ≠ 0)
    (hsmul : ∀ g : G, ContMDiff I I n (fun x : M ↦ g • x)) :
    MDifferentiable I I (quotientProjection (M := M) (G := G)) :=
  (quotientProjection_isLocalDiffeomorph I n hsmul).mdifferentiable hn

end Manifold

section Combined

variable {M G H 𝕜 E : Type*} [TopologicalSpace M] [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [TopologicalSpace H] [ChartedSpace H M]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H)

/-- The canonical-chart compatibility condition, together with a smooth group action, gives both
the quotient manifold and its local-diffeomorphism projection. -/
public theorem orbitQuotient_isManifold_and_projection_isLocalDiffeomorph
    (n : WithTop ℕ∞) [IsManifold I n M]
    (hcharts : QuotientChartContDiff (M := M) (G := G) I n)
    (hsmul : ∀ g : G, ContMDiff I I n (fun x : M ↦ g • x)) :
    IsManifold I n (OrbitQuotient (M := M) (G := G)) ∧
      IsLocalDiffeomorph I I n (quotientProjection (M := M) (G := G)) := by
  have hmanifold := isManifold_orbitQuotient_of_quotientChartContDiff I n hcharts
  refine ⟨hmanifold, ?_⟩
  let _ : IsManifold I n (OrbitQuotient (M := M) (G := G)) := hmanifold
  exact quotientProjection_isLocalDiffeomorph I n hsmul

/-- A free properly discontinuous action by `C^n` translations gives a quotient manifold whose
projection is a local diffeomorphism. -/
public theorem orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    (n : WithTop ℕ∞) [IsManifold I n M]
    (hsmul : ∀ g : G, ContMDiff I I n (fun x : M ↦ g • x)) :
    IsManifold I n (OrbitQuotient (M := M) (G := G)) ∧
      IsLocalDiffeomorph I I n (quotientProjection (M := M) (G := G)) :=
  orbitQuotient_isManifold_and_projection_isLocalDiffeomorph I n
    (quotientChartContDiff_of_contMDiff_smul I n hsmul) hsmul

/-- At differentiability order one, the preceding theorem gives a complex-manifold quotient and a
locally holomorphic quotient projection. -/
public theorem orbitQuotient_isManifold_and_projection_mdifferentiable
    [IsManifold I 1 M]
    (hcharts : QuotientChartContDiff (M := M) (G := G) I 1)
    (hsmul : ∀ g : G, ContMDiff I I 1 (fun x : M ↦ g • x)) :
    IsManifold I 1 (OrbitQuotient (M := M) (G := G)) ∧
      MDifferentiable I I (quotientProjection (M := M) (G := G)) := by
  have h := orbitQuotient_isManifold_and_projection_isLocalDiffeomorph I 1 hcharts hsmul
  refine ⟨h.1, ?_⟩
  exact h.2.mdifferentiable one_ne_zero

/-- At order one, a free properly discontinuous action by smooth translations gives a complex
manifold quotient and a locally holomorphic quotient projection. -/
public theorem orbitQuotient_isManifold_and_projection_mdifferentiable_of_contMDiff_smul
    [IsManifold I 1 M] (hsmul : ∀ g : G, ContMDiff I I 1 (fun x : M ↦ g • x)) :
    IsManifold I 1 (OrbitQuotient (M := M) (G := G)) ∧
      MDifferentiable I I (quotientProjection (M := M) (G := G)) :=
  orbitQuotient_isManifold_and_projection_mdifferentiable I
    (quotientChartContDiff_of_contMDiff_smul I 1 hsmul) hsmul

end Combined

end

end SphereSixComplex.Geometry
