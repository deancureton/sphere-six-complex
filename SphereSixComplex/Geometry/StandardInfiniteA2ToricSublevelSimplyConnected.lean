/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCarrierGeometry
import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Subpath

/-!
# Simply connected sublevels of the infinite `A₂` toric carrier

The proof uses the affine toric-chart cover.  Each chart sublevel is star convex, every pairwise
intersection is path connected by density of the common algebraic torus, and all chart sublevels
contain one common torus point.  The open-cover argument and the logarithmic-coordinate argument
are adapted from Boris Alexeev's Apache-2.0 `HopfProblem/Solution.lean`.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The height sublevel in one raw affine chart. -/
public def affineHeightSublevel (r : ℝ) : Set RawCoordinates :=
  {z | ‖rawHeight z‖ < r}

public theorem affineHeightSublevel_isOpen (r : ℝ) : IsOpen (affineHeightSublevel r) := by
  apply isOpen_lt
  · unfold rawHeight
    fun_prop
  · fun_prop

public theorem affineHeightSublevel_starConvex (r : ℝ) :
    StarConvex ℝ 0 (affineHeightSublevel r) := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  simp only [smul_zero, zero_add]
  change ‖rawHeight (b • z)‖ < r
  have he : ‖rawHeight (b • z)‖ = b ^ 3 * ‖rawHeight z‖ := by
    simp only [rawHeight, Pi.smul_apply, norm_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hb]
    ring
  rw [he]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hb hb1)).trans_lt hz

public theorem affineHeightSublevel_isSimplyConnected {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (affineHeightSublevel r) := by
  let _ :=
    (affineHeightSublevel_starConvex r).contractibleSpace
      (show (affineHeightSublevel r).Nonempty from
        ⟨0, by simpa [affineHeightSublevel, rawHeight] using hr⟩)
  exact SimplyConnectedSpace.ofContractible _

/-- Logarithmic coordinates for the common-torus part of an affine sublevel. -/
public def logarithmicHeightSublevel (r : ℝ) : Set RawCoordinates :=
  {z | (z 0 + z 1 + z 2).re < Real.log r}

public theorem logarithmicHeightSublevel_convex (r : ℝ) :
    Convex ℝ (logarithmicHeightSublevel r) := by
  apply convex_halfSpace_lt
  constructor
  · intro z w
    simp only [Pi.add_apply, Complex.add_re]
    ring
  · intro s z
    simp only [Pi.smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul]
    ring

public theorem logarithmicHeightSublevel_nonempty (r : ℝ) :
    (logarithmicHeightSublevel r).Nonempty := by
  refine ⟨![((Real.log r - 1 : ℝ) : ℂ), 0, 0], ?_⟩
  simp [logarithmicHeightSublevel]

/-- Coordinatewise complex exponential. -/
public def coordinateExp (z : RawCoordinates) : RawCoordinates := fun j ↦ Complex.exp (z j)

public theorem coordinateExp_continuous : Continuous coordinateExp :=
  continuous_pi fun j ↦ Complex.continuous_exp.comp (continuous_apply j)

public theorem range_coordinateExp : Set.range coordinateExp = coordinateTorus := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩ j
    exact Complex.exp_ne_zero (w j)
  · intro hz
    refine ⟨fun j ↦ Complex.log (z j), ?_⟩
    funext j
    exact Complex.exp_log (hz j)

public theorem norm_rawHeight_coordinateExp (z : RawCoordinates) :
    ‖rawHeight (coordinateExp z)‖ = Real.exp (z 0 + z 1 + z 2).re := by
  simp only [rawHeight, coordinateExp, ← Complex.exp_add, Complex.norm_exp]

public theorem coordinateExp_mem_affineHeightSublevel_iff {r : ℝ} (hr : 0 < r)
    (z : RawCoordinates) :
    coordinateExp z ∈ affineHeightSublevel r ↔ z ∈ logarithmicHeightSublevel r := by
  change ‖rawHeight (coordinateExp z)‖ < r ↔ (z 0 + z 1 + z 2).re < Real.log r
  rw [norm_rawHeight_coordinateExp]
  exact (Real.lt_log_iff_exp_lt hr).symm

public theorem coordinateExp_image_logarithmicHeightSublevel {r : ℝ} (hr : 0 < r) :
    coordinateExp '' logarithmicHeightSublevel r =
      coordinateTorus ∩ affineHeightSublevel r := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun j ↦ Complex.exp_ne_zero _,
      (coordinateExp_mem_affineHeightSublevel_iff hr w).mpr hw⟩
  · rintro ⟨hzT, hz⟩
    obtain ⟨w, rfl⟩ := range_coordinateExp.symm ▸ hzT
    exact ⟨w, (coordinateExp_mem_affineHeightSublevel_iff hr w).mp hz, rfl⟩

public theorem coordinateTorus_inter_affineHeightSublevel_isPathConnected
    {r : ℝ} (hr : 0 < r) :
    IsPathConnected (coordinateTorus ∩ affineHeightSublevel r) := by
  rw [← coordinateExp_image_logarithmicHeightSublevel hr]
  exact
    ((logarithmicHeightSublevel_convex r).isPathConnected
      (logarithmicHeightSublevel_nonempty r)).image coordinateExp_continuous

public theorem monomialDomain_inter_affineHeightSublevel_isPathConnected
    (A : Matrix (Fin 3) (Fin 3) ℤ) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (monomialDomain A ∩ affineHeightSublevel r) := by
  apply ((monomialDomain_isOpen A).inter
    (affineHeightSublevel_isOpen r)).isConnected_iff_isPathConnected.mp
  apply (coordinateTorus_inter_affineHeightSublevel_isPathConnected hr).isConnected.subset_closure
  · exact fun _ hz ↦ ⟨coordinateTorus_subset_monomialDomain A hz.1, hz.2⟩
  · intro z hz
    simpa only [Set.inter_comm] using
      (coordinateTorus_isDense.open_subset_closure_inter
        (affineHeightSublevel_isOpen r) hz.2)

/-- The image of one affine height sublevel in the glued carrier. -/
public def carrierAffineHeightSublevel (a : ChartIndex) (r : ℝ) : Set Carrier :=
  inclusion a '' affineHeightSublevel r

public theorem carrierAffineHeightSublevel_isOpen (a : ChartIndex) (r : ℝ) :
    IsOpen (carrierAffineHeightSublevel a r) :=
  (inclusion_isOpenEmbedding a).isOpenMap _ (affineHeightSublevel_isOpen r)

public theorem carrierAffineHeightSublevel_isSimplyConnected
    (a : ChartIndex) {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (carrierAffineHeightSublevel a r) :=
  (inclusion_isOpenEmbedding a).isEmbedding.isSimplyConnected_image.mpr
    (affineHeightSublevel_isSimplyConnected hr)

public theorem carrierAffineHeightSublevels_inter (a b : ChartIndex) (r : ℝ) :
    carrierAffineHeightSublevel a r ∩ carrierAffineHeightSublevel b r =
      inclusion a '' (monomialDomain (transitionMatrix a b) ∩ affineHeightSublevel r) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, ⟨w, _, hw⟩⟩
    refine ⟨z, ⟨?_, hz⟩, rfl⟩
    simpa only [chartChange_source] using
      ((inclusion_eq_iff a b z w).mp hw.symm).1
  · rintro ⟨z, ⟨hzD, hz⟩, rfl⟩
    have hzS : z ∈ (chartChange a b).source := by
      simpa only [chartChange_source] using hzD
    refine ⟨⟨z, hz, rfl⟩, chartChange a b z, ?_, ?_⟩
    · change ‖rawHeight (chartChange a b z)‖ < r
      have he := rawHeight_chartChange a b hzS
      change rawHeight (chartChange a b z) = rawHeight z at he
      rw [he]
      exact hz
    · exact ((inclusion_eq_iff a b z _).mpr ⟨hzS, rfl⟩).symm

public theorem carrierAffineHeightSublevels_inter_isPathConnected
    (a b : ChartIndex) {r : ℝ} (hr : 0 < r) :
    IsPathConnected
      (carrierAffineHeightSublevel a r ∩ carrierAffineHeightSublevel b r) := by
  rw [carrierAffineHeightSublevels_inter]
  exact
    (monomialDomain_inter_affineHeightSublevel_isPathConnected _ hr).image
      (inclusion_isOpenEmbedding a).continuous

public theorem carrierHeightSublevel_eq_iUnion (r : ℝ) :
    carrierHeight ⁻¹' Metric.ball 0 r =
      ⋃ a : ChartIndex, carrierAffineHeightSublevel a r := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
    refine Set.mem_iUnion.mpr ⟨a, z, ?_, rfl⟩
    change ‖rawHeight z‖ < r
    change carrierHeight (inclusion a z) ∈ Metric.ball 0 r at hx
    simpa only [carrierHeight_inclusion, Metric.mem_ball, dist_zero_right] using hx
  · intro hx
    obtain ⟨a, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    change carrierHeight (inclusion a z) ∈ Metric.ball 0 r
    simpa only [affineHeightSublevel, Set.mem_ofPred_eq, carrierHeight_inclusion,
      Metric.mem_ball, dist_zero_right] using hz

namespace SimplyConnectedOpenCover

theorem homotopic_of_mem {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsSimplyConnected s) {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ s)
    (hq : ∀ t, q t ∈ s) : Path.Homotopic p q := by
  let _ : SimplyConnectedSpace s := hs
  have hx : x ∈ s := by simpa using hp 0
  have hy : y ∈ s := by simpa using hp 1
  let p' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact p.source
      target' := by apply Subtype.ext; exact p.target }
  let q' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact q.source
      target' := by apply Subtype.ext; exact q.target }
  have h :=
    (SimplyConnectedSpace.paths_homotopic p' q').map
      (⟨Subtype.val, continuous_subtype_val⟩ : ContinuousMap s X)
  have hp' : p'.map continuous_subtype_val = p := by ext t; rfl
  have hq' : q'.map continuous_subtype_val = q := by ext t; rfl
  exact hp' ▸ hq' ▸ h

theorem trans_mem {X : Type*} [TopologicalSpace X] {s : Set X} {x y z : X}
    (p : Path x y) (q : Path y z) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    ∀ t, p.trans q t ∈ s := by
  apply Set.range_subset_iff.mp
  rw [Path.trans_range]
  exact Set.union_subset (Set.range_subset_iff.mpr hp) (Set.range_subset_iff.mpr hq)

noncomputable def chartPath {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i)
    (i : ι) (x : X) (hx : x ∈ U i) : Path o x :=
  ((hs i).isPathConnected.joinedIn o (ho i) x hx).somePath

theorem chartPath_mem {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i)
    (i : ι) (x : X) (hx : x ∈ U i) (t : unitInterval) :
    chartPath U hs o ho i x hx t ∈ U i :=
  JoinedIn.somePath_mem _ t

theorem chartPath_homotopic {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i)
    (hinter : ∀ i j, IsPathConnected (U i ∩ U j)) (i j : ι) (x : X)
    (hi : x ∈ U i) (hj : x ∈ U j) :
    Path.Homotopic (chartPath U hs o ho i x hi) (chartPath U hs o ho j x hj) := by
  let h := (hinter i j).joinedIn o ⟨ho i, ho j⟩ x ⟨hi, hj⟩
  exact
    (homotopic_of_mem (hs i) _ h.somePath (chartPath_mem U hs o ho i x hi)
      (fun t ↦ (h.somePath_mem t).1)).trans
    (homotopic_of_mem (hs j) h.somePath _ (fun t ↦ (h.somePath_mem t).2)
      (chartPath_mem U hs o ho j x hj))

theorem quotient_cast_trans {X : Type*} [TopologicalSpace X]
    {o x y o' x' y' : X} (p : Path.Homotopic.Quotient o x)
    (q : Path.Homotopic.Quotient x y) (ho : o' = o) (hx : x' = x) (hy : y' = y) :
    (p.trans q).cast ho hy = (p.cast ho hx).trans (q.cast hx hy) := by
  cases ho
  cases hx
  cases hy
  simp

theorem quotient_cast_section {X : Type*} [TopologicalSpace X] {o : X}
    (F : ∀ z, Path.Homotopic.Quotient o z) {x y : X} (h : x = y) :
    (F y).cast rfl h = F x := by
  cases h
  simp

theorem section_subpath_zero_one {X : Type*} [TopologicalSpace X] {o x y : X}
    (F : ∀ z, Path.Homotopic.Quotient o z) (p : Path x y)
    (h :
      Path.Homotopic.Quotient.trans (F (p 0))
          (Path.Homotopic.Quotient.mk (p.subpath 0 1)) = F (p 1)) :
    Path.Homotopic.Quotient.trans (F x) (Path.Homotopic.Quotient.mk p) = F y := by
  have hp :
      (Path.Homotopic.Quotient.mk (p.subpath 0 1)).cast p.source.symm p.target.symm =
        Path.Homotopic.Quotient.mk p := by
    rw [← Path.Homotopic.Quotient.mk_cast, Path.subpath_zero_one]
    rfl
  have h' := congrArg (fun q : Path.Homotopic.Quotient o (p 1) ↦ q.cast rfl p.target.symm) h
  rw [quotient_cast_trans _ _ rfl p.source.symm p.target.symm,
    quotient_cast_section F p.source.symm, hp,
    quotient_cast_section F p.target.symm] at h'
  exact h'

theorem section_trans_of_open_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (o : X)
    (F : ∀ x, Path.Homotopic.Quotient o x)
    (hF : ∀ i {x y : X} (p : Path x y), (∀ t, p t ∈ U i) →
      Path.Homotopic.Quotient.trans (F x) (Path.Homotopic.Quotient.mk p) = F y)
    {x y : X} (p : Path x y) :
    Path.Homotopic.Quotient.trans (F x) (Path.Homotopic.Quotient.mk p) = F y := by
  have hpre : Set.univ ⊆ ⋃ i, p ⁻¹' U i := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i ↦ (hopen i).preimage p.continuous) hpre
  have hwalk :
      ∀ k : ℕ,
        Path.Homotopic.Quotient.trans (F (p 0))
            (Path.Homotopic.Quotient.mk (p.subpath 0 (t k))) = F (p (t k)) := by
    intro k
    induction k with
    | zero =>
        rw [ht0, Path.subpath_self, Path.Homotopic.Quotient.mk_refl,
          Path.Homotopic.Quotient.trans_refl]
    | succ k ih =>
        obtain ⟨i, hi⟩ := hsub k
        have hmem : ∀ s, p.subpath (t k) (t (k + 1)) s ∈ U i := by
          apply Set.range_subset_iff.mp
          rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ k))]
          exact Set.image_subset_iff.mpr hi
        have hconcat :
            Path.Homotopic.Quotient.trans
                (Path.Homotopic.Quotient.mk (p.subpath 0 (t k)))
                (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) =
              Path.Homotopic.Quotient.mk (p.subpath 0 (t (k + 1))) := by
          rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
          exact ⟨Path.Homotopy.subpathTransSubpath p 0 (t k) (t (k + 1))⟩
        calc
          Path.Homotopic.Quotient.trans (F (p 0))
                (Path.Homotopic.Quotient.mk (p.subpath 0 (t (k + 1)))) =
              Path.Homotopic.Quotient.trans
                (Path.Homotopic.Quotient.trans (F (p 0))
                  (Path.Homotopic.Quotient.mk (p.subpath 0 (t k))))
                (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) := by
            rw [Path.Homotopic.Quotient.trans_assoc, hconcat]
          _ = Path.Homotopic.Quotient.trans (F (p (t k)))
                (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) := by rw [ih]
          _ = F (p (t (k + 1))) := hF i _ hmem
  have h := hwalk n
  rw [hn n le_rfl] at h
  exact section_subpath_zero_one F p h

theorem simplyConnectedSpace_of_open_cover {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    (hsimply : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i)
    (hinter : ∀ i j, IsPathConnected (U i ∩ U j)) : SimplyConnectedSpace X := by
  classical
  have hcov : ∀ x : X, ∃ i, x ∈ U i := by
    intro x
    apply Set.mem_iUnion.mp
    rw [hcover]
    trivial
  let idx (x : X) : ι := (hcov x).choose
  have hidx (x : X) : x ∈ U (idx x) := (hcov x).choose_spec
  let c (x : X) : Path o x := chartPath U hsimply o ho (idx x) x (hidx x)
  let F (x : X) : Path.Homotopic.Quotient o x := Path.Homotopic.Quotient.mk (c x)
  have hFi (i : ι) (x : X) (hx : x ∈ U i) :
      F x = Path.Homotopic.Quotient.mk (chartPath U hsimply o ho i x hx) := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact chartPath_homotopic U hsimply o ho hinter (idx x) i x (hidx x) hx
  have hF (i : ι) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i) :
      (F x).trans (Path.Homotopic.Quotient.mk p) = F y := by
    have hx : x ∈ U i := by simpa using hp 0
    have hy : y ∈ U i := by simpa using hp 1
    rw [hFi i x hx, hFi i y hy, ← Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.eq]
    exact
      homotopic_of_mem (hsimply i) _ _
        (trans_mem _ _ (chartPath_mem U hsimply o ho i x hx) hp)
        (chartPath_mem U hsimply o ho i y hy)
  have hpc : PathConnectedSpace X :=
    { nonempty := ⟨o⟩
      joined := fun x y ↦ ⟨(c x).symm.trans (c y)⟩ }
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨hpc, ?_⟩
  intro x y p q
  have hp := section_trans_of_open_cover U hopen hcover o F hF p
  have hq := section_trans_of_open_cover U hopen hcover o F hF q
  apply Path.Homotopic.Quotient.eq.mp
  have h := congrArg (fun r : Path.Homotopic.Quotient o y ↦ (F x).symm.trans r)
    (hp.trans hq.symm)
  simpa only [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans] using h

end SimplyConnectedOpenCover

/-- A torus point of height `r / 2`, used as a common point of all affine sublevel charts. -/
public def commonSublevelTorusPoint (r : ℝ) (hr : 0 < r) : DenseTorus :=
  ![1, 1, Units.mk0 ((r / 2 : ℝ) : ℂ) (by
    exact_mod_cast (half_pos hr).ne')]

/-- Every affine chart sublevel contains the same dense-torus point. -/
public theorem commonSublevelTorusPoint_mem_carrierAffineHeightSublevel
    (a : ChartIndex) {r : ℝ} (hr : 0 < r) :
    carrierTorusEmbedding (commonSublevelTorusPoint r hr) ∈
      carrierAffineHeightSublevel a r := by
  refine ⟨torusChartCoordinates a (commonSublevelTorusPoint r hr), ?_, ?_⟩
  · change ‖rawHeight (torusChartCoordinates a (commonSublevelTorusPoint r hr))‖ < r
    rw [← carrierHeight_inclusion]
    rw [← carrierTorusEmbedding_eq_inclusion_torusChartCoordinates]
    rw [carrierHeight_torus]
    simpa [commonSublevelTorusPoint, abs_of_pos hr] using half_lt_self hr
  · exact (carrierTorusEmbedding_eq_inclusion_torusChartCoordinates a _).symm

/-- One affine member of the cover of the carrier height sublevel. -/
public def carrierHeightSublevelChart (r : ℝ) (a : ChartIndex) :
    Set {p : Carrier // p ∈ carrierHeight ⁻¹' Metric.ball 0 r} :=
  Subtype.val ⁻¹' carrierAffineHeightSublevel a r

public theorem carrierHeightSublevelChart_isOpen (r : ℝ) (a : ChartIndex) :
    IsOpen (carrierHeightSublevelChart r a) :=
  (carrierAffineHeightSublevel_isOpen a r).preimage continuous_subtype_val

public theorem carrierHeightSublevelChart_isSimplyConnected
    {r : ℝ} (hr : 0 < r) (a : ChartIndex) :
    IsSimplyConnected (carrierHeightSublevelChart r a) := by
  apply Topology.IsEmbedding.subtypeVal.isSimplyConnected_image.mp
  have he :
      (Subtype.val : {p : Carrier // p ∈ carrierHeight ⁻¹' Metric.ball 0 r} → Carrier) ''
          carrierHeightSublevelChart r a = carrierAffineHeightSublevel a r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      rw [carrierHeightSublevel_eq_iUnion]
      exact Set.mem_iUnion.mpr ⟨a, hx⟩
  rw [he]
  exact carrierAffineHeightSublevel_isSimplyConnected a hr

public theorem carrierHeightSublevelCharts_inter_isPathConnected
    {r : ℝ} (hr : 0 < r) (a b : ChartIndex) :
    IsPathConnected
      (carrierHeightSublevelChart r a ∩ carrierHeightSublevelChart r b) := by
  change IsPathConnected
    ((Subtype.val : {p : Carrier // p ∈ carrierHeight ⁻¹' Metric.ball 0 r} → Carrier) ⁻¹'
      (carrierAffineHeightSublevel a r ∩ carrierAffineHeightSublevel b r))
  exact
    (carrierAffineHeightSublevels_inter_isPathConnected a b hr).preimage_coe
      (Set.inter_subset_left.trans (by
        rw [carrierHeightSublevel_eq_iUnion]
        exact Set.subset_iUnion (fun c ↦ carrierAffineHeightSublevel c r) a))

public theorem carrierHeightSublevelCharts_cover (r : ℝ) :
    ⋃ a : ChartIndex, carrierHeightSublevelChart r a = Set.univ := by
  unfold carrierHeightSublevelChart
  rw [← Set.preimage_iUnion, ← carrierHeightSublevel_eq_iUnion]
  ext x
  simp

/-- Every positive height sublevel of the explicit infinite `A₂` toric carrier is simply
connected. -/
public theorem carrierHeightSublevel_simplyConnected (r : ℝ) (hr : 0 < r) :
    SimplyConnectedSpace {p : Carrier // p ∈ carrierHeight ⁻¹' Metric.ball 0 r} := by
  let x : Carrier := carrierTorusEmbedding (commonSublevelTorusPoint r hr)
  have hxChart : ∀ a, x ∈ carrierAffineHeightSublevel a r :=
    fun a ↦ commonSublevelTorusPoint_mem_carrierAffineHeightSublevel a hr
  have hxSublevel : x ∈ carrierHeight ⁻¹' Metric.ball 0 r := by
    rw [carrierHeightSublevel_eq_iUnion]
    exact Set.mem_iUnion.mpr ⟨baseChart, hxChart baseChart⟩
  exact SimplyConnectedOpenCover.simplyConnectedSpace_of_open_cover
    (carrierHeightSublevelChart r)
    (carrierHeightSublevelChart_isOpen r)
    (carrierHeightSublevelCharts_cover r)
    (carrierHeightSublevelChart_isSimplyConnected hr)
    ⟨x, hxSublevel⟩
    (fun a ↦ hxChart a)
    (carrierHeightSublevelCharts_inter_isPathConnected hr)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
