module

public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.CrossingField
public import DifferentialGeometry.Topology.Morse.Rearrangement.EqualIndexPosition
public import DifferentialGeometry.Topology.Morse.Cancellation.Setup.Isolate
public import DifferentialGeometry.Topology.Homology.Spheres.SphereHomology
public import DifferentialGeometry.Topology.Homology.Relative.PairVanishing
public import DifferentialGeometry.Topology.Homology.Naturality
public import DifferentialGeometry.Topology.Homology.Relative.HomotopyInvariance
public import DifferentialGeometry.Topology.Homology.MayerVietoris.OpenRelative
public import DifferentialGeometry.Topology.Homology.Local.LocalHomology
public import DifferentialGeometry.Topology.Manifold.GeneralPosition.GeneralPosition
public import DifferentialGeometry.Topology.ClosedBall.UnitDisk
public import DifferentialGeometry.Topology.Morse.Cancellation.FirstCancellation
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

set_option autoImplicit false

open Set Filter
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

noncomputable section

namespace SardData

variable {k l : ℕ}

def zeros (S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)) (U : Set (Fin k → ℝ)) : Set (Fin k → ℝ) :=
  {w | w ∈ U ∧ ‖w‖ = 1 ∧ S w = 0}

def transverse (S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)) (U : Set (Fin k → ℝ)) : Prop :=
  ∀ w ∈ U, S w = 0 → Function.Surjective (fderiv ℝ S w)

def matrix (S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)) (w : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = 0 then w j
    else if hi : (i : ℕ) - 1 < l then (fderiv ℝ S w (Pi.single j 1)) ⟨(i : ℕ) - 1, hi⟩ else 0

def sign (S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)) (w : Fin k → ℝ) : ℤ :=
  ((SignType.sign (matrix S w).det : SignType) : ℤ)

def count (S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)) (U : Set (Fin k → ℝ)) : ℤ :=
  ∑ᶠ w ∈ zeros S U, sign S w

def rayInvariant (S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)) (U : Set (Fin k → ℝ)) : Prop :=
  (∀ w ∈ U, w ≠ 0) ∧ ∀ w ∈ U, ∀ t : ℝ, 0 < t → t • w ∈ U ∧ S (t • w) = S w

theorem congr_data {k' l' : ℕ} (hk : k' = k) (hl : l' = l)
    {S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)} {U : Set (Fin k → ℝ)}
    {S' : (Fin k' → ℝ) → EuclideanSpace ℝ (Fin l')} {U' : Set (Fin k' → ℝ)} (hU : IsOpen U)
    (hzero : ∀ w, (w ∈ U ∧ S w = 0) ↔ (w ∘ Fin.cast hk ∈ U' ∧ S' (w ∘ Fin.cast hk) = 0))
    (hloc : ∀ w ∈ U, S w = 0 → ∀ᶠ v in 𝓝 w,
      v ∘ Fin.cast hk ∈ U' ∧ ∀ j, S' (v ∘ Fin.cast hk) j = S v (Fin.cast hl j)) :
    (transverse S' U' ↔ transverse S U) ∧ count S' U' = count S U ∧
      (zeros S' U').ncard = (zeros S U).ncard := by
  subst hk hl
  have hc : ∀ w : Fin k' → ℝ, w ∘ Fin.cast rfl = w := fun w => by
    funext i; simp
  simp only [hc] at hzero hloc
  have hloc' : ∀ w ∈ U, S w = 0 → S' =ᶠ[𝓝 w] S := by
    intro w hw hSw
    filter_upwards [hloc w hw hSw] with v hv
    exact PiLp.ext fun j => by simpa using hv.2 j
  have hZ : zeros S' U' = zeros S U := by
    ext w
    simp only [zeros, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨((hzero w).2 ⟨h1, h3⟩).1, h2, ((hzero w).2 ⟨h1, h3⟩).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨((hzero w).1 ⟨h1, h3⟩).1, h2, ((hzero w).1 ⟨h1, h3⟩).2⟩
  refine ⟨?_, ?_, by rw [hZ]⟩
  · constructor
    · intro h w hw hSw
      obtain ⟨hw', hSw'⟩ := (hzero w).1 ⟨hw, hSw⟩
      rw [← (hloc' w hw hSw).fderiv_eq]
      exact h w hw' hSw'
    · intro h w hw' hSw'
      obtain ⟨hw, hSw⟩ := (hzero w).2 ⟨hw', hSw'⟩
      rw [(hloc' w hw hSw).fderiv_eq]
      exact h w hw hSw
  · unfold count
    refine finsum_mem_congr hZ ?_
    intro w hw
    obtain ⟨hwU, -, hSw⟩ := hw
    unfold sign matrix
    rw [(hloc' w hwU hSw).fderiv_eq]

theorem sign_eq_one_or_neg_one (hkl : k = l + 1) {S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)}
    {U : Set (Fin k → ℝ)} (hU : IsOpen U) (hray : rayInvariant S U) {w : Fin k → ℝ} (hw : w ∈ U)
    (hS : S w = 0) (hsurj : Function.Surjective (fderiv ℝ S w)) : sign S w = 1 ∨ sign S w = -1 := by
  subst hkl
  set L := fderiv ℝ S w with hL
  have hw0 : w ≠ 0 := hray.1 w hw
  have hLw : L w = 0 := by
    by_cases hd : DifferentiableAt ℝ S w
    · have hg : HasDerivAt (fun t : ℝ => t • w) w 1 := by
        simpa using (hasDerivAt_id (1 : ℝ)).smul_const w
      have hd' : HasFDerivAt S L ((fun t : ℝ => t • w) 1) := by
        simp only [one_smul]; exact hd.hasFDerivAt
      have h1 : HasDerivAt (fun t : ℝ => S (t • w)) (L w) 1 := hd'.comp_hasDerivAt 1 hg
      have h2 : HasDerivAt (fun t : ℝ => S (t • w)) 0 1 := by
        have hc : HasDerivAt (fun _ : ℝ => S w) 0 1 := hasDerivAt_const _ _
        refine hc.congr_of_eventuallyEq ?_
        filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
        exact (hray.2 w hw t ht).2
      exact h1.unique h2
    · simp [hL, fderiv_zero_of_not_differentiableAt hd]
  have hker : ∀ v, L v = 0 → ∃ c : ℝ, v = c • w := by
    have hrange : LinearMap.range (L : (Fin (l + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin l)) = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hrank := LinearMap.finrank_range_add_finrank_ker
      (L : (Fin (l + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin l))
    rw [hrange, finrank_top, finrank_euclideanSpace, Fintype.card_fin,
      Module.finrank_fin_fun] at hrank
    have hk1 : Module.finrank ℝ
        (LinearMap.ker (L : (Fin (l + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin l))) = 1 := by
      omega
    have hle : (ℝ ∙ w) ≤ LinearMap.ker (L : (Fin (l + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin l)) := by
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]; exact hLw
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hw0, hk1])
    intro v hv
    have hmem : v ∈ (ℝ ∙ w) := by rw [heq, LinearMap.mem_ker]; exact hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  have hdet : (matrix S w).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hrow : ∀ i, ∑ j, matrix S w i j * v j = 0 := fun i => by
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct] using this
    have hexp : v = ∑ j, v j • (Pi.single j (1 : ℝ) : Fin (l + 1) → ℝ) := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hLv : L v = 0 := by
      ext m
      have := hrow m.succ
      simp only [matrix, Matrix.of_apply, Fin.val_succ] at this
      rw [hexp, map_sum]
      simpa [mul_comm] using this
    obtain ⟨c, rfl⟩ := hker v hLv
    have h0' := hrow 0
    simp only [matrix, Matrix.of_apply, Fin.val_zero, ite_true, Pi.smul_apply, smul_eq_mul] at h0'
    have hc : c = 0 := by
      by_contra hc
      apply hw0
      have hs : ∑ j, w j * w j = 0 := by
        have : c * ∑ j, w j * w j = 0 := by
          rw [Finset.mul_sum]; rw [← h0']
          refine Finset.sum_congr rfl fun j _ => ?_; ring
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hc
        · exact h
      ext j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (w i))).mp hs j
        (Finset.mem_univ _)
      simpa using this
    exact hv0 (by rw [hc, zero_smul])
  unfold sign
  rcases lt_or_gt_of_ne hdet with h | h
  · right; rw [sign_neg h]; rfl
  · left; rw [sign_pos h]; rfl

theorem natAbs_count_le (hkl : k = l + 1) {S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)}
    {U : Set (Fin k → ℝ)} (hU : IsOpen U) (hray : rayInvariant S U) (htr : transverse S U) :
    (count S U).natAbs ≤ (zeros S U).ncard := by
  have hsgn : ∀ w ∈ zeros S U, sign S w = 1 ∨ sign S w = -1 := by
    intro w hw
    exact sign_eq_one_or_neg_one hkl hU hray hw.1 hw.2.2 (htr w hw.1 hw.2.2)
  by_cases hfin : (zeros S U).Finite
  · unfold count
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin]
    refine (Int.natAbs_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans (by simp)
    intro w hw
    rcases hsgn w (hfin.mem_toFinset.mp hw) with h | h <;> simp [h]
  · have hzero : count S U = 0 := by
      unfold count
      apply finsum_mem_eq_zero_of_infinite
      have hsub : zeros S U ⊆ zeros S U ∩ Function.support (sign S) := by
        intro w hw
        refine ⟨hw, ?_⟩
        rcases hsgn w hw with h | h <;> simp [h]
      exact Set.Infinite.mono hsub hfin
    simp [hzero]

theorem exists_opposite_signs (hkl : k = l + 1) {S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)}
    {U : Set (Fin k → ℝ)} (hU : IsOpen U) (hray : rayInvariant S U) (htr : transverse S U)
    (hlt : (count S U).natAbs < (zeros S U).ncard) :
    ∃ w₁ ∈ zeros S U, ∃ w₂ ∈ zeros S U, sign S w₁ = 1 ∧ sign S w₂ = -1 := by
  have hfin : (zeros S U).Finite := Set.finite_of_ncard_pos (lt_of_le_of_lt (Nat.zero_le _) hlt)
  have hpm : ∀ w ∈ zeros S U, sign S w = 1 ∨ sign S w = -1 := fun w hw =>
    sign_eq_one_or_neg_one hkl hU hray hw.1 hw.2.2 (htr w hw.1 hw.2.2)
  have hcount : count S U = ∑ w ∈ hfin.toFinset, sign S w :=
    finsum_mem_eq_finite_toFinset_sum _ hfin
  have hcard : (zeros S U).ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  by_contra hcon
  have hconst : ∃ c : ℤ, (c = 1 ∨ c = -1) ∧ ∀ w ∈ zeros S U, sign S w = c := by
    by_cases hex : ∃ w₁ ∈ zeros S U, sign S w₁ = 1
    · obtain ⟨w₁, hw₁, hs₁⟩ := hex
      refine ⟨1, Or.inl rfl, fun w hw => ?_⟩
      rcases hpm w hw with h | h
      · exact h
      · exact absurd ⟨w₁, hw₁, w, hw, hs₁, h⟩ hcon
    · refine ⟨-1, Or.inr rfl, fun w hw => ?_⟩
      rcases hpm w hw with h | h
      · exact absurd ⟨w, hw, h⟩ hex
      · exact h
  obtain ⟨c, hc, hcw⟩ := hconst
  have hsum : count S U = hfin.toFinset.card • c := by
    rw [hcount, ← Finset.sum_const]
    exact Finset.sum_congr rfl fun w hw => hcw w (hfin.mem_toFinset.mp hw)
  have habs : (count S U).natAbs = (zeros S U).ncard := by
    rw [hsum, hcard, nsmul_eq_mul]
    rcases hc with rfl | rfl <;> simp
  omega

theorem sign_smul {S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)} {U : Set (Fin k → ℝ)}
    (hU : IsOpen U) (hray : rayInvariant S U) {w : Fin k → ℝ} (hw : w ∈ U) {t : ℝ} (ht : 0 < t) :
    sign S (t • w) = sign S w := by
  classical
  have ht0 : t ≠ 0 := ht.ne'
  set e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 t⁻¹ (inv_ne_zero ht0)) with he
  have he_apply : ∀ v, e v = t⁻¹ • v := fun v => rfl
  have htw : t • w ∈ U := ((hray.2 w hw t ht).1)
  have hev : S =ᶠ[𝓝 (t • w)] S ∘ e := by
    filter_upwards [hU.mem_nhds htw] with v hv
    have h1 := (hray.2 (t⁻¹ • v) ((hray.2 v hv t⁻¹ (inv_pos.mpr ht)).1) t ht).2
    rw [smul_smul, mul_inv_cancel₀ ht0, one_smul] at h1
    simp only [Function.comp_apply, he_apply]
    exact h1
  have hfd : fderiv ℝ S (t • w) = (fderiv ℝ S w).comp (e : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) := by
    rw [hev.fderiv_eq, ContinuousLinearEquiv.comp_right_fderiv, he_apply, smul_smul,
      inv_mul_cancel₀ ht0, one_smul]
  let d : Fin k → ℝ := fun i => if (i : ℕ) = 0 then t else t⁻¹
  have hmat : matrix S (t • w) = Matrix.diagonal d * matrix S w := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [matrix, Matrix.of_apply, d, hfd, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, he_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [PiLp.smul_apply]
  have hdpos : 0 < ∏ i, d i := by
    apply Finset.prod_pos
    intro i _
    simp only [d]
    split_ifs
    · exact ht
    · exact inv_pos.mpr ht
  unfold sign
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal, sign_mul, sign_pos hdpos, one_mul]

end SardData

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M} (D : GradientLikeStrip I f a b crit)

def sardZeros (p : M) {q : M} (hq : q ∈ crit) (ε c : ℝ) (hp : p ∈ crit) :
    Set (Fin (D.chart q hq).k → ℝ) :=
  SardData.zeros (D.sardMap p hq ε c ε hp) (D.sardDom p hq ε c ε hp)

def isSardTransverse (p : M) {q : M} (hq : q ∈ crit) (ε c : ℝ) (hp : p ∈ crit) : Prop :=
  SardData.transverse (D.sardMap p hq ε c ε hp) (D.sardDom p hq ε c ε hp)

def sardSign (p : M) {q : M} (hq : q ∈ crit) (ε c : ℝ) (hp : p ∈ crit)
    (w : Fin (D.chart q hq).k → ℝ) : ℤ :=
  SardData.sign (D.sardMap p hq ε c ε hp) w

def sardCount (p : M) {q : M} (hq : q ∈ crit) (ε c : ℝ) (hp : p ∈ crit) : ℤ :=
  SardData.count (D.sardMap p hq ε c ε hp) (D.sardDom p hq ε c ε hp)

def sardValid (ε : ℝ) (p : M) {q : M} (hq : q ∈ crit) (hp : p ∈ crit) : Prop :=
  0 < ε ∧ (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ (D.chart q hq).r₀ ^ 2 < 2 * ε ∧
    8 * ε < D.rm p hp ^ 2 ∧ 8 * ε < D.rm q hq ^ 2 ∧ f p + ε < f q - ε ∧
    ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx

def sardAgree {g : M → ℝ} (D' : GradientLikeStrip I g a b crit) (ε ε' c c' : ℝ) (p : M) {q : M}
    (hq : q ∈ crit) (hp : p ∈ crit) : Prop :=
  (D'.isSardTransverse p hq ε' c' hp ↔ D.isSardTransverse p hq ε c hp) ∧
    D'.sardCount p hq ε' c' hp = D.sardCount p hq ε c hp ∧
    (D'.sardZeros p hq ε' c' hp).ncard = (D.sardZeros p hq ε c hp).ncard

def noCommon (x : M) (hx : x ∈ crit) (y : M) (hy : y ∈ crit) (rx ry : ℝ) : Prop :=
  ∀ z ∈ (D.chart x hx).χ '' {w | morseNorm n w < rx}, ∀ s : ℝ,
    D.flow s z ∉ (D.chart y hy).χ '' {w | morseNorm n w < ry}

def isRescaleOf {g : M → ℝ} (D' : GradientLikeStrip I g a b crit) : Prop :=
  ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
    ∀ x, D'.V x = φ x • D.V x

def hitTime (t : ℝ) (x : M) : ℝ := sInf {s : ℝ | 0 ≤ s ∧ f (D.flow s x) ≤ t}

def descend (t : ℝ) (x : M) : M := D.flow (D.hitTime t x) x

def rightCoord (p : M) (hp : p ∈ crit) (ε : ℝ) (z : M) : EuclideanSpace ℝ (Fin (D.chart p hp).k) :=
  negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow (f z - (f p + ε)) z))

def leftCoord (q : M) (hq : q ∈ crit) (ε : ℝ) (z : M) :
    EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)) :=
  posPart (D.chart q hq).hk ((D.chart q hq).χ.symm (D.flow (f z - (f q - ε)) z))

open Classical in
def tubeCoord (x : M) (hx : x ∈ crit) (ε : ℝ) (z : M) : EuclideanSpace ℝ (Fin (D.chart x hx).k) :=
  if f x + ε ≤ f z then D.rightCoord x hx ε z
  else negPart (D.chart x hx).hk ((D.chart x hx).χ.symm z)

def tubeCoordE (x : M) (hx : x ∈ crit) (ε : ℝ) (μ : ℕ) (z : M) : EuclideanSpace ℝ (Fin μ) :=
  WithLp.toLp 2 fun i =>
    if h : (i : ℕ) < (D.chart x hx).k then D.tubeCoord x hx ε z ⟨i, h⟩ else 0

theorem landing_smul (p : M) {q : M} (hq : q ∈ crit) (ε c η : ℝ) {t : ℝ} (ht : 0 < t)
    {w : Fin (D.chart q hq).k → ℝ} (hw : w ≠ 0) :
    D.landing p hq ε c η (t • w) = D.landing p hq ε c η w := by
  unfold landing
  rw [(D.chart q hq).sphereParam_smul ε ht hw]

end GradientLikeStrip

namespace Handle

def reidx {k μ : ℕ} (y : EuclideanSpace ℝ (Fin μ)) : Fin k → ℝ :=
  fun i => if h : (i : ℕ) < μ then y ⟨i, h⟩ else 0

end Handle

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M} (D : GradientLikeStrip I f a b crit)

open Classical in
def leftDiscMap (x : M) (μ : ℕ) (ε t : ℝ) (y : EuclideanSpace ℝ (Fin μ)) : M :=
  if hx : x ∈ crit then
    if ‖y‖ ≤ 1 / 2 then
      (D.chart x hx).χ (recombine (D.chart x hx).hk
        ((2 * Real.sqrt (2 * ε)) • (D.chart x hx).toE (Handle.reidx y)) 0)
    else D.flow ((2 * ‖y‖ - 1) * (f x - ε - t))
      ((D.chart x hx).χ ((D.chart x hx).sphereParam ε (Handle.reidx y)))
  else x

open Classical in
def leftSphereMap (x : M) (μ : ℕ) (ε t : ℝ) (y : EuclideanSpace ℝ (Fin μ)) : M :=
  if hx : x ∈ crit then
    D.flow (f x - ε - t) ((D.chart x hx).χ ((D.chart x hx).sphereParam ε (Handle.reidx y)))
  else x

open Classical in
def leftSphereHit (x : M) (μ : ℕ) (ε t : ℝ) (y : EuclideanSpace ℝ (Fin μ)) : M :=
  if hx : x ∈ crit then
    D.descend t ((D.chart x hx).χ ((D.chart x hx).sphereParam ε (Handle.reidx y)))
  else x

open Classical in
def smallDiscMap (x : M) (μ : ℕ) (δ : ℝ) (y : EuclideanSpace ℝ (Fin μ)) : M :=
  if hx : x ∈ crit then
    (D.chart x hx).χ (recombine (D.chart x hx).hk (δ • (D.chart x hx).toE (Handle.reidx y)) 0)
  else x

def slabCap (τ : ℝ) : Set M := ⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.captured x hx

def tube (x : M) (hx : x ∈ crit) (δ : ℝ) : Set M :=
  {y | ∃ s, 0 ≤ s ∧ D.flow s y ∈ (D.chart x hx).χ ''
    {z | morseNorm n z < D.rm x hx ∧ ‖negPart (D.chart x hx).hk z‖ < δ}}

end GradientLikeStrip

def sameCritIn (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f g : M → ℝ) (a b : ℝ) : Prop :=
  (∀ x, f x ∈ Ioo a b → (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)) ∧
    ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x

theorem sameCritIn.refl (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f : M → ℝ) (a b : ℝ) :
    sameCritIn I f f a b :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩

theorem sameCritIn.trans {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f g k : M → ℝ} {a b : ℝ}
    (hfg : sameCritIn I f g a b) (hmod : ModifiedWithin f a b g) (hgk : sameCritIn I g k a b) :
    sameCritIn I f k a b := by
  refine ⟨fun x hx => ?_, fun x hx hc => ?_⟩
  · have hgx : g x ∈ Ioo a b := hmod.mapsTo hx
    exact (hgk.1 x hgx).trans (hfg.1 x hx)
  · have hgx : g x ∈ Ioo a b := hmod.mapsTo hx
    rw [hgk.2 x hgx ((hfg.1 x hx).2 hc), hfg.2 x hx hc]

theorem sameCritIn.crit_of {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f g : M → ℝ} {a b : ℝ}
    (h : sameCritIn I f g a b) (hmod : ModifiedWithin f a b g) {x : M} (hx : g x ∈ Ioo a b)
    (hc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) :
    f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∧ morseIndex I g x = morseIndex I f x := by
  have hxf : f x ∈ Ioo a b := (Set.ext_iff.1 hmod.preimage_Ioo x).1 hx
  have hcf : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := (h.1 x hxf).1 hc
  exact ⟨hxf, hcf, h.2 x hxf hcf⟩

structure BlockConfig (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M] (f : M → ℝ)
    (a b : ℝ) (ℓ : ℕ) where
  crit : Finset M
  hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x
  D : GradientLikeStrip I f a b crit
  α : ℝ
  β : ℝ
  ε : ℝ
  c : ℝ
  hε : 0 < ε
  hr₀ : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε
  hrm : ∀ x hx, 8 * ε < D.rm x hx ^ 2
  haα : a < α
  hαc : α + ε < c
  hcβ : c < β - ε
  hβb : β < b
  hmin : ∀ x ∈ crit, ℓ ≤ morseIndex I f x
  hP : ∀ x ∈ crit, morseIndex I f x = ℓ → f x = α
  hQ : ∀ x ∈ crit, morseIndex I f x = ℓ + 1 → f x = β
  hhigh : ∀ x ∈ crit, ℓ + 1 < morseIndex I f x → β < f x
  hlev : ∀ y, f y ∈ Icc (α + ε) (β - ε) → ∀ x hx, y ∉ D.smallBall x hx

namespace BlockConfig

section Basic

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M]
  {f : M → ℝ} {a b : ℝ} {ℓ : ℕ} (B : BlockConfig I f a b ℓ)

def lowerIndexCriticalPoints : Finset M := by
  classical exact B.crit.filter (fun x => morseIndex I f x = ℓ)

def upperIndexCriticalPoints : Finset M := by
  classical exact B.crit.filter (fun x => morseIndex I f x = ℓ + 1)

theorem mem_lowerIndexCriticalPoints {x : M} : x ∈ B.lowerIndexCriticalPoints ↔ x ∈ B.crit ∧ morseIndex I f x = ℓ := by
  classical
  unfold lowerIndexCriticalPoints
  convert Finset.mem_filter

theorem mem_upperIndexCriticalPoints {x : M} : x ∈ B.upperIndexCriticalPoints ↔ x ∈ B.crit ∧ morseIndex I f x = ℓ + 1 := by
  classical
  unfold upperIndexCriticalPoints
  convert Finset.mem_filter

theorem lowerIndexCriticalPoints_eq_of_crit_eq {B' : BlockConfig I f a b ℓ} (h : B'.crit = B.crit) : B'.lowerIndexCriticalPoints = B.lowerIndexCriticalPoints := by
  ext x
  rw [mem_lowerIndexCriticalPoints, mem_lowerIndexCriticalPoints, h]

theorem upperIndexCriticalPoints_eq_of_crit_eq {B' : BlockConfig I f a b ℓ} (h : B'.crit = B.crit) : B'.upperIndexCriticalPoints = B.upperIndexCriticalPoints := by
  ext x
  rw [mem_upperIndexCriticalPoints, mem_upperIndexCriticalPoints, h]

end Basic

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {ℓ : ℕ} (B : BlockConfig I f a b ℓ)

open Classical in
def count (p q : M) : ℤ :=
  if hp : p ∈ B.crit then if hq : q ∈ B.crit then B.D.sardCount p hq B.ε B.c hp else 0 else 0

open Classical in
def zerosCard (p q : M) : ℕ :=
  if hp : p ∈ B.crit then
    if hq : q ∈ B.crit then (B.D.sardZeros p hq B.ε B.c hp).ncard else 0
  else 0

def pairTransverse (p q : M) : Prop :=
  ∃ (hp : p ∈ B.crit) (hq : q ∈ B.crit), B.D.isSardTransverse p hq B.ε B.c hp

def transverse : Prop :=
  ∀ p ∈ B.lowerIndexCriticalPoints, ∀ q ∈ B.upperIndexCriticalPoints, B.pairTransverse p q

open Classical in
def rightSphere (p : M) : Set M :=
  if hp : p ∈ B.crit then B.D.rightSphere p hp B.ε B.c else ∅

open Classical in
def leftSphere (q : M) : Set M :=
  if hq : q ∈ B.crit then B.D.leftSphere q hq B.ε B.c else ∅

omit [T2Space M] [I.Boundaryless] in
theorem sardValid {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints) :
    B.D.sardValid B.ε p ((B.mem_upperIndexCriticalPoints.1 hq).1) ((B.mem_lowerIndexCriticalPoints.1 hp).1) := by
  have hpα : f p = B.α := B.hP p (B.mem_lowerIndexCriticalPoints.1 hp).1 (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hqβ : f q = B.β := B.hQ q (B.mem_upperIndexCriticalPoints.1 hq).1 (B.mem_upperIndexCriticalPoints.1 hq).2
  refine ⟨B.hε, B.hr₀ _ _, B.hr₀ _ _, B.hrm _ _, B.hrm _ _, ?_, ?_⟩
  · rw [hpα, hqβ]; linarith [B.hαc, B.hcβ]
  · intro y hy x hx
    rw [hpα, hqβ] at hy
    exact B.hlev y hy x hx

theorem natAbs_count_le_zerosCard {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints)
    (htr : B.pairTransverse p q) : (B.count p q).natAbs ≤ B.zerosCard p q := by
  classical
  obtain ⟨hpc, hqc, htr'⟩ := htr
  have hkp : (B.D.chart p hpc).k = ℓ := by
    rw [← (B.D.chart p hpc).hkidx]; exact (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hkq : (B.D.chart q hqc).k = ℓ + 1 := by
    rw [← (B.D.chart q hqc).hkidx]; exact (B.mem_upperIndexCriticalPoints.1 hq).2
  have hkl : (B.D.chart q hqc).k = (B.D.chart p hpc).k + 1 := by rw [hkq, hkp]
  have hR : 2 * B.ε ≤ (B.D.chart q hqc).R ^ 2 := by
    have h1 := B.hrm q hqc
    have h2 := (B.D.hrm q hqc).2
    have h3 := B.D.rm_pos q hqc
    nlinarith [B.hε]
  have hU : IsOpen (B.D.sardDom p hqc B.ε B.c B.ε hpc) :=
    GradientLikeStrip.isOpen_sardDom B.hε.le hR
  have hray : SardData.rayInvariant (B.D.sardMap p hqc B.ε B.c B.ε hpc)
      (B.D.sardDom p hqc B.ε B.c B.ε hpc) := by
    refine ⟨fun w hw => hw.1, fun w hw t ht => ?_⟩
    have hl := B.D.landing_smul p hqc B.ε B.c B.ε ht hw.1
    refine ⟨⟨smul_ne_zero ht.ne' hw.1, ?_⟩, ?_⟩
    · have h2 : B.D.landing p hqc B.ε B.c B.ε w ∈ (B.D.chart p hpc).χ ''
          {y | morseNorm n y < (B.D.chart p hpc).R} := hw.2
      rw [← hl] at h2
      exact h2
    · unfold GradientLikeStrip.sardMap; rw [hl]
  have key := SardData.natAbs_count_le hkl hU hray htr'
  simp only [BlockConfig.count, BlockConfig.zerosCard, hpc, hqc, ↓reduceDIte]
  exact key

theorem exists_opposite_zeros {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints)
    (htr : B.pairTransverse p q) (hlt : (B.count p q).natAbs < B.zerosCard p q) :
    ∃ w₁ ∈ B.D.sardZeros p ((B.mem_upperIndexCriticalPoints.1 hq).1) B.ε B.c ((B.mem_lowerIndexCriticalPoints.1 hp).1),
      ∃ w₂ ∈ B.D.sardZeros p ((B.mem_upperIndexCriticalPoints.1 hq).1) B.ε B.c ((B.mem_lowerIndexCriticalPoints.1 hp).1),
        B.D.sardSign p ((B.mem_upperIndexCriticalPoints.1 hq).1) B.ε B.c ((B.mem_lowerIndexCriticalPoints.1 hp).1) w₁ = 1 ∧
        B.D.sardSign p ((B.mem_upperIndexCriticalPoints.1 hq).1) B.ε B.c ((B.mem_lowerIndexCriticalPoints.1 hp).1) w₂ = -1 := by
  have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hkl : (B.D.chart q hqc).k = (B.D.chart p hpc).k + 1 := by
    rw [← (B.D.chart q hqc).hkidx, ← (B.D.chart p hpc).hkidx, (B.mem_upperIndexCriticalPoints.1 hq).2,
      (B.mem_lowerIndexCriticalPoints.1 hp).2]
  have hεR : 2 * B.ε ≤ (B.D.chart q hqc).R ^ 2 := by
    have hrm0 := B.D.rm_pos q hqc
    have := pow_le_pow_left₀ hrm0.le (B.D.hrm q hqc).2 2
    linarith [pow_pos hrm0 2, B.hrm q hqc]
  have hU : IsOpen (B.D.sardDom p hqc B.ε B.c B.ε hpc) :=
    GradientLikeStrip.isOpen_sardDom B.hε.le hεR
  have hray : SardData.rayInvariant (B.D.sardMap p hqc B.ε B.c B.ε hpc)
      (B.D.sardDom p hqc B.ε B.c B.ε hpc) := by
    refine ⟨fun w hw => hw.1, fun w hw t ht => ?_⟩
    have hw0 : w ≠ 0 := hw.1
    have hland := B.D.landing_smul p hqc B.ε B.c B.ε ht hw0
    refine ⟨⟨smul_ne_zero ht.ne' hw0, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, hland]; exact hw.2
    · unfold GradientLikeStrip.sardMap
      rw [hland]
  obtain ⟨htr', -⟩ : ∃ (_ : B.D.isSardTransverse p hqc B.ε B.c hpc), True := by
    obtain ⟨hp', hq', h⟩ := htr
    exact ⟨h, trivial⟩
  have hlt' : (SardData.count (B.D.sardMap p hqc B.ε B.c B.ε hpc)
      (B.D.sardDom p hqc B.ε B.c B.ε hpc)).natAbs <
      (SardData.zeros (B.D.sardMap p hqc B.ε B.c B.ε hpc)
        (B.D.sardDom p hqc B.ε B.c B.ε hpc)).ncard := by
    have h1 : B.count p q = B.D.sardCount p hqc B.ε B.c hpc := by
      simp [count, hpc, hqc]
    have h2 : B.zerosCard p q = (B.D.sardZeros p hqc B.ε B.c hpc).ncard := by
      simp [zerosCard, hpc, hqc]
    rw [h1, h2] at hlt
    exact hlt
  exact SardData.exists_opposite_signs hkl hU hray htr' hlt'

end BlockConfig

def colOp {α : Type*} [DecidableEq α] (r : α → ℤ) (q₁ q₂ : α) (t : ℤ) : α → ℤ :=
  Function.update r q₁ (r q₁ + t * r q₂)

theorem exists_row_unit {α : Type*} [DecidableEq α] {Q : Finset α} (R : (α → ℤ) → Prop)
    (hstep : ∀ r, R r → ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, q₁ ≠ q₂ → ∀ t : ℤ, (t = 1 ∨ t = -1) →
      ∃ r', R r' ∧ ∀ q ∈ Q, |r' q| = |colOp r q₁ q₂ t q|)
    {r : α → ℤ} (hr : R r) (hgcd : ∃ y : α → ℤ, ∑ q ∈ Q, r q * y q = 1) :
    ∃ r', R r' ∧ ∃ q ∈ Q, |r' q| = 1 := by
  suffices H : ∀ n : ℕ, ∀ r : α → ℤ, R r → (∀ d : ℤ, (∀ q ∈ Q, d ∣ r q) → d ∣ 1) →
      ∑ q ∈ Q, (r q).natAbs ≤ n → ∃ r', R r' ∧ ∃ q ∈ Q, |r' q| = 1 by
    obtain ⟨y, hy⟩ := hgcd
    refine H _ r hr ?_ le_rfl
    intro d hd
    rw [← hy]
    exact Finset.dvd_sum fun q hq => dvd_mul_of_dvd_left (hd q hq) _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro r hr hI hn
  by_cases hone : ∃ q ∈ Q, |r q| = 1
  · exact ⟨r, hr, hone⟩
  push Not at hone
  have hex : ∃ q₁ ∈ Q, r q₁ ≠ 0 := by
    by_contra h
    push Not at h
    have h0 := hI 0 (fun q hq => by rw [h q hq])
    exact one_ne_zero (zero_dvd_iff.1 h0)
  obtain ⟨q₁, hq₁, h₁⟩ := hex
  have hex2 : ∃ q₂ ∈ Q, q₂ ≠ q₁ ∧ r q₂ ≠ 0 := by
    by_contra h
    push Not at h
    have hd := hI (r q₁) (fun q hq => by
      by_cases hqq : q = q₁
      · rw [hqq]
      · rw [h q hq hqq]; exact dvd_zero _)
    exact hone q₁ hq₁ (Int.isUnit_iff_abs_eq.1 (isUnit_of_dvd_one hd))
  obtain ⟨q₂, hq₂, h₂₁, h₂⟩ := hex2
  have key : ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → r b ≠ 0 → |r b| ≤ |r a| →
      ∃ r', R r' ∧ ∃ q ∈ Q, |r' q| = 1 := by
    intro a ha b hb hab hb0 hle
    obtain ⟨t, ht, hlt⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ |r a + t * r b| < |r a| := by
      rcases le_or_gt 0 (r a) with h1 | h1 <;> rcases le_or_gt 0 (r b) with h2 | h2
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [abs_of_nonneg h1, abs_of_nonneg h2] at hle
        rw [abs_of_nonneg h1, abs_lt]; constructor <;> omega
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [abs_of_nonneg h1, abs_of_neg h2] at hle
        rw [abs_of_nonneg h1, abs_lt]; constructor <;> omega
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [abs_of_neg h1, abs_of_nonneg h2] at hle
        rw [abs_of_neg h1, abs_lt]; constructor <;> omega
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [abs_of_neg h1, abs_of_neg h2] at hle
        rw [abs_of_neg h1, abs_lt]; constructor <;> omega
    obtain ⟨r', hr', habs⟩ := hstep r hr a ha b hb hab t ht
    have hca : colOp r a b t a = r a + t * r b := by
      unfold colOp; exact Function.update_self _ _ _
    have hcq : ∀ q, q ≠ a → colOp r a b t q = r q := by
      intro q hq; unfold colOp; exact Function.update_of_ne hq _ _
    have hnat : ∀ q ∈ Q, (r' q).natAbs = (colOp r a b t q).natAbs := by
      intro q hq
      rw [← Int.natAbs_abs, habs q hq, Int.natAbs_abs]
    have hI' : ∀ d : ℤ, (∀ q ∈ Q, d ∣ r' q) → d ∣ 1 := by
      intro d hd
      have hd' : ∀ q ∈ Q, d ∣ colOp r a b t q := by
        intro q hq
        have := (dvd_abs d (r' q)).2 (hd q hq)
        rw [habs q hq] at this
        exact (dvd_abs _ _).1 this
      apply hI d
      intro q hq
      have hdb : d ∣ r b := by
        have := hd' b hb
        rwa [hcq b (Ne.symm hab)] at this
      by_cases hqa : q = a
      · subst hqa
        have := hd' q ha
        rw [hca] at this
        have h3 : r q = (r q + t * r b) - t * r b := by ring
        rw [h3]
        exact dvd_sub this (dvd_mul_of_dvd_right hdb _)
      · have := hd' q hq
        rwa [hcq q hqa] at this
    have hlt' : ∑ q ∈ Q, (r' q).natAbs < ∑ q ∈ Q, (r q).natAbs := by
      apply Finset.sum_lt_sum
      · intro q hq
        rw [hnat q hq]
        by_cases hqa : q = a
        · subst hqa
          rw [hca]
          have := hlt.le
          rw [← Int.natCast_natAbs, ← Int.natCast_natAbs] at this
          exact_mod_cast this
        · rw [hcq q hqa]
      · refine ⟨a, ha, ?_⟩
        rw [hnat a ha, hca]
        rw [← Int.natCast_natAbs, ← Int.natCast_natAbs] at hlt
        exact_mod_cast hlt
    exact ih _ (lt_of_lt_of_le hlt' hn) r' hr' hI' le_rfl
  rcases le_total |r q₂| |r q₁| with hle | hle
  · exact key q₁ hq₁ q₂ hq₂ (Ne.symm h₂₁) h₂ hle
  · exact key q₂ hq₂ q₁ hq₁ h₂₁ h₁ hle

theorem joinedIn_det_pos {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ} (hA : 0 < A.det)
    (hB : 0 < B.det) : JoinedIn {C : Matrix (Fin k) (Fin k) ℝ | 0 < C.det} A B := by
  have hF : ∀ (i j : Fin k) (hij : i ≠ j),
      ([(⟨i, j, hij, -1⟩ : Matrix.TransvectionStruct (Fin k) ℝ), ⟨j, i, hij.symm, 1⟩,
        ⟨i, j, hij, -1⟩, ⟨i, j, hij, -1⟩, ⟨j, i, hij.symm, 1⟩, ⟨i, j, hij, -1⟩].map
        Matrix.TransvectionStruct.toMatrix).prod
      = Matrix.diagonal (fun a => if a = i ∨ a = j then (-1 : ℝ) else 1) := by
    intro i j hij
    have e1 : ∀ (a b : Fin k) (c d : ℝ), Matrix.single a i c * Matrix.single j b d = 0 := by
      intro a b c d; exact Matrix.single_mul_single_of_ne _ _ _ _ hij _
    have e2 : ∀ (a b : Fin k) (c d : ℝ), Matrix.single a j c * Matrix.single i b d = 0 := by
      intro a b c d; exact Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
    have hR : Matrix.transvection i j (-1 : ℝ) * (Matrix.transvection j i 1 *
        Matrix.transvection i j (-1))
        = 1 - Matrix.single i i 1 - Matrix.single j j 1 - Matrix.single i j 1
          + Matrix.single j i 1 := by
      simp only [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.single_mul_single_same, e2]
      ext a b
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
      split_ifs <;> subst_vars <;> simp_all [← sub_eq_add_neg]
    have hRR : (1 - Matrix.single i i 1 - Matrix.single j j 1 - Matrix.single i j 1
          + Matrix.single j i (1 : ℝ)) * (1 - Matrix.single i i 1 - Matrix.single j j 1
          - Matrix.single i j 1 + Matrix.single j i 1)
        = Matrix.diagonal (fun a => if a = i ∨ a = j then (-1 : ℝ) else 1) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.single_mul_single_same, e1, e2]
      ext a b
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply,
        Matrix.diagonal_apply]
      split_ifs <;> subst_vars <;> simp_all <;> aesop
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one,
      Matrix.TransvectionStruct.toMatrix_mk]
    rw [← hRR, ← hR, Matrix.mul_assoc, Matrix.mul_assoc]
  have hstep : ∀ (X Y : Matrix (Fin k) (Fin k) ℝ) (t : Matrix.TransvectionStruct (Fin k) ℝ),
      0 < (X * Y).det →
        JoinedIn {C : Matrix (Fin k) (Fin k) ℝ | 0 < C.det} (X * t.toMatrix * Y) (X * Y) := by
    intro X Y t hXY
    apply JoinedIn.of_segment_subset
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    have hz : a • (X * t.toMatrix * Y) + b • (X * Y)
        = X * Matrix.transvection t.i t.j (a * t.c) * Y := by
      simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_one, smul_add]
      rw [show Matrix.single t.i t.j (a * t.c) = a • Matrix.single t.i t.j t.c by
        rw [Matrix.smul_single, smul_eq_mul], Matrix.mul_smul, Matrix.smul_mul,
        add_right_comm, ← add_smul, hab, one_smul]
    change 0 < (a • (X * t.toMatrix * Y) + b • (X * Y)).det
    rw [hz, Matrix.det_mul, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ t.hij, mul_one,
      ← Matrix.det_mul]
    exact hXY
  have hleft : ∀ (L : List (Matrix.TransvectionStruct (Fin k) ℝ))
      (W : Matrix (Fin k) (Fin k) ℝ),
      0 < W.det → JoinedIn {C : Matrix (Fin k) (Fin k) ℝ | 0 < C.det}
        ((L.map Matrix.TransvectionStruct.toMatrix).prod * W) W := by
    intro L
    induction L with
    | nil =>
      intro W hW
      simpa using JoinedIn.refl (show W ∈ {C : Matrix (Fin k) (Fin k) ℝ | 0 < C.det} from hW)
    | cons t L ih =>
      intro W hW
      have hdet : 0 < (1 * ((L.map Matrix.TransvectionStruct.toMatrix).prod * W)).det := by
        rw [Matrix.one_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, one_mul]
        exact hW
      have h1 := hstep 1 ((L.map Matrix.TransvectionStruct.toMatrix).prod * W) t hdet
      simp only [Matrix.one_mul] at h1
      simpa [Matrix.mul_assoc] using h1.trans (ih W hW)
  have hright : ∀ (L : List (Matrix.TransvectionStruct (Fin k) ℝ))
      (W : Matrix (Fin k) (Fin k) ℝ),
      0 < W.det → JoinedIn {C : Matrix (Fin k) (Fin k) ℝ | 0 < C.det}
        (W * (L.map Matrix.TransvectionStruct.toMatrix).prod) W := by
    intro L
    induction L with
    | nil =>
      intro W hW
      simpa using JoinedIn.refl (show W ∈ {C : Matrix (Fin k) (Fin k) ℝ | 0 < C.det} from hW)
    | cons t L ih =>
      intro W hW
      have hdet1 : 0 < (W * 1).det := by rw [Matrix.mul_one]; exact hW
      have h1 := hstep W 1 t hdet1
      simp only [Matrix.mul_one] at h1
      have hdet2 : 0 < (W * t.toMatrix).det := by
        rw [Matrix.det_mul, Matrix.TransvectionStruct.det, mul_one]; exact hW
      have h2 := ih (W * t.toMatrix) hdet2
      simpa [Matrix.mul_assoc] using h2.trans h1
  have hflip : ∀ (i j : Fin k), i ≠ j → ∀ W : Matrix (Fin k) (Fin k) ℝ, 0 < W.det →
      JoinedIn {C : Matrix (Fin k) (Fin k) ℝ | 0 < C.det} W
        (W * Matrix.diagonal (fun a => if a = i ∨ a = j then (-1 : ℝ) else 1)) := by
    intro i j hij W hW
    rw [← hF i j hij]
    exact (hright _ W hW).symm
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hAB : A = B := by
      ext a
      exact Fin.elim0 a
    subst hAB
    exact JoinedIn.refl hA
  have hdiag : ∀ (s : Finset (Fin k)) (D : Fin k → ℝ), 0 < ∏ a, D a →
      (∀ a, a ≠ ⟨0, hk⟩ → D a < 0 → a ∈ s) →
      JoinedIn {C : Matrix (Fin k) (Fin k) ℝ | 0 < C.det} (Matrix.diagonal D) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro D hD hneg
      have hpos : ∀ a, a ≠ ⟨0, hk⟩ → 0 < D a := by
        intro a ha
        rcases lt_trichotomy (D a) 0 with h | h | h
        · exact absurd (hneg a ha h) (Finset.notMem_empty a)
        · exfalso
          have h0 : ∏ a, D a = 0 := Finset.prod_eq_zero (Finset.mem_univ a) h
          linarith
        · exact h
      have hpos0 : 0 < D ⟨0, hk⟩ := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (⟨0, hk⟩ : Fin k))] at hD
        have hP : 0 < ∏ a ∈ Finset.univ.erase (⟨0, hk⟩ : Fin k), D a :=
          Finset.prod_pos (fun a ha => hpos a (Finset.ne_of_mem_erase ha))
        by_contra hc
        nlinarith
      have hall : ∀ a, 0 < D a := by
        intro a
        by_cases ha : a = ⟨0, hk⟩
        · rw [ha]; exact hpos0
        · exact hpos a ha
      apply JoinedIn.of_segment_subset
      rintro z ⟨a, b, ha, hb, hab, rfl⟩
      have hz : a • Matrix.diagonal D + b • (1 : Matrix (Fin k) (Fin k) ℝ)
          = Matrix.diagonal (fun x => a * D x + b) := by
        ext x y
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
          smul_eq_mul]
        split_ifs <;> simp
      change 0 < (a • Matrix.diagonal D + b • (1 : Matrix (Fin k) (Fin k) ℝ)).det
      rw [hz, Matrix.det_diagonal]
      apply Finset.prod_pos
      intro x _
      rcases eq_or_lt_of_le hb with h | h
      · subst h
        have ha1 : a = 1 := by linarith
        subst ha1
        simpa using hall x
      · exact add_pos_of_nonneg_of_pos (mul_nonneg ha (hall x).le) h
    | insert j s hj ih =>
      intro D hD hneg
      by_cases hjD : j ≠ ⟨0, hk⟩ ∧ D j < 0
      · have hD' : Matrix.diagonal D *
            Matrix.diagonal (fun a => if a = ⟨0, hk⟩ ∨ a = j then (-1 : ℝ) else 1)
            = Matrix.diagonal (fun a => if a = ⟨0, hk⟩ ∨ a = j then -D a else D a) := by
          rw [Matrix.diagonal_mul_diagonal]
          congr 1
          funext a
          split_ifs <;> ring
        have hdet : 0 < (Matrix.diagonal D).det := by rw [Matrix.det_diagonal]; exact hD
        have h1 := hflip ⟨0, hk⟩ j (Ne.symm hjD.1) _ hdet
        rw [hD'] at h1
        have hD'pos : 0 < ∏ a, (fun a => if a = ⟨0, hk⟩ ∨ a = j then -D a else D a) a := by
          rw [← Matrix.det_diagonal, ← hD', Matrix.det_mul,
            ← hF ⟨0, hk⟩ j (Ne.symm hjD.1),
            Matrix.TransvectionStruct.det_toMatrix_prod, mul_one]
          exact hdet
        refine h1.trans (ih _ hD'pos ?_)
        intro a ha h
        by_cases haj : a = j
        · subst haj
          simp only [or_true, ↓reduceIte] at h
          linarith [hjD.2]
        · have hDa : D a < 0 := by
            simpa [ha, haj] using h
          rcases Finset.mem_insert.1 (hneg a ha hDa) with h' | h'
          · exact absurd h' haj
          · exact h'
      · apply ih D hD
        intro a ha h
        rcases Finset.mem_insert.1 (hneg a ha h) with h' | h'
        · subst h'
          exact absurd ⟨ha, h⟩ hjD
        · exact h'
  have hone : ∀ A : Matrix (Fin k) (Fin k) ℝ, 0 < A.det →
      JoinedIn {C : Matrix (Fin k) (Fin k) ℝ | 0 < C.det} A 1 := by
    intro A hA
    obtain ⟨L, L', D, rfl⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
    have hdetD : 0 < (Matrix.diagonal D).det := by
      simpa [Matrix.det_mul] using hA
    have e1 := hleft L (Matrix.diagonal D * (L'.map Matrix.TransvectionStruct.toMatrix).prod)
      (by rw [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, mul_one]; exact hdetD)
    rw [← Matrix.mul_assoc] at e1
    refine e1.trans ((hright L' _ hdetD).trans (hdiag Finset.univ D ?_ ?_))
    · rwa [Matrix.det_diagonal] at hdetD
    · intro a _ _
      exact Finset.mem_univ a
  exact (hone A hA).trans (hone B hB).symm

end

end DifferentialGeometry.Topology
