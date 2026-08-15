/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Information.Entropy.RelativeEntropyTraceLog
public import QITBench.Base.Information.Renyi.FrankLieb.Concavity
public import QITBench.Base.Information.Renyi.RenyiDPI.LowAlpha

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology Matrix.Norms.L2Operator

namespace QITBench

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

open RenyiDPI.Statement

theorem sandwichedRenyiQ_marginalA_ge_of_half_lt_lt_one
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a] [Nonempty b]
    {ρ σ : CMatrix (Prod a b)}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ hσ α ≤
      sandwichedRenyiQ
        (partialTraceB ρ) (partialTraceB σ)
        (partialTraceB_posSemidef hρ)
        (partialTraceB_posSemidef hσ)
        α := by
  classical
  let ι : Type v := (b → Bool) × Equiv.Perm b
  let w : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹
  let U : ι → Matrix.unitaryGroup b ℂ :=
    fun idx => permutationUnitary idx.2 * diagonalSignUnitary idx.1
  have hcardR : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hw_sum : ∑ i ∈ (Finset.univ : Finset ι), w i = 1 := by
    dsimp [w]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcardR]
  have hcast : (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) =
      (Fintype.card ι : ℂ)⁻¹ := by
    norm_num [hcardR]
  have hTwirlρ :
      (∑ i ∈ (Finset.univ : Finset ι), (w i : ℂ) •
        ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
          star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))) =
        Matrix.kronecker (partialTraceB ρ) (maximallyMixed b).matrix := by
    simpa [ι, w, U, hcast] using
      localRightSignPermutationTwirl_eq_marginalA_kronecker_maximallyMixed
        (a := a) (b := b) ρ
  have hTwirlσ :
      (∑ i ∈ (Finset.univ : Finset ι), (w i : ℂ) •
        ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
          star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))) =
        Matrix.kronecker (partialTraceB σ) (maximallyMixed b).matrix := by
    simpa [ι, w, U, hcast] using
      localRightSignPermutationTwirl_eq_marginalA_kronecker_maximallyMixed
        (a := a) (b := b) σ
  exact
    sandwichedRenyiQ_marginalA_ge_of_localRightUnitary_twirling
      (a := a) (b := b) (s := Finset.univ) (w := w) (U := U)
      hρ hσ hα_half hα_lt_one hw_nonneg hw_sum hTwirlρ hTwirlσ

theorem sandwichedRenyiQ_stinespringLiftState
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ σ : State a) {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (stinespringLiftState K hTP ρ).matrix
        (stinespringLiftState K hTP σ).matrix
        (stinespringLiftState K hTP ρ).pos
        (stinespringLiftState K hTP σ).pos α =
      sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α := by
  let V := MatrixMap.krausStinespringIsometry K hTP
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos two_pos hα_pos)
  simpa [stinespringLiftState, V] using
    sandwichedRenyiQ_isometry_conj
      (V := V.matrix) V.isometry ρ.pos σ.pos α hs_pos hα_pos

def stinespringLiftMatrix {b : Type v} {κ : Type w}
    [Fintype b] [DecidableEq b] [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (X : CMatrix a) : CMatrix (Prod b κ) :=
  (MatrixMap.krausStinespringIsometry K hTP).matrix * X *
    Matrix.conjTranspose (MatrixMap.krausStinespringIsometry K hTP).matrix

theorem stinespringLiftMatrix_posSemidef
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {X : CMatrix a} (hX : X.PosSemidef) :
    (stinespringLiftMatrix K hTP X).PosSemidef := by
  simpa [stinespringLiftMatrix] using
    hX.mul_mul_conjTranspose_same
      (MatrixMap.krausStinespringIsometry K hTP).matrix

theorem partialTraceB_stinespringLiftMatrix
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (X : CMatrix a) :
    partialTraceB (stinespringLiftMatrix K hTP X) = MatrixMap.ofKraus K X := by
  simpa [stinespringLiftMatrix] using
    MatrixMap.partialTraceB_krausStinespringIsometry K hTP X

theorem sandwichedRenyiQ_stinespringLiftMatrix_reference
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (stinespringLiftState K hTP ρ).matrix
        (stinespringLiftMatrix K hTP σ)
        (stinespringLiftState K hTP ρ).pos
        (stinespringLiftMatrix_posSemidef K hTP hσ) α =
      sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α := by
  let V := MatrixMap.krausStinespringIsometry K hTP
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos two_pos hα_pos)
  simpa [stinespringLiftState, stinespringLiftMatrix, V] using
    sandwichedRenyiQ_isometry_conj
      (V := V.matrix) V.isometry ρ.pos hσ α hs_pos hα_pos

theorem sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α ≤
      sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α := by
  classical
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  let ρL := stinespringLiftState K hTP ρ
  let σL : CMatrix (Prod b (a × b)) := stinespringLiftMatrix K hTP σ
  letI : Nonempty a := ρ.nonempty
  letI : Nonempty b := (Φ.applyState ρ).nonempty
  have hσL : σL.PosSemidef := by
    simpa [σL] using stinespringLiftMatrix_posSemidef K hTP hσ
  have hPT :
      sandwichedRenyiQ ρL.matrix σL ρL.pos hσL α ≤
        sandwichedRenyiQ (partialTraceB ρL.matrix) (partialTraceB σL)
          (partialTraceB_posSemidef ρL.pos) (partialTraceB_posSemidef hσL) α := by
    exact sandwichedRenyiQ_marginalA_ge_of_half_lt_lt_one
      (a := b) (b := a × b) (hρ := ρL.pos) (hσ := hσL)
      hα_half hα_lt_one
  have hIso :
      sandwichedRenyiQ ρL.matrix σL ρL.pos hσL α =
        sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α := by
    simpa [ρL, σL] using
      sandwichedRenyiQ_stinespringLiftMatrix_reference
        K hTP ρ hσ hα_half hα_lt_one
  have hρout : partialTraceB ρL.matrix = (Φ.applyState ρ).matrix := by
    have hstate := stinespringLiftState_marginalA_eq_applyState K Φ hK hTP ρ
    have hm := congrArg State.matrix hstate
    simpa [ρL, State.marginalA] using hm
  have hσout : partialTraceB σL = Φ.map σ := by
    simpa [σL, hK] using partialTraceB_stinespringLiftMatrix K hTP σ
  calc
    sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α =
        sandwichedRenyiQ ρL.matrix σL ρL.pos hσL α := hIso.symm
    _ ≤ sandwichedRenyiQ (partialTraceB ρL.matrix) (partialTraceB σL)
        (partialTraceB_posSemidef ρL.pos) (partialTraceB_posSemidef hσL) α := hPT
    _ = sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α := by
      simp [sandwichedRenyiQ, hρout, hσout]

theorem matrixMap_ofKraus_quadraticForm_sum
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b] [Fintype κ]
    (K : κ → Matrix b a ℂ) (N : CMatrix a) (y : b → ℂ) :
    dotProduct (star y) (Matrix.mulVec ((MatrixMap.ofKraus K) N) y) =
      ∑ k : κ, dotProduct (star (Matrix.mulVec (Matrix.conjTranspose (K k)) y))
        (Matrix.mulVec N (Matrix.mulVec (Matrix.conjTranspose (K k)) y)) := by
  simp [MatrixMap.ofKraus, Matrix.sum_mulVec, dotProduct_sum, Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem matrixMap_ofKraus_supports
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b] [Fintype κ]
    (K : κ → Matrix b a ℂ)
    {M N : CMatrix a} (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    Matrix.Supports ((MatrixMap.ofKraus K) M) ((MatrixMap.ofKraus K) N) := by
  intro y hy
  have hqsum_zero :
      (∑ k : κ, dotProduct (star (Matrix.mulVec (Matrix.conjTranspose (K k)) y))
        (Matrix.mulVec N (Matrix.mulVec (Matrix.conjTranspose (K k)) y))) = 0 := by
    have hqform :
        dotProduct (star y) (Matrix.mulVec ((MatrixMap.ofKraus K) N) y) = 0 := by
      rw [hy]
      simp
    simpa [matrixMap_ofKraus_quadraticForm_sum K N y] using hqform
  have hq_nonneg :
      ∀ k ∈ (Finset.univ : Finset κ),
        0 ≤ dotProduct (star (Matrix.mulVec (Matrix.conjTranspose (K k)) y))
          (Matrix.mulVec N (Matrix.mulVec (Matrix.conjTranspose (K k)) y)) := by
    intro k _hk
    exact hN.dotProduct_mulVec_nonneg _
  have hq_zero :
      ∀ k : κ, dotProduct (star (Matrix.mulVec (Matrix.conjTranspose (K k)) y))
          (Matrix.mulVec N (Matrix.mulVec (Matrix.conjTranspose (K k)) y)) = 0 := by
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonneg hq_nonneg).mp hqsum_zero
      k (Finset.mem_univ k)
  have hpull :
      ∀ k : κ, Matrix.mulVec M (Matrix.mulVec (Matrix.conjTranspose (K k)) y) = 0 := by
    intro k
    exact hSupport (Matrix.mulVec (Matrix.conjTranspose (K k)) y)
      ((hN.dotProduct_mulVec_zero_iff
        (Matrix.mulVec (Matrix.conjTranspose (K k)) y)).mp (hq_zero k))
  have hterm :
      ∀ k : κ, Matrix.mulVec (K k * M * Matrix.conjTranspose (K k)) y = 0 := by
    intro k
    calc
      Matrix.mulVec (K k * M * Matrix.conjTranspose (K k)) y =
          Matrix.mulVec (K k) (Matrix.mulVec M
            (Matrix.mulVec (Matrix.conjTranspose (K k)) y)) := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by simp [hpull k]
  calc
    Matrix.mulVec ((MatrixMap.ofKraus K) M) y =
        ∑ k : κ, Matrix.mulVec (K k * M * Matrix.conjTranspose (K k)) y := by
          simp [MatrixMap.ofKraus, Matrix.sum_mulVec]
    _ = 0 := by simp [hterm]

theorem channel_map_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {M N : CMatrix a} (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    Matrix.Supports (Φ.map M) (Φ.map N) := by
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  simpa [← hK] using matrixMap_ofKraus_supports K hN hSupport

theorem channel_applyState_supports_of_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) := by
  exact channel_map_supports Φ hσ hSupport

def sandwichedRenyiReferenceRegularization (σ : CMatrix a) (ε : ℝ) : CMatrix a :=
  σ + ε • (1 : CMatrix a)

omit [Fintype a] in
@[simp] theorem sandwichedRenyiReferenceRegularization_zero (σ : CMatrix a) :
    sandwichedRenyiReferenceRegularization σ 0 = σ := by
  simp [sandwichedRenyiReferenceRegularization]

omit [Fintype a] in

theorem sandwichedRenyiReferenceRegularization_posDef
    {σ : CMatrix a} (hσ : σ.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (sandwichedRenyiReferenceRegularization σ ε).PosDef := by
  simpa [sandwichedRenyiReferenceRegularization] using
    cMatrix_posSemidef_add_pos_smul_one_posDef hσ hε

omit [Fintype a] in

theorem sandwichedRenyiReferenceRegularization_posSemidef
    {σ : CMatrix a} (hσ : σ.PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) :
    (sandwichedRenyiReferenceRegularization σ ε).PosSemidef := by
  simpa [sandwichedRenyiReferenceRegularization] using
    cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hσ hε

theorem supports_sandwichedRenyiReferenceRegularization_of_pos
    (M : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    Matrix.Supports M (sandwichedRenyiReferenceRegularization σ ε) :=
  Matrix.Supports.of_right_posDef M
    (sandwichedRenyiReferenceRegularization σ ε)
    (sandwichedRenyiReferenceRegularization_posDef hσ hε)

theorem channel_applyState_supports_regularized_reference
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    {ε : ℝ} (hε : 0 < ε) :
    Matrix.Supports (Φ.applyState ρ).matrix
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) := by
  exact channel_applyState_supports_of_supports ρ
    (sandwichedRenyiReferenceRegularization_posSemidef hσ (le_of_lt hε)) Φ
    (supports_sandwichedRenyiReferenceRegularization_of_pos ρ.matrix hσ hε)

omit [Fintype a] in

theorem sandwichedRenyiReferenceRegularization_tendsto
    (σ : CMatrix a) :
    Filter.Tendsto (fun ε : ℝ => sandwichedRenyiReferenceRegularization σ ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds σ) := by
  simpa [sandwichedRenyiReferenceRegularization] using
    cMatrix_tendsto_add_pos_smul_one (A := σ)

theorem sandwichedRenyiReferenceInner_conj_eigenbasis
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ) :
    let s : ℝ := (1 - α) / (2 * α)
    let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
    let D : CMatrix a := Matrix.diagonal
      (fun i => ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))
    star (U : CMatrix a) *
        sandwichedRenyiReferenceInner ρ σ α * (U : CMatrix a) =
      D * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * D := by
  classical
  dsimp
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun i => ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))
  have hpow :
      CFC.rpow σ s = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, s] using cMatrix_rpow_eq_eigenbasis_diagonal hσ s
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp
  change star (U : CMatrix a) *
      ((CFC.rpow σ s) * ρ.matrix * (CFC.rpow σ s)) * (U : CMatrix a) =
    D * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * D
  rw [hpow]
  calc
    star (U : CMatrix a) *
        (((U : CMatrix a) * D * star (U : CMatrix a)) * ρ.matrix *
          ((U : CMatrix a) * D * star (U : CMatrix a))) * (U : CMatrix a)
        = D * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * D := by
          simp [Matrix.mul_assoc, hUstarU]
          rw [← Matrix.mul_assoc, hUstarU, Matrix.one_mul]

theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) (α : ℝ) :
    let s : ℝ := (1 - α) / (2 * α)
    let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
    let Dε : CMatrix a := Matrix.diagonal
      (fun i => (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ))
    star (U : CMatrix a) *
        sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α * (U : CMatrix a) =
      Dε * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * Dε := by
  classical
  dsimp
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let Dε : CMatrix a := Matrix.diagonal
    (fun i => (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ))
  have hpow :
      CFC.rpow (sandwichedRenyiReferenceRegularization σ ε) s =
        (U : CMatrix a) * Dε * star (U : CMatrix a) := by
    simpa [sandwichedRenyiReferenceRegularization, U, Dε, s] using
      cMatrix_rpow_add_nonneg_smul_one_eigenbasis_diagonal hσ hε s
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp
  change star (U : CMatrix a) *
      ((CFC.rpow (sandwichedRenyiReferenceRegularization σ ε) s) * ρ.matrix *
        (CFC.rpow (sandwichedRenyiReferenceRegularization σ ε) s)) * (U : CMatrix a) =
    Dε * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * Dε
  rw [hpow]
  calc
    star (U : CMatrix a) *
        (((U : CMatrix a) * Dε * star (U : CMatrix a)) * ρ.matrix *
          ((U : CMatrix a) * Dε * star (U : CMatrix a))) * (U : CMatrix a)
        = Dε * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * Dε := by
          simp [Matrix.mul_assoc, hUstarU]
          rw [← Matrix.mul_assoc, hUstarU, Matrix.one_mul]

theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_eq_zero
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    {ε : ℝ} (hε : 0 ≤ ε) (α : ℝ) {i j : a}
    (hzero : hσ.isHermitian.eigenvalues i = 0 ∨
      hσ.isHermitian.eigenvalues j = 0) :
    (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
        sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α *
        (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j = 0 := by
  classical
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let Dε : CMatrix a := Matrix.diagonal
    (fun k => (((hσ.isHermitian.eigenvalues k + ε) ^ s : ℝ) : ℂ))
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  have hMzero : M' i j = 0 := by
    simpa [M', U] using
      supports_conjugate_entry_eq_zero_of_left_or_right_zero
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport (i := i) (j := j) hzero
  have hform :=
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis
      ρ hσ hε α
  rw [hform]
  change (Dε * M' * Dε) i j = 0
  simp [Dε, Matrix.mul_apply, Matrix.diagonal, hMzero]

theorem sandwichedRenyiReferenceInner_conj_eigenbasis_entry_eq_zero
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) {i j : a}
    (hzero : hσ.isHermitian.eigenvalues i = 0 ∨
      hσ.isHermitian.eigenvalues j = 0) :
    (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
        sandwichedRenyiReferenceInner ρ σ α *
        (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j = 0 := by
  classical
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun k => ((hσ.isHermitian.eigenvalues k ^ s : ℝ) : ℂ))
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  have hMzero : M' i j = 0 := by
    simpa [M', U] using
      supports_conjugate_entry_eq_zero_of_left_or_right_zero
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport (i := i) (j := j) hzero
  have hform :=
    sandwichedRenyiReferenceInner_conj_eigenbasis
      ρ hσ α
  rw [hform]
  change (D * M' * D) i j = 0
  simp [D, Matrix.mul_apply, Matrix.diagonal, hMzero]

theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) (α : ℝ) (i j : a) :
    let s : ℝ := (1 - α) / (2 * α)
    let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
    (star (U : CMatrix a) *
        sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α *
        (U : CMatrix a)) i j =
      (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ) *
        (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) i j *
          (((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ) : ℂ) := by
  classical
  dsimp
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let Dε : CMatrix a := Matrix.diagonal
    (fun k => (((hσ.isHermitian.eigenvalues k + ε) ^ s : ℝ) : ℂ))
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  have hform :=
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis
      ρ hσ hε α
  rw [hform]
  change (Dε * M' * Dε) i j =
    (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ) *
      M' i j * (((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ) : ℂ)
  simp [Dε, M', Matrix.mul_apply, Matrix.diagonal]

theorem sandwichedRenyiReferenceInner_conj_eigenbasis_entry
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (i j : a) :
    let s : ℝ := (1 - α) / (2 * α)
    let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
    (star (U : CMatrix a) *
        sandwichedRenyiReferenceInner ρ σ α *
        (U : CMatrix a)) i j =
      ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
        (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) i j *
          ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ) := by
  classical
  dsimp
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun k => ((hσ.isHermitian.eigenvalues k ^ s : ℝ) : ℂ))
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  have hform :=
    sandwichedRenyiReferenceInner_conj_eigenbasis
      ρ hσ α
  rw [hform]
  change (D * M' * D) i j =
    ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
      M' i j * ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ)
  simp [D, M', Matrix.mul_apply, Matrix.diagonal]

theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_tendsto
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (i j : a) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ
            (sandwichedRenyiReferenceRegularization σ ε) α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        ((star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j)) := by
  classical
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  by_cases hi0 : hσ.isHermitian.eigenvalues i = 0
  · have htarget :
        (star (U : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a)) i j = 0 := by
      simpa [U] using
        sandwichedRenyiReferenceInner_conj_eigenbasis_entry_eq_zero
          ρ hσ hSupport α (i := i) (j := j) (Or.inl hi0)
    rw [htarget]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    symm
    simpa [U] using
      sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_eq_zero
        ρ hσ hSupport (le_of_lt hε) α (i := i) (j := j) (Or.inl hi0)
  by_cases hj0 : hσ.isHermitian.eigenvalues j = 0
  · have htarget :
        (star (U : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a)) i j = 0 := by
      simpa [U] using
        sandwichedRenyiReferenceInner_conj_eigenbasis_entry_eq_zero
          ρ hσ hSupport α (i := i) (j := j) (Or.inr hj0)
    rw [htarget]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    symm
    simpa [U] using
      sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_eq_zero
        ρ hσ hSupport (le_of_lt hε) α (i := i) (j := j) (Or.inr hj0)
  have hi_pos : 0 < hσ.isHermitian.eigenvalues i := by
    exact lt_of_le_of_ne (hσ.eigenvalues_nonneg i) (by
      intro h
      exact hi0 h.symm)
  have hj_pos : 0 < hσ.isHermitian.eigenvalues j := by
    exact lt_of_le_of_ne (hσ.eigenvalues_nonneg j) (by
      intro h
      exact hj0 h.symm)
  have hlin_i :
      Filter.Tendsto (fun ε : ℝ => hσ.isHermitian.eigenvalues i + ε)
        l (nhds (hσ.isHermitian.eigenvalues i)) := by
    have hcont : Continuous fun ε : ℝ => hσ.isHermitian.eigenvalues i + ε := by
      fun_prop
    simpa [l] using
      (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioi (0 : ℝ))).tendsto
  have hlin_j :
      Filter.Tendsto (fun ε : ℝ => hσ.isHermitian.eigenvalues j + ε)
        l (nhds (hσ.isHermitian.eigenvalues j)) := by
    have hcont : Continuous fun ε : ℝ => hσ.isHermitian.eigenvalues j + ε := by
      fun_prop
    simpa [l] using
      (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioi (0 : ℝ))).tendsto
  have hpow_i :
      Filter.Tendsto
        (fun ε : ℝ => ((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ))
        l (nhds (hσ.isHermitian.eigenvalues i ^ s)) := by
    exact
      (Real.continuousAt_rpow_const (hσ.isHermitian.eigenvalues i) s
        (Or.inl (ne_of_gt hi_pos))).tendsto.comp hlin_i
  have hpow_j :
      Filter.Tendsto
        (fun ε : ℝ => ((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ))
        l (nhds (hσ.isHermitian.eigenvalues j ^ s)) := by
    exact
      (Real.continuousAt_rpow_const (hσ.isHermitian.eigenvalues j) s
        (Or.inl (ne_of_gt hj_pos))).tendsto.comp hlin_j
  have hcpow_i :
      Filter.Tendsto
        (fun ε : ℝ => (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ))
        l (nhds (((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.tendsto _ |>.comp hpow_i
  have hcpow_j :
      Filter.Tendsto
        (fun ε : ℝ => (((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ) : ℂ))
        l (nhds (((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.tendsto _ |>.comp hpow_j
  have hexplicit :
      Filter.Tendsto
        (fun ε : ℝ =>
          (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ) *
            M' i j *
              (((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ) : ℂ))
        l
        (nhds
          (((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
            M' i j *
              (((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ)))) := by
    exact (hcpow_i.mul tendsto_const_nhds).mul hcpow_j
  have htarget :
      (star (U : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a)) i j =
        ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
          M' i j * ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ) := by
    simpa [s, U, M'] using
      sandwichedRenyiReferenceInner_conj_eigenbasis_entry
        ρ hσ α i j
  rw [htarget]
  refine hexplicit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  symm
  simpa [s, U, M'] using
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry
      ρ hσ (le_of_lt hε) α i j

theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_tendsto
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ
            (sandwichedRenyiReferenceRegularization σ ε) α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a))) := by
  change Filter.Tendsto
      (fun ε : ℝ => fun i => fun j =>
        (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ
            (sandwichedRenyiReferenceRegularization σ ε) α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (fun i => fun j =>
          (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
            sandwichedRenyiReferenceInner ρ σ α *
            (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_tendsto
      ρ hσ hSupport α i j

theorem sandwichedRenyiReferenceInner_regularization_tendsto_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (sandwichedRenyiReferenceInner ρ σ α)) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  have hconj :=
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_tendsto
      ρ hσ hSupport α
  have hcont : Continuous fun X : CMatrix a => (U : CMatrix a) * X * star (U : CMatrix a) := by
    fun_prop
  have hback :=
    (hcont.tendsto
      (star (U : CMatrix a) * sandwichedRenyiReferenceInner ρ σ α *
        (U : CMatrix a))).comp hconj
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp
  change Filter.Tendsto
      (fun ε : ℝ =>
        (U : CMatrix a) *
          (star (U : CMatrix a) *
            sandwichedRenyiReferenceInner ρ
              (sandwichedRenyiReferenceRegularization σ ε) α *
            (U : CMatrix a)) *
          star (U : CMatrix a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        ((U : CMatrix a) *
          (star (U : CMatrix a) *
            sandwichedRenyiReferenceInner ρ σ α *
            (U : CMatrix a)) *
          star (U : CMatrix a))) at hback
  have hback' :
      Filter.Tendsto
        (fun ε : ℝ =>
          (U : CMatrix a) *
            (star (U : CMatrix a) *
              sandwichedRenyiReferenceInner ρ
                (sandwichedRenyiReferenceRegularization σ ε) α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          ((U : CMatrix a) *
            (star (U : CMatrix a) *
              sandwichedRenyiReferenceInner ρ σ α))) := by
    simpa [Matrix.mul_assoc, hUstarU] using hback
  have htarget :
      (U : CMatrix a) *
          (star (U : CMatrix a) * sandwichedRenyiReferenceInner ρ σ α) =
        sandwichedRenyiReferenceInner ρ σ α := by
    rw [← Matrix.mul_assoc, hUUstar, Matrix.one_mul]
  rw [htarget] at hback'
  refine hback'.congr' ?_
  filter_upwards with ε
  symm
  rw [← Matrix.mul_assoc, hUUstar, Matrix.one_mul]

theorem sandwichedRenyiReferenceInner_ne_zero_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) :
    sandwichedRenyiReferenceInner ρ σ α ≠ 0 := by
  classical
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  intro hinner_zero
  have hconj_zero :
      star (U : CMatrix a) * sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a) = 0 := by
    rw [hinner_zero]
    simp
  have hM'_zero : M' = 0 := by
    ext i j
    by_cases hi0 : hσ.isHermitian.eigenvalues i = 0
    · simpa [M', U] using
        supports_conjugate_entry_eq_zero_of_left_or_right_zero
          (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
          (i := i) (j := j) (Or.inl hi0)
    by_cases hj0 : hσ.isHermitian.eigenvalues j = 0
    · simpa [M', U] using
        supports_conjugate_entry_eq_zero_of_left_or_right_zero
          (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
          (i := i) (j := j) (Or.inr hj0)
    have hi_pos : 0 < hσ.isHermitian.eigenvalues i := by
      exact lt_of_le_of_ne (hσ.eigenvalues_nonneg i) (by
        intro h
        exact hi0 h.symm)
    have hj_pos : 0 < hσ.isHermitian.eigenvalues j := by
      exact lt_of_le_of_ne (hσ.eigenvalues_nonneg j) (by
        intro h
        exact hj0 h.symm)
    have hentry_zero :
        (star (U : CMatrix a) * sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a)) i j = 0 := by
      simpa using congrArg (fun M : CMatrix a => M i j) hconj_zero
    have hentry_formula :
        (star (U : CMatrix a) *
            sandwichedRenyiReferenceInner ρ σ α *
            (U : CMatrix a)) i j =
          ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
            M' i j * ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ) := by
      simpa [s, U, M'] using
        sandwichedRenyiReferenceInner_conj_eigenbasis_entry
          ρ hσ α i j
    rw [hentry_formula] at hentry_zero
    have hi_ne :
        ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast
        (ne_of_gt (Real.rpow_pos_of_pos hi_pos s))
    have hj_ne :
        ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast
        (ne_of_gt (Real.rpow_pos_of_pos hj_pos s))
    have hleft :
        ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) * M' i j = 0 :=
      (mul_eq_zero.mp hentry_zero).resolve_right hj_ne
    exact (mul_eq_zero.mp hleft).resolve_left hi_ne
  have hρ_zero : ρ.matrix = 0 := by
    have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
      simp
    have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
      simp
    calc
      ρ.matrix = (U : CMatrix a) * M' * star (U : CMatrix a) := by
        symm
        calc
          (U : CMatrix a) * M' * star (U : CMatrix a) =
              (U : CMatrix a) *
                (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) *
                  star (U : CMatrix a) := by
                rfl
          _ = ((U : CMatrix a) * star (U : CMatrix a)) * ρ.matrix *
                ((U : CMatrix a) * star (U : CMatrix a)) := by
                noncomm_ring
          _ = ρ.matrix := by
                rw [hUUstar]
                simp
      _ = 0 := by
        rw [hM'_zero]
        simp
  exact ρ.matrix_ne_zero hρ_zero

theorem sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) :
    0 <
      psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
        (sandwichedRenyiReferenceInner_posSemidef ρ hσ α) α :=
  psdTracePower_pos_of_ne_zero
    (sandwichedRenyiReferenceInner ρ σ α)
    (sandwichedRenyiReferenceInner_posSemidef ρ hσ α)
    (sandwichedRenyiReferenceInner_ne_zero_of_supports ρ hσ hSupport α)

theorem sandwichedRenyiReferenceInner_tracePower_regularization_tendsto_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (hα_pos : 0 < α) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ((CFC.rpow
          (sandwichedRenyiReferenceInner ρ
            (sandwichedRenyiReferenceRegularization σ ε) α) α).trace).re)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        ((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re) := by
  have hinner :=
    sandwichedRenyiReferenceInner_regularization_tendsto_of_supports
      ρ hσ hSupport α
  have hinner_psd_event :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact
      sandwichedRenyiReferenceInner_posSemidef ρ
        (sandwichedRenyiReferenceRegularization_posSemidef hσ (le_of_lt hε)) α
  exact
    cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
      hα_pos hinner hinner_psd_event
      (sandwichedRenyiReferenceInner_posSemidef ρ hσ α)

def sandwichedRenyiPSDReferenceLowAlpha
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * log2 (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α)

theorem sandwichedRenyiPSDReferenceLowAlpha_eq_reference_posDef
    (ρ : State a) {σ : CMatrix a}
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ.posSemidef α =
      sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one := by
  rfl

theorem sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) :
    sandwichedRenyiPSDReferenceLowAlpha
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α := by
  have hQ :=
    sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
      ρ hσ Φ α hα_half hα_lt_one
  have hlog :
      log2 (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) ≤
        log2 (sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α) := by
    unfold log2
    exact div_le_div_of_nonneg_right (Real.log_le_log hQpos hQ)
      (le_of_lt (Real.log_pos one_lt_two))
  have hcoef_nonpos : 1 / (α - 1) ≤ 0 := by
    have hcoef_neg : 1 / (α - 1) < 0 := by
      simpa [one_div] using (inv_lt_zero.2 (sub_neg.mpr hα_lt_one))
    exact le_of_lt hcoef_neg
  simpa [sandwichedRenyiPSDReferenceLowAlpha] using
    mul_le_mul_of_nonpos_left hlog hcoef_nonpos

def sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (ε : ℝ) : ℝ :=
  if hε : 0 ≤ ε then
    sandwichedRenyiPSDReferenceLowAlpha ρ
      (sandwichedRenyiReferenceRegularization σ ε)
      (sandwichedRenyiReferenceRegularization_posSemidef hσ hε) α
  else
    sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α

def sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ) (ε : ℝ) : ℝ :=
  if hε : 0 ≤ ε then
    sandwichedRenyiPSDReferenceLowAlpha (Φ.applyState ρ)
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
      (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posSemidef hσ hε)) α
  else
    sandwichedRenyiPSDReferenceLowAlpha (Φ.applyState ρ)
      (Φ.map σ) (Φ.mapsPositive σ hσ) α

theorem sandwichedRenyiPSDReferenceLowAlphaRegularizedCurves_eventually_le
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve ρ hσ Φ α ε ≤
        sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve ρ hσ α ε := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  have hσreg_psd :
      (sandwichedRenyiReferenceRegularization σ ε).PosSemidef :=
    sandwichedRenyiReferenceRegularization_posSemidef hσ hε_nonneg
  have hσreg_pd :
      (sandwichedRenyiReferenceRegularization σ ε).PosDef :=
    sandwichedRenyiReferenceRegularization_posDef hσ hε
  have hQpos :
      0 < sandwichedRenyiQ ρ.matrix
        (sandwichedRenyiReferenceRegularization σ ε)
        ρ.pos hσreg_psd α :=
    sandwichedRenyiQ_pos_of_state_posDef_reference ρ hσreg_pd α
  have hDPI :=
    sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel
      ρ hσreg_psd Φ α hα_half hα_lt_one hQpos
  simpa [sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve,
    sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve, hε_nonneg]
    using hDPI

theorem sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve_tendsto
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve ρ hσ α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let σF : ℝ → CMatrix a := fun ε =>
    if hε : 0 ≤ ε then sandwichedRenyiReferenceRegularization σ ε else σ
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos two_pos hα_pos)
  have hσF_psd : ∀ ε, (σF ε).PosSemidef := by
    intro ε
    by_cases hε : 0 ≤ ε
    · simpa [σF, hε] using
        sandwichedRenyiReferenceRegularization_posSemidef hσ hε
    · simpa [σF, hε] using hσ
  have hσF_tend : Filter.Tendsto σF l (nhds σ) := by
    have hreg := sandwichedRenyiReferenceRegularization_tendsto (a := a) σ
    have hcongr :
        (fun ε : ℝ => sandwichedRenyiReferenceRegularization σ ε) =ᶠ[l] σF := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nonneg : 0 ≤ ε := le_of_lt hε
      simp [σF, hε_nonneg]
    exact Filter.Tendsto.congr' hcongr hreg
  have hQ_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ ρ.matrix (σF ε) ρ.pos (hσF_psd ε) α)
        l
        (nhds (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos tendsto_const_nhds hσF_tend
      (fun _ => ρ.pos) hσF_psd ρ.pos hσ
  have hlog_tend :
      Filter.Tendsto
        (fun ε => log2 (sandwichedRenyiQ ρ.matrix (σF ε) ρ.pos (hσF_psd ε) α))
        l
        (nhds (log2 (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α))) := by
    have hraw := Filter.Tendsto.log hQ_tend (ne_of_gt hQpos)
    simpa [log2] using
      hraw.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  have hdiv_tend :
      Filter.Tendsto
        (fun ε =>
          (1 / (α - 1)) *
            log2 (sandwichedRenyiQ ρ.matrix (σF ε) ρ.pos (hσF_psd ε) α))
        l
        (nhds
          ((1 / (α - 1)) *
            log2 (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α))) :=
    hlog_tend.const_mul (1 / (α - 1))
  have hcurve :
      (fun ε =>
          (1 / (α - 1)) *
            log2 (sandwichedRenyiQ ρ.matrix (σF ε) ρ.pos (hσF_psd ε) α))
        =ᶠ[l]
      sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve ρ hσ α := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_nonneg : 0 ≤ ε := le_of_lt hε
    simp [sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve,
      sandwichedRenyiPSDReferenceLowAlpha, σF, hε_nonneg]
  exact Filter.Tendsto.congr' hcurve hdiv_tend

theorem sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve_tendsto
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos :
      0 < sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve ρ hσ Φ α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (sandwichedRenyiPSDReferenceLowAlpha
          (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let σF : ℝ → CMatrix b := fun ε =>
    if hε : 0 ≤ ε then
      Φ.map (sandwichedRenyiReferenceRegularization σ ε)
    else
      Φ.map σ
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos two_pos hα_pos)
  have hσF_psd : ∀ ε, (σF ε).PosSemidef := by
    intro ε
    by_cases hε : 0 ≤ ε
    · simpa [σF, hε] using
        Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
          (sandwichedRenyiReferenceRegularization_posSemidef hσ hε)
    · simpa [σF, hε] using Φ.mapsPositive σ hσ
  have hσF_tend : Filter.Tendsto σF l (nhds (Φ.map σ)) := by
    have hreg := sandwichedRenyiReferenceRegularization_tendsto (a := a) σ
    have hmap :
        Filter.Tendsto
          (fun ε : ℝ => Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          l (nhds (Φ.map σ)) :=
      (LinearMap.continuous_of_finiteDimensional Φ.map).tendsto σ |>.comp hreg
    have hcongr :
        (fun ε : ℝ => Φ.map (sandwichedRenyiReferenceRegularization σ ε)) =ᶠ[l] σF := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nonneg : 0 ≤ ε := le_of_lt hε
      simp [σF, hε_nonneg]
    exact Filter.Tendsto.congr' hcongr hmap
  have hQ_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ (Φ.applyState ρ).matrix (σF ε)
          (Φ.applyState ρ).pos (hσF_psd ε) α)
        l
        (nhds
          (sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos tendsto_const_nhds hσF_tend
      (fun _ => (Φ.applyState ρ).pos) hσF_psd
      (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ)
  have hlog_tend :
      Filter.Tendsto
        (fun ε => log2
          (sandwichedRenyiQ (Φ.applyState ρ).matrix (σF ε)
            (Φ.applyState ρ).pos (hσF_psd ε) α))
        l
        (nhds (log2
          (sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α))) := by
    have hraw := Filter.Tendsto.log hQ_tend (ne_of_gt hQpos)
    simpa [log2] using
      hraw.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  have hdiv_tend :
      Filter.Tendsto
        (fun ε =>
          (1 / (α - 1)) *
            log2
              (sandwichedRenyiQ (Φ.applyState ρ).matrix (σF ε)
                (Φ.applyState ρ).pos (hσF_psd ε) α))
        l
        (nhds
          ((1 / (α - 1)) *
            log2
              (sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
                (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α))) :=
    hlog_tend.const_mul (1 / (α - 1))
  have hcurve :
      (fun ε =>
          (1 / (α - 1)) *
            log2
              (sandwichedRenyiQ (Φ.applyState ρ).matrix (σF ε)
                (Φ.applyState ρ).pos (hσF_psd ε) α))
        =ᶠ[l]
      sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve ρ hσ Φ α := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_nonneg : 0 ≤ ε := le_of_lt hε
    simp [sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve,
      sandwichedRenyiPSDReferenceLowAlpha, σF, hε_nonneg]
  exact Filter.Tendsto.congr' hcurve hdiv_tend

private theorem frankLieb_log2_mono_of_pos {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) :
    log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos one_lt_two))

theorem sandwichedRenyiReference_le_of_lowAlphaQ_ge
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρIn : State a) {σIn : CMatrix a}
    (ρOut : State b) {σOut : CMatrix b}
    (hρIn : ρIn.matrix.PosDef) (hσIn : σIn.PosDef)
    (hρOut : ρOut.matrix.PosDef) (hσOut : σOut.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQ :
      sandwichedRenyiQ ρIn.matrix σIn ρIn.pos hσIn.posSemidef α ≤
        sandwichedRenyiQ ρOut.matrix σOut ρOut.pos hσOut.posSemidef α) :
    sandwichedRenyiReference ρOut σOut hρOut hσOut α
        (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyiReference ρIn σIn hρIn hσIn α
        (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  rw [sandwichedRenyiReference_eq_log2_psdTracePower_inner
      ρOut hρOut hσOut α hα_pos hα_ne_one,
    sandwichedRenyiReference_eq_log2_psdTracePower_inner
      ρIn hρIn hσIn α hα_pos hα_ne_one]
  have hpower :
      psdTracePower (sandwichedRenyiReferenceInner ρIn σIn α)
          (sandwichedRenyiReferenceInner_posSemidef ρIn hσIn.posSemidef α) α ≤
        psdTracePower (sandwichedRenyiReferenceInner ρOut σOut α)
          (sandwichedRenyiReferenceInner_posSemidef ρOut hσOut.posSemidef α) α := by
    simpa [sandwichedRenyiQ_eq_psdTracePower_referenceInner] using hQ
  have hin_pos :
      0 <
        psdTracePower (sandwichedRenyiReferenceInner ρIn σIn α)
          (sandwichedRenyiReferenceInner_posSemidef ρIn hσIn.posSemidef α) α :=
    sandwichedRenyiReferenceInner_psdTracePower_pos ρIn hρIn hσIn α
  have hlog := frankLieb_log2_mono_of_pos hin_pos hpower
  have hcoef_nonpos : 1 / (α - 1) ≤ 0 := by
    have hcoef_neg : 1 / (α - 1) < 0 := by
      simpa [one_div] using (inv_lt_zero.2 (sub_neg.mpr hα_lt_one))
    exact le_of_lt hcoef_neg
  exact mul_le_mul_of_nonpos_left hlog hcoef_nonpos

theorem sandwichedRenyiReference_dataProcessing_channel_of_half_lt_lt_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ)
        hρΦ hσΦ α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyiReference ρ σ hρ hσ α
        (by linarith) (ne_of_lt hα_lt_one) := by
  have hQ :=
    sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
      ρ hσ.posSemidef Φ α hα_half hα_lt_one
  exact
    sandwichedRenyiReference_le_of_lowAlphaQ_ge
      ρ (Φ.applyState ρ) hρ hσ hρΦ hσΦ α hα_half hα_lt_one hQ

theorem sandwichedRenyi_dataProcessing_channel_statement_of_half_lt_lt_one_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  classical
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  let ρL := stinespringLiftState K hTP ρ
  let σL := stinespringLiftState K hTP σ
  letI : Nonempty a := ρ.nonempty
  letI : Nonempty b := (Φ.applyState ρ).nonempty
  have hPT :
      sandwichedRenyiQ ρL.matrix σL.matrix ρL.pos σL.pos α ≤
        sandwichedRenyiQ (partialTraceB ρL.matrix) (partialTraceB σL.matrix)
          (partialTraceB_posSemidef ρL.pos) (partialTraceB_posSemidef σL.pos) α := by
    exact sandwichedRenyiQ_marginalA_ge_of_half_lt_lt_one
      (a := b) (b := a × b) (hρ := ρL.pos) (hσ := σL.pos)
      hα_half hα_lt_one
  have hIso :
      sandwichedRenyiQ ρL.matrix σL.matrix ρL.pos σL.pos α =
        sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α := by
    simpa [ρL, σL] using
      sandwichedRenyiQ_stinespringLiftState K hTP ρ σ hα_half hα_lt_one
  have hρout : partialTraceB ρL.matrix = (Φ.applyState ρ).matrix := by
    have hstate := stinespringLiftState_marginalA_eq_applyState K Φ hK hTP ρ
    have hm := congrArg State.matrix hstate
    simpa [ρL, State.marginalA] using hm
  have hσout : partialTraceB σL.matrix = (Φ.applyState σ).matrix := by
    have hstate := stinespringLiftState_marginalA_eq_applyState K Φ hK hTP σ
    have hm := congrArg State.matrix hstate
    simpa [σL, State.marginalA] using hm
  have hQ :
      sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α ≤
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ).pos α := by
    calc
      sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α =
          sandwichedRenyiQ ρL.matrix σL.matrix ρL.pos σL.pos α := hIso.symm
      _ ≤ sandwichedRenyiQ (partialTraceB ρL.matrix) (partialTraceB σL.matrix)
          (partialTraceB_posSemidef ρL.pos) (partialTraceB_posSemidef σL.pos) α := hPT
      _ = sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ).pos α := by
        simp [sandwichedRenyiQ, hρout, hσout]
  exact
    sandwichedRenyi_dataProcessing_le_of_lowAlphaQ_ge
      ρ σ Φ hρ hσ hρΦ hσΦ α (le_of_lt hα_half) hα_lt_one hQ

theorem sandwichedRenyi_dataProcessing_channel_statement_of_half_le_lt_one_or_one_lt_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α
      (by
        rcases hα_range with hlow | hhigh
        · exact hlow.1
        · linarith)
      (by
        rcases hα_range with hlow | hhigh
        · exact ne_of_lt hlow.2
        · exact ne_of_gt hhigh) := by
  rcases hα_range with hlow | hhigh
  · rcases hlow with ⟨hhalf, hlt⟩
    by_cases hEq : α = 1 / 2
    · exact sandwichedRenyi_dataProcessing_channel_statement_of_eq_half_or_one_lt
        ρ σ Φ hρ hσ hρΦ hσΦ α (Or.inl hEq)
    · have hhalf_strict : 1 / 2 < α := by
        exact lt_of_le_of_ne hhalf (Ne.symm hEq)
      exact sandwichedRenyi_dataProcessing_channel_statement_of_half_lt_lt_one_channel
        ρ σ Φ hρ hσ hρΦ hσΦ α hhalf_strict hlt
  · exact sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
      ρ σ Φ hρ hσ hρΦ hσΦ α hhigh

theorem sandwichedRenyi_dataProcessing_channel_posDef_reference
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) (σ : CMatrix a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ) hρΦ hσΦ α
        (by
          rcases hα_range with hlow | hhigh
          · linarith
          · linarith)
        (by
          rcases hα_range with hlow | hhigh
          · exact ne_of_lt hlow.2
          · exact ne_of_gt hhigh) ≤
      sandwichedRenyiReference ρ σ hρ hσ α
        (by
          rcases hα_range with hlow | hhigh
          · linarith
          · linarith)
        (by
          rcases hα_range with hlow | hhigh
          · exact ne_of_lt hlow.2
          · exact ne_of_gt hhigh) := by
  classical
  let lambda : ℝ := (σ.trace.re)⁻¹
  have htr_pos : 0 < σ.trace.re :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hσ)).1
  have hlambda_pos : 0 < lambda := by
    exact inv_pos.mpr htr_pos
  have hα_pos : 0 < α := by
    rcases hα_range with hlow | hhigh <;> linarith
  have hα_ne_one : α ≠ 1 := by
    rcases hα_range with hlow | hhigh
    · exact ne_of_lt hlow.2
    · exact ne_of_gt hhigh
  let σ₀ : State a := stateOfPosDefReference σ hσ
  have hσ₀ : σ₀.matrix.PosDef := by
    simpa [σ₀] using stateOfPosDefReference_posDef σ hσ
  have hσ₀Φ : (Φ.applyState σ₀).matrix.PosDef := by
    have hmap :
        (Φ.applyState σ₀).matrix = lambda • Φ.map σ := by
      change Φ.map (lambda • σ : CMatrix a) = lambda • Φ.map σ
      change Φ.map (((lambda : ℝ) : ℂ) • σ) =
        (((lambda : ℝ) : ℂ) • Φ.map σ)
      simp [lambda]
    rw [hmap]
    exact Matrix.PosDef.smul hσΦ hlambda_pos
  have hDPI :=
    sandwichedRenyi_dataProcessing_channel_statement_of_half_le_lt_one_or_one_lt_channel
      ρ σ₀ Φ hρ hσ₀ hρΦ hσ₀Φ α hα_range
  have hin :
      sandwichedRenyi ρ σ₀ hρ hσ₀ α hα_pos hα_ne_one =
        sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one -
          log2 lambda := by
    rw [← sandwichedRenyiReference_state ρ σ₀ hρ hσ₀ α hα_pos hα_ne_one]
    simpa [σ₀, lambda, stateOfPosDefReference] using
      sandwichedRenyiReference_real_smul_reference
        ρ hρ hσ hlambda_pos α hα_pos hα_ne_one
  have hout :
      sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ₀)
          hρΦ hσ₀Φ α hα_pos hα_ne_one =
        sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ)
          hρΦ hσΦ α hα_pos hα_ne_one - log2 lambda := by
    rw [← sandwichedRenyiReference_state
      (Φ.applyState ρ) (Φ.applyState σ₀) hρΦ hσ₀Φ α hα_pos hα_ne_one]
    have hmap :
        (Φ.applyState σ₀).matrix = lambda • Φ.map σ := by
      change Φ.map (lambda • σ : CMatrix a) = lambda • Φ.map σ
      change Φ.map (((lambda : ℝ) : ℂ) • σ) =
        (((lambda : ℝ) : ℂ) • Φ.map σ)
      simp [lambda]
    simpa [hmap] using
      sandwichedRenyiReference_real_smul_reference
        (Φ.applyState ρ) hρΦ hσΦ hlambda_pos α hα_pos hα_ne_one
  have hshift :
      sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ)
          hρΦ hσΦ α hα_pos hα_ne_one - log2 lambda ≤
        sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one -
          log2 lambda := by
    simpa [sandwichedRenyi_dataProcessing_channel_statement, hin, hout] using hDPI
  linarith

theorem Channel.map_sandwichedRenyiReferenceRegularization
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (σ : CMatrix a) (ε : ℝ) :
    Φ.map (sandwichedRenyiReferenceRegularization σ ε) =
      Φ.map σ + ε • Φ.map (1 : CMatrix a) := by
  change Φ.map (σ + (((ε : ℝ) : ℂ) • (1 : CMatrix a))) =
    Φ.map σ + (((ε : ℝ) : ℂ) • Φ.map (1 : CMatrix a))
  simp [map_add]

theorem Channel.map_supports_map_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (_hσ : σ.PosSemidef) :
    Matrix.Supports (Φ.map σ) (Φ.map (1 : CMatrix a)) := by
  exact channel_map_supports Φ Matrix.PosSemidef.one
    (Matrix.Supports.of_right_posDef σ (1 : CMatrix a) Matrix.PosDef.one)

theorem Channel.applyState_fixed_by_map_one_supportProjector
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (ρ : State a) :
    let Pi : CMatrix b :=
      psdInvSqrt (Φ.map (1 : CMatrix a))
          (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one).isHermitian *
        (Φ.map (1 : CMatrix a)) *
        psdInvSqrt (Φ.map (1 : CMatrix a))
          (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one).isHermitian
    Pi * (Φ.applyState ρ).matrix = (Φ.applyState ρ).matrix ∧
      (Φ.applyState ρ).matrix * Pi = (Φ.applyState ρ).matrix := by
  exact
    _root_.QITBench.supportProjector_fixes_of_supports
      (M := (Φ.applyState ρ).matrix)
      (N := Φ.map (1 : CMatrix a))
      (Φ.applyState ρ).pos
      (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one)
      (channel_applyState_supports_of_supports ρ Matrix.PosSemidef.one Φ
        (Matrix.Supports.of_right_posDef ρ.matrix (1 : CMatrix a)
          Matrix.PosDef.one))

theorem Channel.applyState_supports_map_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (ρ : State a) :
    Matrix.Supports (Φ.applyState ρ).matrix (Φ.map (1 : CMatrix a)) :=
  channel_applyState_supports_of_supports ρ Matrix.PosSemidef.one Φ
    (Matrix.Supports.of_right_posDef ρ.matrix (1 : CMatrix a)
      Matrix.PosDef.one)

theorem Channel.map_regularized_reference_supports_map_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (_hε : 0 ≤ ε) :
    Matrix.Supports (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
      (Φ.map (1 : CMatrix a)) := by
  rw [Channel.map_sandwichedRenyiReferenceRegularization]
  exact Matrix.Supports.add_left
    (Channel.map_supports_map_one Φ hσ)
    (Matrix.Supports.smul_left (((ε : ℝ) : ℂ)
      ) (Matrix.Supports.refl (Φ.map (1 : CMatrix a))))

theorem Channel.map_one_supports_regularized_reference
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    Matrix.Supports (Φ.map (1 : CMatrix a))
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) := by
  rw [Channel.map_sandwichedRenyiReferenceRegularization]
  exact Matrix.Supports.of_pos_smul_right_add
    (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one)
    (Φ.mapsPositive σ hσ) hε

theorem Channel.map_regularized_reference_fixed_by_map_one_supportProjector
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) :
    let Pi : CMatrix b :=
      psdInvSqrt (Φ.map (1 : CMatrix a))
          (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one).isHermitian *
        (Φ.map (1 : CMatrix a)) *
        psdInvSqrt (Φ.map (1 : CMatrix a))
          (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one).isHermitian
    Pi * (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) =
        Φ.map (sandwichedRenyiReferenceRegularization σ ε) ∧
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) * Pi =
        Φ.map (sandwichedRenyiReferenceRegularization σ ε) := by
  exact
    _root_.QITBench.supportProjector_fixes_of_supports
      (M := Φ.map (sandwichedRenyiReferenceRegularization σ ε))
      (N := Φ.map (1 : CMatrix a))
      (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posSemidef hσ hε))
      (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one)
      (Channel.map_regularized_reference_supports_map_one Φ hσ hε)

theorem Channel.map_one_fixed_by_regularized_reference_supportProjector
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    let SigmaEps : CMatrix b := Φ.map (sandwichedRenyiReferenceRegularization σ ε)
    let hSigmaEps : SigmaEps.PosSemidef :=
      Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posSemidef hσ (le_of_lt hε))
    let Pi : CMatrix b :=
      psdInvSqrt SigmaEps hSigmaEps.isHermitian * SigmaEps *
        psdInvSqrt SigmaEps hSigmaEps.isHermitian
    Pi * (Φ.map (1 : CMatrix a)) = Φ.map (1 : CMatrix a) ∧
      (Φ.map (1 : CMatrix a)) * Pi = Φ.map (1 : CMatrix a) := by
  exact
    _root_.QITBench.supportProjector_fixes_of_supports
      (M := Φ.map (1 : CMatrix a))
      (N := Φ.map (sandwichedRenyiReferenceRegularization σ ε))
      (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one)
      (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posSemidef hσ (le_of_lt hε)))
      (Channel.map_one_supports_regularized_reference Φ hσ hε)

theorem Channel.applyState_supports_map_regularized_reference
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    Matrix.Supports (Φ.applyState ρ).matrix
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) := by
  intro v hv
  exact
    (Channel.applyState_supports_map_one Φ ρ) v
      ((Channel.map_one_supports_regularized_reference Φ hσ hε) v hv)

theorem sandwichedRenyiReference_dataProcessing_channel_regularized
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α)
    {ε : ℝ} (hε : 0 < ε)
    (hσΦε :
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef) :
    sandwichedRenyiReference (Φ.applyState ρ)
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
        hρΦ hσΦε α
        (by
          rcases hα_range with hlow | hhigh
          · linarith
          · linarith)
        (by
          rcases hα_range with hlow | hhigh
          · exact ne_of_lt hlow.2
          · exact ne_of_gt hhigh) ≤
      sandwichedRenyiReference ρ (sandwichedRenyiReferenceRegularization σ ε)
        hρ (sandwichedRenyiReferenceRegularization_posDef hσ hε) α
        (by
          rcases hα_range with hlow | hhigh
          · linarith
          · linarith)
        (by
          rcases hα_range with hlow | hhigh
          · exact ne_of_lt hlow.2
          · exact ne_of_gt hhigh) :=
  sandwichedRenyi_dataProcessing_channel_posDef_reference
    ρ (sandwichedRenyiReferenceRegularization σ ε) Φ hρ
    (sandwichedRenyiReferenceRegularization_posDef hσ hε) hρΦ hσΦε α hα_range

def sandwichedRenyiReferenceRegularizationLimitGate
    (regularizedIn regularizedOut : ℝ → ℝ) (DIn DOut : ℝ) : Prop :=
  Filter.Tendsto regularizedIn (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds DIn) ∧
    Filter.Tendsto regularizedOut (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds DOut)

theorem sandwichedRenyiReferenceRegularizationLimitGate.le_of_eventually_le
    {regularizedIn regularizedOut : ℝ → ℝ} {DIn DOut : ℝ}
    (hgate :
      sandwichedRenyiReferenceRegularizationLimitGate
        regularizedIn regularizedOut DIn DOut)
    (hle : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      regularizedOut ε ≤ regularizedIn ε) :
    DOut ≤ DIn :=
  le_of_tendsto_of_tendsto hgate.2 hgate.1 hle

def sandwichedRenyiReferenceRegularizedInputCurve
    (ρ : State a) {σ : CMatrix a} (hρ : ρ.matrix.PosDef) (hσ : σ.PosSemidef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then
    sandwichedRenyiReference ρ (sandwichedRenyiReferenceRegularization σ ε)
      hρ (sandwichedRenyiReferenceRegularization_posDef hσ hε)
      α hα_pos hα_ne_one
  else
    0

def sandwichedRenyiReferenceRegularizedOutputCurve
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (ε : ℝ) : ℝ :=
  by
    classical
    exact
      if hσΦε : (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef then
        sandwichedRenyiReference (Φ.applyState ρ)
          (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          hρΦ hσΦε α hα_pos hα_ne_one
      else
        0

theorem sandwichedRenyiReferenceRegularizedCurves_eventually_le
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α)
    (hσΦε :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiReferenceRegularizedOutputCurve ρ Φ hρΦ α
          (σ := σ)
          (by
            rcases hα_range with hlow | hhigh
            · linarith
            · linarith)
          (by
            rcases hα_range with hlow | hhigh
            · exact ne_of_lt hlow.2
            · exact ne_of_gt hhigh) ε ≤
        sandwichedRenyiReferenceRegularizedInputCurve ρ hρ hσ α
          (by
            rcases hα_range with hlow | hhigh
            · linarith
            · linarith)
          (by
            rcases hα_range with hlow | hhigh
            · exact ne_of_lt hlow.2
            · exact ne_of_gt hhigh) ε := by
  filter_upwards [self_mem_nhdsWithin, hσΦε] with ε hε_mem hσΦε_pos
  have hε_pos : 0 < ε := hε_mem
  simp [sandwichedRenyiReferenceRegularizedInputCurve,
    sandwichedRenyiReferenceRegularizedOutputCurve, hε_pos, hσΦε_pos]
  exact
    sandwichedRenyiReference_dataProcessing_channel_regularized
      ρ hσ Φ hρ hρΦ α hα_range hε_pos hσΦε_pos

theorem sandwichedRenyiReference_dataProcessing_channel_of_regularizationLimitGate
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α)
    (DIn DOut : ℝ)
    (hσΦε :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef)
    (hgate :
      sandwichedRenyiReferenceRegularizationLimitGate
        (sandwichedRenyiReferenceRegularizedInputCurve ρ hρ hσ α
          (by
            rcases hα_range with hlow | hhigh
            · linarith
            · linarith)
          (by
            rcases hα_range with hlow | hhigh
            · exact ne_of_lt hlow.2
            · exact ne_of_gt hhigh))
        (sandwichedRenyiReferenceRegularizedOutputCurve ρ Φ hρΦ α
          (σ := σ)
          (by
            rcases hα_range with hlow | hhigh
            · linarith
            · linarith)
          (by
            rcases hα_range with hlow | hhigh
            · exact ne_of_lt hlow.2
            · exact ne_of_gt hhigh))
        DIn DOut) :
    DOut ≤ DIn :=
  sandwichedRenyiReferenceRegularizationLimitGate.le_of_eventually_le hgate
    (sandwichedRenyiReferenceRegularizedCurves_eventually_le
      ρ hσ Φ hρ hρΦ α hα_range hσΦε)

theorem sandwichedRenyiPSDReferenceLowAlpha_regularizationLimitGate
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) :
    sandwichedRenyiReferenceRegularizationLimitGate
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve ρ hσ α)
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve ρ hσ Φ α)
      (sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α)
      (sandwichedRenyiPSDReferenceLowAlpha
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α) := by
  have hQ :=
    sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
      ρ hσ Φ α hα_half hα_lt_one
  have hQout_pos :
      0 < sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α :=
    lt_of_lt_of_le hQpos hQ
  exact
    ⟨sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve_tendsto
        ρ hσ α hα_half hα_lt_one hQpos,
      sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve_tendsto
        ρ hσ Φ α hα_half hα_lt_one hQout_pos⟩

theorem sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel_of_sourceRegularization
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) :
    sandwichedRenyiPSDReferenceLowAlpha
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α := by
  exact
    sandwichedRenyiReferenceRegularizationLimitGate.le_of_eventually_le
      (sandwichedRenyiPSDReferenceLowAlpha_regularizationLimitGate
        ρ hσ Φ α hα_half hα_lt_one hQpos)
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedCurves_eventually_le
        ρ hσ Φ α hα_half hα_lt_one)

def sandwichedRenyiPSDReferenceLowAlphaE
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : EReal :=
  if sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α = 0 then
    ⊤
  else
    (sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α : EReal)

@[simp]
theorem sandwichedRenyiPSDReferenceLowAlphaE_eq_top_of_Q_eq_zero
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    (hQzero : sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α = 0) :
    sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ α = ⊤ := by
  simp [sandwichedRenyiPSDReferenceLowAlphaE, hQzero]

@[simp]
theorem sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    (hQne : sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α ≠ 0) :
    sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ α =
      (sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α : EReal) := by
  simp [sandwichedRenyiPSDReferenceLowAlphaE, hQne]

theorem sandwichedRenyiQ_pos_of_ne_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ)
    (hQne : sandwichedRenyiQ ρ σ hρ hσ α ≠ 0) :
    0 < sandwichedRenyiQ ρ σ hρ hσ α := by
  have hQnonneg := sandwichedRenyiQ_nonneg hρ hσ α
  rcases lt_or_eq_of_le hQnonneg with hQpos | hQzero
  · exact hQpos
  · exact False.elim (hQne hQzero.symm)

def stateOfPSDReference [Nonempty a] (σ : CMatrix a) (hσ : σ.PosSemidef)
    (htr : 0 < σ.trace.re) : State a where
  matrix := (σ.trace.re)⁻¹ • σ
  pos := by
    exact Matrix.PosSemidef.smul hσ (inv_nonneg.mpr (le_of_lt htr))
  trace_eq_one := by
    have htr_im : σ.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hσ).2.symm
    rw [Matrix.trace_smul]
    apply Complex.ext
    · simp [Complex.real_smul, ne_of_gt htr]
    · simp [Complex.real_smul, htr_im]

@[simp]
theorem stateOfPSDReference_matrix [Nonempty a] (σ : CMatrix a)
    (hσ : σ.PosSemidef) (htr : 0 < σ.trace.re) :
    (stateOfPSDReference σ hσ htr).matrix = (σ.trace.re)⁻¹ • σ :=
  rfl

theorem sandwichedRenyiQ_real_smul_reference_half
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    sandwichedRenyiQ ρ.matrix (lambda • σ : CMatrix a)
        ρ.pos (Matrix.PosSemidef.smul hσ (le_of_lt hlambda)) (1 / 2 : ℝ) =
      lambda ^ (1 / 2 : ℝ) *
        sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) := by
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
  have hscale :=
    sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
      ρ hσ hlambda_nonneg (1 / 2 : ℝ)
  have hfactor :
      ((lambda ^ ((1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ))) *
          lambda ^ ((1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)))) ^
          (1 / 2 : ℝ)) =
        lambda ^ (1 / 2 : ℝ) := by
    have hs : (1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    have hmul : lambda ^ (1 / 2 : ℝ) * lambda ^ (1 / 2 : ℝ) = lambda := by
      calc
        lambda ^ (1 / 2 : ℝ) * lambda ^ (1 / 2 : ℝ) =
            lambda ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
              rw [Real.rpow_add hlambda]
        _ = lambda := by norm_num
    rw [hs, hmul]
  have hfactor' :
      ((lambda ^ (1 - (1 / 2 : ℝ)) *
          lambda ^ (1 - (1 / 2 : ℝ))) ^
          (1 / 2 : ℝ)) =
        lambda ^ (1 / 2 : ℝ) := by
    have hone_sub : 1 - (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
      norm_num
    have hmul : lambda ^ (1 / 2 : ℝ) * lambda ^ (1 / 2 : ℝ) = lambda := by
      calc
        lambda ^ (1 / 2 : ℝ) * lambda ^ (1 / 2 : ℝ) =
            lambda ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
              rw [Real.rpow_add hlambda]
        _ = lambda := by norm_num
    rw [hone_sub, hmul]
  have hfactor_two :
      ((lambda ^ (1 - (2 : ℝ)⁻¹) *
          lambda ^ (1 - (2 : ℝ)⁻¹)) ^
          ((2 : ℝ)⁻¹)) =
        lambda ^ ((2 : ℝ)⁻¹) := by
    have hone_sub : 1 - (2 : ℝ)⁻¹ = ((2 : ℝ)⁻¹) := by
      norm_num
    have hmul : lambda ^ ((2 : ℝ)⁻¹) * lambda ^ ((2 : ℝ)⁻¹) = lambda := by
      calc
        lambda ^ ((2 : ℝ)⁻¹) * lambda ^ ((2 : ℝ)⁻¹) =
            lambda ^ (((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) := by
              rw [Real.rpow_add hlambda]
        _ = lambda := by norm_num
    rw [hone_sub, hmul]
  rw [sandwichedRenyiQ_eq_psdTracePower_referenceInner,
    sandwichedRenyiQ_eq_psdTracePower_referenceInner]
  exact hscale.trans (by
    dsimp
    rw [hfactor])

theorem sandwichedRenyiQ_zero_right_half (ρ : State a) :
    sandwichedRenyiQ ρ.matrix (0 : CMatrix a) ρ.pos Matrix.PosSemidef.zero
      (1 / 2 : ℝ) = 0 := by
  have hs : (1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
    norm_num
  have hzero :
      CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ) = 0 := by
    simpa using
      (CFC.zero_rpow (A := CMatrix a) (x := (1 / 2 : ℝ)) (by norm_num))
  have hzero_two :
      CFC.rpow (0 : CMatrix a) ((2 : ℝ)⁻¹) = 0 := by
    simpa using
      (CFC.zero_rpow (A := CMatrix a) (x := ((2 : ℝ)⁻¹)) (by norm_num))
  have hzero_sub :
      CFC.rpow (0 : CMatrix a) (1 - (2 : ℝ)⁻¹) = 0 := by
    simpa using
      (CFC.zero_rpow (A := CMatrix a) (x := (1 - (2 : ℝ)⁻¹)) (by norm_num))
  unfold sandwichedRenyiQ
  dsimp
  rw [hs]
  change
    (CFC.rpow
      (CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ) * ρ.matrix *
        CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ))
      (1 / 2 : ℝ)).trace.re = 0
  have hinner_zero :
      CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ) * ρ.matrix *
          CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ) = 0 := by
    rw [hzero]
    simp
  rw [hinner_zero, hzero]
  simp

theorem sandwichedRenyiQ_dataProcessing_channel_reference_half_of_trace_pos
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (htr : 0 < σ.trace.re) :
    sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) ≤
      sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) := by
  classical
  letI : Nonempty a := ρ.nonempty
  let lambda : ℝ := (σ.trace.re)⁻¹
  have hlambda_pos : 0 < lambda := inv_pos.mpr htr
  let σ₀ : State a := stateOfPSDReference σ hσ htr
  have hmap :
      (Φ.applyState σ₀).matrix = lambda • Φ.map σ := by
    change Φ.map (lambda • σ : CMatrix a) = lambda • Φ.map σ
    change Φ.map (((lambda : ℝ) : ℂ) • σ) =
      (((lambda : ℝ) : ℂ) • Φ.map σ)
    simp [lambda]
  have hin_scale :
      sandwichedRenyiQ ρ.matrix σ₀.matrix ρ.pos σ₀.pos (1 / 2 : ℝ) =
        lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) := by
    simpa [σ₀, lambda, stateOfPSDReference] using
      sandwichedRenyiQ_real_smul_reference_half ρ hσ hlambda_pos
  have hout_scale :
      sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ₀).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ₀).pos (1 / 2 : ℝ) =
        lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) := by
    simpa [hmap, sandwichedRenyiQ] using
      sandwichedRenyiQ_real_smul_reference_half
        (Φ.applyState ρ) (Φ.mapsPositive σ hσ) hlambda_pos
  have hfid_sq := State.squaredFidelity_le_applyState_squaredFidelity Φ ρ σ₀
  have hfid :
      ρ.fidelity σ₀ ≤ (Φ.applyState ρ).fidelity (Φ.applyState σ₀) := by
    rw [State.squaredFidelity_eq_fidelity_sq,
      State.squaredFidelity_eq_fidelity_sq] at hfid_sq
    exact (sq_le_sq₀ (State.fidelity_nonneg ρ σ₀)
      (State.fidelity_nonneg (Φ.applyState ρ) (Φ.applyState σ₀))).mp hfid_sq
  have hQ_state :
      sandwichedRenyiQ ρ.matrix σ₀.matrix ρ.pos σ₀.pos (1 / 2 : ℝ) ≤
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ₀).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ₀).pos (1 / 2 : ℝ) := by
    rw [sandwichedRenyiQ_eq_psdTracePower_inner,
      sandwichedRenyiInner_psdTracePower_half_eq_fidelity,
      sandwichedRenyiQ_eq_psdTracePower_inner,
      sandwichedRenyiInner_psdTracePower_half_eq_fidelity]
    exact hfid
  have hscaled :
      lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) ≤
        lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) := by
    calc
      lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) =
          sandwichedRenyiQ ρ.matrix σ₀.matrix ρ.pos σ₀.pos (1 / 2 : ℝ) := hin_scale.symm
      _ ≤ sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ₀).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ₀).pos (1 / 2 : ℝ) := hQ_state
      _ = lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) := hout_scale
  exact le_of_mul_le_mul_left hscaled
    (Real.rpow_pos_of_pos hlambda_pos (1 / 2 : ℝ))

theorem sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel_half
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (htr : 0 < σ.trace.re)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ)) :
    sandwichedRenyiPSDReferenceLowAlpha
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) ≤
      sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ (1 / 2 : ℝ) := by
  have hQmono :=
    sandwichedRenyiQ_dataProcessing_channel_reference_half_of_trace_pos
      ρ hσ Φ htr
  unfold sandwichedRenyiPSDReferenceLowAlpha
  have hlog := frankLieb_log2_mono_of_pos hQpos hQmono
  have hcoef : 1 / ((1 / 2 : ℝ) - 1) = -2 := by norm_num
  rw [hcoef]
  exact mul_le_mul_of_nonpos_left hlog (by norm_num)

theorem sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel_half
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b) :
    sandwichedRenyiPSDReferenceLowAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) ≤
      sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ (1 / 2 : ℝ) := by
  by_cases hQin_zero :
      sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) = 0
  · rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_top_of_Q_eq_zero
      ρ hσ (1 / 2 : ℝ) hQin_zero]
    exact le_top
  · have hQin_pos :
        0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) :=
      sandwichedRenyiQ_pos_of_ne_zero ρ.pos hσ (1 / 2 : ℝ) hQin_zero
    have hσ_ne_zero : σ ≠ 0 := by
      intro hσzero
      exact hQin_zero (by
        simpa [hσzero] using sandwichedRenyiQ_zero_right_half ρ)
    have htr_ne : σ.trace.re ≠ 0 := by
      intro htr_zero
      have htrace_zero : σ.trace = 0 := by
        apply Complex.ext
        · simpa using htr_zero
        · simp [(Matrix.PosSemidef.trace_nonneg hσ).2.symm]
      exact hσ_ne_zero ((Matrix.PosSemidef.trace_eq_zero_iff hσ).mp htrace_zero)
    have htr_pos : 0 < σ.trace.re := by
      exact lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hσ).1 (Ne.symm htr_ne)
    have hQmono :
        sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) ≤
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) :=
      sandwichedRenyiQ_dataProcessing_channel_reference_half_of_trace_pos
        ρ hσ Φ htr_pos
    have hQout_pos :
        0 < sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) :=
      lt_of_lt_of_le hQin_pos hQmono
    have hQout_ne :
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) ≠ 0 :=
      ne_of_gt hQout_pos
    have hDPI :
        sandwichedRenyiPSDReferenceLowAlpha
            (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) ≤
          sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ (1 / 2 : ℝ) :=
      sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel_half
        ρ hσ Φ htr_pos hQin_pos
    rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
        (Φ.applyState ρ) (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) hQout_ne,
      sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
        ρ hσ (1 / 2 : ℝ) hQin_zero]
    exact_mod_cast hDPI

theorem sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiPSDReferenceLowAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ α := by
  by_cases hQin_zero : sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α = 0
  · simp [sandwichedRenyiPSDReferenceLowAlphaE, hQin_zero]
  · have hQin_pos :
        0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α :=
      sandwichedRenyiQ_pos_of_ne_zero ρ.pos hσ α hQin_zero
    have hQmono :
        sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α ≤
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α :=
      sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
        ρ hσ Φ α hα_half hα_lt_one
    have hQout_pos :
        0 < sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α :=
      lt_of_lt_of_le hQin_pos hQmono
    have hQout_ne :
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α ≠ 0 :=
      ne_of_gt hQout_pos
    have hDPI :
        sandwichedRenyiPSDReferenceLowAlpha
            (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
          sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α :=
      sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel_of_sourceRegularization
        ρ hσ Φ α hα_half hα_lt_one hQin_pos
    simp [sandwichedRenyiPSDReferenceLowAlphaE, hQin_zero, hQout_ne,
      EReal.coe_le_coe_iff, hDPI]

theorem sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_reference_posDef
    (ρ : State a) {σ : CMatrix a}
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ.posSemidef α =
      (sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one : EReal) := by
  have hQpos := sandwichedRenyiQ_pos_of_state_posDef_reference ρ hσ α
  have hQne :
      sandwichedRenyiQ ρ.matrix σ ρ.pos hσ.posSemidef α ≠ 0 :=
    ne_of_gt hQpos
  rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
    ρ hσ.posSemidef α hQne]
  simp [sandwichedRenyiPSDReferenceLowAlpha_eq_reference_posDef
    ρ hρ hσ α hα_pos hα_ne_one]

def sandwichedRenyiPSDReferenceHighAlphaFinite
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : ℝ :=
  (1 / (α - 1)) *
    log2 (psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
      (sandwichedRenyiReferenceInner_posSemidef ρ hσ α) α)

theorem sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosDef)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ
        (lambda • σ : CMatrix a)
        (Matrix.PosDef.smul hσ hlambda).posSemidef α =
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α -
        log2 lambda := by
  let s : ℝ := (1 - α) / (2 * α)
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hα_ne_one : α ≠ 1 := ne_of_gt hα
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
  have htrace_scale :
      psdTracePower
          (sandwichedRenyiReferenceInner ρ (lambda • σ : CMatrix a) α)
          (sandwichedRenyiReferenceInner_posSemidef ρ
            (Matrix.PosDef.smul hσ hlambda).posSemidef α)
          α =
        ((lambda ^ s * lambda ^ s) ^ α) *
          psdTracePower
            (sandwichedRenyiReferenceInner ρ σ α)
            (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)
            α := by
    simpa [s] using
      sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
        ρ hσ.posSemidef hlambda_nonneg α
  have hfactor :
      (lambda ^ s * lambda ^ s) ^ α = lambda ^ (1 - α) := by
    have hmul : lambda ^ s * lambda ^ s = lambda ^ (s + s) := by
      rw [Real.rpow_add hlambda]
    calc
      (lambda ^ s * lambda ^ s) ^ α = (lambda ^ (s + s)) ^ α := by
        rw [hmul]
      _ = lambda ^ ((s + s) * α) := by
        rw [← Real.rpow_mul hlambda_nonneg]
      _ = lambda ^ (1 - α) := by
        congr 1
        dsimp [s]
        field_simp [ne_of_gt hα_pos]
        ring_nf
  have hfactor_pos : 0 < lambda ^ (1 - α) :=
    Real.rpow_pos_of_pos hlambda _
  have hTpos :
      0 <
        psdTracePower
          (sandwichedRenyiReferenceInner ρ σ α)
          (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)
          α :=
    sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
      ρ hσ α
  have hlog_factor : log2 (lambda ^ (1 - α)) = (1 - α) * log2 lambda := by
    unfold log2
    rw [Real.log_rpow hlambda]
    ring
  have hcoef :
      (1 / (α - 1)) * ((1 - α) * log2 lambda) = -log2 lambda := by
    field_simp [hα_ne_one]
    ring
  simp only [sandwichedRenyiPSDReferenceHighAlphaFinite]
  rw [htrace_scale, hfactor]
  rw [log2_mul (ne_of_gt hfactor_pos) (ne_of_gt hTpos), hlog_factor]
  rw [mul_add, hcoef]
  ring

theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_stateReference_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : State a) (Φ : Channel a b)
    (hσ : σ.matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.applyState σ).matrix (Φ.applyState σ).pos α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ.matrix σ.pos α := by
  have hpower :=
    sandwichedRenyiInner_tracePower_le_of_one_lt_channel
      ρ σ Φ hσ hσΦ α hα
  have hout_pos :
      0 <
        psdTracePower
          (sandwichedRenyiReferenceInner
            (Φ.applyState ρ) (Φ.applyState σ).matrix α)
          (sandwichedRenyiReferenceInner_posSemidef
            (Φ.applyState ρ) (Φ.applyState σ).pos α)
          α := by
    simpa [sandwichedRenyiInner, sandwichedRenyiReferenceInner] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
        (Φ.applyState ρ) (σ := (Φ.applyState σ).matrix) hσΦ α
  have hlog :
      log2
          (psdTracePower
            (sandwichedRenyiReferenceInner
              (Φ.applyState ρ) (Φ.applyState σ).matrix α)
            (sandwichedRenyiReferenceInner_posSemidef
              (Φ.applyState ρ) (Φ.applyState σ).pos α)
            α) ≤
        log2
          (psdTracePower (sandwichedRenyiReferenceInner ρ σ.matrix α)
            (sandwichedRenyiReferenceInner_posSemidef ρ σ.pos α) α) := by
    exact frankLieb_log2_mono_of_pos hout_pos (by
      simpa [sandwichedRenyiInner, sandwichedRenyiReferenceInner] using hpower)
  have hcoef_nonneg : 0 ≤ 1 / (α - 1) := by
    exact le_of_lt (one_div_pos.2 (sub_pos.mpr hα))
  simpa [sandwichedRenyiPSDReferenceHighAlphaFinite] using
    mul_le_mul_of_nonneg_left hlog hcoef_nonneg

theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_posDef_reference
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hσ : σ.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α := by
  classical
  let lambda : ℝ := (σ.trace.re)⁻¹
  have htr_pos : 0 < σ.trace.re :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hσ)).1
  have hlambda_pos : 0 < lambda := by
    exact inv_pos.mpr htr_pos
  let σ₀ : State a := stateOfPosDefReference σ hσ
  have hσ₀ : σ₀.matrix.PosDef := by
    simpa [σ₀] using stateOfPosDefReference_posDef σ hσ
  have hmap :
      (Φ.applyState σ₀).matrix = lambda • Φ.map σ := by
    change Φ.map (lambda • σ : CMatrix a) = lambda • Φ.map σ
    change Φ.map (((lambda : ℝ) : ℂ) • σ) =
      (((lambda : ℝ) : ℂ) • Φ.map σ)
    simp [lambda]
  have hσ₀Φ : (Φ.applyState σ₀).matrix.PosDef := by
    rw [hmap]
    exact Matrix.PosDef.smul hσΦ hlambda_pos
  have hDPI :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_stateReference_posDef
      ρ σ₀ Φ hσ₀ hσ₀Φ α hα
  have hin :
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ₀.matrix σ₀.pos α =
        sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α -
          log2 lambda := by
    simpa [σ₀, lambda, stateOfPosDefReference] using
      sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference
        ρ hσ hlambda_pos α hα
  have hout :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.applyState σ₀).matrix
          (Φ.applyState σ₀).pos α =
        sandwichedRenyiPSDReferenceHighAlphaFinite
            (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α -
          log2 lambda := by
    simpa [hmap, lambda] using
      sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference
        (Φ.applyState ρ) hσΦ hlambda_pos α hα
  have hshift :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α - log2 lambda ≤
        sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α -
          log2 lambda := by
    simpa [hin, hout] using hDPI
  linarith

def sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ
      (sandwichedRenyiReferenceRegularization σ ε)
      (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α
  else
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α

theorem sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve_tendsto_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (hα : 1 < α) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve ρ hσ α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have htrace :=
    sandwichedRenyiReferenceInner_tracePower_regularization_tendsto_of_supports
      ρ hσ hSupport α hα_pos
  have htarget_pos :
      0 <
        ((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re := by
    simpa [psdTracePower] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
        ρ hσ hSupport α
  have hlog :
      Filter.Tendsto
        (fun ε : ℝ =>
          log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner ρ
                (sandwichedRenyiReferenceRegularization σ ε) α) α).trace).re))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (log2 (((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re))) := by
    have hrawLog := Filter.Tendsto.log htrace (ne_of_gt htarget_pos)
    simpa [log2] using
      hrawLog.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  have hraw :
      Filter.Tendsto
        (fun ε : ℝ =>
          (1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner ρ
                  (sandwichedRenyiReferenceRegularization σ ε) α) α).trace).re))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          ((1 / (α - 1)) *
            log2
              (((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re))) :=
    tendsto_const_nhds.mul hlog
  have hcurve :
      (fun ε : ℝ =>
          (1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner ρ
                  (sandwichedRenyiReferenceRegularization σ ε) α) α).trace).re))
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve ρ hσ α := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_pos : 0 < ε := hε
    simp [sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve,
      sandwichedRenyiPSDReferenceHighAlphaFinite, psdTracePower, hε_pos]
  exact Filter.Tendsto.congr' hcurve hraw

theorem sandwichedRenyiReferenceInner_tracePower_tendsto_of_tendsto_posDef_reference
    {X : Type*} {l : Filter X} (ρ : State a)
    {σF : X → CMatrix a} {σ : CMatrix a}
    (hσF : Filter.Tendsto σF l (nhds σ))
    (hσFpd : ∀ᶠ x in l, (σF x).PosDef)
    (hσ : σ.PosDef)
    (α : ℝ) (hα_pos : 0 < α) :
    Filter.Tendsto
      (fun x : X =>
        (((CFC.rpow (sandwichedRenyiReferenceInner ρ (σF x) α) α).trace).re))
      l
      (nhds
        (((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re)) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hpow :
      Filter.Tendsto (fun x : X => CFC.rpow (σF x) s) l
        (nhds (CFC.rpow σ s)) :=
    _root_.QITBench.cMatrix_rpow_tendsto_of_tendsto_posDef s hσF hσFpd hσ
  have hinner :
      Filter.Tendsto (fun x : X => sandwichedRenyiReferenceInner ρ (σF x) α)
        l (nhds (sandwichedRenyiReferenceInner ρ σ α)) := by
    unfold sandwichedRenyiReferenceInner
    exact (hpow.mul tendsto_const_nhds).mul hpow
  have hinner_psd :
      ∀ᶠ x in l, (sandwichedRenyiReferenceInner ρ (σF x) α).PosSemidef := by
    exact hσFpd.mono fun x hx =>
      sandwichedRenyiReferenceInner_posSemidef ρ hx.posSemidef α
  exact
    cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
      hα_pos hinner hinner_psd
      (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)

def sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ) (ε : ℝ) : ℝ := by
  classical
  exact
    if hσΦε : (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef then
      sandwichedRenyiPSDReferenceHighAlphaFinite (Φ.applyState ρ)
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
        hσΦε.posSemidef α
    else
      sandwichedRenyiPSDReferenceHighAlphaFinite (Φ.applyState ρ)
        (Φ.map σ) (Φ.mapsPositive σ hσ) α

theorem Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (_hσ : σ.PosSemidef)
    (hσΦ : (Φ.map σ).PosDef) {ε : ℝ} (hε : 0 ≤ ε) :
    (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef := by
  rw [Channel.map_sandwichedRenyiReferenceRegularization]
  exact hσΦ.add_posSemidef
      (Matrix.PosSemidef.smul
        (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one) hε)

theorem sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve_tendsto_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
        ρ hσ Φ α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let σF : ℝ → CMatrix b := fun ε =>
    if hε : 0 ≤ ε then
      Φ.map (sandwichedRenyiReferenceRegularization σ ε)
    else
      Φ.map σ
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hσF_pd : ∀ ε, (σF ε).PosDef := by
    intro ε
    by_cases hε : 0 ≤ ε
    · simpa [σF, hε] using
        Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
          Φ hσ hσΦ hε
    · simpa [σF, hε] using hσΦ
  have hσF_tend : Filter.Tendsto σF l (nhds (Φ.map σ)) := by
    have hreg := sandwichedRenyiReferenceRegularization_tendsto (a := a) σ
    have hmap :
        Filter.Tendsto
          (fun ε : ℝ => Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          l (nhds (Φ.map σ)) :=
      (LinearMap.continuous_of_finiteDimensional Φ.map).tendsto σ |>.comp hreg
    have hcongr :
        (fun ε : ℝ => Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          =ᶠ[l] σF := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nonneg : 0 ≤ ε := le_of_lt hε
      simp [σF, hε_nonneg]
    exact Filter.Tendsto.congr' hcongr hmap
  have htrace :=
    sandwichedRenyiReferenceInner_tracePower_tendsto_of_tendsto_posDef_reference
      (Φ.applyState ρ) hσF_tend
      (Filter.Eventually.of_forall (fun ε => hσF_pd ε)) hσΦ α hα_pos
  have htarget_pos :
      0 <
        (((CFC.rpow
          (sandwichedRenyiReferenceInner (Φ.applyState ρ) (Φ.map σ) α)
          α).trace).re) := by
    simpa [psdTracePower] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
        (Φ.applyState ρ) hσΦ α
  have hlog :
      Filter.Tendsto
        (fun ε : ℝ =>
          log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner (Φ.applyState ρ) (σF ε) α)
              α).trace).re))
        l
        (nhds
          (log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner (Φ.applyState ρ) (Φ.map σ) α)
              α).trace).re))) := by
    have hrawLog := Filter.Tendsto.log htrace (ne_of_gt htarget_pos)
    simpa [log2] using
      hrawLog.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  have hraw :
      Filter.Tendsto
        (fun ε : ℝ =>
          (1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner (Φ.applyState ρ) (σF ε) α)
                α).trace).re))
        l
        (nhds
          ((1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner (Φ.applyState ρ) (Φ.map σ) α)
                α).trace).re))) :=
    hlog.const_mul (1 / (α - 1))
  have hcurve :
      (fun ε : ℝ =>
          (1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner (Φ.applyState ρ) (σF ε) α)
                α).trace).re))
        =ᶠ[l]
      sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
        ρ hσ Φ α := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_pos : 0 < ε := hε
    have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
    have hσFε_pos :
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef :=
      Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
        Φ hσ hσΦ hε_nonneg
    simp [sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve,
      sandwichedRenyiPSDReferenceHighAlphaFinite, psdTracePower, σF,
      hε_nonneg, hσFε_pos]
  exact Filter.Tendsto.congr' hcurve hraw

theorem sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedCurves_eventually_le
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα : 1 < α)
    (hσΦε :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
          ρ hσ Φ α ε ≤
        sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
          ρ hσ α ε := by
  filter_upwards [self_mem_nhdsWithin, hσΦε] with ε hε_mem hσΦε_pos
  have hε_pos : 0 < ε := hε_mem
  simp [sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve,
    sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve,
    hε_pos, hσΦε_pos]
  exact
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_posDef_reference
      ρ Φ (sandwichedRenyiReferenceRegularization_posDef hσ hε_pos)
      hσΦε_pos α hα

theorem sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedCurves_eventually_le_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
          ρ hσ Φ α ε ≤
        sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
          ρ hσ α ε := by
  refine
    sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedCurves_eventually_le
      ρ hσ Φ α hα ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact
    Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
      Φ hσ hσΦ (le_of_lt hε)

theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_of_regularizationLimitGate
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα : 1 < α)
    (DIn DOut : ℝ)
    (hσΦε :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef)
    (hgate :
      sandwichedRenyiReferenceRegularizationLimitGate
        (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
          ρ hσ α)
        (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
          ρ hσ Φ α)
        DIn DOut) :
    DOut ≤ DIn :=
  sandwichedRenyiReferenceRegularizationLimitGate.le_of_eventually_le hgate
    (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedCurves_eventually_le
      ρ hσ Φ α hα hσΦε)

theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α := by
  refine
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_of_regularizationLimitGate
      ρ hσ Φ α hα
      (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α)
      (sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α)
      ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact
      Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
        Φ hσ hσΦ (le_of_lt hε)
  · exact
      ⟨sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve_tendsto_of_supports
          ρ hσ hSupport α hα,
        sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve_tendsto_of_map_posDef
          ρ hσ Φ hσΦ α hα⟩

noncomputable def sandwichedRenyiPSDReferenceHighAlphaE
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : EReal :=
  by
    classical
    exact
      if Matrix.Supports ρ.matrix σ then
        (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α : EReal)
      else
        ⊤

@[simp]
theorem sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    (hSupport : ¬ Matrix.Supports ρ.matrix σ) :
    sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α = ⊤ := by
  simp [sandwichedRenyiPSDReferenceHighAlphaE, hSupport]

@[simp]
theorem sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α =
      (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α : EReal) := by
  simp [sandwichedRenyiPSDReferenceHighAlphaE, hSupport]

theorem sandwichedRenyiPSDReferenceHighAlphaE_regularized_input_eq_coe
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiPSDReferenceHighAlphaE ρ
        (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α =
      (sandwichedRenyiPSDReferenceHighAlphaFinite ρ
        (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α :
        EReal) := by
  have hSupport :
      Matrix.Supports ρ.matrix
        (sandwichedRenyiReferenceRegularization σ ε) :=
    Matrix.Supports.of_right_posDef ρ.matrix
      (sandwichedRenyiReferenceRegularization σ ε)
      (sandwichedRenyiReferenceRegularization_posDef hσ hε)
  exact
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      ρ
      (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α
      hSupport

theorem sandwichedRenyiPSDReferenceHighAlphaE_regularized_output_eq_coe
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiPSDReferenceHighAlphaE (Φ.applyState ρ)
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
        (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
          (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef) α =
      (sandwichedRenyiPSDReferenceHighAlphaFinite (Φ.applyState ρ)
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
        (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
          (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef) α :
        EReal) := by
  have hSupport :
      Matrix.Supports (Φ.applyState ρ).matrix
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) :=
    Channel.applyState_supports_map_regularized_reference Φ ρ hσ hε
  exact
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (Φ.applyState ρ)
      (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef) α
      hSupport

noncomputable def sandwichedRenyiPSDReferenceHighAlphaERegularizedInputCurve
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (ε : ℝ) : EReal :=
  by
    classical
    exact
      if hε : 0 < ε then
        sandwichedRenyiPSDReferenceHighAlphaE ρ
          (sandwichedRenyiReferenceRegularization σ ε)
          (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α
      else
        sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α

noncomputable def sandwichedRenyiPSDReferenceHighAlphaERegularizedOutputCurve
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ) (ε : ℝ) : EReal :=
  by
    classical
    exact
      if hε : 0 < ε then
        sandwichedRenyiPSDReferenceHighAlphaE (Φ.applyState ρ)
          (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
            (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef) α
      else
        sandwichedRenyiPSDReferenceHighAlphaE (Φ.applyState ρ)
          (Φ.map σ) (Φ.mapsPositive σ hσ) α

theorem sandwichedRenyiPSDReferenceHighAlphaERegularizedCurves_eventually_le_of_finite
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ)
    (hfinite :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ hε : 0 < ε,
          sandwichedRenyiPSDReferenceHighAlphaFinite (Φ.applyState ρ)
              (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
              (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
                (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef)
              α ≤
            sandwichedRenyiPSDReferenceHighAlphaFinite ρ
              (sandwichedRenyiReferenceRegularization σ ε)
              (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef
              α) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiPSDReferenceHighAlphaERegularizedOutputCurve
          ρ hσ Φ α ε ≤
        sandwichedRenyiPSDReferenceHighAlphaERegularizedInputCurve
          ρ hσ α ε := by
  filter_upwards [self_mem_nhdsWithin, hfinite] with ε hε_mem hle
  have hε : 0 < ε := hε_mem
  simp [sandwichedRenyiPSDReferenceHighAlphaERegularizedOutputCurve,
    sandwichedRenyiPSDReferenceHighAlphaERegularizedInputCurve, hε]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_regularized_output_eq_coe
      ρ hσ Φ α hε,
    sandwichedRenyiPSDReferenceHighAlphaE_regularized_input_eq_coe
      ρ hσ α hε]
  exact_mod_cast hle hε

theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_posDef_reference_finite
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hσ : σ.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ.posSemidef α := by
  have hSupport : Matrix.Supports ρ.matrix σ :=
    Matrix.Supports.of_right_posDef ρ.matrix σ hσ
  have hSupportOut :
      Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) :=
    Matrix.Supports.of_right_posDef (Φ.applyState ρ).matrix (Φ.map σ) hσΦ
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (Φ.applyState ρ) hσΦ.posSemidef α hSupportOut,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      ρ hσ.posSemidef α hSupport]
  exact_mod_cast
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_posDef_reference
      ρ Φ hσ hσΦ α hα

theorem sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
    (ρ : State a) {σ : CMatrix a}
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ.posSemidef α =
      (sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one : EReal) := by
  have hSupport : Matrix.Supports ρ.matrix σ :=
    Matrix.Supports.of_right_posDef ρ.matrix σ hσ
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    ρ hσ.posSemidef α hSupport]
  simp [sandwichedRenyiPSDReferenceHighAlphaFinite,
    sandwichedRenyiReference_eq_log2_psdTracePower_inner
      ρ hρ hσ α hα_pos hα_ne_one]

theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_not_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hSupport : ¬ Matrix.Supports ρ.matrix σ) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  simp [sandwichedRenyiPSDReferenceHighAlphaE, hSupport]

theorem sandwichedRenyiPSDReferenceHighAlphaE_output_supports_of_input_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) :=
  channel_applyState_supports_of_supports ρ hσ Φ hSupport

theorem sandwichedRenyiPSDReferenceHighAlphaE_output_supportProjector_fixes_of_input_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    let Pi : CMatrix b :=
      psdInvSqrt (Φ.map σ) (Φ.mapsPositive σ hσ).isHermitian *
        (Φ.map σ) *
        psdInvSqrt (Φ.map σ) (Φ.mapsPositive σ hσ).isHermitian
    Pi * (Φ.applyState ρ).matrix = (Φ.applyState ρ).matrix ∧
      (Φ.applyState ρ).matrix * Pi = (Φ.applyState ρ).matrix := by
  exact
    _root_.QITBench.supportProjector_fixes_of_supports
      (M := (Φ.applyState ρ).matrix) (N := Φ.map σ)
      (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ)
      (sandwichedRenyiPSDReferenceHighAlphaE_output_supports_of_input_supports
        ρ hσ Φ hSupport)

theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_posDef_reference
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ.posSemidef α := by
  have hα_pos : 0 < α := by linarith
  have hα_ne_one : α ≠ 1 := ne_of_gt hα
  have hDPI :
      sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ)
          hρΦ hσΦ α hα_pos hα_ne_one ≤
        sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one :=
    sandwichedRenyi_dataProcessing_channel_posDef_reference
      ρ σ Φ hρ hσ hρΦ hσΦ α (Or.inr hα)
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
      (Φ.applyState ρ) hρΦ hσΦ α hα_pos hα_ne_one,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
      ρ hρ hσ α hα_pos hα_ne_one]
  exact_mod_cast hDPI

theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_supported_finite_le
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hSupport : Matrix.Supports ρ.matrix σ)
    (hfinite :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
        sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  have hSupportOut :
      Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) :=
    sandwichedRenyiPSDReferenceHighAlphaE_output_supports_of_input_supports
      ρ hσ Φ hSupport
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (Φ.applyState ρ) (Φ.mapsPositive σ hσ) α hSupportOut,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      ρ hσ α hSupport]
  exact_mod_cast hfinite

theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_finite_branch
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ)
    (hfinite :
      Matrix.Supports ρ.matrix σ →
        sandwichedRenyiPSDReferenceHighAlphaFinite
            (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
          sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  by_cases hSupport : Matrix.Supports ρ.matrix σ
  · exact
      sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_supported_finite_le
        ρ hσ Φ α hSupport (hfinite hSupport)
  · exact
      sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_not_supports
        ρ hσ Φ α hSupport

theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  refine
    sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_finite_branch
      ρ hσ Φ α ?_
  intro hSupport
  have hfinite :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_of_map_posDef
      ρ hσ Φ hSupport hσΦ α hα
  simpa using hfinite

noncomputable def psdSupportCompressedState
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    State (psdSupportIndex σ hσ) :=
  _root_.QITBench.psdSupportCompressedState ρ hσ hSupport

@[simp]
theorem psdSupportCompressedState_matrix
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    (psdSupportCompressedState ρ hσ hSupport).matrix =
      psdSupportCompress σ hσ ρ.matrix := rfl

theorem psdSupportCompressedState_reference_posDef
    {σ : CMatrix a} (hσ : σ.PosSemidef) :
    (psdSupportCompress σ hσ σ).PosDef :=
  _root_.QITBench.psdSupportCompressedState_reference_posDef hσ

theorem psdSupportCompressedState_support_nonempty
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    Nonempty (psdSupportIndex σ hσ) :=
  _root_.QITBench.psdSupportCompressedState_support_nonempty ρ hσ hSupport

noncomputable def psdSupportEmbeddingMap
    (σ : CMatrix a) (hσ : σ.PosSemidef) :
    MatrixMap (psdSupportIndex σ hσ) a :=
  MatrixMap.ofKraus (fun (_ : Unit) => psdSupportIsometry σ hσ)

@[simp]
theorem psdSupportEmbeddingMap_apply
    (σ : CMatrix a) (hσ : σ.PosSemidef)
    (X : CMatrix (psdSupportIndex σ hσ)) :
    psdSupportEmbeddingMap σ hσ X =
      psdSupportIsometry σ hσ * X *
        Matrix.conjTranspose (psdSupportIsometry σ hσ) := by
  simp [psdSupportEmbeddingMap, MatrixMap.ofKraus]

noncomputable def psdSupportCompressionMap
    (σ : CMatrix a) (hσ : σ.PosSemidef) :
    MatrixMap a (psdSupportIndex σ hσ) :=
  MatrixMap.ofKraus
    (fun (_ : Unit) => Matrix.conjTranspose (psdSupportIsometry σ hσ))

@[simp]
theorem psdSupportCompressionMap_apply
    (σ : CMatrix a) (hσ : σ.PosSemidef) (X : CMatrix a) :
    psdSupportCompressionMap σ hσ X =
      psdSupportCompress σ hσ X := by
  simp [psdSupportCompressionMap, psdSupportCompress, MatrixMap.ofKraus]

noncomputable def psdSupportRestrictedChannel
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (σ : CMatrix a) (hσ : σ.PosSemidef) :
    Channel (psdSupportIndex σ hσ)
      (psdSupportIndex (Φ.map σ) (Φ.mapsPositive σ hσ)) where
  map :=
    (psdSupportCompressionMap (Φ.map σ) (Φ.mapsPositive σ hσ)).comp
      (Φ.map.comp (psdSupportEmbeddingMap σ hσ))
  completelyPositive := by
    refine MatrixMap.isCompletelyPositive_comp
      (psdSupportCompressionMap (Φ.map σ) (Φ.mapsPositive σ hσ))
      (Φ.map.comp (psdSupportEmbeddingMap σ hσ)) ?_ ?_
    · exact MatrixMap.ofKraus_completelyPositive _
    · exact MatrixMap.isCompletelyPositive_comp Φ.map
        (psdSupportEmbeddingMap σ hσ)
        Φ.completelyPositive (MatrixMap.ofKraus_completelyPositive _)
  tracePreserving := by
    intro X
    let τ : CMatrix b := Φ.map σ
    let hτ : τ.PosSemidef := Φ.mapsPositive σ hσ
    have hEmbedSupport :
        Matrix.Supports ((psdSupportEmbeddingMap σ hσ) X) σ := by
      simpa [psdSupportEmbeddingMap_apply] using
        _root_.QITBench.psdSupportIsometry_conj_supports σ hσ X
    have hOutSupport :
        Matrix.Supports (Φ.map ((psdSupportEmbeddingMap σ hσ) X)) τ := by
      simpa [τ] using channel_map_supports Φ hσ hEmbedSupport
    calc
      ((psdSupportCompressionMap τ hτ).comp
          (Φ.map.comp (psdSupportEmbeddingMap σ hσ)) X).trace =
          (psdSupportCompress τ hτ
            (Φ.map ((psdSupportEmbeddingMap σ hσ) X))).trace := by
            simp [τ, psdSupportCompressionMap_apply]
      _ = (Φ.map ((psdSupportEmbeddingMap σ hσ) X)).trace := by
            exact psdSupportCompress_trace_of_supports_right hτ hOutSupport
      _ = ((psdSupportEmbeddingMap σ hσ) X).trace := Φ.tracePreserving _
      _ = X.trace := by
            simp [psdSupportEmbeddingMap_apply, psdSupportIsometry_conj_trace]
  mapsPositive := by
    intro X hX
    exact
      MatrixMap.isCompletelyPositive_mapsPositive
        ((psdSupportCompressionMap (Φ.map σ) (Φ.mapsPositive σ hσ)).comp
          (Φ.map.comp (psdSupportEmbeddingMap σ hσ)))
        (MatrixMap.isCompletelyPositive_comp
          (psdSupportCompressionMap (Φ.map σ) (Φ.mapsPositive σ hσ))
          (Φ.map.comp (psdSupportEmbeddingMap σ hσ))
          (MatrixMap.ofKraus_completelyPositive _)
          (MatrixMap.isCompletelyPositive_comp Φ.map
            (psdSupportEmbeddingMap σ hσ)
            Φ.completelyPositive (MatrixMap.ofKraus_completelyPositive _)))
        X hX

@[simp]
theorem psdSupportRestrictedChannel_map_reference
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (σ : CMatrix a) (hσ : σ.PosSemidef) :
    (psdSupportRestrictedChannel Φ σ hσ).map
        (psdSupportCompress σ hσ σ) =
      psdSupportCompress (Φ.map σ) (Φ.mapsPositive σ hσ) (Φ.map σ) := by
  have hrec :
      psdSupportIsometry σ hσ * psdSupportCompress σ hσ σ *
          Matrix.conjTranspose (psdSupportIsometry σ hσ) = σ := by
    simpa using psdSupportCompress_reconstruct_self σ hσ
  simp [psdSupportRestrictedChannel, psdSupportEmbeddingMap_apply,
    psdSupportCompressionMap_apply, hrec]

@[simp]
theorem psdSupportRestrictedChannel_applyState_compressed
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (hSupport : Matrix.Supports ρ.matrix σ) :
    (psdSupportRestrictedChannel Φ σ hσ).applyState
        (psdSupportCompressedState ρ hσ hSupport) =
      psdSupportCompressedState (Φ.applyState ρ) (Φ.mapsPositive σ hσ)
        (channel_applyState_supports_of_supports ρ hσ Φ hSupport) := by
  apply State.ext
  have hrec :
      psdSupportIsometry σ hσ *
          psdSupportCompress σ hσ ρ.matrix *
          Matrix.conjTranspose (psdSupportIsometry σ hσ) =
        ρ.matrix := by
    simpa using
      psdSupportCompress_reconstruct_of_supports
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
  simp [Channel.applyState, psdSupportRestrictedChannel,
    psdSupportEmbeddingMap_apply, psdSupportCompressionMap_apply, hrec]

theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supportCompressed
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (psdSupportCompressedState (Φ.applyState ρ) (Φ.mapsPositive σ hσ)
          (channel_applyState_supports_of_supports ρ hσ Φ hSupport))
        (psdSupportCompress (Φ.map σ) (Φ.mapsPositive σ hσ) (Φ.map σ))
        (psdSupportCompressedState_reference_posDef
          (Φ.mapsPositive σ hσ)).posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite
        (psdSupportCompressedState ρ hσ hSupport)
        (psdSupportCompress σ hσ σ)
        (psdSupportCompressedState_reference_posDef hσ).posSemidef α := by
  classical
  letI : Nonempty (psdSupportIndex σ hσ) :=
    psdSupportCompressedState_support_nonempty ρ hσ hSupport
  let ρc : State (psdSupportIndex σ hσ) :=
    psdSupportCompressedState ρ hσ hSupport
  let σc : CMatrix (psdSupportIndex σ hσ) :=
    psdSupportCompress σ hσ σ
  let Ψ := psdSupportRestrictedChannel Φ σ hσ
  have hσc : σc.PosDef := by
    simpa [σc] using psdSupportCompressedState_reference_posDef hσ
  have hσcΨ : (Ψ.map σc).PosDef := by
    simpa [Ψ, σc] using
      psdSupportCompressedState_reference_posDef (Φ.mapsPositive σ hσ)
  have hDPI :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_posDef_reference
      ρc Ψ hσc hσcΨ α hα
  simpa [ρc, σc, Ψ] using hDPI

theorem sandwichedRenyiPSDReferenceHighAlphaFinite_supportCompress_eq
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α =
      sandwichedRenyiPSDReferenceHighAlphaFinite
        (psdSupportCompressedState ρ hσ hSupport)
        (psdSupportCompress σ hσ σ)
        (psdSupportCompressedState_reference_posDef hσ).posSemidef α := by
  classical
  letI : Nonempty (psdSupportIndex σ hσ) :=
    psdSupportCompressedState_support_nonempty ρ hσ hSupport
  let V : Matrix a (psdSupportIndex σ hσ) ℂ := psdSupportIsometry σ hσ
  let ρc : State (psdSupportIndex σ hσ) :=
    psdSupportCompressedState ρ hσ hSupport
  let σc : CMatrix (psdSupportIndex σ hσ) :=
    psdSupportCompress σ hσ σ
  let s : ℝ := (1 - α) / (2 * α)
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    field_simp [ne_of_gt hα_pos]
    linarith
  have hV : Matrix.conjTranspose V * V =
      (1 : CMatrix (psdSupportIndex σ hσ)) := by
    simpa [V] using psdSupportIsometry_isometry σ hσ
  have hρ_embed :
      V * ρc.matrix * Matrix.conjTranspose V = ρ.matrix := by
    simpa [V, ρc, psdSupportCompressedState_matrix] using
      psdSupportCompress_reconstruct_of_supports
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
  have hpow_embed :
      V * CFC.rpow σc s * Matrix.conjTranspose V = CFC.rpow σ s := by
    simpa [V, σc, s] using
      _root_.QITBench.cMatrix_rpow_psdSupportCompress_reconstruct_self
        σ hσ hs_ne
  have hinner_embed :
      V * sandwichedRenyiReferenceInner ρc σc α *
          Matrix.conjTranspose V =
        sandwichedRenyiReferenceInner ρ σ α := by
    unfold sandwichedRenyiReferenceInner
    dsimp [ρc, σc, s]
    let P : CMatrix (psdSupportIndex σ hσ) := CFC.rpow σc s
    let R : CMatrix (psdSupportIndex σ hσ) := ρc.matrix
    have halg :
        V * (P * R * P) * Matrix.conjTranspose V =
          (V * P * Matrix.conjTranspose V) *
            (V * R * Matrix.conjTranspose V) *
            (V * P * Matrix.conjTranspose V) := by
      symm
      calc
        (V * P * Matrix.conjTranspose V) *
            (V * R * Matrix.conjTranspose V) *
            (V * P * Matrix.conjTranspose V) =
          V * P * (Matrix.conjTranspose V * V) * R *
            (Matrix.conjTranspose V * V) * P *
            Matrix.conjTranspose V := by
              simp [Matrix.mul_assoc]
        _ = V * P * R * P * Matrix.conjTranspose V := by
              rw [hV]
              simp [Matrix.mul_assoc]
        _ = V * (P * R * P) * Matrix.conjTranspose V := by
              simp [Matrix.mul_assoc]
    calc
      V * (CFC.rpow σc s * ρc.matrix * CFC.rpow σc s) *
          Matrix.conjTranspose V =
        (V * CFC.rpow σc s * Matrix.conjTranspose V) *
          (V * ρc.matrix * Matrix.conjTranspose V) *
          (V * CFC.rpow σc s * Matrix.conjTranspose V) := by
            simpa [P, R] using halg
      _ = CFC.rpow σ s * ρ.matrix * CFC.rpow σ s := by
            rw [hpow_embed, hρ_embed]
  let A : CMatrix (psdSupportIndex σ hσ) :=
    sandwichedRenyiReferenceInner ρc σc α
  have hA : A.PosSemidef := by
    simpa [A, ρc, σc] using
      sandwichedRenyiReferenceInner_posSemidef
        ρc (psdSupportCompressedState_reference_posDef hσ).posSemidef α
  have hpower :
      psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
          (sandwichedRenyiReferenceInner_posSemidef ρ hσ α) α =
        psdTracePower A hA α := by
    have hiso :=
      _root_.QITBench.psdTracePower_isometry_conj
        (V := V) hA hV (p := α) hα_pos
    have hVA :
        V * A * Matrix.conjTranspose V =
          sandwichedRenyiReferenceInner ρ σ α := by
      simpa [A] using hinner_embed
    simpa [A, hVA] using hiso
  simpa [sandwichedRenyiPSDReferenceHighAlphaFinite, A, ρc, σc] using
    congrArg (fun t : ℝ => (1 / (α - 1)) * log2 t) hpower

theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supported
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα : 1 < α)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α := by
  classical
  have hSupportOut :
      Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) :=
    channel_applyState_supports_of_supports ρ hσ Φ hSupport
  have hout :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_supportCompress_eq
      (Φ.applyState ρ) (Φ.mapsPositive σ hσ) hSupportOut α hα
  have hin :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_supportCompress_eq
      ρ hσ hSupport α hα
  have hcomp :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supportCompressed
      ρ hσ Φ hSupport α hα
  rw [hout, hin]
  exact hcomp

theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  refine
    sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_finite_branch
      ρ hσ Φ α ?_
  intro hSupport
  exact
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supported
      ρ hσ Φ α hα hSupport

noncomputable def sandwichedRenyiPSDReferenceE
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : EReal :=
  if α < 1 then
    sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ α
  else if α = 1 then
    relativeEntropyPSDReferenceTraceLogE ρ σ hσ
  else
    sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α

@[simp]
theorem sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) {α : ℝ}
    (hα : α < 1) :
    sandwichedRenyiPSDReferenceE ρ σ hσ α =
      sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ α := by
  simp [sandwichedRenyiPSDReferenceE, hα]

@[simp]
theorem sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) {α : ℝ}
    (hα : α = 1) :
    sandwichedRenyiPSDReferenceE ρ σ hσ α =
      relativeEntropyPSDReferenceTraceLogE ρ σ hσ := by
  subst α
  simp [sandwichedRenyiPSDReferenceE]

@[simp]
theorem sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) {α : ℝ}
    (hα : 1 < α) :
    sandwichedRenyiPSDReferenceE ρ σ hσ α =
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  have hnot_lt : ¬ α < 1 := not_lt.mpr hα.le
  have hne : α ≠ 1 := ne_of_gt hα
  simp [sandwichedRenyiPSDReferenceE, hnot_lt, hne]

theorem sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_lt_lt_one_or_one_lt
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_range : (1 / 2 < α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyiPSDReferenceE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceE ρ σ hσ α := by
  by_cases hlt : α < 1
  · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hlt,
      sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hlt]
    rcases hα_range with hlow | hhigh
    · exact
        sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel
          ρ hσ Φ α hlow.1 hlow.2
    · linarith
  · rcases hα_range with hlow | hhigh
    · linarith
    · rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hhigh,
        sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hhigh]
      exact
        sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel
          ρ hσ Φ α hhigh

theorem sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_le_lt_one_or_one_lt
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyiPSDReferenceE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceE ρ σ hσ α := by
  by_cases hlt : α < 1
  · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hlt,
      sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hlt]
    rcases hα_range with hlow | hhigh
    · rcases hlow with ⟨hhalf, hlt_one⟩
      by_cases hEq : α = 1 / 2
      · subst α
        exact sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel_half
          ρ hσ Φ
      · have hhalf_strict : 1 / 2 < α := lt_of_le_of_ne hhalf (Ne.symm hEq)
        exact
          sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel
            ρ hσ Φ α hhalf_strict hlt_one
    · linarith
  · rcases hα_range with hlow | hhigh
    · linarith
    · rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hhigh,
        sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hhigh]
      exact
        sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel
          ρ hσ Φ α hhigh

theorem sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyiPSDReferenceE ρ σ hσ α ≥
      sandwichedRenyiPSDReferenceE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α := by
  exact
    sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_le_lt_one_or_one_lt
      ρ hσ Φ α hα_range

theorem sandwichedRenyiQ_jointConcave_lowAlpha_diagonal
    (ρ₁ ρ₂ σ₁ σ₂ : a → ℝ)
    (hρ₁ : ∀ i, 0 ≤ ρ₁ i) (hρ₂ : ∀ i, 0 ≤ ρ₂ i)
    (hσ₁ : ∀ i, 0 < σ₁ i) (hσ₂ : ∀ i, 0 < σ₂ i)
    {α t : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let ρt : a → ℝ := fun i => t * ρ₁ i + (1 - t) * ρ₂ i
    let σt : a → ℝ := fun i => t * σ₁ i + (1 - t) * σ₂ i
    t * sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ₁ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ₁ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ₁ hρ₁)
        (cMatrix_diagonal_ofReal_posSemidef σ₁ fun i => (hσ₁ i).le)
        α +
      (1 - t) * sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ₂ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ₂ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ₂ hρ₂)
        (cMatrix_diagonal_ofReal_posSemidef σ₂ fun i => (hσ₂ i).le)
        α ≤
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρt i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σt i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρt fun i =>
          add_nonneg (mul_nonneg ht0 (hρ₁ i))
            (mul_nonneg (sub_nonneg.mpr ht1) (hρ₂ i)))
        (cMatrix_diagonal_ofReal_posSemidef σt fun i =>
          add_nonneg (mul_nonneg ht0 (hσ₁ i).le)
            (mul_nonneg (sub_nonneg.mpr ht1) (hσ₂ i).le))
        α := by
  let ρt : a → ℝ := fun i => t * ρ₁ i + (1 - t) * ρ₂ i
  let σt : a → ℝ := fun i => t * σ₁ i + (1 - t) * σ₂ i
  have hα_pos : 0 < α := by linarith
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  have hρt : ∀ i, 0 ≤ ρt i := by
    intro i
    exact add_nonneg (mul_nonneg ht0 (hρ₁ i))
      (mul_nonneg (sub_nonneg.mpr ht1) (hρ₂ i))
  have hσt : ∀ i, 0 < σt i := by
    intro i
    have hmin : 0 < min (σ₁ i) (σ₂ i) := lt_min (hσ₁ i) (hσ₂ i)
    have hsum : t + (1 - t) = 1 := by ring
    have hle :
        min (σ₁ i) (σ₂ i) * (t + (1 - t)) ≤
          t * σ₁ i + (1 - t) * σ₂ i := by
      have hle₁ :
          min (σ₁ i) (σ₂ i) * t ≤ t * σ₁ i := by
        calc
          min (σ₁ i) (σ₂ i) * t = t * min (σ₁ i) (σ₂ i) := by ring
          _ ≤ t * σ₁ i :=
            mul_le_mul_of_nonneg_left (min_le_left (σ₁ i) (σ₂ i)) ht0
      have hle₂ :
          min (σ₁ i) (σ₂ i) * (1 - t) ≤ (1 - t) * σ₂ i := by
        calc
          min (σ₁ i) (σ₂ i) * (1 - t) =
              (1 - t) * min (σ₁ i) (σ₂ i) := by ring
          _ ≤ (1 - t) * σ₂ i :=
            mul_le_mul_of_nonneg_left
              (min_le_right (σ₁ i) (σ₂ i)) (sub_nonneg.mpr ht1)
      calc
        min (σ₁ i) (σ₂ i) * (t + (1 - t)) =
            min (σ₁ i) (σ₂ i) * t + min (σ₁ i) (σ₂ i) * (1 - t) := by ring
        _ ≤ t * σ₁ i + (1 - t) * σ₂ i := add_le_add hle₁ hle₂
    have hpos : 0 < min (σ₁ i) (σ₂ i) * (t + (1 - t)) := by
      rw [hsum, mul_one]
      exact hmin
    exact lt_of_lt_of_le hpos hle
  have heval₁ :
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ₁ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ₁ i : ℂ) : CMatrix a)
        (Matrix.PosSemidef.diagonal (d := fun i => (ρ₁ i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (ρ₁ i : ℂ)
          exact_mod_cast hρ₁ i))
        (Matrix.PosSemidef.diagonal (d := fun i => (σ₁ i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (σ₁ i : ℂ)
          exact_mod_cast (hσ₁ i).le))
        α =
        ∑ i, ρ₁ i ^ α * σ₁ i ^ (1 - α) :=
    sandwichedRenyiQ_diagonal_eval ρ₁ σ₁ hρ₁ hσ₁ hα_pos
  have heval₂ :
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ₂ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ₂ i : ℂ) : CMatrix a)
        (Matrix.PosSemidef.diagonal (d := fun i => (ρ₂ i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (ρ₂ i : ℂ)
          exact_mod_cast hρ₂ i))
        (Matrix.PosSemidef.diagonal (d := fun i => (σ₂ i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (σ₂ i : ℂ)
          exact_mod_cast (hσ₂ i).le))
        α =
        ∑ i, ρ₂ i ^ α * σ₂ i ^ (1 - α) :=
    sandwichedRenyiQ_diagonal_eval ρ₂ σ₂ hρ₂ hσ₂ hα_pos
  have hevalt :
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρt i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σt i : ℂ) : CMatrix a)
        (Matrix.PosSemidef.diagonal (d := fun i => (ρt i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (ρt i : ℂ)
          exact_mod_cast hρt i))
        (Matrix.PosSemidef.diagonal (d := fun i => (σt i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (σt i : ℂ)
          exact_mod_cast (hσt i).le))
        α =
        ∑ i, ρt i ^ α * σt i ^ (1 - α) :=
    sandwichedRenyiQ_diagonal_eval ρt σt hρt hσt hα_pos
  dsimp only
  rw [heval₁, heval₂, hevalt]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    sandwichedRenyiQ_scalarTerm_concave_lowAlpha
      (p₁ := ρ₁ i) (p₂ := ρ₂ i) (q₁ := σ₁ i) (q₂ := σ₂ i)
      (α := α) (t := t)
      (hρ₁ i) (hρ₂ i) (hσ₁ i) (hσ₂ i)
      hα_nonneg hα_le_one ht0 ht1

end State

end

end QITBench
