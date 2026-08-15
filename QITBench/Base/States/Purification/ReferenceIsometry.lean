/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.States.Purification.Predicate

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QITBench

universe u v w

noncomputable section

structure ReferenceIsometry (r₁ : Type u) (r₂ : Type v)
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂] where
  matrix : Matrix r₂ r₁ Complex
  isometry : Matrix.conjTranspose matrix * matrix = 1

namespace ReferenceIsometry

variable {r₁ : Type u} {r₂ : Type v} {a : Type w}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

variable (V : ReferenceIsometry r₁ r₂)

theorem sum_mul_star (i j : r₁) :
    (Finset.univ.sum fun k : r₂ => V.matrix k i * star (V.matrix k j)) =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun V.isometry j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.one_apply, eq_comm, mul_comm] using h

def ofInjective
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) (hf : Function.Injective f) :
    ReferenceIsometry α β where
  matrix := fun y x => if y = f x then 1 else 0
  isometry := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single (f i)]
      · simp [Matrix.conjTranspose]
      · intro y _ hy
        simp [Matrix.conjTranspose, hy]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ (f i)))
    · rw [Matrix.mul_apply]
      rw [Finset.sum_eq_zero]
      · simp [hij]
      · intro y _
        by_cases hyi : y = f i
        · have hfi_ne_fj : f i ≠ f j := by
            intro h
            exact hij (hf h)
          have hyj : y ≠ f j := by
            intro hyj
            exact hfi_ne_fj (hyi.symm.trans hyj)
          simp [Matrix.conjTranspose, hyi, hfi_ne_fj]
        · simp [Matrix.conjTranspose, hyi]

variable {r₃ : Type w} [Fintype r₃] [DecidableEq r₃]

def comp (W : ReferenceIsometry r₂ r₃) (V : ReferenceIsometry r₁ r₂) :
    ReferenceIsometry r₁ r₃ where
  matrix := W.matrix * V.matrix
  isometry := by
    calc
      Matrix.conjTranspose (W.matrix * V.matrix) * (W.matrix * V.matrix) =
          Matrix.conjTranspose V.matrix *
            (Matrix.conjTranspose W.matrix * W.matrix) * V.matrix := by
            rw [Matrix.conjTranspose_mul]
            rw [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (Matrix.conjTranspose W.matrix) W.matrix V.matrix]
            rw [← Matrix.mul_assoc (Matrix.conjTranspose V.matrix)
              (Matrix.conjTranspose W.matrix * W.matrix) V.matrix]
      _ = Matrix.conjTranspose V.matrix * V.matrix := by
            rw [W.isometry, Matrix.mul_one]
      _ = 1 := V.isometry

def targetBlock (X : CMatrix (Prod r₁ a)) (x y : a) : CMatrix r₁ :=
  fun i j => X (i, x) (j, y)

def applyMatrix (X : CMatrix (Prod r₁ a)) : CMatrix (Prod r₂ a) :=
  fun x y => (V.matrix * targetBlock X x.2 y.2 * Matrix.conjTranspose V.matrix) x.1 y.1

def rightBlock (X : CMatrix (Prod a r₁)) (x y : a) : CMatrix r₁ :=
  fun i j => X (x, i) (y, j)

def applyMatrixRight (X : CMatrix (Prod a r₁)) : CMatrix (Prod a r₂) :=
  fun x y => (V.matrix * rightBlock X x.1 y.1 * Matrix.conjTranspose V.matrix) x.2 y.2

def applyAmp (ψ : Prod r₁ a -> Complex) : Prod r₂ a -> Complex :=
  fun x => V.matrix.mulVec (fun i : r₁ => ψ (i, x.2)) x.1

def applyAmpRight (ψ : Prod a r₁ -> Complex) : Prod a r₂ -> Complex :=
  fun x => V.matrix.mulVec (fun i : r₁ => ψ (x.1, i)) x.2

theorem rankOne_applyAmp (ψ : Prod r₁ a -> Complex) :
    rankOneMatrix (V.applyAmp ψ) = V.applyMatrix (rankOneMatrix ψ) := by
  ext x y
  simp [rankOneMatrix, applyAmp, applyMatrix, targetBlock, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem rankOne_applyAmpRight (ψ : Prod a r₁ -> Complex) :
    rankOneMatrix (V.applyAmpRight ψ) = V.applyMatrixRight (rankOneMatrix ψ) := by
  ext x y
  simp [rankOneMatrix, applyAmpRight, applyMatrixRight, rightBlock, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem trace_apply_block (B : CMatrix r₁) :
    (V.matrix * B * Matrix.conjTranspose V.matrix).trace = B.trace := by
  rw [Matrix.trace_mul_cycle, V.isometry, Matrix.one_mul]

theorem partialTraceA_applyMatrix (X : CMatrix (Prod r₁ a)) :
    partialTraceA (a := r₂) (b := a) (V.applyMatrix X) =
      partialTraceA (a := r₁) (b := a) X := by
  ext x y
  exact V.trace_apply_block (targetBlock X x y)

theorem partialTraceB_applyMatrix_of_referenceIsometry [Fintype a]
    (X : CMatrix (Prod r₁ a)) :
    partialTraceB (a := r₂) (b := a) (V.applyMatrix X) =
      V.matrix * partialTraceB (a := r₁) (b := a) X *
        Matrix.conjTranspose V.matrix := by
  ext i j
  simp [partialTraceB, applyMatrix, targetBlock, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

theorem partialTraceB_applyMatrixRight [Fintype a] (X : CMatrix (Prod a r₁)) :
    partialTraceB (a := a) (b := r₂) (V.applyMatrixRight X) =
      partialTraceB (a := a) (b := r₁) X := by
  ext x y
  exact V.trace_apply_block (rightBlock X x y)

theorem partialTraceA_applyMatrixRight [Fintype a] (X : CMatrix (Prod a r₁)) :
    partialTraceA (a := a) (b := r₂) (V.applyMatrixRight X) =
      V.matrix * partialTraceA (a := a) (b := r₁) X * Matrix.conjTranspose V.matrix := by
  ext x y
  simp [partialTraceA, applyMatrixRight, rightBlock, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

theorem matrix_mul_conjTranspose_mul_matrix (B C : CMatrix r₁) :
    (V.matrix * B * Matrix.conjTranspose V.matrix) *
        (V.matrix * C * Matrix.conjTranspose V.matrix) =
      V.matrix * (B * C) * Matrix.conjTranspose V.matrix := by
  calc
    (V.matrix * B * Matrix.conjTranspose V.matrix) *
        (V.matrix * C * Matrix.conjTranspose V.matrix) =
      V.matrix * B * (Matrix.conjTranspose V.matrix * V.matrix) *
        C * Matrix.conjTranspose V.matrix := by
          simp only [Matrix.mul_assoc]
    _ = V.matrix * B * (1 : CMatrix r₁) * C * Matrix.conjTranspose V.matrix := by
          rw [V.isometry]
    _ = V.matrix * (B * C) * Matrix.conjTranspose V.matrix := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem trace_applyMatrix [Fintype a] (X : CMatrix (Prod r₁ a)) :
    (V.applyMatrix X).trace = X.trace := by
  have h := congrArg Matrix.trace (V.partialTraceA_applyMatrix X)
  simpa [partialTraceA_trace] using h

def applyPureVector [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod r₁ a)) :
    PureVector (Prod r₂ a) where
  amp := V.applyAmp Ψ.amp
  trace_rankOne_eq_one := by
    have h := congrArg Matrix.trace (V.partialTraceA_applyMatrix (rankOneMatrix Ψ.amp))
    rw [partialTraceA_trace, partialTraceA_trace] at h
    rw [V.rankOne_applyAmp Ψ.amp, h, Ψ.trace_rankOne_eq_one]

theorem applyPureVector_amp [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod r₁ a)) :
    (V.applyPureVector Ψ).amp = V.applyAmp Ψ.amp :=
  rfl

theorem marginalA_applyPureVector [Fintype a] [DecidableEq a]
    (Ψ : PureVector (Prod r₁ a)) :
    (V.applyPureVector Ψ).state.marginalA.matrix =
      V.matrix * Ψ.state.marginalA.matrix * Matrix.conjTranspose V.matrix := by
  rw [State.marginalA_matrix]
  rw [PureVector.state_matrix]
  rw [applyPureVector_amp]
  rw [V.rankOne_applyAmp]
  rw [V.partialTraceB_applyMatrix_of_referenceIsometry]
  rfl

def applyPureVectorRight [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod a r₁)) :
    PureVector (Prod a r₂) :=
  (V.applyPureVector (Ψ.reindex (Equiv.prodComm a r₁))).reindex (Equiv.prodComm r₂ a)

theorem applyPureVectorRight_amp [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod a r₁)) :
    (V.applyPureVectorRight Ψ).amp = V.applyAmpRight Ψ.amp :=
  rfl

theorem rankOne_applyPureVectorRight [Fintype a] [DecidableEq a]
    (Ψ : PureVector (Prod a r₁)) :
    (V.applyPureVectorRight Ψ).state.matrix = V.applyMatrixRight Ψ.state.matrix := by
  rw [PureVector.state_matrix, PureVector.state_matrix]
  exact V.rankOne_applyAmpRight Ψ.amp

theorem marginalA_applyPureVectorRight [Fintype a] [DecidableEq a]
    (Ψ : PureVector (Prod a r₁)) :
    (V.applyPureVectorRight Ψ).state.marginalA = Ψ.state.marginalA := by
  apply State.ext
  rw [State.marginalA_matrix, State.marginalA_matrix]
  rw [V.rankOne_applyPureVectorRight]
  exact V.partialTraceB_applyMatrixRight Ψ.state.matrix

theorem applyPureVector_purifies [Fintype a] [DecidableEq a]
    {Ψ : PureVector (Prod r₁ a)} {ρ : State a} (hΨ : Ψ.Purifies ρ) :
    (V.applyPureVector Ψ).Purifies ρ := by
  rw [PureVector.purifies_iff]
  rw [PureVector.state_matrix]
  change partialTraceA (a := r₂) (b := a) (rankOneMatrix (V.applyAmp Ψ.amp)) = ρ.matrix
  rw [V.rankOne_applyAmp]
  rw [V.partialTraceA_applyMatrix]
  exact hΨ

variable {r₃ : Type*} {r₄ : Type*}
variable [Fintype r₃] [DecidableEq r₃] [Fintype r₄] [DecidableEq r₄]

def prod (V : ReferenceIsometry r₁ r₂) (W : ReferenceIsometry r₃ r₄) :
    ReferenceIsometry (Prod r₁ r₃) (Prod r₂ r₄) where
  matrix := Matrix.kronecker V.matrix W.matrix
  isometry := by
    change (V.matrix.kronecker W.matrix).conjTranspose *
        V.matrix.kronecker W.matrix = 1
    rw [show (V.matrix.kronecker W.matrix).conjTranspose =
        Matrix.kronecker V.matrix.conjTranspose W.matrix.conjTranspose from
      Matrix.conjTranspose_kronecker V.matrix W.matrix]
    rw [show Matrix.kronecker V.matrix.conjTranspose W.matrix.conjTranspose *
          Matrix.kronecker V.matrix W.matrix =
        Matrix.kronecker (V.matrix.conjTranspose * V.matrix)
          (W.matrix.conjTranspose * W.matrix) from by
      exact (Matrix.mul_kronecker_mul V.matrix.conjTranspose V.matrix
        W.matrix.conjTranspose W.matrix).symm]
    rw [V.isometry, W.isometry]
    exact Matrix.one_kronecker_one

def tensorPower (V : ReferenceIsometry r₁ r₂) :
    (n : ℕ) → ReferenceIsometry (TensorPower r₁ n) (TensorPower r₂ n)
  | 0 =>
      { matrix := fun _ _ => 1
        isometry := by
          ext x y
          cases x
          cases y
          rw [Matrix.mul_apply]
          simp [TensorPower, Matrix.conjTranspose]
          change (1 : ℂ) = (1 : ℂ)
          rfl }
  | n + 1 => V.prod (tensorPower V n)

@[simp]
theorem tensorPower_succ (V : ReferenceIsometry r₁ r₂) (n : ℕ) :
    V.tensorPower (n + 1) = V.prod (V.tensorPower n) :=
  rfl

def sumInr (extra : Type*) [Fintype extra] [DecidableEq extra]
    (r : Type*) [Fintype r] [DecidableEq r] :
    ReferenceIsometry r (Sum extra r) where
  matrix := fun x i =>
    match x with
    | Sum.inl _ => 0
    | Sum.inr j => if j = i then 1 else 0
  isometry := by
    classical
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose, Matrix.one_apply, eq_comm]

end ReferenceIsometry

end

end QITBench
