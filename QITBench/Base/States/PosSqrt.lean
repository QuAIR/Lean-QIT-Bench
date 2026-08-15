/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.State
public import QITBench.Base.Util.Matrix.PosSqrt

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QITBench

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

def sqrtMatrix (rho : State a) : CMatrix a :=
  psdSqrt rho.matrix

theorem sqrtMatrix_pos (rho : State a) :
    rho.sqrtMatrix.PosSemidef :=
  psdSqrt_pos rho.matrix

theorem sqrtMatrix_isHermitian (rho : State a) :
    rho.sqrtMatrix.IsHermitian :=
  psdSqrt_isHermitian rho.matrix

@[simp]
theorem sqrtMatrix_mul_self (rho : State a) :
    rho.sqrtMatrix * rho.sqrtMatrix = rho.matrix :=
  psdSqrt_mul_self_of_posSemidef rho.pos

end State

end

end QITBench
