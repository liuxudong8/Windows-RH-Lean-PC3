import OrderPreservingBijection.Exceptional.PrimeCountAsymptoticInProgressions
import OrderPreservingBijection.Exceptional.Statement
import OrderPreservingBijection.Exceptional.ExceptionalZeroInterface

open Formalism.HermitianLattices.GL2a2
open Formalism.HermitianLattices.GL2PrimeSums
open Formalism.ZeroFreeDirichlet
open OrderPreservingBijection.ExceptionalZero

-- 图纸：错版假设
#check @ZFRDirichlet
-- 图纸：22 条
#check @ZeroFreeSymmetric
#check @PrimeCountAsymptoticInProgressions
#check @ShortIntervalImpliesProgressions
#check @PrimesInProgressionCountLowerBound
#check @ExceptionalCharacterCountBound
#check @TailSumBound
-- 真件：零 axiom 的零自由区主定理
#check @dirichlet_exceptional_zero_unique_zero_free_region

#print axioms ZFRDirichlet
#print axioms ZeroFreeSymmetric
#print axioms dirichlet_exceptional_zero_unique_zero_free_region
