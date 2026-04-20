import ProvableSec.Defination.CryptoNotation

/-!
# CryptoNotation Validation Examples

中文：验证抽象接口层的类型透明度与定义等价性。
English: Validate type transparency and definitional equality of the abstract interface layer.
-/

namespace ProvableSec.Examples

open TuringMachine.Crypto
open OneWayFunction
open ProvableSec.CryptoNotation
open scoped CryptoNotation

section SecurityValidation

variable {K Λ σ : Type} [DecidableEq K] [Inhabited Λ] [Inhabited σ]
variable (F : OWFFamily)
variable (A : BitPPTAdversary)
variable (n : Nat)

-- 验证宏展开后与底层反演成功率函数的定义完全等价 (Defeq)
example : Pr[F](A, n) = inversionSuccessProb F A n := by
  rfl

example : PrFail[F](A, n) = failureProb F A n := by
  rfl

-- 验证 Weak 简写与底层 IsWeakOWF 的无缝对接
example : Weak F ↔ IsWeakOWF F := by
  rfl

-- 验证 Strong 简写与底层 IsStrongOWF 的无缝对接
example : Strong F ↔ IsStrongOWF F := by
  rfl

end SecurityValidation

end ProvableSec.Examples
