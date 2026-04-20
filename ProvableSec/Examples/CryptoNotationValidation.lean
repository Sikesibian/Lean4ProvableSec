import ProvableSec.Defination.CryptoNotation

/-!
# CryptoNotation Validation Examples

中文：验证抽象接口层的类型透明度与定义等价性。
English: Validate type transparency and definitional equality of the abstract interface layer.
-/

namespace ProvableSec.Examples

open TuringMachine.Crypto
open ProvableSec.CryptoNotation
open scoped CryptoNotation

section SecurityValidation

variable (F : OWFFamily)
variable (A : BitPPTAdversary)
variable (n : Nat)

-- 验证宏展开后与底层反演成功率函数的定义完全等价 (Defeq)
example : Pr[F](A, n) = OneWayFunction.inversionSuccessProb F A n := by
  rfl

example : PrFail[F](A, n) = OneWayFunction.failureProb F A n := by
  rfl

-- 验证 Weak 简写与底层 IsWeakOWF 的无缝对接
example : Weak F ↔ OneWayFunction.IsWeakOWF F := by
  rfl

-- 验证 Strong 简写与底层 IsStrongOWF 的无缝对接
example : Strong F ↔ OneWayFunction.IsStrongOWF F := by
  rfl

end SecurityValidation

end ProvableSec.Examples
