import ProvableSec.Defination.CryptoNotation

/-!
# CryptoNotation Usage Examples / 记号使用与对象化演示

展示如何使用顶层密码学抽象接口、scoped notation 语法糖，
以及如同面向对象编程一般丝滑的硬度放大调用。
-/

namespace ProvableSec.Examples.Usage

open ProvableSec.CryptoNotation
open scoped CryptoNotation

section ProbabilityNotations

variable (F : OWFFamily)
variable (A : Inverter)
variable (n : Nat)

/-- 1. 语法糖直接转化为底层的概率等式。 -/
example : PrFail[F](A, n) = 1 - Pr[F](A, n) := by
  exact OneWayFunction.PrFail_eq_failureProb F A n

/-- 2. 使用间隙参数的弱单向性简写。 -/
example (δ : Nat → ℝ) : DeltaWeak F δ ↔ OneWayFunction.IsDeltaWeakOWF F δ := by
  rfl

end ProbabilityNotations

section ObjectOrientedAmplification

/-- 3. 展示弱到强 (wOWF 到 sOWF) 的过程。

在使用姚氏定理（Yao's Theorem）进行推导时，只需 `w.amplify Yao`，Lean 4 的类型系统会自动强制校验定理的前提。
-/
def applyYaoTransform
    (w : wOWF)
    (Yao : WeakToStrongTransform) : sOWF :=
  w.amplify Yao

end ObjectOrientedAmplification

end ProvableSec.Examples.Usage
