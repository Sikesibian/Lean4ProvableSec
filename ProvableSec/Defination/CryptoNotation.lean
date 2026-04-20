import ProvableSec.Defination.Baisc.Complexity.ComplexityClass
import ProvableSec.Defination.OneWayFunction.owfBasic
import Mathlib.Data.Real.Basic

/-!
# Crypto Notation Facade

该文件仅提供密码学全局语义接口。
接口聚焦于随机带导致的成功概率，并把讨论对象固定在 PPT 敌手。

This module only exposes a global cryptographic semantics interface.
It focuses on random-tape-induced success probabilities for PPT adversaries.
-/

namespace ProvableSec
namespace CryptoNotation

open TuringMachine.Crypto
open OneWayFunction

section CoreTypes

abbrev OWFFamily := OneWayFunction.OWFFamily

/--
密码学 PPT 反演器别名。
-/
abbrev Inverter := OneWayFunction.Inverter

end CoreTypes

section SecurityNotations

/--
密码学标准记号：Pr[F](A, n)
表示反演器 A 在安全参数 n 下，对函数族 F 的求逆成功概率。
-/
scoped notation "Pr[" F "](" A "," n ")" => OneWayFunction.Pr F A n

/--
密码学标准记号：PrFail[F](A, n)
表示反演失败概率。
-/
scoped notation "PrFail[" F "](" A "," n ")" => OneWayFunction.PrFail F A n

/--
弱单向性简写，支持如 `Weak F` 的自然书写。
-/
abbrev Weak (F : OWFFamily) : Prop := OneWayFunction.IsWeakOWF F

/--
强单向性简写，支持如 `Strong F` 的自然书写。
-/
abbrev Strong (F : OWFFamily) : Prop := OneWayFunction.IsStrongOWF F

/-- 显式间隙的 δ-弱单向性简写，常用于归约过程中的中间状态描述。 -/
abbrev DeltaWeak (F : OWFFamily) (δ : Nat → ℝ) : Prop := OneWayFunction.IsDeltaWeakOWF F δ

end SecurityNotations

section Primitives

variable {K : Type u} {Λ : Type v} {σ : Type w}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

/--
**弱单向函数对象 (wOWF)**
将函数族与其弱单向性证明捆绑在一起。
这允许我们在高层定理中直接声明参数 `(w : wOWF)`，而不是 `(F : OWFFamily) (h : Weak F)`。
-/
structure wOWF where
  family : OWFFamily
  isWeak : Weak family

/--
**强单向函数对象 (sOWF)**
将函数族与其强单向性证明捆绑在一起。
-/
structure sOWF where
  family : OWFFamily
  isStrong : Strong family

/--
**弱到强单向性构造接口 (Weak-to-Strong Transform)**
抽象了类似姚氏定理 (Yao's Hardness Amplification) 的构造。
它不仅提供了一个映射 `map`，还提供了一个严格的证明 `correct`。
-/
structure WeakToStrongTransform where
  /-- 构造函数映射：F -> F' -/
  map : OWFFamily → OWFFamily
  /-- 正确性：如果 F 是弱单向的，则 F' 必须是强单向的 -/
  correct : ∀ (F : OWFFamily), Weak F → Strong (map F)

namespace wOWF

/--
**对象化硬度放大 (Object-Oriented Amplification)**
给定一个弱单向函数对象 `w` 和一个证明框架 `T`，直接提升为强单向函数对象。
-/
def amplify (w : wOWF) (T : WeakToStrongTransform) : sOWF where
  family := T.map w.family
  isStrong := T.correct w.family w.isWeak

end wOWF

end Primitives

end CryptoNotation
end ProvableSec
