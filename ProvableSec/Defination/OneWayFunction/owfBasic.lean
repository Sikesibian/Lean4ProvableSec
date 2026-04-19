import ProvableSec.Defination.Baisc.Complexity.ComplexityClass
import Mathlib.Data.Real.Basic

/-!
# One-Way Function Basic Definitions

## 目标 / Goals
- 中文：基于已有 TM/PPT/复杂度接口，给出 weak OWF 与 strong OWF 的专业定义。
- English: provide professional definitions of weak and strong OWFs on top of existing TM/PPT/complexity interfaces.

## 核心思想 / Core Idea
- 中文：将“反演成功概率”抽象为接口 `OWFSemantics`，从而把概率层与机器语义层解耦。
- English: abstract inversion success probability via `OWFSemantics`, decoupling probability semantics from machine semantics.

## 公式 / Formulas

可忽略函数接口：

$$
\forall c\in\mathbb{N},\ \exists n_0,\ \forall n\ge n_0,
\ |\varepsilon(n)| \le \frac{1}{(n+1)^c}.
$$

weak OWF：

$$
\forall A\in PPT,\ \exists p\in Poly^+,\ \exists n_0,\ \forall n\ge n_0,
\ \Pr[A(f_n(U_n))\in f_n^{-1}(f_n(U_n))] \le 1 - \frac{1}{p(n)}.
$$

strong OWF：

$$
\forall A\in PPT,\ \Pr[A(f_n(U_n))\in f_n^{-1}(f_n(U_n))]
\text{ is negligible in } n.
$$
-/

namespace OneWayFunction

open Complexity
open TuringMachine.Crypto

universe u v w

/-- 比特串别名。 -/
abbrev Bits : Type := Complexity.Bits

/-- 正值多项式函数（`Nat → Nat`）。 -/
def IsPosPoly (p : Nat → Nat) : Prop :=
  IsPolynomial p ∧ ∀ n, 0 < p n

/-- 可忽略函数（`Nat → ℝ`）。 -/
def IsNegligible (ε : Nat → ℝ) : Prop :=
  ∀ c : Nat, ∃ n0 : Nat, ∀ n : Nat, n ≥ n0 →
    |ε n| ≤ (1 : ℝ) / (((n + 1 : Nat) : ℝ) ^ c)

/--
可高效计算的函数族接口（参数化按安全参数 `n`）。

`eval n x` 表示安全参数为 `n` 时函数值。
-/
structure EfficientFamily where
  eval : Nat → Bits → Bits
  timeBound : Nat → Nat
  timeBound_poly : IsPolynomial timeBound
  outLenBound : Nat → Nat
  outLenBound_poly : IsPolynomial outLenBound
  outLen_spec : ∀ n x, x.length = n → (eval n x).length ≤ outLenBound n

/--
OWF 常用函数族约束：在上面效率接口基础上加长度保持。
-/
structure OWFFamily extends EfficientFamily where
  lengthPreserving : ∀ n x, x.length = n → (eval n x).length = n

section Semantics

variable {K : Type u} {Λ : Type v} {σ : Type w}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

/--
反演实验语义接口：
`inversionSuccessProb f A n` 表示对安全参数 `n`，
PPT 反演器 `A` 针对函数族 `f` 的反演成功概率。
-/
structure OWFSemantics where
  inversionSuccessProb : (Nat → Bits → Bits) → BitPPTAdversary K Λ σ → Nat → ℝ
  inversionSuccessProb_range :
    ∀ f A n,
      0 ≤ inversionSuccessProb f A n ∧ inversionSuccessProb f A n ≤ 1

/--
- `f` 对应函数族 `(f_n)_n`。
- `A` 对应 PPT 反演器。
- `n` 对应安全参数。

可将 `PrInv S f A n` 读作：
在语义 `S` 下，反演器 `A` 对 `f` 在参数 `n` 的反演成功概率。
-/
def PrInv (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (f : Nat → Bits → Bits) (A : BitPPTAdversary K Λ σ) (n : Nat) : ℝ :=
  S.inversionSuccessProb f A n

/-- 抽取某反演器在参数 `n` 处的成功概率。 -/
def successProb (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) (A : BitPPTAdversary K Λ σ) (n : Nat) : ℝ :=
  PrInv (K := K) (Λ := Λ) (σ := σ) S F.eval A n

/-- 失败概率接口。 -/
def failureProb (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) (A : BitPPTAdversary K Λ σ) (n : Nat) : ℝ :=
  1 - successProb (K := K) (Λ := Λ) (σ := σ) S F A n

/--
weak OWF 定义：
任意 PPT 反演器都不能以“趋近 1 的概率”成功，
至少有 `1/p(n)` 级别的失败间隙。
-/
def IsWeakOWF (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) : Prop :=
  ∀ A : BitPPTAdversary K Λ σ,
    ∃ p : Nat → Nat,
      IsPosPoly p ∧
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          successProb (K := K) (Λ := Λ) (σ := σ) S F A n ≤ 1 - (1 : ℝ) / (p n : ℝ)

/--
`δ`-weak OWF 定义（显式间隙函数版本）。

与 `IsWeakOWF` 的区别：
- `IsWeakOWF` 采用“存在正值多项式 `p`，成功率 <= 1 - 1/p(n)`”形式。
- `IsDeltaWeakOWF` 直接给定间隙 `δ(n)`，并要求成功率 <= `1 - δ(n)`。
-/
def IsDeltaWeakOWF (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) (δ : Nat → ℝ) : Prop :=
  (∀ n : Nat, 0 < δ n ∧ δ n ≤ 1) ∧
    ∀ A : BitPPTAdversary K Λ σ,
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          successProb (K := K) (Λ := Λ) (σ := σ) S F A n ≤ 1 - δ n

/--
strong OWF 定义：
任意 PPT 反演器的成功概率关于安全参数是可忽略函数。
-/
def IsStrongOWF (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) : Prop :=
  ∀ A : BitPPTAdversary K Λ σ,
    IsNegligible (fun n => successProb (K := K) (Λ := Λ) (σ := σ) S F A n)

/--
密码学读者友好的符号接口层。

该层不改变任何语义，仅提供更贴近教材的短记号：

- `Inverter`：PPT 反演器。
- `Pr`：反演成功概率。
- `PrFail`：反演失败概率。
- `Weak` / `Strong`：弱/强单向性的短名。
-/
abbrev Inverter : Type (max u v w) :=
  BitPPTAdversary K Λ σ

/-- `Pr S F A n`。 -/
def Pr (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) (A : Inverter (K := K) (Λ := Λ) (σ := σ)) (n : Nat) : ℝ :=
  successProb (K := K) (Λ := Λ) (σ := σ) S F A n

/-- `PrFail S F A n`。 -/
def PrFail (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) (A : Inverter (K := K) (Λ := Λ) (σ := σ)) (n : Nat) : ℝ :=
  failureProb (K := K) (Λ := Λ) (σ := σ) S F A n

/-- 弱单向短记号。 -/
abbrev Weak (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) : Prop :=
  IsWeakOWF (K := K) (Λ := Λ) (σ := σ) S F

/-- 强单向短记号。 -/
abbrev Strong (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) : Prop :=
  IsStrongOWF (K := K) (Λ := Λ) (σ := σ) S F

/-- `Pr` 与 `successProb` 完全等价。 -/
theorem Pr_eq_successProb
    (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) (A : Inverter (K := K) (Λ := Λ) (σ := σ)) (n : Nat) :
    Pr (K := K) (Λ := Λ) (σ := σ) S F A n =
      successProb (K := K) (Λ := Λ) (σ := σ) S F A n :=
  rfl

/-- `PrFail` 与 `failureProb` 完全等价。 -/
theorem PrFail_eq_failureProb
    (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) (A : Inverter (K := K) (Λ := Λ) (σ := σ)) (n : Nat) :
    PrFail (K := K) (Λ := Λ) (σ := σ) S F A n =
      failureProb (K := K) (Λ := Λ) (σ := σ) S F A n :=
  rfl

/-- `Weak` 是 `IsWeakOWF` 的阅读友好别名。 -/
theorem Weak_iff
    (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) :
    Weak (K := K) (Λ := Λ) (σ := σ) S F ↔
      IsWeakOWF (K := K) (Λ := Λ) (σ := σ) S F :=
  Iff.rfl

/-- `Strong` 是 `IsStrongOWF` 的阅读友好别名。 -/
theorem Strong_iff
    (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily) :
    Strong (K := K) (Λ := Λ) (σ := σ) S F ↔
      IsStrongOWF (K := K) (Λ := Λ) (σ := σ) S F :=
  Iff.rfl

end Semantics

end OneWayFunction
