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

open Complexity
open TuringMachine.Crypto

universe u v w

/-- 比特串短名。 -/
abbrev Bits : Type := Complexity.Bits

section Semantics

variable {K : Type u} {Λ : Type v} {σ : Type w}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

/-- PPT 敌手短名（语义层别名：隐藏图灵机纸带细节）。 -/
abbrev Adversary : Type (max u v w) :=
  PPTDecider (K := K) (Λ := Λ) (σ := σ)

/--
全局语义接口：给出随机带诱导的成功概率。

`successProb A n` 表示：
在安全参数 `n` 下，PPT 敌手 `A` 的成功概率。
-/
structure GlobalSemantics where
  successProb : Adversary (K := K) (Λ := Λ) (σ := σ) → Nat → ℝ
  successProb_range :
    ∀ A n, 0 ≤ successProb A n ∧ successProb A n ≤ 1

/-- 全局语义模型短名。 -/
abbrev Model : Type (max u v w) :=
  GlobalSemantics (K := K) (Λ := Λ) (σ := σ)

/-- 成功概率记号。 -/
def Pr (S : Model (K := K) (Λ := Λ) (σ := σ))
    (A : Adversary (K := K) (Λ := Λ) (σ := σ)) (n : Nat) : ℝ :=
  S.successProb A n

/--
敌手在语义模型 `S` 下、由随机带诱导的成功概率曲线。

`successProfile S A` 是关于安全参数 `n` 的函数，返回 `Pr[S, A](n)`。
-/
def successProfile (S : Model (K := K) (Λ := Λ) (σ := σ))
    (A : Adversary (K := K) (Λ := Λ) (σ := σ)) : Nat → ℝ :=
  fun n => Pr (K := K) (Λ := Λ) (σ := σ) S A n

/-- 成功概率曲线逐点落在区间 `[0, 1]`。 -/
theorem successProfile_range
    (S : Model (K := K) (Λ := Λ) (σ := σ))
    (A : Adversary (K := K) (Λ := Λ) (σ := σ)) :
    ∀ n : Nat,
      0 ≤ successProfile (K := K) (Λ := Λ) (σ := σ) S A n ∧
        successProfile (K := K) (Λ := Λ) (σ := σ) S A n ≤ 1 := by
  intro n
  exact S.successProb_range A n

/-- 失败概率记号。 -/
def PrFail (S : Model (K := K) (Λ := Λ) (σ := σ))
    (A : Adversary (K := K) (Λ := Λ) (σ := σ)) (n : Nat) : ℝ :=
  1 - Pr (K := K) (Λ := Λ) (σ := σ) S A n

/-- 成功概率非负。 -/
theorem Pr_nonneg
    (S : Model (K := K) (Λ := Λ) (σ := σ))
    (A : Adversary (K := K) (Λ := Λ) (σ := σ)) (n : Nat) :
    0 ≤ Pr (K := K) (Λ := Λ) (σ := σ) S A n :=
  (S.successProb_range A n).1

/-- 成功概率至多为 1。 -/
theorem Pr_le_one
    (S : Model (K := K) (Λ := Λ) (σ := σ))
    (A : Adversary (K := K) (Λ := Λ) (σ := σ)) (n : Nat) :
    Pr (K := K) (Λ := Λ) (σ := σ) S A n ≤ 1 :=
  (S.successProb_range A n).2

/-- `PrFail` 的定义展开。 -/
theorem PrFail_eq
    (S : Model (K := K) (Λ := Λ) (σ := σ))
    (A : Adversary (K := K) (Λ := Λ) (σ := σ)) (n : Nat) :
    PrFail (K := K) (Λ := Λ) (σ := σ) S A n =
      1 - Pr (K := K) (Λ := Λ) (σ := σ) S A n :=
  rfl

end Semantics

/--
将机器参数与类型类实例打包，避免在使用层反复书写 `(K := ...) (Λ := ...) (σ := ...)`。
-/
structure Context where
  K : Type u
  Λ : Type v
  σ : Type w
  decEqK : DecidableEq K
  inhΛ : Inhabited Λ
  inhσ : Inhabited σ

instance (C : Context) : DecidableEq C.K := C.decEqK
instance (C : Context) : Inhabited C.Λ := C.inhΛ
instance (C : Context) : Inhabited C.σ := C.inhσ

namespace Context

variable (C : Context)

/-- 上下文 `C` 下的全局语义模型。 -/
abbrev Model :=
  CryptoNotation.Model (K := C.K) (Λ := C.Λ) (σ := C.σ)

/-- 上下文 `C` 下的 PPT 敌手。 -/
abbrev Adversary :=
  CryptoNotation.Adversary (K := C.K) (Λ := C.Λ) (σ := C.σ)

/-- 上下文 `C` 下的成功概率记号。 -/
def Pr (M : Model C) (A : Adversary C) (n : Nat) : ℝ :=
  CryptoNotation.Pr (K := C.K) (Λ := C.Λ) (σ := C.σ) M A n

/-- 上下文 `C` 下的成功概率曲线（按安全参数）。 -/
def successProfile (M : Model C) (A : Adversary C) : Nat → ℝ :=
  fun n => Pr C M A n

/-- 上下文版本：成功概率曲线逐点落在 `[0, 1]`。 -/
theorem successProfile_range
    (M : Model C) (A : Adversary C) :
    ∀ n : Nat, 0 ≤ successProfile C M A n ∧ successProfile C M A n ≤ 1 := by
  intro n
  exact CryptoNotation.successProfile_range (K := C.K) (Λ := C.Λ) (σ := C.σ) M A n

/-- 上下文 `C` 下的失败概率记号。 -/
def PrFail (M : Model C) (A : Adversary C) (n : Nat) : ℝ :=
  CryptoNotation.PrFail (K := C.K) (Λ := C.Λ) (σ := C.σ) M A n

/-- 上下文版本：`PrFail = 1 - Pr`。 -/
theorem PrFail_eq
    (M : Model C) (A : Adversary C) (n : Nat) :
    PrFail C M A n = 1 - Pr C M A n :=
  rfl

/-- 上下文版本：成功概率非负。 -/
theorem Pr_nonneg
    (M : Model C) (A : Adversary C) (n : Nat) :
    0 ≤ Pr C M A n :=
  CryptoNotation.Pr_nonneg (K := C.K) (Λ := C.Λ) (σ := C.σ) M A n

/-- 上下文版本：成功概率至多为 1。 -/
theorem Pr_le_one
    (M : Model C) (A : Adversary C) (n : Nat) :
    Pr C M A n ≤ 1 :=
  CryptoNotation.Pr_le_one (K := C.K) (Λ := C.Λ) (σ := C.σ) M A n

namespace Model

variable {C : Context}

/-- 点号风格：`M.Pr A n`。 -/
def Pr (M : Context.Model C) (A : Context.Adversary C) (n : Nat) : ℝ :=
  Context.Pr C M A n

/-- 点号风格：`M.PrFail A n`。 -/
def PrFail (M : Context.Model C) (A : Context.Adversary C) (n : Nat) : ℝ :=
  Context.PrFail C M A n

/-- 点号风格：`M.successProfile A`。 -/
def successProfile (M : Context.Model C) (A : Context.Adversary C) : Nat → ℝ :=
  Context.successProfile C M A

/-- 点号风格：`M.PrFail_eq A n`。 -/
theorem PrFail_eq (M : Context.Model C) (A : Context.Adversary C) (n : Nat) :
    M.PrFail A n = 1 - M.Pr A n :=
  Context.PrFail_eq C M A n

/-- 点号风格：`M.Pr_nonneg A n`。 -/
theorem Pr_nonneg (M : Context.Model C) (A : Context.Adversary C) (n : Nat) :
    0 ≤ M.Pr A n :=
  Context.Pr_nonneg C M A n

/-- 点号风格：`M.Pr_le_one A n`。 -/
theorem Pr_le_one (M : Context.Model C) (A : Context.Adversary C) (n : Nat) :
    M.Pr A n ≤ 1 :=
  Context.Pr_le_one C M A n

/-- 点号风格：`M.successProfile_range A n`。 -/
theorem successProfile_range
    (M : Context.Model C) (A : Context.Adversary C) (n : Nat) :
    0 ≤ M.successProfile A n ∧ M.successProfile A n ≤ 1 :=
  Context.successProfile_range C M A n

end Model

end Context

section OWFNotation

variable {K : Type u} {Λ : Type v} {σ : Type w}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

/--
`f : {0,1}* → {0,1}*` 的 OWF 记号版本。

说明：
- `eval` 是单函数本体。
- `timeBound`/`outLenBound` 提供多项式时间与输出长度界。
- `lengthPreserving` 对齐 OWF 常见设定 `|f(x)| = |x|`。
-/
structure OWFFunction where
  eval : Bits → Bits
  timeBound : Nat → Nat
  timeBound_poly : IsPolynomial timeBound
  outLenBound : Nat → Nat
  outLenBound_poly : IsPolynomial outLenBound
  outLen_spec : ∀ x : Bits, (eval x).length ≤ outLenBound x.length
  lengthPreserving : ∀ x : Bits, (eval x).length = x.length

namespace OWFFunction

/-- 把单函数 `f` 视为按 `n` 索引的函数族。 -/
def toFamily (f : OWFFunction) : OneWayFunction.OWFFamily where
  eval := fun _ x => f.eval x
  timeBound := f.timeBound
  timeBound_poly := f.timeBound_poly
  outLenBound := f.outLenBound
  outLenBound_poly := f.outLenBound_poly
  outLen_spec := by
    intro n x hx
    simpa [hx] using f.outLen_spec x
  lengthPreserving := by
    intro n x hx
    simpa [hx] using f.lengthPreserving x

end OWFFunction

/-- OWF 语义模型（来自基础定义层）。 -/
abbrev OWFModel : Type (max u v w) :=
  OneWayFunction.OWFSemantics (K := K) (Λ := Λ) (σ := σ)

/-- OWF 反演器（PPT）。 -/
abbrev OWFAdversary : Type (max u v w) :=
  PPTDecider (K := K) (Λ := Λ) (σ := σ)

/-- 单函数版本成功概率：`Pr_f(A, n)`。 -/
def PrFn (S : OWFModel (K := K) (Λ := Λ) (σ := σ))
    (f : OWFFunction) (A : OWFAdversary (K := K) (Λ := Λ) (σ := σ)) (n : Nat) : ℝ :=
  OneWayFunction.Pr (K := K) (Λ := Λ) (σ := σ) S f.toFamily A n

/-- 单函数版本失败概率。 -/
def PrFailFn (S : OWFModel (K := K) (Λ := Λ) (σ := σ))
    (f : OWFFunction) (A : OWFAdversary (K := K) (Λ := Λ) (σ := σ)) (n : Nat) : ℝ :=
  OneWayFunction.PrFail (K := K) (Λ := Λ) (σ := σ) S f.toFamily A n

/--
定义 1（弱单向函数，单函数版）：
`f : {0,1}* → {0,1}*` 在语义 `S` 下是弱单向。
-/
def IsWeakOWFFunction (S : OWFModel (K := K) (Λ := Λ) (σ := σ))
    (f : OWFFunction) : Prop :=
  OneWayFunction.IsWeakOWF (K := K) (Λ := Λ) (σ := σ) S f.toFamily

/--
定义 2（强单向函数，单函数版）：
对任意 PPT 反演器，成功概率是可忽略函数。
-/
def IsStrongOWFFunction (S : OWFModel (K := K) (Λ := Λ) (σ := σ))
    (f : OWFFunction) : Prop :=
  OneWayFunction.IsStrongOWF (K := K) (Λ := Λ) (σ := σ) S f.toFamily

/-- 单函数版弱单向定义展开。 -/
theorem IsWeakOWFFunction_iff
    (S : OWFModel (K := K) (Λ := Λ) (σ := σ))
    (f : OWFFunction) :
    IsWeakOWFFunction (K := K) (Λ := Λ) (σ := σ) S f ↔
      ∀ A : OWFAdversary (K := K) (Λ := Λ) (σ := σ),
        ∃ p : Nat → Nat,
          OneWayFunction.IsPosPoly p ∧
          ∃ n0 : Nat,
            ∀ n : Nat, n ≥ n0 →
              OneWayFunction.successProb (K := K) (Λ := Λ) (σ := σ) S f.toFamily A n ≤
                1 - (1 : ℝ) / (p n : ℝ) :=
  Iff.rfl

/-- 单函数版强单向定义展开。 -/
theorem IsStrongOWFFunction_iff
    (S : OWFModel (K := K) (Λ := Λ) (σ := σ))
    (f : OWFFunction) :
    IsStrongOWFFunction (K := K) (Λ := Λ) (σ := σ) S f ↔
      ∀ A : OWFAdversary (K := K) (Λ := Λ) (σ := σ),
        OneWayFunction.IsNegligible
          (fun n => OneWayFunction.successProb (K := K) (Λ := Λ) (σ := σ) S f.toFamily A n) :=
  Iff.rfl

/-- 弱单向函数打包对象。 -/
structure WeakOWF (S : OWFModel (K := K) (Λ := Λ) (σ := σ)) where
  f : OWFFunction
  isWeak : IsWeakOWFFunction (K := K) (Λ := Λ) (σ := σ) S f

/-- 强单向函数打包对象。 -/
structure StrongOWF (S : OWFModel (K := K) (Λ := Λ) (σ := σ)) where
  f : OWFFunction
  isStrong : IsStrongOWFFunction (K := K) (Λ := Λ) (σ := σ) S f

/-- 与文献中的记号对齐：`wOWF`。 -/
abbrev wOWF (S : OWFModel (K := K) (Λ := Λ) (σ := σ)) :=
  WeakOWF (K := K) (Λ := Λ) (σ := σ) S

/-- 与文献中的记号对齐：`sOWF`。 -/
abbrev sOWF (S : OWFModel (K := K) (Λ := Λ) (σ := σ)) :=
  StrongOWF (K := K) (Λ := Λ) (σ := σ) S

/--
`WeakToStrongTransform`：弱到强的提升接口。

说明：
- 这里不固定具体构造，也不在本文件陈述 Yao 定理。
- `correct` 可以由其他文件中的定理（例如 Yao 定理）来实例化。
-/
structure WeakToStrongTransform (S : OWFModel (K := K) (Λ := Λ) (σ := σ)) where
  map : OWFFunction → OWFFunction
  correct :
    ∀ f : OWFFunction,
      IsWeakOWFFunction (K := K) (Λ := Λ) (σ := σ) S f →
      IsStrongOWFFunction (K := K) (Λ := Λ) (σ := σ) S (map f)

namespace WeakOWF

/--
`to_sOWF`：在给定提升接口下，把一个 `wOWF` 构造成 `sOWF`。

构造正确性由 `WeakToStrongTransform.correct` 提供。
-/
def to_sOWF
    {S : OWFModel (K := K) (Λ := Λ) (σ := σ)}
    (w : WeakOWF (K := K) (Λ := Λ) (σ := σ) S)
    (T : WeakToStrongTransform (K := K) (Λ := Λ) (σ := σ) S) :
    StrongOWF (K := K) (Λ := Λ) (σ := σ) S where
  f := T.map w.f
  isStrong := T.correct w.f w.isWeak

/-- `to_sOWF` 输出对象满足强单向性。 -/
theorem to_sOWF_isStrong
    {S : OWFModel (K := K) (Λ := Λ) (σ := σ)}
    (w : WeakOWF (K := K) (Λ := Λ) (σ := σ) S)
    (T : WeakToStrongTransform (K := K) (Λ := Λ) (σ := σ) S) :
    IsStrongOWFFunction (K := K) (Λ := Λ) (σ := σ) S
      (to_sOWF (K := K) (Λ := Λ) (σ := σ) w T).f :=
  (to_sOWF (K := K) (Λ := Λ) (σ := σ) w T).isStrong

end WeakOWF

end OWFNotation

namespace Context
namespace OWF

variable (C : Context)

/-- 上下文 `C` 下的 OWF 语义模型。 -/
abbrev Model :=
  OneWayFunction.OWFSemantics (K := C.K) (Λ := C.Λ) (σ := C.σ)

/-- 上下文 `C` 下的单函数 OWF 对象。 -/
abbrev OWFunction :=
  CryptoNotation.OWFFunction

/-- 上下文 `C` 下的 OWF 反演器（PPT）。 -/
abbrev Adversary :=
  CryptoNotation.OWFAdversary (K := C.K) (Λ := C.Λ) (σ := C.σ)

/-- 上下文 `C` 下的单函数 OWF 成功概率。 -/
def Pr (M : Model C) (f : OWFunction) (A : Adversary C) (n : Nat) : ℝ :=
  CryptoNotation.PrFn (K := C.K) (Λ := C.Λ) (σ := C.σ) M f A n

/-- 上下文 `C` 下的单函数 OWF 失败概率。 -/
def PrFail (M : Model C) (f : OWFunction) (A : Adversary C) (n : Nat) : ℝ :=
  CryptoNotation.PrFailFn (K := C.K) (Λ := C.Λ) (σ := C.σ) M f A n

/-- 上下文 `C` 下的单函数 OWF 成功概率曲线（按安全参数）。 -/
def successProfile (M : Model C) (f : OWFunction) (A : Adversary C) : Nat → ℝ :=
  fun n => Pr C M f A n

/-- 上下文版本：`PrFail = 1 - Pr`（单函数 OWF）。 -/
theorem PrFail_eq
    (M : Model C) (f : OWFunction) (A : Adversary C) (n : Nat) :
    PrFail C M f A n = 1 - Pr C M f A n :=
  rfl

/-- 上下文版本：单函数 OWF 成功概率非负。 -/
theorem Pr_nonneg
    (M : Model C) (f : OWFunction) (A : Adversary C) (n : Nat) :
    0 ≤ Pr C M f A n :=
  (M.inversionSuccessProb_range f.toFamily.eval A n).1

/-- 上下文版本：单函数 OWF 成功概率至多为 1。 -/
theorem Pr_le_one
    (M : Model C) (f : OWFunction) (A : Adversary C) (n : Nat) :
    Pr C M f A n ≤ 1 :=
  (M.inversionSuccessProb_range f.toFamily.eval A n).2

/-- 上下文版本：单函数 OWF 成功概率曲线逐点落在 `[0, 1]`。 -/
theorem successProfile_range
    (M : Model C) (f : OWFunction) (A : Adversary C) :
    ∀ n : Nat, 0 ≤ successProfile C M f A n ∧ successProfile C M f A n ≤ 1 := by
  intro n
  exact ⟨Pr_nonneg C M f A n, Pr_le_one C M f A n⟩

namespace Model

variable {C : Context}

/-- 点号风格：`M.Pr f A n`。 -/
def Pr (M : Context.OWF.Model C)
  (f : Context.OWF.OWFunction) (A : Context.OWF.Adversary C) (n : Nat) : ℝ :=
  Context.OWF.Pr C M f A n

/-- 点号风格：`M.PrFail f A n`。 -/
def PrFail (M : Context.OWF.Model C)
  (f : Context.OWF.OWFunction) (A : Context.OWF.Adversary C) (n : Nat) : ℝ :=
  Context.OWF.PrFail C M f A n

/-- 点号风格：`M.successProfile f A`。 -/
def successProfile (M : Context.OWF.Model C)
  (f : Context.OWF.OWFunction) (A : Context.OWF.Adversary C) : Nat → ℝ :=
  Context.OWF.successProfile C M f A

/-- 点号风格：`M.PrFail_eq f A n`。 -/
theorem PrFail_eq (M : Context.OWF.Model C)
  (f : Context.OWF.OWFunction) (A : Context.OWF.Adversary C) (n : Nat) :
    M.PrFail f A n = 1 - M.Pr f A n :=
  Context.OWF.PrFail_eq C M f A n

/-- 点号风格：`M.Pr_nonneg f A n`。 -/
theorem Pr_nonneg (M : Context.OWF.Model C)
  (f : Context.OWF.OWFunction) (A : Context.OWF.Adversary C) (n : Nat) :
    0 ≤ M.Pr f A n :=
  Context.OWF.Pr_nonneg C M f A n

/-- 点号风格：`M.Pr_le_one f A n`。 -/
theorem Pr_le_one (M : Context.OWF.Model C)
  (f : Context.OWF.OWFunction) (A : Context.OWF.Adversary C) (n : Nat) :
    M.Pr f A n ≤ 1 :=
  Context.OWF.Pr_le_one C M f A n

/-- 点号风格：`M.successProfile_range f A n`。 -/
theorem successProfile_range (M : Context.OWF.Model C)
  (f : Context.OWF.OWFunction) (A : Context.OWF.Adversary C) (n : Nat) :
    0 ≤ M.successProfile f A n ∧ M.successProfile f A n ≤ 1 :=
  Context.OWF.successProfile_range C M f A n

end Model

/-- 上下文 `C` 下的弱单向函数定义。 -/
def IsWeak (M : Model C) (f : OWFunction) : Prop :=
  CryptoNotation.IsWeakOWFFunction (K := C.K) (Λ := C.Λ) (σ := C.σ) M f

/-- 上下文 `C` 下的强单向函数定义。 -/
def IsStrong (M : Model C) (f : OWFunction) : Prop :=
  CryptoNotation.IsStrongOWFFunction (K := C.K) (Λ := C.Λ) (σ := C.σ) M f

/-- 上下文 `C` 下的弱单向函数打包对象。 -/
abbrev Weak (M : Model C) : Type _ :=
  CryptoNotation.WeakOWF (K := C.K) (Λ := C.Λ) (σ := C.σ) M

/-- 上下文 `C` 下的强单向函数打包对象。 -/
abbrev Strong (M : Model C) : Type _ :=
  CryptoNotation.StrongOWF (K := C.K) (Λ := C.Λ) (σ := C.σ) M

/-- 上下文 `C` 下的弱到强提升接口。 -/
abbrev WeakToStrong (M : Model C) : Type _ :=
  CryptoNotation.WeakToStrongTransform (K := C.K) (Λ := C.Λ) (σ := C.σ) M

/-- 上下文版本 `wOWF -> sOWF` 构造。 -/
def to_sOWF
    (M : Model C)
    (w : Weak C M)
    (T : WeakToStrong C M) :
    Strong C M :=
  CryptoNotation.WeakOWF.to_sOWF (K := C.K) (Λ := C.Λ) (σ := C.σ) w T

/-- 上下文版本：`to_sOWF` 输出对象满足强单向性。 -/
theorem to_sOWF_isStrong
    (M : Model C)
    (w : Weak C M)
    (T : WeakToStrong C M) :
    IsStrong C M (to_sOWF C M w T).f :=
  (to_sOWF C M w T).isStrong

end OWF
end Context

/-!
数学化记号层（scoped notation）。

使用方式：
- 在使用文件里加入 `open scoped CryptoNotation`。
- 全局语义层：`Pr[M](A, n)`、`PrFail[M](A, n)`。
- OWF 单函数层：`Pr[M|f](A, n)`、`PrFail[M|f](A, n)`。
-/

/-- 数学化记号：全局语义成功概率。 -/
scoped notation "Pr[" M "](" A "," n ")" =>
  Context.Model.Pr M A n

/-- 数学化记号：全局语义失败概率。 -/
scoped notation "PrFail[" M "](" A "," n ")" =>
  Context.Model.PrFail M A n

/-- 数学化记号：OWF 单函数成功概率。 -/
scoped notation "Pr[" M "|" f "](" A "," n ")" =>
  Context.OWF.Model.Pr M f A n

/-- 数学化记号：OWF 单函数失败概率。 -/
scoped notation "PrFail[" M "|" f "](" A "," n ")" =>
  Context.OWF.Model.PrFail M f A n

end CryptoNotation
end ProvableSec
