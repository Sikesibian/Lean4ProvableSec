import ProvableSec.Defination.Baisc.TuringMachine.TMCrypto
import Mathlib.Data.Real.Basic

/-!
# 复杂度类接口 / Complexity Class Interface

## 目标 / Goals
- 在现有 TM2/PPT 接口之上提供复杂度类构造。
- Provide complexity-class constructions on top of existing TM2/PPT interfaces.

## 覆盖范围 / Coverage
- `P`：多项式时间确定性判定。
- `NP`：多项式时间可验证（带多项式见证长度界）。
- `coNP`：补语言属于 `NP`。
- `BPP`：概率判定接口（抽象接受概率阈值）。
- `PPT`：多项式时间概率函数族接口。

## 公式化定义 / Formal Definitions

多项式时间界（沿用 `TuringMachine.Crypto.IsPolynomial`）：

$$
\exists C,d\in\mathbb{N},\ \forall n,\ T(n) \le C (n+1)^d.
$$

语言 $L$ 属于 $P$（固定机器宇宙参数下）：

$$
\exists D,\ \forall x,\ D(x)=1 \iff x\in L.
$$

语言 $L$ 属于 $NP$（固定机器宇宙参数下）：

$$
\exists V,\forall x,\ x\in L \iff \exists w,\ |w|\le p(|x|)\land V(x,w)=1.
$$

`BPP` 接口采用标准阈值：

$$
x\in L \Rightarrow \Pr[A(x)=1]\ge 2/3,
\qquad
x\notin L \Rightarrow \Pr[A(x)=1]\le 1/3.
$$
-/

namespace Complexity

open TuringMachine.Crypto

universe u v w

/-- 比特串输入类型。 -/
abbrev Bits : Type := List Bool

/-- 语言类型：比特串集合。 -/
abbrev Language : Type := Set Bits

/-- 从输出串读取判定位（空串默认 `false`）。 -/
def outputBit : Bits → Bool
  | [] => false
  | b :: _ => b

section Deterministic

variable {K : Type u} {Λ : Type v} {σ : Type w}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

/-- 多项式时间确定性判定器接口。 -/
structure PolyTimeDecider where
  adv : BitAdversary K Λ σ
  timeBound : Nat → Nat
  timeBound_poly : IsPolynomial timeBound
  halts_timeBound :
    ∀ n (x : Bits),
      x.length = n →
      (adv.runFor (steps := timeBound n) x []).l = none

namespace PolyTimeDecider

/-- 在时间界处读取输出串（随机币固定为 `[]`）。 -/
def outputAtBound (D : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ)) (x : Bits) : Bits :=
  D.adv.outputAfter (steps := D.timeBound x.length) x []

/-- 在时间界处读取判定位。 -/
def acceptBit (D : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ)) (x : Bits) : Bool :=
  outputBit (D.outputAtBound x)

/-- 判定器在输入 `x` 上接受。 -/
def accepts (D : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ)) (x : Bits) : Prop :=
  D.acceptBit x = true

/-- 判定器在输入 `x` 上拒绝。 -/
def rejects (D : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ)) (x : Bits) : Prop :=
  D.acceptBit x = false

/-- 该判定器正确判定语言 `L`。 -/
def DecidesLanguage (D : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ)) (L : Language) : Prop :=
  ∀ x, D.accepts x ↔ x ∈ L

theorem accepts_or_rejects (D : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ)) (x : Bits) :
    D.accepts x ∨ D.rejects x := by
  unfold accepts rejects acceptBit
  cases outputBit (D.outputAtBound x) <;> simp

end PolyTimeDecider

/-- 固定机器宇宙参数下的 `P`。 -/
def IsInP (L : Language) : Prop :=
  ∃ D : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ), D.DecidesLanguage L

/-- 见证编码接口。 -/
structure PairEncoding where
  encode : Bits → Bits → Bits

/-- 平凡编码：忽略见证。 -/
def trivialPairEncoding : PairEncoding :=
  { encode := fun x _ => x }

/-- `NP` 验证器接口。 -/
structure NPVerifier where
  decider : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ)
  encoding : PairEncoding
  witnessBound : Nat → Nat
  witnessBound_poly : IsPolynomial witnessBound

namespace NPVerifier

/-- 验证器在输入 `x` 和见证 `w` 上接受。 -/
def acceptsWithWitness (V : NPVerifier (K := K) (Λ := Λ) (σ := σ))
    (x w : Bits) : Prop :=
  V.decider.accepts (V.encoding.encode x w)

/-- 验证器 `V` 对语言 `L` 的验证正确性。 -/
def VerifiesLanguage (V : NPVerifier (K := K) (Λ := Λ) (σ := σ)) (L : Language) : Prop :=
  ∀ x,
    x ∈ L ↔
      ∃ w : Bits, w.length ≤ V.witnessBound x.length ∧ V.acceptsWithWitness x w

end NPVerifier

/-- 固定机器宇宙参数下的 `NP`。 -/
def IsInNP (L : Language) : Prop :=
  ∃ V : NPVerifier (K := K) (Λ := Λ) (σ := σ), V.VerifiesLanguage L

/-- 语言补集。 -/
def complement (L : Language) : Language :=
  { x | x ∉ L }

/-- 固定机器宇宙参数下的 `coNP`。 -/
def IsIncoNP (L : Language) : Prop :=
  IsInNP (K := K) (Λ := Λ) (σ := σ) (complement L)

/-- 把 `P` 判定器提升为 `NP` 验证器（忽略见证）。 -/
def pDeciderToNPVerifier
    (D : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ)) :
    NPVerifier (K := K) (Λ := Λ) (σ := σ) where
  decider := D
  encoding := trivialPairEncoding
  witnessBound := fun _ => 0
  witnessBound_poly := by
    refine ⟨0, 0, ?_⟩
    intro n
    simp

theorem pDeciderToNPVerifier_correct
    (D : PolyTimeDecider (K := K) (Λ := Λ) (σ := σ))
    (L : Language)
    (hD : D.DecidesLanguage L) :
    (pDeciderToNPVerifier (K := K) (Λ := Λ) (σ := σ) D).VerifiesLanguage L := by
  intro x
  constructor
  · intro hx
    refine ⟨[], ?_, ?_⟩
    · simp [pDeciderToNPVerifier]
    · have hAcc : D.accepts x := (hD x).2 hx
      simpa [NPVerifier.acceptsWithWitness, pDeciderToNPVerifier, trivialPairEncoding] using hAcc
  · intro hx
    rcases hx with ⟨w, hw, hacc⟩
    have hAccD : D.accepts x := by
      simpa [NPVerifier.acceptsWithWitness, pDeciderToNPVerifier, trivialPairEncoding] using hacc
    exact (hD x).1 hAccD

theorem p_subset_np {L : Language}
    (hP : IsInP (K := K) (Λ := Λ) (σ := σ) L) :
    IsInNP (K := K) (Λ := Λ) (σ := σ) L := by
  rcases hP with ⟨D, hD⟩
  exact ⟨pDeciderToNPVerifier (K := K) (Λ := Λ) (σ := σ) D,
    pDeciderToNPVerifier_correct (K := K) (Λ := Λ) (σ := σ) D L hD⟩

end Deterministic

/-- 机器宇宙参数存在化后的 `P`。 -/
def IsInPAny (L : Language) : Prop :=
  ∃ (K : Type u) (Λ : Type v) (σ : Type w)
    (hK : DecidableEq K) (hΛ : Inhabited Λ) (hσ : Inhabited σ),
      @IsInP K Λ σ hK hΛ hσ L

/-- 机器宇宙参数存在化后的 `NP`。 -/
def IsInNPAny (L : Language) : Prop :=
  ∃ (K : Type u) (Λ : Type v) (σ : Type w)
    (hK : DecidableEq K) (hΛ : Inhabited Λ) (hσ : Inhabited σ),
      @IsInNP K Λ σ hK hΛ hσ L

/-- 机器宇宙参数存在化后的 `coNP`。 -/
def IsIncoNPAny (L : Language) : Prop :=
  ∃ (K : Type u) (Λ : Type v) (σ : Type w)
    (hK : DecidableEq K) (hΛ : Inhabited Λ) (hσ : Inhabited σ),
      @IsIncoNP K Λ σ hK hΛ hσ L

section Randomized

variable {K : Type u} {Λ : Type v} {σ : Type w}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

/-- 概率判定器别名：复用现有 `BitPPTAdversary`。 -/
abbrev PPTDecider : Type (max u v w) :=
  BitPPTAdversary K Λ σ

/-- 在时间界处（给定随机币）读取输出串。 -/
def pptOutputAtBound (A : PPTDecider (K := K) (Λ := Λ) (σ := σ))
    (x r : Bits) : Bits :=
  A.adv.outputAfter (steps := A.timeBound x.length) x r

/-- 在时间界处（给定随机币）读取判定位。 -/
def pptAcceptBitAtBound (A : PPTDecider (K := K) (Λ := Λ) (σ := σ))
    (x r : Bits) : Bool :=
  outputBit (pptOutputAtBound (K := K) (Λ := Λ) (σ := σ) A x r)

/-- 在固定随机币下是否接受。 -/
def pptAcceptsWithCoins (A : PPTDecider (K := K) (Λ := Λ) (σ := σ))
    (x r : Bits) : Prop :=
  pptAcceptBitAtBound (K := K) (Λ := Λ) (σ := σ) A x r = true

/--
`BPP` 见证接口：
- `decider` 提供机器语义
- `acceptProb` 提供接受概率规格
- `completeness/soundness` 提供 `2/3` 与 `1/3` 阈值

说明：
该结构是接口层，`acceptProb` 与机器执行语义的精确连接可在概率模块中继续构造。
-/
structure BPPWitness (L : Language) where
  decider : PPTDecider (K := K) (Λ := Λ) (σ := σ)
  acceptProb : Bits → ℝ
  acceptProb_range : ∀ x, 0 ≤ acceptProb x ∧ acceptProb x ≤ 1
  completeness : ∀ x, x ∈ L → (2 : ℝ) / 3 ≤ acceptProb x
  soundness : ∀ x, x ∉ L → acceptProb x ≤ (1 : ℝ) / 3

/-- 固定机器宇宙参数下的 `BPP` 接口类。 -/
def IsInBPP (L : Language) : Prop :=
  Nonempty (BPPWitness (K := K) (Λ := Λ) (σ := σ) L)

/--
PPT 函数族接口：
- 算法为 `PPTDecider`
- 输出长度有多项式上界
-/
structure PPTFunctionFamily where
  algorithm : PPTDecider (K := K) (Λ := Λ) (σ := σ)
  outLenBound : Nat → Nat
  outLenBound_poly : IsPolynomial outLenBound
  output_len_bound :
    ∀ n (x r : Bits),
      x.length = n →
      r.length = algorithm.coinLength n →
      (algorithm.adv.outputAfter (steps := algorithm.timeBound n) x r).length ≤ outLenBound n

end Randomized

end Complexity
