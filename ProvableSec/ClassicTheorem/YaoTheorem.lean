import ProvableSec.Defination.CryptoNotation
import Mathlib.Tactic

/-!
# Yao Theorem Interface Layer

This module introduces three standard statement forms used in Yao-style
weak-to-strong OWF discussions, and proves the implication chain:

1. same-family statement -> transform statement
2. transform statement -> existential statement

The actual cryptographic construction can be added later by instantiating
`weak_to_strong_transform` with a concrete transform.
-/

namespace ProvableSec
namespace CryptoNotation
namespace Context
namespace Yao

variable (C : Context)

/-- OWF model in context `C`. -/
abbrev Model := Context.OWF.Model C

/-- OWF family type in context `C`. -/
abbrev Family := Context.OWF.OWFunction

/-- Weak OWF predicate in context `C`. -/
abbrev WeakOWF (M : Model C) (F : Family) : Prop :=
  Context.OWF.IsWeak C M F

/-- Strong OWF predicate in context `C`. -/
abbrev StrongOWF (M : Model C) (F : Family) : Prop :=
  Context.OWF.IsStrong C M F

/-- Yao statement form 1: same-family weak-to-strong. -/
def weak_to_strong_same_family (M : Model C) : Prop :=
  ∀ F : Family, WeakOWF C M F → StrongOWF C M F

/-- Yao statement form 2: existence of a transform `T`. -/
def weak_to_strong_transform (M : Model C) : Prop :=
  ∃ T : Family → Family,
    ∀ F : Family, WeakOWF C M F → StrongOWF C M (T F)

/-- Yao statement form 3: weak existence implies strong existence. -/
def weak_to_strong_existential (M : Model C) : Prop :=
  (∃ F : Family, WeakOWF C M F) →
    ∃ G : Family, StrongOWF C M G

/-- A textbook-style packaged hypothesis for a fixed transform. -/
structure TextbookYaoHypothesis (M : Model C) where
  lift : Family → Family
  sound : ∀ F : Family, WeakOWF C M F → StrongOWF C M (lift F)

/-- same-family implies transform (choose identity transform). -/
theorem same_family_implies_transform
    (M : Model C)
    (h : weak_to_strong_same_family C M) :
    weak_to_strong_transform C M := by
  refine ⟨fun F => F, ?_⟩
  intro F hF
  exact h F hF

/-- transform implies existential statement. -/
theorem transform_implies_existential
    (M : Model C)
    (h : weak_to_strong_transform C M) :
    weak_to_strong_existential C M := by
  intro hWeak
  rcases h with ⟨T, hT⟩
  rcases hWeak with ⟨F, hF⟩
  exact ⟨T F, hT F hF⟩

/-- same-family implies existential statement. -/
theorem same_family_implies_existential
    (M : Model C)
    (h : weak_to_strong_same_family C M) :
    weak_to_strong_existential C M :=
  transform_implies_existential (C := C) (M := M)
    (same_family_implies_transform (C := C) (M := M) h)

/-- A textbook packaged hypothesis yields the transform statement. -/
theorem textbook_to_transform
    (M : Model C)
    (H : TextbookYaoHypothesis C M) :
    weak_to_strong_transform C M :=
  ⟨H.lift, H.sound⟩

/-- Pointwise weak-to-strong consequence from textbook packaged hypothesis. -/
theorem textbook_yao_of_hyp
    (M : Model C)
    (H : TextbookYaoHypothesis C M)
    (F : Family) :
    WeakOWF C M F → StrongOWF C M (H.lift F) :=
  H.sound F

/-- A textbook packaged hypothesis also yields existential implication. -/
theorem textbook_implies_existential
    (M : Model C)
    (H : TextbookYaoHypothesis C M) :
    weak_to_strong_existential C M :=
  transform_implies_existential (C := C) (M := M)
    (textbook_to_transform (C := C) (M := M) H)

/-- Bridge from existing weak-to-strong interface to Yao transform statement. -/
theorem interface_to_transform
    (M : Model C)
    (T : Context.OWF.WeakToStrong C M) :
    weak_to_strong_transform C M :=
  ⟨T.map, T.correct⟩

/-- Bridge from existing weak-to-strong interface to Yao existential statement. -/
theorem interface_to_existential
    (M : Model C)
    (T : Context.OWF.WeakToStrong C M) :
    weak_to_strong_existential C M :=
  transform_implies_existential (C := C) (M := M)
    (interface_to_transform (C := C) (M := M) T)

/-!
## Phase 2: Reduction Framework (definition-first)

This section adds *definitions* that will host the real Yao proof data.
No theorem statement is disguised as `def`.
-/

/--
A concrete Yao transform candidate.

- `lift`: maps a weak candidate family to a stronger candidate family.
- `reduceAdv`: reduction map from a breaker of `lift F` to a breaker of `F`.
-/
structure ReductionSpec (M : Model C) where
  lift : Family → Family
  reduceAdv : Family → Context.OWF.Adversary C → Context.OWF.Adversary C

/-- Family-level negation wrapper: `F` is not weak under `M`. -/
def FailsWeak (M : Model C) (F : Family) : Prop :=
  ¬ WeakOWF C M F

/-- Family-level negation wrapper: `F` is not strong under `M`. -/
def FailsStrong (M : Model C) (F : Family) : Prop :=
  ¬ StrongOWF C M F

/--
Core contrapositive reduction statement used in many Yao proofs.

If the lifted family is not strong, then the original family is not weak.
-/
def ReductionCorrect (M : Model C) (R : ReductionSpec C M) : Prop :=
  ∀ F : Family, FailsStrong C M (R.lift F) → FailsWeak C M F

/--
Pointwise soundness form for a fixed `lift`.

This is the direct textbook target: `Weak F -> Strong (lift F)`.
-/
def LiftSound (M : Model C) (R : ReductionSpec C M) : Prop :=
  ∀ F : Family, WeakOWF C M F → StrongOWF C M (R.lift F)

/--
Proof obligations roadmap (definitions only).

TODO fields intentionally remain abstract for now:
- `quantitativeReduction`: should become an explicit success-probability inequality.
- `amplificationBound`: should become an explicit amplification / tail bound statement.
-/
structure QuantitativeObligations (M : Model C) (R : ReductionSpec C M) where
  quantitativeReduction : Prop
  amplificationBound : Prop

/--
Full Yao proof package in current project phase.

`coreReduction` is already meaningful and used to derive transform/existential results.
`quantitative` keeps placeholders for later probability-level formalization.
-/
structure ProofPlan (M : Model C) where
  spec : ReductionSpec C M
  coreReduction : ReductionCorrect C M spec
  quantitative : QuantitativeObligations C M spec

/-- Convert core contrapositive reduction to pointwise lift soundness. -/
theorem reductionCorrect_implies_liftSound
    (M : Model C)
    (R : ReductionSpec C M)
    (hRed : ReductionCorrect C M R) :
    LiftSound C M R := by
  intro F hWeak
  by_contra hNotStrong
  exact (hRed F hNotStrong) hWeak

/-- Build textbook packaged hypothesis from reduction correctness. -/
def toTextbookHypothesis
    (M : Model C)
    (R : ReductionSpec C M)
    (hRed : ReductionCorrect C M R) :
    TextbookYaoHypothesis C M where
  lift := R.lift
  sound := reductionCorrect_implies_liftSound (C := C) (M := M) (R := R) hRed

/-- Core reduction correctness yields the transform statement. -/
theorem reductionCorrect_implies_transform
    (M : Model C)
    (R : ReductionSpec C M)
    (hRed : ReductionCorrect C M R) :
    weak_to_strong_transform C M :=
  textbook_to_transform (C := C) (M := M)
    (toTextbookHypothesis (C := C) (M := M) (R := R) hRed)

/-- Core reduction correctness yields the existential statement. -/
theorem reductionCorrect_implies_existential
    (M : Model C)
    (R : ReductionSpec C M)
    (hRed : ReductionCorrect C M R) :
    weak_to_strong_existential C M :=
  transform_implies_existential (C := C) (M := M)
    (reductionCorrect_implies_transform (C := C) (M := M) (R := R) hRed)

/-- A complete proof plan already implies transform at the current abstraction level. -/
theorem plan_implies_transform
    (M : Model C)
    (P : ProofPlan C M) :
    weak_to_strong_transform C M :=
  reductionCorrect_implies_transform (C := C) (M := M) (R := P.spec) P.coreReduction

/-- A complete proof plan also implies existential statement. -/
theorem plan_implies_existential
    (M : Model C)
    (P : ProofPlan C M) :
    weak_to_strong_existential C M :=
  reductionCorrect_implies_existential (C := C) (M := M) (R := P.spec) P.coreReduction

end Yao
end Context
end CryptoNotation
end ProvableSec

namespace OneWayFunction

universe u v w

section ConcreteYaoTheorem

variable {K : Type u} {Λ : Type v} {σ : Type w}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

/-!
### Standard-proof scaffolding (Good sets / Claim 1.5 / embedding)

These are *definitions* matching the textbook proof structure.
The proof obligations are kept explicit; theorem proofs can be completed later.
-/

/-- 抽象“集合密度”接口（相对 `U_n` 的密度）。 -/
structure DensityModel where
  density : Nat → Set Bits → ℝ
  density_range : ∀ n G, 0 ≤ density n G ∧ density n G ≤ 1

/--
直积反演敌手的成功率剖面（按标准证明所需最小接口抽象）。

- `alpha n`：敌手在参数 `n` 上反演直积函数的总体成功率下界。
- `condSuccess n i xi`：固定第 `i` 坐标输入为 `xi` 时，
  对其余坐标随机化后的条件成功率。
-/
structure ProductAttackProfile (m : Nat → Nat) where
  alpha : Nat → ℝ
  alpha_nonneg : ∀ n : Nat, 0 ≤ alpha n
  alpha_nonnegligible : ¬ IsNegligible alpha
  condSuccess : (n : Nat) → Fin (m n) → Bits → ℝ
  condSuccess_range :
    ∀ (n : Nat) (i : Fin (m n)) (xi : Bits),
      0 ≤ condSuccess n i xi ∧ condSuccess n i xi ≤ 1

/-- 标准证明中的好集合 `G_i`。 -/
def GoodSet {m : Nat → Nat}
    (A : ProductAttackProfile m) (n : Nat) (i : Fin (m n)) : Set Bits :=
  { xi : Bits | A.condSuccess n i xi ≥ A.alpha n / (2 * (m n : ℝ)) }

/-- 好集合成员条件的定义展开。 -/
theorem mem_GoodSet_iff {m : Nat → Nat}
    (A : ProductAttackProfile m) (n : Nat) (i : Fin (m n)) (xi : Bits) :
    xi ∈ GoodSet A n i ↔
      A.condSuccess n i xi ≥ A.alpha n / (2 * (m n : ℝ)) :=
  Iff.rfl

/-- 由定义直接得到：`x ∈ G_i` 时单轮成功率下界成立。 -/
theorem singleRound_lb_of_memGoodSet {m : Nat → Nat}
    (A : ProductAttackProfile m) (n : Nat) (i : Fin (m n)) (xi : Bits)
    (hMem : xi ∈ GoodSet A n i) :
    A.condSuccess n i xi ≥ A.alpha n / (2 * (m n : ℝ)) :=
  hMem

/-- 固定长度 `n` 的比特向量类型。 -/
abbrev BitVec (n : Nat) : Type := Fin n → Bool

/-- 从长度 `n` 的比特向量还原为 `Bits` 列表。 -/
def bitVecToBits {n : Nat} (x : BitVec n) : Bits :=
  List.ofFn x

/-- 有限计数：长度为 `n` 的比特向量里，满足谓词 `P` 的元素个数。 -/
noncomputable def countBitVec
    (n : Nat)
    (P : BitVec n → Prop) : Nat := by
  classical
  exact (Finset.univ.filter P).card

/-- 计数密度：`count / 2^n`。 -/
noncomputable def densityByCounting
    (n : Nat)
    (G : Set Bits) : ℝ := by
  classical
  exact
    (countBitVec n (fun x : BitVec n => bitVecToBits x ∈ G) : ℝ) /
      ((2 : ℝ) ^ n)

/-- 计数密度的值域约束：始终落在 `[0,1]`。 -/
theorem densityByCounting_range
    (n : Nat)
    (G : Set Bits) :
    0 ≤ densityByCounting n G ∧ densityByCounting n G ≤ 1 := by
  classical
  let s : Finset (BitVec n) :=
    Finset.univ.filter (fun x : BitVec n => bitVecToBits x ∈ G)
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hs_nonneg : (0 : ℝ) ≤ s.card := by
    exact_mod_cast Nat.zero_le s.card
  have hs_le_nat : s.card ≤ 2 ^ n := by
    have hs_le_univ : s.card ≤ (Finset.univ : Finset (BitVec n)).card :=
      by
        simpa [s] using
          (Finset.card_filter_le
            (s := (Finset.univ : Finset (BitVec n)))
            (p := fun x : BitVec n => bitVecToBits x ∈ G))
    simpa [BitVec] using hs_le_univ
  have hs_le_real : (s.card : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hs_le_nat
  constructor
  ·
    simpa [densityByCounting, countBitVec, s] using
      (div_nonneg hs_nonneg (le_of_lt hpow_pos))
  ·
    have hDivLeOne : (s.card : ℝ) / ((2 : ℝ) ^ n) ≤ 1 := by
      exact (div_le_iff₀ hpow_pos).2 (by simpa using hs_le_real)
    simpa [densityByCounting, countBitVec, s] using hDivLeOne

/-- 把计数密度打包成当前文件使用的 `DensityModel`。 -/
noncomputable def countingDensityModel : DensityModel where
  density := densityByCounting
  density_range := densityByCounting_range

/-- `GoodSet` 的计数密度记号。 -/
noncomputable def goodSetDensityByCounting
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (n : Nat)
    (i : Fin (m n)) : ℝ :=
  densityByCounting n (GoodSet A n i)

/-- 高密度好坐标命题：存在某坐标的好集合密度至少 `1 - δ/2`。 -/
def DenseGoodCoordinateStatement
    (D : DensityModel)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m) : Prop :=
  ∀ n : Nat, ∃ i : Fin (m n), D.density n (GoodSet A n i) ≥ 1 - δ n / 2

/-- 经过 `t(n)` 轮后的理论失败上界模板。 -/
noncomputable def FailureUpperBound
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (t : Nat → Nat) : Nat → ℝ :=
  fun n => (1 - A.alpha n / (2 * (m n : ℝ))) ^ (t n)

/-- 归约敌手成功率超过弱单向阈值 `1 - δ(n)` 的模板命题。 -/
def ReductionBeatsDelta
    (δ : Nat → ℝ)
    (succ : Nat → ℝ) : Prop :=
  ∃ n0 : Nat,
    ∀ n : Nat, n ≥ n0 → succ n > 1 - δ n

/--
抽象谓词：`G` 是 `F` 的 `m(n)`-次直积。

当前阶段作为接口占位，后续可替换为具体的分块编码/解码语义。
-/
def IsDirectProductWithArity
  (_F _G : OWFFamily)
  (_m : Nat → Nat) : Prop :=
  True

/--
Yao 直积构造数据：给定基函数族 `F`，输出被提升后的函数族 `lifted`。
-/
structure YaoConstruction (F : OWFFamily) where
  lifted : OWFFamily

/--
Yao 结论命题：若 `F` 弱单向，则构造后的 `C.lifted` 强单向。
-/
def YaoStrongnessGoal
    (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily)
    (C : YaoConstruction F)
  (_hWeak : IsWeakOWF (K := K) (Λ := Λ) (σ := σ) S F) :
    Prop :=
  IsStrongOWF (K := K) (Λ := Λ) (σ := σ) S C.lifted

/-!
## Section 2 Framework: Contradiction + Good Sets + Reduction

下面给出与你文字证明一一对应的 Lean 骨架。
目前“反证链条 + 关键不等式拼接”已落地；
剩余难点主要体现在概率语义与分布等价仍通过接口假设注入。
-/

/-- 高密度好坐标的“最终形式”（eventually 版本）。 -/
def EventuallyDenseGoodCoordinate
    (D : DensityModel)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m) : Prop :=
  ∃ n0 : Nat,
    ∀ n : Nat, n ≥ n0 →
      ∃ i : Fin (m n), D.density n (GoodSet A n i) ≥ 1 - δ n / 2

/-- “高密度好坐标”命题在计数模型下的展开形式。 -/
theorem denseGoodCoordinate_counting_form
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m) :
    DenseGoodCoordinateStatement countingDensityModel δ A ↔
      ∀ n : Nat, ∃ i : Fin (m n),
        goodSetDensityByCounting A n i ≥ 1 - δ n / 2 := by
  rfl

/-- eventually 版“高密度好坐标”命题在计数模型下的展开形式。 -/
theorem eventuallyDenseGoodCoordinate_counting_form
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m) :
    EventuallyDenseGoodCoordinate countingDensityModel δ A ↔
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          ∃ i : Fin (m n),
            goodSetDensityByCounting A n i ≥ 1 - δ n / 2 := by
  rfl

/--
高密度好坐标命题的反证法义务打包。

- `allBad_upper_bound` 对应文字证明中的
  `Pr[S] < (1-δ/2)^m + α/2` 型上界。
- `tail_lt_half_alpha` 对应 “指数尾项最终小于 α/2”。
-/
structure DenseGoodCoordinateContradictionObligations
    (D : DensityModel)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m) where
  allBad_upper_bound :
    ∀ n : Nat,
      (∀ i : Fin (m n), D.density n (GoodSet A n i) < 1 - δ n / 2) →
      A.alpha n < (1 - δ n / 2) ^ (m n) + A.alpha n / 2
  tail_lt_half_alpha :
    ∃ n0 : Nat,
      ∀ n : Nat, n ≥ n0 →
        (1 - δ n / 2) ^ (m n) < A.alpha n / 2

/--
逐坐标“坏事件”上界求和：
若每个坐标贡献都不超过 `alpha/(2m)`，则总和不超过 `alpha/2`。
-/
theorem sum_bad_contrib_le_half_alpha
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (n : Nat)
    (pBad : Fin (m n) → ℝ)
    (hm_pos : 0 < m n)
    (hEach :
      ∀ i : Fin (m n),
        pBad i ≤ A.alpha n / (2 * (m n : ℝ))) :
    (∑ i : Fin (m n), pBad i) ≤ A.alpha n / 2 := by
  have hSumLe :
      (∑ i : Fin (m n), pBad i) ≤
        ∑ _i : Fin (m n), A.alpha n / (2 * (m n : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact hEach i
  have hm_ne_nat : m n ≠ 0 := Nat.ne_of_gt hm_pos
  have hm_ne : (m n : ℝ) ≠ 0 := by
    exact_mod_cast hm_ne_nat
  have hConst :
      (∑ _i : Fin (m n), A.alpha n / (2 * (m n : ℝ))) = A.alpha n / 2 := by
    calc
      (∑ _i : Fin (m n), A.alpha n / (2 * (m n : ℝ)))
          = (m n : ℝ) * (A.alpha n / (2 * (m n : ℝ))) := by
              simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = A.alpha n / 2 := by
              field_simp [hm_ne]
  simpa [hConst] using hSumLe

/--
把“成功事件分解 + 全好项上界 + 坏项求和上界”拼接成
`alpha < (1-δ/2)^m + alpha/2`。
-/
theorem allBad_upper_bound_of_decomposition
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (n : Nat)
    (pAllGood : ℝ)
    (pBad : Fin (m n) → ℝ)
    (hDecomp : A.alpha n ≤ pAllGood + (∑ i : Fin (m n), pBad i))
    (hAllGood : pAllGood < (1 - δ n / 2) ^ (m n))
    (hm_pos : 0 < m n)
    (hEachBad :
      ∀ i : Fin (m n),
        pBad i ≤ A.alpha n / (2 * (m n : ℝ))) :
    A.alpha n < (1 - δ n / 2) ^ (m n) + A.alpha n / 2 := by
  have hBadTail :
      (∑ i : Fin (m n), pBad i) ≤ A.alpha n / 2 :=
    sum_bad_contrib_le_half_alpha (A := A) (n := n) (pBad := pBad) hm_pos hEachBad
  have hStep :
      pAllGood + (∑ i : Fin (m n), pBad i) <
        (1 - δ n / 2) ^ (m n) + A.alpha n / 2 :=
    add_lt_add_of_lt_of_le hAllGood hBadTail
  exact lt_of_le_of_lt hDecomp hStep

/--
把“成功事件分解”层面的义务显式打包。

- `pAllGood n` 对应事件 `forall i, x_i in G_i` 的概率上界项；
- `pBad n i` 对应第 `i` 坐标坏事件与成功事件的联合项。
-/
structure DenseGoodCoordinateDecompositionObligations
    (D : DensityModel)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m) where
  m_pos : ∀ n : Nat, 0 < m n
  pAllGood : Nat → ℝ
  pBad : (n : Nat) → Fin (m n) → ℝ
  success_decompose :
    ∀ n : Nat,
      A.alpha n ≤ pAllGood n + (∑ i : Fin (m n), pBad n i)
  allGood_term_lt :
    ∀ n : Nat,
      (∀ i : Fin (m n), D.density n (GoodSet A n i) < 1 - δ n / 2) →
      pAllGood n < (1 - δ n / 2) ^ (m n)
  each_bad_le :
    ∀ (n : Nat) (i : Fin (m n)),
      pBad n i ≤ A.alpha n / (2 * (m n : ℝ))

/--
由“分解层义务 + 指数尾项小于 `alpha/2`”恢复到原反证义务结构。
-/
theorem contradiction_obligations_of_decomposition
    (D : DensityModel)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (hDec : DenseGoodCoordinateDecompositionObligations D δ A)
    (hTail :
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          (1 - δ n / 2) ^ (m n) < A.alpha n / 2) :
    DenseGoodCoordinateContradictionObligations D δ A := by
  refine
    { allBad_upper_bound := ?_
      tail_lt_half_alpha := hTail }
  intro n hAllBad
  exact allBad_upper_bound_of_decomposition
    (δ := δ)
    (A := A)
    (n := n)
    (pAllGood := hDec.pAllGood n)
    (pBad := hDec.pBad n)
    (hDecomp := hDec.success_decompose n)
    (hAllGood := hDec.allGood_term_lt n hAllBad)
    (hm_pos := hDec.m_pos n)
    (hEachBad := hDec.each_bad_le n)

/--
固定参数 `n` 的高密度好坐标反证引理。

若“所有坐标都坏”会推出
`alpha n < (1 - δ/2)^m + alpha n/2`，
且指数尾项已满足 `< alpha n/2`，
则必须存在某个坐标达到密度下界。
-/
theorem dense_good_coordinate_at_n_of_upper_tail
    (D : DensityModel)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (n : Nat)
    (hUpper :
      (∀ i : Fin (m n), D.density n (GoodSet A n i) < 1 - δ n / 2) →
      A.alpha n < (1 - δ n / 2) ^ (m n) + A.alpha n / 2)
    (hTailN : (1 - δ n / 2) ^ (m n) < A.alpha n / 2) :
    ∃ i : Fin (m n), D.density n (GoodSet A n i) ≥ 1 - δ n / 2 := by
  by_contra hNoGood
  have hAllBad :
      ∀ i : Fin (m n), D.density n (GoodSet A n i) < 1 - δ n / 2 := by
    intro i
    have hNotGe : ¬ D.density n (GoodSet A n i) ≥ 1 - δ n / 2 := by
      intro hGe
      exact hNoGood ⟨i, hGe⟩
    exact lt_of_not_ge hNotGe
  have hUpperN : A.alpha n < (1 - δ n / 2) ^ (m n) + A.alpha n / 2 :=
    hUpper hAllBad
  have hUpper' : A.alpha n < A.alpha n / 2 + A.alpha n / 2 := by
    have hSum :
        (1 - δ n / 2) ^ (m n) + A.alpha n / 2 <
          A.alpha n / 2 + A.alpha n / 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_lt_add_right hTailN (A.alpha n / 2))
    exact lt_trans hUpperN hSum
  have hContra : A.alpha n < A.alpha n := by
    calc
      A.alpha n < A.alpha n / 2 + A.alpha n / 2 := hUpper'
      _ = A.alpha n := add_halves (A.alpha n)
  exact (lt_irrefl (A.alpha n)) hContra

/--
高密度好坐标（eventually 版本）的证明骨架。

TODO:
1. 对固定大参数 `n` 反设所有 `i` 都不满足密度下界；
2. 应用 `allBad_upper_bound` 得到 `alpha n` 的严格上界；
3. 应用 `tail_lt_half_alpha` 把上界压到 `< alpha n`，导出矛盾；
4. 得到存在好坐标 `i`。
-/
theorem eventually_dense_good_coordinate_of_obligations
    (D : DensityModel)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
  (hOb : DenseGoodCoordinateContradictionObligations D δ A) :
  EventuallyDenseGoodCoordinate D δ A := by
  rcases hOb.tail_lt_half_alpha with ⟨n0, hTail⟩
  refine ⟨n0, ?_⟩
  intro n hn
  exact dense_good_coordinate_at_n_of_upper_tail
    (D := D)
    (δ := δ)
    (A := A)
    (n := n)
    (hUpper := hOb.allBad_upper_bound n)
    (hTailN := hTail n hn)

/--
由“分解层义务”直接推出 eventually 版高密度好坐标结论。
-/
theorem eventually_dense_good_coordinate_of_decomposition
    (D : DensityModel)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (hDec : DenseGoodCoordinateDecompositionObligations D δ A)
    (hTail :
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          (1 - δ n / 2) ^ (m n) < A.alpha n / 2) :
    EventuallyDenseGoodCoordinate D δ A :=
  eventually_dense_good_coordinate_of_obligations
    (D := D)
    (δ := δ)
    (A := A)
    (hOb :=
      contradiction_obligations_of_decomposition
        (D := D)
        (δ := δ)
        (A := A)
        (hDec := hDec)
        (hTail := hTail))

/--
归约算法参数（对应文字里的“选 `i`、重复 `t(n)` 轮”）。
-/
structure ReductionPlan
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (D : DensityModel) where
  pickIndex : (n : Nat) → Fin (m n)
  rounds : Nat → Nat
  rounds_poly : TuringMachine.Crypto.IsPolynomial rounds
  goodDensity :
    ∀ n : Nat,
      D.density n (GoodSet A n (pickIndex n)) ≥ 1 - δ n / 2

/--
归约成功率下界模板：

`密度项 * (1 - t 轮失败概率)`。
-/
noncomputable def ReductionSuccessLowerBound
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (D : DensityModel)
    {δ : Nat → ℝ}
    (R : ReductionPlan δ A D) : Nat → ℝ :=
  fun n =>
    D.density n (GoodSet A n (R.pickIndex n)) *
      (1 - FailureUpperBound A R.rounds n)

/--
“随机嵌入后输入分布不变”陈述占位。

TODO: 后续替换为对 `f'(U_{nm})` 与归约单轮输入分布相等的正式定义。
-/
def EmbeddingUniformityStatement
    {m : Nat → Nat}
    (_A : ProductAttackProfile m)
    (_D : DensityModel)
    {δ : Nat → ℝ}
    (_R : ReductionPlan δ _A _D) : Prop :=
  True

/--
“单轮成功率下界”陈述占位。

TODO: 后续替换为条件概率形式：`x ∈ G_i -> Pr[success in one round] >= α/(2m)`。
-/
def SingleRoundLowerBoundStatement
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (_D : DensityModel)
    {δ : Nat → ℝ}
    (_R : ReductionPlan δ A _D) : Prop :=
  ∀ n : Nat, 0 ≤ A.alpha n / (2 * (m n : ℝ))

/--
放大后失败概率可忽略的陈述占位。

TODO: 后续替换为你证明中的
`(1 - α/(2m))^t <= exp(-ω(log n)) = negl(n)` 的正式版本。
-/
def AmplificationBoundStatement
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (t : Nat → Nat) : Prop :=
  IsNegligible (FailureUpperBound A t)

/--
分布引理骨架（2.4 第一段）。

TODO: 在概率语义层给出“每轮输入分布与 `f'(U_{nm})` 相同”的严格证明。
-/
theorem reduction_input_distribution_lemma
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (D : DensityModel)
    {δ : Nat → ℝ}
    (R : ReductionPlan δ A D) :
    EmbeddingUniformityStatement A D R := by
  trivial

/--
条件成功率骨架（2.4 第二段）：在好集合上，多轮成功概率趋近 1。

TODO: 结合单轮下界与独立重复，形式化
`1 - (1 - α/(2m))^t`。
-/
theorem conditioned_success_on_good_inputs
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (D : DensityModel)
    {δ : Nat → ℝ}
    (R : ReductionPlan δ A D)
  (_hSingle : SingleRoundLowerBoundStatement A D R) :
    ∀ n : Nat,
      D.density n (GoodSet A n (R.pickIndex n)) *
        (1 - FailureUpperBound A R.rounds n)
        ≤ ReductionSuccessLowerBound A D R n := by
  intro n
  -- 该引理目前只是下界模板的一致性检查，后续会被更强概率结论替换。
  simp [ReductionSuccessLowerBound]

/-!
由高密度好坐标 + 放大界得到“归约成功率超过 `1-δ`”的骨架（2.4 末段）。

这里已把“密度下界 + 失败概率上界”组合成严格不等式链。
-/
theorem reduction_beats_delta_of_dense_good_coordinate
    {m : Nat → Nat}
    (δ : Nat → ℝ)
    (A : ProductAttackProfile m)
    (D : DensityModel)
    (R : ReductionPlan δ A D)
    (hδRange : ∀ n : Nat, 0 < δ n ∧ δ n ≤ 1)
    (hFailureSmall :
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          FailureUpperBound A R.rounds n < δ n / 2) :
    ReductionBeatsDelta δ (ReductionSuccessLowerBound A D R) := by
  rcases hFailureSmall with ⟨n0, hFail⟩
  refine ⟨n0, ?_⟩
  intro n hn
  have hδPos : 0 < δ n := (hδRange n).1
  have hδLeOne : δ n ≤ 1 := (hδRange n).2
  have hFailLt : FailureUpperBound A R.rounds n < δ n / 2 := hFail n hn
  have hFactorNonneg : 0 ≤ 1 - FailureUpperBound A R.rounds n := by
    nlinarith [hFailLt, hδLeOne]
  have hDensityLower : 1 - δ n / 2 ≤ D.density n (GoodSet A n (R.pickIndex n)) :=
    R.goodDensity n
  have hLowerMul :
      (1 - δ n / 2) * (1 - FailureUpperBound A R.rounds n)
        ≤ ReductionSuccessLowerBound A D R n := by
    have hMul := mul_le_mul_of_nonneg_right hDensityLower hFactorNonneg
    simpa [ReductionSuccessLowerBound, mul_assoc, mul_left_comm, mul_comm] using hMul
  have hOneMinusLt : 1 - δ n / 2 < 1 - FailureUpperBound A R.rounds n := by
    nlinarith [hFailLt]
  have hHalfPos : 0 < 1 - δ n / 2 := by
    nlinarith [hδLeOne]
  have hStrictStep :
      (1 - δ n / 2) * (1 - δ n / 2)
        < (1 - δ n / 2) * (1 - FailureUpperBound A R.rounds n) := by
    exact mul_lt_mul_of_pos_left hOneMinusLt hHalfPos
  have hSquareGap : 1 - δ n < (1 - δ n / 2) * (1 - δ n / 2) := by
    nlinarith [hδPos]
  have hCore : 1 - δ n < (1 - δ n / 2) * (1 - FailureUpperBound A R.rounds n) :=
    lt_trans hSquareGap hStrictStep
  have hFinal : 1 - δ n < ReductionSuccessLowerBound A D R n :=
    lt_of_lt_of_le hCore hLowerMul
  exact hFinal

/--
把“成功率函数”与某个具体 PPT 归约敌手关联起来。

TODO: 后续需要把 `ReductionSuccessLowerBound` 连接到真实机器语义的
`successProb S F I n`。
-/
def ReductionRealizedByPPT
    (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily)
    (succ : Nat → ℝ) : Prop :=
  ∃ I : TuringMachine.Crypto.BitPPTAdversary K Λ σ,
    succ = fun n => successProb S F I n

/--
最终矛盾骨架：
若归约成功率最终超过 `1-δ`，则与 `δ`-weak 定义冲突。

TODO: 该步骤需要完整展开 `IsDeltaWeakOWF` 的量词顺序并代入具体归约敌手。
-/
theorem contradiction_with_deltaWeak
    (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily)
    (δ : Nat → ℝ)
    (succ : Nat → ℝ)
    (hWeak : IsDeltaWeakOWF S F δ)
    (hRealized : ReductionRealizedByPPT S F succ)
    (hBreak : ReductionBeatsDelta δ succ) :
    False := by
  rcases hWeak with ⟨_hδrange, hWeakAll⟩
  rcases hRealized with ⟨I, hSucc⟩
  rcases hWeakAll I with ⟨nWeak, hWeakBound⟩
  rcases hBreak with ⟨nBreak, hBreakBound⟩
  let n := max nWeak nBreak
  have hnWeak : n ≥ nWeak := le_max_left _ _
  have hnBreak : n ≥ nBreak := le_max_right _ _
  have hLe : succ n ≤ 1 - δ n := by
    rw [hSucc]
    exact hWeakBound n hnWeak
  have hGt : succ n > 1 - δ n :=
    hBreakBound n hnBreak
  exact (not_lt_of_ge hLe) hGt

/--
Yao 标准证明总骨架（反证法版本）。

此处把 2.1--2.4 的子结论串起来；
当前版本已经完成拼接，关键依赖由显式假设参数给出。
-/
theorem yao_standard_hardness_amplification_framework
    (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily)
    (C : YaoConstruction F)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (D : DensityModel)
    (R : ReductionPlan δ A D)
    (hWeak : IsDeltaWeakOWF S F δ)
    (_hNotStrong : ¬ IsStrongOWF S C.lifted)
    (_hDenseGoodCoordinate : EventuallyDenseGoodCoordinate D δ A)
    (hFailureSmall :
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          FailureUpperBound A R.rounds n < δ n / 2)
    (hRealized :
      ReductionRealizedByPPT S F (ReductionSuccessLowerBound A D R)) :
    False := by
  -- TODO(后续细化): 把 `_hNotStrong` 与 `_hDenseGoodCoordinate` 真正接入到 `hFailureSmall` 的来源证明中。
  have hδRange : ∀ n : Nat, 0 < δ n ∧ δ n ≤ 1 := hWeak.1
  have hBreak : ReductionBeatsDelta δ (ReductionSuccessLowerBound A D R) :=
    reduction_beats_delta_of_dense_good_coordinate
      (δ := δ) (A := A) (D := D) (R := R) hδRange hFailureSmall
  exact contradiction_with_deltaWeak
    (S := S)
    (F := F)
    (δ := δ)
    (succ := ReductionSuccessLowerBound A D R)
    hWeak
    hRealized
    hBreak

/--
Yao 强单向结论（基于已落地的框架定理）。

该版本显式要求“失败概率最终小于 `δ/2`”这一可检查条件，
并把反证法链条完整连接到 `IsStrongOWF` 结论。
-/
theorem YaoStrongnessClaim
    (S : OWFSemantics (K := K) (Λ := Λ) (σ := σ))
    (F : OWFFamily)
    (C : YaoConstruction F)
    (δ : Nat → ℝ)
    {m : Nat → Nat}
    (A : ProductAttackProfile m)
    (D : DensityModel)
    (R : ReductionPlan δ A D)
    (hWeakDelta : IsDeltaWeakOWF S F δ)
    (hDenseGoodCoordinate : EventuallyDenseGoodCoordinate D δ A)
    (hFailureSmall :
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          FailureUpperBound A R.rounds n < δ n / 2)
    (hRealized :
      ReductionRealizedByPPT S F (ReductionSuccessLowerBound A D R)) :
    IsStrongOWF S C.lifted := by
  by_contra hNotStrong
  exact yao_standard_hardness_amplification_framework
    (S := S)
    (F := F)
    (C := C)
    (δ := δ)
    (A := A)
    (D := D)
    (R := R)
    hWeakDelta
    hNotStrong
    hDenseGoodCoordinate
    hFailureSmall
    hRealized

end ConcreteYaoTheorem

end OneWayFunction
