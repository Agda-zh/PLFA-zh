---
title     : "Properties: 进行性与保型性"
layout    : page
prev      : /Lambda/
permalink : /Properties/
next      : /DeBruijn/
translators : ["starxingchenc","alissa-tung"]
progress  : 80
---

```
module plfa.part2.Properties where
```

<!--
This chapter covers properties of the simply-typed lambda calculus, as
introduced in the previous chapter.  The most important of these
properties are progress and preservation.  We introduce these below,
and show how to combine them to get Agda to compute reduction
sequences for us.
-->

本章涵盖了上一章所介绍的简单类型 λ-演算的性质。
在这些性质中最为重要的是进行性（Progress）与保型性（Preservation）。
我们将在稍后介绍它们，并展示如何通过组合它们来使 Agda 为我们计算归约序列。

<!--
## Imports
-->

## 导入

```
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.part1.Isomorphism
open import plfa.part2.Lambda
```


<!--
## Introduction
-->

## 导言

<!--
The last chapter introduced simply-typed lambda calculus,
including the notions of closed terms, terms that are values,
reducing one term to another, and well-typed terms.
-->

在上一章中介绍了简单类型的 λ-演算，包括闭项、作为值的项、将一个项
归约为另一个项和良类型的项的概念。

<!--
Ultimately, we would like to show that we can keep reducing a term
until we reach a value.  For instance, in the last chapter we showed
that two plus two is four,
-->

最终，我们将要展示我们能够通过持续地对一个项做归约，直到它达到一个值。
例如，在上一章中我们展示了二加上二的和是四，


    plus · two · two  —↠  `suc `suc `suc `suc `zero

<!--
which was proved by a long chain of reductions, ending in the value
on the right.  Every term in the chain had the same type, `` `ℕ ``.
We also saw a second, similar example involving Church numerals.
-->

而这是通过一长链的归约步骤证明的，结束于链最右侧的值。
链上的每一个项都具有相同的类型，即 `` `ℕ ``。
我们还见到了第二个类似的例子，涉及了 Church 表示法表示的数字。

<!--
What we might expect is that every term is either a value or can take
a reduction step.  As we will see, this property does _not_ hold for
every term, but it does hold for every closed, well-typed term.
-->

我们可能会希望任意一个项要么是一个值，要么可以进行一步规约。
我们将会看到，此性质**并不**对所有项都成立，但对于所有良类型的闭项成立。

<!--
_Progress_: If `∅ ⊢ M ⦂ A` then either `M` is a value or there is an `N` such
that `M —→ N`.
-->

**进行性**：如果有 `∅ ⊢ M ⦂ A`，那么要么项 `M` 是一个值，要么存在一个项 `N` 使
得 `M —→ N` 成立。

<!--
So, either we have a value, and we are done, or we can take a reduction step.
In the latter case, we would like to apply progress again. But to do so we need
to know that the term yielded by the reduction is itself closed and well typed.
It turns out that this property holds whenever we start with a closed,
well-typed term.
-->

所以要么我们有一个值，这时我们已经完成了规约；要么我们可以进行一步规约。
当处于后者的情况时，我们可以再一次应用进行性。
但要这样做需要我们首先知道通过规约得到的项本身是良类型的闭项。
事实上，只要我们规约的起点是一个良类型的闭项，所得到的项就满足这个性质。

<!--
_Preservation_: If `∅ ⊢ M ⦂ A` and `M —→ N` then `∅ ⊢ N ⦂ A`.
-->

**保型性**：如果 `∅ ⊢ M ⦂ A` 且 `M —→ N`，那么 `∅ ⊢ N ⦂ A`。

<!--
This gives us a recipe for automating evaluation. Start with a closed
and well-typed term.  By progress, it is either a value, in which case
we are done, or it reduces to some other term.  By preservation, that
other term will itself be closed and well typed.  Repeat.  We will
either loop forever, in which case evaluation does not terminate, or
we will eventually reach a value, which is guaranteed to be closed and
of the same type as the original term.  We will turn this recipe into
Agda code that can compute for us the reduction sequence of `plus · two · two`,
and its Church numeral variant.
-->

这给予我们一种自动化求值的策略。
从一个良类型的闭项开始。
由进行性，它要么是一个值，于是求值结束了；要么可以被规约为另一个项。
由保型性，所以得到的另一个项本身也是一个良类型的闭项。
重复这一过程。
我们要么会陷入永久的循环中，此时求值过程将不会停机；
要么最终会得到一个被确保是闭项且类型与原始项相同的值。
接下来我们将这种策略转化为 Agda 代码，以计算 `plus · two · two` 和所
对应 Church 表示法表示数字的变体的规约序列。

<!--
(The development in this chapter was inspired by the corresponding
development in _Software Foundations_, Volume _Programming Language
Foundations_, Chapter _StlcProp_.  It will turn out that one of our technical choices
— to introduce an explicit judgment `Γ ∋ x ⦂ A` in place of
treating a context as a function from identifiers to types —
permits a simpler development. In particular, we can prove substitution preserves
types without needing to develop a separate inductive definition of the
`appears_free_in` relation.)
-->

（这一章启发自《软件基础》（_Software Foundations_）/《程序语言基础》（_Programming Language Foundations_）中对应的 _StlcProp_ 的内容。
事实上我们技术选择中的一个——通过显示地引入一条判断 `Γ ∋ x ⦂ A`，
而不是将上下文视作为一个从标识符映射到类型的函数——简化了开发过程。
特别地，我们不需要额外地去归纳定义关系 `appears_free_in` 就可以证明替换保留了类型。）

<!--
## Values do not reduce
-->

## 值无法被规约

<!--
We start with an easy observation. Values do not reduce:
-->

我们从一个简单的观察开始。值无法被规约：

```
V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N
```

<!--
We consider the three possibilities for values:
-->

我们考虑值可能处于的三种情况：

<!--
* If it is an abstraction then no reduction applies

* If it is zero then no reduction applies

* If it is a successor then rule `ξ-suc` may apply,
  but in that case the successor is itself of a value
  that reduces, which by induction cannot occur.
-->

* 如果它是一个 λ-抽象，那么不会匹配任何规约规则

* 如果它是零，也不会匹配任何规约规则

* 如果它是一个数的后继，那么它可能可以与规则 `ξ-suc` 相匹配，
  但由归纳证明它作为值本身还能进行规约的情况是不可能发生的。

<!--
As a corollary, terms that reduce are not values:
-->

作为推论，可以再进行规约的项不是值：

```
—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N
```

<!--
If we expand out the negations, we have
-->

如果我们将这些否定形式展开，可以得到

    V¬—→ : ∀ {M N} → Value M → M —→ N → ⊥
    —→¬V : ∀ {M N} → M —→ N → Value M → ⊥

<!--
which are the same function with the arguments swapped.
-->

可知原命题与推论是同一个函数，只是交换了参数顺序。

<!--
#### Exercise `Canonical-≃` (practice)
-->

#### 练习 `Canonical-≃` （实践）

<!--
Well-typed values must take one of a small number of _canonical forms_,
which provide an analogue of the `Value` relation that relates values
to their types.  A lambda expression must have a function type,
and a zero or successor expression must be a natural.
Further, the body of a function must be well typed in a context
containing only its bound variable, and the argument of successor
must itself be canonical:
-->

良型的式子都属于少数几种**标准式（Canonical Form）**中的一种。
标准式提供了一种类似于 `Value` 的关系，关联值和它们所属的类型。
一个 λ-表达式一定属于函数类型，同时零和后继表达式都属于自然数。
更进一步说，此时函数的函数体必须在只包含它的约束变量的上下文中是良型的，
后继的参数本身也必须是标准式：

```
infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ
```

<!--
Show that `Canonical V ⦂ A` is isomorphic to `(∅ ⊢ V ⦂ A) × (Value V)`,
that is, the canonical forms are exactly the well-typed values.
-->

证明 `Canonical V ⦂ A` 与 `(∅ ⊢ V ⦂ A) × (Value V)` 同构，
也就是标准式即良类型的值。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
## Progress
-->

## 进行性

<!--
We would like to show that every term is either a value or takes a
reduction step.  However, this is not true in general.  The term
-->

我们可能希望任意一个项要么是值，要么可以进行一步规约。
但并不是所有情况都是这样。考虑这样的项

    `zero · `suc `zero

<!--
is neither a value nor can take a reduction step. And if `` s ⦂ `ℕ ⇒ `ℕ ``
then the term
-->

既不是一个值也无法进行一步规约。另外，如果 `` s ⦂ `ℕ ⇒ `ℕ ``，那么项

     s · `zero

<!--
cannot reduce because we do not know which function is bound to the
free variable `s`.  The first of those terms is ill typed, and the
second has a free variable.  Every term that is well typed and closed
has the desired property.
-->

也无法被规约，因为我们不知道哪个函数被绑定到了自由变量 `s` 上。
上述例子中的第一个项是不良类型的，第二个项包含一个自由变量。
只有良类型的闭项才有如下求证的性质：

<!--
_Progress_: If `∅ ⊢ M ⦂ A` then either `M` is a value or there is an `N` such
that `M —→ N`.
-->

**进行性**：如果有 `∅ ⊢ M ⦂ A`，那么要么项 `M` 是一个值，要么存在一个项 `N` 使
得 `M —→ N` 成立。

<!--
To formulate this property, we first introduce a relation that
captures what it means for a term `M` to make progress:
-->

要陈述这一性质，我们首先需要引入一个关系来刻画什么样的项 `M` 才是进行的：

```
data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
```

<!--
A term `M` makes progress if either it can take a step, meaning there
exists a term `N` such that `M —→ N`, or if it is done, meaning that
`M` is a value.
-->

一个进行的项 `M` 要么可以进行一步规约，这意味着存在一个项 `N` 使得 `M —→ N`，
要么已经完成了规约，这意味着 `M` 是一个值。

<!--
If a term is well typed in the empty context then it satisfies progress:
-->

如果一个项在空上下文中是良类型的，那么它满足进行性：

```
progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                             =  step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done (V-zero)                         =  step β-zero
... | done (V-suc VL)                       =  step (β-suc VL)
progress (⊢μ ⊢M)                            =  step β-μ
```

<!--
We induct on the evidence that the term is well typed.
Let's unpack the first three cases:
-->

我们对这个项良类型的论据做归纳。
让我们首先分析前三个情况：

<!--
* The term cannot be a variable, since no variable is well typed
  in the empty context.

* If the term is a lambda abstraction then it is a value.
-->

* 这个项不可能是变量，因为没有变量在空上下文中是良类型的。

* 如果这个项是一个 λ-抽象，可知它是一个值。

<!--
* If the term is an application `L · M`, recursively apply
  progress to the derivation that `L` is well typed:

  + If the term steps, we have evidence that `L —→ L′`,
    which by `ξ-·₁` means that our original term steps
    to `L′ · M`

  + If the term is done, we have evidence that `L` is
    a value, which must be a lambda abstraction.
    Recursively apply progress to the derivation
    that `M` is well typed:
-->

* 如果这个项是一个函数应用 `L · M`，则考虑对项 `L` 良类型的推导过程递归应用进行性：

  + 如果这个项还能够进行一步规约，我们就有了 `L —→ L′` 的论据，再由 `ξ-·₁`，
    可知原来的项进行到 `L′ · M`。

  + 如果这个项的规约结束了，我们就有了 `L` 是一个值的论据。
    则考虑对项 `L` 良类型的推导过程递归应用进行性：

    <!--
    - If the term steps, we have evidence that `M —→ M′`,
      which by `ξ-·₂` means that our original term steps
      to `L · M′`.  Step `ξ-·₂` applies only if we have
      evidence that `L` is a value, but progress on that
      subterm has already supplied the required evidence.
    -->

    - 如果这个项还能够进行一步规约，我们就有了 `M —→ M′` 的论据，再由 `ξ-·₂`，
      可知原来的项进行到 `L′ · M`。要应用规约步骤 `ξ-·₂` 需要我们提供项 `L` 是
      一个值的论据，而之前对子项进行性的分析已经提供了需要的证明。

    <!--
    - If the term is done, we have evidence that `M` is
      a value, so our original term steps by `β-ƛ`.
    -->

    - 如果这个项的规约已经完成了，我们便有了项 `M` 是值的论据。
      我们项 `L` 是一个良类型的值的论据应用标准式引理

<!--
The remaining cases are similar.  If by induction we have a
`step` case we apply a `ξ` rule, and if we have a `done` case
then either we have a value or apply a `β` rule.  For fixpoint,
no induction is required as the `β` rule applies immediately.
-->

剩下的情况都很类似。如果我们由归纳得到了一个可以继续进行规约的
情况 `case` 则应用一条 `ξ` 规则；如果得到的是已经完成规约的
情况 `done` 则要么我们已经得到了一个值，要么应用一条 `β` 规则。
对于不动点，由于可以直接应用所对应的 `β` 规则，不需要再做归纳。

<!--
Our code reads neatly in part because we consider the
`step` option before the `done` option. We could, of course,
do it the other way around, but then the `...` abbreviation
no longer works, and we will need to write out all the arguments
in full. In general, the rule of thumb is to consider the easy case
(here `step`) before the hard case (here `done`).
If you have two hard cases, you will have to expand out `...`
or introduce subsidiary functions.
-->

由于我们在处理 `done` 的情况之前先考虑了 `step` 的情况，
我们的代码读起来还算简洁。当然我们也可以将其以相反的顺序写，
但这样 `...` 的简写形式便不再起作用了，我们便需要在所有情况
都写出所有的参数。一般来说，推荐先考虑简单的情况（也就是此
处的 `step`），然后再考虑较难的情况（此处的 `done`）。
如果两个情况都比较难，此时你可能不得不将 `...` 展开，或者引
入一些辅助函数。

<!--
Instead of defining a data type for `Progress M`, we could
have formulated progress using disjunction and existentials:
-->

也可以用析取和存在量化来形式化进行性，
而不是为 `Progress M` 定义一个数据类型：

```
postulate
  progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
```

<!--
This leads to a less perspicuous proof.  Instead of the mnemonic `done`
and `step` we use `inj₁` and `inj₂`, and the term `N` is no longer
implicit and so must be written out in full.  In the case for `β-ƛ`
this requires that we match against the lambda expression `L` to
determine its bound variable and body, `ƛ x ⇒ N`, so we can show that
`L · M` reduces to `N [ x := M ]`.
-->

但这会导致证明变得不那么明晰易懂。
比起有助于记忆的 `done` 与 `step`，现在我们只能用 `inj₁` 和 `inj₂`；
同时项 `N` 也不再是隐式的，从而我们需要将其完整写出。
当遇到 `β-ƛ` 的情况时，需要我们对 λ-表达式做匹配，以决定它的约束变量和函数体，
也就是形如 `ƛ x ⇒ N` 的形式，从而我们才能证明项 `L · M` 规约到了 `N [ x := M ]`。

<!--
#### Exercise `Progress-≃` (practice)
-->

#### 练习 `Progress-≃`（实践）

<!--
Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.
-->

证明 `Progress M` 与 `Value M ⊎ ∃[ N ](M —→ N)` 是同构的。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
#### Exercise `progress′` (practice)
-->

#### 练习 `progress′`（实践）

<!--
Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.
-->

补全 `progress′` 的证明，并与之前 `progress` 的证明相对比。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
#### Exercise `value?` (practice)
-->

#### 练习 `value?`（实践）

<!--
Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value:
-->

通过将 `progress` 与 `—→¬V` 相组合，
写一个程序判断一个良类型的项是否是一个值：

```
postulate
  value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
```

<!--
## Prelude to preservation
-->

## 证明保型性前的准备工作

<!--
The other property we wish to prove, preservation of typing under
reduction, turns out to require considerably more work.  The proof has
three key steps.
-->

规约过程保持类型是我们所期望去证明的另一个性质，
而事实上这需要做一定程度的准备工作。
在证明中有三个关键步骤。

<!--
The first step is to show that types are preserved by _renaming_.
-->

第一步是证明**重命名**保持类型。

<!--
_Renaming_:
Let `Γ` and `Δ` be two contexts such that every variable that
appears in `Γ` also appears with the same type in `Δ`.  Then
if any term is typeable under `Γ`, it has the same type under `Δ`.
-->

**重命名**：
考虑两个上下文 `Γ` 和 `Δ`，满足 `Γ` 中出现的每个变量同时
也在 `Δ` 中出现且具有相同的类型。那么如果一个项在上下文 `Γ` 中
是可赋型的，它在 `Δ` 中也具有同样的类型。

<!--
In symbols:
-->

用符号表示为：

    ∀ {x A} → Γ ∋ x ⦂ A  →  Δ ∋ x ⦂ A
    ---------------------------------
    ∀ {M A} → Γ ⊢ M ⦂ A  →  Δ ⊢ M ⦂ A

<!--
Three important corollaries follow.  The _weaken_ lemma asserts that a term
which is well typed in the empty context is also well typed in an arbitrary
context.  The _drop_ lemma asserts that a term which is well typed in a context
where the same variable appears twice remains well typed if we drop the shadowed
occurrence. The _swap_ lemma asserts that a term which is well typed in a
context remains well typed if we swap two variables.
-->

接下来是三个重要的结论。
**弱化（Weaken）**引理断言说如果一个项在空上下文中是良类型的，那么它在任意上下文中都是良类型的。
**去除（Drop）**引理断言说如果一个项在给定上下文中是良类型的，且此上下文中同一个变量出现了两次，
此时去除上下文中被遮盖的变量，这个项仍然是良类型的。
**交换（Swap）**引理断言说如果一个项在给定上下文中是良类型的，那么在通过交换上下文中两个变量后得到的
上下文中，这个项仍然是良类型的。

<!--
(Renaming is similar to the _context invariance_ lemma in _Software
Foundations_, but it does not require the definition of
`appears_free_in` nor the `free_in_context` lemma.)
-->

（重命名与《软件基础》中出现的 _context invariance_ 引理类似，
但在这里既不需要先定义 `appears_free_in` 引理，也不需要 `free_in_context` 引理。）

<!--
The second step is to show that types are preserved by
_substitution_.
-->

证明的第二步是论述**替换**保持类型。

<!--
_Substitution_:
Say we have a closed term `V` of type `A`, and under the
assumption that `x` has type `A` the term `N` has type `B`.
Then substituting `V` for `x` in `N` yields a term that
also has type `B`.
-->

**替换**：
如果我们有一个类型为 `A` 的闭项 `V`，同时假定变量 `x` 的类型是 `A`、项 `N` 的类型是 `B`。
此时用项 `V` 替换掉项 `N` 中的变量 `x` 得到的项的类型也为 `B`。

<!--
In symbols:
-->

用符号表示为：

    ∅ ⊢ V ⦂ A
    Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
    Γ ⊢ N [ x := V ] ⦂ B

<!--
The result does not depend on `V` being a value, but it does
require that `V` be closed; recall that we restricted our attention
to substitution by closed terms in order to avoid the need to
rename bound variables.  The term into which we are substituting
is typed in an arbitrary context `Γ`, extended by the variable
`x` for which we are substituting; and the result term is typed
in `Γ`.
-->

此结论不依赖于项 `V` 是一个值，但要求 `V` 是一个闭项；
回忆我们之所以只关注闭项的替换，是为了避免重命名约束变量。
我们将要做替换的项在上下文 `Γ` 扩充上一个变量 `x` 中是良类型的；
同时完成替换后的项在上下文 `Γ` 中是良类型的。

<!--
The lemma establishes that substitution composes well with typing:
typing the components separately guarantees that the result of
combining them is also well typed.
-->

这条引理证明了替换与赋型是可组合的：
独立地对各组件赋型保证组合的结果也是良类型的。

<!--
The third step is to show preservation.
-->

第三步是证明保型性。

<!--
_Preservation_:
If `∅ ⊢ M ⦂ A` and `M —→ N` then `∅ ⊢ N ⦂ A`.
-->

**保型性**：
如果 `∅ ⊢ M ⦂ A` 且 `M —→ N`，那么 `∅ ⊢ N ⦂ A`。


<!--
The proof is by induction over the possible reductions, and
the substitution lemma is crucial in showing that each of the
`β` rules that uses substitution preserves types.
-->

我们对所有可能的规约步骤进行归纳来证明保型性，
在证明的过程中替换引理起到了重要的作用，
它论证了在替换过程中用到的每一条 `β`-规则都保留了类型。

<!--
We now proceed with our three-step programme.
-->

现在继续我们的三步走。

<!--
## Renaming
-->

## 重命名

<!--
We often need to "rebase" a type derivation, replacing a derivation
`Γ ⊢ M ⦂ A` by a related derivation `Δ ⊢ M ⦂ A`.  We may do so as long
as every variable that appears in `Γ` also appears in `Δ`, and with
the same type.
-->

我们常常会需要去 “重建” 一个类型推演过程，
也就是将一个类型推演 `Γ ⊢ M ⦂ A` 替换为对应的推演 `Δ ⊢ M ⦂ A`。
我们能够这样做的前提是每个在上下文 `Γ` 中出现的变量同时也出现在上下文 `Δ` 中，
且它们的类型相同。

<!--
Three of the rules for typing (lambda abstraction, case on naturals,
and fixpoint) have hypotheses that extend the context to include a
bound variable. In each of these rules, `Γ` appears in the conclusion
and `Γ , x ⦂ A` appears in a hypothesis.  Thus:
-->

赋型的三条规则（λ-抽象、对自然数分项与不动点）都有假设来拓展上下文以
包含一个约束变量。三条规则的每一条中都有上下文 `Γ` 都出现在结论中，同时
拓展后的上下文 `Γ , x ⦂ A` 出现在假设中。对于 λ-表达式，也就是：

    Γ , x ⦂ A ⊢ N ⦂ B
    ------------------- ⊢ƛ
    Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

<!--
for lambda expressions, and similarly for case and fixpoint.  To deal
with this situation, we first prove a lemma showing that if one context maps to another,
this is still true after adding the same variable to
both contexts:
-->

对自然数分项和不动点亦是如此。
要处理这类情况，我们首先证明一条论述 “如果一个上下文和另一个上下文之间存在映射，
在对两者添加同一个变量后映射仍然存在” 的引理：

```
ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)
```

<!--
Let `ρ` be the name of the map that takes evidence that
`x` appears in `Γ` to evidence that `x` appears in `Δ`.
The proof is by case analysis of the evidence that `x` appears
in the extended context `Γ , y ⦂ B`:
-->

令 `ρ` 为这个映射，它将变量 `x` 出现在上下文 `Γ` 中的论据映射到
变量 `x` 出现在上下文 `Δ` 中的论据。
这是由分类讨论变量 `x` 出现在拓展后上下文 `Γ , y ⦂ B` 的论据证明的：

<!--
* If `x` is the same as `y`, we used `Z` to access the last variable
in the extended `Γ`; and can similarly use `Z` to access the last
variable in the extended `Δ`.
-->

* 如果变量 `x` 与变量 `y` 相同，我们使用 `Z` 来访问
  拓展后 `Γ` 中的最后一个变量；类似地，访问拓展后 `Δ` 中
  的最后一个变量也是通过使用 `Z` 来完成的。


<!--
* If `x` differs from `y`, then we used `S` to skip over the last
variable in the extended `Γ`, where `x≢y` is evidence that `x` and `y`
differ, and `∋x` is the evidence that `x` appears in `Γ`; and we can
similarly use `S` to skip over the last variable in the extended `Δ`,
applying `ρ` to find the evidence that `x` appears in `Δ`.
-->

* 如果 `x` 与 `y` 不相同，我们则使用 `S` 来跳过拓展后 `Γ` 中的最后一个变量，
  在这里 `x≢y` 即是变量 `x` 与 `y` 不相同的论据，同时 `∋x` 是变量 `x` 出现在
  上下文 `Γ` 中的论据；类似地，我们使用 `S` 来跳过拓展后 `Δ` 的最后一个变量，
  应用 `ρ` 来寻找变量 `x` 出现在上下文 `Δ` 中的论据。

<!--
With the extension lemma under our belts, it is straightforward to
prove renaming preserves types:
-->

有了拓展引理为我们所用，就可以直接写出重命名保持赋型的证明了：

```
rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)           =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero             =  ⊢zero
rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)
```

<!--
As before, let `ρ` be the name of the map that takes evidence that
`x` appears in `Γ` to evidence that `x` appears in `Δ`.  We induct
on the evidence that `M` is well typed in `Γ`.  Let's unpack the
first three cases:
-->

像之前一样，令 `ρ` 为变量 `x` 出现在上下文 `Γ` 中的论据至 `x` 出现在 `Δ` 中变量的映射。
我们对项 `M` 在上下文 `Γ` 中是良赋型的论据做归纳。我们首先来分析前三种情况：

<!--
* If the term is a variable, then applying `ρ` to the evidence
that the variable appears in `Γ` yields the corresponding evidence that
the variable appears in `Δ`.
-->

* 如果项是一个变量，那么对该变量出现在上下文 `Γ` 的论据应用 `ρ` 就能得到
  所对应的该变量出现在 `Δ` 的证明。

<!--
* If the term is a lambda abstraction, use the previous lemma to
extend the map `ρ` suitably and use induction to rename the body of the
abstraction.
-->

* 如果项是一个 λ-抽象，首先使用之前证明的引理来无误地拓展映射 `ρ`，
  然后通过归纳重命名这个 λ-抽象的函数体。

<!--
* If the term is an application, use induction to rename both the
function and the argument.
-->

* 如果项是函数应用的形式，则通过归纳以重命名函数与对应的参数。

<!--
The remaining cases are similar, using induction for each subterm, and
extending the map whenever the construct introduces a bound variable.
-->

对剩下情况的证明大致相同，都是通过对各个子项做归纳，并且在构造
引入一个约束变量时拓展映射。

<!--
The induction is over the derivation that the term is well typed,
so extending the context doesn't invalidate the inductive hypothesis.
Equivalently, the recursion terminates because the second argument
always grows smaller, even though the first argument sometimes grows larger.
-->

由于做归纳的对象是这个项良赋型的推演过程，拓展上下文不会使得归纳假设
无效。等价地，此时的递归会停机，这是由于第二个参数在递归过程中总是变
小一些，尽管第一个参数有时候变大一些。

<!--
We have three important corollaries, each proved by constructing
a suitable map between contexts.
-->

我们有三条重要推论，每条都是通过构造一个恰当的上下文间映射证明的：

<!--
First, a closed term can be weakened to any context:
-->

第一，一个闭项可以被弱化到任意上下文：

```
weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()
```

<!--
Here the map `ρ` is trivial, since there are no possible
arguments in the empty context `∅`.
-->

这里的映射 `ρ` 是平凡的，由于在空上下文 `∅` 中不会出现可能的参数。

<!--
Second, if the last two variables in a context are equal then we can
drop the shadowed one:
-->

第二，如果上下文中的最后两个变量相等，我们就可以去除掉被遮盖的一个：

```
drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z
```

<!--
Here map `ρ` can never be invoked on the inner occurrence of `x` since
it is masked by the outer occurrence.  Skipping over the `x` in the
first position can only happen if the variable looked for differs from
`x` (the evidence for which is `x≢x` or `z≢x`) but if the variable is
found in the second position, which also contains `x`, this leads to a
contradiction (evidenced by `x≢x refl`).
-->

在这里映射 `ρ` 不可能调用较里出现的 `x`，由于它被较外的出现遮盖了。
忽略掉在首位的 `x` 的情况只可能发生在当前寻找的变量不同于 `x` 的情
况（由 `x≢x` 或 `z≢x` 论证），但如果变量在第二个位置被发现了，
并且也包含 `x`，便会导出矛盾（由 `x≢x refl` 论证）。

<!--
Third, if the last two variables in a context differ then we can swap them:
-->

第三，如果上下文中的最后两个变量不同，我们可以交换它们：

```
swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S z≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)
```

<!--
Here the renaming map takes a variable at the end into a variable one
from the end, and vice versa.  The first line is responsible for
moving `x` from a position at the end to a position one from the end
with `y` at the end, and requires the provided evidence that `x ≢ y`.
-->

在这里重命名将上下文的最后一个变量映射到倒数第二个，反之亦然。
第一行负责将 `x` 从上下文的最后一个位置移动到倒数第二个，并且
将 `y` 置于最后，这要求提供 `x ≢ y` 的论据。


<!--
## Substitution
-->

## 替换

<!--
The key to preservation – and the trickiest bit of the proof – is
the lemma establishing that substitution preserves types.
-->

证明保型性的关键——也正是证明最具有技巧性的部分——是
一条证明替换保持赋型的引理。

<!--
Recall that in order to avoid renaming bound variables,
substitution is restricted to be by closed terms only.
This restriction was not enforced by our definition of substitution,
but it is captured by our lemma to assert that substitution
preserves typing.
-->

回忆为了避免重命名约束变量，替换被限制为只替换闭项。
我们所定义的替换并没有强加这一约束，而是由一条断言替换
保持赋型的引理刻画的。

<!--
Our concern is with reducing closed terms, which means that when
we apply `β` reduction, the term substituted in contains a single
free variable (the bound variable of the lambda abstraction, or
similarly for case or fixpoint). However, substitution
is defined by recursion, and as we descend into terms with bound
variables the context grows.  So for the induction to go through,
we require an arbitrary context `Γ`, as in the statement of the lemma.
-->

我们所关注的是规约闭项，这意味着每当我们应用 `β`-规约时，
所替换的项只含有一个自由变量（也就是所对应 λ-抽象、
对自然数分项或不动点表达式的绑定变量）。然而，替换是通过
递归定义的，在我们逐层深入项时遇到的绑定变量增长了上下文。
所以为了进行归纳，我们需要一个任意的上下文 `Γ`，正如这条引理
中所陈述的。

<!--
Here is the formal statement and proof that substitution preserves types:
-->

下面是替换保持赋型的形式化陈述及其证明：

```
subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _           =  weaken ⊢V
... | no  x≢y         =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl        =  ⊥-elim (x≢y refl)
... | no  _           =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl        =  ⊢ƛ (drop ⊢N)
... | no  x≢y         =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)    =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero        =  ⊢zero
subst ⊢V (⊢suc ⊢M)    =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl        =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y         =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl        =  ⊢μ (drop ⊢M)
... | no  x≢y         =  ⊢μ (subst ⊢V (swap x≢y ⊢M))
```

<!--
We induct on the evidence that `N` is well typed in the
context `Γ` extended by `x`.
-->

我们对 `N` 在由 `x`拓展 `Γ` 后得到的上下文中是良赋型的论据做归纳。

<!--
First, we note a wee issue with naming.  In the lemma
statement, the variable `x` is an implicit parameter for the variable
substituted, while in the type rules for variables, abstractions,
cases, and fixpoints, the variable `x` is an implicit parameter for
the relevant variable.  We are going to need to get hold of both
variables, so we use the syntax `{x = y}` to bind `y` to the
substituted variable and the syntax `{x = x}` to bind `x` to the
relevant variable in the patterns for `` ⊢` ``, `⊢ƛ`, `⊢case`, and `⊢μ`.
Using the name `y` here is consistent with the naming in the original
definition of substitution in the previous chapter.  The proof never
mentions the types of `x`, `y`, `V`, or `N`, so in what follows we
choose type names as convenient.
-->

首先我们注意到一个有关命名的问题。
在引理的陈述中，被替换的变量 `x` 是一个隐式参数，同时在变量、抽象、
对自然数分项和不动点的赋型规则中，相关变量 `x` 是一个隐式参数，因此
我们使用形同 `{x = y}` 的语法来将 `y` 与被替换的变量绑定，
用 `{x = x}` 来将 `x` 与 `` ⊢` ``、`⊢ƛ`、`⊢case` 和 `⊢μ` 中相关的变量绑定。
在这里用 `y` 这一名字业余前一章中替换的原始定义一致。
在证明中从来没有提及过 `x`、`y`、`V` 或 `N` 的类型，所以接下来我们按照惯例
选取类型的名字：

<!--
Now that naming is resolved, let's unpack the first three cases:
-->

解决了命名问题，接下来我们来分析前三种情况：

<!--
* In the variable case, we must show
-->

* 当处于变量的情况时，我们必须证明

      ∅ ⊢ V ⦂ B
      Γ , y ⦂ B ⊢ ` x ⦂ A
      ------------------------
      Γ ⊢ ` x [ y := V ] ⦂ A

  <!--
  where the second hypothesis follows from:
  -->

  此时第二个假设形如：

      Γ , y ⦂ B ∋ x ⦂ A

<!--
  There are two subcases, depending on the evidence for this judgment:
-->

  此处有两种子情况，取决于该命题的论据：

  + The lookup judgment is evidenced by rule `Z`:

        ----------------
        Γ , x ⦂ A ∋ x ⦂ A

    In this case, `x` and `y` are necessarily identical, as are `A`
    and `B`.  Nonetheless, we must evaluate `x ≟ y` in order to allow
    the definition of substitution to simplify:

    - If the variables are equal, then after simplification we
      must show

          ∅ ⊢ V ⦂ A
          ---------
          Γ ⊢ V ⦂ A

      which follows by weakening.

    - If the variables are unequal we have a contradiction.

  + The lookup judgment is evidenced by rule `S`:

        x ≢ y
        Γ ∋ x ⦂ A
        -----------------
        Γ , y ⦂ B ∋ x ⦂ A

    In this case, `x` and `y` are necessarily distinct.
    Nonetheless, we must again evaluate `x ≟ y` in order to allow
    the definition of substitution to simplify:

    - If the variables are equal we have a contradiction.

    - If the variables are unequal, then after simplification we
      must show

          ∅ ⊢ V ⦂ B
          x ≢ y
          Γ ∋ x ⦂ A
          -------------
          Γ ⊢ ` x ⦂ A

      which follows by the typing rule for variables.

* In the abstraction case, we must show

      ∅ ⊢ V ⦂ B
      Γ , y ⦂ B ⊢ (ƛ x ⇒ N) ⦂ A ⇒ C
      --------------------------------
      Γ ⊢ (ƛ x ⇒ N) [ y := V ] ⦂ A ⇒ C

  where the second hypothesis follows from

      Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C

  We evaluate `x ≟ y` in order to allow the definition of substitution to simplify:

  + If the variables are equal then after simplification we must show:

        ∅ ⊢ V ⦂ B
        Γ , x ⦂ B , x ⦂ A ⊢ N ⦂ C
        -------------------------
        Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ C

    From the drop lemma, `drop`, we may conclude:

        Γ , x ⦂ B , x ⦂ A ⊢ N ⦂ C
        -------------------------
        Γ , x ⦂ A ⊢ N ⦂ C

    The typing rule for abstractions then yields the required conclusion.

  + If the variables are distinct then after simplification we must show:

        ∅ ⊢ V ⦂ B
        Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
        --------------------------------
        Γ ⊢ ƛ x ⇒ (N [ y := V ]) ⦂ A ⇒ C

    From the swap lemma we may conclude:

        Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
        -------------------------
        Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C

    The inductive hypothesis gives us:

        ∅ ⊢ V ⦂ B
        Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C
        ----------------------------
        Γ , x ⦂ A ⊢ N [ y := V ] ⦂ C

    The typing rule for abstractions then yields the required conclusion.

* In the application case, we must show

      ∅ ⊢ V ⦂ C
      Γ , y ⦂ C ⊢ L · M ⦂ B
      --------------------------
      Γ ⊢ (L · M) [ y := V ] ⦂ B

  where the second hypothesis follows from the two judgments

      Γ , y ⦂ C ⊢ L ⦂ A ⇒ B
      Γ , y ⦂ C ⊢ M ⦂ A

  By the definition of substitution, we must show:

      ∅ ⊢ V ⦂ C
      Γ , y ⦂ C ⊢ L ⦂ A ⇒ B
      Γ , y ⦂ C ⊢ M ⦂ A
      ---------------------------------------
      Γ ⊢ (L [ y := V ]) · (M [ y := V ]) ⦂ B

  Applying the induction hypothesis for `L` and `M` and the typing
  rule for applications yields the required conclusion.

<!--
The remaining cases are similar, using induction for each subterm.
Where the construct introduces a bound variable we need to compare it
with the substituted variable, applying the drop lemma if they are
equal and the swap lemma if they are distinct.
-->

对剩下情况的证明大致相同，都是通过对各个子项做归纳。
当构造引入一个约束变量时我们需要将其与被替换的变量进行比较，
如果它们相同则应用去除引理，如果它们不同则应用交换引理。

<!--
For Agda it makes a difference whether we write `x ≟ y` or
`y ≟ x`. In an interactive proof, Agda will show which residual `with`
clauses in the definition of `_[_:=_]` need to be simplified, and the
`with` clauses in `subst` need to match these exactly. The guideline is
that Agda knows nothing about symmetry or commutativity, which require
invoking appropriate lemmas, so it is important to think about order of
arguments and to be consistent.
-->

对于 Agda 来说，我们写 `x ≟ y` 还是写 `y ≟ x` 是有区别的。
在交互式证明中，Agda 将显示 `_[_:=_]` 定义中的哪些剩余 `with` 子句需要简化，
而 `subst` 中的 `with` 子句需要精确匹配这些子句。
指导准则是 Agda 对于对称性和交换性一无所知，这需要调用适当的引理，
因此考虑参数的顺序和保持一致性非常重要。

<!--
#### Exercise `subst′` (stretch)
-->

#### 练习 `subst`（延伸）

<!--
Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.
-->

重写 `subst` 的定义，使得它与在上一章练习中修改过的 `_[_:=_]′` 定义相兼容。
和之前一样，需要将处理约束变量的部分提取成一个单独的函数，与替换保持类型的
证明一同互递归定义。


<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
## Preservation
-->

## 保型性

<!--
Once we have shown that substitution preserves types, showing
that reduction preserves types is straightforward:
-->

一旦我们证明了替换保持类型，证明规约保持类型是简单的：

```
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M
```

<!--
The proof never mentions the types of `M` or `N`,
so in what follows we choose type name as convenient.
-->

证明从来没有提到 `M` 或 `N` 的类型，
因此在下面的内容中，我们尽可能方便地选择类型名称。

<!--
Let's unpack the cases for two of the reduction rules:
-->

让我们分析规约规则的两种情况：

<!--
* Rule `ξ-·₁`.  We have

      L —→ L′
      ----------------
      L · M —→ L′ · M

  where the left-hand side is typed by

      Γ ⊢ L ⦂ A ⇒ B
      Γ ⊢ M ⦂ A
      -------------
      Γ ⊢ L · M ⦂ B

  By induction, we have

      Γ ⊢ L ⦂ A ⇒ B
      L —→ L′
      --------------
      Γ ⊢ L′ ⦂ A ⇒ B

  from which the typing of the right-hand side follows immediately.

* Rule `β-ƛ`.  We have

      Value V
      -----------------------------
      (ƛ x ⇒ N) · V —→ N [ x := V ]

  where the left-hand side is typed by

      Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
      Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B    Γ ⊢ V ⦂ A
      --------------------------------
      Γ ⊢ (ƛ x ⇒ N) · V ⦂ B

  By the substitution lemma, we have

      Γ ⊢ V ⦂ A
      Γ , x ⦂ A ⊢ N ⦂ B
      --------------------
      Γ ⊢ N [ x := V ] ⦂ B

  from which the typing of the right-hand side follows immediately.

The remaining cases are similar.  Each `ξ` rule follows by induction,
and each `β` rule follows by the substitution lemma.
-->

* 规则 `ξ-·₁`。我们有

      L —→ L′
      ----------------
      L · M —→ L′ · M

  其中左手侧由

      Γ ⊢ L ⦂ A ⇒ B
      Γ ⊢ M ⦂ A
      -------------
      Γ ⊢ L · M ⦂ B

  赋型。

  根据归纳，我们有

      Γ ⊢ L ⦂ A ⇒ B
      L —→ L′
      --------------
      Γ ⊢ L′ ⦂ A ⇒ B

  其中右手侧的赋型可以直接得出。

* 规则 `β-ƛ`。我们有

      Value V
      -----------------------------
      (ƛ x ⇒ N) · V —→ N [ x := V ]

  其中左手侧由

      Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
      Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B    Γ ⊢ V ⦂ A
      --------------------------------
      Γ ⊢ (ƛ x ⇒ N) · V ⦂ B

  赋型。

  根据替换引理，我们有

      Γ ⊢ V ⦂ A
      Γ , x ⦂ A ⊢ N ⦂ B
      --------------------
      Γ ⊢ N [ x := V ] ⦂ B

  其中右手侧的赋型可以直接得出。

剩余情况与此类似，对每个 `ξ` 规则使用归纳，
对每个 `β` 规则使用替换引理。


<!--
## Evaluation
-->

## 求值

<!--
By repeated application of progress and preservation, we can evaluate
any well-typed term.  In this section, we will present an Agda
function that computes the reduction sequence from any given closed,
well-typed term to its value, if it has one.
-->

通过重复应用进行性和保型性，我们可以对任何良类型的项求值。
在这一节，我们将介绍一个 Agda 函数，
该函数可以求得任意给定良类型的闭项到其值的规约序列，如果该序列存在。

<!--
Some terms may reduce forever.  Here is a simple example:
-->

一些项将永远规约下去。这是一个例子：

```
sucμ  =  μ "x" ⇒ `suc (` "x")

_ =
  begin
    sucμ
  —→⟨ β-μ ⟩
    `suc sucμ
  —→⟨ ξ-suc β-μ ⟩
    `suc `suc sucμ
  —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc `suc `suc sucμ
  --  ...
  ∎
```

<!--
Since every Agda computation must terminate,
we cannot simply ask Agda to reduce a term to a value.
Instead, we will provide a natural number to Agda, and permit it
to stop short of a value if the term requires more than the given
number of reduction steps.
-->

由于每个 Agda 计算都必须终止，
我们不能仅仅要求 Agda 将项规约为值。
相反，我们将向 Agda 提供一个自然数，
并允许它在需要比给定的数更多的规约步骤时终止规约。

<!--
A similar issue arises with cryptocurrencies.  Systems which use
smart contracts require the miners that maintain the blockchain to
evaluate the program which embodies the contract.  For instance,
validating a transaction on Ethereum may require executing a program
for the Ethereum Virtual Machine (EVM).  A long-running or
non-terminating program might cause the miner to invest arbitrary
effort in validating a contract for little or no return.  To avoid
this situation, each transaction is accompanied by an amount of _gas_
available for computation.  Each step executed on the EVM is charged
an advertised amount of gas, and the transaction pays for the gas at a
published rate: a given number of Ethers (the currency of Ethereum)
per unit of gas.
-->

加密货币也存在类似的问题。
使用智能合约的系统要求维护区块链的矿工评估体现合约的程序。
例如，验证以太坊上的交易可能需要为以太坊虚拟机（EVM）执行一个程序。
一个长期运行或非终止的程序可能会导致矿工在验证合同上投入任意多的努力，
但回报很少或没有回报。为了避免这种情况，
每笔交易都伴随着一定数量的**燃料（Gas）**可用于计算。
在 EVM 上执行的每个步骤都会收取公告数量的燃料，
交易以公布的费率支付燃料：每单位燃料支付给定数量的以太币（以太坊的货币）。

<!--
By analogy, we will use the name _gas_ for the parameter which puts a
bound on the number of reduction steps.  `Gas` is specified by a natural number:
-->

以此类推，我们将使用**燃料**作为参数的名称，
该参数限制了规约步骤的数量。`Gas` 由一个自然数指定。

```
record Gas : Set where
  constructor gas
  field
    amount : ℕ
```

<!--
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value or indicate that it ran out of gas:
-->

当我们的求值器返回了一个项 `N`，它要么证明 `N` 是一个值，
要么表明它耗尽了燃料：

```
data Finished (N : Term) : Set where

  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N
```

<!--
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished:
-->

给定一个类型为 `A` 的项 `L`，对于某个 `N`，
求值器将返回从 `L` 到 `N` 的规约序列以及规约是否完成的指示：

```
data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```

<!--
The evaluator takes gas and evidence that a term is well typed,
and returns the corresponding steps:
-->

求值器使用燃料和项是良类型的论据，
并返回相应的步骤：

```

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero)    ⊢L                                =  steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL                                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) (preserve ⊢L L—→M)
...    | steps M—↠N fin                                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```

<!--
Let `L` be the name of the term we are reducing, and `⊢L` be the
evidence that `L` is well typed.  We consider the amount of gas
remaining.  There are two possibilities:
-->

令 `L` 是我们要规约的项的名称，`⊢L` 是项 `L` 是良类型的论据。
我们考虑剩余的燃料量。

<!--
* It is zero, so we stop early.  We return the trivial reduction
  sequence `L —↠ L`, evidence that `L` is well typed, and an
  indication that we are out of gas.
-->

* 如果是零，则我们过早地停止了。我们将返回简单的规约序列 `L —↠ L`，
  证明 `L` 是良类型，并标明我们用尽了燃料。

<!--
* It is non-zero and after the next step we have `m` gas remaining.
  Apply progress to the evidence that term `L` is well typed.  There
  are two possibilities:
-->

* 如果非零，则在下一个步骤中我们还剩下 `m` 燃料。将进度应用于项 `L` 是良类型的论据。
  此处有两种可能：

<!--
  + Term `L` is a value, so we are done. We return the
    trivial reduction sequence `L —↠ L`, evidence that `L` is
    well typed, and the evidence that `L` is a value.
-->

  + 项 `L` 是一个值，则我们已经完成了。
    我们将返回简单的规约序列 `L —↠ L`，证明 `L` 是良类型，以及 `L` 是值的论据。

<!--
  + Term `L` steps to another term `M`.  Preservation provides
    evidence that `M` is also well typed, and we recursively invoke
    `eval` on the remaining gas.  The result is evidence that
    `M —↠ N`, together with evidence that `N` is well typed and an
    indication of whether reduction finished.  We combine the evidence
    that `L —→ M` and `M —↠ N` to return evidence that `L —↠ N`,
    together with the other relevant evidence.
-->

  + 项 `L` 步进至另一个项 `M`。保型性提供了 `M` 也是良类型的论据，
    我们对剩余的燃料递归调用 `eval`。
    结果将得到 `M —↠ N` 的论据以及 `N` 是良类型的论据和规约是否完成的标识。
    我们将 `L —→ M` 和 `M —↠ N` 的论据结合来得到 `L —↠ N` 以及其它有关的的论据。


<!--
### Examples
-->

### 例子

<!--
We can now use Agda to compute the non-terminating reduction
sequence given earlier.  First, we show that the term `sucμ`
is well typed:
-->

现在我们可以用 Agda 来计算之前给出的不停机的规约序列。
首先我们证明项 `sucμ` 是良赋型的：

```
⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z
```

<!--
To show the first three steps of the infinite reduction
sequence, we evaluate with three steps worth of gas:
-->

我们花三步量的燃料来进行求值，
以展示这个无穷规约序列的前三步：

```
_ : eval (gas 3) ⊢sucμ ≡
  steps
   (μ "x" ⇒ `suc ` "x"
   —→⟨ β-μ ⟩
    `suc (μ "x" ⇒ `suc ` "x")
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ "x" ⇒ `suc ` "x"))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
   ∎)
   out-of-gas
_ = refl
```

<!--
Similarly, we can use Agda to compute the reduction sequences given
in the previous chapter.  We start with the Church numeral two
applied to successor and zero.  Supplying 100 steps of gas is more than enough:
-->

类似地，我们可以用 Agda 计算前一章节中给出的规约序列。
我们从计算 Church 表示法表示数字的数字二应用到后继和数字零开始。
提供 100 步量的燃料就已远超过需求了：

```
_ : eval (gas 100) (⊢twoᶜ · ⊢sucᶜ · ⊢zero) ≡
  steps
   ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
   · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
     `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "n" ⇒ `suc ` "n") · `suc `zero
   —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
   ∎)
   (done (V-suc (V-suc V-zero)))
_ = refl
```

<!--
The example above was generated by using `C-c C-n` to normalise the
left-hand side of the equation and pasting in the result as the
right-hand side of the equation.  The example reduction of the
previous chapter was derived from this result, reformatting and
writing `twoᶜ` and `sucᶜ` in place of their expansions.
-->

上面的例子是通过首先使用组合键 `C-c C-n` 来范式化等式的左侧，
然后将结果粘贴到等式右侧的方式生成的。前一章中规约的例子便是
通过使用这一方式导出结果、重新排版并且将展开的表达式对应地重
写为 `twoᶜ` 和 `sucᶜ` 的形式得到的。

<!--
Next, we show two plus two is four:
-->

接下来，我们来证明二加二的和是四：

```
_ : eval (gas 100) ⊢2+2 ≡
  steps
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "m"
       · ` "n")
      ]))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · ` "n")
     ])
    · `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · `suc (`suc `zero))
    ]
   —→⟨ β-suc (V-suc V-zero) ⟩
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc
    ((ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc
    ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "m"
       · ` "n")
      ])
     · `suc (`suc `zero))
   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc
    case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · `suc (`suc `zero))
    ]
   —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc
    (`suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc
    (`suc
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc
    (`suc
     ((ƛ "n" ⇒
       case `zero [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ])
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc
    (`suc
     case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `suc (`suc `zero))
     ])
   —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
```

<!--
Again, the derivation in the previous chapter was derived by
editing the above.
-->

再一次地，上一章中的推导是通过编辑上述内容得出的。

<!--
Similarly, we can evaluate the corresponding term for Church numerals:
-->

类似地，我们可以计算 Church 表示法表示的数字的相应项。

```
_ : eval (gas 100) ⊢2+2ᶜ ≡
  steps
   ((ƛ "m" ⇒
     (ƛ "n" ⇒
      (ƛ "s" ⇒ (ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")))))
    · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
    · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
    · (ƛ "n" ⇒ `suc ` "n")
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒
     (ƛ "s" ⇒
      (ƛ "z" ⇒
       (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
       (` "n" · ` "s" · ` "z"))))
    · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
    · (ƛ "n" ⇒ `suc ` "n")
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒
     (ƛ "z" ⇒
      (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
      ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" · ` "z")))
    · (ƛ "n" ⇒ `suc ` "n")
    · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒
     (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
     ·
     ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
      · ` "z"))
    · `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
    ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
     · `zero)
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
     · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
     `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "n" ⇒ `suc ` "n") · `suc `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `suc (`suc `zero))
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒ `suc ` "n") · `suc (`suc (`suc `zero))
   —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
```

<!--
And again, the example in the previous section was derived by editing the
above.
-->

再一次地，上一节中的示例是通过编辑上述内容得出的。

<!--
#### Exercise `mul-eval` (recommended)
-->

#### 练习 `mul-eval`（推荐）

<!--
Using the evaluator, confirm that two times two is four.
-->

用这个求值器来验证二乘以二的积是四。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
#### Exercise: `progress-preservation` (practice)
-->

#### 练习 `progress-preservation` （实践）

<!--
Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.
-->

不阅读上面的陈述，
写下简单类型 λ-演算进行性和保型性的定理。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
#### Exercise `subject_expansion` (practice)
-->

#### 练习 `subject_expansion` （实践）

<!--
We say that `M` _reduces_ to `N` if `M —→ N`,
but we can also describe the same situation by saying
that `N` _expands_ to `M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.
-->

如果 `M —→ N`，我们便称 `M` **规约**至 `N`，
相同的情形也被称作 `N` **扩展（Expand）**至 `M`。
保型性有时也被叫做**子规约（Subject Reduction）**。
它的对应是**子扩展（Subject Expansion）**，
如果 `M —→ N` 和 `∅ ⊢ N ⦂ A` 蕴含 `∅ ⊢ M ⦂ A`。
找到两个子扩展的反例，一个涉及 `case` 表达式而另一个不涉及。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
## Well-typed terms don't get stuck
-->

## 良类型的项不会卡住

<!--
A term is _normal_ if it cannot reduce:
-->

一个项是**范式**，如果它不能被规约。

```
Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)
```

<!--
A term is _stuck_ if it is normal yet not a value:
-->

一个项被**卡住**，如果它是一个范式但不是一个值。

```
Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M
```

<!--
Using progress, it is easy to show that no well-typed term is stuck:
-->

使用进行性，很容易证明没有良类型的项会被卡住。

```
postulate
  unstuck : ∀ {M A}
    → ∅ ⊢ M ⦂ A
      -----------
    → ¬ (Stuck M)
```

<!--
Using preservation, it is easy to show that after any number of steps,
a well-typed term remains well typed:
-->

使用保型性，很容易证明在经过任意多次步进后，
良类型的项依旧是良类型的。

```
postulate
  preserves : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M —↠ N
      ---------
    → ∅ ⊢ N ⦂ A
```

<!--
An easy consequence is that starting from a well-typed term, taking
any number of reduction steps leads to a term that is not stuck:
-->

一个简单地结果是，从一个良类型的项开始，进行任意多次步进，
将得到一个不被卡住的项。

```
postulate
  wttdgs : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M —↠ N
      -----------
    → ¬ (Stuck N)
```

<!--
Felleisen and Wright, who introduced proofs via progress and
preservation, summarised this result with the slogan _well-typed terms
don't get stuck_.  (They were referring to earlier work by Robin
Milner, who used denotational rather than operational semantics. He
introduced `wrong` as the denotation of a term with a type error, and
showed _well-typed terms don't go wrong_.)
-->

Felleisen 与 Wright 通过进行性和保型性引入了证明，并将其总结为 **良类型的项不会卡住** 的口号。
（他们提及了 Robin Milner 早期的工作，他使用指称而非操作语义。
他引入了“错误”作为带有类型错误的术语的指称，并展示了 **良类型的项不会出错**。）

<!--
#### Exercise `stuck` (practice)
-->

#### 练习 `stuck` （实践）

<!--
Give an example of an ill-typed term that does get stuck.
-->

给出一个会被卡住的不良类型的项的例子。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
#### Exercise `unstuck` (recommended)
-->

#### 练习 `unstuck` （推荐）

<!--
Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.
-->

提供上文中 `unstuck`、`preserves` 和 `wttdgs` 三个假设的证明。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
## Reduction is deterministic
-->

## 规约是确定的

<!--
When we introduced reduction, we claimed it was deterministic.
For completeness, we present a formal proof here.
-->

当我们引入归约时，我们声称它是确定的。
为完整起见，我们在此提供正式的证明。

<!--
Our proof will need a variant
of congruence to deal with functions of four arguments
(to deal with `case_[zero⇒_|suc_⇒_]`).  It
is exactly analogous to `cong` and `cong₂` as defined previously:
-->

我们的证明需要一个合同变体来处理四个参数的函数（处理`case_[zero⇒_|suc_⇒_]`）。
它与之前定义的 `cong` 和 `cong₂` 完全类似：

```
cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl
```

<!--
It is now straightforward to show that reduction is deterministic:
-->

现在证明规约是确定的十分简单。

```
det : ∀ {M M′ M″}
  → (M —→ M′)
  → (M —→ M″)
    --------
  → M′ ≡ M″
det (ξ-·₁ L—→L′)   (ξ-·₁ L—→L″)     =  cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ L—→L′)   (ξ-·₂ VL M—→M″)  =  ⊥-elim (V¬—→ VL L—→L′)
det (ξ-·₁ L—→L′)   (β-ƛ _)          =  ⊥-elim (V¬—→ V-ƛ L—→L′)
det (ξ-·₂ VL _)    (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ VL L—→L″)
det (ξ-·₂ _ M—→M′) (ξ-·₂ _ M—→M″)   =  cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ _ M—→M′) (β-ƛ VM)         =  ⊥-elim (V¬—→ VM M—→M′)
det (β-ƛ _)        (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ V-ƛ L—→L″)
det (β-ƛ VM)       (ξ-·₂ _ M—→M″)   =  ⊥-elim (V¬—→ VM M—→M″)
det (β-ƛ _)        (β-ƛ _)          =  refl
det (ξ-suc M—→M′)  (ξ-suc M—→M″)    =  cong `suc_ (det M—→M′ M—→M″)
det (ξ-case L—→L′) (ξ-case L—→L″)   =  cong₄ case_[zero⇒_|suc_⇒_]
                                         (det L—→L′ L—→L″) refl refl refl
det (ξ-case L—→L′) β-zero           =  ⊥-elim (V¬—→ V-zero L—→L′)
det (ξ-case L—→L′) (β-suc VL)       =  ⊥-elim (V¬—→ (V-suc VL) L—→L′)
det β-zero         (ξ-case M—→M″)   =  ⊥-elim (V¬—→ V-zero M—→M″)
det β-zero         β-zero           =  refl
det (β-suc VL)     (ξ-case L—→L″)   =  ⊥-elim (V¬—→ (V-suc VL) L—→L″)
det (β-suc _)      (β-suc _)        =  refl
det β-μ            β-μ              =  refl
```

<!--
The proof is by induction over possible reductions.  We consider
three typical cases:
-->

证明通过对可能的规约进行归纳来完成。我们考虑三种典型的情况：

<!--
* Two instances of `ξ-·₁`:

      L —→ L′                 L —→ L″
      --------------- ξ-·₁    --------------- ξ-·₁
      L · M —→ L′ · M         L · M —→ L″ · M

  By induction we have `L′ ≡ L″`, and hence by congruence
  `L′ · M ≡ L″ · M`.

* An instance of `ξ-·₁` and an instance of `ξ-·₂`:

                              Value L
      L —→ L′                 M —→ M″
      --------------- ξ-·₁    --------------- ξ-·₂
      L · M —→ L′ · M         L · M —→ L · M″

  The rule on the left requires `L` to reduce, but the rule on the right
  requires `L` to be a value.  This is a contradiction since values do
  not reduce.  If the value constraint was removed from `ξ-·₂`, or from
  one of the other reduction rules, then determinism would no longer hold.

* Two instances of `β-ƛ`:

      Value V                              Value V
      ----------------------------- β-ƛ    ----------------------------- β-ƛ
      (ƛ x ⇒ N) · V —→ N [ x := V ]        (ƛ x ⇒ N) · V —→ N [ x := V ]

  Since the left-hand sides are identical, the right-hand sides are
  also identical. The formal proof simply invokes `refl`.
-->

* 两个关于 `ξ-·₁` 的实例：

      L —→ L′                 L —→ L″
      --------------- ξ-·₁    --------------- ξ-·₁
      L · M —→ L′ · M         L · M —→ L″ · M

  根据归纳我们有 `L′ ≡ L″`，因此根据合同性有 `L′ · M ≡ L″ · M`。

* 一个关于 `ξ-·₁` 的实例和一个关于 `ξ-·₂` 的实例：

                              Value L
      L —→ L′                 M —→ M″
      --------------- ξ-·₁    --------------- ξ-·₂
      L · M —→ L′ · M         L · M —→ L · M″

  左侧的规则要求 `L` 被规约，但右侧的规则要求 `L` 是一个值。
  这是一个矛盾，因为值无法被规约。如果值的约束从 `ξ-·₂` 或任何其他规约规则中被移除，
  那么确定性将不再适用。

* 两个关于 `β-ƛ` 的实例：

      Value V                              Value V
      ----------------------------- β-ƛ    ----------------------------- β-ƛ
      (ƛ x ⇒ N) · V —→ N [ x := V ]        (ƛ x ⇒ N) · V —→ N [ x := V ]

  因为左侧是相同的，所以右侧也是相同的。
  形式证明只是对 `refl` 的调用。

<!--
Five of the 18 lines in the above proof are redundant, e.g., the case
when one rule is `ξ-·₁` and the other is `ξ-·₂` is considered twice,
once with `ξ-·₁` first and `ξ-·₂` second, and the other time with the
two swapped.  What we might like to do is delete the redundant lines
and add

    det M—→M′ M—→M″ = sym (det M—→M″ M—→M′)

to the bottom of the proof. But this does not work: the termination
checker complains, because the arguments have merely switched order
and neither is smaller.
-->

上述证明中的 18 行中有 5 行是多余的，
例如，当一个规则是 `ξ-·₁` 而另一个是 `ξ-·₂` 的情况被考虑两次，
一次是先有 `ξ-·₁`，然后有 `ξ-·₂`，另一次将两者互换。
我们可能想做的是删除多余的行并在证明的底部添加

    det M—→M′ M—→M″ = sym (det M—→M″ M—→M′)

但这不起作用：停机检查器报错，因为参数只是被交换了顺序，而且没有任何一个变得更小。


<!--
#### Quiz
-->

#### 小测验

<!--
Suppose we add a new term `zap` with the following reduction rule
-->

假设我们加入了一个新项 `zap` 以及以下规约规则

    -------- β-zap
    M —→ zap

<!--
and the following typing rule:
-->

和以下赋型规则：

    ----------- ⊢zap
    Γ ⊢ zap ⦂ A

<!--
Which of the following properties remain true in
the presence of these rules?  For each property, write either
"remains true" or "becomes false." If a property becomes
false, give a counterexample:
-->

在这些规则存在的情况下，以下哪些属性仍然成立？
对于每个属性，写下 “仍为真” 或 “变为假”。
如果一个属性变为假，请举出一个反例：

<!--
  - Determinism of `step`

  - Progress

  - Preservation
-->

  - `step` 的确定性

  - 进行性

  - 保型性


<!--
#### Quiz
-->

#### 小测验

<!--
Suppose instead that we add a new term `foo` with the following
reduction rules:
-->

假设我们加入了一个新项 `foo` 以及以下规约规则：

    ------------------ β-foo₁
    (λ x ⇒ ` x) —→ foo

    ----------- β-foo₂
    foo —→ zero

<!--
Which of the following properties remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample:
-->

在此规则存在的情况下，以下哪些属性仍然成立？
对于每个属性，写下 “仍为真” 或 “变为假”。
如果一个属性变为假，请举出一个反例：

<!--
  - Determinism of `step`

  - Progress

  - Preservation
-->

  - `step` 的确定性

  - 进行性

  - 保型性


<!--
#### Quiz
-->

#### 小测验

<!--
Suppose instead that we remove the rule `ξ·₁` from the step
relation. Which of the following properties remain
true in the absence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample:
-->

假设我们从步进关系中移除了规则 `ξ·₁`。
在此规则不存在的情况下，以下哪些属性仍然成立？
对于每个属性，写下 “仍为真” 或 “变为假”。
如果一个属性变为假，请举出一个反例：

<!--
  - Determinism of `step`

  - Progress

  - Preservation
-->

  - `step` 的确定性

  - 进行性

  - 保型性


<!--
#### Quiz
-->

#### 小测验

<!--
We can enumerate all the computable function from naturals to
naturals, by writing out all programs of type `` `ℕ ⇒ `ℕ`` in
lexical order.  Write `fᵢ` for the `i`'th function in this list.
-->

我们可以通过按照字典序写出所有类型为 `` `ℕ ⇒ `ℕ`` 的程序来遍历所有从自然数到自然数的可计算函数。
将这个列表中的第 `i` 个函数写作 `fᵢ`。

<!--
Say we add a typing rule that applies the above enumeration
to interpret a natural as a function from naturals to naturals:
-->

假设我们添加了一个赋性规则，应用上述遍历来将一个自然数解释为一个从自然数到自然数的函数：


    Γ ⊢ L ⦂ `ℕ
    Γ ⊢ M ⦂ `ℕ
    -------------- _·ℕ_
    Γ ⊢ L · M ⦂ `ℕ

<!--
And that we add the corresponding reduction rule:
-->

并且我们添加了相应的归约规则：

    fᵢ(m) —→ n
    ---------- δ
    i · m —→ n

<!--
Which of the following properties remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample:
-->

在此规则存在的情况下，以下哪些属性仍然成立？
对于每个属性，写下 “仍为真” 或 “变为假”。
如果一个属性变为假，请举出一个反例：

<!--
  - Determinism of `step`

  - Progress

  - Preservation
-->

  - `step` 的确定性

  - 进行性

  - 保型性

<!--
Are all properties preserved in this case? Are there any
other alterations we would wish to make to the system?
-->

在这种情况下是否保留了所有属性？
我们是否希望对系统进行任何其他更改？

## Unicode

<!--
This chapter uses the following unicode:
-->

本章使用了下列 Unicode：

    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    Δ  U+0394  GREEK CAPITAL LETTER DELTA (\GD or \Delta)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    δ  U+03B4  GREEK SMALL LETTER DELTA (\Gd or \delta)
    μ  U+03BC  GREEK SMALL LETTER MU (\Gm or \mu)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    ρ  U+03B4  GREEK SMALL LETTER RHO (\Gr or \rho)
    ᵢ  U+1D62  LATIN SUBSCRIPT SMALL LETTER I (\_i)
    ᶜ  U+1D9C  MODIFIER LETTER SMALL C (\^c)
    –  U+2013  EM DASH (\em)
    ₄  U+2084  SUBSCRIPT FOUR (\_4)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ∅  U+2205  EMPTY SET (\0)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ≟  U+225F  QUESTIONED EQUAL TO (\?=)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
