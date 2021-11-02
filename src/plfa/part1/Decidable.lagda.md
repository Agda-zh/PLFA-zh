---
title     : "Decidable: 布尔值与判定过程"
layout    : page
prev      : /Quantifiers/
permalink : /Decidable/
next      : /Lists/
translators : ["Fangyi Zhou", "Oshmkufa2010"]
progress  : 100
---

```
module plfa.part1.Decidable where
```

<!--
We have a choice as to how to represent relations:
as an inductive data type of _evidence_ that the relation holds,
or as a function that _computes_ whether the relation holds.
Here we explore the relation between these choices.
We first explore the familiar notion of _booleans_,
but later discover that these are best avoided in favour
of a new notion of _decidable_.
-->

我们有两种不同的方式来表示关系：一是表示为由关系成立的**证明（Evidence）**所构成的数据类型；
二是表示为一个**计算（Compute）**关系是否成立的函数。在本章中，我们将探讨这两种方式之间的关系。
我们首先研究大家熟悉的**布尔值（Boolean）**记法，但是之后我们会发现，相较布尔值记法，
使用一种新的**可判定性（Decidable）**记法将会是更好的选择。

<!--
## Imports
-->

## 导入

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)
```

<!--
## Evidence vs Computation
-->

## 证据 vs 计算

<!--
Recall that Chapter [Relations](/Relations/)
defined comparison as an inductive datatype,
which provides _evidence_ that one number
is less than or equal to another:
-->

回忆我们在 [Relations](/Relations/)
章节中将比较定义为一个归纳数据类型，其提供了一个数小于或等于另外一个数的证明：

```
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
```

<!--
For example, we can provide evidence that `2 ≤ 4`,
and show there is no possible evidence that `4 ≤ 2`:
-->

举例来说，我们提供 `2 ≤ 4` 成立的证明，也可以证明没有 `4 ≤ 2` 成立的证明。

```
2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))
```

<!--
The occurrence of `()` attests to the fact that there is
no possible evidence for `2 ≤ 0`, which `z≤n` cannot match
(because `2` is not `zero`) and `s≤s` cannot match
(because `0` cannot match `suc n`).
-->

`()` 的出现表明了没有 `2 ≤ 0` 成立的证明：`z≤n` 不能匹配（因为 `2` 不是
`zero`），`s≤s` 也不能匹配（因为 `0` 不能匹配 `suc n`）。

<!--
An alternative, which may seem more familiar, is to define a
type of booleans:
-->

作为替代的定义，我们可以定义一个大家可能比较熟悉的布尔类型：

```
data Bool : Set where
  true  : Bool
  false : Bool
```

<!--
Given booleans, we can define a function of two numbers that
_computes_ to `true` if the comparison holds and to `false` otherwise:
-->

给定了布尔类型，我们可以定义一个两个数的函数在比较关系成立时来**计算**出 `true`，
否则计算出 `false`：

```
infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n
```

<!--
The first and last clauses of this definition resemble the two
constructors of the corresponding inductive datatype, while the
middle clause arises because there is no possible evidence that
`suc m ≤ zero` for any `m`.
For example, we can compute that `2 ≤ᵇ 4` holds,
and we can compute that `4 ≤ᵇ 2` does not hold:
-->

定义中的第一条与最后一条与归纳数据类型中的两个构造子相对应。因为对于任意的 `m`，不可能出现
`suc m ≤ zero` 的证明，我们使用中间一条定义来表示。
举个例子，我们可以计算 `2 ≤ᵇ 4` 成立，也可以计算 `4 ≤ᵇ 2` 不成立：

```
_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎
```

<!--
In the first case, it takes two steps to reduce the first argument to zero,
and one more step to compute true, corresponding to the two uses of `s≤s`
and the one use of `z≤n` when providing evidence that `2 ≤ 4`.
In the second case, it takes two steps to reduce the second argument to zero,
and one more step to compute false, corresponding to the two uses of `s≤s`
and the one use of `()` when showing there can be no evidence that `4 ≤ 2`.
-->

在第一种情况中，我们需要两步来将第一个参数降低到 0，再用一步来计算出真，这对应着我们需要
使用两次 `s≤s` 和一次 `z≤n` 来证明 `2 ≤ 4`。
在第二种情况中，我们需要两步来将第二个参数降低到 0，再用一步来计算出假，这对应着我们需要
使用两次 `s≤s` 和一次 `()` 来说明没有 `4 ≤ 2` 的证明。

<!--
## Relating evidence and computation
-->

## 将证明与计算相联系

<!--
We would hope to be able to show these two approaches are related, and
indeed we can.  First, we define a function that lets us map from the
computation world to the evidence world:
-->

我们希望能够证明这两种方法是有联系的，而我们的确可以。
首先，我们定义一个函数来把计算世界映射到证明世界：

```
T : Bool → Set
T true   =  ⊤
T false  =  ⊥
```

<!--
Recall that `⊤` is the unit type which contains the single element `tt`,
and the `⊥` is the empty type which contains no values.  (Also note that
`T` is a capital letter t, and distinct from `⊤`.)  If `b` is of type `Bool`,
then `tt` provides evidence that `T b` holds if `b` is true, while there is
no possible evidence that `T b` holds if `b` is false.
-->

回忆到 `⊤` 是只有一个元素 `tt` 的单元类型，`⊥` 是没有值的空类型。（注意 `T` 是大写字母 `t`，
与 `⊤` 不同。）如果 `b` 是 `Bool` 类型的，那么如果 `b` 为真，`tt` 可以提供 `T b` 成立的证明；
如果 `b` 为假，则不可能有 `T b` 成立的证明。

<!--
Another way to put this is that `T b` is inhabited exactly when `b ≡ true`
is inhabited.
In the forward direction, we need to do a case analysis on the boolean `b`:
-->

换句话说，`T b` 当且仅当 `b ≡ true` 成立时成立。在向前的方向，我们需要针对 `b` 进行情况分析：

```
T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt   =  refl
T→≡ false ()
```

<!--
If `b` is true then `T b` is inhabited by `tt` and `b ≡ true` is inhabited
by `refl`, while if `b` is false then `T b` in uninhabited.
-->

如果 `b` 为真，那么 `T b` 由 `tt` 证明，`b ≡ true` 由 `refl` 证明。
当 `b` 为假，那么 `T b` 无法证明。

<!--
In the reverse direction, there is no need for a case analysis on the boolean `b`:
-->

在向后的方向，不需要针对布尔值 `b` 的情况分析：

```
≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt
```

<!--
If `b ≡ true` is inhabited by `refl` we know that `b` is `true` and
hence `T b` is inhabited by `tt`.
-->

如果 `b ≡ true` 由 `refl` 证明，我们知道 `b` 是 `true`，因此 `T b` 由 `tt` 证明。

<!--
Now we can show that `T (m ≤ᵇ n)` is inhabited exactly when `m ≤ n` is inhabited.
-->

现在我们可以证明 `T (m ≤ᵇ n)` 当且仅当 `m ≤ n` 成立时成立。

<!--
In the forward direction, we consider the three clauses in the definition
of `_≤ᵇ_`:
-->

在向前的方向，我们考虑 `_≤ᵇ_` 定义中的三条语句：

```
≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero    n       tt  =  z≤n
≤ᵇ→≤ (suc m) zero    ()
≤ᵇ→≤ (suc m) (suc n) t   =  s≤s (≤ᵇ→≤ m n t)
```

<!--
In the first clause, we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`, and correspondingly `m ≤ n` is
evidenced by `z≤n`. In the middle clause, we immediately have that
`suc m ≤ᵇ zero` is false, and hence `T (m ≤ᵇ n)` is empty, so we need
not provide evidence that `m ≤ n`, which is just as well since there is no
such evidence.  In the last clause, we have that `suc m ≤ᵇ suc n` recurses
to `m ≤ᵇ n`.  We let `t` be the evidence of `T (suc m ≤ᵇ suc n)` if it exists,
which, by definition of `_≤ᵇ_`, will also be evidence of `T (m ≤ᵇ n)`.
We recursively invoke the function to get evidence that `m ≤ n`, which
`s≤s` converts to evidence that `suc m ≤ suc n`.
-->

第一条语句中，我们立即可以得出 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 而得，
相对应地 `m ≤ n` 由 `z≤n` 而证明。在中间的语句中，我们立刻得出 `suc m ≤ᵇ zero` 为假，则
`T (m ≤ᵇ n)` 为空，因此我们无需证明 `m ≤ n`，同时也不存在这样的证明。在最后的语句中，我们对于
`suc m ≤ᵇ suc n` 递归至 `m ≤ᵇ n`。令 `t` 为 `T (suc m ≤ᵇ suc n)` 的证明，如果其存在。
根据 `_≤ᵇ_` 的定义，这也是 `T (m ≤ᵇ n)` 的证明。我们递归地应用函数来获得 `m ≤ n` 的证明，再使用
`s≤s` 将其转换成为 `suc m ≤ suc n` 的证明。

<!--
In the reverse direction, we consider the possible forms of evidence
that `m ≤ n`:
-->

在向后的方向，我们考虑 `m ≤ n` 成立证明的可能形式：

```
≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n        =  tt
≤→≤ᵇ (s≤s m≤n)  =  ≤→≤ᵇ m≤n
```

<!--
If the evidence is `z≤n` then we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`. If the evidence is `s≤s`
applied to `m≤n`, then `suc m ≤ᵇ suc n` reduces to `m ≤ᵇ n`, and we
may recursively invoke the function to produce evidence that `T (m ≤ᵇ n)`.
-->

如果证明是 `z≤n`，我们立即可以得到 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 证明。
如果证明是 `s≤s` 作用于 `m≤n`，那么 `suc m ≤ᵇ suc n` 规约到 `m ≤ᵇ n`，我们可以递归地使用函数
来获得 `T (m ≤ᵇ n)` 的证明。

<!--
The forward proof has one more clause than the reverse proof,
precisely because in the forward proof we need clauses corresponding to
the comparison yielding both true and false, while in the reverse proof
we only need clauses corresponding to the case where there is evidence
that the comparison holds.  This is exactly why we tend to prefer the
evidence formulation to the computation formulation, because it allows
us to do less work: we consider only cases where the relation holds,
and can ignore those where it does not.
-->

向前方向的证明比向后方向的证明多一条语句，因为在向前方向的证明中我们需要考虑比较结果为真和假
的语句，而向后方向的证明只需要考虑比较成立的语句。这也是为什么我们比起计算的形式，更加偏爱证明的形式，
因为这样让我们做更少的工作：我们只需要考虑关系成立时的情况，而可以忽略不成立的情况。

<!--
On the other hand, sometimes the computation formulation may be just what
we want.  Given a non-obvious relation over large values, it might be
handy to have the computer work out the answer for us.  Fortunately,
rather than choosing between _evidence_ and _computation_,
there is a way to get the benefits of both.
-->

从另一个角度来说，有时计算的性质可能正是我们所需要的。面对一个大数值上的非显然关系，
使用电脑来计算出答案可能会更加方便。幸运的是，比起在**证明**或**计算**之中犹豫，
我们有一种更好的方法来兼取其优。

<!--
## The best of both worlds
-->

## 取二者之精华 {name=the-best-of-both-worlds}

<!--
A function that returns a boolean returns exactly a single bit of information:
does the relation hold or does it not? Conversely, the evidence approach tells
us exactly why the relation holds, but we are responsible for generating the
evidence.  But it is easy to define a type that combines the benefits of
both approaches.  It is called `Dec A`, where `Dec` is short for _decidable_:
-->

一个返回布尔值的函数提供恰好一比特的信息：这个关系成立或是不成立。相反地，证明的形式告诉我们
为什么这个关系成立，但却需要我们自行完成这个证明。不过，我们其实可以简单地定义一个类型来取二者之精华。
我们把它叫做：`Dec A`，其中 `Dec` 是**可判定的（Decidable）**的意思。

```
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
```

<!--
Like booleans, the type has two constructors.  A value of type `Dec A`
is either of the form `yes x`, where `x` provides evidence that `A` holds,
or of the form `no ¬x`, where `¬x` provides evidence that `A` cannot hold
(that is, `¬x` is a function which given evidence of `A` yields a contradiction).
-->

正如布尔值，这个类型有两个构造子。一个 `Dec A` 类型的值要么是以 `yes x` 的形式，其中 `x` 提供 `A`
成立的证明，或者是以 `no ¬x` 的形式，其中 `x` 提供了 `A` 无法成立的证明。（也就是说，`¬x` 是一个给定
`A` 成立的证据，返回矛盾的函数）

<!--
For example, we define a function `_≤?_` which given two numbers decides whether one
is less than or equal to the other, and provides evidence to justify its conclusion.
-->

比如说，我们定义一个函数 `_≤?_`，给定两个数，判定是否一个数小于等于另一个，并提供证明来说明结论。

<!--
First, we introduce two functions useful for constructing evidence that
an inequality does not hold:
-->

首先，我们使用两个有用的函数，用于构造不等式不成立的证明：

```
¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n
```

<!--
The first of these asserts that `¬ (suc m ≤ zero)`, and follows by
absurdity, since any evidence of inequality has the form `zero ≤ n`
or `suc m ≤ suc n`, neither of which match `suc m ≤ zero`. The second
of these takes evidence `¬m≤n` of `¬ (m ≤ n)` and returns a proof of
`¬ (suc m ≤ suc n)`.  Any evidence of `suc m ≤ suc n` must have the
form `s≤s m≤n` where `m≤n` is evidence that `m ≤ n`.  Hence, we have
a contradiction, evidenced by `¬m≤n m≤n`.
-->

第一个函数断言了 `¬ (suc m ≤ zero)`，由荒谬可得。因为每个不等式的成立证明必须是
`zero ≤ n` 或者 `suc m ≤ suc n` 的形式，两者都无法匹配 `suc m ≤ zero`。
第二个函数取 `¬ (m ≤ n)` 的证明 `¬m≤n`，返回 `¬ (suc m ≤ suc n)` 的证明。
所有形如 `suc m ≤ suc n` 的证明必须是以 `s≤s m≤n` 的形式给出。因此我们可以构造一个
矛盾，以 `¬m≤n m≤n` 来证明。

<!--
Using these, it is straightforward to decide an inequality:
-->

使用这些，我们可以直接的判定不等关系：

```
_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                   =  yes z≤n
suc m ≤? zero                =  no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  =  yes (s≤s m≤n)
...               | no ¬m≤n  =  no (¬s≤s ¬m≤n)
```

<!--
As with `_≤ᵇ_`, the definition has three clauses.  In the first
clause, it is immediate that `zero ≤ n` holds, and it is evidenced by
`z≤n`.  In the second clause, it is immediate that `suc m ≤ zero` does
not hold, and it is evidenced by `¬s≤z`.
In the third clause, to decide whether `suc m ≤ suc n` holds we
recursively invoke `m ≤? n`.  There are two possibilities.  In the
`yes` case it returns evidence `m≤n` that `m ≤ n`, and `s≤s m≤n`
provides evidence that `suc m ≤ suc n`.  In the `no` case it returns
evidence `¬m≤n` that `¬ (m ≤ n)`, and `¬s≤s ¬m≤n` provides evidence
that `¬ (suc m ≤ suc n)`.
-->

与 `_≤ᵇ_` 一样，定义有三条语句。第一条语句中，`zero ≤ n` 立即成立，由 `z≤n` 证明。
第二条语句中，`suc m ≤ zero` 立即不成立，由 `¬s≤z` 证明。
第三条语句中，我们需要递归地应用 `m ≤? n`。有两种可能性，在 `yes` 的情况中，它会返回
`m ≤ n` 的证明 `m≤n`，所以 `s≤s m≤n` 即可作为 `suc m ≤ suc n` 的证明；在 `no` 的情况中，
它会返回 `¬ (m ≤ n)` 的证明 `¬m≤n`，所以 `¬s≤s ¬m≤n` 即可作为 `¬ (suc m ≤ suc n)` 的证明。

<!--
When we wrote `_≤ᵇ_`, we had to write two other functions, `≤ᵇ→≤` and `≤→≤ᵇ`,
in order to show that it was correct.  In contrast, the definition of `_≤?_`
proves itself correct, as attested to by its type.  The code of `_≤?_`
is far more compact than the combined code of `_≤ᵇ_`, `≤ᵇ→≤`, and `≤→≤ᵇ`.
As we will later show, if you really want the latter three, it is easy
to derive them from `_≤?_`.
-->

当我们写 `_≤ᵇ_` 时，我们必须写两个其他的函数 `≤ᵇ→≤` 和 `≤→≤ᵇ` 来证明其正确性。
作为对比，`_≤?_` 的定义自身就证明了其正确性，由类型即可得知。`_≤?_` 的代码也比
`_≤ᵇ_`、`≤ᵇ→≤` 和 `≤→≤ᵇ` 加起来要简洁的多。我们稍后将会证明，如果我们需要后三者，
我们亦可简单地从 `_≤?_` 中派生出来。

<!--
We can use our new function to _compute_ the _evidence_ that earlier we had to
think up on our own:
-->

我们可以使用我们新的函数来**计算**出我们之前需要自己想出来的**证明**。

```
_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl
```

<!--
You can check that Agda will indeed compute these values.  Typing
`C-c C-n` and providing `2 ≤? 4` or `4 ≤? 2` as the requested expression
causes Agda to print the values given above.
-->

你可以验证 Agda 的确计算出了这些值。输入 `C-c C-n` 并给出 `2 ≤? 4` 或者 `4 ≤? 2` 作为
需要的表达式，Agda 会输出如上的值。

<!--
(A subtlety: if we do not define `¬s≤z` and `¬s≤s` as top-level functions,
but instead use inline anonymous functions then Agda may have
trouble normalising evidence of negation.)
-->

（小细节：如果我们不把 `¬s≤z` 和 `¬s≤s` 作为顶层函数来定义，而是使用内嵌的匿名函数，
Agda 可能会在规范化否定的证明中出现问题。）


<!--
#### Exercise `_<?_` (recommended)
-->

#### 练习 `_<?_` （推荐）

<!--
Analogous to the function above, define a function to decide strict inequality:
-->

与上面的函数相似，定义一个判定严格不等性的函数：

```
postulate
  _<?_ : ∀ (m n : ℕ) → Dec (m < n)
```

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
#### Exercise `_≡ℕ?_` (practice)
-->

#### 练习 `_≡ℕ?_`（实践）

<!--
Define a function to decide whether two naturals are equal:
-->

定义一个函数来判定两个自然数是否相等。

```
postulate
  _≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
```

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
## Decidables from booleans, and booleans from decidables
-->

## 从可判定的值到布尔值，从布尔值到可判定的值 {name=decidables-from-booleans-and-booleans-from-decidables}

<!--
Curious readers might wonder if we could reuse the definition of
`m ≤ᵇ n`, together with the proofs that it is equivalent to `m ≤ n`, to show
decidability.  Indeed, we can do so as follows:
-->

好奇的读者可能会思考能不能重用 `m ≤ᵇ n` 的定义，加上它与 `m ≤ n` 等价的证明，
来证明可判定性。的确，我们是可以做到的：

```
_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p
```

<!--
If `m ≤ᵇ n` is true then `≤ᵇ→≤` yields a proof that `m ≤ n` holds,
while if it is false then `≤→≤ᵇ` takes a proof that `m ≤ n` holds into a contradiction.
-->

如果 `m ≤ᵇ n` 为真，那么 `≤ᵇ→≤` 会返回一个 `m ≤ n` 成立的证明。
如果 `m ≤ᵇ n` 为假，那么 `≤→≤ᵇ` 会取一个 `m ≤ n` 成立的证明，将其转换为一个矛盾。

<!--
The triple binding of the `with` clause in this proof is essential.
If instead we wrote:
-->

在这个证明中，`with` 语句的三重约束是必须的。如果我们取而代之的写：

    _≤?″_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    m ≤?″ n with m ≤ᵇ n
    ... | true   =  yes (≤ᵇ→≤ m n tt)
    ... | false  =  no (≤→≤ᵇ {m} {n})

<!--
then Agda would make two complaints, one for each clause:
-->

那么 Agda 对于每条语句会有一个抱怨：

    ⊤ !=< (T (m ≤ᵇ n)) of type Set
    when checking that the expression tt has type T (m ≤ᵇ n)

    T (m ≤ᵇ n) !=< ⊥ of type Set
    when checking that the expression ≤→≤ᵇ {m} {n} has type ¬ m ≤ n

<!--
Putting the expressions into the `with` clause permits Agda to exploit
the fact that `T (m ≤ᵇ n)` is `⊤` when `m ≤ᵇ n` is true, and that
`T (m ≤ᵇ n)` is `⊥` when `m ≤ᵇ n` is false.
-->

将表达式放在 `with` 语句中能让 Agda 利用下列事实：当 `m ≤ᵇ n` 为真时，`T (m ≤ᵇ n)` 是
`⊤`；当 `m ≤ᵇ n` 为假时，`T (m ≤ᵇ n)` 是 `⊥`。

<!--
However, overall it is simpler to just define `_≤?_` directly, as in the previous
section.  If one really wants `_≤ᵇ_`, then it and its properties are easily derived
from `_≤?_`, as we will now show.
-->

然而，总体来说还是直接定义 `_≤?_` 比较方便，正如之前部分中那样。如果有人真的很需要 `_≤ᵇ_`，
那么它和它的性质可以简单地从 `_≤?_` 中派生出来，正如我们接下来要展示的一样。

<!--
Erasure takes a decidable value to a boolean:
-->

擦除（Erasure）将一个可判定的值转换为一个布尔值：

```
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false
```

<!--
Using erasure, we can easily derive `_≤ᵇ_` from `_≤?_`:
-->

使用擦除，我们可以简单地从 `_≤?_` 中派生出 `_≤ᵇ_`：

```
_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋
```

<!--
Further, if `D` is a value of type `Dec A`, then `T ⌊ D ⌋` is
inhabited exactly when `A` is inhabited:
-->

更进一步来说，如果 `D` 是一个类型为 `Dec A` 的值，那么 `T ⌊ D ⌋`
当且仅当 `A` 成立时成立：
```
toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x
```

<!--
Using these, we can easily derive that `T (m ≤ᵇ′ n)` is inhabited
exactly when `m ≤ n` is inhabited:
-->

使用这些，我们可以简单地派生出 `T (m ≤ᵇ′ n)` 当且仅当 `m ≤ n` 成立时成立。

```
≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness
```

<!--
In summary, it is usually best to eschew booleans and rely on decidables.
If you need booleans, they and their properties are easily derived from the
corresponding decidables.
-->

总结来说，最好避免直接使用布尔值，而使用可判定的值。如果有需要布尔值的时候，它们和它们的性质
可以简单地从对应的可判定的值中派生而来。


<!--
## Logical connectives
-->

<!--
Most readers will be familiar with the logical connectives for booleans.
Each of these extends to decidables.
-->

大多数读者对于布尔值的逻辑运算符很熟悉了。每个逻辑运算符都可以被延伸至可判定的值。

<!--
The conjunction of two booleans is true if both are true,
and false if either is false:
-->

两个布尔值的合取当两者都为真时为真，当任一为假时为假：

```
infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false
```

<!--
In Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  However, regardless of which matches
the answer is the same.
-->

在 Emacs 中，第三个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第二条还是第三条
会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

<!--
Correspondingly, given two decidable propositions, we can
decide their conjunction:
-->

相应地，给定两个可判定的命题，我们可以判定它们的合取：

```
infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }
```

<!--
The conjunction of two propositions holds if they both hold,
and its negation holds if the negation of either holds.
If both hold, then we pair the evidence for each to yield
evidence of the conjunct.  If the negation of either holds,
assuming the conjunct will lead to a contradiction.
-->

两个命题的合取当两者都成立时成立，其否定则当任意一者否定成立时成立。如果两个都成立，
我们将每一证明放入数据对中，作为合取的证明。如果任意一者的否定成立，假设整个合取将会引入一个矛盾。

<!--
Again in Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  This time the answer is different depending
on which matches; if both conjuncts fail to hold we pick the first to
yield the contradiction, but it would be equally valid to pick the second.
-->

同样地，在 Emacs 中，第三条等式在左手边以灰色显示，说明等式的顺序决定了第二条还是第三条会被匹配。
这一次，我们给出的结果会因为是第二条还是第三条而不一样。如果两个命题都不成立，我们选择第一个来构造矛盾，
但选择第二个也是同样正确的。

<!--
The disjunction of two booleans is true if either is true,
and false if both are false:
-->

两个布尔值的析取当任意为真时为真，当两者为假时为假：

```
infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false
```

<!--
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.
-->

在 Emacs 中，第二个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第一条还是第二条
会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

<!--
Correspondingly, given two decidable propositions, we can
decide their disjunction:
-->

相应地，给定两个可判定的命题，我们可以判定它们的析取：

```
infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }
```

<!--
The disjunction of two propositions holds if either holds,
and its negation holds if the negation of both hold.
If either holds, we inject the evidence to yield
evidence of the disjunct.  If the negation of both hold,
assuming either disjunct will lead to a contradiction.
-->

两个命题的析取当任意一者成立时成立，其否定则当两者的否定成立时成立。如果任意一者成立，
我们使用其证明来作为析取的证明。如果两个的否定都成立，假设任意一者都会引入一个矛盾。

<!--
Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; if both disjuncts hold we pick the first,
but it would be equally valid to pick the second.
-->

同样地，在 Emacs 中，第二条等式在左手边以灰色显示，说明等式的顺序决定了第一条还是第二条会被匹配。
这一次，我们给出的结果会因为是第二条还是第三条而不一样。如果两个命题都成立，我们选择第一个来构造析取，
但选择第二个也是同样正确的。

<!--
The negation of a boolean is false if its argument is true,
and vice versa:
-->

一个布尔值的否定当值为真时为假，反之亦然：

```
not : Bool → Bool
not true  = false
not false = true
```

<!--
Correspondingly, given a decidable proposition, we
can decide its negation:
-->

相应地，给定一个可判定的命题，我们可以判定它的否定：

```
¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x
```

<!--
We simply swap yes and no.  In the first equation,
the right-hand side asserts that the negation of `¬ A` holds,
in other words, that `¬ ¬ A` holds, which is an easy consequence
of the fact that `A` holds.
-->

我们直接把 yes 和 no 交换。在第一个等式中，右手边断言了 `¬ A` 的否定成立，也就是说
`¬ ¬ A` 成立——这是一个 `A` 成立时可以简单得到的推论。

<!--
There is also a slightly less familiar connective,
corresponding to implication:
-->

还有一个与蕴涵相对应，但是稍微不那么知名的运算符：

```
_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false
```

<!--
One boolean implies another if
whenever the first is true then the second is true.
Hence, the implication of two booleans is true if
the second is true or the first is false,
and false if the first is true and the second is false.
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.
-->

当任何一个布尔值为真的时候，另一个布尔值恒为真，我们成为第一个布尔值蕴涵第二个布尔值。
因此，两者的蕴涵在第二个为真或者第一个为假时为真，在第一个为真而第二个为假时为假。
在 Emacs 中，第二个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第一条还是第二条
会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

<!--
Correspondingly, given two decidable propositions,
we can decide if the first implies the second:
-->

相应地，给定两个可判定的命题，我们可以判定它们的析取：

```
_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))
```

<!--
The implication holds if either the second holds or
the negation of the first holds, and its negation
holds if the first holds and the negation of the second holds.
Evidence for the implication is a function from evidence
of the first to evidence of the second.
If the second holds, the function returns the evidence for it.
If the negation of the first holds, the function takes the
evidence of the first and derives a contradiction.
If the first holds and the negation of the second holds,
given evidence of the implication we must derive a contradiction;
we apply the evidence of the implication `f` to the evidence of the
first `x`, yielding a contradiction with the evidence `¬y` of
the negation of the second.
-->

两者的蕴涵在第二者成立或者第一者的否定成立时成立，其否定在第一者成立而第二者否定成立时成立。
蕴涵成立的证明是一个从第一者成立的证明到第二者成立的证明的函数。如果第二者成立，那么这个函数
直接返回第二者的证明。如果第一者的否定成立，那么使用第一者成立的证明，构造一个矛盾。
如果第一者成立，第二者不成立，给定蕴涵成立的证明，我们必须构造一个矛盾：我们将成立的证明 `f`
应用于第一者成立的证明 `x`，再加以第二者否定成立的证明 `¬y` 来构造矛盾。

<!--
Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; but either is equally valid.
-->

同样地，在 Emacs 中，第二条等式在左手边以灰色显示，说明等式的顺序决定了第一条还是第二条会被匹配。
这一次，我们给出的结果会因为是哪一条被匹配而不一样，但两者都是同样正确的。

<!--
#### Exercise `erasure` (practice)
-->

#### 练习 `erasure`（实践）

<!--
Show that erasure relates corresponding boolean and decidable operations:
-->

证明擦除将对应的布尔值和可判定的值的操作联系了起来：

```
postulate
  ∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
  ∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
  not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
```

<!--
#### Exercise `iff-erasure` (recommended)
-->

#### 练习 `iff-erasure` （推荐）

<!--
Give analogues of the `_⇔_` operation from
Chapter [Isomorphism](/Isomorphism/#iff),
operation on booleans and decidables, and also show the corresponding erasure:
-->

给出与[同构与嵌入](/Isomorphism/#iff)章节中 `_↔_` 相对应的布尔值与可判定的值的操作，
并证明其对应的擦除：

```
postulate
  _iff_ : Bool → Bool → Bool
  _⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
  iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
```

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
## Proof by reflection {name=proof-by-reflection}
-->

## 互映证明 {name=proof-by-reflection}

<!--
Let's revisit our definition of monus from
Chapter [Naturals](/Naturals/).
If we subtract a larger number from a smaller number, we take the result to be
zero. We had to do something, after all. What could we have done differently? We
could have defined a *guarded* version of minus, a function which subtracts `n`
from `m` only if `n ≤ m`:
-->

让我们回顾一下章节[自然数](/Naturals/)中 `monus` 的定义。
如果从一个较小的数中减去一个较大的数，结果为零。毕竟我们总是要得到一个结果。
我们可以用其他方式定义吗？可以定义一版带有**守卫（guarded）**的减法──只有当 `n ≤ m` 时才能从 `m` 中减去 `n` ：

```
minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m
```

<!--
Unfortunately, it is painful to use, since we have to explicitly provide
the proof that `n ≤ m`:
-->

然而这种定义难以使用，因为我们必须显式地为 `n ≤ m` 提供证明：

```
_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl
```

<!--
We cannot solve this problem in general, but in the scenario above, we happen to
know the two numbers *statically*. In that case, we can use a technique called
*proof by reflection*. Essentially, we can ask Agda to run the decidable
equality `n ≤? m` while type checking, and make sure that `n ≤ m`!
-->

这个问题没有通用的解决方案，但是在上述的情景下，我们恰好**静态地**知道这两个数字。这种情况下，我们可以使用一种被称为**互映证明（proof by reflection）**的技术。
实质上，在类型检查的时候我们可以让 Agda 运行可判定的等式 `n ≤? m` 并且保证 `n ≤ m`！

<!--
We do this by using a feature of implicits. Agda will fill in an implicit of a
record type if it can fill in all its fields. So Agda will *always* manage to
fill in an implicit of an *empty* record type, since there aren't any fields
after all. This is why `⊤` is defined as an empty record.
-->

我们使用「隐式参数」的一个特性来实现这个功能。如果 Agda 可以填充一个记录类型的所有字段，那么 Agda 就可以填充此记录类型的隐式参数。
由于空记录类型没有任何字段，Agda 总是会设法填充空记录类型的隐式参数。这就是 `⊤` 类型被定义成空记录的原因。

<!--
The trick is to have an implicit argument of the type `T ⌊ n ≤? m ⌋`. Let's go
through what this means step-by-step. First, we run the decision procedure,
`n ≤? m`. This provides us with evidence whether `n ≤ m` holds or not. We erase the
evidence to a boolean. Finally, we apply `T`. Recall that `T` maps booleans into
the world of evidence: `true` becomes the unit type `⊤`, and `false` becomes the
empty type `⊥`. Operationally, an implicit argument of this type works as a
guard.
-->

这里的技巧是设置一个类型为 `T ⌊ n ≤? m ⌋` 的隐式参数。让我们一步一步阐述这句话的含义。
首先，我们运行判定过程 `n ≤? m`。它向我们提供了 `n ≤ m` 是否成立的证据。我们擦除证据得到布尔值。
最后，我们应用 `T`。回想一下，`T` 将布尔值映射到证据的世界：`true` 变成了单位类型 `⊤`，
`false` 变成了空类型 `⊥` 。在操作上，这个类型的隐式参数起到了守卫的作用。

<!--
- If `n ≤ m` holds, the type of the implicit value reduces to `⊤`. Agda then
  happily provides the implicit value.
- Otherwise, the type reduces to `⊥`, which Agda has no chance of providing, so
  it will throw an error. For instance, if we call `3 - 5` we get `_n≤m_254 : ⊥`.
-->

- 如果 `n ≤ m` 成立，隐式参数的类型规约为 `⊤`。 然后 Agda 会欣然地提供隐式参数。
- 否则，类型规约为 `⊥` ，Agda 无法为此类型提供对应的值，因此会报错。例如，如果我们调用 `3 - 5` 会得到 `_n≤m_254 : ⊥`。

<!--
We obtain the witness for `n ≤ m` using `toWitness`, which we defined earlier:
-->

我们使用之前定义的 `toWitness` 获得了 `n ≤ m` 的证据：

```
_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)
```

<!--
We can safely use `_-_` as long as we statically know the two numbers:
-->

我们现在只要能静态地知道这两个数就可以安全地使用 `_-_` 了：

```
_ : 5 - 3 ≡ 2
_ = refl
```

<!--
It turns out that this idiom is very common. The standard library defines a
synonym for `T ⌊ ? ⌋` called `True`:
-->

事实上，这种惯用语法非常普遍。标准库为 `T ⌊ ? ⌋` 定义了叫做 `True` 的同义词：

```
True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋
```
<!--
#### Exercise `False`
-->

#### 练习 `False`

<!--
Give analogues of `True`, `toWitness`, and `fromWitness` which work with *negated* properties. Call these `False`, `toWitnessFalse`, and `fromWitnessFalse`.
-->

给出 `True`，`toWitness` 和 `fromWitness` 的**相反**定义。分别称为 `False`，`toWitnessFalse` 和 `fromWitnessFalse`。

<!--
## Standard Library
-->

## 标准库

```
import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
import Data.Nat using (_≤?_)
import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)
```


## Unicode

<!--
    ∧  U+2227  LOGICAL AND (\and, \wedge)
    ∨  U+2228  LOGICAL OR (\or, \vee)
    ⊃  U+2283  SUPERSET OF (\sup)
    ᵇ  U+1D47  MODIFIER LETTER SMALL B  (\^b)
    ⌊  U+230A  LEFT FLOOR (\clL)
    ⌋  U+230B  RIGHT FLOOR (\clR)
-->

    ∧  U+2227  逻辑和 (\and, \wedge)
    ∨  U+2228  逻辑或 (\or, \vee)
    ⊃  U+2283  超集 (\sup)
    ᵇ  U+1D47  修饰符小写 B  (\^b)
    ⌊  U+230A  左向下取整 (\clL)
    ⌋  U+230B  右向下取整 (\clR)
