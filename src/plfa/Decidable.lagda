---
title     : "Decidable: 布尔值与判定过程"
layout    : page
prev      : /Quantifiers/
permalink : /Decidable/
next      : /Lists/
translators : ["Fangyi Zhou"]
progress  : 35
---

\begin{code}
module plfa.Decidable where
\end{code}

{::comment}
We have a choice as to how to represent relations:
as an inductive data type of _evidence_ that the relation holds,
or as a function that _computes_ whether the relation holds.
Here we explore the relation between these choices.
We first explore the familiar notion of _booleans_,
but later discover that these are best avoided in favour
of a new notion of _decidable_.
{:/}

我们在如何表示关系上可以有所选择：表示为其成立的*证明*（Evidence）的数据类型，
或者表示为一个*计算*（Compute）其是否成立的函数。我们在此探讨这两个选择直接的关系。
我们首先研究大家熟悉的*布尔值*（Boolean）记法，但是我们之后会发现，我们最好避免布尔值的记法，
而使用一种新的*可决定性*（Decidable）记法。

{::comment}
## Imports
{:/}

## 导入

\begin{code}
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
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Isomorphism using (_⇔_)
\end{code}

{::comment}
## Evidence vs Computation
{:/}

## 证据 vs 计算

{::comment}
Recall that Chapter [Relations][plfa.Relations]
defined comparison as an inductive datatype,
which provides _evidence_ that one number
is less than or equal to another:
{:/}

回忆我们在 [Relations][plfa.Relations] 章节中将比较定义为一个归纳数据类型，
其提供了一个数小于或等于另外一个数的证明：

\begin{code}
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
\end{code}
{::comment}
For example, we can provide evidence that `2 ≤ 4`,
and show there is no possible evidence that `4 ≤ 2`:
{:/}

举例来说，我们提供 `2 ≤ 4` 成立的证明，也可以证明没有 `4 ≤ 2` 成立的证明。

\begin{code}
2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))
\end{code}
{::comment}
The occurrence of `()` attests to the fact that there is
no possible evidence for `2 ≤ 0`, which `z≤n` cannot match
(because `2` is not `zero`) and `s≤s` cannot match
(because `0` cannot match `suc n`).
{:/}

`()` 的出现表明了没有 `2 ≤ 0` 成立的证明：`z≤n` 不能匹配（因为 `2` 不是
`zero`），`s≤s` 也不能匹配（因为 `0` 不能匹配 `suc n`）。

{::comment}
An alternative, which may seem more familiar, is to define a
type of booleans:
{:/}

作为替代的定义，我们可以定义一个大家可能比较熟悉的布尔类型：

\begin{code}
data Bool : Set where
  true  : Bool
  false : Bool
\end{code}
{::comment}
Given booleans, we can define a function of two numbers that
_computes_ to `true` if the comparison holds and to `false` otherwise:
{:/}

给定了布尔类型，我们可以定义一个两个数的函数在比较关系成立时来*计算*出 `true`，
否则计算出 `false`：

\begin{code}
infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n
\end{code}
{::comment}
The first and last clauses of this definition resemble the two
constructors of the corresponding inductive datatype, while the
middle clause arises because there is no possible evidence that
`suc m ≤ zero` for any `m`.
For example, we can compute that `2 ≤ 4` holds,
and we can compute that `4 ≤ 2` does not hold:
{:/}

定义中的第一条与最后一条与归纳数据类型中的两个构造器相对应。因为对于任意的 `m`，不可能出现
`suc m ≤ zero` 的证明，我们使用中间一条定义来表示。
举个例子，我们可以计算 `2 ≤ 4` 成立，也可以计算 `4 ≤ 2` 不成立：

\begin{code}
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
\end{code}
{::comment}
In the first case, it takes two steps to reduce the first argument to zero,
and one more step to compute true, corresponding to the two uses of `s≤s`
and the one use of `z≤n` when providing evidence that `2 ≤ 4`.
In the second case, it takes two steps to reduce the second argument to zero,
and one more step to compute false, corresponding to the two uses of `s≤s`
and the one use of `()` when showing there can be no evidence that `4 ≤ 2`.
{:/}

在第一种情况中，我们需要两步来将第一个参数降低到 0，再用一步来计算出真，这对应着我们需要
使用两次 `s≤s` 和一次 `z≤n` 来证明 `2 ≤ 4`。
在第二种情况中，我们需要两步来将第二个参数降低到 0，再用一步来计算出假，这对应着我们需要
使用两次 `s≤s` 和一次 `()` 来说明没有 `4 ≤ 2` 的证明。

{::comment}
## Relating evidence and computation
{:/}

## 将证明与计算相联系

{::comment}
We would hope to be able to show these two approaches are related, and
indeed we can.  First, we define a function that lets us map from the
computation world to the evidence world:
{:/}

我们希望能够证明这两种方法是有联系的，而我们的确可以。
首先，我们定义一个函数来把计算世界映射到证明世界：

\begin{code}
T : Bool → Set
T true   =  ⊤
T false  =  ⊥
\end{code}
{::comment}
Recall that `⊤` is the unit type which contains the single element `tt`,
and the `⊥` is the empty type which contains no values.  (Also note that
`T` is a capital letter t, and distinct from `⊤`.)  If `b` is of type `Bool`,
then `tt` provides evidence that `T b` holds if `b` is true, while there is
no possible evidence that `T b` holds if `b` is false.
{:/}

回忆到 `⊤` 是只有一个元素 `tt` 的单元类型，`⊥` 是没有值的空类型。（注意 `T` 是大写字母 `t`，
与 `⊤` 不同。）如果 `b` 是 `Bool` 类型的，那么如果 `b` 为真，`tt` 可以提供 `T b` 成立的证明；
如果 `b` 为假，则不可能有 `T b` 成立的证明。

{::comment}
Another way to put this is that `T b` is inhabited exactly when `b ≡ true`
is inhabited.
In the forward direction, we need to do a case analysis on the boolean `b`:
{:/}

换句话说，`T b` 当且仅当 `b ≡ true` 成立时成立。在向前的方向，我们需要针对 `b` 进行情况分析：

\begin{code}
T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt   =  refl
T→≡ false ()
\end{code}
{::comment}
If `b` is true then `T b` is inhabited by `tt` and `b ≡ true` is inhabited
by `refl`, while if `b` is false then `T b` in uninhabited.
{:/}

如果 `b` 为真，那么 `T b` 由 `tt` 证明，`b ≡ true` 由 `refl` 证明。
当 `b` 为家，那么 `T b` 无法证明。

{::comment}
In the reverse direction, there is no need for a case analysis on the boolean `b`:
{:/}

在向后的方向，不需要针对布尔值 `b` 的情况分析：

\begin{code}
≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt
\end{code}
{::comment}
If `b ≡ true` is inhabited by `refl` we know that `b` is `true` and
hence `T b` is inhabited by `tt`.
{:/}

如果 `b ≡ true` 由 `refl` 证明，我们知道 `b` 是 `true`，因此 `T b` 由 `tt` 证明。

{::comment}
Now we can show that `T (m ≤ᵇ n)` is inhabited exactly when `m ≤ n` is inhabited.
{:/}

现在我们可以证明 `T (m ≤ᵇ n)` 当且仅当 `m ≤ n` 成立时成立。

{::comment}
In the forward direction, we consider the three clauses in the definition
of `_≤ᵇ_`:
{:/}

在向前的方向，我们考虑 `_≤ᵇ_` 定义中的三条语句：

\begin{code}
≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero    n       tt  =  z≤n
≤ᵇ→≤ (suc m) zero    ()
≤ᵇ→≤ (suc m) (suc n) t   =  s≤s (≤ᵇ→≤ m n t)
\end{code}
{::comment}
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
{:/}

第一条语句中，我们立即可以得出 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 而得，
相对应地 `m ≤ n` 由 `z≤n` 而证明。在中间的语句中，我们立刻得出 `suc m ≤ᵇ zero` 为假，则
`T (m ≤ᵇ n)` 为空，因此我们无需证明 `m ≤ n`，同时也不存在这样的证明。在最后的语句中，我们对于
`suc m ≤ᵇ suc n` 递归至 `m ≤ᵇ n`。令 `t` 为 `T (suc m ≤ᵇ suc n)` 的证明，如果其存在。
根据 `_≤ᵇ_` 的定义，这也是 `T (m ≤ᵇ n)` 的证明。我们递归地应用函数来获得 `m ≤ n` 的证明，再使用
`s≤s` 将其转换成为 `suc m ≤ suc n` 的证明。

{::comment}
In the reverse direction, we consider the possible forms of evidence
that `m ≤ n`:
{:/}

在向后的方向，我们考虑 `m ≤ n` 成立证明的可能形式：

\begin{code}
≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n        =  tt
≤→≤ᵇ (s≤s m≤n)  =  ≤→≤ᵇ m≤n
\end{code}
{::comment}
If the evidence is `z≤n` then we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`. If the evidence is `s≤s`
applied to `m≤n`, then `suc m ≤ᵇ suc n` reduces to `m ≤ᵇ n`, and we
may recursively invoke the function to produce evidence that `T (m ≤ᵇ n)`.
{:/}

如果证明是 `z≤n`，我们立即可以得到 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 证明。
如果证明是 `s≤s` 作用于 `m≤n`，那么 `suc m ≤ᵇ suc n` 规约到 `m ≤ᵇ n`，我们可以递归地使用函数
来获得 `T (m ≤ᵇ n)` 的证明。

{::comment}
The forward proof has one more clause than the reverse proof,
precisely because in the forward proof we need clauses corresponding to
the comparison yielding both true and false, while in the reverse proof
we only need clauses corresponding to the case where there is evidence
that the comparison holds.  This is exactly why we tend to prefer the
evidence formulation to the computation formulation, because it allows
us to do less work: we consider only cases where the relation holds,
and can ignore those where it does not.
{:/}

向前方向的证明比向后方向的证明多一条语句，因为在向前方向的证明中我们需要考虑比较结果为真和假
的语句，而向后方向的证明只需要考虑比较成立的语句。这也是为什么我们比起计算的形式，更加偏爱证明的形式，
因为这样让我们做更少的工作：我们只需要考虑关系成立时的情况，而可以忽略不成立的情况。

{::comment}
On the other hand, sometimes the computation formulation may be just what
we want.  Given a non-obvious relation over large values, it might be
handy to have the computer work out the answer for us.  Fortunately,
rather than choosing between _evidence_ and _computation_,
there is a way to get the benefits of both.
{:/}

从另一个角度来说，有时计算的性质可能是我们所需要的。给定一个在很多值之上的不显然的关系，
可能使用电脑来计算出答案会更加方便。幸运的是，比起需要自行选择*证明*和*计算*，我们有一种方法来获得
两种方法的优点。

## The best of both worlds

A function that returns a boolean returns exactly a single bit of information:
does the relation hold or does it not? Conversely, the evidence approach tells
us exactly why the relation holds, but we are responsible for generating the
evidence.  But it is easy to define a type that combines the benefits of
both approaches.  It is called `Dec A`, where `Dec` is short for _decidable_:
\begin{code}
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
\end{code}
Like booleans, the type has two constructors.  A value of type `Dec A`
is either of the form `yes x`, where `x` provides evidence that `A` holds,
or of the form `no ¬x`, where `¬x` provides evidence that `A` cannot hold
(that is, `¬x` is a function which given evidence of `A` yields a contradiction).

For example, we define a function `_≤?_` which given two numbers decides whether one
is less than or equal to the other, and provides evidence to justify its conclusion.

First, we introduce two functions useful for constructing evidence that
an inequality does not hold:
\begin{code}
¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n
\end{code}
The first of these asserts that `¬ (suc m ≤ zero)`, and follows by
absurdity, since any evidence of inequality has the form `zero ≤ n`
or `suc m ≤ suc n`, neither of which match `suc m ≤ zero`. The second
of these takes evidence `¬m≤n` of `¬ (m ≤ n)` and returns a proof of
`¬ (suc m ≤ suc n)`.  Any evidence of `suc m ≤ suc n` must have the
form `s≤s m≤n` where `m≤n` is evidence that `m ≤ n`.  Hence, we have
a contradiction, evidenced by `¬m≤n m≤n`.

Using these, it is straightforward to decide an inequality:
\begin{code}
_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                   =  yes z≤n
suc m ≤? zero                =  no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  =  yes (s≤s m≤n)
...               | no ¬m≤n  =  no (¬s≤s ¬m≤n)
\end{code}
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

When we wrote `_≤ᵇ_`, we had to write two other functions, `≤ᵇ→≤` and `≤→≤ᵇ`,
in order to show that it was correct.  In contrast, the definition of `_≤?_`
proves itself correct, as attested to by its type.  The code of `_≤?_`
is far more compact than the combined code of `_≤ᵇ_`, `≤ᵇ→≤`, and `≤→≤ᵇ`.
As we will later show, if you really want the latter three, it is easy
to derive them from `_≤?_`.

We can use our new function to _compute_ the _evidence_ that earlier we had to
think up on our own:
\begin{code}
_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl
\end{code}
You can check that Agda will indeed compute these values.  Typing
`C-c C-n` and providing `2 ≤? 4` or `4 ≤? 2` as the requested expression
causes Agda to print the values given above.

(A subtlety: if we do not define `¬s≤z` and `¬s≤s` as top-level functions,
but instead use inline anonymous functions then Agda may have
trouble normalising evidence of negation.)


#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality:
\begin{code}
postulate
  _<?_ : ∀ (m n : ℕ) → Dec (m < n)
\end{code}

\begin{code}
-- Your code goes here
\end{code}

#### Exercise `_≡ℕ?_`

Define a function to decide whether two naturals are equal:
\begin{code}
postulate
  _≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
\end{code}

\begin{code}
-- Your code goes here
\end{code}


## Decidables from booleans, and booleans from decidables

Curious readers might wonder if we could reuse the definition of
`m ≤ᵇ n`, together with the proofs that it is equivalent to `m ≤ n`, to show
decidability.  Indeed, we can do so as follows:
\begin{code}
_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p
\end{code}
If `m ≤ᵇ n` is true then `≤ᵇ→≤` yields a proof that `m ≤ n` holds,
while if it is false then `≤→≤ᵇ` takes a proof that `m ≤ n` holds into a contradiction.

The triple binding of the `with` clause in this proof is essential.
If instead we wrote:

    _≤?″_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    m ≤?″ n with m ≤ᵇ n
    ... | true   =  yes (≤ᵇ→≤ m n tt)
    ... | false  =  no (≤→≤ᵇ {m} {n})

then Agda would make two complaints, one for each clause:

    ⊤ !=< (T (m ≤ᵇ n)) of type Set
    when checking that the expression tt has type T (m ≤ᵇ n)

    T (m ≤ᵇ n) !=< ⊥ of type Set
    when checking that the expression ≤→≤ᵇ {m} {n} has type ¬ m ≤ n

Putting the expressions into the `with` clause permits Agda to exploit
the fact that `T (m ≤ᵇ n)` is `⊤` when `m ≤ᵇ n` is true, and that
`T (m ≤ᵇ n)` is `⊥` when `m ≤ᵇ n` is false.

However, overall it is simpler to just define `_≤?_` directly, as in the previous
section.  If one really wants `_≤ᵇ_`, then it and its properties are easily derived
from `_≤?_`, as we will now show.

Erasure takes a decidable value to a boolean:
\begin{code}
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false
\end{code}
Using erasure, we can easily derive `_≤ᵇ_` from `_≤?_`:
\begin{code}
_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋
\end{code}

Further, if `D` is a value of type `Dec A`, then `T ⌊ D ⌋` is
inhabited exactly when `A` is inhabited:
\begin{code}
toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x
\end{code}
Using these, we can easily derive that `T (m ≤ᵇ′ n)` is inhabited
exactly when `m ≤ n` is inhabited:
\begin{code}
≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness
\end{code}

In summary, it is usually best to eschew booleans and rely on decidables.
If you need booleans, they and their properties are easily derived from the
corresponding decidables.


## Logical connectives

Most readers will be familiar with the logical connectives for booleans.
Each of these extends to decidables.

The conjunction of two booleans is true if both are true,
and false if either is false:
\begin{code}
infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false
\end{code}
In Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  However, regardless of which matches
the answer is the same.

Correspondingly, given two decidable propositions, we can
decide their conjunction:
\begin{code}
infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }
\end{code}
The conjunction of two propositions holds if they both hold,
and its negation holds if the negation of either holds.
If both hold, then we pair the evidence for each to yield
evidence of the conjunct.  If the negation of either holds,
assuming the conjunct will lead to a contradiction.

Again in Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  This time the answer is different depending
on which matches; if both conjuncts fail to hold we pick the first to
yield the contradiction, but it would be equally valid to pick the second.

The disjunction of two booleans is true if either is true,
and false if both are false:
\begin{code}
infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false
\end{code}
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.

Correspondingly, given two decidable propositions, we can
decide their disjunction:
\begin{code}
infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }
\end{code}
The disjunction of two propositions holds if either holds,
and its negation holds if the negation of both hold.
If either holds, we inject the evidence to yield
evidence of the disjunct.  If the negation of both hold,
assuming either disjunct will lead to a contradiction.

Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; if both disjuncts hold we pick the first,
but it would be equally valid to pick the second.

The negation of a boolean is false if its argument is true,
and vice versa:
\begin{code}
not : Bool → Bool
not true  = false
not false = true
\end{code}
Correspondingly, given a decidable proposition, we
can decide its negation:
\begin{code}
¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x
\end{code}
We simply swap yes and no.  In the first equation,
the right-hand side asserts that the negation of `¬ A` holds,
in other words, that `¬ ¬ A` holds, which is an easy consequence
of the fact that `A` holds.

There is also a slightly less familiar connective,
corresponding to implication:
\begin{code}
_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false
\end{code}
One boolean implies another if
whenever the first is true then the second is true.
Hence, the implication of two booleans is true if
the second is true or the first is false,
and false if the first is true and the second is false.
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.

Correspondingly, given two decidable propositions,
we can decide if the first implies the second:
\begin{code}
_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))
\end{code}
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

Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; but either is equally valid.

#### Exercise `erasure`

Show that erasure relates corresponding boolean and decidable operations:
\begin{code}
postulate
  ∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
  ∨-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
  not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
\end{code}
  
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from 
Chapter [Isomorphism][plfa.Isomorphism#iff],
operation on booleans and decidables, and also show the corresponding erasure:
\begin{code}
postulate
  _iff_ : Bool → Bool → Bool
  _⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
  iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋  
\end{code}

\begin{code}
-- Your code goes here
\end{code}

## Standard Library

\begin{code}
import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
import Data.Nat using (_≤?_)
import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
\end{code}


## Unicode

    ∧  U+2227  LOGICAL AND (\and, \wedge)
    ∨  U+2228  LOGICAL OR (\or, \vee)
    ⊃  U+2283  SUPERSET OF (\sup)
    ᵇ  U+1D47  MODIFIER LETTER SMALL B  (\^b)
    ⌊  U+230A  LEFT FLOOR (\cll)
    ⌋  U+230B  RIGHT FLOOR (\clr)
