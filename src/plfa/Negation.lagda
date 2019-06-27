---
title     : "Negation: 直觉逻辑与命题逻辑中的否定"
layout    : page
prev      : /Connectives/
permalink : /Negation/
next      : /Quantifiers/
---

\begin{code}
module plfa.Negation where
\end{code}

{::comment}
This chapter introduces negation, and discusses intuitionistic
and classical logic.
{:/}

本章介绍了否定的性质，讨论了直觉逻辑和经典逻辑。

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import plfa.Isomorphism using (_≃_; extensionality)
\end{code}


{::comment}
## Negation
{:/}

## 否定

{::comment}
Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false:
{:/}

给定命题 `A`，当 `A` 不成立时，它的否定形式 `¬ A` 成立。
我们将否定阐述为「蕴含假」来形式化此概念。

\begin{code}
¬_ : Set → Set
¬ A = A → ⊥
\end{code}

{::comment}
This is a form of _proof by contradiction_: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.
{:/}

这是一种**反证法（proof by contradiction）**的形式：若从 `A` 可得出结论 `⊥`（即矛盾），
则 `¬ A` 必定成立。

{::comment}
Evidence that `¬ A` holds is of the form
{:/}

`¬ A` 成立的证据的形式为：

    λ{ x → N }

{::comment}
where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.
{:/}

其中 `N` 是类型为 `⊥` 的项，它包含类型为 `A` 的自由变量 `x`。换言之，`¬ A` 成立
的证据是一个函数，该函数将 `A` 成立的证据转换为 `⊥` 成立的证据。

{::comment}
Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction:
{:/}

给定 `¬ A` 和 `A` 均成立的证据，我们可以得出 `⊥` 成立。换言之，若 `¬ A` 和 `A` 均成立，
那么我们就得到了矛盾：

\begin{code}
¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x
\end{code}

{::comment}
Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.
{:/}

在这里，我们将 `¬ A` 的证据写作 `¬x`，将 `A` 的证据写作 `x`。这表示 `¬x` 必须是类型为 `A → ⊥`
的函数，因此应用 `¬x x` 的类型必为 `⊥`。注意此规则只是 `→-elim` 的一个特例。

{::comment}
We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else:
{:/}

我们将否定的优先级设定为高于析取和合取，但低于其它运算：

\begin{code}
infix 3 ¬_
\end{code}

{::comment}
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.
{:/}

因此，`¬ A × ¬ B` 会解析为 `(¬ A) × (¬ B)`，而 `¬ m ≡ n` 会解析为 `¬ (m ≡ n)`。

{::comment}
In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`:
{:/}

在**经典逻辑**中，`A` 等价于 `¬ ¬ A`。而如前文所述，Agda 中使用了**直觉逻辑**，
因此我们只有该等价关系的一半，即 `A` 蕴含 `¬ ¬ A`：

\begin{code}
¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}
\end{code}

{::comment}
Let `x` be evidence of `A`. We show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.
{:/}

令 `x` 为 `A` 的证据。我们要证明若假定 `¬ A` 成立，则会导出矛盾，因此 `¬ ¬ A`
必定成立。令 `¬x` 为 `¬ A` 的证据。那么以 `¬x x` 为证据，从 `A` 和 `¬ A` 可以导出矛盾。
这样我们就证明了 `¬ ¬ A`。

{::comment}
An equivalent way to write the above is as follows:
{:/}

以上描述的等价写法如下：

\begin{code}
¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x
\end{code}

{::comment}
Here we have simply converted the argument of the lambda term
to an additional argument of the function.  We will usually
use this latter style, as it is more compact.
{:/}

在这里我们简单地将 λ-项的参数转换成了该函数的附加参数。
我们通常会使用后面这种形式，因为它更加紧凑。

{::comment}
We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`:
{:/}

我们无法证明 `¬ ¬ A` 蕴含 `A`，但可以证明 `¬ ¬ ¬ A` 蕴含 `¬ A`：

\begin{code}
¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)
\end{code}

{::comment}
Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.
{:/}

令 `¬¬¬x` 为 `¬ ¬ ¬ A` 的证据。我们要证明若假定 `A` 成立就会导出矛盾，
因此 `¬ A` 必定成立。令 `x` 为 `A` 的证据。根据前面的结果，以 `¬¬-intro x`
为证据可得出结论 `¬ ¬ A`。根据 `¬¬¬x (¬¬-intro x)`，我们可从
`¬ ¬ ¬ A` 和 `¬ ¬ A` 导出矛盾。这样我们就证明了 `¬ A`。

{::comment}
Another law of logic is _contraposition_,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`:
{:/}

另一个逻辑规则是**换质换位律（contraposition）**，它陈述了若 `A` 蕴含 `B`，
则 `¬ B` 蕴含 `¬ A`：

\begin{code}
contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)
\end{code}

{::comment}
Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence `¬ A`
must hold. Let `x` be evidence of `A`.  Then from `A → B` and `A` we
may conclude `B`, evidenced by `f x`, and from `B` and `¬ B` we may
conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown `¬ A`.
{:/}

令 `f` 为 `A → B` 的证据，`¬y` 为 `¬ B` 的证据。我们要证明，若假定 `A`
成立就会导出矛盾，因此 `¬ A` 必定成立。令 `x` 为 `A` 的证据。根据 `f x`，
我们可从 `A → B` 和 `A` 我们可得出结论 `B`。而根据 `¬y (f x)`，可从
B` 和 `¬ B` 得出结论 `⊥`。这样，我们就证明了 `¬ A`。

{::comment}
Using negation, it is straightforward to define inequality:
{:/}

利用否定可直接定义不等性：

\begin{code}
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)
\end{code}

{::comment}
It is trivial to show distinct numbers are not equal:
{:/}

要证明不同的数不相等很简单：

\begin{code}
_ : 1 ≢ 2
_ = λ()
\end{code}

{::comment}
This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number:
{:/}

这是我们第一次在 λ-表达式中使用谬模式（absurd pattern）。类型 `M ≡ N`
只有在 `M` 和 `N` 可被化简为相同的项时才能居留。由于 `1` 和 `2`
会化简为不同的正规形式，因此 Agda 判定没有正据可证明 `1 ≡ 2`。
第二个例子是，很容易验证皮亚诺公理中「零不是任何数的后继数」的假设：

\begin{code}
peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()
\end{code}

{::comment}
The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.
{:/}

它们证据本质上相同，因为谬模式会匹配所有类型为 `zero ≡ suc m` 的可能的证据。

{::comment}
Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where
{:/}

鉴于蕴含和幂运算之间的对应关系，以及没有成员的类型为假，
我们可以将否定看作零的幂。它确实对应于我们所知的算术运算，即

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0

{::comment}
Indeed, there is exactly one proof of `⊥ → ⊥`.  We can write
this proof two different ways:
{:/}

确实，只有一个 `⊥ → ⊥` 的证明。我们可以用两种方式写出此证明：

\begin{code}
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()
\end{code}

{::comment}
But, using extensionality, we can prove these equal:
{:/}

不过使用外延性，我们可以证明二者相等：

\begin{code}
id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())
\end{code}

{::comment}
By extensionality, `id ≡ id′` holds if for every
`x` in their domain we have `id x ≡ id′ x`. But there
is no `x` in their domain, so the equality holds trivially.
{:/}

根据外延性，对于任何在二者定义域中的 `x`，都有 `id x ≡ id′ x`，
则 `id ≡ id′` 成立。不过没有 `x` 在它们的定义域中，因此其相等性平凡成立。

{::comment}
Indeed, we can show any two proofs of a negation are equal:
{:/}

实际上，我们可以证明任意两个否定的证明都是相等的：

\begin{code}
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))
\end{code}

{::comment}
Evidence for `¬ A` implies that any evidence of `A`
immediately leads to a contradiction.  But extensionality
quantifies over all `x` such that `A` holds, hence any
such `x` immediately leads to a contradiction,
again causing the equality to hold trivially.
{:/}

`¬ A` 的证据蕴含任何 `A` 的证据都可直接得出矛盾。但由于外延性全称量化了使
`A` 成立的 `x`，因此任何这样的 `x` 都会直接导出矛盾，同样其相等性平凡成立。


{::comment}
#### Exercise `<-irreflexive` (recommended)
{:/}

#### 练习 `<-irreflexive`（推荐）

{::comment}
Using negation, show that
[strict inequality][plfa.Relations#strict-inequality]
is irreflexive, that is, `n < n` holds for no `n`.
{:/}

利用否定证明 [strict inequality][plfa.Relations#strict-inequality]
不满足自反性，即 `n < n` 对于任何 `n` 都不成立。
{::comment}

\begin{code}
-- Your code goes here
\end{code}

{:/}

\begin{code}
-- 请将代码写在此处
\end{code}

{::comment}
#### Exercise `trichotomy`
{:/}

#### 练习 `trichotomy`

{::comment}
Show that strict inequality satisfies
[trichotomy][plfa.Relations#trichotomy],
that is, for any naturals `m` and `n` exactly one of the following holds:
{:/}

请证明严格不相等满足 [trichotomy][plfa.Relations#trichotomy]（三分性），
即对于任何自然数 `m` 和 `n`，以下三条刚好只有一条成立：

* `m < n`
* `m ≡ n`
* `m > n`

{::comment}
Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.
{:/}

「刚好只有一条」的意思是，三者中不仅有一条成立，而且当其中一条成立时，
其它二者的否定也必定成立。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处
\end{code}

{::comment}
#### Exercise `⊎-dual-×` (recommended)
{:/}

#### 练习 `⊎-dual-×`（推荐）

{::comment}
Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.
{:/}

请证明合取、析取和否定可通过以下版本的德·摩根定律关联在一起。

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

{::comment}
This result is an easy consequence of something we've proved previously.
{:/}

此结果是我们之前证明的定理的简单推论。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处
\end{code}

{::comment}
Do we also have the following?
{:/}

以下命题也成立吗？

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

{::comment}
If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?
{:/}

若成立，请证明；若不成立，你能给出一个比同构更弱的关系将两边关联起来吗？


{::comment}
## Intuitive and Classical logic
{:/}

## 直觉逻辑与经典逻辑

{::comment}
In Gilbert and Sullivan's _The Gondoliers_, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."
{:/}

在 Gilbert 和 Sullivan 的电影《船夫（The Gondoliers）》中，
Casilda 被告知她还是个婴儿时，就被许配给了巴塔维亚国王的继承人。
但由于一场动乱，没人知道她被许配给了两位继承人 Marco 和 Giuseppe
中的哪一位。她惊慌地哀嚎道：「那么你的意思是说我嫁给了两位船夫中的一位，
但却无法确定是谁？」对此的回答是：「虽然不知到是谁，但这件事却是毫无疑问的。」

{::comment}
Logic comes in many varieties, and one distinction is between
_classical_ and _intuitionistic_. Intuitionists, concerned
by assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
_which_ of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.
{:/}

逻辑学有很多变种，而**经典逻辑**和**直觉逻辑**之间有一个区别。
直觉主义者关注于某些逻辑学家对无限性本质的假设，坚持真理的构造主义的概念。
具体来说，它们坚持认为 `A ⊎ B` 的证明必须确定 `A` 或 `B` 中的**哪一个**成立，
因此它们会解决宣称 Casilda 嫁给了 Marco 或者 Giuseppe，直到其中一个被确定为
她的丈夫为止。或许 Gilbert 和 Sullivan 期待直觉主义，因为在故事的结局中，
继承人是第三个人 Luiz，他和 Casilda 已经顺利地相爱了。

{::comment}
Intuitionists also reject the law of the excluded middle, which
asserts `A ⊎ ¬ A` for every `A`, since the law gives no clue as to
_which_ of `A` or `¬ A` holds. Heyting formalised a variant of
Hilbert's classical logic that captures the intuitionistic notion of
provability. In particular, the law of the excluded middle is provable
in Hilbert's logic, but not in Heyting's.  Further, if the law of the
excluded middle is added as an axiom to Heyting's logic, then it
becomes equivalent to Hilbert's.  Kolmogorov showed the two logics
were closely related: he gave a double-negation translation, such that
a formula is provable in classical logic if and only if its
translation is provable in intuitionistic logic.
{:/}

直觉主义者也拒绝排中律，该定律断言，对于所有的 `A`，`A ⊎ ¬ A` 必定成立，
因为该定律没有给出 `A` 和 `¬ A` 中的哪一个成立。海廷形式化了希尔伯特经典逻辑的
一个变种，他抓住了直觉主义中可证明性的概念。具体来说，排中律在希尔伯特逻辑
中是可证明的，但在海廷逻辑中却不可证明。进一步来说，如果排中律作为一条公理
添加到海廷逻辑中，那么它会等价于希尔伯特逻辑。柯尔莫哥洛夫证明了两种逻辑紧密相关：
他给出了双重否定翻译，即一个式子在经典逻辑中可证，当且仅当它的双重否定式在
直觉逻辑中可证。

{::comment}
Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.
{:/}

「命题即类型」最初是为直觉逻辑而制定的。这是一种完美的契合，因为在直觉主义的
解释中，式子 `A ⊎ B` 刚好可以在给出 `A` 或 `B` 之一的证明时得证，因此对应于析取
的类型是一个不交和（disjoint sum）。

{::comment}
(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)
{:/}

（以上内容部分来源于 "Propositions as Types", Philip Wadler,
_Communications of the ACM_，2015 年 12月。）

{::comment}
## Excluded middle is irrefutable
{:/}

## 排中律是不可辩驳的

{::comment}
The law of the excluded middle can be formulated as follows:
{:/}

排中律可形式化如下：

\begin{code}
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A
\end{code}

{::comment}
As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is _irrefutable_,
meaning that the negation of its negation is provable (and hence that
its negation is never provable):
{:/}

如之前所言，排中律在直觉逻辑中并不成立。然而，我们可以证明它是
**不可辩驳（irrefutable）**的，即其否定的否定是可证明的（因而其否定式不可证明）：

\begin{code}
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))
\end{code}

{::comment}
The best way to explain this code is to develop it interactively:
{:/}

解释此代码的最佳方式是交互式地推导它：

    em-irrefutable k = ?

{::comment}
Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that given a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly:
{:/}

Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that given a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly:

    em-irrefutable k = k ?

{::comment}
We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct:
{:/}

We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct:

    em-irrefutable k = k (inj₂ λ{ x → ? })

{::comment}
The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, the only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly:
{:/}

The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, the only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly:

    em-irrefutable k = k (inj₂ λ{ x → k ? })

{::comment}
This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct:
{:/}

This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct:

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

{::comment}
There are no holes left! This completes the proof.
{:/}

There are no holes left! This completes the proof.

{::comment}
The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)
{:/}

The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)

{::comment}
Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."
{:/}

Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."

{::comment}
The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.
{:/}

The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.

{::comment}
The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?
{:/}

The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?

{::comment}
"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."
{:/}

"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."

{::comment}
The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.
{:/}

The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.

{::comment}
"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"
{:/}

"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"

{::comment}
The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."
{:/}

The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."

{::comment}
And the devil handed back to the man the same valise that the man had
just handed to him.
{:/}

And the devil handed back to the man the same valise that the man had
just handed to him.

{::comment}
(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003.)
{:/}

(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003.)


{::comment}
#### Exercise `Classical` (stretch)
{:/}

#### 练习 `Classical`（延伸）

{::comment}
Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.
{:/}

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

{::comment}
Show that each of these implies all the others.
{:/}

Show that each of these implies all the others.

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- Your code goes here
\end{code}


{::comment}
#### Exercise `Stable` (stretch)
{:/}

#### Exercise `Stable` (stretch)

{::comment}
Say that a formula is _stable_ if double negation elimination holds for it:
{:/}

Say that a formula is _stable_ if double negation elimination holds for it:

\begin{code}
Stable : Set → Set
Stable A = ¬ ¬ A → A
\end{code}

{::comment}
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.
{:/}


Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

\begin{code}
-- Your code goes here
\end{code}

{::comment}
## Standard Prelude
{:/}

## Standard Prelude

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

Definitions similar to those in this chapter can be found in the standard library:

\begin{code}
import Relation.Nullary using (¬_)
import Relation.Nullary.Negation using (contraposition)
\end{code}

## Unicode

{::comment}
This chapter uses the following unicode:
{:/}

This chapter uses the following unicode:

{::comment}
    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
{:/}


    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
