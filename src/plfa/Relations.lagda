---
title     : "Relations: 关系的归纳定义"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
translators : ["Fangyi Zhou"]
progress  : 60
---

\begin{code}
module plfa.Relations where
\end{code}

在定义了加法和乘法等运算以后，下一步我们来定义关系（Relation），比如说*小于等于*。
{::comment}
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.
{:/}

## 导入
{::comment}
## Imports
{:/}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
\end{code}

## 定义关系
{::comment}
## Defining relations
{:/}

小于等于这个关系有无穷个实例，如下所示：
{::comment}
The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:
{:/}

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

但是，我们仍然可以用几行有限的定义来表示所有的实例，如下文所示的一对推理规则：
{::comment}
And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:
{:/}

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

以及其 Agda 定义：
{::comment}
And here is the definition in Agda:
{:/}
\begin{code}
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
\end{code}
在这里，`z≤n` 和 `s≤s`（无空格）是构造器的名称，`zero ≤ n`、`m ≤ n` 和
`suc m ≤ suc n` （带空格）是类型。在这里我们第一次用到了 *索引数据类型*
(Indexed datatype）。我们使用 `m` 和 `n` 这两个自然数来索引 `m ≤ n` 这个类型。
在 Agda 里，由两个及以上短横线开始的行是注释行，我们巧妙利用这一语法特性，用上述形式
来表示相应的推理规则。在后文中，我们还会继续使用这一形式。
{::comment}
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.
{:/}

这两条定义告诉我们相同的两件事：
{::comment}
Both definitions above tell us the same two things:
{:/}

* *起始步骤*: 对于所有的自然数 `n`，命题 `zero ≤ n` 成立。
* *归纳步骤*：对于所有的自然数 `m` 和 `n`，如果命题 `m ≤ n` 成立，
  那么命题 `suc m ≤ suc n` 成立。

{::comment}
* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.
{:/}

实际上，他们分别给我们更多的信息：

{::comment}
In fact, they each give us a bit more detail:
{:/}

* *起始步骤*: 对于所有的自然数 `n`，构造器 `z≤n` 提供了 `zero ≤ n` 成立的证明。
* *归纳步骤*：对于所有的自然数 `m` 和 `n`，构造器 `s≤s` 将 `m ≤ n` 成立的证明
  转化为 `suc m ≤ suc n` 成立的证明。

{::comment}
* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.
{:/}

例如，我们在这里以推理规则的形式写出 `2 ≤ 4` 的证明：

{::comment}
For example, here in inference rule notation is the proof that
`2 ≤ 4`:
{:/}

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

下面是对应的 Agda 证明：

{::comment}
And here is the corresponding Agda proof:
{:/}
\begin{code}
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)
\end{code}


## 隐式参数
{::comment}
## Implicit arguments
{:/}

这是我们第一次使用隐式参数。定义不等式时，构造器的定义中使用了 `∀`，
就像我们在下面的命题中使用 `∀` 一样：
{::comment}
This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:
{:/}

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

但是我们这里的定义使用了花括号 `{ }`，而不是小括号 `( )`。
这意味着参数是 *隐式的* （Implicit），不需要额外声明。实际上，Agda 的类型检查器
会 *推导* 出它们。因此，我们在 `m + n ≡ n + m` 的证明中需要写出 `+-comm m n`，
在 `zero ≤ n` 的证明中可以省略 `n`。同理，如果 `m≤n` 是 `m ≤ n`的证明，
那么我们写出 `s≤s m≤n` 作为 `suc m ≤ suc n` 的证明，无需声明 `m` 和 `n`。
{::comment}
However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.
{:/}

如果有希望的话，我们也可以在大括号里显式声明隐式参数。例如，下面是 `2 ≤ 4` 的 Agda
证明，包括了显式声明了的隐式参数：
{::comment}
If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
{:/}
\begin{code}
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
\end{code}
也可以额外加上参数的名字：
{::comment}
One may also identify implicit arguments by name:
{:/}
\begin{code}
_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))
\end{code}
在后者的形式中，也可以只声明一部分隐式参数：
{::comment}
In the latter format, you may only supply some implicit arguments:
{:/}
\begin{code}
_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)
\end{code}
但是不可以改变隐式参数的顺序，即便加上了名字。
{::comment}
It is not permitted to swap implicit arguments, even when named.
{:/}


## 优先级
{::comment}
## Precedence
{:/}

我们如下定义比较的优先级：
{::comment}
We declare the precedence for comparison as follows:
{:/}
\begin{code}
infix 4 _≤_
\end{code}
我们将 `_≤_` 的优先级设置为 4，所以它比优先级为 6 的 `_+_` 结合的更紧，此外，
`1 + 2 ≤ 3` 将被解析为 `(1 + 2) ≤ 3`。我们用 `infix` 来表示运算符既不是左结合的，
也不是右结合的。因为 `1 ≤ 2 ≤ 3` 解析为 `(1 ≤ 2) ≤ 3` 或者 `1 ≤ (2 ≤ 3)` 都没有意义。
{::comment}
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.
{:/}

## 可决定性
{::comment}
## Decidability
{:/}

给定两个数，我们可以很直接地决定第一个数是不是小于等于第二个数。我们在此处不给出说明的代码，
但我们会在 [Decidable][plfa.Decidable] 章节重新讨论这个问题。
{::comment}
Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable][plfa.Decidable].
{:/}

## 序关系的性质
{::comment}
## Properties of ordering relations
{:/}

数学家对于关系的常见性质给出了约定的名称。
{::comment}
Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.
{:/}

* *自反*（Reflexive）：对于所有的 `n`，关系 `n ≤ n` 成立。
* *传递*（Transitive）：对于所有的 `m`、 `n` 和 `p`，如果 `m ≤ n` 和 `n ≤ p`
  成立，那么 `m ≤ p` 也成立。
* *反对称*（Anti-symmetric）：对于所有的 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
  同时成立，那么 `m ≡ n` 成立。
* *完全*（Total）：对于所有的 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。

{::comment}
* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.
{:/}

`_≤_` 关系满足上述四条性质。
{::comment}
The relation `_≤_` satisfies all four of these properties.
{:/}

对于上述性质的组合也有约定的名称。
{::comment}
There are also names for some combinations of these properties.
{:/}

* *预序*（Preorder）：满足自反和传递的关系。
* *偏序*（Partial Order）：满足反对称的预序。
* *全序*（Total Order）：满足完全的偏序。

{::comment}
* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.
{:/}

如果你进入了关于关系的聚会，你现在知道怎么样和人讨论了，可以讨论关于自反、传递、反对称和完全，
或者问一问这是不是预序、偏序或者全序。
{::comment}
If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.
{:/}

更认真的来说，如果你在阅读论文时碰到了一个关系，本文的介绍让你可以对关系有基本的了解和判断，
来判断这个关系是不是预序、偏序或者全序。一个认真的作者一般会在文章指出这个关系具有（或者缺少）
上述性质，比如说指出新定义的关系是一个偏序而不是全序。
{::comment}
Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.
{:/}

#### 练习 `orderings` {#orderings}
{::comment}
#### Exercise `orderings` {#orderings}
{:/}

给出一个不是偏序的预序的例子。
{::comment}
Give an example of a preorder that is not a partial order.
{:/}

\begin{code}
-- 在此处书写你的代码
\end{code}

给出一个不是全序的偏序的例子。
{::comment}
Give an example of a partial order that is not a total order.
{:/}

\begin{code}
-- 在此处书写你的代码
\end{code}

## 自反性
{::comment}
## Reflexivity
{:/}

我们第一个来证明的性质是自反性：对于任意自然数 `n`，关系 `n ≤ n` 成立。我们使用标准库
的惯例来隐式申明参数，在使用自反性的证明时这样可以更加方便。
{::comment}
The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{:/}
\begin{code}
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero}   =  z≤n
≤-refl {suc n}  =  s≤s (≤-refl {n})
\end{code}

这个证明直接在 `n` 上进行归纳。在起始步骤中，`zero ≤ zero` 由 `z≤n` 证明；在归纳步骤中，
归纳假设 `≤-refl {n}` 给我们带来了 `n ≤ n` 的证明，我们只需要使用 `s≤s`，就可以获得
`suc n ≤ suc n` 的证明。
{::comment}
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.
{:/}

在 Emacs 中来交互式地证明自反性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。
{::comment}
It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
{:/}

## 传递性
{::comment}
## Transitivity
{:/}

我们第二个证明的性质是传递性：对于任意自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ p`
成立，那么 `m ≤ p` 成立。同样，`m`、`n` 和 `p` 是隐式参数：
{::comment}
The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
{:/}
\begin{code}
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)
\end{code}
这里我们在 `m ≤ n` 的 *证据* 上进行归纳。在起始步骤里，第一个不等式因为 `z≤n` 而成立，
那么结论亦可由 `z≤n` 而得出。在这里，`n ≤ p` 的证明是不需要的，我们用 `_` 来表示这个
证明没有被使用。
{::comment}
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.
{:/}

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个不等式因为 `s≤s n≤p` 而成立，
所以我们已知 `suc m ≤ suc n` 和 `suc n ≤ suc p`，求证 `suc m ≤ suc p`。
通过归纳假设 `≤-trans m≤n n≤p`，我们得知 `m ≤ p`，在此之上使用 `s≤s` 即可证。
{::comment}
In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.
{:/}

`≤-trans (s≤s m≤n) z≤n` 不可能发生，因为第一个不等式告诉我们中间的数是一个 `suc n`，
而第二个不等式告诉我们中间的书是 `zero`。Agda 可以推断这样的情况不可能发现，所以我们不需要
（也不可以）列出这种情况。
{::comment}
The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.
{:/}

我们也可以将隐式参数显式地声明。
{::comment}
Alternatively, we could make the implicit parameters explicit:
{:/}
\begin{code}
≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)
\end{code}
有人说这样的证明更加的清晰，也有人说这个更长的证明让人难以抓住证明的重点。
我们一般选择使用简短的证明。
{::comment}
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.
{:/}

对于性质成立证明进行的归纳（如上文中对于 `m ≤ n` 的证明进行归纳），相比于对于性质成立的值进行的归纳
（如对于 `m` 进行归纳），有非常大的价值。我们会经常使用这样的方法。
{::comment}
The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.
{:/}

同样，在 Emacs 中来交互式地证明传递性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。
{::comment}
Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
{:/}

## 反对称性
{::comment}
## Anti-symmetry
{:/}

我们证明的第三个性质是反对称性：对于所有的自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
同时成立，那么 `m ≡ n` 成立：
{::comment}
The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
{:/}
\begin{code}
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)
\end{code}
同样，我们对于 `m ≤ n` 和 `n ≤ m` 的证明进行归纳。
{::comment}
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.
{:/}

在起始步骤中，两个不等式都因为 `z≤n` 而成立。因此我们已知 `zero ≤ zero` 和 `zero ≤ zero`，
求证 `zero ≡ zero`，由自反性可证。（注：由等式的自反性可证，而不是不等式的自反性）
{::comment}
In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)
{:/}

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个等式因为 `s≤s n≤m` 而成立。因此我们已知
`suc m ≤ suc n` 和 `suc n ≤ suc m`，求证 `suc m ≡ suc n`。归纳假设 `≤-antisym m≤n n≤m`
可以证明 `m ≡ n`，因此我们可以使用同余性完成证明。

{::comment}
In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.
{::comment}

#### 练习 `≤-antisym-cases` {#leq-antisym-cases}
{::comment}
#### Exercise `≤-antisym-cases` {#leq-antisym-cases}
{:/}

上面的证明中省略了一个参数是 `z≤n`，另一个参数是 `s≤s` 的情况。为什么可以省略这种情况？
{::comment}
The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?
{:/}

\begin{code}
-- 在此处书写你的代码
\end{code}

## 完全性
{::comment}
## Total
{:/}

我们证明的第四个性质是完全性：对于任何自然数 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。
在 `m` 和 `n` 相等时，两者同时成立。
{::comment}
The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.
{:/}

我们首先来说明怎么样不等式才是完全的：
{::comment}
We specify what it means for inequality to be total:
{:/}
\begin{code}
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n
\end{code}
`Total m n` 成立的证明有两种形式：`forward m≤n` 或者 `flipped n≤m`，其中
`m≤n` 和 `n≤m` 分别是 `m ≤ n` 和 `n ≤ m` 的证明。
{::comment}
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.
{:/}

（如果你对于逻辑学有所了解，上面的定义可以由析取（Disjunction）表示。
我们会在 [Connectives][plfa.Connectives] 章节介绍析取。）
{::comment}
(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives][plfa.Connectives].)
{:/}

这是我们第一次使用带*参数*的数据类型，这里 `m` 和 `n` 是参数。这等同于下面的索引数据类型：
{::comment}
This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{:/}
\begin{code}
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n
\end{code}
类型里的每个参数都转换成构造器的一个隐式参数。索引数据类型中的索引可以变化，正如在
`zero ≤ n` 和 `suc m ≤ suc n` 中那样，而参数化数据类型不一样，其参数必须保持相同，
正如在 `Total m n` 中那样。参数化的声明更短，更易于阅读，而且有时可以帮助到 Agda 的
终结检查器，所以我们尽可能地使用它们，而不是索引数据类型。

{::comment}
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.
{:/}

在上述准备工作完成后，我们定义并证明完全性。
{::comment}
With that preliminary out of the way, we specify and prove totality:
{:/}
\begin{code}
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
\end{code}
这里，我们的证明在两个参数上进行归纳，并按照情况分析：
{::comment}
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:
{:/}

* *第一起始步骤*：如果第一个参数是 `zero`，第二个参数是 `n`，那么 forward
  条件成立，我们使用 `z≤n` 作为 `zero ≤ n` 的证明。

* *第二起始步骤*：如果第一个参数是 `suc m`，第二个参数是 `zero`，那么 flipped
  条件成立，我们使用 `z≤n` 作为 `zero ≤ suc m` 的证明。

* *归纳步骤*：如果第一个参数是 `suc m`，第二个参数是 `suc n`，那么归纳假设
  `≤-total m n` 可以给出如下推断：

  + 归纳假设的 forward 条件成立，以 `m≤n` 作为 `m ≤ n` 的证明。以此我们可以使用
    `s≤s m≤n` 作为 `suc m ≤ suc n` 来证明 forward 条件成立。

  + 归纳假设的 flipped 条件成立，以 `n≤m` 作为 `n ≤ m` 的证明。以此我们可以使用
    `s≤s n≤m` 作为 `suc n ≤ suc m` 来证明 flipped 条件成立。

{::comment}
* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.
{:/}

这是我们第一次在 Agda 中使用 `with` 语句。`with` 关键字后面有一个表达式和一或多行。
每行以省略号（`...`）和一个竖线（`|`）开头，后面跟着用来匹配表达式的模式，和等式的右手边。
{::comment}
This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.
{:/}

使用 `with` 语句等同于定义一个辅助函数。比如说，上面的定义和下面的等价：
{::comment}
Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
{:/}
\begin{code}
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)
\end{code}

这也是我们第一次在 Agda 中使用 `where` 语句。`where` 关键字后面有一或多条定义，其必须被缩进。
之前等式左手边的约束变量（此例中的 `m` 和 `n`）在嵌套的定义中仍然在作用域内。
在嵌套定义中的约束标识符（此例中的 `helper` ）在等式的右手边的作用域内。
{::comment}
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.
{:/}

如果两个参数相同，那么两个情况同时成立，我们可以返回任一证明。上面的代码中我们返回 forward 条件，
但是我们也可以返回 flipped 条件，如下：
{::comment}
If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{:/}
\begin{code}
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                        | forward m≤n   =  forward (s≤s m≤n)
...                        | flipped n≤m   =  flipped (s≤s n≤m)
\end{code}
两者的区别在于上述代码在对于第一个参数进行模式匹配之前先对于第二个参数先进行模式匹配。
{::comment}
It differs from the original code in that it pattern
matches on the second argument before the first argument.
{:/}


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
\begin{code}
+-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
    -------------
  → m + p ≤ m + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc m) p q p≤q  =  s≤s (+-monoʳ-≤ m p q p≤q)
\end{code}
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
\begin{code}
+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n
\end{code}
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
\begin{code}
+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
\end{code}
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

\begin{code}
-- Your code goes here
\end{code}


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
\begin{code}
infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n
\end{code}
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation][plfa.Negation].

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

\begin{code}
-- Your code goes here
\end{code}

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

\begin{code}
-- Your code goes here
\end{code}

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

\begin{code}
-- Your code goes here
\end{code}

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

\begin{code}
-- Your code goes here
\end{code}

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

\begin{code}
-- Your code goes here
\end{code}


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
\begin{code}
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc   : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
\end{code}
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
\begin{code}
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)
\end{code}
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

\begin{code}
-- Your code goes here
\end{code}

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)

\begin{code}
-- Your code goes here
\end{code}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
\begin{code}
import Data.Nat using (_≤_; z≤n; s≤s)
import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                  +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
\end{code}
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives][plfa.Connectives]),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
