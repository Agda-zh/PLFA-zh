---
title     : "Relations: 关系的归纳定义"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
translators : ["Fangyi Zhou"]
progress  : 100
---

```
module plfa.part1.Relations where
```

<!--
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.
-->

在定义了加法和乘法等运算以后，下一步我们来定义**关系（Relation）**，比如说**小于等于**。


<!--
## Imports
-->

## 导入

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
```


<!--
## Defining relations
-->

## 定义关系

<!--
The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:
-->

小于等于这个关系有无穷个实例，如下所示：


    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

<!--
And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:
-->

但是，我们仍然可以用几行有限的定义来表示所有的实例，如下文所示的一对推理规则：

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

<!--
And here is the definition in Agda:
-->

以及其 Agda 定义：

```
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
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.
-->

在这里，`z≤n` 和 `s≤s`（无空格）是构造子的名称，`zero ≤ n`、`m ≤ n` 和
`suc m ≤ suc n` （带空格）是类型。在这里我们第一次用到了
**索引数据类型（Indexed datatype）**。我们使用 `m` 和 `n` 这两个自然数来索引
`m ≤ n` 这个类型。在 Agda 里，由两个及以上短横线开始的行是注释行，
我们巧妙利用这一语法特性，用上述形式来表示相应的推理规则。
在后文中，我们还会继续使用这一形式。

<!--
Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.
-->

这两条定义告诉我们相同的两件事：

* **起始步骤**: 对于所有的自然数 `n`，命题 `zero ≤ n` 成立。
* **归纳步骤**：对于所有的自然数 `m` 和 `n`，如果命题 `m ≤ n` 成立，
  那么命题 `suc m ≤ suc n` 成立。

<!--
In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.
-->

实际上，他们分别给我们更多的信息：

* **起始步骤**: 对于所有的自然数 `n`，构造子 `z≤n` 提供了 `zero ≤ n` 成立的证明。
* **归纳步骤**：对于所有的自然数 `m` 和 `n`，构造子 `s≤s` 将 `m ≤ n` 成立的证明
  转化为 `suc m ≤ suc n` 成立的证明。

<!--
For example, here in inference rule notation is the proof that
`2 ≤ 4`:
-->

例如，我们在这里以推理规则的形式写出 `2 ≤ 4` 的证明：

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

<!--
And here is the corresponding Agda proof:
-->

下面是对应的 Agda 证明：

```
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)
```

<!--
## Implicit arguments
-->

## 隐式参数

<!--
This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:
-->

这是我们第一次使用隐式参数。定义不等式时，构造子的定义中使用了 `∀`，
就像我们在下面的命题中使用 `∀` 一样：

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

<!--
However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.
-->

但是我们这里的定义使用了花括号 `{ }`，而不是小括号 `( )`。
这意味着参数是**隐式的（Implicit）**，不需要额外声明。实际上，Agda 的类型检查器
会**推导（Infer）**出它们。因此，我们在 `m + n ≡ n + m` 的证明中需要写出 `+-comm m n`，
在 `zero ≤ n` 的证明中可以省略 `n`。同理，如果 `m≤n` 是 `m ≤ n`的证明，
那么我们写出 `s≤s m≤n` 作为 `suc m ≤ suc n` 的证明，无需声明 `m` 和 `n`。

<!--
If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
-->

如果有希望的话，我们也可以在大括号里显式声明隐式参数。例如，下面是 `2 ≤ 4` 的 Agda
证明，包括了显式声明了的隐式参数：

```
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
```

<!--
One may also identify implicit arguments by name:
-->

也可以额外加上参数的名字：

```
_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))
```

<!--
In the latter format, you can choose to only supply some implicit arguments:
-->

在后者的形式中，也可以选择只声明一部分隐式参数：

```
_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)
```

<!--
It is not permitted to swap implicit arguments, even when named.
-->

但是不可以改变隐式参数的顺序，即便加上了名字。

<!--
We can ask Agda to use the same inference to try and infer an _explicit_ term,
by writing `_`. For instance, we can define a variant of the proposition
`+-identityʳ` with implicit arguments:
-->

我们可以写出 `_` 来让 Agda 用相同的推导方式试着推导一个**显式**的项。
例如，我们可以为命题 `+-identityʳ` 定义一个带有隐式参数的变体：

```
+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _
```

<!--
We use `_` to ask Agda to infer the value of the _explicit_ argument from
context. There is only one value which gives us the correct proof, `m`, so Agda
happily fills it in.
If Agda fails to infer the value, it reports an error.
-->

我们用 `_` 来让 Agda 从上下文中推导**显式参数**的值。只有 `m`
这一个值能够给出正确的证明，因此 Agda 愉快地填入了它。
如果 Agda 推导值失败，那么它会报一个错误。


<!--
## Precedence
-->

## 优先级

<!--
We declare the precedence for comparison as follows:
-->

我们如下定义比较的优先级：

```
infix 4 _≤_
```

<!--
We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.
-->

我们将 `_≤_` 的优先级设置为 4，所以它比优先级为 6 的 `_+_` 结合的更紧，此外，
`1 + 2 ≤ 3` 将被解析为 `(1 + 2) ≤ 3`。我们用 `infix` 来表示运算符既不是左结合的，
也不是右结合的。因为 `1 ≤ 2 ≤ 3` 解析为 `(1 ≤ 2) ≤ 3` 或者 `1 ≤ (2 ≤ 3)` 都没有意义。


<!--
## Decidability
-->

## 可决定性

<!--
Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable](/Decidable/).
-->

给定两个数，我们可以很直接地决定第一个数是不是小于等于第二个数。我们在此处不给出说明的代码，
但我们会在 [Decidable](/Decidable/) 章节重新讨论这个问题。


<!--
## Inversion
-->

## 反演

<!--
In our definitions, we go from smaller things to larger things.
For instance, from `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.
-->

在我们的定义中，我们从更小的东西得到更大的东西。例如，我们可以从
`m ≤ n` 得出 `suc m ≤ suc n` 的结论，这里的 `suc m` 比 `m` 更大
（也就是说，前者包含后者），`suc n` 也比 `n` 更大。但有时我们也
需要从更大的东西得到更小的东西。

<!--
There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
-->

只有一种方式能够证明对于任意 `m` 和 `n` 有 `suc m ≤ suc n`。
这让我们能够反演（invert）之前的规则。

```
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n
```

<!--
Here `m≤n` (with no spaces) is a variable name while
`m ≤ n` (with spaces) is a type, and the latter
is the type of the former.  It is a common convention
in Agda to derive a variable name by removing
spaces from its type.
-->

这里的 `m≤n`（不带空格）是一个变量名，而 `m ≤ n`（带空格）是一个类型，
且后者是前者的类型。在 Agda 中，将类型中的空格去掉来作为变量名是一种常见的约定。

<!--
Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.
-->

并不是所有规则都可以反演。实际上，`z≤n` 的规则没有非隐式的假设，
因此它没有可以被反演的规则。但这种反演通常是成立的。

<!--
Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
-->

反演的另一个例子是证明只存在一种情况使得一个数字能够小于或等于零。

```
inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl
```

<!--
## Properties of ordering relations
-->

## 序关系的性质

<!--
Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.
-->

数学家对于关系的常见性质给出了约定的名称。

* **自反（Reflexive）**：对于所有的 `n`，关系 `n ≤ n` 成立。
* **传递（Transitive）**：对于所有的 `m`、 `n` 和 `p`，如果 `m ≤ n` 和 `n ≤ p`
  成立，那么 `m ≤ p` 也成立。
* **反对称（Anti-symmetric）**：对于所有的 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
  同时成立，那么 `m ≡ n` 成立。
* **完全（Total）**：对于所有的 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。

<!--
The relation `_≤_` satisfies all four of these properties.
-->

`_≤_` 关系满足上述四条性质。

<!--
There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.
-->

对于上述性质的组合也有约定的名称。

* **预序（Preorder）**：满足自反和传递的关系。
* **偏序（Partial Order）**：满足反对称的预序。
* **全序（Total Order）**：满足完全的偏序。

<!--
If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.
-->

如果你进入了关于关系的聚会，你现在知道怎么样和人讨论了，可以讨论关于自反、传递、反对称和完全，
或者问一问这是不是预序、偏序或者全序。

<!--
Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.
-->

更认真的来说，如果你在阅读论文时碰到了一个关系，本文的介绍让你可以对关系有基本的了解和判断，
来判断这个关系是不是预序、偏序或者全序。一个认真的作者一般会在文章指出这个关系具有（或者缺少）
上述性质，比如说指出新定义的关系是一个偏序而不是全序。

<!--
#### Exercise `orderings` (practice) {name=orderings}
-->

#### 练习 `orderings`（实践） {name=orderings}

<!--
Give an example of a preorder that is not a partial order.
-->

给出一个不是偏序的预序的例子。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
Give an example of a partial order that is not a total order.
-->

给出一个不是全序的偏序的例子。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
## Reflexivity
-->

## 自反性

<!--
The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
-->

我们第一个来证明的性质是自反性：对于任意自然数 `n`，关系 `n ≤ n` 成立。我们使用标准库
的惯例来隐式申明参数，在使用自反性的证明时这样可以更加方便。

```
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
```

<!--
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.
-->

这个证明直接在 `n` 上进行归纳。在起始步骤中，`zero ≤ zero` 由 `z≤n` 证明；在归纳步骤中，
归纳假设 `≤-refl {n}` 给我们带来了 `n ≤ n` 的证明，我们只需要使用 `s≤s`，就可以获得
`suc n ≤ suc n` 的证明。

<!--
It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
-->

在 Emacs 中来交互式地证明自反性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。


<!--
## Transitivity
-->

## 传递性

<!--
The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
-->

我们第二个证明的性质是传递性：对于任意自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ p`
成立，那么 `m ≤ p` 成立。同样，`m`、`n` 和 `p` 是隐式参数：

```
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)
```

<!--
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.
-->

这里我们在 `m ≤ n` 的**证据（Evidence）**上进行归纳。在起始步骤里，第一个不等式因为 `z≤n` 而成立，
那么结论亦可由 `z≤n` 而得出。在这里，`n ≤ p` 的证明是不需要的，我们用 `_` 来表示这个
证明没有被使用。

<!--
In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.
-->

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个不等式因为 `s≤s n≤p` 而成立，
所以我们已知 `suc m ≤ suc n` 和 `suc n ≤ suc p`，求证 `suc m ≤ suc p`。
通过归纳假设 `≤-trans m≤n n≤p`，我们得知 `m ≤ p`，在此之上使用 `s≤s` 即可证。

<!--
The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.
-->

`≤-trans (s≤s m≤n) z≤n` 不可能发生，因为第一个不等式告诉我们中间的数是一个 `suc n`，
而第二个不等式告诉我们中间的数是 `zero`。Agda 可以推断这样的情况不可能发现，所以我们不需要
（也不可以）列出这种情况。

<!--
Alternatively, we could make the implicit parameters explicit:
-->

我们也可以将隐式参数显式地声明。

```
≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)
```

<!--
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.
-->

有人说这样的证明更加的清晰，也有人说这个更长的证明让人难以抓住证明的重点。
我们一般选择使用简短的证明。

<!--
The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.
-->

对于性质成立证明进行的归纳（如上文中对于 `m ≤ n` 的证明进行归纳），相比于对于性质成立的值进行的归纳
（如对于 `m` 进行归纳），有非常大的价值。我们会经常使用这样的方法。

<!--
Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
-->

同样，在 Emacs 中来交互式地证明传递性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。


<!--
## Anti-symmetry
-->

## 反对称性

<!--
The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds:
-->

我们证明的第三个性质是反对称性：对于所有的自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
同时成立，那么 `m ≡ n` 成立：

```
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)
```

<!--
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.
-->

同样，我们对于 `m ≤ n` 和 `n ≤ m` 的证明进行归纳。

<!--
In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)
-->

在起始步骤中，两个不等式都因为 `z≤n` 而成立。因此我们已知 `zero ≤ zero` 和 `zero ≤ zero`，
求证 `zero ≡ zero`，由自反性可证。（注：由等式的自反性可证，而不是不等式的自反性）

<!--
In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.
-->

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个等式因为 `s≤s n≤m` 而成立。因此我们已知
`suc m ≤ suc n` 和 `suc n ≤ suc m`，求证 `suc m ≡ suc n`。归纳假设 `≤-antisym m≤n n≤m`
可以证明 `m ≡ n`，因此我们可以使用同余性完成证明。


<!--
#### Exercise `≤-antisym-cases` (practice) {name=leq-antisym-cases}
-->

#### 练习 `≤-antisym-cases`（实践） {name=leq-antisym-cases}

<!--
The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?
-->

上面的证明中省略了一个参数是 `z≤n`，另一个参数是 `s≤s` 的情况。为什么可以省略这种情况？

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
## Total
-->

## 完全性

<!--
The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.
-->

我们证明的第四个性质是完全性：对于任何自然数 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。
在 `m` 和 `n` 相等时，两者同时成立。

<!--
We specify what it means for inequality to be total:
-->

我们首先来说明怎么样不等式才是完全的：

```
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n
```

<!--
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.
-->

`Total m n` 成立的证明有两种形式：`forward m≤n` 或者 `flipped n≤m`，其中
`m≤n` 和 `n≤m` 分别是 `m ≤ n` 和 `n ≤ m` 的证明。

<!--
(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives](/Connectives/).)
-->

（如果你对于逻辑学有所了解，上面的定义可以由析取（Disjunction）表示。
我们会在 [Connectives](/Connectives/) 章节介绍析取。）

<!--
This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
-->

这是我们第一次使用带*参数*的数据类型，这里 `m` 和 `n` 是参数。这等同于下面的索引数据类型：

```
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n
```

<!--
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.
-->

类型里的每个参数都转换成构造子的一个隐式参数。索引数据类型中的索引可以变化，正如在
`zero ≤ n` 和 `suc m ≤ suc n` 中那样，而参数化数据类型不一样，其参数必须保持相同，
正如在 `Total m n` 中那样。参数化的声明更短，更易于阅读，而且有时可以帮助到 Agda 的
终结检查器，所以我们尽可能地使用它们，而不是索引数据类型。

<!--
With that preliminary out of the way, we specify and prove totality:
-->

在上述准备工作完成后，我们定义并证明完全性。

```
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
```

<!--
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

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
-->

这里，我们的证明在两个参数上进行归纳，并按照情况分析：

* **第一起始步骤**：如果第一个参数是 `zero`，第二个参数是 `n`，那么 forward
  条件成立，我们使用 `z≤n` 作为 `zero ≤ n` 的证明。

* **第二起始步骤**：如果第一个参数是 `suc m`，第二个参数是 `zero`，那么 flipped
  条件成立，我们使用 `z≤n` 作为 `zero ≤ suc m` 的证明。

* **归纳步骤**：如果第一个参数是 `suc m`，第二个参数是 `suc n`，那么归纳假设
  `≤-total m n` 可以给出如下推断：

  + 归纳假设的 forward 条件成立，以 `m≤n` 作为 `m ≤ n` 的证明。以此我们可以使用
    `s≤s m≤n` 作为 `suc m ≤ suc n` 来证明 forward 条件成立。

  + 归纳假设的 flipped 条件成立，以 `n≤m` 作为 `n ≤ m` 的证明。以此我们可以使用
    `s≤s n≤m` 作为 `suc n ≤ suc m` 来证明 flipped 条件成立。

<!--
This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.
-->

这是我们第一次在 Agda 中使用 `with` 语句。`with` 关键字后面有一个表达式和一或多行。
每行以省略号（`...`）和一个竖线（`|`）开头，后面跟着用来匹配表达式的模式，和等式的右手边。

<!--
Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
-->

使用 `with` 语句等同于定义一个辅助函数。比如说，上面的定义和下面的等价：

```
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)
```

<!--
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.
-->

这也是我们第一次在 Agda 中使用 `where` 语句。`where` 关键字后面有一或多条定义，其必须被缩进。
之前等式左手边的约束变量（此例中的 `m` 和 `n`）在嵌套的定义中仍然在作用域内。
在嵌套定义中的约束标识符（此例中的 `helper` ）在等式的右手边的作用域内。

<!--
If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
-->

如果两个参数相同，那么两个情况同时成立，我们可以返回任一证明。上面的代码中我们返回 forward 条件，
但是我们也可以返回 flipped 条件，如下：

```
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                         | forward m≤n  =  forward (s≤s m≤n)
...                         | flipped n≤m  =  flipped (s≤s n≤m)
```

<!--
It differs from the original code in that it pattern
matches on the second argument before the first argument.
-->

两者的区别在于上述代码在对于第一个参数进行模式匹配之前先对于第二个参数先进行模式匹配。


<!--
## Monotonicity
-->

## 单调性

<!--
If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:
-->

如果在聚会中碰到了一个运算符和一个序，那么有人可能会问这个运算符对于这个序是不是
**单调的（Monotonic）**。比如说，加法对于小于等于是单调的，这意味着：

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

<!--
The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
-->

这个证明可以用我们学会的方法，很直接的来完成。我们最好把它分成三个部分，首先我们证明加法对于
小于等于在右手边是单调的：

```
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)
```

<!--
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.
-->

我们对于第一个参数进行归纳。

* **起始步骤**：第一个参数是 `zero`，那么 `zero + p ≤ zero + q` 可以化简为 `p ≤ q`，
  其证明由 `p≤q` 给出。

* **归纳步骤**：第一个参数是 `suc n`，那么 `suc n + p ≤ suc n + q` 可以化简为
  `suc (n + p) ≤ suc (n + q)`。归纳假设 `+-monoʳ-≤ n p q p≤q` 可以证明
  `n + p ≤ n + q`，我们在此之上使用 `s≤s` 即可得证。

<!--
Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
-->

接下来，我们证明加法对于小于等于在左手边是单调的。我们可以用之前的结论和加法的交换律来证明：

```
+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n
```

<!--
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.
-->

用 `+-comm m p` 和 `+-comm n p` 来重写，可以让 `m + p ≤ n + p` 转换成 `p + n ≤ p + m`，
而我们可以用 `+-moroʳ-≤ p m n m≤n` 来证明。

<!--
Third, we combine the two previous results:
-->

最后，我们把前两步的结论结合起来：

```
+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
```

<!--
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.
-->

使用 `+-monoˡ-≤ m n p m≤n` 可以证明 `m + p ≤ n + p`，
使用 `+-monoʳ-≤ n p q p≤q` 可以证明 `n + p ≤ n + q`，用传递性把两者连接起来，
我们可以获得 `m + p ≤ n + q` 的证明，如上所示。

<!--
#### Exercise `*-mono-≤` (stretch)
-->

#### 练习 `*-mono-≤` （延伸）

<!--
Show that multiplication is monotonic with regard to inequality.
-->

证明乘法对于小于等于是单调的。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
## Strict inequality {name=strict-inequality}
-->

## 严格不等关系 {name=strict-inequality}

<!--
We can define strict inequality similarly to inequality:
-->

我们可以用类似于定义不等关系的方法来定义严格不等关系。

```
infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n
```

<!--
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.
-->

严格不等关系与不等关系最重要的区别在于，0 小于任何数的后继，而不小于 0。

<!--
Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.
-->

显然，严格不等关系不是自反的，而是**非自反的（Irreflexive）**，表示 `n < n` 对于
任何值 `n` 都不成立。和不等关系一样，严格不等关系是传递的。严格不等关系不是完全的，但是满足
一个相似的性质：**三分律（Trichotomy）**：对于任意的 `m` 和 `n`，`m < n`、`m ≡ n` 或者
`m > n` 三者有且仅有一者成立。（我们定义 `m > n` 当且仅当 `n < m` 成立时成立）
严格不等关系对于加法和乘法也是单调的。

<!--
Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation](/Negation/).
-->

我们把一部分上述性质作为习题。非自反性需要逻辑非，三分律需要证明三者是互斥的，因此这两个性质
暂不做为习题。我们会在 [Negation](/Negation/) 章节来重新讨论。

<!--
It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.
-->

我们可以直接地来证明 `suc m ≤ n` 蕴涵了 `m < n`，及其逆命题。
因此我们亦可从不等关系的性质中，使用此性质来证明严格不等关系的性质。


<!--
#### Exercise `<-trans` (recommended) {name=less-trans}
-->

#### 练习 `<-trans` （推荐） {name=less-trans}

<!--
Show that strict inequality is transitive.
-->

证明严格不等是传递的。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
#### Exercise `trichotomy` (practice) {name=trichotomy}
-->

#### 练习 `trichotomy`（实践） {name=trichotomy}

<!--
Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.
-->

证明严格不等关系满足弱化的三元律，证明对于任意 `m` 和 `n`，下列命题有一条成立：

  * `m < n`，
  * `m ≡ n`，或者
  * `m > n`。

<!--
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation](/Negation/).)
-->

定义 `m > n` 为 `n < m`。你需要一个合适的数据类型声明，如同我们在证明完全性中使用的那样。
（我们会在介绍完[否定](/Negation/)之后证明三者是互斥的。）

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
#### Exercise `+-mono-<` (practice) {name=plus-mono-less}
-->

#### 练习 `+-mono-<`（实践） {name=plus-mono-less}

<!--
Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.
-->

证明加法对于严格不等关系是单调的。正如不等关系中那样，你可以需要额外的定义。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
#### Exercise `≤-iff-<` (recommended) {name=leq-iff-less}
-->

#### 练习 `≤-iff-<` (推荐) {name=leq-iff-less}

<!--
Show that `suc m ≤ n` implies `m < n`, and conversely.
-->

证明 `suc m ≤ n` 蕴涵了 `m < n`，及其逆命题。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
#### Exercise `<-trans-revisited` (practice) {name=less-trans-revisited}
-->

#### 练习 `<-trans-revisited`（实践） {name=less-trans-revisited}

<!--
Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.
-->

用另外一种方法证明严格不等是传递的，使用之前证明的不等关系和严格不等关系的联系，
以及不等关系的传递性。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
## Even and odd
-->

## 奇和偶

<!--
As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
-->

作为一个额外的例子，我们来定义奇数和偶数。不等关系和严格不等关系是**二元关系**，而奇偶性
是**一元关系**，有时也被叫做**谓词（Predicate）**：

```
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

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```

<!--
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.
-->

一个数是偶数，如果它是 0，或者是奇数的后继。一个数是奇数，如果它是偶数的后继。

<!--
This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).
-->

这是我们第一次定义一个相互递归的数据类型。因为每个标识符必须在使用前声明，所以
我们首先声明索引数据类型 `even` 和 `odd` （省略 `where` 关键字和其构造子的定义），
然后声明其构造子（省略其签名 `ℕ → Set`，因为在之前已经给出）。

<!--
This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:
-->

这也是我们第一次使用 **重载（Overloaded）**的构造子。这意味着不同类型的构造子
拥有相同的名字。在这里 `suc` 表示下面三种构造子其中之一：

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

<!--
Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.
-->

同理，`zero` 表示两种构造子的一种。因为类型推导的限制，Agda 不允许重载已定义的名字，
但是允许重载构造子。我们推荐将重载限制在有关联的定义中，如我们所做的这样，但这不是必须的。

<!--
We show that the sum of two even numbers is even:
-->

我们证明两个偶数之和是偶数：

```
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
```

<!--
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.
-->

与相互递归的定义对应，我们用两个相互递归的函数，一个证明两个偶数之和是偶数，另一个证明
一个奇数与一个偶数之和是奇数。

<!--
This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.
-->

这是我们第一次使用相互递归的函数。因为每个标识符必须在使用前声明，我们先给出两个函数的签名，
然后再给出其定义。

<!--
To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.
-->

要证明两个偶数之和为偶，我们考虑第一个数为偶数的证明。如果是因为第一个数为 0，
那么第二个数为偶数的证明即为和为偶数的证明。如果是因为第一个数为奇数的后继，
那么和为偶数是因为他是一个奇数和一个偶数的和的后续，而这个和是一个奇数。


<!--
To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.
-->

要证明一个奇数和一个偶数的和是奇数，我们考虑第一个数是奇数的证明。
如果是因为它是一个偶数的后继，那么和为奇数，因为它是两个偶数之和的后继，
而这个和是一个偶数。


<!--
#### Exercise `o+o≡e` (stretch) {name=odd-plus-odd}
-->

#### 练习 `o+o≡e` (延伸) {name=odd-plus-odd}

<!--
Show that the sum of two odd numbers is even.
-->

证明两个奇数之和为偶数。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
#### Exercise `Bin-predicates` (stretch) {name=Bin-predicates}
-->

#### 练习 `Bin-predicates` (延伸) {name=Bin-predicates}

<!--
Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:
-->

回忆我们在练习 [Bin](/Naturals/#Bin) 中定义了一个数据类型 `Bin` 来用二进制字符串表示自然数。
这个表达方法不是唯一的，因为我们在开头加任意个 0。因此，11 可以由以下方法表示：

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

<!--
Define a predicate
-->

定义一个谓词

    Can : Bin → Set

<!--
over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate
-->

其在一个二进制字符串的表示是标准的（Canonical）时成立，表示它没有开头的 0。在两个 11 的表达方式中，
第一个是标准的，而第二个不是。在定义这个谓词时，你需要一个辅助谓词：

    One : Bin → Set

<!--
that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).
-->

其仅在一个二进制字符串开头为 1 时成立。一个二进制字符串是标准的，如果它开头是 1 （表示一个正数），
或者它仅是一个 0 （表示 0）。

<!--
Show that increment preserves canonical bitstrings:
-->

证明递增可以保持标准性。

    Can b
    ------------
    Can (inc b)

<!--
Show that converting a natural to a bitstring always yields a
canonical bitstring:
-->

证明从自然数转换成的二进制字符串是标准的。

    ----------
    Can (to n)

<!--
Show that converting a canonical bitstring to a natural
and back is the identity:
-->

证明将一个标准的二进制字符串转换成自然数之后，再转换回二进制字符串与原二进制字符串相同。

    Can b
    ---------------
    to (from b) ≡ b

<!--
(Hint: For each of these, you may first need to prove related
properties of `One`. Also, you may need to prove that
if `One b` then `1` is less or equal to the result of `from b`.)
-->

（提示：对于每一条习题，先从 `One` 的性质开始。此外，你或许还需要证明若
`One b` 成立，则 `1` 小于或等于 `from b` 的结果。）

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
## Standard library
-->

## 标准库

<!--
Definitions similar to those in this chapter can be found in the standard library:
-->

标准库中有类似于本章介绍的定义：

```
import Data.Nat using (_≤_; z≤n; s≤s)
import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                  +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
```

<!--
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives](/Connectives/)),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.
-->

在标准库中，`≤-total` 是使用析取定义的（我们将在 [Connectives](/Connectives/) 章节定义）。
`+-monoʳ-≤`、`+-monoˡ-≤` 和 `+-mono-≤` 的证明方法和本书不同。
更多的参数是隐式申明的。


## Unicode

<!--
This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
-->

本章使用了如下 Unicode 符号：

    ≤  U+2264  小于等于 (\<=, \le)
    ≥  U+2265  大于等于 (\>=, \ge)
    ˡ  U+02E1  小写字母 L 标识符 (\^l)
    ʳ  U+02B3  小写字母 R 标识符 (\^r)

<!--
The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
-->

`\^l` 和 `\^r` 命令给出了左右箭头，以及上标字母 `l` 和 `r`。
