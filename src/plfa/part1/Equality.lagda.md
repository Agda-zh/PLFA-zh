---
title     : "Equality: 相等性与等式推理"
permalink : /Equality/
translators : ["Fangyi Zhou"]
progress  : 99
---

```agda
module plfa.part1.Equality where
```

<!--
Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.
-->

我们在论证的过程中经常会使用相等性。给定两个都为 `A` 类型的项 `M` 和 `N`，
我们用 `M ≡ N` 来表示 `M` 和 `N` 可以相互替换。在此之前，
我们将相等性作为一个基础运算，而现在我们来说明如何将其定义为一个归纳的数据类型。


<!--
## Imports
-->

## 导入

<!--
This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.
-->

本章节没有导入的内容。本书的每一章节，以及 Agda 标准库的每个模块都导入了相等性。
我们在此定义相等性，导入其他内容将会产生冲突。


<!--
## Equality
-->

## 相等性

<!--
We declare equality as follows:
-->

我们如下定义相等性：
```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
```

<!--
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.
-->

用其他的话来说，对于任意类型 `A` 和任意 `A` 类型的 `x`，构造子 `refl` 提供了
`x ≡ x` 的证明。所以，每个值等同于它本身，我们并没有其他办法来证明值的相等性。
这个定义里有不对称的地方，`_≡_` 的第一个参数（Argument）由 `x : A` 给出，
而第二个参数（Argument）则是由 `A → Set` 的索引给出。
这和我们尽可能多的使用参数（Parameter）的理念相符。`_≡_` 的第一个参数（Argument）
可以作为一个参数（Parameter），因为它不会变，而第二个参数（Argument）则必须是一个索引，
这样它才可以等于第一个。

<!--
We declare the precedence of equality as follows:
-->

我们如下定义相等性的优先级：

```agda
infix 4 _≡_
```

<!--
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.
-->

我们将 `_≡_` 的优先级设置为 4，与 `_≤_` 相同，所以其它算术运算符的结合都比它紧密。
由于它既不是左结合，也不是右结合的，因此 `x ≡ y ≡ z` 是不合法的。


<!--
## Equality is an equivalence relation
-->

## 相等性是一个等价关系（Equivalence Relation）

<!--
An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry:
-->

一个等价关系是自反、对称和传递的。其中自反性可以通过构造子 `refl` 直接从相等性的定义中得来。
我们可以直接地证明其对称性：

```agda
sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl
```

<!--
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.
-->

这个证明是怎么运作的呢？`sym` 参数的类型是 `x ≡ y`，但是等式的左手边被 `refl` 模式实例化了，
这要求 `x` 和 `y` 相等。因此，等式的右手边需要一个类型为 `x ≡ x` 的项，用 `refl` 即可。

<!--
It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:
-->

交互式地证明 `sym` 很有教育意义。首先，我们在左手边使用一个变量来表示参数，在右手边使用一个洞：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

<!--
If we go into the hole and type `C-c C-,` then Agda reports:
-->

如果我们进入这个洞，使用 `C-c C-,`，Agda 会告诉我们：

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

<!--
If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:
-->

在这个洞里，我们使用 `C-c C-c e`，Agda 会将 `e` 逐一展开为所有可能的构造子。
此处只有一个构造子：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

<!--
If we go into the hole again and type `C-c C-,` then Agda now reports:
-->

如果我们再次进入这个洞，重新使用 `C-c C-,`，然后 Agda 现在会告诉我们：

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

<!--
This is the key step-Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!
-->

这是一个重要的步骤—— Agda 发现了 `x` 和 `y` 必须相等，才能与模式 `refl` 相匹配。

<!--
Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type:
-->

最后，我们回到洞里，使用 `C-c C-r`，Agda 将会把洞变成一个可以满足给定类型的构造子实例。

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

<!--
This completes the definition as given above.
-->

我们至此完成了与之前给出证明相同的证明。

<!--
Transitivity is equally straightforward:
-->

传递性亦是很直接：

```agda
trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl  =  refl
```

<!--
Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.
-->

同样，交互式地证明这个特性是一个很好的练习，尤其是观察 Agda 的已知内容根据参数的实例而变化的过程。

<!--
## Congruence and substitution {#cong}
-->

## 合同性和替换性 {#cong}

<!--
Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both:
-->

相等性满足**合同性（Congruence）**。如果两个项相等，那么对它们使用相同的函数，
其结果仍然相等：

```agda
cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl  =  refl
```

<!--
Congruence of functions with two arguments is similar:
-->

两个参数的函数也满足合同性：

```agda
cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl  =  refl
```

<!--
Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms:
-->

在函数上的等价性也满足合同性。如果两个函数是相等的，那么它们作用在同一项上的结果是相等的：

```agda
cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl
```

<!--
Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second:
-->

相等性也满足**替换性（Substitution）**。
如果两个值相等，其中一个满足某谓词，那么另一个也满足此谓词。

```agda
subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px
```
A predicate is a proposition over values of some type `A`, and since we model
_propositions as types_, a predicate is a type parameterized in `A`.
As an example, consider our earlier examples `even` and `odd` from
Chapter [Relations](/Relations/#even-and-odd), which are predicates on natural numbers `ℕ`.
(We will compare representing predicates as inductive data types `A → Set`
versus functions to booleans `A → Bool` in Chapter [Decidable](/Decidable/).)

<!--
## Chains of equations
-->

## 等式串

<!--
Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library:
-->

我们在此演示如何使用等式串来论证，正如本书中使用证明形式。我们将声明放在一个叫做
`≡-Reasoning` 的模块里，与 Agda 标准库中的格式相对应。

```agda
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning
```

<!--
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.
-->

这是我们第一次使用嵌套的模块。它包括了关键字 `module` 和后续的模块名、隐式或显式参数，
关键字 `where`，和模块中的内容（在缩进内）。模块里可以包括任何形式的声明，也可以包括其他模块。
嵌套的模块和本书每章节所定义的顶层模块相似，只是顶层模块不需要缩进。
打开（`open`）一个模块会把模块内的所有定义导入进当前的环境中。

<!--
As an example, let's look at a proof of transitivity
as a chain of equations:
-->

举个例子，我们来看看如何用等式串证明传递性：

```agda
trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
```

<!--
According to the fixity declarations, the body parses as follows:
-->

根据其定义，等式右边会被解析成如下：

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

<!--
The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:
-->

这里 `begin` 的使用纯粹是装饰性的，因为它直接返回了其参数。其参数包括了
`_≡⟨_⟩_` 作用于 `x`、`x≡y` 和 `y ≡⟨ y≡z ⟩ (z ∎)`。第一个参数是一个项 `x`，
而第二、第三个参数分别是等式 `x ≡ y`、`y ≡ z` 的证明，它们在 `_≡⟨_⟩_` 的定义中用
`trans` 连接起来，形成 `x ≡ z` 的证明。`y ≡ z` 的证明包括了 `_≡⟨_⟩_` 作用于 `y`、
`y≡z` 和 `z ∎`。第一个参数是一个项 `y`，而第二、第三个参数分别是等式 `y ≡ z`、`z ≡ z` 的证明，
它们在 `_≡⟨_⟩_` 的定义中用 `trans` 连接起来，形成 `y ≡ z` 的证明。最后，`z ≡ z`
的证明包括了 `_∎` 作用于 `z` 之上，使用了 `refl`。经过化简，上述定义等同于：

    trans x≡y (trans y≡z refl)

<!--
We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` that ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.
-->

我们可以把任意等式串转化成一系列的 `trans` 的使用。这样的证明更加精简，但是更难以阅读。
`∎` 的小窍门意味着等式串化简成为的一系列 `trans` 会以 `trans e refl` 结尾，尽管只需要 `e`
就足够了，这里的 `e` 是等式的证明。

#### Exercise `trans` and `≡-Reasoning` (practice)

Sadly, we cannot use the definition of trans' using ≡-Reasoning as the definition
for trans. Can you see why? (Hint: look at the definition of `_≡⟨_⟩_`)

```agda
-- Your code goes here
```

<!--
## Chains of equations, another example
-->

## 等式串的另外一个例子

<!--
As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict:
-->

我们重新证明加法的交换律来作为等式串的第二个例子。我们首先重复自然数和加法的定义。
我们不能导入它们（正如本章节开头中所解释的那样），因为那样会产生一个冲突：

```agda
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)
```

<!--
To save space we postulate (rather than prove in full) two lemmas:
-->

为了节约空间，我们假设两条引理（而不是证明它们）：

```agda
postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
```

<!--
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.
-->

这是我们第一次使用**假设（Postulate）**。假设为一个标识符指定一个签名，但是不提供定义。
我们在这里假设之前证明过的东西，来节约空间。假设在使用时必须加以注意。如果假设的内容为假，
那么我们可以证明出任何东西。

<!--
We then repeat the proof of commutativity:
-->

我们接下来重复交换律的证明：

```agda
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
```

<!--
The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.
-->

论证的过程和之前的相似。我们在不需要解释的地方使用 `_≡⟨⟩_`，我们可以认为
`_≡⟨⟩_` 和 `_≡⟨ refl ⟩_` 是等价的。

<!--
Agda always treats a term as equivalent to its
simplified term.  The reason that one can write
-->

Agda 总是认为一个项与其化简的项是等价的。我们之所以可以写出

      suc (n + m)
    ≡⟨⟩
      suc n + m

<!--
is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write
-->

是因为 Agda 认为它们是一样的。这也意味着我们可以交换两行的顺序，写出

      suc n + m
    ≡⟨⟩
      suc (n + m)

<!--
and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.
-->

而 Agda 并不会反对。Agda 只会检查由 `≡⟨⟩` 隔开的项是否化简后相同。
而书写的顺序合不合理则是由我们自行决定。


<!--
#### Exercise `≤-Reasoning` (stretch)
-->

#### 练习 `≤-Reasoning` (延伸)

<!--
The proof of monotonicity from
Chapter [Relations](/Relations/)
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.
-->

章节 [Relations](/Relations/) 中的单调性证明亦可以用相似于 `≡-Reasoning` 的，更易于理解的形式给出。
相似地来定义 `≤-Reasoning`，并用其重新给出加法对于不等式是单调的证明。重写 `+-monoˡ-≤`、`+-monoʳ-≤`
和 `+-mono-≤` 的定义。



```agda
-- 请将代码写在此处。
```


<!--
## Rewriting
-->

## 重写

<!--
Consider a property of natural numbers, such as being even.
We repeat the earlier definition:
-->

考虑一个自然数的性质，比如说一个数是偶数。我们重复之前给出的定义：

```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```

<!--
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.
-->

在前面的部分中，我们证明了加法满足交换律。给定 `even (m + n)` 成立的证据，我们应当可以用它来做
`even (n + m)` 成立的证据。

<!--
Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality:
-->

Agda 对这种论证有特殊记法的支持——我们之前提到过的 `rewrite` 记法。来启用这种记法，
我们只用编译程序指令来告诉 Agda 什么类型对应相等性：

```agda
{-# BUILTIN EQUALITY _≡_ #-}
```

<!--
We can then prove the desired property as follows:
-->

我们然后就可以如下证明求证的性质：

```agda
even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev  rewrite +-comm n m  =  ev
```

<!--
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.
-->

在这里，`ev` 包括了所有 `even (m + n)` 成立的证据，我们证明它亦可作为 `even (n + m)`
成立的证据。一般来说，关键字 `rewrite` 之后跟着一个等式的证明，这个等式被用于重写目标和任意作用域内变量的类型。

<!--
It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:
-->

交互性地证明 `even-comm` 是很有帮助的。一开始，我们先给左边的参数赋予变量，给右手边放上一个洞：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

<!--
If we go into the hole and type `C-c C-,` then Agda reports:
-->

如果我们进入洞里，输入 `C-c C-,`，Agda 会报告：

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

<!--
Now we add the rewrite:
-->

现在我们加入重写：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

<!--
If we go into the hole again and type `C-c C-,` then Agda now reports:
-->

如果我们再次进入洞里，并输入 `C-c C-,`，Agda 现在会报告：

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

<!--
The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.
-->

目标里的参数被交换了。现在 `ev` 显然满足目标条件，输入 `C-c C-a` 会用 `ev` 来填充这个洞。
命令 `C-c C-a` 可以进行自动搜索，检查作用域内的变量是否和目标有相同的类型。


<!--
## Multiple rewrites
-->

## 多重重写

<!--
One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities:
-->

我们可以多次使用重写，以竖线隔开。举个例子，这里是加法交换律的第二个证明，使用重写而不是等式串：

```agda
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero    n  rewrite +-identity n             =  refl
+-comm′ (suc m) n  rewrite +-suc n m | +-comm′ m n  =  refl
```

<!--
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.
-->

这个证明更加的简短。之前的证明用 `cong suc (+-comm m n)` 作为使用归纳假设的说明，
而这里我们使用 `+-comm m n` 来重写就足够了，因为重写可以将合同性考虑在其中。尽管使用重写的证明更加的简短，
使用等式串的证明能容易理解，我们将尽可能的使用后者。


<!--
## Rewriting expanded
-->

## 深入重写

<!--
The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction:
-->

`rewrite` 记法实际上是 `with` 抽象的一种应用：

```agda
even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev
```

<!--
In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)
-->

总的来着，我们可以在 `with` 后面跟上任何数量的表达式，用竖线分隔开，并且在每个等式中使用相同个数的模式。
我们经常将表达式和模式如上对齐。这个第一列表明了 `m + n` 和 `n + m` 是相同的，第二列使用相应等式来证明的前述的断言。
注意在这里使用的**点模式（Dot Pattern）**，`.(n + m)`。点模式由一个点和一个表达式组成，
在其他信息迫使这个值和点模式中的值相等时使用。在这里，`m + n` 和 `n + m` 由后续的
`+-comm m n` 与 `refl` 的匹配来识别。我们可能会认为第一种情况是多余的，因为第二种情况中才蕴涵了需要的信息。
但实际上 Agda 在这件事上很挑剔——省略第一条或者更换顺序会让 Agda 报告一个错误。（试一试你就知道！）

<!--
In this case, we can avoid rewrite by simply applying the substitution
function defined earlier:
-->

在这种情况中，我们也可以使用之前定义的替换函数来避免使用重写：

```agda
even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ m n  =  subst even (+-comm m n)
```

<!--
Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.
-->

尽管如此，重写是 Agda 工具箱中很重要的一部分。我们会偶尔使用它，但是它有的时候是必要的。


<!--
## Leibniz equality
-->

## 莱布尼兹（Leibniz）相等性

<!--
The form of asserting equality that we have used is due to Martin-Löf,
and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin-Löf equality.
-->

我们使用的相等性断言的形式源于 Martin-Löf，于 1975 年发表。一个更早的形式源于莱布尼兹，
于 1686 年发表。莱布尼兹断言的相等性表示**不可分辨的实体（Identity of Indiscernibles）**：
两个对象相等当且仅当它们满足完全相同的性质。这条原理有时被称作莱布尼兹定律（Leibniz' Law），
与史波克定律紧密相关：「一个不造成区别的区别不是区别」。我们在这里定义莱布尼兹相等性，
并证明两个项满足莱布尼兹相等性当且仅当其满足 Martin-Löf 相等性。

<!--
Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.
-->

莱布尼兹相等性一般如下来定义：`x ≐ y` 当每个对于 `x` 成立的性质 `P` 对于 `y` 也成立时成立。
可能这有些出乎意料，但是这个定义亦足够保证其相反的命题：每个对于 `y` 成立的性质 `P` 对于 `x` 也成立。

<!--
Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`:
-->

令 `x` 和 `y` 为类型 `A` 的对象。我们定义 `x ≐ y` 成立，当每个对于类型 `A` 成立的谓词 `P`，
我们有 `P x` 蕴涵了 `P y`：

```agda
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
```

<!--
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.
-->

我们不能在左手边使用 `x ≐ y`，取而代之我们使用 `_≐_ {A} x y` 来提供隐式参数 `A`，这样 `A`
可以出现在右手边。

<!--
This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.
-->

这是我们第一次使用**等级（Levels）**。我们不能将 `Set` 赋予类型 `Set`，因为这会导致自相矛盾，
比如罗素悖论（Russell's Paradox）或者 Girard 悖论。不同的是，我们有一个阶级的类型：其中
`Set : Set₁`，`Set₁ : Set₂`，以此类推。实际上，`Set` 本身就是 `Set₀` 的缩写。定义
`_≐_` 的等式在右手边提到了 `Set`，因此签名中必须使用 `Set₁`。我们稍后将进一步介绍等级。

<!--
Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition:
-->

莱布尼兹相等性是自反和传递的。自反性由恒等函数的变种得来，传递性由函数组合的变种得来：

```agda
refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px  =  y≐z P (x≐y P Px)
```

<!--
Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well:
-->

对称性就没有那么显然了。我们需要证明如果对于所有谓词 `P`，`P x` 蕴涵 `P y`，
那么反方向的蕴涵也成立。

```agda
sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx
```

<!--
Given `x ≐ y`, a specific `P`, we have to construct a proof that `P y`
implies `P x`.  To do so, we instantiate the equality with a predicate
`Q` such that `Q z` holds if `P z` implies `P x`.  The property `Q x`
is trivial by reflexivity, and hence `Q y` follows from `x ≐ y`.  But
`Q y` is exactly a proof of what we require, that `P y` implies `P x`.
-->

给定 `x ≐ y` 和一个特定的 `P`，我们需要构造一个 `P y` 蕴涵 `P x` 的证明。
我们首先用一个谓词 `Q` 将相等性实例化，使得 `Q z` 在 `P z` 蕴涵 `P x` 时成立。
`Q x` 这个性质是显然的，由自反性可以得出，由此通过 `x ≐ y` 就能推出 `Q y` 成立。而 `Q y`
正是我们需要的证明，即 `P y` 蕴涵 `P x`。

<!--
We now show that Martin-Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`:
-->

我们现在来证明 Martin-Löf 相等性蕴涵了莱布尼兹相等性，以及其逆命题。在正方向上，
如果我们已知 `x ≡ y`，我们需要对于任意的 `P`，将 `P x` 的证明转换为 `P y` 的证明。
我们很容易就可以做到这一点，因为 `x` 与 `y` 相等意味着任何 `P x` 的证明即是 `P y` 的证明。

```agda
≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P  =  subst P x≡y
```

<!--
This direction follows from substitution, which we showed earlier.
-->

因为这个方向由替换性可以得来，如之前证明的那样。

<!--
In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`:
-->

在反方向上，我们已知对于任何 `P`，我们可以将 `P x` 的证明转换成 `P y` 的证明，
我们需要证明 `x ≡ y`：

```agda
≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx
```

<!--
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin-Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.
-->

此证明与莱布尼兹相等性的对称性证明相似。我们取谓词 `Q`，使得 `Q z` 在 `x ≡ z` 成立时成立。
那么 `Q x` 是显然的，由 Martin Löf 相等性的自反性得来。从而 `Q y` 由 `x ≐ y` 可得，
而 `Q y` 即是我们所需要的 `x ≡ y` 的证明。

<!--
(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)
-->

（本部分的内容由此处改编得来：
*≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*
作者：Andreas Abel、Jesper Cockx、Dominique Devries、Andreas Nuyts 与 Philip Wadler，
草稿，2017）


<!--
## Universe polymorphism {#unipoly}
-->

## 全体多态 {#unipoly}

<!--
As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?
-->

正如我们之前看到的那样，不是每个类型都属于 `Set`，但是每个类型都属于类型阶级的某处，
`Set₀`、`Set₁`、`Set₂`等等。其中 `Set` 是 `Set₀` 的缩写，此外 `Set₀ : Set₁`，`Set₁ : Set₂`，以此类推。
当我们需要比较两个属于 `Set` 的类型的值时，我们之前给出的定义是足够的，
但如果我们需要比较对于任何等级 `ℓ`，两个属于 `Set ℓ` 的类型的值该怎么办呢？

<!--
The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following:
-->

答案是**全体多态（Universe Polymorphism）**，一个定义可以根据任何等级 `ℓ` 来做出。
为了使用等级，我们首先导入下列内容：

```agda
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
```

<!--
We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.
-->

我们将构造子 `zero` 和 `suc` 重命名至 `lzero` 和 `lsuc`，为了防止自然数和等级之间的混淆。

<!--
Levels are isomorphic to natural numbers, and have similar constructors:
-->

等级与自然数是同构的，有相似的构造子：

    lzero : Level
    lsuc  : Level → Level

<!--
The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for
-->

`Set₀`、`Set₁`、`Set₂` 等名称，是下列的简写：

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

<!--
and so on. There is also an operator
-->

以此类推。我们还有一个运算符：

    _⊔_ : Level → Level → Level

<!--
that given two levels returns the larger of the two.
-->

给定两个等级，返回两者中较大的那个。

<!--
Here is the definition of equality, generalised to an arbitrary level:
-->

下面是相等性的定义，推广到任意等级：

```agda
data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x
```

<!--
Similarly, here is the generalised definition of symmetry:
-->

相似的，下面是对称性的推广定义：

```agda
sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    ------
  → y ≡′ x
sym′ refl′ = refl′
```

<!--
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.
-->

为了简洁，我们在本书中给出的定义将避免使用全体多态，但是大多数标准库中的定义，
包括相等性的定义，都推广到了任意等级，如上所示。

<!--
Here is the generalised definition of Leibniz equality:
-->

下面是莱布尼兹相等性的推广定义：

```agda
_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y
```

<!--
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.
-->

之前，签名中使用了 `Set₁` 来作为一个值包括了 `Set` 的类型；而此处，我们使用
`Set (lsuc ℓ)` 来作为一个值包括了 `Set ℓ` 的类型。

<!--
Most other functions in the standard library are also generalised to
arbitrary levels. For instance, here is the definition of composition.
-->

标准库中的大部分函数都泛化到了任意层级。例如，以下是复合的定义。

```agda
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)
```

<!--
Further information on levels can be found in the [Agda docs][docs].
-->

更多关于层级的信息可以从[Agda 文档][docs]中查询。

[docs]: https://agda.readthedocs.io/en/v2.6.1/language/universe-levels.html


<!--
## Standard library
-->

## 标准库

<!--
Definitions similar to those in this chapter can be found in the standard
library. The Agda standard library defines `_≡⟨_⟩_` as `step-≡`, [which reverses
the order of the arguments][step-≡]. The standard library also defines a syntax
macro, which is automatically imported whenever you import `step-≡`, which
recovers the original argument order:
-->

标准库中可以找到与本章节中相似的定义。Agda 标准库将 `_≡⟨_⟩_` 定义为 `step-≡`，
[它反转了参数的顺序][step-≡]。标准库还定义了一个语法宏，它可以在你导入 `step-≡`
时被自动导入，它能够恢复原始的参数顺序：

```agda
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
```

<!--
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.
-->

这里的导入以注释的形式给出，以防止冲突，如引言中解释的那样。

[step-≡]: https://github.com/agda/agda-stdlib/blob/master/CHANGELOG/v1.3.md#changes-to-how-equational-reasoning-is-implemented

## Unicode

<!--
This chapter uses the following unicode:

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
-->

本章节使用下列 Unicode：

    ≡  U+2261  等同于 (\==, \equiv)
    ⟨  U+27E8  数学左尖括号 (\<)
    ⟩  U+27E9  数学右尖括号 (\>)
    ∎  U+220E  证毕 (\qed)
    ≐  U+2250  趋近于极限 (\.=)
    ℓ  U+2113  手写小写 L (\ell)
    ⊔  U+2294  正方形向上开口 (\lub)
    ₀  U+2080  下标 0 (\_0)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
