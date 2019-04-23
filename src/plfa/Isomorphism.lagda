---
title     : "Isomorphism: 同构与嵌入"
layout    : page
prev      : /Equality/
permalink : /Isomorphism/
next      : /Connectives/
translators : ["Fangyi Zhou"]
progress  : 67
---

\begin{code}
module plfa.Isomorphism where
\end{code}

本部分介绍同构（Isomorphism）与嵌入（Embedding）。
同构可以断言两个类型是相等的，嵌入可以断言一个类型比另一个类型小。
我们会在下一章中使用同构来展示类型上的运算，例如积或者和，满足类似于交换律、结合律和分配律的性质。
{::comment}
This section introduces isomorphism as a way of asserting that two
types are equal, and embedding as a way of asserting that one type is
smaller than another.  We apply isomorphisms in the next chapter
to demonstrate that operations on types such as product and sum
satisfy properties akin to associativity, commutativity, and
distributivity.
{:/}

## 导入
{::comment}
## Imports
{:/}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
\end{code}


## Lambda 表达式
{::comment}
## Lambda expressions
{:/}

本章节开头将补充一些有用的基础知识：lambda 表达式，函数组合，以及外延性。
{::comment}
The chapter begins with a few preliminaries that will be useful
here and elsewhere: lambda expressions, function composition, and
extensionality.
{:/}

*Lambda 表达式*提供了一种简洁的定义函数的方法，且不需要提供函数名。一个如同这样的项：
{::comment}
_Lambda expressions_ provide a compact way to define functions without
naming them.  A term of the form
{:/}

    λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

等同于定义一个函数 `f`，使用下列等式：
{::comment}
is equivalent to a function `f` defined by the equations
{:/}

    f P₁ = N₁
    ⋯
    f Pₙ = Nₙ

其中 `Pₙ` 是模式（即等式的左手边），`Nₙ` 是表达式（即等式的右手边）。
{::comment}
where the `Pₙ` are patterns (left-hand sides of an equation) and the
`Nₙ` are expressions (right-hand side of an equation).
{:/}

如果只有一个等式，且模式是一个变量，我们亦可使用下面的语法：
{::comment}
In the case that there is one equation and the pattern is a variable,
we may also use the syntax
{:/}

    λ x → N

或者
{::comment}
or
{:/}

    λ (x : A) → N

两个都与 `λ{x → N}` 等价。后者可以指定函数的作用域。
{::comment}
both of which are equivalent to `λ{x → N}`. The latter allows one to
specify the domain of the function.
{:/}

往往使用匿名的 lambda 表达式比使用带名字的函数要方便：它避免了冗长的类型声明；
其定义出现在其使用的地方，所以在书写时不需要记得提前声明，在阅读时不需要上下搜索函数定义。
{::comment}
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition in the code.
{:/}


## 函数组合 （Function Composition）
{::comment}
## Function composition
{:/}

接下来，我们将使用函数组合：
{::comment}
In what follows, we will make use of function composition:
{:/}
\begin{code}
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)
\end{code}
`g ∘ f` 是一个函数，先使用函数 `f`，再使用函数 `g`。
一个等价的定义，使用 lambda 表达式，如下：
{::comment}
Thus, `g ∘ f` is the function that first applies `f` and
then applies `g`.  An equivalent definition, exploiting lambda
expressions, is as follows:
{:/}
\begin{code}
_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)
\end{code}


## 外延性（Extensionality） {#extensionality}
{::comment}
## Extensionality {#extensionality}
{:/}

外延性断言了区分函数的唯一方法是应用它们。如果两个函数作用在相同的参数上永远返回相同的结果，
那么两个函数相同。这是 `cong-app` 的逆命题，在[之前][plfa.Equality#cong]有所介绍。
{::comment}
Extensionality asserts that the only way to distinguish functions is
by applying them; if two functions applied to the same argument always
yield the same result, then they are the same function.  It is the
converse of `cong-app`, as introduced
[earlier][plfa.Equality#cong].
{:/}

Agda 并不预设外延性，但我们可以假设其成立：
{::comment}
Agda does not presume extensionality, but we can postulate that it holds:
{:/}
\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
\end{code}
假设外延性不会造成困顿，因为我们知道它与 Agda 使用的理论是连贯一致的。
{::comment}
Postulating extensionality does not lead to difficulties, as it is
known to be consistent with the theory that underlies Agda.
{:/}

举个例子，我们考虑两个库都定义了加法，一个按照我们在 [Naturals][plfa.Naturals]
章节中那样定义，另一个如下，反过来定义：
{::comment}
As an example, consider that we need results from two libraries,
one where addition is defined, as in
Chapter [Naturals][plfa.Naturals],
and one where it is defined the other way around.
{:/}
\begin{code}
_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)
\end{code}
通过使用交换律，我们可以简单地证明两个运算符在给定相同参数的情况下，
会返回相同的值：
{::comment}
Applying commutativity, it is easy to show that both operators always
return the same result given the same arguments:
{:/}
\begin{code}
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)
\end{code}

然而，有时断言两个运算符是无法区分的会更加方便。我们可以使用两次外延性：
{::comment}
However, it might be convenient to assert that the two operators are
actually indistinguishable. This we can do via two applications of
extensionality:
{:/}
\begin{code}
same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))
\end{code}
我们偶尔需要在之后的情况中假设外延性。
{::comment}
We occasionally need to postulate extensionality in what follows.
{:/}


## 同构（Isomorphism）
{::comment}
## Isomorphism
{:/}

如果两个集合有一一对应的关系，那么它们是同构的。
下面是同构的正式定义：
{::comment}
Two sets are isomorphic if they are in one-to-one correspondence.
Here is a formal definition of isomorphism:
{:/}
\begin{code}
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
\end{code}
我们来一一展开这个定义。一个集合 `A` 和 `B` 之间的同构有四个要素：
+ 从 `A` 到 `B` 的函数 `to`
+ 从 `B` 回到 `A` 的函数 `from`
+ `from` 是 `to` 的*左逆*（left-inverse）的证明 `from∘to`
+ `from` 是 `to` 的*右逆*（right-inverse）的证明 `to∘from`

{::comment}
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `from` from `B` back to `A`,
+ Evidence `from∘to` asserting that `from` is a *left-inverse* for `to`,
+ Evidence `to∘from` asserting that `from` is a *right-inverse* for `to`.
{:/}

具体来说，第三条断言了 `from ∘ to` 是恒等函数，第四条断言了 `to ∘ from` 是恒等函数，
它们的名称由此得来。声明 `open _≃_` 使得 `to`、`from`、`from∘to` 和 `to∘from`
在当前作用域内可用，否则我们需要使用类似 `_≃_.to` 的写法。
{::comment}
In particular, the third asserts that `from ∘ to` is the identity, and
the fourth that `to ∘ from` is the identity, hence the names.
The declaration `open _≃_` makes available the names `to`, `from`,
`from∘to`, and `to∘from`, otherwise we would need to write `_≃_.to` and so on.
{:/}

这是我们第一次使用记录（Record）。记录声明等同于下面的归纳数据声明：
{::comment}
The above is our first use of records. A record declaration is equivalent
to a corresponding inductive data declaration:
{:/}
\begin{code}
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g
\end{code}

我们用下面的语法来构造一个记录类型的值：
{::comment}
We construct values of the record type with the syntax
{:/}

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

这与使用相应的归纳类型的构造器对应：
{::comment}
which corresponds to using the constructor of the corresponding
inductive type
{:/}

    mk-≃′ f g g∘f f∘g

其中 `f`、`g`、`g∘f` 和 `f∘g` 是相应类型的值。
{::comment}
where `f`, `g`, `g∘f`, and `f∘g` are values of suitable types.
{:/}


## 同构是一个等价关系
{::comment}
## Isomorphism is an equivalence
{:/}

同构是一个等价关系。这意味着它自反、对称、传递。要证明同构是自反的，我们用恒等函数
作为 `to` 和 `from`：
{::comment}
Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `from` to be the identity function:
{:/}
\begin{code}
≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }
\end{code}
如上，`to` 和 `from` 都是恒等函数，`from∘to` 和 `to∘from` 都是丢弃参数、返回
`refl` 的函数。在这样的情况下，`refl` 足够可以证明左逆，因为 `from (to x)`
化简为 `x`。右逆的证明同理。
{::comment}
In the above, `to` and `from` are both bound to identity functions,
and `from∘to` and `to∘from` are both bound to functions that discard
their argument and return `refl`.  In this case, `refl` alone is an
adequate proof since for the left inverse, `from (to x)`
simplifies to `x`, and similarly for the right inverse.
{:/}

要证明同构是对称的，我们把 `to` 和 `from`、`from∘to` 和 `to∘from` 互换：
{::comment}
To show isomorphism is symmetric, we simply swap the roles of `to`
and `from`, and `from∘to` and `to∘from`:
{:/}
\begin{code}
≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }
\end{code}

要证明同构是传递的，我们将 `to` 和 `from` 函数进行组合，并使用相等性论证来结合左逆和右逆：
{::comment}
To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
{:/}
\begin{code}
≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to       = to   B≃C ∘ to   A≃B
    ; from     = from A≃B ∘ from B≃C
    ; from∘to  = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
     }
\end{code}


## 同构的相等性论证
{::comment}
## Equational reasoning for isomorphism
{:/}

我们可以直接的构造一种同构的相等性论证方法。我们对之前的相等性论证定义进行修改。
我们省略 `_≡⟨⟩_` 的定义，因为简单的同构比简单的相等性出现的少很多：
{::comment}
It is straightforward to support a variant of equational reasoning for
isomorphism.  We essentially copy the previous definition
of equality for isomorphism.  We omit the form that corresponds to `_≡⟨⟩_`, since
trivial isomorphisms arise far less often than trivial equalities:
{:/}

\begin{code}
module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning
\end{code}


## Embedding

We also need the notion of _embedding_, which is a weakening of
isomorphism.  While an isomorphism shows that two types are in
one-to-one correspondence, an embedding shows that the first type is
included in the second; or, equivalently, that there is a many-to-one
correspondence between the second type and the first.

Here is the formal definition of embedding:
\begin{code}
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_
\end{code}
It is the same as an isomorphism, save that it lacks the `to∘from` field.
Hence, we know that `from` is left-inverse to `to`, but not that `from`
is right-inverse to `to`.

Embedding is reflexive and transitive, but not symmetric.  The proofs
are cut down versions of the similar proofs for isomorphism:
\begin{code}
≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }
\end{code}

It is also easy to see that if two types embed in each other, and the
embedding functions correspond, then they are isomorphic.  This is a
weak form of anti-symmetry:
\begin{code}
≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }
\end{code}
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `from` components from the two embeddings to obtain
the right inverse of the isomorphism.

## Equational reasoning for embedding

We can also support tabular reasoning for embedding,
analogous to that used for isomorphism:

\begin{code}
module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning
\end{code}

#### Exercise `≃-implies-≲`

Show that every isomorphism implies an embedding.
\begin{code}
postulate
  ≃-implies-≲ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≲ B
\end{code}

\begin{code}
-- 在此处书写你的代码
\end{code}

#### Exercise `_⇔_` {#iff}

Define equivalence of propositions (also known as "if and only if") as follows:
\begin{code}
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
\end{code}
Show that equivalence is reflexive, symmetric, and transitive.

\begin{code}
-- 在此处书写你的代码
\end{code}

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin][plfa.Naturals#Bin] and
[Bin-laws][plfa.Induction#Bin-laws]
define a datatype of bitstrings representing natural numbers:
\begin{code}
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
\end{code}
And ask you to define the following functions

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
\begin{code}
-- 在此处书写你的代码
\end{code}

Why do `to` and `from` not form an isomorphism?

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
\begin{code}
import Function using (_∘_)
import Function.Inverse using (_↔_)
import Function.LeftInverse using (_↞_)
\end{code}
The standard library `_↔_` and `_↞_` correspond to our `_≃_` and
`_≲_`, respectively, but those in the standard library are less
convenient, since they depend on a nested record structure and are
parameterised with regard to an arbitrary notion of equivalence.

## Unicode

This chapter uses the following unicode:

    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
