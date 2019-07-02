---
title     : "Lists: 列表与高阶函数"
layout    : page
prev      : /Decidable/
permalink : /Lists/
next      : /Lambda/
translators: ["Fangyi Zhou"]
progress  : 100
---

\begin{code}
module plfa.Lists where
\end{code}

{::comment}
This chapter discusses the list data type.  It gives further examples
of many of the techniques we have developed so far, and provides
examples of polymorphic types and higher-order functions.
{:/}

本章节讨论列表（List）数据类型。我们用列表作为例子，来使用我们之前学习的技巧。同时，
列表也给我们带来多态类型（Polymorphic Types）和高阶函数（Higher-order Functions）的例子。

{::comment}
## Imports
{:/}

## 导入

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.Isomorphism using (_≃_; _⇔_)
\end{code}


{::comment}
## Lists
{:/}

## 列表

{::comment}
Lists are defined in Agda as follows:
{:/}

Agda 中的列表如下定义：
\begin{code}
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
\end{code}

{::comment}
Let's unpack this definition. If `A` is a set, then `List A` is a set.
The next two lines tell us that `[]` (pronounced _nil_) is a list of
type `A` (often called the _empty_ list), and that `_∷_` (pronounced
_cons_, short for _constructor_) takes a value of type `A` and a value
of type `List A` and returns a value of type `List A`.  Operator `_∷_`
has precedence level 5 and associates to the right.
{:/}

我们来仔细研究这个定义。如果 `A` 是个集合，那么 `List A` 也是一个集合。接下来的两行告诉我们
`[]` （读作 *nil*）是一个类型为 `A` 的列表（通常被叫做*空*列表），`_∷_`（读作 *cons*，是
*constructor* 的简写）取一个类型为 `A` 的值，和一个类型为 `List A` 的值，返回一个类型为
`List A` 的值。`_∷_` 运算符的优先级是 5，向右结合。

{::comment}
For example,
{:/}

例如：

\begin{code}
_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []
\end{code}

{::comment}
denotes the list of the first three natural numbers.  Since `_∷_`
associates to the right, the term parses as `0 ∷ (1 ∷ (2 ∷ []))`.
Here `0` is the first element of the list, called the _head_,
and `1 ∷ (2 ∷ [])` is a list of the remaining elements, called the
_tail_. A list is a strange beast: it has a head and a tail,
nothing in between, and the tail is itself another list!
{:/}

表示了一个三个自然数的列表。因为 `_∷_` 向右结合，这一项被解析成 `0 ∷ (1 ∷ (2 ∷ []))`。
在这里，`0` 是列表的第一个元素，称之为*头*（Head），`1 ∷ (2 ∷ [])` 是剩下元素的列表，
称之为*尾*（Tail）。列表是一个奇怪的怪兽：它有一头一尾，中间没有东西，然而它的尾巴又是一个列表！

{::comment}
As we've seen, parameterised types can be translated to
indexed types. The definition above is equivalent to the following:
{:/}

正如我们所见，参数化的类型可以被转换成索引类型。上面的定义与下列等价：

\begin{code}
data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A
\end{code}
{::comment}
Each constructor takes the parameter as an implicit argument.
Thus, our example list could also be written:
{:/}

每个构造器将参数作为隐式参数。因此我们列表的例子也可以写作：

\begin{code}
_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))
\end{code}
{::comment}
where here we have provided the implicit parameters explicitly.
{:/}

此处我们将隐式参数显式地声明。

{::comment}
Including the pragma:
{:/}

包含下面的编译器指令

    {-# BUILTIN LIST List #-}

{::comment}
tells Agda that the type `List` corresponds to the Haskell type
list, and the constructors `[]` and `_∷_` correspond to nil and
cons respectively, allowing a more efficient representation of lists.
{:/}

告诉 Agda，`List` 类型对应了 Haskell 的列表类型，构造器 `[]` 和 `_∷_`
分别代表了 nil 和 cons，这可以让列表的表示更加的有效率。

{::comment}
## List syntax
{:/}

## 列表语法

{::comment}
We can write lists more conveniently by introducing the following definitions:
{:/}

我们可以用下面的定义，更简便地表示列表：

\begin{code}
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
\end{code}
{::comment}
This is our first use of pattern declarations.  For instance,
the third line tells us that `[ x , y , z ]` is equivalent to
`x ∷ y ∷ z ∷ []`, and permits the former to appear either in
a pattern on the left-hand side of an equation, or a term
on the right-hand side of an equation.
{:/}

这是我们第一次使用模式声明。举例来说，第三行告诉我们 `[ x , y , z ]` 等价于
`x ∷ y ∷ z ∷ []`。前者可以在模式或者等式的左手边，或者是等式右手边的项中出现。

{::comment}
## Append
{:/}

## 附加

{::comment}
Our first function on lists is written `_++_` and pronounced
_append_:
{:/}

我们对于列表的第一个函数写作 `_++_`，读作*附加*（Append）：

\begin{code}
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
\end{code}
{::comment}
The type `A` is an implicit argument to append, making it a
_polymorphic_ function (one that can be used at many types).  The
empty list appended to another list yields the other list.  A
non-empty list appended to another list yields a list with head the
same as the head of the first list and tail the same as the tail of
the first list appended to the second list.
{:/}

`A` 类型是附加的隐式参数，这让这个函数变为一个*多态*（Polymorphic）函数
（即可以用作多种类型）。空列表附加到另一个列表得到是第二个列表。非空列表附加到
另一个列表，得到的列表的头是第一个列表的头，尾是第一个列表的尾附加至第二个列表的结果。

{::comment}
Here is an example, showing how to compute the result
of appending two lists:
{:/}

我们举个例子，来展示将两个列表附加的计算过程：

\begin{code}
_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎
\end{code}
{::comment}
Appending two lists requires time linear in the
number of elements in the first list.
{:/}

附加两个列表需要对于第一个列表元素个数线性的时间。


{::comment}
## Reasoning about append
{:/}

## 论证附加

{::comment}
We can reason about lists in much the same way that we reason
about numbers.  Here is the proof that append is associative:
{:/}

我们可以与用论证数几乎相同的方法来论证列表。下面是附加满足结合律的证明：
\begin{code}
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎
\end{code}
{::comment}
The proof is by induction on the first argument. The base case instantiates
to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs`,
and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated by a recursive
invocation of the proof, in this case `++-assoc xs ys zs`.
{:/}

证明对于第一个参数进行归纳。起始步骤将列表实例化为 `[]`，由直接的运算可证。
归纳步骤将列表实例化为 `x ∷ xs`，由直接的运算配合归纳假设可证。
与往常一样，归纳假设由递归使用证明函数来表明，此处为 `++-assoc xs ys zs`。

{::comment}
Recall that Agda supports [sections][plfa.Induction#sections].
Applying `cong (x ∷_)` promotes the inductive hypothesis:
{:/}

回忆到 Agda 支持[片段][plfa.Induction#sections]。使用 `cong (x ∷_)`
可以将归纳假设：

    (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

{::comment}
to the equality:
{:/}

提升至等式：

    x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ (xs ++ (ys ++ zs))

{::comment}
which is needed in the proof.
{:/}

即证明中所需。

{::comment}
It is also easy to show that `[]` is a left and right identity for `_++_`.
That it is a left identity is immediate from the definition:
{:/}

我们也可以简单地证明 `[]` 是 `_++_` 的左幺元和右幺元。
左幺元的证明从定义中即可得：

\begin{code}
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎
\end{code}
{::comment}
That it is a right identity follows by simple induction:
{:/}

右幺元的证明可由简单的归纳得到：
\begin{code}
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎
\end{code}
{::comment}
As we will see later,
these three properties establish that `_++_` and `[]` form
a _monoid_ over lists.
{:/}

我们之后会了解到，这三条性质表明了 `_++_` 和 `[]` 在列表上构成了一个*幺半群*（Monoid）。

{::comment}
## Length
{:/}

## 长度

{::comment}
Our next function finds the length of a list:
{:/}

在下一个函数里，我们来寻找列表的长度：

\begin{code}
length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)
\end{code}
{::comment}
Again, it takes an implicit parameter `A`.
The length of the empty list is zero.
The length of a non-empty list
is one greater than the length of the tail of the list.
{:/}

同样，它取一个隐式参数 `A`。
空列表的长度为零。非空列表的长度比其尾列表长度多一。

{::comment}
Here is an example showing how to compute the length of a list:
{:/}

我们用下面的例子来展示如何计算列表的长度：
\begin{code}
_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎
\end{code}
{::comment}
Computing the length of a list requires time
linear in the number of elements in the list.
{:/}

计算列表的长度需要关于列表元素个数线性的时间。

{::comment}
In the second-to-last line, we cannot write simply `length []` but
must instead write `length {ℕ} []`.  Since `[]` has no elements, Agda
has insufficient information to infer the implicit parameter.
{:/}

在倒数第二行中，我们不可以直接写 `length []`，而需要写 `length {ℕ} []`。
因为 `[]` 没有元素，Agda 没有足够的信息来推导其隐式参数。

{::comment}
## Reasoning about length
{:/}

## 论证长度

{::comment}
The length of one list appended to another is the
sum of the lengths of the lists:
{:/}

两个附加在一起的列表的长度是两列表长度之和：

\begin{code}
length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎
\end{code}
{::comment}
The proof is by induction on the first argument. The base case
instantiates to `[]`, and follows by straightforward computation.  As
before, Agda cannot infer the implicit type parameter to `length`, and
it must be given explicitly.  The inductive case instantiates to
`x ∷ xs`, and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated
by a recursive invocation of the proof, in this case `length-++ xs ys`,
and it is promoted by the congruence `cong suc`.
{:/}

证明对于第一个参数进行归纳。起始步骤将列表实例化为 `[]`，由直接的运算可证。
如同之前一样，Agda 无法推导 `length` 的隐式参数，所以我们必须显式地给出这个参数。
归纳步骤将列表实例化为 `x ∷ xs`，由直接的运算配合归纳假设可证。
与往常一样，归纳假设由递归使用证明函数来表明，此处为 `length-++ xs ys`，
由 `cong suc` 来提升。

{::comment}
## Reverse
{:/}

## 反转

{::comment}
Using append, it is easy to formulate a function to reverse a list:
{:/}

我们可以使用附加，来简单地构造一个函数来反转一个列表：
\begin{code}
reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]
\end{code}
{::comment}
The reverse of the empty list is the empty list.
The reverse of a non-empty list
is the reverse of its tail appended to a unit list
containing its head.
{:/}

空列表的反转是空列表。
非空列表的反转是其头元素构成的单元列表附加至其尾列表反转之后的结果。

{::comment}
Here is an example showing how to reverse a list:
{:/}

下面的例子展示了如何反转一个列表。
\begin{code}
_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎
\end{code}
{::comment}
Reversing a list in this way takes time _quadratic_ in the length of
the list. This is because reverse ends up appending lists of lengths
`1`, `2`, up to `n - 1`, where `n` is the length of the list being
reversed, append takes time linear in the length of the first
list, and the sum of the numbers up to `n - 1` is `n * (n - 1) / 2`.
(We will validate that last fact in an exercise later in this chapter.)
{:/}

这样子反转一个列表需要列表长度**二次**的时间。这是因为反转一个长度为 `n` 的列表需要
将长度为 `1`、`2` 直到 `n - 1` 的列表附加起来，而附加两个列表需要第一个列表长度线性的时间，
因此加起来就需要 `n * (n - 1) / 2` 的时间。（我们将在本章节后部分验证这一结果）

{::comment}
#### Exercise `reverse-++-commute` (recommended)
{:/}

#### 练习 `reverse-++-commute` （推荐）

{::comment}
Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first:
{:/}

证明一个列表附加到另外一个列表的反转即是反转后的第二个列表附加至反转后的第一个列表：
\begin{code}
postulate
  reverse-++-commute : ∀ {A : Set} {xs ys : List A}
    → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
\end{code}

{::comment}
#### Exercise `reverse-involutive` (recommended)
{:/}

#### 练习 `reverse-involutive` （推荐）

{::comment}
A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution:
{:/}

当一个函数应用两次后与恒等函数作用相同，那么这个函数是一个**对合**（Involution）。
证明反转是一个对合：

\begin{code}
postulate
  reverse-involutive : ∀ {A : Set} {xs : List A}
    → reverse (reverse xs) ≡ xs
\end{code}


{::comment}
## Faster reverse
{:/}

## 更快地反转

{::comment}
The definition above, while easy to reason about, is less efficient than
one might expect since it takes time quadratic in the length of the list.
The idea is that we generalise reverse to take an additional argument:
{:/}

上面的定义虽然论证起来方便，但是它比期望中的实现更低效，因为它的运行时间是关于列表长度的二次函数。
我们可以将反转进行推广，使用一个额外的参数：

\begin{code}
shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)
\end{code}
{::comment}
The definition is by recursion on the first argument. The second argument
actually becomes _larger_, but this is not a problem because the argument
on which we recurse becomes _smaller_.
{:/}

这个定义对于第一个参数进行递归。第二个参数会变_大_，但这样做没有问题，因为我们递归的参数
在变_小_。

{::comment}
Shunt is related to reverse as follows:
{:/}

转移（Shunt）与反转的关系如下：
\begin{code}
shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎
\end{code}
{::comment}
The proof is by induction on the first argument.
The base case instantiates to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs` and follows by the inductive
hypothesis and associativity of append.  When we invoke the inductive hypothesis,
the second argument actually becomes *larger*, but this is not a problem because
the argument on which we induct becomes *smaller*.
{:/}

证明对于第一个参数进行归纳。起始步骤将列表实例化为 `[]`，由直接的运算可证。
归纳步骤将列表实例化为 `x ∷ xs`，由归纳假设和附加的结合律可证。
当我们使用归纳假设时，第二个参数实际上变**大**了，但是这样做没有问题，因为我们归纳的参数变**小**了。

{::comment}
Generalising on an auxiliary argument, which becomes larger as the argument on
which we recurse or induct becomes smaller, is a common trick. It belongs in
your quiver of arrows, ready to slay the right problem.
{:/}

使用一个会在归纳或递归的参数变小时，变大的辅助参数来进行推广，是一个常用的技巧。
这个技巧在以后的证明中很有用。

{::comment}
Having defined shunt be generalisation, it is now easy to respecialise to
give a more efficient definition of reverse:
{:/}

在定义了推广的转移之后，我们可以将其特化，作为一个更高效的反转的定义：

\begin{code}
reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []
\end{code}

{::comment}
Given our previous lemma, it is straightforward to show
the two definitions equivalent:
{:/}

因为我们之前证明的引理，我们可以直接地证明两个定义是等价的：

\begin{code}
reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎
\end{code}

{::comment}
Here is an example showing fast reverse of the list `[ 0 , 1 , 2 ]`:
{:/}

下面的例子展示了如何快速反转列表 `[ 0 , 1 , 2 ]`：

\begin{code}
_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎
\end{code}

{::comment}
Now the time to reverse a list is linear in the length of the list.
{:/}

现在反转一个列表需要的时间与列表的长度线性相关。

{::comment}
## Map {#Map}
{:/}

## 映射 {#Map}

{::comment}
Map applies a function to every element of a list to generate a corresponding list.
Map is an example of a _higher-order function_, one which takes a function as an
argument or returns a function as a result:
{:/}

映射将一个函数应用于列表中的所有元素，生成一个对应的列表。
映射是一个**高阶函数**（Higher-Order Function）的例子，它取一个函数作为参数，返回一个函数作为结果：
\begin{code}
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs
\end{code}
{::comment}
Map of the empty list is the empty list.
Map of a non-empty list yields a list
with head the same as the function applied to the head of the given list,
and tail the same as map of the function applied to the tail of the given list.
{:/}

空列表的映射是空列表。
非空列表的映射生成一个列表，其头元素是原列表的头元素在应用函数之后的结果，
其尾列表是原列表的尾列表映射后的结果。

{::comment}
Here is an example showing how to use map to increment every element of a list:
{:/}

下面的例子展示了如何使用映射来增加列表中的每一个元素：
\begin{code}
_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎
\end{code}
{::comment}
Map requires time linear in the length of the list.
{:/}

映射需要关于列表长度线性的时间。

{::comment}
It is often convenient to exploit currying by applying
map to a function to yield a new function, and at a later
point applying the resulting function:
{:/}

我们常常可以利用柯里化，将映射作用于一个函数，获得另一个函数，然后在之后的时候应用获得的函数：
\begin{code}
sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎
\end{code}

{::comment}
Any type that is parameterised on another type, such as lists, has a
corresponding map, which accepts a function and returns a function
from the type parameterised on the domain of the function to the type
parameterised on the range of the function. Further, a type that is
parameterised on _n_ types will have a map that is parameterised on
_n_ functions.
{:/}

任何对于另外一个类型参数化的类型，例如列表，都有对应的映射，其接受一个函数，并返回另一个
从由给定函数定义域参数化的类型，到由给定函数值域参数化的函数。除此之外，一个对于 _n_ 个类型
参数化的类型会有一个对于 _n_ 个函数参数化的映射。

{::comment}
#### Exercise `map-compose`
{:/}

#### 练习 `map-compose`

{::comment}
Prove that the map of a composition is equal to the composition of two maps:
{:/}

证明函数组合的映射是两个映射的组合：
\begin{code}
postulate
  map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C}
    → map (g ∘ f) ≡ map g ∘ map f
\end{code}
{::comment}
The last step of the proof requires extensionality.
{:/}

证明的最后一步需要外延性。

{::comment}
#### Exercise `map-++-commute`
{:/}

#### 练习 `map-++-commute`

{::comment}
Prove the following relationship between map and append:
{:/}

证明下列关于映射与附加的关系：
\begin{code}
postulate
  map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A}
   →  map f (xs ++ ys) ≡ map f xs ++ map f ys
\end{code}

{::comment}
#### Exercise `map-Tree`
{:/}

#### 练习 `map-Tree`

{::comment}
Define a type of trees with leaves of type `A` and internal
nodes of type `B`:
{:/}

定义一个树数据类型，其叶节点类型为 `A`，内部节点类型为 `B`：
\begin{code}
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
\end{code}
{::comment}
Define a suitable map operator over trees:
{:/}

定义一个对于树的映射运算符：
\begin{code}
postulate
  map-Tree : ∀ {A B C D : Set}
    → (A → C) → (B → D) → Tree A B → Tree C D
\end{code}


{::comment}
## Fold {#Fold}
{:/}

## 折叠 {#Fold}

{::comment}
Fold takes an operator and a value, and uses the operator to combine
each of the elements of the list, taking the given value as the result
for the empty list:
{:/}

折叠取一个运算符和一个值，并使用运算符将列表中的元素合并至一个值，如果给定的列表为空，
则使用给定的值：
\begin{code}
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs
\end{code}
{::comment}
Fold of the empty list is the given value.
Fold of a non-empty list uses the operator to combine
the head of the list and the fold of the tail of the list.
{:/}

空列表的折叠是给定的值。
非空列表的折叠使用给定的运算符，将头元素和尾列表的折叠合并起来。

{::comment}
Here is an example showing how to use fold to find the sum of a list:
{:/}

下面的例子展示了如何使用折叠来对一个列表求和：
\begin{code}
_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎
\end{code}
{::comment}
Fold requires time linear in the length of the list.
{:/}

折叠需要关于列表长度线性的时间。

{::comment}
It is often convenient to exploit currying by applying
fold to an operator and a value to yield a new function,
and at a later point applying the resulting function:
{:/}

我们常常可以利用柯里化，将折叠作用于一个运算符和一个值，获得另一个函数，
然后在之后的时候应用获得的函数：
\begin{code}
sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎
\end{code}

{::comment}
Just as the list type has two constructors, `[]` and `_∷_`,
so the fold function takes two arguments, `e` and `_⊗_`
(in addition to the list argument).
In general, a data type with _n_ constructors will have
a corresponding fold function that takes _n_ arguments.
{:/}

正如列表由两个构造器 `[]` 和 `_∷_`，折叠函数取两个参数 `e` 和 `_⊗_`
（除去列表参数）。推广来说，一个有 _n_ 个构造器的数据类型，会有对应的
取 _n_ 个参数的折叠函数。

{::comment}
#### Exercise `product` (recommended)
{:/}

#### 练习 `product` （推荐）

{::comment}
Use fold to define a function to find the product of a list of numbers.
For example:
{:/}

使用折叠来定义一个计算列表数字之积的函数。例如：

    product [ 1 , 2 , 3 , 4 ] ≡ 24

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
#### Exercise `foldr-++` (recommended)
{:/}

#### 练习 `foldr-++` （推荐）

{::comment}
Show that fold and append are related as follows:
{:/}

证明折叠和附加有如下的关系：
\begin{code}
postulate
  foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
\end{code}


{::comment}
#### Exercise `map-is-foldr`
{:/}

#### 练习 `map-is-foldr`

{::comment}
Show that map can be defined using fold:
{:/}

证明映射可以用折叠定义：
\begin{code}
postulate
  map-is-foldr : ∀ {A B : Set} {f : A → B} →
    map f ≡ foldr (λ x xs → f x ∷ xs) []
\end{code}
{::comment}
This requires extensionality.
{:/}

此证明需要外延性。

{::comment}
#### Exercise `fold-Tree`
{:/}

#### 练习 `fold-Tree`

{::comment}
Define a suitable fold function for the type of trees given earlier:
{:/}

为之前给出的树数据类型定义一个折叠函数：
\begin{code}
postulate
  fold-Tree : ∀ {A B C : Set}
    → (A → C) → (C → B → C → C) → Tree A B → C
\end{code}

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
#### Exercise `map-is-fold-Tree`
{:/}

#### 练习 `map-is-fold-Tree`

{::comment}
Demonstrate an analogue of `map-is-foldr` for the type of trees.
{:/}

对于树数据类型，证明与 `map-is-foldr` 相似的性质。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
#### Exercise `sum-downFrom` (stretch)
{:/}

#### 证明 `sum-downFrom` （延伸）

{::comment}
Define a function that counts down as follows:
{:/}

定义一个向下数数的函数：
\begin{code}
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
\end{code}
{::comment}
For example:
{:/}

例如：
\begin{code}
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl
\end{code}
{::comment}
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`:
{:/}

证明数列之和 `(n - 1) + ⋯ + 0` 等于 `n * (n ∸ 1) / 2`：

\begin{code}
postulate
  sum-downFrom : ∀ (n : ℕ)
    → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
\end{code}


{::comment}
## Monoids
{:/}

## 幺半群

{::comment}
Typically when we use a fold the operator is associative and the
value is a left and right identity for the value, meaning that the
operator and the value form a _monoid_.
{:/}

一般来说，我们会对于折叠函数使用一个满足结合律的运算符，和这个运算符的左右幺元。
这意味着这个运算符和这个值形成了一个**幺半群**（Monoid）。

{::comment}
We can define a monoid as a suitable record type:
{:/}

我们可以用一个合适的记录类型来定义幺半群：
\begin{code}
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid
\end{code}

{::comment}
As examples, sum and zero, multiplication and one, and append and the empty
list, are all examples of monoids:
{:/}

举例来说，加法和零，乘法和一，附加和空列表，都是幺半群：
\begin{code}
+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }
\end{code}

{::comment}
If `_⊗_` and `e` form a monoid, then we can re-express fold on the
same operator and an arbitrary value:
{:/}


如果 `_⊗_` 和 `e` 构成一个幺半群，那么我们可以用相同的运算符和一个任意的值来表示折叠：
\begin{code}
foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎
\end{code}

{::comment}
As a consequence, using a previous exercise, we have the following:
{:/}

使用之前练习中的一个结论，我们可以得到如下：
\begin{code}
foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎
\end{code}

{::comment}
#### Exercise `foldl`
{:/}

#### 练习 `foldl`

{::comment}
Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example:
{:/}

定义一个函数 `foldl`，与 `foldr` 相似，但是运算符向左结合，而不是向右。例如：

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}


{::comment}
#### Exercise `foldr-monoid-foldl`
{:/}

#### 练习 `foldr-monoid-foldl`

{::comment}
Show that if `_⊗_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.
{:/}

证明如果 `_⊗_` 和 `e` 构成幺半群，那么 `foldr _⊗_ e` 和 `foldl _⊗_ e` 的结果
永远是相同的。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}


{::comment}
## All {#All}
{:/}

## 所有 {#All}

{::comment}
We can also define predicates over lists. Two of the most important
are `All` and `Any`.
{:/}

我们也可以定义关于列表的谓词。最重要的两个谓词是 `All` 和 `Any`。

{::comment}
Predicate `All P` holds if predicate `P` is satisfied by every element of a list:
{:/}

谓词 `All P` 当列表里的所有元素满足 `P` 时成立：
\begin{code}
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
\end{code}
{::comment}
The type has two constructors, reusing the names of the same constructors for lists.
The first asserts that `P` holds for every element of the empty list.
The second asserts that if `P` holds of the head of a list and for every
element of the tail of a list, then `P` holds for every element of the list.
Agda uses types to disambiguate whether the constructor is building
a list or evidence that `All P` holds.
{:/}

这个类型有两个构造器，使用了与列表构造器相同的名称。第一个断言了 `P` 对于空列表的任何元素成立。
第二个断言了如果 `P` 对于列表的头元素和尾列表的所有元素成立，那么 `P` 对于这个列表的任何元素成立。
Agda 使用类型来区分构造器是用于构造一个列表，还是构造 `All P` 成立的证明。

{::comment}
For example, `All (_≤ 2)` holds of a list where every element is less
than or equal to two.  Recall that `z≤n` proves `zero ≤ n` for any
`n`, and that if `m≤n` proves `m ≤ n` then `s≤s m≤n` proves `suc m ≤
suc n`, for any `m` and `n`:
{:/}

比如说，`All (_≤ 2)` 对于一个每一个元素都小于等于二的列表成立。
回忆 `z≤n` 证明了对于任意 `n`， `zero ≤ n` 成立；
对于任意 `m` 和 `n`，如果 `m≤n` 证明了 `m ≤ n`，那么 `s≤s m≤n` 证明了 `suc m ≤
suc n`:
\begin{code}
_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []
\end{code}
{::comment}
Here `_∷_` and `[]` are the constructors of `All P` rather than of `List A`.
The three items are proofs of `0 ≤ 2`, `1 ≤ 2`, and `2 ≤ 2`, respectively.
{:/}

这里 `_∷_` 和 `[]` 是 `All P` 的构造器，而不是 `List A` 的。
这三项分别是 `0 ≤ 2`、 `1 ≤ 2` 和 `2 ≤ 2` 的证明。

{::comment}
(One might wonder whether a pattern such as `[_,_,_]` can be used to
construct values of type `All` as well as type `List`, since both use
the same constructors. Indeed it can, so long as both types are in
scope when the pattern is declared.  That's not the case here, since
`List` is defined before `[_,_,_]`, but `All` is defined later.)
{:/}

（读者可能会思考诸如 `[_,_,_]` 的模式是否可以用于构造 `All` 类型的值，
像构造 `List` 类型的一样，因为两者使用了相同的构造器。事实上这样做是可以的，只要两个类型
在模式声明时在作用域内。然而现在不是这样的情况，因为 `List` 先于 `[_,_,_]` 定义，而 `All` 在
之后定义。）

{::comment}
## Any
{:/}

## 任意

{::comment}
Predicate `Any P` holds if predicate `P` is satisfied by some element of a list:
{:/}

谓词 `Any P` 当列表里的一些元素满足 `P` 时成立：
\begin{code}
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
\end{code}
{::comment}
The first constructor provides evidence that the head of the list
satisfies `P`, while the second provides evidence that some element of
the tail of the list satisfies `P`.  For example, we can define list
membership as follows:
{:/}

第一个构造器证明了列表的头元素满足 `P`，第二个构造器证明的列表的尾列表中的一些元素满足 `P`。
举例来说，我们可以如下定义列表的成员关系：
\begin{code}
infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)
\end{code}
{::comment}
For example, zero is an element of the list `[ 0 , 1 , 0 , 2 ]`.  Indeed, we can demonstrate
this fact in two different ways, corresponding to the two different
occurrences of zero in the list, as the first element and as the third element:
{:/}

比如说，零是列表 `[ 0 , 1 , 0 , 2 ]` 中的一个元素。
我们可以用两种方法来展示这个事实，对应零在列表中出现了两次：第一个元素和第三个元素：

\begin{code}
_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))
\end{code}
{::comment}
Further, we can demonstrate that three is not in the list, because
any possible proof that it is in the list leads to contradiction:
{:/}

除此之外，我们可以展示三不在列表之中，因为任何它在列表中的证明会推导出矛盾：
\begin{code}
not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))
\end{code}
{::comment}
The five occurrences of `()` attest to the fact that there is no
possible evidence for `3 ≡ 0`, `3 ≡ 1`, `3 ≡ 0`, `3 ≡ 2`, and
`3 ∈ []`, respectively.
{:/}

`()` 出现了五次，分别表示没有 `3 ≡ 0`、 `3 ≡ 1`、 `3 ≡ 0`、 `3 ≡ 2` 和
`3 ∈ []` 的证明。

{::comment}
## All and append
{:/}

## 所有和附加

{::comment}
A predicate holds for every element of one list appended to another if and
only if it holds for every element of both lists:
{:/}

一个谓词对两个附加在一起的列表的每个元素都成立，当且仅当这个谓词对两个列表的每个元素都成立：
\begin{code}
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩
\end{code}

{::comment}
#### Exercise `Any-++-⇔` (recommended)
{:/}

#### 练习 `Any-++-⇔` （推荐）

{::comment}
Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.
{:/}
使用 `Any` 代替 `All` 与一个合适的 `_×_` 的替代，证明一个类似于 `All-++-⇔` 的结果。
作为结论，展示关联 `_∈_` 和 `_++_` 的一个等价关系。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
#### Exercise `All-++-≃` (stretch)
{:/}

#### 练习 `All-++-≃` （延伸）

{::comment}
Show that the equivalence `All-++-⇔` can be extended to an isomorphism.
{:/}

证明 `All-++-⇔` 的等价关系可以被扩展至一个同构关系。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
#### Exercise `¬Any≃All¬` (stretch)
{:/}

#### 练习 `¬Any≃All¬` （拓展）

{::comment}
First generalise composition to arbitrary levels, using
[universe polymorphism][plfa.Equality#unipoly]:
{:/}

首先我们将函数组合使用[全体多态][plfa.Equality#unipoly]推广到任意等级：
\begin{code}
_∘′_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)
\end{code}

{::comment}
Show that `Any` and `All` satisfy a version of De Morgan's Law:
{:/}

证明 `Any` 和 `All` 满足某个形式的德摩根定律：
\begin{code}
postulate
  ¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
    → (¬_ ∘′ Any P) xs ≃ All (¬_ ∘′ P) xs
\end{code}

{::comment}
Do we also have the following?
{:/}

下列命题是否成立？

\begin{code}
postulate
  ¬All≃Any¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
    → (¬_ ∘′ All P) xs ≃ Any (¬_ ∘′ P) xs
\end{code}
{::comment}
If so, prove; if not, explain why.
{:/}

如果成立，请证明；如果不成立，请解释原因。


{::comment}
## Decidability of All
{:/}

## 所有的可判定性

{::comment}
If we consider a predicate as a function that yields a boolean,
it is easy to define an analogue of `All`, which returns true if
a given predicate returns true for every element of a list:
{:/}

如果我们将一个谓词看作一个返回布尔值的函数，那么我们可以简单的定义一个类似于 `All`
的函数，其当给定谓词对于列表每个元素返回真时返回真：

\begin{code}
all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p
\end{code}
{::comment}
The function can be written in a particularly compact style by
using the higher-order functions `map` and `foldr`.
{:/}

我们可以使用高阶函数 `map` 和 `foldr` 来简洁地写出这个函数。

{::comment}
As one would hope, if we replace booleans by decidables there is again
an analogue of `All`.  First, return to the notion of a predicate `P` as
a function of type `A → Set`, taking a value `x` of type `A` into evidence
`P x` that a property holds for `x`.  Say that a predicate `P` is _decidable_
if we have a function that for a given `x` can decide `P x`:
{:/}

正如所希望的那样，如果我们将布尔值替换成可判定值，这与 `All` 是相似的。首先，回到将 `P`
当作一个类型为 `A → Set` 的函数的概念，将一个类型为 `A` 的值 `x` 转换成 `P x` 对 `x` 成立
的证明。我们成 `P` 为**可判定的**（Decidable），如果我们有一个函数，其在给定 `x` 时能够判定 `P x`：

\begin{code}
Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)
\end{code}
{::comment}
Then if predicate `P` is decidable, it is also decidable whether every
element of a list satisfies the predicate:
{:/}

那么当谓词 `P` 可判定时，我们亦可判定列表中的每一个元素是否满足这个谓词：
\begin{code}
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }
\end{code}
{::comment}
If the list is empty, then trivially `P` holds for every element of
the list.  Otherwise, the structure of the proof is similar to that
showing that the conjunction of two decidable propositions is itself
decidable, using `_∷_` rather than `⟨_,_⟩` to combine the evidence for
the head and tail of the list.
{:/}

如果列表为空，那么 `P` 显然对列表的每个元素成立。
否则，证明的结构与两个可判定的命题是可判定的证明相似，不过我们使用 `_∷_` 而不是 `⟨_,_⟩`
来整合头元素和尾列表的证明。


{::comment}
#### Exercise `any?` (stretch)
{:/}

#### 练习 `any?` （延伸）

{::comment}
Just as `All` has analogues `all` and `All?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `Any?` which determine whether a predicate holds
for some element of a list.  Give their definitions.
{:/}

正如 `All` 有类似的 `all` 和 `All?` 形式，来判断列表的每个元素是否满足给定的谓词，
那么 `Any` 也有类似的 `any` 和 `Any?` 形式，来判断列表的一些元素是否满足给定的谓词。
给出它们的定义。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}


{::comment}
#### Exercise `All-∀`
{:/}

#### 练习 `All-∀`

{::comment}
Show that `All P xs` is isomorphic to `∀ {x} → x ∈ xs → P x`.
{:/}

证明 `All P xs` 与 `∀ {x} → x ∈ xs → P x` 同构。

{::comment}
\begin{code}
-- You code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}


{::comment}
#### Exercise `Any-∃`
{:/}

#### 练习 `Any-∃`

{::comment}
Show that `Any P xs` is isomorphic to `∃[ x ∈ xs ] P x`.
{:/}

证明 `Any P xs` 与 `∃[ x ∈ xs ] P x` 同构。

{::comment}
\begin{code}
-- You code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}


{::comment}
#### Exercise `filter?` (stretch)
{:/}

#### 练习 `filter?` （延伸）

{::comment}
Define the following variant of the traditional `filter` function on lists,
which given a decidable predicate and a list returns all elements of the
list satisfying the predicate:
{:/}

定义下面给出的列表 `filter` 函数的变种，给定一个可判定的谓词和一个列表，返回列表中所有满足
谓词的元素：
\begin{code}
postulate
  filter? : ∀ {A : Set} {P : A → Set}
    → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
\end{code}


{::comment}
## Standard Library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：
\begin{code}
import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
import Data.List.All using (All; []; _∷_)
import Data.List.Any using (Any; here; there)
import Data.List.Membership.Propositional using (_∈_)
import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
  renaming (mapIsFold to map-is-foldr)
import Algebra.Structures using (IsMonoid)
import Relation.Unary using (Decidable)
import Relation.Binary using (Decidable)
\end{code}
{::comment}
The standard library version of `IsMonoid` differs from the
one given here, in that it is also parameterised on an equivalence relation.
{:/}

标准库中的 `IsMonoid` 与给出的定义不同，因为它可以针对特定的等价关系参数化。

{::comment}
Both `Relation.Unary` and `Relation.Binary` define a version of `Decidable`,
one for unary relations (as used in this chapter where `P` ranges over
unary predicates) and one for binary relations (as used earlier, where `_≤_`
ranges over a binary relation).
{:/}

`Relation.Unary` 和 `Relation.Binary` 都定义了 `Decidable` 的某个版本，一个
用于单元关系（正如本章中的单元谓词 `P`），一个用于二元关系（正如之前使用的 `_≤_`）。

## Unicode

{::comment}
This chapter uses the following unicode:
{:/}

本章节使用下列 Unicode：

{::comment}
    ∷  U+2237  PROPORTION  (\::)
    ⊗  U+2297  CIRCLED TIMES  (\otimes, \ox)
    ∈  U+2208  ELEMENT OF  (\in)
    ∉  U+2209  NOT AN ELEMENT OF  (\inn, \notin)

{:/}

    ∷  U+2237  比例  (\::)
    ⊗  U+2297  带圈的乘号  (\otimes, \ox)
    ∈  U+2208  是……的元素  (\in)
    ∉  U+2209  不是……的元素  (\inn, \notin)
