---
title     : "Connectives: 合取、析取与蕴涵"
permalink : /Connectives/
translators : ["Fangyi Zhou"]
progress  : 100
---

```agda
module plfa.part1.Connectives where
```

<!-- The ⊥ ⊎ A ≅ A exercise requires a (inj₁ ()) pattern,
     which the reader will not have seen. Restore this
     exercise, and possibly also associativity? Take the
     exercises from the final sections on distributivity
     and exponentials? -->

<!--
This chapter introduces the basic logical connectives, by observing a
correspondence between connectives of logic and data types, a
principle known as _Propositions as Types_:
-->

本章节介绍基础的逻辑运算符。我们使用逻辑运算符与数据类型之间的对应关系，
即**命题即类型（Propositions as Types）**原理。

<!--
  * _conjunction_ is _product_,
  * _disjunction_ is _sum_,
  * _true_ is _unit type_,
  * _false_ is _empty type_,
  * _implication_ is _function space_.
-->

  * **合取（Conjunction）**即是**积（Product）**
  * **析取（Disjunction）**即是**和（Sum）**
  * **真（True）**即是**单元类型（Unit Type）**
  * **假（False）**即是**空类型（Empty Type）**
  * **蕴涵（Implication）**即是**函数空间（Function Space）**

<!--
## Imports
-->

## 导入

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning
```


<!--
## Conjunction is product
-->

## 合取即是积

<!--
Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable datatype:
-->

给定两个命题 `A` 和 `B`，其合取 `A × B` 成立当 `A` 成立和 `B` 成立。
我们用一个合适的数据类型将这样的概念形式化：

```agda
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B
```

<!--
Evidence that `A × B` holds is of the form `⟨ M , N ⟩`, where `M`
provides evidence that `A` holds and `N` provides evidence that `B`
holds.
-->

`A × B` 成立的证明由 `⟨ M , N ⟩` 的形式表现，其中 `M` 是 `A` 成立的证明，
`N` 是 `B` 成立的证明。

<!--
Given evidence that `A × B` holds, we can conclude that both
`A` holds and `B` holds:
-->

给定 `A × B` 成立的证明，我们可以得出 `A` 成立和 `B` 成立。

```agda
proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y
```

<!--
If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.
-->

如果 `L` 是 `A × B` 成立的证据, 那么 `proj₁ L` 是 `A` 成立的证据，
`proj₂ L` 是 `B` 成立的证据。

<!--
When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a _constructor_, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a _destructor_.
We may also refer to `proj₁` and `proj₂` as destructors, since they
play a similar role.
-->

当 `⟨_,_⟩` 在等式右手边的项中出现的时候，我们将其称作**构造子（Constructor）**，
当它出现在等式左边时，我们将其称作**析构器（Destructor）**。我们亦可将 `proj₁` 和 `proj₂`
称作析构器，因为它们起到相似的效果。

<!--
Other terminology refers to `⟨_,_⟩` as _introducing_ a conjunction, and
to `proj₁` and `proj₂` as _eliminating_ a conjunction; indeed, the
former is sometimes given the name `×-I` and the latter two the names
`×-E₁` and `×-E₂`.  As we read the rules from top to bottom,
introduction and elimination do what they say on the tin: the first
_introduces_ a formula for the connective, which appears in the
conclusion but not in the hypotheses; the second _eliminates_ a
formula for the connective, which appears in a hypothesis but not in
the conclusion. An introduction rule describes under what conditions
we say the connective holds---how to _define_ the connective. An
elimination rule describes what we may conclude when the connective
holds---how to _use_ the connective.[^from-wadler-2015]
-->

其他的术语将 `⟨_,_⟩` 称作**引入（Introduce）**合取，将 `proj₁` 和 `proj₂` 称作**消去（Eliminate）**合取。
前者亦记作 `×-I`，后者 `×-E₁` 和 `×-E₂`。如果我们从上到下来阅读这些规则，引入和消去
正如其名字所说的那样：第一条**引入**一个运算符，所以运算符出现在结论中，而不是假设中；
第二条**消去**一个带有运算符的式子，而运算符出现在假设中，而不是结论中。引入规则描述了
运算符在什么情况下成立——即怎么样**定义**一个运算符。消去规则描述了运算符成立时，可以得出
什么样的结论——即怎么样**使用**一个运算符。[^from-wadler-2015]

<!--
In this case, applying each destructor and reassembling the results with the
constructor is the identity over products:
-->

在这样的情况下，先使用析构器，再使用构造子将结果重组，得到还是原来的积。

```agda
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl
```

<!--
The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the
propositional equality to simplify to the same term.
-->

左手边的模式匹配是必要的。用 `⟨ x , y ⟩` 来替换 `w` 让等式的两边可以化简成相同的项。

<!--
We set the precedence of conjunction so that it binds less
tightly than anything save disjunction:
-->

我们设置合取的优先级，使它与除了析取之外结合的都不紧密：

```agda
infixr 2 _×_
```

<!--
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.
-->

因此，`m ≤ n × n ≤ p` 解析为 `(m ≤ n) × (n ≤ p)`。

Alternatively, we can declare conjunction as a record type:

```agda
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
```

The record construction `record { proj₁′ = M ; proj₂′ = N }` corresponds to the
term `⟨ M , N ⟩` where `M` is a term of type `A` and `N` is a term of type `B`.
The constructor declaration allows us to write `⟨ M , N ⟩′` in place of the
record construction.

The data type `_x_` and the record type `_×′_` behave similarly. One
difference is that for data types we have to prove η-equality, but for record
types, η-equality holds *by definition*. While proving `η-×′`, we do not have to
pattern match on `w` to know that η-equality holds:

```agda
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl
```

It can be very convenient to have η-equality *definitionally*, and so the
standard library defines `_×_` as a record type. We use the definition from the
standard library in later chapters.

<!--
Given two types `A` and `B`, we refer to `A × B` as the
_product_ of `A` and `B`.  In set theory, it is also sometimes
called the _Cartesian product_, and in computing it corresponds
to a _record_ type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members:
-->

给定两个类型 `A` 和 `B`，我们将 `A × B` 称为 `A` 与 `B` 的**积**。
在集合论中它也被称作**笛卡尔积（Cartesian Product）**，在计算机科学中它对应**记录**类型。
如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，
那么类型 `A × B` 有 `m * n` 个不同的成员。这也是它被称为积的原因之一。
例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型：

```agda
data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```

<!--
Then the type `Bool × Tri` has six members:
-->

那么，`Bool × Tri` 类型有如下的六个成员：

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

<!--
For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
-->

下面的函数枚举了所有类型为 `Bool × Tri` 的参数：

```agda
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6
```

<!--
Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative _up to
isomorphism_.
-->

类型上的积与数的积有相似的性质——它们满足交换律和结合律。
更确切地说，积在**在同构意义下**满足交换律和结合率。

<!--
For commutativity, the `to` function swaps a pair, taking `⟨ x , y ⟩` to
`⟨ y , x ⟩`, and the `from` function does the same (up to renaming).
Instantiating the patterns correctly in `from∘to` and `to∘from` is essential.
Replacing the definition of `from∘to` by `λ w → refl` will not work;
and similarly for `to∘from`:
-->

对于交换律，`to` 函数将有序对交换，将 `⟨ x , y ⟩` 变为 `⟨ y , x ⟩`，`from`
函数亦是如此（忽略命名）。
在 `from∘to` 和 `to∘from` 中正确地实例化要匹配的模式是很重要的。
使用 `λ w → refl` 作为 `from∘to` 的定义是不可行的，`to∘from` 同理。

```agda
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }
```

<!--
Being _commutative_ is different from being _commutative up to
isomorphism_.  Compare the two statements:
-->

满足**交换律**和**在同构意义下满足交换律**是不一样的。比较下列两个命题：

    m * n ≡ n * m
    A × B ≃ B × A

<!--
In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
_not_ the same as `Tri × Bool`.  But there is an isomorphism between
the two types.  For instance, `⟨ true , aa ⟩`, which is a member of the
former, corresponds to `⟨ aa , true ⟩`, which is a member of the latter.
-->

在第一个情况下，我们可能有 `m` 是 `2`、`n` 是 `3`，那么 `m * n` 和 `n * m` 都是 `6`。
在第二个情况下，我们可能有 `A` 是 `Bool` 和 `B` 是 `Tri`，但是 `Bool × Tri` 和
`Tri × Bool` **不是**一样的。但是存在一个两者之间的同构。例如：`⟨ true , aa ⟩` 是前者的成员，
其对应后者的成员 `⟨ aa , true ⟩`。

<!--
For associativity, the `to` function reassociates two uses of pairing,
taking `⟨ ⟨ x , y ⟩ , z ⟩` to `⟨ x , ⟨ y , z ⟩ ⟩`, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification:
-->

对于结合律来说，`to` 函数将两个有序对进行重组：将 `⟨ ⟨ x , y ⟩ , z ⟩` 转换为 `⟨ x , ⟨ y , z ⟩ ⟩`，
`from` 函数则为其逆。同样，左逆和右逆的证明需要在一个合适的模式来匹配，从而可以直接化简：

```agda
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }
```

<!--
Being _associative_ is not the same as being _associative
up to isomorphism_.  Compare the two statements:
-->

满足**结合律**和**在同构意义下满足结合律**是不一样的。比较下列两个命题：

    (m * n) * p ≡ m * (n * p)
    (A × B) × C ≃ A × (B × C)

<!--
For example, the type `(ℕ × Bool) × Tri` is _not_ the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `⟨ ⟨ 1 , true ⟩ , aa ⟩`, which is a member of the former,
corresponds to `⟨ 1 , ⟨ true , aa ⟩ ⟩`, which is a member of the latter.
-->

举个例子，`(ℕ × Bool) × Tri` 与 `ℕ × (Bool × Tri)` **不同**，但是两个类型之间
存在同构。例如 `⟨ ⟨ 1 , true ⟩ , aa ⟩`，一个前者的成员，与 `⟨ 1 , ⟨ true , aa ⟩ ⟩`，
一个后者的成员，相对应。

<!--
#### Exercise `⇔≃×` (recommended)
-->

#### 练习 `⇔≃×` （推荐）

<!--
Show that `A ⇔ B` as defined [earlier](/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.
-->

证明[之前](/Isomorphism/#iff)定义的 `A ⇔ B` 与 `(A → B) × (B → A)` 同构。

<!--
```agda
-- Your code goes here
```
-->

```agda
-- 请将代码写在此处。
```

<!--
## Truth is unit
-->

## 真即是单元类型

<!--
Truth `⊤` always holds. We formalise this idea by
declaring a suitable datatype:
-->

恒真 `⊤` 恒成立。我们将这个概念用合适的数据类型来形式化：

```agda
data ⊤ : Set where

  tt :
    --
    ⊤
```

<!--
Evidence that `⊤` holds is of the form `tt`.
-->

`⊤` 成立的证明由 `tt` 的形式构成。

<!--
There is an introduction rule, but no elimination rule.
Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.
-->

恒真有引入规则，但没有消去规则。给定一个 `⊤` 成立的证明，我们不能得出任何有趣的结论。
因为恒真恒成立，知道恒真成立不会给我们带来新的知识。

<!--
The nullary case of `η-×` is `η-⊤`, which asserts that any
value of type `⊤` must be equal to `tt`:
-->

`η-×` 的 零元形式是 `η-⊤`，其断言了任何 `⊤` 类型的值一定等于 `tt`：

```agda
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
```

<!--
The pattern matching on the left-hand side is essential. Replacing
`w` by `tt` allows both sides of the propositional equality to
simplify to the same term.
-->

左手边的模式匹配是必要的。将 `w` 替换为 `tt` 让等式两边可以化简为相同的值。

Alternatively, we can declare truth as an empty record:
```agda
record ⊤′ : Set where
  constructor tt′
```
The record construction `record {}` corresponds to the term `tt`. The
constructor declaration allows us to write `tt′`.

As with the product, the data type `⊤` and the record type `⊤′` behave
similarly, but η-equality holds *by definition* for the record type. While
proving `η-⊤′`, we do not have to pattern match on `w`---Agda *knows* it is
equal to `tt′`:
```agda
η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl
```
Agda knows that *any* value of type `⊤′` must be `tt′`, so any time we need a
value of type `⊤′`, we can tell Agda to figure it out:
```agda
truth′ : ⊤′
truth′ = _
```

<!--
We refer to `⊤` as the _unit_ type. And, indeed,
type `⊤` has exactly one member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:
-->

我们将 `⊤` 称为**单元（Unit Type）**类型。实际上，`⊤` 类型只有一个成员 `tt`。
例如，下面的函数枚举了所有 `⊤` 类型的参数：

```agda
⊤-count : ⊤ → ℕ
⊤-count tt = 1
```

<!--
For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product _up to isomorphism_.  For left
identity, the `to` function takes `⟨ tt , x ⟩` to `x`, and the `from`
function does the inverse.  The evidence of left inverse requires
matching against a suitable pattern to enable simplification:
-->

对于数来说，1 是乘法的幺元。对应地，单元是积的幺元（**在同构意义下**）。对于左幺元来说，
`to` 函数将 `⟨ tt , x ⟩` 转换成 `x`， `from` 函数则是其反函数。左逆的证明需要
匹配一个合适的模式来化简：

```agda
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }
```

<!--
Having an _identity_ is different from having an identity
_up to isomorphism_.  Compare the two statements:
-->

**幺元**和**在同构意义下的幺元**是不一样的。比较下列两个命题：

    1 * m ≡ m
    ⊤ × A ≃ A

<!--
In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is _not_ the
same as `Bool`.  But there is an isomorphism between the two types.
For instance, `⟨ tt , true ⟩`, which is a member of the former,
corresponds to `true`, which is a member of the latter.
-->

在第一种情况下，我们可能有 `m` 是 `2`，那么 `1 * m` 和 `m` 都为 `2`。
在第二种情况下，我们可能有 `A` 是 `Bool`，但是 `⊤ × Bool` 和 `Bool` 是不同的。
例如：`⟨ tt , true ⟩` 是前者的成员，其对应后者的成员 `true`。

<!--
Right identity follows from commutativity of product and left identity:
-->

右幺元可以由积的交换律得来：

```agda
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎
```

<!--
Here we have used a chain of isomorphisms, analogous to that used for
equality.
-->

我们在此使用了同构链，与等式链相似。

<!--
## Disjunction is sum
-->

## 析取即是和

<!--
Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type:
-->

给定两个命题 `A` 和 `B`，析取 `A ⊎ B` 在 `A` 成立或者 `B` 成立时成立。
我们将这个概念用合适的归纳类型来形式化：

```agda
data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B
```

<!--
Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.
-->

`A ⊎ B` 成立的证明有两个形式： `inj₁ M`，其中 `M` 是 `A` 成立的证明，或者
`inj₂ N`，其中 `N` 是 `B` 成立的证明。

<!--
Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds:
-->

给定 `A → C` 和 `B → C` 成立的证明，那么给定一个 `A ⊎ B` 的证明，我们可以得出 `C` 成立：

```agda
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y
```

<!--
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.
-->

对 `inj₁` 和 `inj₂` 进行模式匹配，是我们使用析取成立的证明的常见方法。

<!--
When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as _constructors_, and when they appear on the
left-hand side we refer to them as _destructors_.  We also refer to
`case-⊎` as a destructor, since it plays a similar role.  Other
terminology refers to `inj₁` and `inj₂` as _introducing_ a
disjunction, and to `case-⊎` as _eliminating_ a disjunction; indeed
the former are sometimes given the names `⊎-I₁` and `⊎-I₂` and the
latter the name `⊎-E`.
-->

当 `inj₁` 和 `inj₂` 在等式右手边出现的时候，我们将其称作**构造子**，
当它出现在等式左边时，我们将其称作**析构器**。我们亦可将 `case-⊎`
称作析构器，因为它们起到相似的效果。其他术语将 `inj₁` 和 `inj₂` 称为**引入**析取，
将 `case-⊎` 称为**消去**析取。前者亦被称为 `⊎-I₁` 和 `⊎-I₂`，后者 `⊎-E`。

<!--
Applying the destructor to each of the constructors is the identity:
-->

对每个构造子使用析构器得到的是原来的值：

```agda
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl
```

<!--
More generally, we can also throw in an arbitrary function from a disjunction:
-->

更普遍地来说，我们亦可对于析取使用一个任意的函数：

```agda
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl
```

<!--
The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the propositional equality to
simplify to the same term, and similarly for `inj₂ y`.
-->

左手边的模式匹配是必要的。用 `inj₁ x` 来替换 `w` 让等式的两边可以化简成相同的项，
`inj₂ y` 同理。

<!--
We set the precedence of disjunction so that it binds less tightly
than any other declared operator:
-->

我们设置析取的优先级，使它与任何已经定义的运算符都结合的不紧密：

```agda
infixr 1 _⊎_
```

<!--
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.
-->

因此 `A × C ⊎ B × C` 解析为 `(A × C) ⊎ (B × C)`。

<!--
Given two types `A` and `B`, we refer to `A ⊎ B` as the
_sum_ of `A` and `B`.  In set theory, it is also sometimes
called the _disjoint union_, and in computing it corresponds
to a _variant record_ type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:
-->

给定两个类型 `A` 和 `B`，我们将 `A ⊎ B` 称为 `A` 与 `B` 的**和**。
在集合论中它也被称作**不交并（Disjoint Union）**，在计算机科学中它对应**变体记录**类型。
如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，
那么类型 `A ⊎ B` 有 `m + n` 个不同的成员。这也是它被称为和的原因之一。
例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型，如之前的定义。
那么，`Bool ⊎ Tri` 类型有如下的五个成员：

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

<!--
For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
-->

下面的函数枚举了所有类型为 `Bool ⊎ Tri` 的参数：

```agda
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5
```

<!--
Sum on types also shares a property with sum on numbers in that it is
commutative and associative _up to isomorphism_.
-->

类型上的和与数的和有相似的性质——它们满足交换律和结合律。
更确切地说，和在**在同构意义下**是交换和结合的。

<!--
#### Exercise `⊎-comm` (recommended)
-->

#### 练习 `⊎-comm` （推荐）

<!--
Show sum is commutative up to isomorphism.
-->

证明和类型在同构意义下满足交换律。

<!--
```agda
-- Your code goes here
```
-->

```agda
-- 请将代码写在此处。
```

<!--
#### Exercise `⊎-assoc` (practice)
-->

#### 练习 `⊎-assoc`（实践）

<!--
Show sum is associative up to isomorphism.
-->

证明和类型在同构意义下满足结合律。

<!--
```agda
-- Your code goes here
```
-->

```agda
-- 请将代码写在此处。
```

<!--
## False is empty
-->

## 假即是空类型

<!--
False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type:
-->

恒假 `⊥` 从不成立。我们将这个概念用合适的归纳类型来形式化：

<!--
FIXME: the code block is removed to make Agda not recognise this as code.
data ⊥ : Set where
  -- no clauses!
-->

```agda
data ⊥ : Set where
  -- 没有语句！
```

<!--
There is no possible evidence that `⊥` holds.
-->

没有 `⊥` 成立的证明。

<!--
Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the Latin phrase _ex falso_, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows:
-->

与 `⊤` 相对偶，`⊥` 没有引入规则，但是有消去规则。因为恒假从不成立，
如果它一旦成立，我们就进入了矛盾之中。给定 `⊥` 成立的证明，我们可以得出任何结论！
这是逻辑学的基本原理，又由中世纪的拉丁文词组 _ex falso_ 为名。小孩子也由诸如
「如果猪有翅膀，那我就是示巴女王」的词组中知晓。我们如下将它形式化：

```agda
⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()
```

<!--
This is our first use of the _absurd pattern_ `()`.
Here since `⊥` is a type with no members, we indicate that it is
_never_ possible to match against a value of this type by using
the pattern `()`.
-->

这是我们第一次使**用荒谬模式（Absurd Pattern）** `()`。在这里，因为 `⊥`
是一个没有成员的类型，我们用 `()` 模式来指明这里不可能匹配任何这个类型的值。

<!--
The nullary case of `case-⊎` is `⊥-elim`.  By analogy,
we might have called it `case-⊥`, but chose to stick with the name
in the standard library.
-->

`case-⊎` 的零元形式是 `⊥-elim`。类比的来说，它应该叫做 `case-⊥`，
但是我们在此使用标准库中使用的名字。

<!--
The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`:
-->

`uniq-⊎` 的零元形式是 `uniq-⊥`，其断言了 `⊥-elim` 和任何取 `⊥` 的函数是等价的。

```agda
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
```

<!--
Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.
-->

使用荒谬模式断言了 `w` 没有任何可能的值，因此等式显然成立。

<!--
We refer to `⊥` as the _empty_ type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
-->

我们将 `⊥` 成为**空（Empty）**类型。实际上，`⊥` 类型没有成员。
例如，下面的函数枚举了所有 `⊥` 类型的参数：

```agda
⊥-count : ⊥ → ℕ
⊥-count ()
```

<!--
Here again the absurd pattern `()` indicates that no value can match
type `⊥`.
-->

同样，荒谬模式告诉我们没有值可以来匹配类型 `⊥`。

<!--
For numbers, zero is the identity of addition. Correspondingly, empty
is the identity of sums _up to isomorphism_.
-->

对于数来说，0 是加法的幺元。对应地，空是和的幺元（**在同构意义下**）。

<!--
#### Exercise `⊥-identityˡ` (recommended)
-->

#### 练习 `⊥-identityˡ` （推荐）

<!--
Show empty is the left identity of sums up to isomorphism.
-->

证明空在同构意义下是和的左幺元。

<!--
```agda
-- Your code goes here
```
-->

```agda
-- 请将代码写在此处。
```

#### Exercise `⊥-identityʳ` (practice)

#### 练习 `⊥-identityʳ`（实践）

<!--
Show empty is the right identity of sums up to isomorphism.
-->

证明空在同构意义下是和的右幺元。

<!--
```agda
-- Your code goes here
```
-->

```agda
-- 请将代码写在此处。
```

<!--
## Implication is function {#implication}
-->

## 蕴涵即是函数 {#implication}

<!--
Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.
-->

给定两个命题 `A` 和 `B`，其蕴涵 `A → B` 在任何 `A` 成立的时候，`B` 也成立时成立。
我们用函数类型来形式化蕴涵，如本书中通篇出现的那样。


<!--
Evidence that `A → B` holds is of the form
-->

`A → B` 成立的证据由下面的形式组成：

    λ (x : A) → N

<!--
where `N` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.
-->

其中 `N` 是一个类型为 `B` 的项，其包括了一个类型为 `A` 的自由变量 `x`。
给定一个 `A → B` 成立的证明 `L`，和一个 `A` 成立的证明 `M`，那么 `L M` 是 `B` 成立的证明。
也就是说，`A → B` 成立的证明是一个函数，将 `A` 成立的证明转换成 `B` 成立的证明。

<!--
Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds:
-->

换句话说，如果知道 `A → B` 和 `A` 同时成立，那么我们可以推出 `B` 成立：

```agda
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M
```

<!--
In medieval times, this rule was known by the name _modus ponens_.
It corresponds to function application.
-->

在中世纪，这条规则被叫做 _modus ponens_，它与函数应用相对应。

<!--
Defining a function, with a named definition or a lambda abstraction,
is referred to as _introducing_ a function,
while applying a function is referred to as _eliminating_ the function.
-->

定义一个函数，不管是带名字的定义或是使用 Lambda 抽象，被称为**引入**一个函数，
使用一个函数被称为**消去**一个函数。

<!--
Elimination followed by introduction is the identity:
-->

引入后接着消去，得到的还是原来的值：

```agda
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
```

<!--
Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.
-->

蕴涵比其他的运算符结合得都不紧密。因此 `A ⊎ B → B ⊎ A` 被解析为 `(A ⊎ B) → (B ⊎ A)`。

<!--
Given two types `A` and `B`, we refer to `A → B` as the _function_
space from `A` to `B`.  It is also sometimes called the _exponential_,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `nᵐ` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. Then the type `Bool → Tri` has nine (that is,
three squared) members:
-->

给定两个类型 `A` 和 `B`，我们将 `A → B` 称为从 `A` 到 `B` 的**函数**空间。
它有时也被称作以 `B` 为底，`A` 为次数的**幂**。如果类型 `A` 有 `m` 个不同的成员，
类型 `B` 有 `n` 个不同的成员，那么类型 `A → B` 有 `nᵐ` 个不同的成员。
这也是它被称为幂的原因之一。例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型，
如之前的定义。那么，`Bool → Tri` 类型有如下的九个成员（三的平方）：

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

<!--
For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
-->

下面的函数枚举了所有类型为 `Bool → Tri` 的参数：

```agda
→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9
```

<!--
Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.
-->

类型上的幂与数的幂有相似的性质，很多数上成立的关系式也可以在类型上成立。

<!--
Corresponding to the law
-->

对应如下的定律：

    (p ^ n) ^ m  ≡  p ^ (n * m)

<!--
we have the isomorphism
-->

我们有如下的同构：

    A → (B → C)  ≃  (A × B) → C

<!--
Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality:
-->

两个类型可以被看作给定 `A` 成立的证据和 `B` 成立的证据，返回 `C` 成立的证据。
这个同构有时也被称作**柯里化（Currying）**。右逆的证明需要外延性：

```agda
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```

<!--
Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, our way of writing addition
-->

柯里化告诉我们，如果一个函数有取一个数据对作为参数，
那么我们可以构造一个函数，取第一个参数，返回一个取第二个参数，返回最终结果的函数。
因此，举例来说，下面表示加法的形式：

    _+_ : ℕ → ℕ → ℕ

<!--
is isomorphic to a function that accepts a pair of arguments:
-->

和下面的一个带有一个数据对作为参数的函数是同构的：

    _+′_ : (ℕ × ℕ) → ℕ

<!--
Agda is optimised for currying, so `2 + 3` abbreviates `_+_ 2 3`.
In a language optimised for pairing, we would instead take `2 +′ 3` as
an abbreviation for `_+′_ ⟨ 2 , 3 ⟩`.
-->

Agda 对柯里化进行了优化，因此 `2 + 3` 是 `_+_ 2 3` 的简写。在一个对有序对进行优化的语言里，
`2 +′ 3` 可能是 `_+′_ ⟨ 2 , 3 ⟩` 的简写。

<!--
Corresponding to the law
-->

对应如下的定律：

    p ^ (n + m) = (p ^ n) * (p ^ m)

<!--
we have the isomorphism:
-->

我们有如下的同构：

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

<!--
That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.  The proof of the left inverse requires extensionality:
-->

命题如果 `A` 成立或者 `B` 成立，那么 `C` 成立，和命题如果 `A` 成立，那么 `C` 成立以及
如果 `B` 成立，那么 `C` 成立，是一样的。左逆的证明需要外延性：

```agda
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
```

<!--
Corresponding to the law
-->

对应如下的定律：

    (p * n) ^ m = (p ^ m) * (n ^ m)

<!--
we have the isomorphism:
-->

我们有如下的同构：

    A → B × C  ≃  (A → B) × (A → C)

<!--
That is, the assertion that if `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof of left inverse requires both extensionality
and the rule `η-×` for products:
-->

命题如果 `A` 成立，那么 `B` 成立和 `C` 成立，和命题如果 `A` 成立，那么 `B` 成立以及
如果 `A` 成立，那么 `C` 成立，是一样的。左逆的证明需要外延性和积的 `η-×` 规则：

```agda
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
```


<!--
## Distribution
-->

## 分配律

<!--
Products distribute over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results:
-->

在同构意义下，积对于和满足分配律。验证这条形式的代码和之前的证明相似：

```agda
×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }
```

<!--
Sums do not distribute over products up to isomorphism, but it is an embedding:
-->

和对于积不满足分配律，但满足嵌入：

```agda
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }
```

<!--
Note that there is a choice in how we write the `from` function.
As given, it takes `⟨ inj₂ z , inj₂ z′ ⟩` to `inj₂ z`, but it is
easy to write a variant that instead returns `inj₂ z′`.  We have
an embedding rather than an isomorphism because the
`from` function must discard either `z` or `z′` in this case.
-->

我们在定义 `from` 函数的时候可以有选择。给定的定义中，它将 `⟨ inj₂ z , inj₂ z′ ⟩`
转换为 `inj₂ z`，但我们也可以返回 `inj₂ z′` 作为嵌入证明的变种。我们在这里只能证明嵌入，
而不能证明同构，因为 `from` 函数必须丢弃 `z` 或者 `z′` 其中的一个。

<!--
In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:
-->

在一般的逻辑学方法中，两条分配律都以等价的形式给出，每一边都蕴涵了另一边：

    A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
    A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)

<!--
But when we consider the functions that provide evidence for these
implications, then the first corresponds to an isomorphism while the
second only corresponds to an embedding, revealing a sense in which
one of these laws is "more true" than the other.
-->

但当我们考虑提供上述蕴涵证明的函数时，第一条对应同构而第二条只能对应嵌入，
揭示了有些定理比另一个更加的「正确」。


<!--
#### Exercise `⊎-weak-×` (recommended)
-->

#### 练习 `⊎-weak-×` （推荐）

<!--
Show that the following property holds:
-->

证明如下性质成立：

```agda
postulate
  ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
```

<!--
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.
-->

这被称为**弱分配律（Weak Distributive Law）**。给出相对应的分配律，并解释分配律与弱分配律的关系。

<!--
```agda
-- Your code goes here
```
-->

```agda
-- 请将代码写在此处。
```


<!--
#### Exercise `⊎×-implies-×⊎` (practice)
-->

#### 练习 `⊎×-implies-×⊎`（实践）

<!--
Show that a disjunct of conjuncts implies a conjunct of disjuncts:
-->

证明合取的析取蕴涵了析取的合取：

```agda
postulate
  ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
```

<!--
Does the converse hold? If so, prove; if not, give a counterexample.
-->

反命题成立吗？如果成立，给出证明；如果不成立，给出反例。

<!--
```agda
-- Your code goes here
```
-->

```agda
-- 请将代码写在此处。
```

<!--
## Standard library
-->

## 标准库

<!--
Definitions similar to those in this chapter can be found in the standard library:
-->

标准库中可以找到与本章节中相似的定义：

```agda
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)
```

<!--
The standard library constructs pairs with `_,_` whereas we use `⟨_,_⟩`.
The former makes it convenient to build triples or larger tuples from pairs,
permitting `a , b , c` to stand for `(a , (b , c))`.  But it conflicts with
other useful notations, such as `[_,_]` to construct a list of two elements in
Chapter [Lists](/Lists/)
and `Γ , A` to extend environments in
Chapter [DeBruijn](/DeBruijn/).
The standard library `_⇔_` is similar to ours, but the one in the
standard library is less convenient, since it is parameterised with
respect to an arbitrary notion of equivalence.
-->

标准库中使用 `_,_` 构造数据对，而我们使用 `⟨_,_⟩`。前者在从数据对构造三元对或者更大的
元组时更加的方便，允许 `a , b , c` 作为 `(a, (b , c))` 的记法。但它与其他有用的记法相冲突，
比如说 [Lists](/Lists/) 中的 `[_,_]` 记法表示两个元素的列表，
或者 [DeBruijn](/DeBruijn/) 章节中的 `Γ , A` 来表示环境的扩展。
标准库中的 `_⇔_` 和我们的相似，但使用起来比较不便，
因为它可以根据任意的相等性定义进行参数化。

## Unicode

<!--
This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
-->

本章节使用下列 Unicode：

    ×  U+00D7  乘法符号 (\x)
    ⊎  U+228E  多重集并集 (\u+)
    ⊤  U+22A4  向下图钉 (\top)
    ⊥  U+22A5  向上图钉 (\bot)
    η  U+03B7  希腊小写字母 ETA (\eta)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
    ⇔  U+21D4  左右双箭头 (\<=>)

<!--
[^from-wadler-2015]: This paragraph was adopted from "Propositions as Types", Philip Wadler, _Communications of the ACM_, December 2015.
-->

[^from-wadler-2015]: 此段内容由 Propositions as Types（命题即类型）改编而来，
作者：Philip Wadler，发表于 《ACM 通讯》，2015 年 9 月
