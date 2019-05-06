---
title     : "Connectives: 合取、析取与蕴含"
layout    : page
prev      : /Isomorphism/
permalink : /Connectives/
next      : /Negation/
translators : ["Fangyi Zhou"]
progress  : 50
---

\begin{code}
module plfa.Connectives where
\end{code}

<!-- The ⊥ ⊎ A ≅ A exercise requires a (inj₁ ()) pattern,
     which the reader will not have seen. Restore this
     exercise, and possibly also associativity? Take the
     exercises from the final sections on distributivity
     and exponentials? -->

本章节介绍基础的逻辑运算符。我们使用逻辑运算符与数据类型之间的对应关系，即*命题即类型*原理（Propositions as Types）。
{::comment}
This chapter introduces the basic logical connectives, by observing a
correspondence between connectives of logic and data types, a
principle known as _Propositions as Types_:
{:/}

  * *合取*（Conjunction）即是*积*（Product）
  * *析取*（Disjunction）即是*和*（Sum）
  * *真*（True）即是*单元类型*（Unit Type）
  * *假*（False）即是*空类型*（Empty Type）
  * *蕴含*（Implication）即是*函数空间*（Function Space）

{::comment}
  * _conjunction_ is _product_,
  * _disjunction_ is _sum_,
  * _true_ is _unit type_,
  * _false_ is _empty type_,
  * _implication_ is _function space_.
{:/}


## 导入
{::comment}
## Imports
{:/}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; _≲_; extensionality)
open plfa.Isomorphism.≃-Reasoning
\end{code}


## 合取即是积
{::comment}
## Conjunction is product
{:/}

给定两个命题 `A` 和 `B`，其合取 `A × B` 成立当 `A` 成立和 `B` 成立。
我们将这样的概念形式化，使用如下的归纳类型：
{::comment}
Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{:/}
\begin{code}
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B
\end{code}
`A × B` 成立的证明由 `⟨ M , N ⟩` 的形式表现，其中 `M` 是 `A` 成立的证明，
`N` 是 `B` 成立的证明。
{::comment}
Evidence that `A × B` holds is of the form `⟨ M , N ⟩`, where `M`
provides evidence that `A` holds and `N` provides evidence that `B`
holds.
{:/}

给定 `A × B` 成立的证明，我们可以得出 `A` 成立或者 `B` 成立。
{::comment}
Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds:
{:/}
\begin{code}
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
\end{code}

如果 `L` 是 `A × B` 成立的证据, 那么 `proj₁ L` 是 `A` 成立的证据，
`proj₂ L` 是 `B` 成立的证据。
{::comment}
If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.
{:/}

等价地，我们亦可以将合取定义为一个记录类型：
{::comment}
Equivalently, we could also declare conjunction as a record type:
{:/}
\begin{code}
record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
\end{code}
在这里，记录的构造
{::comment}
Here record construction
{:/}

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

对应
{::comment}
corresponds to the term
{:/}

    ⟨ M , N ⟩

其中 `M` 是 `A` 类型的项，`N` 是 `B` 类型的项。
{::comment}
where `M` is a term of type `A` and `N` is a term of type `B`.
{:/}

当 `⟨_,_⟩` 在等式右手边的项中出现的时候，我们将其称作*构造器*（Constructor），
当它出现在等式左边时，我们将其称作*析构器*（Destructor）。我们亦可将 `proj₁` 和 `proj₂`
称作析构器，因为它们起到相似的效果。
{::comment}
When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a _constructor_, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a _destructor_.
We may also refer to `proj₁` and `proj₂` as destructors, since they
play a similar role.
{:/}

其他的术语将 `⟨_,_⟩` 称作*引入*合取，将 `proj₁` 和 `proj₂` 称作*消去*合取。
前者亦记作 `×-I`，后者 `×-E₁` 和 `×-E₂`。如果我们从上到下来阅读这些规则，引入和消去
正如其名字所说的那样：第一条*引入*一个运算符，所以运算符出现在结论中，而不是假设中；
第二条*消去*一个带有运算符的式子，而运算符出现在假设中，而不是结论中。引入规则描述了
运算符在什么情况下成立——即怎么样*定义*一个运算符。消去规则描述了运算符成立时，可以得出
什么样的结论——即怎么样*使用*一个运算符。
{::comment}
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
holds---how to _use_ the connective.
{:/}

（上面一段内容由此处改编得来：*Propositions as Types*，作者：Philip Wadler，发表于 《ACM 通讯》，2015 年 9 月）
{::comment}
(The paragraph above was adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)
{:/}

在这样的情况下，先使用析构器，再使用构造器将结果重组，得到还是原来的积。
{::comment}
In this case, applying each destructor and reassembling the results with the
constructor is the identity over products:
{:/}
\begin{code}
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl
\end{code}
左手边的模式匹配是必要的。用 `⟨ x , y ⟩` 来替换 `w` 让等式的两边可以化简成相同的项。
{::comment}
The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the
propositional equality to simplify to the same term.
{:/}

我们设置合取的优先级，使它与除了析取之外结合的都不紧密：
{::comment}
We set the precedence of conjunction so that it binds less
tightly than anything save disjunction:
{:/}
\begin{code}
infixr 2 _×_
\end{code}
因此，`m ≤ n × n ≤ p` 解析为 `(m ≤ n) × (n ≤ p)`。
{::comment}
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.
{:/}

给定两个类型 `A` 和 `B`，我们将 `A × B` 称为 `A` 与 `B` 的*积*。
在集合论中它也被称作*笛卡尔积*（Cartesian Product），在计算机科学中它对应*记录*类型。
如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，
那么类型 `A × B` 有 `m * n` 个不同的成员。这也是它被称为积的原因之一。
例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型：

{::comment}
Given two types `A` and `B`, we refer to `A × B` as the
_product_ of `A` and `B`.  In set theory, it is also sometimes
called the _Cartesian product_, and in computing it corresponds
to a _record_ type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members:
{:/}
\begin{code}
data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
\end{code}
那么，`Bool × Tri` 类型有如下的六个成员：
{::comment}
Then the type `Bool × Tri` has six members:
{:/}

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

下面的函数枚举了所有类型为 `Bool × Tri` 的参数：
{::comment}
For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
{:/}
\begin{code}
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6
\end{code}

类型上的积与数的积有相似的性质——它们满足交换律和结合律。
更确切地说，积在*忽略同构*的情况下是交换和结合的。
{::comment}
Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative _up to
isomorphism_.
{:/}

对于交换律，`to` 函数将有序对交换，将 `⟨ x , y ⟩` 变为 `⟨ y , x ⟩`，`from`
函数亦是如此（忽略命名）。
在 `from∘to` 和 `to∘from` 中正确地实例化要匹配的模式是很重要的。
使用 `λ w → refl` 作为 `from∘to` 的定义是不可行的，`to∘from` 同理。
{::comment}
For commutativity, the `to` function swaps a pair, taking `⟨ x , y ⟩` to
`⟨ y , x ⟩`, and the `from` function does the same (up to renaming).
Instantiating the patterns correctly in `from∘to` and `to∘from` is essential.
Replacing the definition of `from∘to` by `λ w → refl` will not work;
and similarly for `to∘from`:
{:/}
\begin{code}
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }
\end{code}

满足*交换律*和*忽略同构*下满足*交换律*是不一样的。比较下列两个命题：
{::comment}
Being _commutative_ is different from being _commutative up to
isomorphism_.  Compare the two statements:
{:/}

    m * n ≡ n * m
    A × B ≃ B × A

在第一个情况下，我们可能有 `m` 是 `2`、`n` 是 `3`，那么 `m * n` 和 `n * m` 都是 `6`。
在第二个情况下，我们可能有 `A` 是 `Bool` 和 `B` 是 `Tri`，但是 `Bool × Tri` 和
`Tri × Bool` *不是*一样的。但是存在一个两者之间的同构。例如：`⟨ true , aa ⟩` 是前者的成员，
其对应后者的成员 `⟨ aa , true ⟩`。
{::comment}
In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
_not_ the same as `Tri × Bool`.  But there is an isomorphism between
the two types.  For instance, `⟨ true , aa ⟩`, which is a member of the
former, corresponds to `⟨ aa , true ⟩`, which is a member of the latter.
{:/}

对于结合律来说，`to` 函数将两个有序对进行重组：将 `⟨ ⟨ x , y ⟩ , z ⟩` 转换为 `⟨ x , ⟨ y , z ⟩ ⟩`，
`from` 函数则为其逆。同样，左逆和右逆的证明需要在一个合适的模式来匹配，从而可以直接化简：
{::comment}
For associativity, the `to` function reassociates two uses of pairing,
taking `⟨ ⟨ x , y ⟩ , z ⟩` to `⟨ x , ⟨ y , z ⟩ ⟩`, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification:
{:/}
\begin{code}
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }
\end{code}

满足*结合律*和*忽略同构*下满足*结合律*是不一样的。比较下列两个命题：
{::comment}
Being _associative_ is not the same as being _associative
up to isomorphism_.  Compare the two statements:
{:/}

    (m * n) * p ≡ m * (n * p)
    (A × B) × C ≃ A × (B × C)

举个例子，`(ℕ × Bool) × Tri` 与 `ℕ × (Bool × Tri)` *不同*，但是两个类型之间
存在同构。例如 `⟨ ⟨ 1 , true ⟩ , aa ⟩`，一个前者的成员，与 `⟨ 1 , ⟨ true , aa ⟩ ⟩`，
一个后者的成员，相对应。
{::comment}
For example, the type `(ℕ × Bool) × Tri` is _not_ the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `⟨ ⟨ 1 , true ⟩ , aa ⟩`, which is a member of the former,
corresponds to `⟨ 1 , ⟨ true , aa ⟩ ⟩`, which is a member of the latter.
{:/}

#### 练习 `⇔≃×` （推荐）
{::comment}
#### Exercise `⇔≃×` (recommended)
{:/}

证明[之前][plfa.Isomorphism#iff]定义的 `A ⇔ B` 与 `(A → B) × (B → A)` 同构。
{::comment}
Show that `A ⇔ B` as defined [earlier][plfa.Isomorphism#iff]
is isomorphic to `(A → B) × (B → A)`.
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}


## 真即是单元类型
{::comment}
## Truth is unit
{:/}

恒真 `⊤` 恒成立。我们将这个概念用合适的归纳类型来形式化：
{::comment}
Truth `⊤` always holds. We formalise this idea by
declaring a suitable inductive type:
{:/}
\begin{code}
data ⊤ : Set where

  tt :
    --
    ⊤
\end{code}
`⊤` 成立的证明由 `tt` 的形式构成。
{::comment}
Evidence that `⊤` holds is of the form `tt`.
{:/}

恒真有引入规则，但没有消去规则。给定一个 `⊤` 成立的证明，我们不能得出任何有趣的结论。
因为恒真恒成立，知道恒真成立不会给我们带来新的知识。
{::comment}
There is an introduction rule, but no elimination rule.
Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.
{:/}

`η-×` 的 零元形式是 `η-⊤`，其断言了任何 `⊤` 类型的值一定等于 `tt`：
{::comment}
The nullary case of `η-×` is `η-⊤`, which asserts that any
value of type `⊤` must be equal to `tt`:
{:/}
\begin{code}
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
\end{code}
左手边的模式匹配是必要的。将 `w` 替换为 `tt` 让等式两边可以化简为相同的值。
{::comment}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `tt` allows both sides of the propositional equality to
simplify to the same term.
{:/}

我们将 `⊤` 称为*单元*类型（Unit Type）。实际上，`⊤` 类型只有一个成员 `tt`。
例如，下面的函数枚举了所有 `⊤` 类型的参数：
{::comment}
We refer to `⊤` as the _unit_ type. And, indeed,
type `⊤` has exactly one member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:
{:/}
\begin{code}
⊤-count : ⊤ → ℕ
⊤-count tt = 1
\end{code}

对于数来说，1 是乘法的幺元。对应地，单元是积的幺元（*忽略同构*）。对于左幺元来说，
`to` 函数将 `⟨ tt , x ⟩` 转换成 `x`， `from` 函数则是其反函数。左逆的证明需要
匹配一个合适的模式来化简：
{::comment}
For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product _up to isomorphism_.  For left
identity, the `to` function takes `⟨ tt , x ⟩` to `x`, and the `from`
function does the inverse.  The evidence of left inverse requires
matching against a suitable pattern to enable simplification:
{:/}
\begin{code}
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }
\end{code}

*幺元*和*忽略同构*的*幺元*是不一样的。比较下列两个命题：
{::comment}
Having an _identity_ is different from having an identity
_up to isomorphism_.  Compare the two statements:
{:/}

    1 * m ≡ m
    ⊤ × A ≃ A

在第一种情况下，我们可能有 `m` 是 `2`，那么 `1 * m` 和 `m` 都为 `2`。
在第二种情况下，我们可能有 `A` 是 `Bool`，但是 `⊤ × Bool` 和 `Bool` 是不同的。
例如：`⟨ tt , true ⟩` 是前者的成员，其对应后者的成员 `true`。
{::comment}
In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is _not_ the
same as `Bool`.  But there is an isomorphism between the two types.
For instance, `⟨ tt , true ⟩`, which is a member of the former,
corresponds to `true`, which is a member of the latter.
{:/}

右幺元可以由积的交换律得来：
{::comment}
Right identity follows from commutativity of product and left identity:
{:/}
\begin{code}
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎
\end{code}
我们在此使用了同构链，与等式链相似。
{::comment}
Here we have used a chain of isomorphisms, analogous to that used for
equality.
{:/}


## Disjunction is sum

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type:
\begin{code}
data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B
\end{code}
Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds:
\begin{code}
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y
\end{code}
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as _constructors_, and when they appear on the
left-hand side we refer to them as _destructors_.  We also refer to
`case-⊎` as a destructor, since it plays a similar role.  Other
terminology refers to `inj₁` and `inj₂` as _introducing_ a
disjunction, and to `case-⊎` as _eliminating_ a disjunction; indeed
the former are sometimes given the names `⊎-I₁` and `⊎-I₂` and the
latter the name `⊎-E`.

Applying the destructor to each of the constructors is the identity:
\begin{code}
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl
\end{code}
More generally, we can also throw in an arbitrary function from a disjunction:
\begin{code}
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl
\end{code}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the propositional equality to
simplify to the same term, and similarly for `inj₂ y`.

We set the precedence of disjunction so that it binds less tightly
than any other declared operator:
\begin{code}
infix 1 _⊎_
\end{code}
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

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

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
\begin{code}
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5
\end{code}

Sum on types also shares a property with sum on numbers in that it is
commutative and associative _up to isomorphism_.

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

\begin{code}
-- Your code goes here
\end{code}

#### Exercise `⊎-assoc`

Show sum is associative up to isomorphism.

\begin{code}
-- Your code goes here
\end{code}

## False is empty

False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type:
\begin{code}
data ⊥ : Set where
  -- no clauses!
\end{code}
There is no possible evidence that `⊥` holds.

Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the Latin phrase _ex falso_, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows:
\begin{code}
⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()
\end{code}
This is our first use of the _absurd pattern_ `()`.
Here since `⊥` is a type with no members, we indicate that it is
_never_ possible to match against a value of this type by using
the pattern `()`.

The nullary case of `case-⊎` is `⊥-elim`.  By analogy,
we might have called it `case-⊥`, but chose to stick with the name
in the standard library.

The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`:
\begin{code}
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
\end{code}
Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.

We refer to `⊥` as the _empty_ type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
\begin{code}
⊥-count : ⊥ → ℕ
⊥-count ()
\end{code}
Here again the absurd pattern `()` indicates that no value can match
type `⊥`.

For numbers, zero is the identity of addition. Correspondingly, empty
is the identity of sums _up to isomorphism_.

#### Exercise `⊥-identityˡ` (recommended)

Show empty is the left identity of sums up to isomorphism.

\begin{code}
-- Your code goes here
\end{code}

#### Exercise `⊥-identityʳ`

Show empty is the right identity of sums up to isomorphism.

\begin{code}
-- Your code goes here
\end{code}

## Implication is function {#implication}

Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.

Evidence that `A → B` holds is of the form

    λ (x : A) → N

where `N` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.

Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds:
\begin{code}
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M
\end{code}
In medieval times, this rule was known by the name _modus ponens_.
It corresponds to function application.

Defining a function, with a named definition or a lambda abstraction,
is referred to as _introducing_ a function,
while applying a function is referred to as _eliminating_ the function.

Elimination followed by introduction is the identity:
\begin{code}
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
\end{code}

Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.

Given two types `A` and `B`, we refer to `A → B` as the _function_
space from `A` to `B`.  It is also sometimes called the _exponential_,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `nᵐ` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. The the type `Bool → Tri` has nine (that is,
three squared) members:

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
\begin{code}
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
\end{code}

Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.

Corresponding to the law

    (p ^ n) ^ m  ≡  p ^ (n * m)

we have the isomorphism

    A → (B → C)  ≃  (A × B) → C

Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality:
\begin{code}
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
\end{code}

Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, our way of writing addition

    _+_ : ℕ → ℕ → ℕ

is isomorphic to a function that accepts a pair of arguments:

    _+′_ : (ℕ × ℕ) → ℕ

Agda is optimised for currying, so `2 + 3` abbreviates `_+_ 2 3`.
In a language optimised for pairing, we would instead take `2 +′ 3` as
an abbreviation for `_+′_ ⟨ 2 , 3 ⟩`.

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have the isomorphism:

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.  The proof of the left inverse requires extensionality:
\begin{code}
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
\end{code}

Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have the isomorphism:

    A → B × C  ≃  (A → B) × (A → C)

That is, the assertion that if `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof of left inverse requires both extensionality
and the rule `η-×` for products:
\begin{code}
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ x → ⟨ g x , h x ⟩ } }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
\end{code}


## Distribution

Products distribute over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results:
\begin{code}
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
\end{code}

Sums do not distribute over products up to isomorphism, but it is an embedding:
\begin{code}
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
\end{code}
Note that there is a choice in how we write the `from` function.
As given, it takes `⟨ inj₂ z , inj₂ z′ ⟩` to `inj₂ z`, but it is
easy to write a variant that instead returns `inj₂ z′`.  We have
an embedding rather than an isomorphism because the
`from` function must discard either `z` or `z′` in this case.

In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:

    A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
    A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)

But when we consider the functions that provide evidence for these
implications, then the first corresponds to an isomorphism while the
second only corresponds to an embedding, revealing a sense in which
one of these laws is "more true" than the other.


#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:
\begin{code}
postulate
  ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
\end{code}
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

\begin{code}
-- Your code goes here
\end{code}


#### Exercise `⊎×-implies-×⊎`

Show that a disjunct of conjuncts implies a conjunct of disjuncts:
\begin{code}
postulate
  ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
\end{code}
Does the converse hold? If so, prove; if not, give a counterexample.

\begin{code}
-- Your code goes here
\end{code}


## Standard library

Definitions similar to those in this chapter can be found in the standard library:
\begin{code}
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)
\end{code}
The standard library constructs pairs with `_,_` whereas we use `⟨_,_⟩`.
The former makes it convenient to build triples or larger tuples from pairs,
permitting `a , b , c` to stand for `(a , (b , c))`.  But it conflicts with
other useful notations, such as `[_,_]` to construct a list of two elements in
Chapter [Lists][plfa.Lists]
and `Γ , A` to extend environments in
Chapter [DeBruijn][plfa.DeBruijn].
The standard library `_⇔_` is similar to ours, but the one in the
standard library is less convenient, since it is parameterised with
respect to an arbitrary notion of equivalence.


## Unicode

This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
