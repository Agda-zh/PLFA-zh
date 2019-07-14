---
title     : "Quantifiers: 全称量词与存在量词"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
translators: ["Fangyi Zhou"]
progress  : 100
---

```
module plfa.Quantifiers where
```

{::comment}
This chapter introduces universal and existential quantification.
{:/}

本章节介绍全称量化（Universal Quantification）和存在量化（Existential Quantification）。

{::comment}
## Imports
{:/}

## 导入

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import plfa.Isomorphism using (_≃_; extensionality)
```


{::comment}
## Universals
{:/}

## 全称量化

{::comment}
We formalise universal quantification using the
dependent function type, which has appeared throughout this book.
{:/}

我们用依赖函数类型（Dependent Function Type）来形式化全称量化。
这样的形式贯穿全书地出现。


{::comment}
Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`∀ (x : A) → B x`.
{:/}

给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，全称量化
的命题 `∀ (x : A) → B x` 当对于所有类型为 `A` 的项 `M`，命题 `B M` 成立时成立。
在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 以后的命题。
变量 `x` 在 `B x` 中以自由变量形式出现，但是在 `∀ (x : A) → B x` 中是约束的。

{::comment}
Evidence that `∀ (x : A) → B x` holds is of the form
{:/}

`∀ (x : A) → B x` 成立的证明由以下形式构成：

    λ (x : A) → N x

{::comment}
where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L
M` provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.
{:/}

其中 `N x` 是一个 `B x` 类型的项，`N x` 和 `B x` 都包含了一个 `A` 类型的自由变量 `x`。
给定一个项 `L`， 其提供 `∀ (x : A) → B x` 成立的证明，和一个类型为 `A` 的项 `M`，
`L M` 这一项则是 `B M` 成立的证明。换句话说，`∀ (x : A) → B x` 成立的证明是一个函数，
将类型为 `A` 的项 `M` 转换成 `B M` 成立的证明。

{::comment}
Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
{:/}

再换句话说，如果我们知道 `∀ (x : A) → B x` 成立，又知道 `M` 是一个类型为 `A` 的项，
那么我们可以推导出 `B M` 成立：
```
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M
```

{::comment}
As with `→-elim`, the rule corresponds to function application.
{:/}

如 `→-elim` 那样，这条规则对应了函数应用。

{::comment}
Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.
{:/}

函数是依赖函数的一种特殊形式，其值域不取决于定义域中的变量。当一个函数被视为
蕴含的证明时，它的参数和结果都是证明，而当一个依赖函数被视为全称量词的证明时，
它的参数被视为数据类型中的一个元素，而结果是一个依赖于参数的命题的证明。因为在
Agda 中，一个数据类型中的一个值和一个命题的证明是无法区别的，这样的区别很大程度上
取决于如何来诠释。

{::comment}
Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.
{:/}

依赖函数类型也被叫做依赖积（Dependent Product），因为如果 `A` 是一个有限的数据类型，
有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，
那么 `∀ (x : A) → B x` 有 `m₁ * ⋯ * mₙ` 个成员。的确，`∀ (x : A) → B x` 的记法有时
也被 `Π[ x ∈ A ] (B x)` 取代，其中 `Π` 代表积。然而，我们还是使用依赖函数这个名称，
因为依赖积这个名称是有歧义的，我们后续会体会到歧义所在。

{::comment}
#### Exercise `∀-distrib-×` (recommended)
{:/}

#### 练习 `∀-distrib-×` （推荐）

{::comment}
Show that universals distribute over conjunction:
{:/}

证明全称量词对于合取满足分配律：

```
postulate
  ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
```

{::comment}
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].
{:/

将这个结果与 [Connectives][plfa.Connectives] 章节中的 (`→-distrib-×`) 结果对比。

{::comment}
#### Exercise `⊎∀-implies-∀⊎`
{:/}

#### 练习 `⊎∀-implies-∀⊎`

{::comment}
Show that a disjunction of universals implies a universal of disjunctions:
{:/}

证明全称命题的析取蕴含了析取的全称命题：

```
postulate
  ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
```

{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。


{::comment}
#### Exercise `∀-×`
{:/}

#### 练习 `∀-×`

{::comment}
Consider the following type.
{:/}

参考下面的类型：

```
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```

{::comment}
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
{:/}

令 `B` 作为由 `Tri` 索引的一个类型，也就是说 `B : Tri → Set`。
证明 `∀ (x : Tri) → B x` 和 `B aa × B bb × B cc` 是同构的。


{::comment}
## Existentials
{:/}

## 存在量化

{::comment}
Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.
{:/}

给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，存在量化
的命题 `Σ[ x ∈ A ] B x` 当对于一些类型为 `A` 的项 `M`，命题 `B M` 成立时成立。
在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 以后的命题。
变量 `x` 在 `B x` 中以自由变量形式出现，但是在 `Σ[ x ∈ A ] B x` 中是约束的。

{::comment}
We formalise existential quantification by declaring a suitable
inductive type:
{:/}

我们定义一个合适的归纳数据类型来形式化存在量化：

```
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
```

{::comment}
We define a convenient syntax for existentials as follows:
{:/}

我们为存在量词定义一个方便的语法：

```
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
```

{::comment}
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.
{:/}

这是我们第一次使用语法声明，其表示左手边的项可以以右手边的语法来书写。
这种特殊语法只有在标识符 `Σ-syntax` 被导入时可用。

{::comment}
Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.
{:/}

`Σ[ x ∈ A ] B x` 成立的证明由 `⟨ M , N ⟩` 组成，其中 `M` 是类型为 `A` 的项，
`N` 是 `B M` 成立的证明。


{::comment}
Equivalently, we could also declare existentials as a record type:
{:/}

我们也可以用记录类型来等价地定义存在量化。

```
record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′
```

{::comment}
Here record construction
{:/}

这里的记录构造

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

{::comment}
corresponds to the term
{:/}

对应了项

    ⟨ M , N ⟩

{::comment}
where `M` is a term of type `A` and `N` is a term of type `B M`.
{:/}

其中 `M` 是类型为 `A` 的项，`N` 是类型为 `B M` 的项。

{::comment}
Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.
{:/}

积是依赖积的一种特殊形式，其第二分量不取决于第一分量中的变量。当一个积被视为
合取的证明时，它的两个分量都是证明，而当一个依赖积被视为存在量词的证明时，
它的第一分量被视为数据类型中的一个元素，而第二分量是一个依赖于第一分量的命题的证明。因为在
Agda 中，一个数据类型中的一个值一个命题的证明是无法区别的，这样的区别很大程度上
取决于如何来诠释。

{::comment}
Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.
{:/}

存在量化也被叫做依赖和（Dependent Sum），因为如果 `A` 是一个有限的数据类型，
有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，
那么 `Σ[ x ∈ A ] B x` 有 `m₁ + ⋯ + mₙ` 个成员，这也解释了选择使用这个记法的原因——
`Σ` 代表和。

{::comment}
Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.
{:/}

存在量化有时也被叫做依赖积（Dependent Product），因为积是其中的一种特殊形式。但是，
这样的叫法非常让人困扰，因为全程量化也被叫做依赖积，而存在量化已经有依赖和的叫法。

{::comment}
A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
{:/}

存在量词的普通记法是 `∃` （与全程量词的 `∀` 记法相类似）。我们使用 Agda 标准库中的惯例，
使用一种隐式申明约束变量定义域的记法。

```
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
```

{::comment}
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.
{:/}

这种特殊的语法只有在 `∃-syntax` 标识符被导入时可用。我们将倾向于使用这种语法，因为它更短，
而且看上去更熟悉。

{::comment}
Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{:/}

给定 `∀ x → B x → C` 成立的证明，其中 `C` 不包括自由变量 `x`，给定 `∃[ x ] B x` 成立的
证明，我们可以推导出 `C` 成立。

```
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y
```

{::comment}
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.
{:/}

换句话说，如果我们知道对于任何 `A` 类型的 `x`，`B x` 蕴含了 `C`，还知道对于某个类型
`A` 的 `x`，`B x` 成立，那么我们可以推导出 `C` 成立。这是因为我们可以先将 `∀ x → B x → C`
的证明对于 `A` 类型的 `x` 和 `B x` 类型的 `y` 实例化，而这样的值恰好可以由 `∃[ x ] B x`
的证明来提供。

{::comment}
Indeed, the converse also holds, and the two together form an isomorphism:
{:/}

的确，逆命题也成立，两者合起来构成一个同构：

```
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```

{::comment}
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication][plfa.Connectives#implication].
{:/}

这可以被看做是将柯里化推广的结果。的确，建立这两者同构的证明与之前我们讨论
[蕴含][plfa.Connectives#implication]时给出的证明是一样的。

{::comment}
#### Exercise `∃-distrib-⊎` (recommended)
{:/}

#### 练习 `∃-distrib-⊎` （推荐）

{::comment}
Show that existentials distribute over disjunction:
{:/}

证明存在量词对于析取满足分配律：

```
postulate
  ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
```

{::comment}
#### Exercise `∃×-implies-×∃`
{:/}

#### 练习 `∃×-implies-×∃`

{::comment}
Show that an existential of conjunctions implies a conjunction of existentials:
{:/}

证明合取的存在命题蕴含了存在命题的合取：

```
postulate
  ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
```

{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `∃-⊎`
{:/}

#### 练习 `∃-⊎`

{::comment}
Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.
{:/}

沿用练习 `∀-×` 中的 `Tri` 和 `B` 。
证明 `∃[ x ] B x` 与 `B aa ⊎ B bb ⊎ B cc` 是同构的。

{::comment}
## An existential example
{:/}

## 一个存在量化的例子

{::comment}
Recall the definitions of `even` and `odd` from
Chapter [Relations][plfa.Relations]:
{:/}

回忆我们在 [Relations][plfa.Relations] 章节中定义的 `even` 和 `odd`：

```
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

{::comment}
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.
{:/}

如果一个数是 0 或者它是奇数的后继，那么这个数是偶数。如果一个数是偶数的后继，那么这个数是奇数。

{::comment}
We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:
{:/}

我们接下来要证明，一个数是偶数当且仅当这个数是一个数的两倍，一个数是奇数当且仅当这个数
是一个数的两倍多一。换句话说，我们要证明的是：

{::comment}
`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`
{:/}

`even n`   当且仅当   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   当且仅当   `∃[ m ] (1 + m * 2 ≡ n)`

{::comment}
By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.
{:/}

惯例来说，我们往往将常数因子写在前面、将和里的常数项写在后面。但是这里我们没有按照惯例，
而是反了过来，因为这样可以让证明更简单：

{::comment}
Here is the proof in the forward direction:
{:/}

这是向前方向的证明：

```
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩
```

{::comment}
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:
{:/}

我们定义两个相互递归的函数。给定 `n` 是奇数或者是偶数的证明，我们返回一个数
`m`，以及 `m * 2 ≡ n` 或者 `1 + m * 2 ≡ n` 的证明。我们根据 `n` 是奇数
或者是偶数的证明进行归纳：

{::comment}
* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.
{:/}

* 如果这个数是偶数，因为它是 0，那么我们返回数据对 0 ，以及 0 的两倍是 0 的证明。

* 如果这个数是偶数，因为它是比一个奇数多 1，那么我们可以使用归纳假设，来获得一个数 `m` 和
`1 + m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `suc m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

* 如果这个数是奇数，因为它是一个偶数的后继，那么我们可以使用归纳假设，来获得一个数 `m` 和
`m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `1 + m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

{::comment}
This completes the proof in the forward direction.
{:/}

这样，我们就完成了正方向的证明。

{::comment}
Here is the proof in the reverse direction:
{:/}

接下来是反方向的证明：

```
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)
```

{::comment}
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:
{:/}

给定一个是另一个数两倍的数，我们需要证明这个数是偶数。给定一个是另一个数两倍多一的数，
我们需要证明这个数是奇数。我们对于存在量化的证明进行归纳。在偶数的情况，我们也需要考虑两种
一个数是另一个数两倍的情况。

{::comment}
- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.
{:/}

- 在偶数是 `zero` 的情况中，我们需要证明 `zero * 2` 是偶数，由 `even-zero` 可得。

- 在偶数是 `suc n` 的情况中，我们需要证明 `suc m * 2` 是偶数。归纳假设告诉我们，
`1 + m * 2` 是奇数，那么所求证的结果由 `even-suc` 可得。

- 在偶数的情况中，我们需要证明 `1 + m * 2` 是奇数。归纳假设告诉我们，`m * 2` 是偶数，
那么所求证的结果由 `odd-suc` 可得。

{::comment}
This completes the proof in the backward direction.
{:/}

这样，我们就完成了向后方向的证明。

{::comment}
#### Exercise `∃-even-odd`
{:/}

#### 练习 `∃-even-odd`

{::comment}
How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.
{:/}

如果我们用 `m * 2` 代替 `2 * m`，`1 + m * 2` 代替 `2 * m + 1`，上述证明会变得复杂多少呢？
用这种方法来重写 `∃-even` 和 `∃-odd`。

{::comment}
```
-- Your code goes here
```
{:/}

```
-- 请将代码写在此处。
```

{::comment}
#### Exercise `∃-+-≤`
{:/}

#### 练习 `∃-+-≤`

{::comment}
Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.
{:/}

证明 `y ≤ z` 当且仅当存在一个 `x` 使得 `x + y ≡ z` 成立时成立。

{::comment}
```
-- Your code goes here
```
{:/}

```
-- 请将代码写在此处。
```

{::comment}
## Existentials, Universals, and Negation
{:/}

## 存在量化、全称量化和否定

{::comment}
Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{:/}

存在量化的否定与否定的全称量化是同构的。考虑到存在量化是析构的推广，全称量化是合构的推广，
这样的结果与析构的否定与否定的合构是同构的结果相似。

```
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }
```

{::comment}
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.
{:/}

在 `to` 的方向，给定了一个 `¬ ∃[ x ] B x` 类型的值 `¬∃xy`，需要证明给定一个 `x` 的值，
可以推导出 `¬ B x`。换句话说，给定一个 `B x` 类型的值 `y`，我们可以推导出假。将 `x` 和 `y`
合并起来我们就得到了 `∃[ x ] B x` 类型的值 `⟨ x , y ⟩`，对其使用 `¬∃xy` 即可获得矛盾。

{::comment}
In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.
{:/}

在 `from` 的方向，给定了一个 `∀ x → ¬ B x` 类型的值 `∀¬xy`，需要证明从一个类型为
`∃[ x ] B x` 类型的值 `⟨ x , y ⟩` ，我们可以推导出假。将 `∀¬xy` 使用于 `x` 之上，
可以得到类型为 `¬ B x` 的值，对其使用 `y` 即可获得矛盾。

{::comment}
The two inverse proofs are straightforward, where one direction
requires extensionality.
{:/}

两个逆的证明很直接，其中有一个方向需要外延性。

{::comment}
#### Exercise `∃¬-implies-¬∀` (recommended)
{:/}

#### 练习 `∃¬-implies-¬∀` （推荐）

{::comment}
Show that existential of a negation implies negation of a universal:
{:/}

证明否定的存在量化蕴含了全称量化的否定：

```
postulate
  ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)
```

{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}
{:/}

#### 练习 `Bin-isomorphism` （延伸） {#Bin-isomorphism}

{::comment}
Recall that Exercises
[Bin][plfa.Naturals#Bin],
[Bin-laws][plfa.Induction#Bin-laws], and
[Bin-predicates][plfa.Relations#Bin-predicates]
define a datatype of bitstrings representing natural numbers:
{:/}

回忆在练习 [Bin][plfa.Naturals#Bin]、
[Bin-laws][plfa.Induction#Bin-laws] 和
[Bin-predicates][plfa.Relations#Bin-predicates] 中，
我们定义了比特串的数据类型来表示自然数：

```
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
```

{::comment}
And ask you to define the following functions and predicates:
{:/}

并要求你来定义下列函数和谓词：

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

{::comment}
And to establish the following properties:
{:/}

以及证明下列性质：

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

{::comment}
Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.
{:/}

使用上述，证明 `ℕ` 与 `∃[ x ](Can x)` 之间存在同构。

{::comment}
```
-- Your code goes here
```
{:/}

```
-- 请将代码写在此处。
```

{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

```
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
```


## Unicode

{::comment}
This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)

{:/}

本章节使用下列 Unicode：

    Π  U+03A0  希腊大写字母 PI (\Pi)
    Σ  U+03A3  希腊大写字母 SIGMA (\Sigma)
    ∃  U+2203  存在 (\ex, \exists)
