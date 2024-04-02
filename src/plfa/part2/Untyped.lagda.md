---
title      : "Untyped: 完全正规化的无类型 λ-演算"
permalink  : /Untyped/
translators: ["Fangyi Zhou"]
---

```agda
module plfa.part2.Untyped where
```

<!--
In this chapter we play with variations on a theme:
-->

本章中，我们对于之前的主题加入不同的变化：

<!--
* Previous chapters consider intrinsically-typed calculi;
  here we consider one that is untyped but intrinsically scoped.
-->

* 之前的章节中讨论了内在类型的演算；我们这次讨论无类型，但是内在作用域的演算。

<!--
* Previous chapters consider call-by-value calculi;
  here we consider call-by-name.
-->

* 之前的章节中讨论了传值调用（Call-by-value）的演算；我们这次讨论传名调用（Call-by-name）。

<!--
* Previous chapters consider _weak head normal form_,
  where reduction stops at a lambda abstraction;
  here we consider _full normalisation_,
  where reduction continues underneath a lambda.
-->

* 之前的章节中讨论了**弱头部范式**（Weak Head Normal Form），其归约止步于
  λ 抽象；我们这次讨论**完全正规化**（Full Normalisation），其在 λ 抽象之下仍然继续归约。

<!--
* Previous chapters consider _deterministic_ reduction,
  where there is at most one redex in a given term;
  here we consider _non-deterministic_ reduction
  where a term may contain many redexes and any one of them may reduce.
-->

* 之前的章节中讨论了**确定性**（Deterministic）的归约，每个项中至多有一个可归约项；
  我们这次讨论**非确定性**（Non-deterministic）的归约，每个项中可能有多个可归约项，而每一个都可归约。

<!--
* Previous chapters consider reduction of _closed_ terms,
  those with no free variables;
  here we consider _open_ terms,
  those which may have free variables.
-->

* 之前的章节中讨论了**封闭**（Closed）的项，其不包含自由变量；
  我们这次讨论**开放**（Open）的项，其可能包含自由变量。

<!--
* Previous chapters consider lambda calculus extended
  with natural numbers and fixpoints;
  here we consider a tiny calculus with just variables,
  abstraction, and application, in which the other
  constructs may be encoded.
-->

* 之前的章节中讨论了加入自然数和不动点的 λ 演算；
  我们这次讨论只包括变量、抽象和应用的小巧的演算，其他构造均可编码至其中。

<!--
In general, one may mix and match these features,
save that full normalisation requires open terms and
encoding naturals and fixpoints requires being untyped.
The aim of this chapter is to give some appreciation for
the range of different lambda calculi one may encounter.
-->

一般来说，我们可以将这些特性选择性的混合匹配，而完全正规化要求开放项，
且编码自然数和不动点需要无类型的演算。
本章的目的是展示 λ 演算可能出现的不同形式。


<!--
## Imports
-->

## 导入

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```


<!--
## Untyped is Uni-typed
-->

## 无类型即是单一类型

<!--
Our development will be close to that in
Chapter [DeBruijn](/DeBruijn/),
save that every term will have exactly the same type, written `★`
and pronounced "any".
This matches a slogan introduced by Dana Scott
and echoed by Robert Harper: "Untyped is Uni-typed".
One consequence of this approach is that constructs which previously
had to be given separately (such as natural numbers and fixpoints)
can now be defined in the language itself.
-->

我们的内容将会和 [DeBruijn] 章节中相似，只是每个项会有相同的类型，写作 `★`，读作『任意』。
这呼应了一条 Dana Scott 提出，Robert Harper 重复的口号：『无类型即是单一类型』。
这样的结果之一就是之前我们需要额外给出的构造（例如自然数和不动点），现在可以在直接在语言本身中定义。


<!--
## Syntax
-->

## 语法

<!--
First, we get all our infix declarations out of the way:
-->

我们首先定义中缀声明：

```agda
infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  ′_
infixl 7  _·_
```

<!--
## Types
-->

## 类型

<!--
We have just one type:
-->

我们只有一种类型：

```agda
data Type : Set where
  ★ : Type
```

<!--
#### Exercise (`Type≃⊤`) (practice)
-->

#### 练习 (`Type≃⊤`) （习题）

<!--
Show that `Type` is isomorphic to `⊤`, the unit type.
-->

证明 `Type` 与单元类型 `⊤` 同构。

```agda
-- 请将代码写在此处。
```

<!--
## Contexts
-->

## 语境

<!--
As before, a context is a list of types, with the type of the
most recently bound variable on the right:
-->

和之前一样，语境是类型的列表，最新出现的约束变量的类型出现在最右边：

```agda
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

<!--
We let `Γ` and `Δ` range over contexts.
-->

我们使用 `Γ` 和 `Δ` 来指代语境。

<!--
#### Exercise (`Context≃ℕ`) (practice)
-->

#### 练习 (`Context≃ℕ`) （习题）

<!--
Show that `Context` is isomorphic to `ℕ`.
-->

证明 `Context` 和 `ℕ` 同构。

```agda
-- 请将代码写在此处。
```

<!--
## Variables and the lookup judgment
-->

## 变量和查询判断

<!--
Intrinsically-scoped variables correspond to the lookup judgment.  The
rules are as before:
-->

内在作用域的变量对应了查询判断。规则与之前一样：

```agda
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
     ---------
   → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
```

<!--
We could write the rules with all instances of `A` and `B`
replaced by `★`, but arguably it is clearer not to do so.
-->

我们可以在规则中将所有的 `A` 和 `B` 都替换成 `★`，但不这样做更加清晰。

<!--
Because `★` is the only type, the judgment doesn't guarantee anything
useful about types.  But it does ensure that all variables are in
scope.  For instance, we cannot use `S S Z` in a context that only
binds two variables.
-->

因为 `★` 是唯一的类型，这样的判断并不会给出很多与类型相关的保证。
但它确实确保了所有的变量在作用域内。例如，我们不能在只有两个约束变量的语境中使用 `S S Z`。


<!--
## Terms and the scoping judgment
-->

## 项与作用域判断

<!--
Intrinsically-scoped terms correspond to the typing judgment, but with
`★` as the only type.  The result is that we check that terms are
well scoped — that is, that all variables they mention are in scope —
but not that they are well typed:
-->

内类作用域的项对应了赋型判断，但类型只有唯一的 `★` 类型。
得到的结果则是我们检查了每个项都是良作用域的——即所有使用的变量都在作用域内——而不是它们是良类型的：

```agda
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ}
    → Γ , ★ ⊢ ★
      ---------
    → Γ ⊢ ★

  _·_ : ∀ {Γ}
    → Γ ⊢ ★
    → Γ ⊢ ★
      ------
    → Γ ⊢ ★
```

<!--
Now we have a tiny calculus, with only variables, abstraction, and
application.  Below we will see how to encode naturals and
fixpoints into this calculus.
-->

现在我们有了一个迷你的演算，至包含变量、抽象和应用。
接下来我们展示如果将自然数和不动点编码进这个演算中。

<!--
## Writing variables as numerals
-->

## 用数表示变量

<!--
As before, we can convert a natural to the corresponding de Bruijn
index.  We no longer need to lookup the type in the context, since
every variable has the same type:
-->

如之前一样，我们可以将自然数转换为对应的 de Bruijn 因子。
我们不再需要从语境中查询变量的类型，因为每个变量都有一样的类型：

```agda
length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ ★
count {Γ , ★} {zero}    (s≤s z≤n)  =  Z
count {Γ , ★} {(suc n)} (s≤s p)    =  S (count p)
```

<!--
We can then introduce a convenient abbreviation for variables:
-->

我们可以接下来引入一种变量的缩略用法：

```agda
#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ ★
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
```

<!--
## Test examples
-->

## 测试例子

<!--
Our only example is computing two plus two on Church numerals:
-->

我们唯一的例子是用 Church 数计算二加二：

```agda
twoᶜ : ∀ {Γ} → Γ ⊢ ★
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

fourᶜ : ∀ {Γ} → Γ ⊢ ★
fourᶜ = ƛ ƛ (# 1 · (# 1 · (# 1 · (# 1 · # 0))))

plusᶜ : ∀ {Γ} → Γ ⊢ ★
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

2+2ᶜ : ∅ ⊢ ★
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ
```

<!--
Before, reduction stopped when we reached a lambda term, so we had to
compute `` plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero `` to ensure we reduced
to a representation of the natural four.  Now, reduction continues
under lambda, so we don't need the extra arguments.  It is convenient
to define a term to represent four as a Church numeral, as well as
two.
-->

在之前，我们在遇到 λ 抽象时停止归约，因此我们需要计算
`` plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ``
来确保我们归约至自然数四。
现在，归约在 λ 之下继续进行，所以我们不需要额外的参数。
为了便利，我们定义用 Church 数来表示二和四的项。

<!--
## Renaming
-->

## 重命名

<!--
Our definition of renaming is as before.  First, we need an extension lemma:
-->

我们重命名的定义与以前一样。首先我们需要一条扩充引理：

```agda
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```
<!--
We could replace all instances of `A` and `B` by `★`, but arguably it is
clearer not to do so.
-->

我们可以在规则中将所有的 `A` 和 `B` 都替换成 `★`，但不这样做更加清晰。

<!--
Now it is straightforward to define renaming:
-->

现在定义重命名就很直接了：

```agda
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
```
<!--
This is exactly as before, save that there are fewer term forms.
-->

这和之前一样，只是我们项的形式更少了。

<!--
## Simultaneous substitution
-->

## 同时替换

<!--
Our definition of substitution is also exactly as before.
First we need an extension lemma:
-->

我们重命名的定义与以前一样。首先我们需要一条扩充引理：

```agda
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)
```
<!--
Again, we could replace all instances of `A` and `B` by `★`.
-->

一样，我们可以把所有的 `A` 和 `B` 替换成 `★`。

<!--
Now it is straightforward to define substitution:
-->

现在定义替换就很直接了：

```agda
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
```
<!--
Again, this is exactly as before, save that there are fewer term forms.
-->

同样，这和之前一样，只是我们项的形式更少了。

<!--
## Single substitution
-->

## 单个替换

<!--
It is easy to define the special case of substitution for one free variable:
-->

定义替换一个自由变量的特例很简单：

```agda
subst-zero : ∀ {Γ B} → (Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (Γ ⊢ A)
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x

_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (subst-zero M) {A} N
```

<!--
## Neutral and normal terms
-->

## 中性项和范式

<!--
Reduction continues until a term is fully normalised.  Hence, instead
of values, we are now interested in _normal forms_.  Terms in normal
form are defined by mutual recursion with _neutral_ terms:
-->

直到项完全范式化之前，规则可以继续进行。
因此，我们现在在意的是**范式**（Normal Form），而不是值。
范式的项由与**中性项**（Neutral Terms）共同递归定义：

```agda
data Neutral : ∀ {Γ A} → Γ ⊢ A → Set
data Normal  : ∀ {Γ A} → Γ ⊢ A → Set
```

<!--
Neutral terms arise because we now consider reduction of open terms,
which may contain free variables.  A term is neutral if it is a
variable or a neutral term applied to a normal term:
-->

中性项由于我们需要考虑带有自由变量的开放项而产生。
一个项在其为变量时，或者是将中性项应用于范式项时，是一个中性项：

```agda
data Neutral where

  `_  : ∀ {Γ A} (x : Γ ∋ A)
      -------------
    → Neutral (` x)

  _·_  : ∀ {Γ} {L M : Γ ⊢ ★}
    → Neutral L
    → Normal M
      ---------------
    → Neutral (L · M)
```

<!--
A term is a normal form if it is neutral or an abstraction where the
body is a normal form. We use `′_` to label neutral terms.
Like `` `_ ``, it is unobtrusive:
-->

一个项在其为中型项时，或者其为抽象且抽象体是范式时，是一个范式。
我们用 `′_` 来标记中型项。
如果 `` `_ `` 一样，它不显眼：

```agda
data Normal where

  ′_ : ∀ {Γ A} {M : Γ ⊢ A}
    → Neutral M
      ---------
    → Normal M

  ƛ_  : ∀ {Γ} {N : Γ , ★ ⊢ ★}
    → Normal N
      ------------
    → Normal (ƛ N)
```

<!--
We introduce a convenient abbreviation for evidence that a variable is neutral:
-->

我们引入一种缩略用法，来提供变量是中型项的证明：

```agda
#′_ : ∀ {Γ} (n : ℕ) {n∈Γ : True (suc n ≤? length Γ)} → Neutral {Γ} (# n)
#′_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
```

<!--
For example, here is the evidence that the Church numeral two is in
normal form:
-->

比如说，下面是 Church 数二为范式的证明：

```agda
_ : Normal (twoᶜ {∅})
_ = ƛ ƛ (′ #′ 1 · (′ #′ 1 · (′ #′ 0)))
```

<!--
The evidence that a term is in normal form is almost identical to
the term itself, decorated with some additional primes to indicate
neutral terms, and using `#′` in place of `#`
-->

某一项为范式的证明与其本身基本一致，其中包括的额外的撇来标记中型项，并且其中使用了 `#′` 而不是 `#`。


<!--
## Reduction step
-->

## 归约步骤

<!--
The reduction rules are altered to switch from call-by-value to
call-by-name and to enable full normalisation:
-->

归约规则从传值调用改为传名调用，以实现完全范式化：

<!--
* The rule `ξ₁` remains the same as it was for the simply-typed
  lambda calculus.
-->

* 规则 `ξ₁` 与简单类型的 λ 演算一样，保持不变。

<!--
* In rule `ξ₂`, the requirement that the term `L` is a value
  is dropped. So this rule can overlap with `ξ₁` and
  reduction is _non-deterministic_. One can choose to reduce
  a term inside either `L` or `M`.
-->

* 规则 `ξ₂` 之中，项 `L` 是值的要求现在被丢弃了。
  所以这条规则现在与 `ξ₁` 重合，且归约是**非确定的**。
  现在可选择归约 `L` 或者 `M` 中的项。

<!--
* In rule `β`, the requirement that the argument is a value
  is dropped, corresponding to call-by-name evaluation.
  This introduces further non-determinism, as `β` overlaps
  with `ξ₂` when there are redexes in the argument.
-->

* 规则 `β` 之中，参数是值的要求现在被丢弃了，对应了传名调用的求值。
  这引入了更多的非确定性，由于 `β` 与 `ξ₂` 在参数中有可归约项时重合。

<!--
* A new rule `ζ` is added, to enable reduction underneath a lambda.
-->

* 额外了新规则 `ζ`，使得 λ 抽象下可以继续归约。

<!--
Here are the formalised rules:
-->

这里是形式化的规则：

```agda
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ₁ : ∀ {Γ} {L L′ M : Γ ⊢ ★}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂ : ∀ {Γ} {L M M′ : Γ ⊢ ★}
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  ζ : ∀ {Γ} {N N′ : Γ , ★ ⊢ ★}
    → N —→ N′
      -----------
    → ƛ N —→ ƛ N′
```

<!--
#### Exercise (`variant-1`) (practice)
-->

#### 练习 (`variant-1`) （习题）

<!--
How would the rules change if we want call-by-value where terms
normalise completely?  Assume that `β` should not permit reduction
unless both terms are in normal form.
-->

如果我们想要传值调用，但需要项范式化其中的项的话，要怎么样修改规则？
假设 `β` 在除了两个项都是范式时，不允许归约。

```agda
-- 请将代码写在此处。
```

<!--
#### Exercise (`variant-2`) (practice)
-->

#### 练习 (`variant-2`) （习题）

<!--
How would the rules change if we want call-by-value where terms
do not reduce underneath lambda?  Assume that `β`
permits reduction when both terms are values (that is, lambda
abstractions).  What would `2+2ᶜ` reduce to in this case?
-->

如果我们想要传值调用，但项不在 λ 之下归约的话，要怎么样修改规则？
假设 `β` 在双项均为值（即 λ 抽象）时允许归约。
`2+2ᶜ` 在这种情况下会归约成什么？


```agda
-- 请将代码写在此处。
```


<!--
## Reflexive and transitive closure
-->

## 自反传递闭包

<!--
We cut-and-paste the previous definition:
-->

我们复制粘贴之前的定义：

```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  step—→ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M —↠ N
    → L —→ M
      ------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```


<!--
## Example reduction sequence
-->

## 归约序列的例子

<!--
Here is the demonstration that two plus two is four:
-->

这里是二加二得四的展示：

```agda
_ : 2+2ᶜ —↠ fourᶜ
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ
  —→⟨ ξ₁ β ⟩
    (ƛ ƛ ƛ twoᶜ · # 1 · (# 2 · # 1 · # 0)) · twoᶜ
  —→⟨ β ⟩
    ƛ ƛ twoᶜ · # 1 · (twoᶜ · # 1 · # 0)
  —→⟨ ζ (ζ (ξ₁ β)) ⟩
    ƛ ƛ ((ƛ # 2 · (# 2 · # 0)) · (twoᶜ · # 1 · # 0))
  —→⟨ ζ (ζ β) ⟩
    ƛ ƛ # 1 · (# 1 · (twoᶜ · # 1 · # 0))
  —→⟨ ζ (ζ (ξ₂ (ξ₂ (ξ₁ β)))) ⟩
    ƛ ƛ # 1 · (# 1 · ((ƛ # 2 · (# 2 · # 0)) · # 0))
  —→⟨ ζ (ζ (ξ₂ (ξ₂ β))) ⟩
   ƛ (ƛ # 1 · (# 1 · (# 1 · (# 1 · # 0))))
  ∎
```
<!--
After just two steps the top-level term is an abstraction,
and `ζ` rules drive the rest of the normalisation.
-->

在两步之后，顶层项是一个抽象，而 `ζ` 规则支持了剩余的范式化。


<!--
## Progress
-->

## 可进性

<!--
Progress adapts.  Instead of claiming that every term either is a value
or takes a reduction step, we claim that every term is either in normal
form or takes a reduction step.
-->

可进性相应地也变更了。之前我们说每个项要么是值，要么可以归约一步；我们现在说每个项要么是范式，要么可以归约一步。

<!--
Previously, progress only applied to closed, well-typed terms.  We had
to rule out terms where we apply something other than a function (such
as `` `zero ``) or terms with a free variable.  Now we can demonstrate
it for open, well-scoped terms.  The definition of normal form permits
free variables, and we have no terms that are not functions.
-->

之前，可进性只应用于封闭的、良类型的项。
我们没有考虑诸如应用一个不是函数的项（如 `` `zero` ``）或者是带有自由变量的项。
现在我们展示的包含了开放的、良作用域的项。
范式的定义容许了自由变量，且我们也有不是函数的项。

<!--
A term makes progress if it can take a step or is in normal form:
-->

如果一个项可以归约一步，或其为范式，那么它具有可进性：

```agda
data Progress {Γ A} (M : Γ ⊢ A) : Set where

  step : ∀ {N : Γ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Normal M
      ----------
    → Progress M
```

<!--
If a term is well scoped then it satisfies progress:
-->

如果一个项是良作用域的，那么它满足可进性：

```agda
progress : ∀ {Γ A} → (M : Γ ⊢ A) → Progress M
progress (` x)                                 =  done (′ ` x)
progress (ƛ N)  with  progress N
... | step N—→N′                               =  step (ζ N—→N′)
... | done NrmN                                =  done (ƛ NrmN)
progress (` x · M) with progress M
... | step M—→M′                               =  step (ξ₂ M—→M′)
... | done NrmM                                =  done (′ (` x) · NrmM)
progress ((ƛ N) · M)                           =  step β
progress (L@(_ · _) · M) with progress L
... | step L—→L′                               =  step (ξ₁ L—→L′)
... | done (′ NeuL) with progress M
...    | step M—→M′                            =  step (ξ₂ M—→M′)
...    | done NrmM                             =  done (′ NeuL · NrmM)
```

<!--
We induct on the evidence that the term is well scoped:
-->

我们对项为良作用域的证明上进行归纳：

<!--
* If the term is a variable, then it is in normal form.
  (This contrasts with previous proofs, where the variable case was
  ruled out by the restriction to closed terms.)
* If the term is an abstraction, recursively invoke progress on the body.
  (This contrast with previous proofs, where an abstraction is
  immediately a value.):
  + If it steps, then the whole term steps via `ζ`.
  + If it is in normal form, then so is the whole term.
* If the term is an application, consider the function subterm:
  + If it is a variable, recursively invoke progress on the argument:
    - If it steps, then the whole term steps via `ξ₂`;
    - If it is normal, then so is the whole term.
  + If it is an abstraction, then the whole term steps via `β`.
  + If it is an application, recursively apply progress to the function subterm:
    - If it steps, then the whole term steps via `ξ₁`.
    - If it is normal, recursively apply progress to the argument subterm:
      * If it steps, then the whole term steps via `ξ₂`.
      * If it is normal, then so is the whole term.
-->

* 如果项是变量，那么它是范式。
  （这与之前的证明不同，以往项为变量的情况被闭项的条件所排除了。）
* 如果项是抽象，那么我们对其抽象体应用可进性。
  （这与之前的证明不同，以往抽象本身即是值。）：
  + 如果它步进，那么整个项由 `ζ` 步进。
  + 如果它是范式，那么整个项也是范式。
* 如果项是应用，那么我们考虑其函数子项：
  + 如果它是变量，我们对参数子项递归应用可进性：
    - 如果它步进，那么整个项由 `ξ₂` 步进；
    - 如果它是范式，那么整个项也是范式。
  + 如果它是抽象，那么整个项由 `β` 步进。
  + 如果它是应用，我们对其函数子项递归应用可进性：
    - 如果它步进，那么整个项由 `ξ₁` 步进。
    - 如果它是范式，我们对参数子项递归应用可进性：
      * 如果它步进，那么整个项由 `ξ₂` 步进；
      * 如果它是范式，那么整个项也是范式。

<!--
The final equation for progress uses an _at pattern_ of the form `P@Q`,
which matches only if both pattern `P` and pattern `Q` match.  Character
`@` is one of the few that Agda doesn't allow in names, so spaces are not
required around it.  In this case, the pattern ensures that `L` is an
application.
-->

可进性最后一条等式中使用了 `P@Q` 形式的 **at 模式**，其只在模式 `P` 和 `Q` 都匹配时匹配。
`@` 是 Agda 不允许出现在变量名中的字符之一，因此不需要在它周围加空格。
在此处，这个模式确保了 `L` 是一个应用。

<!--
## Evaluation
-->

## 求值

<!--
As previously, progress immediately yields an evaluator.
-->

与之前一样，可进性直接提供了一个求值器。

<!--
Gas is specified by a natural number:
-->

汽油由自然数给出：

```agda
record Gas : Set where
  constructor gas
  field
    amount : ℕ
```

<!--
When our evaluator returns a term `N`, it will either give evidence that
`N` is normal or indicate that it ran out of gas:
-->

当我们的求值器返回项 `N`，它要么会给出 `N` 是范式的证明，或者提示汽油耗尽：

```agda
data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Normal N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
```

<!--
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished:
-->

给定类型 `A` 的项 `L`，求值器会对于某 `N` 返回自 `L` 至 `N` 的归约序列，并提示归约是否完成：

```agda
data Steps : ∀ {Γ A} → Γ ⊢ A → Set where

  steps : ∀ {Γ A} {L N : Γ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```

<!--
The evaluator takes gas and a term and returns the corresponding steps:
-->

求值器取汽油和项，返回对应的步骤：

```agda
eval : ∀ {Γ A}
  → Gas
  → (L : Γ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done NrmL                          =  steps (L ∎) (done NrmL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```

<!--
The definition is as before, save that the empty context `∅`
generalises to an arbitrary context `Γ`.
-->

定义与之前一样，除了我们将空语境 `∅` 推广至任意语境 `Γ`。

<!--
## Example
-->

## 例子

<!--
We reiterate our previous example. Two plus two is four, with Church numerals:
-->

我们重复之前的例子。二加二得四，以 Church 数来表示：

```agda
_ : eval (gas 100) 2+2ᶜ ≡
  steps
   ((ƛ
     (ƛ
      (ƛ
       (ƛ
        (` (S (S (S Z)))) · (` (S Z)) ·
        ((` (S (S Z))) · (` (S Z)) · (` Z))))))
    · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
    · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
   —→⟨ ξ₁ β ⟩
    (ƛ
     (ƛ
      (ƛ
       (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) ·
       ((` (S (S Z))) · (` (S Z)) · (` Z)))))
    · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
   —→⟨ β ⟩
    ƛ
    (ƛ
     (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) ·
     ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
   —→⟨ ζ (ζ (ξ₁ β)) ⟩
    ƛ
    (ƛ
     (ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) ·
     ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
   —→⟨ ζ (ζ β) ⟩
    ƛ
    (ƛ
     (` (S Z)) ·
     ((` (S Z)) ·
      ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z))))
   —→⟨ ζ (ζ (ξ₂ (ξ₂ (ξ₁ β)))) ⟩
    ƛ
    (ƛ
     (` (S Z)) ·
     ((` (S Z)) ·
      ((ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) · (` Z))))
   —→⟨ ζ (ζ (ξ₂ (ξ₂ β))) ⟩
    ƛ (ƛ (` (S Z)) · ((` (S Z)) · ((` (S Z)) · ((` (S Z)) · (` Z)))))
   ∎)
   (done
    (ƛ
     (ƛ
      (′
       (` (S Z)) ·
       (′ (` (S Z)) · (′ (` (S Z)) · (′ (` (S Z)) · (′ (` Z)))))))))
_ = refl
```

<!--
## Naturals and fixpoint
-->

## 自然数和不动点

<!--
We could simulate naturals using Church numerals, but computing
predecessor is tricky and expensive.  Instead, we use a different
representation, called Scott numerals, where a number is essentially
defined by the expression that corresponds to its own case statement.
-->

我们可以使用 Church 数来表示自然数，但是计算某数的前继很复杂且昂贵。
取而代之的，我们使用另一种表示方法，叫做 Scott 数，其核心思想是一个数对应了对其自身的分情况讨论。

<!--
Recall that Church numerals apply a given function for the
corresponding number of times.  Using named terms, we represent the
first three Church numerals as follows:
-->

回忆 Church 数将某给定函数应用对应的次数。
使用命名的项，我们如下表示前三个 Church 数：

    zero  =  ƛ s ⇒ ƛ z ⇒ z
    one   =  ƛ s ⇒ ƛ z ⇒ s · z
    two   =  ƛ s ⇒ ƛ z ⇒ s · (s · z)

<!--
In contrast, for Scott numerals, we represent the first three naturals
as follows:
-->

作为对比，我们如下表示前三个 Scott 数：

    zero = ƛ s ⇒ ƛ z ⇒ z
    one  = ƛ s ⇒ ƛ z ⇒ s · zero
    two  = ƛ s ⇒ ƛ z ⇒ s · one

<!--
Each representation expects two arguments, one corresponding to
the successor branch of the case (it expects an additional argument,
the predecessor of the current argument) and one corresponding to the
zero branch of the case.  (The cases could be in either order.
We put the successor case first to ease comparison with Church numerals.)
-->

每个数取两个参数，一个对应了后继分支的情况（它要求额外的参数，即当前参数的前继），
一个对应了零分支的情况。
（两种情况可以以任意顺序出现。我们在此将后继分支放在前面，以方便与 Church 数对比。）

<!--
Here is the Scott representation of naturals encoded with de Bruijn indexes:
-->

下面是以 de Bruijn 因子编码的自然数的 Scott 表示法：

```agda
`zero : ∀ {Γ} → (Γ ⊢ ★)
`zero = ƛ ƛ (# 0)

`suc_ : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★)
`suc_ M  = (ƛ ƛ ƛ (# 1 · # 2)) · M

case : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★) → (Γ , ★ ⊢ ★)  → (Γ ⊢ ★)
case L M N = L · (ƛ N) · M
```

<!--
Here we have been careful to retain the exact form of our previous
definitions.  The successor branch expects an additional variable to
be in scope (as indicated by its type), so it is converted to an
ordinary term using lambda abstraction.
-->

我们小心地保留之前定义相同的形式。
后继分支期望作用域内有一个额外的变量（由它的类型可以看出），所以它被一个抽象转换成了一个普通的项。

<!--
Applying successor to the zero indeed reduces to the Scott numeral
for one.
-->

对零使用后继的确归约至 Scott 数表示的一：

```agda
_ : eval (gas 100) (`suc_ {∅} `zero) ≡
    steps
        ((ƛ (ƛ (ƛ # 1 · # 2))) · (ƛ (ƛ # 0))
    —→⟨ β ⟩
         ƛ (ƛ # 1 · (ƛ (ƛ # 0)))
    ∎)
    (done (ƛ (ƛ (′ (` (S Z)) · (ƛ (ƛ (′ (` Z))))))))
_ = refl
```

<!--
We can also define fixpoint.  Using named terms, we define:
-->

我们同样可以定义不动点。使用命名的项，我们定义：

    μ f = (ƛ x ⇒ f · (x · x)) · (ƛ x ⇒ f · (x · x))

<!--
This works because:
-->

它能实现不动点的原因是：

      μ f
    ≡
      (ƛ x ⇒ f · (x · x)) · (ƛ x ⇒ f · (x · x))
    —→
      f · ((ƛ x ⇒ f · (x · x)) · (ƛ x ⇒ f · (x · x)))
    ≡
      f · (μ f)

<!--
With de Bruijn indices, we have the following:
-->

使用 de Bruijn 因子，我们有如下：

```agda
μ_ : ∀ {Γ} → (Γ , ★ ⊢ ★) → (Γ ⊢ ★)
μ N  =  (ƛ ((ƛ (# 1 · (# 0 · # 0))) · (ƛ (# 1 · (# 0 · # 0))))) · (ƛ N)
```

<!--
The argument to fixpoint is treated similarly to the successor branch of case.
-->

不动点的参数与之前自然数的后继分支的处理方法相似。

<!--
We can now define two plus two exactly as before:
-->

我们可以如之前一样定义二加二：

```agda
infix 5 μ_

two : ∀ {Γ} → Γ ⊢ ★
two = `suc `suc `zero

four : ∀ {Γ} → Γ ⊢ ★
four = `suc `suc `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ ★
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))
```

<!--
Because `` `suc `` is now a defined term rather than primitive,
it is no longer the case that `plus · two · two` reduces to `four`,
but they do both reduce to the same normal term.
-->

由于 `` `suc `` 是定义的项，而不是原语项，
`plus · two · two` 不再归约至 `four`，
但是它们都归约至相同的范式。


<!--
#### Exercise `plus-eval` (practice)
-->

#### 练习 `plus-eval` （实践）

<!--
Use the evaluator to confirm that `plus · two · two` and `four`
normalise to the same term.
-->

使用求值器，证实 `plus · two · two` 和 `four` 正规化至相同的项。

```agda
-- 请将代码写在此处。
```

<!--
#### Exercise `multiplication-untyped` (recommended)
-->

#### 练习 `multiplication-untyped` （推荐）

<!--
Use the encodings above to translate your definition of
multiplication from previous chapters with the Scott
representation and the encoding of the fixpoint operator.
Confirm that two times two is four.
-->

使用上文中的编码，翻译你之前章节乘法的定义，使得其使用 Scott 表示法和编码后的不动点运算符。
证实二乘二得四。

```agda
-- 请将代码写在此处。
```

<!--
#### Exercise `encode-more` (stretch)
-->

#### 练习 `encode-more` （延伸）

<!--
Along the lines above, encode all of the constructs of
Chapter [More](/More/),
save for primitive numbers, in the untyped lambda calculus.
-->

用上文中类似的方法，编码 [More](/More/) 章节除了原语数字以外的剩余构造，用无类型的 λ 演算。

```agda
-- 请将代码写在此处。
```


<!--
## Multi-step reduction is transitive
-->

## 多步归约是传递的

<!--
In our formulation of the reflexive transitive closure of reduction,
i.e., the `—↠` relation, there is not an explicit rule for
transitivity. Instead the relation mimics the structure of lists by
providing a case for an empty reduction sequence and a case for adding
one reduction to the front of a reduction sequence.  The following is
the proof of transitivity, which has the same structure as the append
function `_++_` on lists.
-->

在我们对自反传递闭包的形式化，即 `—↠` 关系中，没有出现直接的传递性规则。
取而代之的是，这个关系模仿了列表形式，有一种空归约序列的情况，也有一种将一步归约加在归约序列之前的情况。
下面是传递性的证明，其与列表的附加 `_++_` 函数的结构相似。

```agda
—↠-trans : ∀{Γ}{A}{L M N : Γ ⊢ A}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M ∎) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)
```

<!--
The following notation makes it convenient to employ
transitivity of `—↠`.
-->

下面的记法使得应用 `—↠` 的传递性更加方便。

```agda
infixr 2 _—↠⟨_⟩_

_—↠⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = —↠-trans L—↠M M—↠N
```

<!--
## Multi-step reduction is a congruence
-->

## 多步归约是合同性的

<!--
Recall from Chapter [Induction](/Induction/) that a
relation `R` is a _congruence_ for a given function `f` if it is
preserved by that function, i.e., if `R x y` then `R (f x) (f y)`.
The term constructors `ƛ_` and `_·_` are functions, and so
the notion of congruence applies to them as well. Furthermore, when a
relation is a congruence for all of the term constructors, we
say that the relation is a congruence for the language in question, in
this case the untyped lambda calculus.
-->

回忆 [Induction](/Induction/) 章节中，一个关系 `R` 对于一个给定的函数 `f` 在函数应用后仍然保持关系时，满足**合同关系**，
即『若 `R x y`，则 `R (f x) (f y)`』。
项构造子 `ƛ_` and `_·_` 是函数，因此合同性的概念也可作用于它们之上。
另外，当一个关系对于所有项的构造子满足合同时，我们说它对于整个语言满足合同性，在此即无类型的 λ 演算。

<!--
The rules `ξ₁`, `ξ₂`, and `ζ` ensure that the reduction relation is a
congruence for the untyped lambda calculus. The multi-step reduction
relation `—↠` is also a congruence, which we prove in the following
three lemmas.
-->

规则 `ξ₁` 、`ξ₂` 和 `ζ` 保证了归约关系对于无类型的 λ 演算满足合同性。
多步归约也是一个合同关系，我们在下面三条引理中证明。

```agda
appL-cong : ∀ {Γ} {L L' M : Γ ⊢ ★}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {Γ}{L}{L'}{M} (L ∎) = L · M ∎
appL-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁ r ⟩ appL-cong rs
```

<!--
The proof of `appL-cong` is by induction on the reduction sequence `L —↠ L'`.
* Suppose `L —↠ L` by `L ∎`. Then we have
  `L · M —↠ L · M` by `L · M ∎`.
* Suppose `L —↠ L''` by `L —→⟨ r ⟩ rs`, so
  `L —→ L'` by `r` and `L' —↠ L''` by `rs`.
  We have `L · M —→ L' · M` by `ξ₁ r` and
  `L' · M —↠ L'' · M` by the induction hypothesis applied to `rs`.
  We conclude that ``L · M —↠ L'' · M`` by putting these two
  facts together using `_—→⟨_⟩_`.
-->

`appL-cong` 的证明对于归约序列 `L —↠ L'` 进行归纳。
* 若 `L —↠ L` 由 `L ∎` 成立。那我们可从 `L · M ∎` 得 `L · M —↠ L · M` 。
* 若 `L —↠ L''` 由 `L —→⟨ r ⟩ rs` 成立，那么
  `L —→ L'` 由 `r` 成立，且 `L' —↠ L''` 由 `rs` 成立。
  我们可从 `ξ₁ r` 得 `L · M —→ L' · M`，且对 `rs` 应用归纳假设得到
  `L' · M —↠ L'' · M`。
  我们可以将两者用 `_—→⟨_⟩_` 组合来获得 ``L · M —↠ L'' · M``。

<!--
The proofs of `appR-cong` and `abs-cong` follow the same pattern as
the proof for `appL-cong`.
-->

`appR-cong` 和 `abs-cong` 的证明与 `appL-cong` 的证明使用一样的方法。

```agda
appR-cong : ∀ {Γ} {L M M' : Γ ⊢ ★}
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {Γ}{L}{M}{M'} (M ∎) = L · M ∎
appR-cong {Γ}{L}{M}{M'} (M —→⟨ r ⟩ rs) = L · M —→⟨ ξ₂ r ⟩ appR-cong rs
```

```agda
abs-cong : ∀ {Γ} {N N' : Γ , ★ ⊢ ★}
         → N —↠ N'
           ----------
         → ƛ N —↠ ƛ N'
abs-cong (M ∎) = ƛ M ∎
abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ ζ r ⟩ abs-cong rs
```

## Unicode

<!--
This chapter uses the following unicode:
-->

本章使用了下列 Unicode：

    ★  U+2605  BLACK STAR (\st)

<!--
The `\st` command permits navigation among many different stars;
the one we use is number 7.
-->

`\st` 命令允许选取不同种类的星，我们使用的是第七种。
