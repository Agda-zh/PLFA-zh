---
title     : "BigStep: 无类型 λ-演算的大步语义"
permalink : /BigStep/
translators : ["starxingchenc"]
---

```agda
module plfa.part2.BigStep where
```
<!--
## Introduction
-->

## 简介

<!--
The call-by-name evaluation strategy is a deterministic method for
computing the value of a program in the lambda calculus.  That is,
call-by-name produces a value if and only if beta reduction can reduce
the program to a lambda abstraction. In this chapter we define
call-by-name evaluation and prove the forward direction of this
if-and-only-if. The backward direction is traditionally proved via
Curry-Feys standardisation, which is quite complex.  We give a sketch
of that proof, due to Plotkin, but postpone the proof in Agda until
after we have developed a denotational semantics for the lambda
calculus, at which point the proof is an easy corollary of properties
of the denotational semantics.
-->

传名调用求值策略（Call-by-name Evaluation Strategy）是在 λ-演算中计算程序值的一种确定性方法。
也就是说，传名调用能够求出值当且仅当 β-归约能将程序归约为一个 λ-抽象。
在这一章节，我们将定义传名调用求值并且证明这个等价命题的必要性。
充分性的部分较为复杂，通常通过 Curry-Feys 标准化证明。
根据 Plotkin 的工作，我们给出这个证明的概要，
但是由于这是指称语义的一个简单性质，
我们将在为 λ-演算发展出指称语义后在 Agda 中完整地证明它。

<!--
We present the call-by-name strategy as a relation between an input
term and an output value. Such a relation is often called a _big-step
semantics_, written `M ⇓ V`, as it relates the input term `M` directly
to the final result `V`, in contrast to the small-step reduction
relation, `M —→ M′`, that maps `M` to another term `M′` in which a
single sub-computation has been completed.
-->

我们将传名调用策略表示为一个输入表达式与输出值间的关系。
因为这样的关系将输入表达式 `M` 和最终结果 `V` 直接相联系，
它通常被叫做**大步语义（Big-stepsemantics）**，写做 `M ⇓ V`。
而小步归约关系则被写做 `M —→ M′`，它仅通过一步子计算来将 `M` 归约为另一个表达式 `M′`。


<!--
## Imports
-->

## 导入

```agda
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong-app)
open import Data.Product.Base using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function.Base using (_∘_)
open import plfa.part2.Untyped
  using (Context; _⊢_; _∋_; ★; ∅; _,_; Z; S_; `_; #_; ƛ_; _·_;
  subst; subst-zero; exts; rename; β; ξ₁; ξ₂; ζ; _—→_; _—↠_; _—→⟨_⟩_; _∎;
  —↠-trans; appL-cong)
open import plfa.part2.Substitution using (Subst; ids)
```

<!--
## Environments
-->

## 环境

<!--
To handle variables and function applications, there is the choice
between using substitution, as in `—→`, or to use an _environment_.
An environment in call-by-name is a map from variables to closures,
that is, to terms paired with their environments. We choose to use
environments instead of substitution because the point of the
call-by-name strategy is to be closer to an implementation of the
language. Also, the denotational semantics introduced in later
chapters uses environments and the proof of adequacy
is made easier by aligning these choices.
-->

为了处理变量和函数应用，我们要么像在 `—→` 中一样使用替换，要么使用一个**环境（Environment）**。
传名调用中的环境是一个从变量到闭包（即项与其对应的环境）的映射。
我们之所以使用环境取代替换是因为传名调用的核心更接近于语言的实现。
在后续章节中介绍的指称语义也会用到环境，而且对 adequacy 的证明也会变得更加容易。

<!--
We define environments and closures as follows.
-->

我们如下定义环境和闭包。

```agda
ClosEnv : Context → Set

data Clos : Set where
  clos : ∀{Γ} → (M : Γ ⊢ ★) → ClosEnv Γ → Clos

ClosEnv Γ = ∀ (x : Γ ∋ ★) → Clos
```

<!--
As usual, we have the empty environment, and we can extend an
environment.
-->

通常，我们有空环境，也可以扩展一个环境。

```agda
∅' : ClosEnv ∅
∅' ()

_,'_ : ∀ {Γ} → ClosEnv Γ → Clos → ClosEnv (Γ , ★)
(γ ,' c) Z = c
(γ ,' c) (S x) = γ x
```

<!--
## Big-step evaluation
-->

## 大步求值

<!--
The big-step semantics is represented as a ternary relation,
written `γ ⊢ M ⇓ V`, where `γ` is the environment, `M` is the input
term, and `V` is the result value.  A _value_ is a closure whose term
is a lambda abstraction.
-->

大步语义被表现为一个三元关系，写作 `γ ⊢ M ⇓ V`，
其中 `γ` 是环境，`M`是输入项，`V` 是结果值。 **值（Value）** 是一个项是 λ-抽象的闭包。

```agda
data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Γ ⊢ ★) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Γ ∋ ★}{Δ}{δ : ClosEnv Δ}{M : Δ ⊢ ★}{V}
    → γ x ≡ clos M δ
    → δ ⊢ M ⇓ V
      -----------
    → γ ⊢ ` x ⇓ V

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{M : Γ , ★ ⊢ ★}
    → γ ⊢ ƛ M ⇓ clos (ƛ M) γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Γ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N : Δ , ★ ⊢ ★}{V}
    → γ ⊢ L ⇓ clos (ƛ N) δ   →   (δ ,' clos M γ) ⊢ N ⇓ V
      ---------------------------------------------------
    → γ ⊢ L · M ⇓ V
```

<!--
* The `⇓-var` rule evaluates a variable by finding the associated
  closure in the environment and then evaluating the closure.

* The `⇓-lam` rule turns a lambda abstraction into a closure
  by packaging it up with its environment.

* The `⇓-app` rule performs function application by first evaluating
  the term `L` in operator position. If that produces a closure containing
  a lambda abstraction `ƛ N`, then we evaluate the body `N` in an
  environment extended with the argument `M`. Note that `M` is not
  evaluated in rule `⇓-app` because this is call-by-name and not
  call-by-value.
-->

* `⇓-var` 规则通过对环境中找到的相关闭包求值，从而完成对变量的求值。

* `⇓-lam` 规则通过包装 λ-抽象与其环境，将其转变为一个闭包。

* `⇓-app` 规则分两步处理函数应用。首先对操作位的项 `L` 求值，如果产生了一个包含 λ-抽象 `ƛ N` 的闭包，
  就在扩展了参数 `M` 的环境中对 `N` 求值。注意到 `M` 并未在 `⇓-app` 规则中被求值，
  因为进行的是传名调用而不是传值调用。


<!--
#### Exercise `big-step-eg` (practice)
-->

#### 练习 `big-step-eg`（实践）


<!--
Show that `(ƛ ƛ # 1) · ((ƛ # 0 · # 0) · (ƛ # 0 · # 0))`
terminates under big-step call-by-name evaluation.
-->

证明 `(ƛ ƛ # 1) · ((ƛ # 0 · # 0) · (ƛ # 0 · # 0))` 能在大步传名调用求值下终止。



```
-- 请将代码写在此处
```

<!--
## The big-step semantics is deterministic
-->

## 大步语义是确定的

<!--
If the big-step relation evaluates a term `M` to both `V` and
`V′`, then `V` and `V′` must be identical. In other words, the
call-by-name relation is a partial function. The proof is a
straightforward induction on the two big-step derivations.
-->

如果大步关系将一个项 `M` 求值为 `V` 和 `V′`，则 `V` 和 `V′` 必然相同。
也就是说，传名调用关系是一个部分函数。该证明由两个大步语义的推论归纳得出。

```agda
⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{V V' : Clos}
  → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
  → V ≡ V'
⇓-determ (⇓-var eq1 mc) (⇓-var eq2 mc')
    with trans (sym eq1) eq2
... | refl = ⇓-determ mc mc'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc mc₁) (⇓-app mc' mc'')
    with ⇓-determ mc mc'
... | refl = ⇓-determ mc₁ mc''
```


<!--
## Big-step evaluation implies beta reduction to a lambda
-->

## 大步求值蕴含 β-归约至 λ-抽象

<!--
If big-step evaluation produces a value, then the input term can
reduce to a lambda abstraction by beta reduction:
-->

如果大步求值能够求出值，那么输入项能被 β-归约归约为一个 λ-抽象：

      ∅' ⊢ M ⇓ clos (ƛ N′) δ
      -----------------------------
    → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)

<!--
The proof is by induction on the big-step derivation. As is often
necessary, one must generalize the statement to get the induction to
go through. In the case for `⇓-app` (function application), the
argument is added to the environment, so the environment becomes
non-empty. The corresponding β reduction substitutes the argument into
the body of the lambda abstraction.  So we generalize the lemma to
allow an arbitrary environment `γ` and we add a premise that relates
the environment `γ` to an equivalent substitution `σ`.
-->

该证明通过对大步推导归纳来完成。通常，我们需要推广命题以完成归纳。
在 `⇓-app`（函数应用）的情况下，参数被添加到环境中，导致环境变得非空。
相应的 β-归约将参数替换进 λ-抽象的主体中。
所以我们将引理推广为允许任意环境 `γ` 并且添加一个前提将环境 `γ` 与等价的替代 `σ` 相关联。

<!--
The case for `⇓-app` also requires that we strengthen the
conclusion. In the case for `⇓-app` we have `γ ⊢ L ⇓ clos (λ N) δ` and
the induction hypothesis gives us `L —↠ ƛ N′`, but we need to know
that `N` and `N′` are equivalent. In particular, that `N′ ≡ subst τ N`
where `τ` is the substitution that is equivalent to `δ`. Therefore we
expand the conclusion of the statement, stating that the results are
equivalent.
-->

`⇓-app` 的情况也要求我们加强结论。
对于 `⇓-app`，有 `γ ⊢ L ⇓ clos (λ N) δ` 以及归纳假设给我们 `L —↠ ƛ N′`，
但我们需要知道 `N` 和 `N′` 是等价的。
特别地，`N' ≡ subst τ N`，其中 `τ` 是等价于 `δ` 的替换。
因此我们扩展命题的结论，以说明这两个结果是等价的。

<!--
We make the two notions of equivalence precise by defining the
following two mutually-recursive predicates `V ≈ M` and `γ ≈ₑ σ`.
-->

我们通过定义以下两个相互递归的谓词 `V ≈ M` 和 `γ ≈ₑ σ` 来得到两个精确等价的概念

```agda
_≈_ : Clos → (∅ ⊢ ★) → Set
_≈ₑ_ : ∀{Γ} → ClosEnv Γ → Subst Γ ∅ → Set

(clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ ∅ ] γ ≈ₑ σ × (N ≡ subst σ M)

γ ≈ₑ σ = ∀ x → (γ x) ≈ (σ x)
```

<!--
We can now state the main lemma:
-->

现在我们可以给出主要的引理。

<!--
    If γ ⊢ M ⇓ V  and  γ ≈ₑ σ,
    then  subst σ M —↠ N  and  V ≈ N  for some N.
-->

    如果 γ ⊢ M ⇓ V  且  γ ≈ₑ σ,
    那么有  subst σ M —↠ N  以及  V ≈ N  对于某个 N。

<!--
Before starting the proof, we establish a couple lemmas
about equivalent environments and substitutions.
-->

在开始证明之前，我们需要建立一些有关等价的环境和替换的引理。

<!--
The empty environment is equivalent to the identity substitution
`ids`, which we import from Chapter [Substitution](/Substitution/).
-->

空环境与我们从 [Substitution](/Substitution/) 章中导入的恒等替换等价。

```agda
≈ₑ-id : ∅' ≈ₑ ids
≈ₑ-id ()
```

<!--
Of course, applying the identity substitution to a term returns
the same term.
-->

显然，对项应用恒等替换会得到相同的项。

```agda
sub-id : ∀{Γ} {A} {M : Γ ⊢ A} → subst ids M ≡ M
sub-id = plfa.part2.Substitution.sub-id
```

<!--
We define an auxiliary function for extending a substitution.
-->

我们定义一个辅助函数来扩展替换。

```agda
ext-subst : ∀{Γ Δ} → Subst Γ Δ → Δ ⊢ ★ → Subst (Γ , ★) Δ
ext-subst{Γ}{Δ} σ N {A} = subst (subst-zero N) ∘ exts σ
```

<!--
The next lemma we need to prove states that if you start with an
equivalent environment and substitution `γ ≈ₑ σ`, extending them with
an equivalent closure and term `V ≈ N` produces an equivalent
environment and substitution: `(γ ,' V) ≈ₑ (ext-subst σ N)`,
or equivalently, `(γ ,' V) x ≈ (ext-subst σ N) x` for any
variable `x`. The proof will be by induction on `x` and
for the induction step we need the following lemma,
which states that applying the composition of `exts σ`
and `subst-zero` to `S x` is the same as just `σ x`,
which is a corollary of a theorem in
Chapter [Substitution](/Substitution/).
-->

下一个需要证明的引理声称如果从等价的环境和替换 `γ ≈ₑ σ` 开始，
将它们用等价的闭包和项 `c ≈ N` 扩展，
将得到等价的环境和替换 `(γ ,' V) ≈ₑ (ext-subst σ N)`，
即对于任何变量 `x` 有 `(γ ,' V) x ≈ₑ (ext-subst σ N) x`。
证明将通过归纳 `x` 完成，并且我们需要如下引理。
该引理声称将`exts σ` 和 `subst-zero` 的组合应用至 `S x` 等同于 `σ x`。
这是 [Substitution](/Substitution/) 章节中一个定理的推论。

```agda
subst-zero-exts : ∀{Γ Δ}{σ : Subst Γ Δ}{B}{M : Δ ⊢ B}{x : Γ ∋ ★}
  → (subst (subst-zero M) ∘ exts σ) (S x) ≡ σ x
subst-zero-exts {Γ}{Δ}{σ}{B}{M}{x} =
   cong-app (plfa.part2.Substitution.subst-zero-exts-cons{σ = σ}) (S x)
```

<!--
So the proof of `≈ₑ-ext` is as follows.
-->

所以 `≈ₑ-ext` 的证明如下。

```agda
≈ₑ-ext : ∀ {Γ} {γ : ClosEnv Γ} {σ : Subst Γ ∅} {V} {N : ∅ ⊢ ★}
  → γ ≈ₑ σ  →  V ≈ N
    --------------------------
  → (γ ,' V) ≈ₑ (ext-subst σ N)
≈ₑ-ext {Γ} {γ} {σ} {V} {N} γ≈ₑσ V≈N Z = V≈N
≈ₑ-ext {Γ} {γ} {σ} {V} {N} γ≈ₑσ V≈N (S x)
  rewrite subst-zero-exts {σ = σ}{M = N}{x} = γ≈ₑσ x
```

<!--
We proceed by induction on the input variable.
-->

我们通过对输入项进行归纳来证明。

<!--
* If it is `Z`, then we immediately conclude using the
  premise `V ≈ N`.

* If it is `S x`, then we rewrite using the
  `subst-zero-exts` lemma and use the premise `γ ≈ₑ σ`
  to conclude.
-->

* 如果它是 `Z`，那么我们使用前提 `V ≈ N` 立即得出结论。

* 如果它是 `S x`，那么我们使用 `subst-zero-exts` 引理来重写，并使用前提 `γ ≈ₑ σ` 来得出结论。


<!--
To prove the main lemma, we need another technical lemma about
substitution. Applying one substitution after another is the same as
composing the two substitutions and then applying them.
-->

为了证明主要的引理，我们需要另一个关于替换的技术性的引理。
接连应用两个替换与先将两个替换连接起来再应用等价。

```agda
sub-sub : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ}
  → subst σ₂ (subst σ₁ M) ≡ subst (subst σ₂ ∘ σ₁) M
sub-sub {M = M} = plfa.part2.Substitution.sub-sub {M = M}
```

<!--
We arrive at the main lemma: if `M` big steps to a
closure `V` in environment `γ`, and if `γ ≈ₑ σ`, then `subst σ M` reduces
to some term `N` that is equivalent to `V`. We describe the proof
below.
-->

我们到达了主要引理：如果 `M` 在环境 `γ` 中大步求值为闭包 `V`，并且 `γ ≈ₑ σ`，
那么 `subst σ M` 将归约为某个等价于 `V` 的项 `N`。我们如下叙述该证明。

```agda
⇓→—↠×≈ : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ ∅}{M : Γ ⊢ ★}{V : Clos}
       → γ ⊢ M ⇓ V  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ ∅ ⊢ ★ ] (subst σ M —↠ N) × V ≈ N
⇓→—↠×≈ {γ = γ} (⇓-var{x = x} γx≡Lδ δ⊢L⇓V) γ≈ₑσ
    with γ x | γ≈ₑσ x | γx≡Lδ
... | clos L δ | ⟨ τ , ⟨ δ≈ₑτ , σx≡τL ⟩ ⟩ | refl
      with ⇓→—↠×≈{σ = τ} δ⊢L⇓V δ≈ₑτ
...   | ⟨ N , ⟨ τL—↠N , V≈N ⟩ ⟩ rewrite σx≡τL =
        ⟨ N , ⟨ τL—↠N , V≈N ⟩ ⟩
⇓→—↠×≈ {σ = σ} {V = clos (ƛ N) γ} (⇓-lam) γ≈ₑσ =
    ⟨ subst σ (ƛ N) , ⟨ subst σ (ƛ N) ∎ , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×≈{Γ}{γ} {σ = σ} {L · M} {V} (⇓-app {N = N} L⇓ƛNδ N⇓V) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ _ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , ≡ƛτN ⟩ ⟩ ⟩ ⟩ rewrite ≡ƛτN
      with ⇓→—↠×≈ {σ = ext-subst τ (subst σ M)} N⇓V
             (λ x → ≈ₑ-ext{σ = τ} δ≈ₑτ ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ x)
           | β{∅}{subst (exts τ) N}{subst σ M}
...   | ⟨ N' , ⟨ —↠N' , V≈N' ⟩ ⟩ | ƛτN·σM—→
        rewrite sub-sub{M = N}{σ₁ = exts τ}{σ₂ = subst-zero (subst σ M)} =
        let rs = (ƛ subst (exts τ) N) · subst σ M —→⟨ ƛτN·σM—→ ⟩ —↠N' in
        let g = —↠-trans (appL-cong σL—↠ƛτN) rs in
        ⟨ N' , ⟨ g , V≈N' ⟩ ⟩
```

<!--
The proof is by induction on `γ ⊢ M ⇓ V`. We have three cases
to consider.
-->

该证明对 `γ ⊢ M ⇓ V` 进行归纳。我们有三种情况需要考虑。

<!--
* Case `⇓-var`.
  So we have `γ x ≡ clos L δ` and `δ ⊢ L ⇓ V`.
  We need to show that ``subst σ (` x) —↠ N`` and `V ≈ N` for some `N`.
  The premise `γ ≈ₑ σ` tells us that `γ x ≈ σ x`, so `clos L δ ≈ σ x`.
  By the definition of `≈`, there exists a `τ` such that
  `δ ≈ₑ τ` and `σ x ≡ subst τ L `.
  Using `δ ⊢ L ⇓ V` and `δ ≈ₑ τ`,
  the induction hypothesis gives us
  `subst τ L —↠ N` and `V ≈ N` for some `N`.
  So we have shown that `subst σ x —↠ N` and `V ≈ N` for some `N`.
-->

* 情况 `⇓-var`：
  此时我们有 `γ x ≡ clos L δ` 和 `δ ⊢ L ⇓ V`。
  我们需要证明对于某个 `N` 有`subst σ x —↠ N` 和 `V ≈ N`。
  前提 `γ ≈ₑ σ` 告诉我们 `γ x ≈ σ x`，所以有 `clos L δ ≈ σ x`。
  根据 `≈` 的定义， 存在一个 `τ` 使得 `δ ≈ₑ τ` 且 `σ x ≡ subst τ L `。
  使用 `δ ⊢ L ⇓ V` 和 `δ ≈ₑ τ`，
  归纳假设使得对于某个 `N` 有 `subst τ L —↠ N` 和 `V ≈ N`。
  所以我们证明了对于某个 `N`，有 `subst σ x —↠ N` 和 `V ≈ N`。

<!--
* Case `⇓-lam`.
  We immediately have `subst σ (ƛ N) —↠ subst σ (ƛ N)`
  and `clos (subst σ (ƛ N)) γ ≈ subst σ (ƛ N)`.
-->

* 情况 `⇓-lam`：
  我们立刻获得 `subst σ (ƛ N) —↠ subst σ (ƛ N)`
  和 `clos (subst σ (ƛ N)) γ ≈ subst σ (ƛ N)`。

<!--
* Case `⇓-app`.
  Using `γ ⊢ L ⇓ clos (ƛ N) δ` and `γ ≈ₑ σ`,
  the induction hypothesis gives us

        subst σ L —↠ ƛ subst (exts τ) N                                     (1)

  and `δ ≈ₑ τ` for some `τ`.
  From `γ≈ₑσ` we have `clos M γ ≈ subst σ M`.
  Then with `(δ ,' clos M γ) ⊢ N ⇓ V`,
  the induction hypothesis gives us `V ≈ N'` and

        subst (subst (subst-zero (subst σ M)) ∘ (exts τ)) N —↠ N'         (2)

  Meanwhile, by `β`, we have

        (ƛ subst (exts τ) N) · subst σ M
        —→ subst (subst-zero (subst σ M)) (subst (exts τ) N)

  which is the same as the following, by `sub-sub`.

        (ƛ subst (exts τ) N) · subst σ M
        —→ subst (subst (subst-zero (subst σ M)) ∘ exts τ) N              (3)

  Using (3) and (2) we have

        (ƛ subst (exts τ) N) · subst σ M —↠ N'                             (4)

  From (1) we have

        subst σ L · subst σ M —↠ (ƛ subst (exts τ) N) · subst σ M

  which we combine with (4) to conclude that

        subst σ L · subst σ M —↠ N'
-->

* 情况 `⇓-app`：
  使用 `γ ⊢ L ⇓ clos N δ` 和 `γ ≈ₑ σ`，
  归纳假设给我们

        subst σ L —↠ ƛ subst (exts τ) N                                     (1)

  并且对于某个 `τ` 有 `δ ≈ₑ τ`。
  根据 `γ≈ₑσ` 我们有 `clos M γ ≈ subst σ M`。
  与 `(δ ,' clos M γ) ⊢ N ⇓ V` 一同，
  归纳假设给我们 `V ≈ N'` 和

        subst (subst (subst-zero (subst σ M)) ∘ (exts τ)) N —↠ N'         (2)

  同时根据 `β`，我们有

        (ƛ subst (exts τ) N) · subst σ M
        —→ subst (subst-zero (subst σ M)) (subst (exts τ) N)

  通过 `sub-sub`，这等价于

        (ƛ subst (exts τ) N) · subst σ M
        —→ subst (subst (subst-zero (subst σ M)) ∘ exts τ) N              (3)

  使用 (3) 和 (2) 我们有

        (ƛ subst (exts τ) N) · subst σ M —↠ N'                             (4)

  根据 (1) 我们有

        subst σ L · subst σ M —↠ (ƛ subst (exts τ) N) · subst σ M

  与 (4) 相结合，我们得出结论

        subst σ L · subst σ M —↠ N'

<!--
With the main lemma complete, we establish the forward direction
of the equivalence between the big-step semantics and beta reduction.
-->

证明了主要引理后，我们便建立起大步语义与 β-归约等价关系的必要性。

```agda
cbn→reduce :  ∀{M : ∅ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N′ : Δ , ★ ⊢ ★}
  → ∅' ⊢ M ⇓ clos (ƛ N′) δ
    -----------------------------
  → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)
cbn→reduce {M}{Δ}{δ}{N′} M⇓c
    with ⇓→—↠×≈{σ = ids} M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩ rewrite sub-id{M = M} | eq2 =
      ⟨ subst (exts σ) N′ , rs ⟩
```

<!--
#### Exercise `big-alt-implies-multi` (practice)
-->

#### 练习 `big-alt-implies-multi`（实践）

<!--
Formulate an alternative big-step semantics, of the form `M ↓ N`, for
call-by-name that uses substitution instead of environments.  That is,
the analogue of the application rule `⇓-app` should perform
substitution, as in `N [ M ]`, instead of extending the environment
with `M`. Prove that `M ↓ N` implies `M —↠ N`.
-->

为使用替换而不是环境的传名调用表达另一种大步语义，形式为 `M ↓ N`。
即应用规则 `⇓-app` 应像在 `N [ M ]` 中一样执行替换而不是用 `M` 扩展环境。
证明 `M ↓ N` 蕴含 `M —↠ N`。



```agda
-- 请将代码写在此处
```

<!--
## Beta reduction to a lambda implies big-step evaluation
-->

## β-归约至 λ-抽象蕴含大步求值

<!--
The proof of the backward direction, that beta reduction to a lambda
implies that the call-by-name semantics produces a result, is more
difficult to prove. The difficulty stems from reduction proceeding
underneath lambda abstractions via the `ζ` rule. The call-by-name
semantics does not reduce under lambda, so a straightforward proof by
induction on the reduction sequence is impossible.  In the article
_Call-by-name, call-by-value, and the λ-calculus_, Plotkin proves the
theorem in two steps, using two auxiliary reduction relations. The
first step uses a classic technique called Curry-Feys standardisation.
It relies on the notion of _standard reduction sequence_, which acts
as a half-way point between full beta reduction and call-by-name by
expanding call-by-name to also include reduction underneath
lambda. Plotkin proves that `M` reduces to `L` if and only if `M` is
related to `L` by a standard reduction sequence.
-->

充分性的证明，也就是 β-归约至 λ-抽象蕴含大步语义求值是更困难的。
困难源于通过 `ζ` 规则在 λ-抽象下的归约过程。
传名调用语义在 λ-演算中并不会归约，因此直接通过归纳归约序列来证明是不可能的。
在文章 **Call-by-name, call-by-value, and the λ-calculus** 中，
Plotkin使用两个辅助归约关系分两步完成了证明。
第一步使用了 Curry-Feys 标准化这一经典方法，
它依赖于 **标准归约序列（Standard Reduction Sequence）** 的概念，
通过在 λ-演算下将传名调用扩展以包括归约，
标准归约序列充当了完整 β-归约与传名调用求值的中间点。
Plotkin证明了 `M` 能被归约为 `L` 当且仅当 `M` 与 `L` 通过一个标准归约序列相关。

<!--
    Theorem 1 (Standardisation)
    `M —↠ L` if and only if `M` goes to `L` via a standard reduction sequence.
-->

    定理 1（标准化）
    `M —↠ L` 当且仅当 `M` 能通过一个标准归约序列归约成 `L`。

<!--
Plotkin then introduces _left reduction_, a small-step version of
call-by-name and uses the above theorem to prove that beta reduction
and left reduction are equivalent in the following sense.
-->

Plotkin 接着引入了**左归约（Left Reduction）** 作为传名调用的小步描述，
并且用上方的定理证明了 β-归约与左归约在下述情况下等价。

<!--
    Corollary 1
    `M —↠ ƛ N` if and only if `M` goes to `ƛ N′`, for some `N′`, by left reduction.
-->

    推论 1
    `M —↠ ƛ N` 当且仅当对于某个 `N′`，`M`能通过左归约成 `ƛ N′`。

<!--
The second step of the proof connects left reduction to call-by-name
evaluation.
-->

证明的下一步将左归约与传名调用求值联系起来。

<!--
    Theorem 2
    `M` left reduces to `ƛ N` if and only if `⊢ M ⇓ ƛ N`。
-->

    定理 2
    `M` 左归约成 `ƛ N` 当且仅当 `⊢ M ⇓ ƛ N`。

<!--
(Plotkin's call-by-name evaluator uses substitution instead of
environments, which explains why the environment is omitted in `⊢ M ⇓
ƛ N` in the above theorem statement.)
-->

（Plotkin 的传名调用求值使用替换而不是环境，
这解释了为何在上文定理的描述中环境被隐去了。）

<!--
Putting Corollary 1 and Theorem 2 together, Plotkin proves that
call-by-name evaluation is equivalent to beta reduction.
-->

将推论 1 和定理 2 相结合，Plotkin 证明了传名调用求值与 β-归约等价。

<!--
    Corollary 2
    `M —↠ ƛ N` if and only if `⊢ M ⇓ ƛ N′` for some `N′`.
-->

    推论 2
    `M —↠ ƛ N` 当且仅当对某个 `N′`，`⊢ M ⇓ ƛ N′`。

<!--
Plotkin also proves an analogous result for the λᵥ calculus, relating
it to call-by-value evaluation. For a nice exposition of that proof,
we recommend Chapter 5 of _Semantics Engineering with PLT Redex_ by
Felleisen, Findler, and Flatt.
-->

Plotkin 还证明了 λᵥ-演算中的类似结果，将其与传值调用求值相联系。
为了更好阐述该证明，我们推荐阅读由 Felleisen、Findler 和 Flatt 所著的
_Semantics Engineering with PLT Redex_ 的第五章。

<!--
Instead of proving the backwards direction via standardisation, as
sketched above, we defer the proof until after we define a
denotational semantics for the lambda calculus, at which point the
proof of the backwards direction will fall out as a corollary to the
soundness and adequacy of the denotational semantics.
-->

我们不通过上文描述的标准化方式来完成充分性的证明，
而是将其推迟到发展出 λ-演算的指称语义后，
此时该证明是指称语义中 soundness 和 adequacy 的推论。

## Unicode

<!--
This chapter uses the following unicode:
-->

本章中使用了以下 Unicode：

    ≈  U+2248  ALMOST EQUAL TO (\~~ or \approx)
    ₑ  U+2091  LATIN SUBSCRIPT SMALL LETTER E (\_e)
    ⊢  U+22A2  RIGHT TACK (\|- or \vdash)
    ⇓  U+21DB  DOWNWARDS DOUBLE ARROW (\d= or \Downarrow)
