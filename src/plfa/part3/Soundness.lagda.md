---
title       : "Soundness: 指称语义归约的可靠性"
permalink   : /Soundness/
translators : ["OlingCat"]
---

```agda
module plfa.part3.Soundness where
```


<!--
## Introduction
-->

## 简介

<!--
In this chapter we prove that the reduction semantics is sound with
respect to the denotational semantics, i.e., for any term L
-->

本章中我们会证明指称语义的归约语义是可靠（Sound）的，即对于任意项 `L`：

    L —↠ ƛ N  蕴含  ℰ L ≃ ℰ (ƛ N)

<!--
The proof is by induction on the reduction sequence, so the main lemma
concerns a single reduction step. We prove that if any term `M` steps
to a term `N`, then `M` and `N` are denotationally equal. We shall
prove each direction of this if-and-only-if separately. One direction
will look just like a type preservation proof. The other direction is
like proving type preservation for reduction going in reverse.  Recall
that type preservation is sometimes called subject
reduction. Preservation in reverse is a well-known property and is
called _subject expansion_. It is also well-known that subject
expansion is false for most typed lambda calculi!
-->

证明可通过对归约序列进行归纳得出，因此主引理涉及单个归约步骤。
我们需要证明，如果任何项 `M` 步进到项 `N`，则 `M` 和 `M` 的指称相等。
我们将分别证明「当且仅当」的两个方向，一个方向类似于保型性（type preservation）的证明，
另一个方向类似于反向归约（即展开）的保型性证明。回想一下，
保型性有时称为主体归约（subject reduction）。
反向的保型性是一个众所周知的属性，称为 **主体展开（subject expansion）**。
众所周知，大多数类型化 λ-演算都不满足主体展开！
（译注：一个 subject 是形如 `(1*2+3) : Int` 这样已经确定类型的项。
大多数类型化 λ-演算会失去保型性的原因参见 https://www.bananaspace.org/wiki/%E7%B1%BB%E5%9E%8B%E4%B8%8D%E5%8F%98%E6%80%A7）


<!--
## Imports
-->

## 导入

```agda
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)
open import plfa.part2.Untyped
     using (Context; _,_; _∋_; _⊢_; ★; Z; S_; `_; ƛ_; _·_;
            subst; _[_]; subst-zero; ext; rename; exts;
            _—→_; ξ₁; ξ₂; β; ζ; _—↠_; _—→⟨_⟩_; _∎)
open import plfa.part2.Substitution using (Rename; Subst; ids)
open import plfa.part3.Denotational
     using (Value; ⊥; Env; _⊢_↓_; _`,_; _⊑_; _`⊑_; `⊥; _`⊔_; init; last; init-last;
            ⊑-refl; ⊑-trans; `⊑-refl; ⊑-env; ⊑-env-conj-R1; ⊑-env-conj-R2; up-env;
            var; ↦-elim; ↦-intro; ⊥-intro; ⊔-intro; sub;
            rename-pres; ℰ; _≃_; ≃-trans)
open import plfa.part3.Compositional using (lambda-inversion; var-inv)
```

<!--
## Forward reduction preserves denotations
-->

## 向前归约保持指称不变

<!--
The proof of preservation in this section mixes techniques from
previous chapters. Like the proof of preservation for the STLC, we are
preserving a relation defined separately from the syntax, in contrast
to the intrinsically-typed terms. On the other hand, we are using de
Bruijn indices for variables.
-->

本节中对指称不变性的证明使用了前一章中的技术。和 STLC
的不变性证明一样，我们保留了独立于语法定义的关系，这与内在类型项相反。
另一方面，我们对变量使用了 de Bruijn 索引。

<!--
The outline of the proof remains the same in that we must prove lemmas
concerning all of the auxiliary functions used in the reduction
relation: substitution, renaming, and extension.
-->

证明的大纲保持不变，因为我们必须证明归约关系中使用的所有辅助函数的引理：
代换、重命名和扩展。


<!--
### Simultaneous substitution preserves denotations
-->

### 同时代换保持指称不变

<!--
Our next goal is to prove that simultaneous substitution preserves
meaning.  That is, if `M` results in `v` in environment `γ`, then applying a
substitution `σ` to `M` gives us a program that also results in `v`, but in
an environment `δ` in which, for every variable `x`, `σ x` results in the
same value as the one for `x` in the original environment `γ`.
We write `` δ `⊢ σ ↓ γ `` for this condition.
-->

我们接下来的目标是证明同时代换变量和环境会保持含义不变。也就是说，若 `M`
在环境 `γ` 中的结果是 `v`，那么代换 `σ` 应用到 `M` 所得的程序，其结果仍然是 `v`，
但环境转移到了 `δ` 中。该环境中对于每一个变量 `x`，`σ x` 产生的结果值与原始环境
`γ` 中的 `x` 的值相同。我们将这种情况写作 `` δ `⊢ σ ↓ γ ``。

```agda
infix 3 _`⊢_↓_
_`⊢_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
_`⊢_↓_ {Δ}{Γ} δ σ γ = (∀ (x : Γ ∋ ★) → δ ⊢ σ x ↓ γ x)
```

<!--
As usual, to prepare for lambda abstraction, we prove an extension
lemma. It says that applying the `exts` function to a substitution
produces a new substitution that maps variables to terms that when
evaluated in `δ , v` produce the values in `γ , v`.
-->

和之前一样，为了证明 λ-抽象，我们需要证明一个扩展引理，
该引理说明了将 `exts` 函数应用于代换会产生一个新的代换，该代换将变量映射到项，
使得当对 `δ , v` 求值时会产生 `γ , v` 中的值。

```agda
subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (σ : Subst Γ Δ)
  → δ `⊢ σ ↓ γ
   --------------------------
  → δ `, v `⊢ exts σ ↓ γ `, v
subst-ext σ d Z = var
subst-ext σ d (S x′) = rename-pres S_ (λ _ → ⊑-refl) (d x′)
```

<!--
The proof is by cases on the de Bruijn index `x`.

* If it is `Z`, then we need to show that `δ , v ⊢ # 0 ↓ v`,
  which we have by rule `var`.

* If it is `S x′`,then we need to show that
  `δ , v ⊢ rename S_ (σ x′) ↓ γ x′`,
  which we obtain by the `rename-pres` lemma.
-->

该证明通过对 de Bruijn 索引 `x` 进行情况分析来论证：

* 若索引为 `Z`，那么我们需要证明 `δ , v ⊢ # 0 ↓ v`，
  它可通过规则 `var` 得证。

* 若索引为 `S x′` 那么我们需要证明
  `δ , v ⊢ rename S_ (σ x′) ↓ γ x′`，
  它可通过 `rename-pres` 引理证明。

<!--
With the extension lemma in hand, the proof that simultaneous
substitution preserves meaning is straightforward.  Let's dive in!
-->

有了这个扩展引理，同时代换会保留含义的证明就很直白了，我们继续深入：

```agda
subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (σ : Subst Γ Δ)
  → δ `⊢ σ ↓ γ
  → γ ⊢ M ↓ v
    ------------------
  → δ ⊢ subst σ M ↓ v
subst-pres σ s (var {x = x}) = s x
subst-pres σ s (↦-elim d₁ d₂) =
  ↦-elim (subst-pres σ s d₁) (subst-pres σ s d₂)
subst-pres σ s (↦-intro d) =
  ↦-intro (subst-pres (λ {A} → exts σ) (subst-ext σ s) d)
subst-pres σ s ⊥-intro = ⊥-intro
subst-pres σ s (⊔-intro d₁ d₂) =
  ⊔-intro (subst-pres σ s d₁) (subst-pres σ s d₂)
subst-pres σ s (sub d lt) = sub (subst-pres σ s d) lt
```

<!--
The proof is by induction on the semantics of `M`.  The two interesting
cases are for variables and lambda abstractions.

* For a variable `x`, we have that `v = γ x` and we need to show that
  `δ ⊢ σ x ↓ v`.  From the premise applied to `x`, we have that
  `δ ⊢ σ x ↓ γ x` aka `δ ⊢ σ x ↓ v`.

* For a lambda abstraction, we must extend the substitution
  for the induction hypothesis. We apply the `subst-ext` lemma
  to show that the extended substitution maps variables to
  terms that result in the appropriate values.
-->

我们通过对 `M` 的语义进行归纳来证明。两个有趣的情况分别对应于变量和
λ-抽象：

* 对于变量 `x`，我们有 `v = γ x`，于是需要证明 `δ ⊢ σ x ↓ v`。
  将前提应用到 `x`，我们有 `δ ⊢ σ x ↓ γ x`，即 `δ ⊢ σ x ↓ v`.

* 对于 λ-抽象，我们必须为归纳假设扩展代换。应用 `subst-ext` 引理可证明
  扩展的代换会将变量映射到产生对应值的项。


<!--
### Single substitution preserves denotations
-->

### 单一代换保持指称不变

<!--
For β reduction, `(ƛ N) · M —→ N [ M ]`, we need to show that the
semantics is preserved when substituting `M` for de Bruijn index 0 in
term `N`. By inversion on the rules `↦-elim` and `↦-intro`,
we have that `γ , v ⊢ M ↓ w` and `γ ⊢ N ↓ v`.
So we need to show that `γ ⊢ M [ N ] ↓ w`, or equivalently,
that `γ ⊢ subst (subst-zero N) M ↓ w`.
-->

对于 β-规约 `(ƛ N) · M —→ N [ M ]`，我们需要证明当用 `M` 代换项 `N`
中的 de Bruijn 索引 0 时，语义保持不变。通过对规则 `↦-elim` 和 `↦-intro`
进行反演，我们可得到 `γ , v ⊢ M ↓ w` 和 `γ ⊢ N ↓ v`。因此，我们需要证明
`γ ⊢ M [ N ] ↓ w`，或等价地证明 `γ ⊢ subst (subst-zero N) M ↓ w`。

```agda
substitution : ∀ {Γ} {γ : Env Γ} {N M v w}
   → γ `, v ⊢ N ↓ w
   → γ ⊢ M ↓ v
     ---------------
   → γ ⊢ N [ M ] ↓ w
substitution{Γ}{γ}{N}{M}{v}{w} dn dm =
  subst-pres (subst-zero M) sub-z-ok dn
  where
  sub-z-ok : γ `⊢ subst-zero M ↓ (γ `, v)
  sub-z-ok Z = dm
  sub-z-ok (S x) = var
```

<!--
This result is a corollary of the lemma for simultaneous substitution.
To use the lemma, we just need to show that `subst-zero M` maps
variables to terms that produces the same values as those in `γ , v`.
Let `y` be an arbitrary variable (de Bruijn index).

* If it is `Z`, then `(subst-zero M) y = M` and `(γ , v) y = v`.
  By the premise we conclude that `γ ⊢ M ↓ v`.

* If it is `S x`, then `(subst-zero M) (S x) = x` and
  `(γ , v) (S x) = γ x`.  So we conclude that
  `γ ⊢ x ↓ γ x` by rule `var`.
-->

这个结果是同时代换引理的推论。要使用该引理，我们只需要证明 `subst-zero M`
会将变量映射到某个项，该项产生的值与 `γ , v` 中产生的值相同。令 `y`
为任意变量（即 de Bruijn 索引）：

* 若索引为 `Z`，则 `(subst-zero M) y = M` 且 `(γ , v) y = v`，
  根据前提可得 `γ ⊢ M ↓ v`。

* 若索引为 `S x`，则 `(subst-zero M) (S x) = x` 且 `(γ , v) (S x) = γ x`，
  根据规则 `var` 可得 `γ ⊢ x ↓ γ x`。


<!--
### Reduction preserves denotations
-->

### 归约保持指称不变

<!--
With the substitution lemma in hand, it is straightforward to prove
that reduction preserves denotations.
-->

有了代换引理，就能直接证明归约保持指称不变：

```agda
preserve : ∀ {Γ} {γ : Env Γ} {M N v}
  → γ ⊢ M ↓ v
  → M —→ N
    ----------
  → γ ⊢ N ↓ v
preserve (var) ()
preserve (↦-elim d₁ d₂) (ξ₁ r) = ↦-elim (preserve d₁ r) d₂
preserve (↦-elim d₁ d₂) (ξ₂ r) = ↦-elim d₁ (preserve d₂ r)
preserve (↦-elim d₁ d₂) β = substitution (lambda-inversion d₁) d₂
preserve (↦-intro d) (ζ r) = ↦-intro (preserve d r)
preserve ⊥-intro r = ⊥-intro
preserve (⊔-intro d d₁) r = ⊔-intro (preserve d r) (preserve d₁ r)
preserve (sub d lt) r = sub (preserve d r) lt
```

<!--
We proceed by induction on the semantics of `M` with case analysis on
the reduction.

* If `M` is a variable, then there is no such reduction.

* If `M` is an application, then the reduction is either a congruence
  (ξ₁ or ξ₂) or β. For each congruence, we use the induction
  hypothesis. For β reduction we use the substitution lemma and the
  `sub` rule.

* The rest of the cases are straightforward.
-->

我们通过对 `M` 的语义进行归纳，并对归约进行情况分析来证明：

* 若 `M` 为变量，则无需归约。

* 若 `M` 为应用，则归约要么满足合同性（ξ₁ 或 ξ₂），要么是 β-归约。
  对于每一种合同性，我们使用归纳假设。对于 β-归约，我们使用代换引理和 `sub` 规则。

* 其余的情况都很直接。

<!--
## Reduction reflects denotations
-->

## 归约反映了指称不变

<!--
This section proves that reduction reflects the denotation of a
term. That is, if `N` results in `v`, and if `M` reduces to `N`, then
`M` also results in `v`. While there are some broad similarities
between this proof and the above proof of semantic preservation, we
shall require a few more technical lemmas to obtain this result.
-->

本节中将证明归约反映了项的指称不变，换言之，若 `N` 的结果是 `v`，且若 `M`
可归约为 `N`，则 `M` 的结果也是 `v`。虽然此证明和前面的语义保持不变的证明
之间存在一些广泛的相似之处，但我们仍需更多的技术引理才能得到这个结果。

<!--
The main challenge is dealing with the substitution in β reduction:
-->

最主要挑战是处理 β-归约中的代换：

    (ƛ N) · M —→ N [ M ]

<!--
We have that `γ ⊢ N [ M ] ↓ v` and need to show that
`γ ⊢ (ƛ N) · M ↓ v`. Now consider the derivation of `γ ⊢ N [ M ] ↓ v`.
The term `M` may occur 0, 1, or many times inside `N [ M ]`. At each of
those occurrences, `M` may result in a different value. But to build a
derivation for `(ƛ N) · M`, we need a single value for `M`.  If `M`
occurred more than 1 time, then we can join all of the different values
using `⊔`. If `M` occurred 0 times, then we do not need any information
about `M` and can therefore use `⊥` for the value of `M`.
-->

我们有 `γ ⊢ N [ M ] ↓ v` 且需要证明 `γ ⊢ (ƛ N) · M ↓ v`。现在考虑
`γ ⊢ N [ M ] ↓ v` 的推导过程。项 `M` 在 `N [ M ]` 中可能会出现 0、1 或多次。
对于它可能出现的任意次数，`M` 都可能产生不同的值。不过为了构建出 `(ƛ N) · M`
的推导过程，我们需要单个的 `M` 值。若 `M` 出现了超过 1 次，那么我们就能将不同的值用
`⊔` 连接到一起。若 `M` 出现了 0 次，那么我们就无需任何关于 `M` 的信息，
并直接使用 `⊥` 作为 `M` 的值。


<!--
### Renaming reflects meaning
-->

### 重命名反映了含义不变

<!--
Previously we showed that renaming variables preserves meaning.  Now
we prove the opposite, that it reflects meaning. That is,
if `δ ⊢ rename ρ M ↓ v`, then `γ ⊢ M ↓ v`, where `(δ ∘ ρ) `⊑ γ`.
-->

前面我们证明了重命名变量会保持含义不变。现在我们证明它的反面，即重命名反映了含义不变。
也就是说，若 `δ ⊢ rename ρ M ↓ v` 则 `γ ⊢ M ↓ v`，其中 ``(δ ∘ ρ) `⊑ γ``.

<!--
First, we need a variant of a lemma given earlier.
-->

首先，我们需要一个前面给出的引理的变体：

```agda
ext-`⊑ : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (ρ : Rename Γ Δ)
  → (δ ∘ ρ) `⊑ γ
    ------------------------------
  → ((δ `, v) ∘ ext ρ) `⊑ (γ `, v)
ext-`⊑ ρ lt Z = ⊑-refl
ext-`⊑ ρ lt (S x) = lt x
```

<!--
The proof is then as follows.
-->

然后证明如下：

```agda
rename-reflect : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} { M : Γ ⊢ ★}
  → {ρ : Rename Γ Δ}
  → (δ ∘ ρ) `⊑ γ
  → δ ⊢ rename ρ M ↓ v
    ------------------------------------
  → γ ⊢ M ↓ v
rename-reflect {M = ` x} all-n d with var-inv d
... | lt =  sub var (⊑-trans lt (all-n x))
rename-reflect {M = ƛ N}{ρ = ρ} all-n (↦-intro d) =
   ↦-intro (rename-reflect (ext-`⊑ ρ all-n) d)
rename-reflect {M = ƛ N} all-n ⊥-intro = ⊥-intro
rename-reflect {M = ƛ N} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-reflect all-n d₁) (rename-reflect all-n d₂)
rename-reflect {M = ƛ N} all-n (sub d₁ lt) =
   sub (rename-reflect all-n d₁) lt
rename-reflect {M = L · M} all-n (↦-elim d₁ d₂) =
   ↦-elim (rename-reflect all-n d₁) (rename-reflect all-n d₂)
rename-reflect {M = L · M} all-n ⊥-intro = ⊥-intro
rename-reflect {M = L · M} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-reflect all-n d₁) (rename-reflect all-n d₂)
rename-reflect {M = L · M} all-n (sub d₁ lt) =
   sub (rename-reflect all-n d₁) lt
```

<!--
We cannot prove this lemma by induction on the derivation of
`δ ⊢ rename ρ M ↓ v`, so instead we proceed by induction on `M`.

* If it is a variable, we apply the inversion lemma to obtain
  that `v ⊑ δ (ρ x)`. Instantiating the premise to `x` we have
  `δ (ρ x) ⊑ γ x`, so we conclude by the `var` rule.

* If it is a lambda abstraction `ƛ N`, we have
  rename `ρ (ƛ N) = ƛ (rename (ext ρ) N)`.
  We proceed by cases on `δ ⊢ ƛ (rename (ext ρ) N) ↓ v`.

  * Rule `↦-intro`: To satisfy the premise of the induction
    hypothesis, we prove that the renaming can be extended to be a
    mapping from `γ , v` to `δ , v`.

  * Rule `⊥-intro`: We simply apply `⊥-intro`.

  * Rule `⊔-intro`: We apply the induction hypotheses and `⊔-intro`.

  * Rule `sub`: We apply the induction hypothesis and `sub`.

* If it is an application `L · M`, we have
  `rename ρ (L · M) = (rename ρ L) · (rename ρ M)`.
  We proceed by cases on `δ ⊢ (rename ρ L) · (rename ρ M) ↓ v`
  and all the cases are straightforward.
-->

我们无法通过对 `δ ⊢ rename ρ M ↓ v` 的推导过程进行归纳来证明此引理，
因此，我们转而通过对 `M` 进行归纳来证明：

* 若它是一个变量，我们可通过对它应用反演引理得到 `v ⊑ δ (ρ x)`。
  将前提实例化为 `x`，我们有 `δ (ρ x) ⊑ γ x`，于是我们可通过 `var` 规则证明。

* 若它是一个 λ-抽象 `ƛ N`，我们有重命名 `ρ (ƛ N) = ƛ (rename (ext ρ) N)`。
  可通过对 `δ ⊢ ƛ (rename (ext ρ) N) ↓ v` 进行情况分析来论证：

  * 规则 `↦-intro`：为了满足归纳假设的前提，我们证明了重命名可扩展为从
    `γ , v` 到 `δ , v` 的映射。

  * 规则 `⊥-intro`：直接应用 `⊥-intro`。

  * 规则 `⊔-intro`：应用归纳假设和 `⊔-intro`。

  * 规则 `sub`：应用归纳假设和 `sub`。

* 若它是一个应用 `L · M`，我们有 `rename ρ (L · M) = (rename ρ L) · (rename ρ M)`，
  于是可通过对 `δ ⊢ (rename ρ L) · (rename ρ M) ↓ v` 进行情况分析来论证，
  而所有的情况都很直白。

<!--
In the upcoming uses of `rename-reflect`, the renaming will always be
the increment function. So we prove a corollary for that special case.
-->

在以后使用 `rename-reflect` 的情况中，重命名始终都是增量函数，
于是我们先在这里为这些特殊情况证明以下推论。

```agda
rename-inc-reflect : ∀ {Γ v′ v} {γ : Env Γ} { M : Γ ⊢ ★}
  → (γ `, v′) ⊢ rename S_ M ↓ v
    ----------------------------
  → γ ⊢ M ↓ v
rename-inc-reflect d = rename-reflect `⊑-refl d
```


<!--
### Substitution reflects denotations, the variable case
-->

### 代换反映了指称不变：变量的情况

<!--
We are almost ready to begin proving that simultaneous substitution
reflects denotations. That is, if `γ ⊢ (subst σ M) ↓ v`, then
`γ ⊢ σ k ↓ δ k` and `δ ⊢ M ↓ v` for any `k` and some `δ`.
We shall start with the case in which `M` is a variable `x`.
So instead the premise is `γ ⊢ σ x ↓ v` and we need to show that
`` δ ⊢ ` x ↓ v `` for some `δ`. The `δ` that we choose shall be the
environment that maps `x` to `v` and every other variable to `⊥`.
-->

我们基本上准备好证明同时代换反映指称不变了，也就是说，若
`γ ⊢ (subst σ M) ↓ v`，则对于任意 `k` 和某些 `δ`，有 `γ ⊢ σ k ↓ δ k`
且 `δ ⊢ M ↓ v`。我们首先从 `M` 是一个变量 `x` 的情况开始，
已知前提是 `γ ⊢ σ x ↓ v`，我们需要证明对于某个 `δ`，有 `` δ ⊢ ` x ↓ v ``。
我们选择的环境 `δ` 应当将 `x` 映射到 `v`，将任何其他变量映射到 `⊥`。

<!--
Next we define the environment that maps `x` to `v` and every other
variable to `⊥`, that is `const-env x v`. To tell variables apart, we
define the following function for deciding equality of variables.
-->

接下来我们定义将 `x` 映射到 `v`，将其他变量映射到 `⊥` 的环境，即
`const-env x v`。为了区分变量，我们定义以下函数来确定变量的相等性：

```agda
_var≟_ : ∀ {Γ} → (x y : Γ ∋ ★) → Dec (x ≡ y)
Z var≟ Z  =  yes refl
Z var≟ (S _)  =  no λ()
(S _) var≟ Z  =  no λ()
(S x) var≟ (S y) with  x var≟ y
...                 |  yes refl =  yes refl
...                 |  no neq   =  no λ{refl → neq refl}

var≟-refl : ∀ {Γ} (x : Γ ∋ ★) → (x var≟ x) ≡ yes refl
var≟-refl Z = refl
var≟-refl (S x) rewrite var≟-refl x = refl
```

<!--
Now we use `var≟` to define `const-env`.
-->

接着我们用 `var≟` 来定义 `const-env`：

```agda
const-env : ∀{Γ} → (x : Γ ∋ ★) → Value → Env Γ
const-env x v y with x var≟ y
...             | yes _       = v
...             | no _        = ⊥
```

<!--
Of course, `const-env x v` maps `x` to value `v`
-->
当然，`const-env x v` 将 `x` 映射到值 `v`：

```agda
same-const-env : ∀{Γ} {x : Γ ∋ ★} {v} → (const-env x v) x ≡ v
same-const-env {x = x} rewrite var≟-refl x = refl
```

<!--
and `const-env x v` maps `y` to `⊥, so long as `x ≢ y`.
-->

以及 `const-env x v` 将 `y` 映射到 `⊥`，且 `x ≢ y`。

```agda
diff-const-env : ∀{Γ} {x y : Γ ∋ ★} {v}
  → x ≢ y
    -------------------
  → const-env x v y ≡ ⊥
diff-const-env {Γ} {x} {y} neq with x var≟ y
...  | yes eq  =  ⊥-elim (neq eq)
...  | no _    =  refl
```

<!--
So we choose `const-env x v` for `δ` and obtain `` δ ⊢ ` x ↓ v ``
with the `var` rule.
-->

于是我们为 `δ` 选择 `const-env x v` 并通过 `var` 规则得到了 `` δ ⊢ ` x ↓ v ``。

<!--
It remains to prove that `` γ `⊢ σ ↓ δ `` and `δ ⊢ M ↓ v` for any `k`, given that
we have chosen `const-env x v` for `δ`.  We shall have two cases to
consider, `x ≡ y` or `x ≢ y`.
-->

剩下的就是证明 `` γ `⊢ σ ↓ δ ``，以及对于任意 `k` 有 `δ ⊢ M ↓ v`，据此我们
就能为 `δ` 选择 `const-env x v`。我们有两种情况需要考虑：`x ≡ y` 或 `x ≢ y`。

<!--
Now to finish the two cases of the proof.

* In the case where `x ≡ y`, we need to show
  that `γ ⊢ σ y ↓ v`, but that's just our premise.
* In the case where `x ≢ y,` we need to show
  that `γ ⊢ σ y ↓ ⊥`, which we do via rule `⊥-intro`.
-->

现在完成该证明的两种情况：

* 对于 `x ≡ y` 的情况，我们需要证明 `γ ⊢ σ y ↓ v`，不过这就是我们的前提。
* 对于 `x ≢ y,` 的情况， we need to show
  that `γ ⊢ σ y ↓ ⊥`, which we do via rule `⊥-intro`.

<!--
Thus, we have completed the variable case of the proof that
simultaneous substitution reflects denotations.  Here is the proof
again, formally.
-->

这样，我们就完成了同时代换反映指称不变的证明中变量的情况。
以下是正式的证明：

```agda
subst-reflect-var : ∀ {Γ Δ} {γ : Env Δ} {x : Γ ∋ ★} {v} {σ : Subst Γ Δ}
  → γ ⊢ σ x ↓ v
    -----------------------------------------
  → Σ[ δ ∈ Env Γ ] γ `⊢ σ ↓ δ  ×  δ ⊢ ` x ↓ v
subst-reflect-var {Γ}{Δ}{γ}{x}{v}{σ} xv
  rewrite sym (same-const-env {Γ}{x}{v}) =
    ⟨ const-env x v , ⟨ const-env-ok , var ⟩ ⟩
  where
  const-env-ok : γ `⊢ σ ↓ const-env x v
  const-env-ok y with x var≟ y
  ... | yes x≡y rewrite sym x≡y | same-const-env {Γ}{x}{v} = xv
  ... | no x≢y rewrite diff-const-env {Γ}{x}{y}{v} x≢y = ⊥-intro
```


<!--
### Substitutions and environment construction
-->

### 代换与环境的构造

<!--
Every substitution produces terms that can evaluate to `⊥`.
-->

每一个代换都能产生可求值为 `⊥` 的项。

```agda
subst-⊥ : ∀{Γ Δ}{γ : Env Δ}{σ : Subst Γ Δ}
    -----------------
  → γ `⊢ σ ↓ `⊥
subst-⊥ x = ⊥-intro
```

<!--
If a substitution produces terms that evaluate to the values in
both `γ₁` and `γ₂`, then those terms also evaluate to the values in
`γ₁ ⊔ γ₂`.
-->

若代换产生的项的求值结果为 `γ₁` 或 `γ₂` 中的值，那么这些项的求值结果也是
`γ₁ ⊔ γ₂` 中的值。

```agda
subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
           → γ `⊢ σ ↓ γ₁
           → γ `⊢ σ ↓ γ₂
             -------------------------
           → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
subst-⊔ γ₁-ok γ₂-ok x = ⊔-intro (γ₁-ok x) (γ₂-ok x)
```

<!--
### The Lambda constructor is injective
-->

### λ 构造子是单射的

```agda
lambda-inj : ∀ {Γ} {M N : Γ , ★ ⊢ ★ }
  → _≡_ {A = Γ ⊢ ★} (ƛ M) (ƛ N)
    ---------------------------
  → M ≡ N
lambda-inj refl = refl
```

<!--
### Simultaneous substitution reflects denotations
-->

### 同时代换反映了指称相等

<!--
In this section we prove a central lemma, that
substitution reflects denotations. That is, if `γ ⊢ subst σ M ↓ v`, then
`δ ⊢ M ↓ v` and `` γ `⊢ σ ↓ δ `` for some `δ`. We shall proceed by induction on
the derivation of `γ ⊢ subst σ M ↓ v`. This requires a minor
restatement of the lemma, changing the premise to `γ ⊢ L ↓ v` and
`L ≡ subst σ M`.
-->

本节中我们要证明一个核心引理，即代换反映了指称不变。也就是说，若
`γ ⊢ subst σ M ↓ v`，则 `δ ⊢ M ↓ v` 且对于某个 `δ` 有 `` γ `⊢ σ ↓ δ ``。
我们通过对 `γ ⊢ subst σ M ↓ v` 的推导过程进行归纳来证明，
为此需要稍微重述一下该引理，将前提更改为 `γ ⊢ L ↓ v` 和 `L ≡ subst σ M`。

```agda
split : ∀ {Γ} {M : Γ , ★ ⊢ ★} {δ : Env (Γ , ★)} {v}
  → δ ⊢ M ↓ v
    --------------------------
  → (init δ `, last δ) ⊢ M ↓ v
split {δ = δ} δMv rewrite init-last δ = δMv

subst-reflect : ∀ {Γ Δ} {δ : Env Δ} {M : Γ ⊢ ★} {v} {L : Δ ⊢ ★} {σ : Subst Γ Δ}
  → δ ⊢ L ↓ v
  → subst σ M ≡ L
    ---------------------------------------
  → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  γ ⊢ M ↓ v

subst-reflect {M = M}{σ = σ} (var {x = y}) eqL with M
... | ` x  with var {x = y}
...           | yv  rewrite sym eqL = subst-reflect-var {σ = σ} yv
subst-reflect {M = M} (var {x = y}) () | M₁ · M₂
subst-reflect {M = M} (var {x = y}) () | ƛ M′

subst-reflect {M = M}{σ = σ} (↦-elim d₁ d₂) eqL
         with M
...    | ` x with ↦-elim d₁ d₂
...    | d′ rewrite sym eqL = subst-reflect-var {σ = σ} d′
subst-reflect (↦-elim d₁ d₂) () | ƛ M′
subst-reflect{Γ}{Δ}{γ}{σ = σ} (↦-elim d₁ d₂)
   refl | M₁ · M₂
     with subst-reflect {M = M₁} d₁ refl | subst-reflect {M = M₂} d₂ refl
...     | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ↦-elim (⊑-env m1 (⊑-env-conj-R1 δ₁ δ₂))
                           (⊑-env m2 (⊑-env-conj-R2 δ₁ δ₂)) ⟩ ⟩

subst-reflect {M = M}{σ = σ} (↦-intro d) eqL with M
...    | ` x with (↦-intro d)
...             | d′ rewrite sym eqL = subst-reflect-var {σ = σ} d′
subst-reflect {σ = σ} (↦-intro d) eq | ƛ M′
      with subst-reflect {σ = exts σ} d (lambda-inj eq)
... | ⟨ δ′ , ⟨ exts-σ-δ′ , m′ ⟩ ⟩ =
    ⟨ init δ′ , ⟨ ((λ x → rename-inc-reflect (exts-σ-δ′ (S x)))) ,
             ↦-intro (up-env (split m′) (var-inv (exts-σ-δ′ Z))) ⟩ ⟩
subst-reflect (↦-intro d) () | M₁ · M₂

subst-reflect {σ = σ} ⊥-intro eq =
    ⟨ `⊥ , ⟨ subst-⊥ {σ = σ} , ⊥-intro ⟩ ⟩

subst-reflect {σ = σ} (⊔-intro d₁ d₂) eq
  with subst-reflect {σ = σ} d₁ eq | subst-reflect {σ = σ} d₂ eq
... | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ⊔-intro (⊑-env m1 (⊑-env-conj-R1 δ₁ δ₂))
                            (⊑-env m2 (⊑-env-conj-R2 δ₁ δ₂)) ⟩ ⟩
subst-reflect (sub d lt) eq
    with subst-reflect d eq
... | ⟨ δ , ⟨ subst-δ , m ⟩ ⟩ = ⟨ δ , ⟨ subst-δ , sub m lt ⟩ ⟩
```

<!--
* Case `var`: We have subst `σ M ≡ y`, so `M` must also be a variable, say `x`.
  We apply the lemma `subst-reflect-var` to conclude.
-->

* 情况 `var`：我们有 `subst σ M ≡ y`，因此 `M` 也必须是一个变量，称为 `x`。
  我们应用引理 `subst-reflect-var` 得出结论。

<!--
* Case `↦-elim`: We have `subst σ M ≡ L₁ · L₂`. We proceed by cases on `M`.
  * Case `` M ≡ ` x ``: We apply the `subst-reflect-var` lemma again to conclude.

  * Case `M ≡ M₁ · M₂`: By the induction hypothesis, we have
    some `δ₁` and `δ₂` such that `δ₁ ⊢ M₁ ↓ v₁ ↦ v₃` and `` γ `⊢ σ ↓ δ₁ ``,
    as well as `δ₂ ⊢ M₂ ↓ v₁` and `` γ `⊢ σ ↓ δ₂ ``.
    By `⊑-env` we have `δ₁ ⊔ δ₂ ⊢ M₁ ↓ v₁ ↦ v₃` and `δ₁ ⊔ δ₂ ⊢ M₂ ↓ v₁`
    (using `⊑-env-conj-R1` and `⊑-env-conj-R2`), and therefore
    `δ₁ ⊔ δ₂ ⊢ M₁ · M₂ ↓ v₃`.
    We conclude this case by obtaining `` γ `⊢ σ ↓ δ₁ ⊔ δ₂ ``
    by the `subst-⊔` lemma.
-->

* 情况 `↦-elim`：我们有 `subst σ M ≡ L₁ · L₂`，需要对 `M` 进行情况分析：
  * 情况 `` M ≡ ` x ``：我们再次应用 `subst-reflect-var` 得出结论。

  * 情况 `M ≡ M₁ · M₂`：根据归纳假设，我们有某个 `δ₁` 和 `δ₂` 使得
    `δ₁ ⊢ M₁ ↓ v₁ ↦ v₃` 和 `` γ `⊢ σ ↓ δ₁ ``，以及 `δ₂ ⊢ M₂ ↓ v₁`
    和 `` γ `⊢ σ ↓ δ₂ ``。
    根据 `⊑-env` 我们有 `δ₁ ⊔ δ₂ ⊢ M₁ ↓ v₁ ↦ v₃` 和 `δ₁ ⊔ δ₂ ⊢ M₂ ↓ v₁`
    （使用 `⊑-env-conj-R1` 和 `⊑-env-conj-R2` 得出），因此 `δ₁ ⊔ δ₂ ⊢ M₁ · M₂ ↓ v₃`。
    我们通过 `subst-⊔` 引理得出 `` γ `⊢ σ ↓ δ₁ ⊔ δ₂ `` 从而证明此情况。

<!--
* Case `↦-intro`: We have `subst σ M ≡ ƛ L′`. We proceed by cases on `M`.
  * Case `M ≡ x`: We apply the `subst-reflect-var` lemma.

  * Case `M ≡ ƛ M′`: By the induction hypothesis, we have
    `(δ′ , v′) ⊢ M′ ↓ v₂` and `(δ , v₁) ⊢ exts σ ↓ (δ′ , v′)`.
    From the later we have `(δ , v₁) ⊢ # 0 ↓ v′`.
    By the lemma `var-inv` we have `v′ ⊑ v₁`, so by the `up-env` lemma we
    have `(δ′ , v₁) ⊢ M′ ↓ v₂` and therefore `δ′ ⊢ ƛ M′ ↓ v₁ → v₂`.  We
    also need to show that `δ ⊢ σ ↓ δ′`.  Fix `k`. We have
    `(δ , v₁) ⊢ rename S_ σ k ↓ δ k′`.  We then apply the lemma
    `rename-inc-reflect` to obtain `δ ⊢ σ k ↓ δ k′`, so this case is
    complete.
-->

* 情况 `↦-intro`：我们有 `subst σ M ≡ ƛ L′`，需要对 `M` 进行情况分析：
  * 情况 `M ≡ x`：我们应用 `subst-reflect-var` 引理。

  * 情况 `M ≡ ƛ M′`：根据归纳假设，我们有 `(δ′ , v′) ⊢ M′ ↓ v₂` 和
    `(δ , v₁) ⊢ exts σ ↓ (δ′ , v′)`。根据后者可得 `(δ , v₁) ⊢ # 0 ↓ v′`。
    根据引理 `var-inv` 我们有 `v′ ⊑ v₁`，于是根据 `up-env` 引理我们有
    `(δ′ , v₁) ⊢ M′ ↓ v₂`，因此 `δ′ ⊢ ƛ M′ ↓ v₁ → v₂`。我们还需要证明
    `δ ⊢ σ ↓ δ′`。固定 `k`，我们有 `(δ , v₁) ⊢ rename S_ σ k ↓ δ k′`，
    接着应用引理 `rename-inc-reflect` 可得 `δ ⊢ σ k ↓ δ k′`，于是此情况证明完毕。

<!--
* Case `⊥-intro`: We choose `⊥` for `δ`.
  We have `⊥ ⊢ M ↓ ⊥` by `⊥-intro`.
  We have `` δ `⊢ σ ↓ `⊥ `` by the lemma `subst-⊥`.
-->

* 情况 `⊥-intro`：我们为 `δ` 选择`⊥`。
  根据 `⊥-intro` 我们有 `⊥ ⊢ M ↓ ⊥`。
  根据 `subst-⊥` 引理有 `` δ `⊢ σ ↓ `⊥ ``。

<!--
* Case `⊔-intro`: By the induction hypothesis we have
  `δ₁ ⊢ M ↓ v₁`, `δ₂ ⊢ M ↓ v₂`, `` δ `⊢ σ ↓ δ₁ ``, and `` δ `⊢ σ ↓ δ₂ ``.
  We have `δ₁ ⊔ δ₂ ⊢ M ↓ v₁` and `δ₁ ⊔ δ₂ ⊢ M ↓ v₂`
  by `⊑-env` with `⊑-env-conj-R1` and `⊑-env-conj-R2`.
  So by `⊔-intro` we have `δ₁ ⊔ δ₂ ⊢ M ↓ v₁ ⊔ v₂`.
  By `subst-⊔` we conclude that `` δ `⊢ σ ↓ δ₁ ⊔ δ₂ ``.
-->

* 情况 `⊔-intro`：根据归纳假设我们有 `δ₁ ⊢ M ↓ v₁`、`δ₂ ⊢ M ↓ v₂`、
  `` δ `⊢ σ ↓ δ₁ `` 和 `` δ `⊢ σ ↓ δ₂ ``。
  根据 `⊑-env`、`⊑-env-conj-R1` 和 `⊑-env-conj-R2` 我们有 `δ₁ ⊔ δ₂ ⊢ M ↓ v₁`
  和 `δ₁ ⊔ δ₂ ⊢ M ↓ v₂`，因此根据 `⊔-intro` 可得 `δ₁ ⊔ δ₂ ⊢ M ↓ v₁ ⊔ v₂`。
  根据 `subst-⊔` 可得 `` δ `⊢ σ ↓ δ₁ ⊔ δ₂ ``。


<!--
### Single substitution reflects denotations
-->

### 单一代换反映了指称不变

<!--
Most of the work is now behind us. We have proved that simultaneous
substitution reflects denotations. Of course, β reduction uses single
substitution, so we need a corollary that proves that single
substitution reflects denotations. That is,
given terms `N : (Γ , ★ ⊢ ★)` and `M : (Γ ⊢ ★)`,
if `γ ⊢ N [ M ] ↓ w`, then `γ ⊢ M ↓ v` and `(γ , v) ⊢ N ↓ w`
for some value `v`. We have `N [ M ] = subst (subst-zero M) N`.
-->

现在大部分工作已经完成，我们已经证明了同时代换反映了指称不变。当然，β-归约使用单一代换，
因此我们需要一个推论来证明单一代换反映了指称不变。也就是说，给定项
`N : (Γ , ★ ⊢ ★)` 和 `M : (Γ ⊢ ★)`，若 `γ ⊢ N [ M ] ↓ w`，则对于某个值 `v`
有 `γ ⊢ M ↓ v` 且 `( γ , v) ⊢ N ↓ w` 。于是我们有 `N [ M ] = subst (subst-zero M) N`。

<!--
We first prove a lemma about `subst-zero`, that if
`δ ⊢ subst-zero M ↓ γ`, then
`` γ `⊑ (δ , w) × δ ⊢ M ↓ w `` for some `w`.
-->

我们首先证明一个关于 `subst-zero` 的引理，即若 `δ ⊢ subst-zero M ↓ γ`，则对某个值
`w`，有 `` γ `⊑ (δ , w) × δ ⊢ M ↓ w ``。

```agda
subst-zero-reflect : ∀ {Δ} {δ : Env Δ} {γ : Env (Δ , ★)} {M : Δ ⊢ ★}
  → δ `⊢ subst-zero M ↓ γ
    ----------------------------------------
  → Σ[ w ∈ Value ] γ `⊑ (δ `, w) × δ ⊢ M ↓ w
subst-zero-reflect {δ = δ} {γ = γ} δσγ = ⟨ last γ , ⟨ lemma , δσγ Z ⟩ ⟩
  where
  lemma : γ `⊑ (δ `, last γ)
  lemma Z  =  ⊑-refl
  lemma (S x) = var-inv (δσγ (S x))
```

<!--
We choose `w` to be the last value in `γ` and we obtain `δ ⊢ M ↓ w`
by applying the premise to variable `Z`. Finally, to prove
`` γ `⊑ (δ , w) ``, we prove a lemma by induction in the input variable.
The base case is trivial because of our choice of `w`.
In the induction case, `S x`, the premise
`δ ⊢ subst-zero M ↓ γ` gives us `δ ⊢ x ↓ γ (S x)` and then
using `var-inv` we conclude that `` γ (S x) ⊑ (δ `, w) (S x) ``.
-->

我们选择 `w` 作为 `γ` 中的最后一个值，通过将前提应用到 `Z` 可得 `δ ⊢ M ↓ w`。
最后，要证明 `` γ `⊑ (δ , w) ``，我们需要在输入项中通过归纳来证明一个引理。
由于我们选择了 `w`，因此基本的情况是平凡的。在归纳的情况中 `S x` 中，
前提 `δ ⊢ subst-zero M ↓ γ` 给出了 `δ ⊢ x ↓ γ (S x)`，接着使用 `var-inv`
可得 `` γ (S x) ⊑ (δ `, w) (S x) ``。

<!--
Now to prove that substitution reflects denotations.
-->

现在证明代换反映了指称不变：

```agda
substitution-reflect : ∀ {Δ} {δ : Env Δ} {N : Δ , ★ ⊢ ★} {M : Δ ⊢ ★} {v}
  → δ ⊢ N [ M ] ↓ v
    ------------------------------------------------
  → Σ[ w ∈ Value ] δ ⊢ M ↓ w  ×  (δ `, w) ⊢ N ↓ v
substitution-reflect d with subst-reflect d refl
...  | ⟨ γ , ⟨ δσγ , γNv ⟩ ⟩ with subst-zero-reflect δσγ
...    | ⟨ w , ⟨ ineq , δMw ⟩ ⟩ = ⟨ w , ⟨ δMw , ⊑-env γNv ineq ⟩ ⟩
```

<!--
We apply the `subst-reflect` lemma to obtain
`δ ⊢ subst-zero M ↓ γ` and `γ ⊢ N ↓ v` for some `γ`.
Using the former, the `subst-zero-reflect` lemma gives
us `` γ `⊑ (δ , w) `` and `δ ⊢ M ↓ w`. We conclude that
`δ , w ⊢ N ↓ v` by applying the `⊑-env` lemma, using
`γ ⊢ N ↓ v` and `` γ `⊑ (δ , w) ``.
-->

我们应用 `subst-reflect` 引理可得对于某个 `γ` 有 `δ ⊢ subst-zero M ↓ γ`
和 `γ ⊢ N ↓ v`。通过使用前者，`subst-zero-reflect` 给出了 `` γ `⊑ (δ , w) ``
和 `δ ⊢ M ↓ w`。我们通过应用 `⊑-env` 引理，使用 `γ ⊢ N ↓ v` 和 `` γ `⊑ (δ , w) ``
可得 `δ , w ⊢ N ↓ v`。


<!--
### Reduction reflects denotations
-->

### 归约反映了指称不变

<!--
Now that we have proved that substitution reflects denotations, we can
easily prove that reduction does too.
-->

现在我们已经证明了代换反映了指称不变，可以很容易地证明归约也拥有此性质：

```agda
reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
    → γ ⊢ (N [ M ]) ↓ v
    → γ ⊢ (ƛ N) · M ↓ v
reflect-beta d
    with substitution-reflect d
... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ = ↦-elim (↦-intro d₂′) d₁′


reflect : ∀ {Γ} {γ : Env Γ} {M M′ N v}
  → γ ⊢ N ↓ v  →  M —→ M′  →   M′ ≡ N
    ---------------------------------
  → γ ⊢ M ↓ v
reflect var (ξ₁ r) ()
reflect var (ξ₂ r) ()
reflect{γ = γ} (var{x = x}) β mn
    with var{γ = γ}{x = x}
... | d′ rewrite sym mn = reflect-beta d′
reflect var (ζ r) ()
reflect (↦-elim d₁ d₂) (ξ₁ r) refl = ↦-elim (reflect d₁ r refl) d₂
reflect (↦-elim d₁ d₂) (ξ₂ r) refl = ↦-elim d₁ (reflect d₂ r refl)
reflect (↦-elim d₁ d₂) β mn
    with ↦-elim d₁ d₂
... | d′ rewrite sym mn = reflect-beta d′
reflect (↦-elim d₁ d₂) (ζ r) ()
reflect (↦-intro d) (ξ₁ r) ()
reflect (↦-intro d) (ξ₂ r) ()
reflect (↦-intro d) β mn
    with ↦-intro d
... | d′ rewrite sym mn = reflect-beta d′
reflect (↦-intro d) (ζ r) refl = ↦-intro (reflect d r refl)
reflect ⊥-intro r mn = ⊥-intro
reflect (⊔-intro d₁ d₂) r mn rewrite sym mn =
   ⊔-intro (reflect d₁ r refl) (reflect d₂ r refl)
reflect (sub d lt) r mn = sub (reflect d r mn) lt
```

<!--
## Reduction implies denotational equality
-->

## 归约蕴含指称等价

<!--
We have proved that reduction both preserves and reflects
denotations. Thus, reduction implies denotational equality.
-->

我们已经证明了归约保持并反映了指称不变，因此归约蕴含指称等价：

```agda
reduce-equal : ∀ {Γ} {M : Γ ⊢ ★} {N : Γ ⊢ ★}
  → M —→ N
    ---------
  → ℰ M ≃ ℰ N
reduce-equal {Γ}{M}{N} r γ v =
    ⟨ (λ m → preserve m r) , (λ n → reflect n r refl) ⟩
```

<!--
We conclude with the _soundness property_, that multi-step reduction
to a lambda abstraction implies denotational equivalence with a lambda
abstraction.
-->

最终我们就得到了**可靠性（Soundness Property）**，即多步归约到一个
λ-抽象蕴含指称等价于该 λ-抽象。

```agda
soundness : ∀{Γ} {M : Γ ⊢ ★} {N : Γ , ★ ⊢ ★}
  → M —↠ ƛ N
    -----------------
  → ℰ M ≃ ℰ (ƛ N)
soundness (.(ƛ _) ∎) γ v = ⟨ (λ x → x) , (λ x → x) ⟩
soundness {Γ} (L —→⟨ r ⟩ M—↠N) γ v =
   let ih = soundness M—↠N in
   let e = reduce-equal r in
   ≃-trans {Γ} e ih γ v
```


## Unicode

本章使用了以下 Unicode：

    ≟  U+225F  QUESTIONED EQUAL TO (\?=)
