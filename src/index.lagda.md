# Index

<!--
```agda
module index where
```
-->

This is a formalization of some aspects of
[Two-Level Type Theory](https://arxiv.org/abs/1705.03307), building on top of
the [Agda-Unimath library](https://unimath.github.io/agda-unimath/). The repository
can be found here [repository](https://github.com/FernandoChu/agda-2LTT).

This library consists of three parts:

### Foundations

Here we develop the basic facts about exotypes, fibrations, cofibrations and
sharp types.

```agda
open import foundation-2LTT public
```

### Category theory

This defines Reedy (co)fibrant diagrams, semi-segal types and there is work in
progress to define ∞-categories.

```agda
open import category-theory-2LTT public
```

### Univalence principle

This folder contains work in progress towards formalizing the
[Univalence Principle](https://arxiv.org/abs/2102.06275) paper.

```agda
open import univalence-principle public
```
