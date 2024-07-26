# Bases of directed trees

```agda
module trees.bases-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.walks-directed-graphsᵉ

open import trees.directed-treesᵉ
```

</details>

## Idea

Theᵉ **base**ᵉ ofᵉ aᵉ directedᵉ treeᵉ consistsᵉ ofᵉ theᵉ nodesᵉ equippedᵉ with anᵉ edgeᵉ to
theᵉ root.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  base-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  base-Directed-Treeᵉ = direct-predecessor-Directed-Treeᵉ Tᵉ (root-Directed-Treeᵉ Tᵉ)

  module _
    (bᵉ : base-Directed-Treeᵉ)
    where

    node-base-Directed-Treeᵉ : node-Directed-Treeᵉ Tᵉ
    node-base-Directed-Treeᵉ = pr1ᵉ bᵉ

    edge-base-Directed-Treeᵉ :
      edge-Directed-Treeᵉ Tᵉ node-base-Directed-Treeᵉ (root-Directed-Treeᵉ Tᵉ)
    edge-base-Directed-Treeᵉ = pr2ᵉ bᵉ
```

## Properties

### The root is not a base element

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  is-proper-node-base-Directed-Treeᵉ :
    (bᵉ : base-Directed-Treeᵉ Tᵉ) →
    is-proper-node-Directed-Treeᵉ Tᵉ (node-base-Directed-Treeᵉ Tᵉ bᵉ)
  is-proper-node-base-Directed-Treeᵉ (xᵉ ,ᵉ eᵉ) reflᵉ =
    no-direct-successor-root-Directed-Treeᵉ Tᵉ (xᵉ ,ᵉ eᵉ)

  no-walk-to-base-root-Directed-Treeᵉ :
    (bᵉ : base-Directed-Treeᵉ Tᵉ) →
    ¬ᵉ ( walk-Directed-Treeᵉ Tᵉ
        ( root-Directed-Treeᵉ Tᵉ)
        ( node-base-Directed-Treeᵉ Tᵉ bᵉ))
  no-walk-to-base-root-Directed-Treeᵉ
    ( pairᵉ .(root-Directed-Treeᵉ Tᵉ) eᵉ)
    refl-walk-Directed-Graphᵉ =
    no-direct-successor-root-Directed-Treeᵉ Tᵉ (root-Directed-Treeᵉ Tᵉ ,ᵉ eᵉ)
  no-walk-to-base-root-Directed-Treeᵉ bᵉ (cons-walk-Directed-Graphᵉ eᵉ wᵉ) =
    no-direct-successor-root-Directed-Treeᵉ Tᵉ (ᵉ_ ,ᵉ eᵉ)
```

### Any node which has a walk to a base element is a proper node

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  is-proper-node-walk-to-base-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) (bᵉ : base-Directed-Treeᵉ Tᵉ) →
    walk-Directed-Treeᵉ Tᵉ xᵉ (node-base-Directed-Treeᵉ Tᵉ bᵉ) →
    is-proper-node-Directed-Treeᵉ Tᵉ xᵉ
  is-proper-node-walk-to-base-Directed-Treeᵉ ._ bᵉ refl-walk-Directed-Graphᵉ =
    is-proper-node-base-Directed-Treeᵉ Tᵉ bᵉ
  is-proper-node-walk-to-base-Directed-Treeᵉ xᵉ bᵉ (cons-walk-Directed-Graphᵉ eᵉ wᵉ) =
    is-proper-node-direct-successor-Directed-Treeᵉ Tᵉ eᵉ
```

### There are no edges between base elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  no-edge-base-Directed-Treeᵉ :
    (aᵉ bᵉ : base-Directed-Treeᵉ Tᵉ) →
    ¬ᵉ ( edge-Directed-Treeᵉ Tᵉ
        ( node-base-Directed-Treeᵉ Tᵉ aᵉ)
        ( node-base-Directed-Treeᵉ Tᵉ bᵉ))
  no-edge-base-Directed-Treeᵉ aᵉ bᵉ eᵉ =
    ex-falsoᵉ
      ( is-not-one-two-ℕᵉ
        ( apᵉ
          ( length-walk-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ))
          ( eq-is-contr'ᵉ
            ( unique-walk-to-root-Directed-Treeᵉ Tᵉ
              ( node-base-Directed-Treeᵉ Tᵉ aᵉ))
            ( cons-walk-Directed-Treeᵉ Tᵉ eᵉ
              ( unit-walk-Directed-Treeᵉ Tᵉ (edge-base-Directed-Treeᵉ Tᵉ bᵉ)))
            ( unit-walk-Directed-Treeᵉ Tᵉ (edge-base-Directed-Treeᵉ Tᵉ aᵉ)))))
```

### For any node `x`, the coproduct of `is-root x` and the type of base elements `b` equipped with a walk from `x` to `b` is contractible

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  cons-cases-center-walk-to-base-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ} (eᵉ : edge-Directed-Treeᵉ Tᵉ xᵉ yᵉ) →
    (wᵉ : walk-Directed-Treeᵉ Tᵉ yᵉ (root-Directed-Treeᵉ Tᵉ)) →
    Σᵉ (base-Directed-Treeᵉ Tᵉ) (walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ pr1ᵉ)
  cons-cases-center-walk-to-base-Directed-Treeᵉ eᵉ refl-walk-Directed-Graphᵉ =
    (ᵉ_ ,ᵉ eᵉ) ,ᵉ refl-walk-Directed-Treeᵉ Tᵉ
  cons-cases-center-walk-to-base-Directed-Treeᵉ eᵉ
    ( cons-walk-Directed-Graphᵉ fᵉ wᵉ) =
    totᵉ
      ( λ uᵉ → cons-walk-Directed-Treeᵉ Tᵉ eᵉ)
      ( cons-cases-center-walk-to-base-Directed-Treeᵉ fᵉ wᵉ)

  cases-center-walk-to-base-Directed-Treeᵉ :
    {xᵉ : node-Directed-Treeᵉ Tᵉ}
    (wᵉ : walk-Directed-Treeᵉ Tᵉ xᵉ (root-Directed-Treeᵉ Tᵉ)) →
    is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
    Σᵉ (base-Directed-Treeᵉ Tᵉ) (walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ pr1ᵉ)
  cases-center-walk-to-base-Directed-Treeᵉ refl-walk-Directed-Graphᵉ = inlᵉ reflᵉ
  cases-center-walk-to-base-Directed-Treeᵉ (cons-walk-Directed-Graphᵉ eᵉ wᵉ) =
    inrᵉ (cons-cases-center-walk-to-base-Directed-Treeᵉ eᵉ wᵉ)

  center-walk-to-base-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
    Σᵉ (base-Directed-Treeᵉ Tᵉ) (walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ pr1ᵉ)
  center-walk-to-base-Directed-Treeᵉ xᵉ =
    cases-center-walk-to-base-Directed-Treeᵉ (walk-to-root-Directed-Treeᵉ Tᵉ xᵉ)

  cons-cases-contraction-walk-to-base-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ} (eᵉ : edge-Directed-Treeᵉ Tᵉ xᵉ yᵉ) →
    (wᵉ : walk-Directed-Treeᵉ Tᵉ yᵉ (root-Directed-Treeᵉ Tᵉ))
    (uᵉ : Σᵉ (base-Directed-Treeᵉ Tᵉ) (walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ pr1ᵉ)) →
    cons-cases-center-walk-to-base-Directed-Treeᵉ eᵉ wᵉ ＝ᵉ uᵉ
  cons-cases-contraction-walk-to-base-Directed-Treeᵉ eᵉ
    ( refl-walk-Directed-Graphᵉ)
    ( (zᵉ ,ᵉ fᵉ) ,ᵉ refl-walk-Directed-Graphᵉ) =
    apᵉ
      ( λ iᵉ → ((zᵉ ,ᵉ iᵉ) ,ᵉ refl-walk-Directed-Graphᵉ))
      ( eq-is-contrᵉ
        ( is-proof-irrelevant-edge-to-root-Directed-Treeᵉ Tᵉ zᵉ eᵉ))
  cons-cases-contraction-walk-to-base-Directed-Treeᵉ {xᵉ} eᵉ
    ( refl-walk-Directed-Graphᵉ)
    ( (zᵉ ,ᵉ fᵉ) ,ᵉ cons-walk-Directed-Graphᵉ {ᵉ_} {yᵉ} gᵉ vᵉ) =
    ex-falsoᵉ
      ( no-walk-to-base-root-Directed-Treeᵉ Tᵉ
        ( zᵉ ,ᵉ fᵉ)
        ( trᵉ
          ( λ uᵉ → walk-Directed-Treeᵉ Tᵉ uᵉ zᵉ)
          ( apᵉ pr1ᵉ
            ( eq-direct-successor-Directed-Treeᵉ Tᵉ
              ( yᵉ ,ᵉ gᵉ)
              ( root-Directed-Treeᵉ Tᵉ ,ᵉ eᵉ)))
          ( vᵉ)))
  cons-cases-contraction-walk-to-base-Directed-Treeᵉ eᵉ
    ( cons-walk-Directed-Graphᵉ {yᵉ} {zᵉ} gᵉ wᵉ)
    ( (uᵉ ,ᵉ fᵉ) ,ᵉ refl-walk-Directed-Graphᵉ) =
    ex-falsoᵉ
      ( no-direct-successor-root-Directed-Treeᵉ Tᵉ
        ( trᵉ
          ( λ iᵉ → Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ iᵉ))
          ( apᵉ pr1ᵉ
            ( eq-direct-successor-Directed-Treeᵉ Tᵉ
              ( yᵉ ,ᵉ eᵉ)
              ( root-Directed-Treeᵉ Tᵉ ,ᵉ fᵉ)))
          ( zᵉ ,ᵉ gᵉ)))
  cons-cases-contraction-walk-to-base-Directed-Treeᵉ {xᵉ} {yᵉ} eᵉ
    ( cons-walk-Directed-Graphᵉ {yᵉ} {zᵉ} gᵉ wᵉ)
    ( (uᵉ ,ᵉ fᵉ) ,ᵉ cons-walk-Directed-Graphᵉ {ᵉ_} {y'ᵉ} e'ᵉ vᵉ) =
    ( apᵉ
      ( totᵉ (λ uᵉ → cons-walk-Directed-Treeᵉ Tᵉ eᵉ))
      ( cons-cases-contraction-walk-to-base-Directed-Treeᵉ gᵉ wᵉ
        ( (uᵉ ,ᵉ fᵉ) ,ᵉ
          ( tr-walk-eq-direct-successor-Directed-Treeᵉ Tᵉ
            ( y'ᵉ ,ᵉ e'ᵉ)
            ( yᵉ ,ᵉ eᵉ) vᵉ)))) ∙ᵉ
    ( apᵉ
      ( pairᵉ (uᵉ ,ᵉ fᵉ))
      ( eq-tr-walk-eq-direct-successor-Directed-Treeᵉ Tᵉ (y'ᵉ ,ᵉ e'ᵉ) (yᵉ ,ᵉ eᵉ) vᵉ))

  cases-contraction-walk-to-base-Directed-Treeᵉ :
    {xᵉ : node-Directed-Treeᵉ Tᵉ}
    (wᵉ : walk-Directed-Treeᵉ Tᵉ xᵉ (root-Directed-Treeᵉ Tᵉ)) →
    (uᵉ :
      is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
      Σᵉ (base-Directed-Treeᵉ Tᵉ) (walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ pr1ᵉ)) →
    cases-center-walk-to-base-Directed-Treeᵉ wᵉ ＝ᵉ uᵉ
  cases-contraction-walk-to-base-Directed-Treeᵉ
    ( refl-walk-Directed-Graphᵉ)
    ( inlᵉ pᵉ) =
    apᵉ inlᵉ (eq-is-contrᵉ (is-contr-loop-space-root-Directed-Treeᵉ Tᵉ))
  cases-contraction-walk-to-base-Directed-Treeᵉ refl-walk-Directed-Graphᵉ
    ( inrᵉ (bᵉ ,ᵉ wᵉ)) =
    ex-falsoᵉ (no-walk-to-base-root-Directed-Treeᵉ Tᵉ bᵉ wᵉ)
  cases-contraction-walk-to-base-Directed-Treeᵉ
    ( cons-walk-Directed-Graphᵉ eᵉ wᵉ)
    ( inlᵉ reflᵉ) =
    ex-falsoᵉ (no-direct-successor-root-Directed-Treeᵉ Tᵉ (ᵉ_ ,ᵉ eᵉ))
  cases-contraction-walk-to-base-Directed-Treeᵉ
    ( cons-walk-Directed-Graphᵉ eᵉ wᵉ) (inrᵉ uᵉ) =
    apᵉ inrᵉ (cons-cases-contraction-walk-to-base-Directed-Treeᵉ eᵉ wᵉ uᵉ)

  contraction-walk-to-base-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ)
    ( wᵉ :
      is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
      Σᵉ (base-Directed-Treeᵉ Tᵉ) (walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ pr1ᵉ)) →
    center-walk-to-base-Directed-Treeᵉ xᵉ ＝ᵉ wᵉ
  contraction-walk-to-base-Directed-Treeᵉ xᵉ =
    cases-contraction-walk-to-base-Directed-Treeᵉ
      ( walk-to-root-Directed-Treeᵉ Tᵉ xᵉ)

  unique-walk-to-base-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-contrᵉ
      ( is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
        Σᵉ ( base-Directed-Treeᵉ Tᵉ)
          ( walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ node-base-Directed-Treeᵉ Tᵉ))
  unique-walk-to-base-Directed-Treeᵉ xᵉ =
    ( center-walk-to-base-Directed-Treeᵉ xᵉ ,ᵉ
      contraction-walk-to-base-Directed-Treeᵉ xᵉ)

  is-root-or-walk-to-base-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
    Σᵉ ( base-Directed-Treeᵉ Tᵉ)
      ( walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ node-base-Directed-Treeᵉ Tᵉ)
  is-root-or-walk-to-base-Directed-Treeᵉ xᵉ =
    centerᵉ (unique-walk-to-base-Directed-Treeᵉ xᵉ)

  is-root-is-root-or-walk-to-base-root-Directed-Treeᵉ :
    is-root-or-walk-to-base-Directed-Treeᵉ (root-Directed-Treeᵉ Tᵉ) ＝ᵉ
    inlᵉ reflᵉ
  is-root-is-root-or-walk-to-base-root-Directed-Treeᵉ =
    eq-is-contrᵉ (unique-walk-to-base-Directed-Treeᵉ (root-Directed-Treeᵉ Tᵉ))

  unique-walk-to-base-is-proper-node-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) → is-proper-node-Directed-Treeᵉ Tᵉ xᵉ →
    is-contrᵉ
      ( Σᵉ ( base-Directed-Treeᵉ Tᵉ)
          ( walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ node-base-Directed-Treeᵉ Tᵉ))
  unique-walk-to-base-is-proper-node-Directed-Treeᵉ xᵉ fᵉ =
    is-contr-equiv'ᵉ
      ( is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
        Σᵉ ( base-Directed-Treeᵉ Tᵉ)
          ( walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ node-base-Directed-Treeᵉ Tᵉ))
      ( left-unit-law-coproduct-is-emptyᵉ
        ( is-root-Directed-Treeᵉ Tᵉ xᵉ)
        ( Σᵉ ( base-Directed-Treeᵉ Tᵉ)
          ( walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ node-base-Directed-Treeᵉ Tᵉ))
        ( fᵉ))
      ( unique-walk-to-base-Directed-Treeᵉ xᵉ)

  walk-to-base-is-proper-node-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) → is-proper-node-Directed-Treeᵉ Tᵉ xᵉ →
    Σᵉ ( base-Directed-Treeᵉ Tᵉ)
      ( walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ node-base-Directed-Treeᵉ Tᵉ)
  walk-to-base-is-proper-node-Directed-Treeᵉ xᵉ Hᵉ =
    centerᵉ (unique-walk-to-base-is-proper-node-Directed-Treeᵉ xᵉ Hᵉ)

  unique-walk-to-base-direct-successor-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ)
    (uᵉ : Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)) →
    is-contrᵉ
      ( Σᵉ ( base-Directed-Treeᵉ Tᵉ)
          ( walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ node-base-Directed-Treeᵉ Tᵉ))
  unique-walk-to-base-direct-successor-Directed-Treeᵉ xᵉ uᵉ =
    unique-walk-to-base-is-proper-node-Directed-Treeᵉ xᵉ
      ( is-proper-node-direct-successor-Directed-Treeᵉ Tᵉ (pr2ᵉ uᵉ))

  is-proof-irrelevant-walk-to-base-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-proof-irrelevantᵉ
      ( Σᵉ ( base-Directed-Treeᵉ Tᵉ)
          ( λ bᵉ → walk-Directed-Treeᵉ Tᵉ xᵉ (node-base-Directed-Treeᵉ Tᵉ bᵉ)))
  is-proof-irrelevant-walk-to-base-Directed-Treeᵉ xᵉ (bᵉ ,ᵉ wᵉ) =
    unique-walk-to-base-is-proper-node-Directed-Treeᵉ xᵉ
      ( is-proper-node-walk-to-base-Directed-Treeᵉ Tᵉ xᵉ bᵉ wᵉ)

  is-prop-walk-to-base-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-propᵉ
      ( Σᵉ ( base-Directed-Treeᵉ Tᵉ)
          ( λ bᵉ → walk-Directed-Treeᵉ Tᵉ xᵉ (node-base-Directed-Treeᵉ Tᵉ bᵉ)))
  is-prop-walk-to-base-Directed-Treeᵉ xᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( is-proof-irrelevant-walk-to-base-Directed-Treeᵉ xᵉ)

  walk-to-base-Directed-Tree-Propᵉ : node-Directed-Treeᵉ Tᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (walk-to-base-Directed-Tree-Propᵉ xᵉ) =
    Σᵉ ( base-Directed-Treeᵉ Tᵉ)
      ( λ bᵉ → walk-Directed-Treeᵉ Tᵉ xᵉ (node-base-Directed-Treeᵉ Tᵉ bᵉ))
  pr2ᵉ (walk-to-base-Directed-Tree-Propᵉ xᵉ) =
    is-prop-walk-to-base-Directed-Treeᵉ xᵉ
```

### The type of proper nodes of a directed tree is equivalent to the type of nodes equipped with a base element `b` and a walk to `b`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  compute-proper-node-Directed-Treeᵉ :
    proper-node-Directed-Treeᵉ Tᵉ ≃ᵉ
    Σᵉ ( base-Directed-Treeᵉ Tᵉ)
      ( λ bᵉ →
        Σᵉ ( node-Directed-Treeᵉ Tᵉ)
          ( λ xᵉ → walk-Directed-Treeᵉ Tᵉ xᵉ (node-base-Directed-Treeᵉ Tᵉ bᵉ)))
  compute-proper-node-Directed-Treeᵉ =
    ( equiv-left-swap-Σᵉ) ∘eᵉ
    ( equiv-totᵉ
      ( λ xᵉ →
        equiv-iffᵉ
          ( is-proper-node-Directed-Tree-Propᵉ Tᵉ xᵉ)
          ( walk-to-base-Directed-Tree-Propᵉ Tᵉ xᵉ)
          ( walk-to-base-is-proper-node-Directed-Treeᵉ Tᵉ xᵉ)
          ( λ (bᵉ ,ᵉ wᵉ) → is-proper-node-walk-to-base-Directed-Treeᵉ Tᵉ xᵉ bᵉ wᵉ)))

  map-compute-proper-node-Directed-Treeᵉ :
    proper-node-Directed-Treeᵉ Tᵉ →
    Σᵉ ( base-Directed-Treeᵉ Tᵉ)
      ( λ bᵉ →
        Σᵉ ( node-Directed-Treeᵉ Tᵉ)
          ( λ xᵉ → walk-Directed-Treeᵉ Tᵉ xᵉ (node-base-Directed-Treeᵉ Tᵉ bᵉ)))
  map-compute-proper-node-Directed-Treeᵉ =
    map-equivᵉ compute-proper-node-Directed-Treeᵉ

  eq-compute-proper-node-Directed-Treeᵉ :
    {xᵉ : node-Directed-Treeᵉ Tᵉ} (Hᵉ : is-proper-node-Directed-Treeᵉ Tᵉ xᵉ)
    (bᵉ : base-Directed-Treeᵉ Tᵉ)
    (wᵉ : walk-Directed-Treeᵉ Tᵉ xᵉ (node-base-Directed-Treeᵉ Tᵉ bᵉ)) →
    map-compute-proper-node-Directed-Treeᵉ (xᵉ ,ᵉ Hᵉ) ＝ᵉ (bᵉ ,ᵉ xᵉ ,ᵉ wᵉ)
  eq-compute-proper-node-Directed-Treeᵉ {xᵉ} Hᵉ bᵉ wᵉ =
    apᵉ
      ( map-equivᵉ equiv-left-swap-Σᵉ)
      ( eq-pair-eq-fiberᵉ (eq-is-propᵉ (is-prop-walk-to-base-Directed-Treeᵉ Tᵉ xᵉ)))
```