# Lists of elements in discrete types

```agda
module lists.lists-discrete-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleansᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ
```

</details>

## Idea

Inᵉ thisᵉ fileᵉ weᵉ studyᵉ listsᵉ ofᵉ elementsᵉ in discreteᵉ types.ᵉ

## Definitions

### The type of lists of a discrete type is discrete

```agda
has-decidable-equality-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  has-decidable-equalityᵉ Aᵉ → has-decidable-equalityᵉ (listᵉ Aᵉ)
has-decidable-equality-listᵉ dᵉ nilᵉ nilᵉ = inlᵉ reflᵉ
has-decidable-equality-listᵉ dᵉ nilᵉ (consᵉ xᵉ lᵉ) =
  inrᵉ (map-inv-raiseᵉ ∘ᵉ Eq-eq-listᵉ nilᵉ (consᵉ xᵉ lᵉ))
has-decidable-equality-listᵉ dᵉ (consᵉ xᵉ lᵉ) nilᵉ =
  inrᵉ (map-inv-raiseᵉ ∘ᵉ Eq-eq-listᵉ (consᵉ xᵉ lᵉ) nilᵉ)
has-decidable-equality-listᵉ dᵉ (consᵉ xᵉ lᵉ) (consᵉ x'ᵉ l'ᵉ) =
  is-decidable-iffᵉ
    ( eq-Eq-listᵉ (consᵉ xᵉ lᵉ) (consᵉ x'ᵉ l'ᵉ))
    ( Eq-eq-listᵉ (consᵉ xᵉ lᵉ) (consᵉ x'ᵉ l'ᵉ))
    ( is-decidable-productᵉ
      ( dᵉ xᵉ x'ᵉ)
      ( is-decidable-iffᵉ
        ( Eq-eq-listᵉ lᵉ l'ᵉ)
        ( eq-Eq-listᵉ lᵉ l'ᵉ)
        ( has-decidable-equality-listᵉ dᵉ lᵉ l'ᵉ)))

has-decidable-equality-has-decidable-equality-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  has-decidable-equalityᵉ (listᵉ Aᵉ) → has-decidable-equalityᵉ Aᵉ
has-decidable-equality-has-decidable-equality-listᵉ dᵉ xᵉ yᵉ =
  is-decidable-left-factorᵉ
    ( is-decidable-iffᵉ
      ( Eq-eq-listᵉ (consᵉ xᵉ nilᵉ) (consᵉ yᵉ nilᵉ))
      ( eq-Eq-listᵉ (consᵉ xᵉ nilᵉ) (consᵉ yᵉ nilᵉ))
      ( dᵉ (consᵉ xᵉ nilᵉ) (consᵉ yᵉ nilᵉ)))
    ( raise-starᵉ)
```

### Testing whether an element of a discrete type is in a list

```agda
elem-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  has-decidable-equalityᵉ Aᵉ →
  Aᵉ → listᵉ Aᵉ → boolᵉ
elem-listᵉ dᵉ xᵉ nilᵉ = falseᵉ
elem-listᵉ dᵉ xᵉ (consᵉ x'ᵉ lᵉ) with (dᵉ xᵉ x'ᵉ)
... | inlᵉ _ = trueᵉ
... | inrᵉ _ = elem-listᵉ dᵉ xᵉ lᵉ
```

### Removing duplicates in lists

```agda
union-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  has-decidable-equalityᵉ Aᵉ →
  listᵉ Aᵉ → listᵉ Aᵉ → listᵉ Aᵉ
union-listᵉ dᵉ nilᵉ l'ᵉ = l'ᵉ
union-listᵉ dᵉ (consᵉ xᵉ lᵉ) l'ᵉ with (elem-listᵉ dᵉ xᵉ l'ᵉ)
... | trueᵉ = l'ᵉ
... | falseᵉ = consᵉ xᵉ l'ᵉ
```

## Properties

### If a list has an element then it is non empty

```agda
is-nonnil-elem-listᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  (dᵉ : has-decidable-equalityᵉ Aᵉ) →
  (aᵉ : Aᵉ) →
  (lᵉ : listᵉ Aᵉ) →
  elem-listᵉ dᵉ aᵉ lᵉ ＝ᵉ trueᵉ →
  is-nonnil-listᵉ lᵉ
is-nonnil-elem-listᵉ dᵉ aᵉ nilᵉ ()
is-nonnil-elem-listᵉ dᵉ aᵉ (consᵉ xᵉ lᵉ) pᵉ ()
```

### If the union of two lists is empty, then these two lists are empty

```agda
is-nil-union-is-nil-listᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  (dᵉ : has-decidable-equalityᵉ Aᵉ) →
  (lᵉ l'ᵉ : listᵉ Aᵉ) →
  union-listᵉ dᵉ lᵉ l'ᵉ ＝ᵉ nilᵉ →
  is-nil-listᵉ lᵉ ×ᵉ is-nil-listᵉ l'ᵉ
is-nil-union-is-nil-listᵉ dᵉ nilᵉ l'ᵉ pᵉ = (reflᵉ ,ᵉ pᵉ)
is-nil-union-is-nil-listᵉ dᵉ (consᵉ xᵉ lᵉ) l'ᵉ pᵉ with (elem-listᵉ dᵉ xᵉ l'ᵉ) in qᵉ
... | trueᵉ =
  ex-falsoᵉ (is-nonnil-elem-listᵉ dᵉ xᵉ l'ᵉ qᵉ pᵉ)
... | falseᵉ = ex-falsoᵉ (is-nonnil-cons-listᵉ xᵉ l'ᵉ pᵉ)
```