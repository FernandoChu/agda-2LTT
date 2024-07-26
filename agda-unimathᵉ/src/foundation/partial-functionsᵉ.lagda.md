# Partial functions

```agda
module foundation.partial-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.partial-elementsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "partialᵉ function"ᵉ Agda=partial-functionᵉ}} fromᵉ `A`ᵉ to `B`ᵉ isᵉ aᵉ
functionᵉ fromᵉ `A`ᵉ intoᵉ theᵉ typeᵉ ofᵉ
[partialᵉ elements](foundation.partial-elements.mdᵉ) ofᵉ `B`.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ
partialᵉ functionᵉ isᵉ aᵉ functionᵉ

```text
  Aᵉ → Σᵉ (Pᵉ : Prop),ᵉ (Pᵉ → B).ᵉ
```

Givenᵉ aᵉ partialᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ anᵉ elementᵉ `aᵉ : A`,ᵉ weᵉ sayᵉ thatᵉ `f`ᵉ isᵉ
{{#conceptᵉ "defined"ᵉ Disambiguation="partialᵉ function"ᵉ Agda=is-defined-partial-functionᵉ}}
atᵉ `a`ᵉ ifᵉ theᵉ partialᵉ elementᵉ `fᵉ a`ᵉ ofᵉ `A`ᵉ isᵉ defined.ᵉ

Partialᵉ functionsᵉ canᵉ beᵉ describedᵉ
[equivalently](foundation-core.equivalences.mdᵉ) asᵉ
[morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ)

```text
  ∅ᵉ     1   ∅ᵉ
  |     |   |
  |  ⇒ᵉ  | ∘ᵉ |
  ∨ᵉ     ∨ᵉ   ∨ᵉ
  Aᵉ   Propᵉ  Bᵉ
```

where theᵉ compositionᵉ operationᵉ isᵉ
[composition](species.composition-cauchy-series-species-of-types.mdᵉ) ofᵉ
[polynomialᵉ endofunctors](trees.polynomial-endofunctors.md).ᵉ

## Definitions

### Partial dependent functions

```agda
partial-dependent-functionᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
partial-dependent-functionᵉ l3ᵉ Aᵉ Bᵉ =
  (xᵉ : Aᵉ) → partial-elementᵉ l3ᵉ (Bᵉ xᵉ)
```

### Partial functions

```agda
partial-functionᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
partial-functionᵉ l3ᵉ Aᵉ Bᵉ = partial-dependent-functionᵉ l3ᵉ Aᵉ (λ _ → Bᵉ)
```

### The predicate on partial dependent functions of being defined at an element in the domain

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ : partial-dependent-functionᵉ l3ᵉ Aᵉ Bᵉ) (aᵉ : Aᵉ)
  where

  is-defined-prop-partial-dependent-functionᵉ : Propᵉ l3ᵉ
  is-defined-prop-partial-dependent-functionᵉ =
    is-defined-prop-partial-elementᵉ (fᵉ aᵉ)

  is-defined-partial-dependent-functionᵉ : UUᵉ l3ᵉ
  is-defined-partial-dependent-functionᵉ =
    type-Propᵉ is-defined-prop-partial-dependent-functionᵉ
```

### The predicate on partial functions of being defined at an element in the domain

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : partial-functionᵉ l3ᵉ Aᵉ Bᵉ)
  (aᵉ : Aᵉ)
  where

  is-defined-prop-partial-functionᵉ : Propᵉ l3ᵉ
  is-defined-prop-partial-functionᵉ =
    is-defined-prop-partial-dependent-functionᵉ fᵉ aᵉ

  is-defined-partial-functionᵉ : UUᵉ l3ᵉ
  is-defined-partial-functionᵉ =
    is-defined-partial-dependent-functionᵉ fᵉ aᵉ
```

### The partial dependent function obtained from a dependent function

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
  where

  partial-dependent-function-dependent-functionᵉ :
    partial-dependent-functionᵉ lzero Aᵉ Bᵉ
  partial-dependent-function-dependent-functionᵉ aᵉ =
    unit-partial-elementᵉ (fᵉ aᵉ)
```

### The partial function obtained from a function

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  partial-function-functionᵉ : partial-functionᵉ lzero Aᵉ Bᵉ
  partial-function-functionᵉ = partial-dependent-function-dependent-functionᵉ fᵉ
```

## See also

-ᵉ [Copartialᵉ functions](foundation.copartial-functions.mdᵉ)
-ᵉ [Partialᵉ elements](foundation.partial-elements.mdᵉ)
-ᵉ [Partialᵉ sequences](foundation.partial-sequences.mdᵉ)