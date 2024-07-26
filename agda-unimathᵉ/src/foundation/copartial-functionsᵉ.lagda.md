# Copartial functions

```agda
module foundation.copartial-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.copartial-elementsᵉ
open import foundation.partial-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "copartialᵉ function"ᵉ Agda=copartial-functionᵉ}} fromᵉ `A`ᵉ to `B`ᵉ isᵉ aᵉ
mapᵉ fromᵉ `A`ᵉ intoᵉ theᵉ typeᵉ ofᵉ
[copartialᵉ elements](foundation.copartial-elements.mdᵉ) ofᵉ `B`.ᵉ I.e.,ᵉ aᵉ copartialᵉ
functionᵉ isᵉ aᵉ mapᵉ

```text
  Aᵉ → Σᵉ (Qᵉ : Prop),ᵉ Bᵉ *ᵉ Qᵉ
```

where `-ᵉ *ᵉ Q`ᵉ isᵉ theᵉ
[closedᵉ modality](orthogonal-factorization-systems.closed-modalities.md),ᵉ whichᵉ
isᵉ definedᵉ byᵉ theᵉ [joinᵉ operation](synthetic-homotopy-theory.joins-of-types.md).ᵉ

Evaluationᵉ ofᵉ aᵉ copartialᵉ functionᵉ `f`ᵉ atᵉ `aᵉ : A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "denied"ᵉ Disambiguation="copartialᵉ function"ᵉ Agda=is-denied-copartial-functionᵉ}}
ifᵉ evaluationᵉ ofᵉ theᵉ copartialᵉ elementᵉ `fᵉ a`ᵉ ofᵉ `B`ᵉ isᵉ denied.ᵉ

Aᵉ copartialᵉ functionᵉ isᵉ [equivalently](foundation-core.equivalences.mdᵉ)
describedᵉ asᵉ aᵉ [morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ)

```text
     Aᵉ     Bᵉ   1
     |     |   |
  idᵉ |  ⇒ᵉ  | □ᵉ | Tᵉ
     ∨ᵉ     ∨ᵉ   ∨ᵉ
     Aᵉ     1  Propᵉ
```

where `□`ᵉ isᵉ theᵉ
[pushout-product](synthetic-homotopy-theory.pushout-products.md).ᵉ Indeed,ᵉ theᵉ
domainᵉ ofᵉ theᵉ pushout-productᵉ `Bᵉ □ᵉ T`ᵉ isᵉ theᵉ typeᵉ ofᵉ copartialᵉ elementsᵉ ofᵉ `B`.ᵉ

{{#conceptᵉ "Composition"ᵉ Disambiguation="copartialᵉ functions"ᵉ}} ofᵉ copartialᵉ
functionsᵉ canᵉ beᵉ definedᵉ byᵉ

```text
                     copartial-elementᵉ (copartial-elementᵉ Cᵉ)
                            ∧ᵉ                 |
   map-copartial-elementᵉ gᵉ /ᵉ                  | join-copartial-elementᵉ
                          /ᵉ                   ∨ᵉ
  Aᵉ ---->ᵉ copartial-elementᵉ Bᵉ       copartial-elementᵉ Cᵉ
      fᵉ
```

Inᵉ thisᵉ diagram,ᵉ theᵉ mapᵉ goingᵉ upᵉ isᵉ definedᵉ byᵉ functorialityᵉ ofᵉ theᵉ operationᵉ

```text
  Xᵉ ↦ᵉ Σᵉ (Qᵉ : Prop),ᵉ Xᵉ *ᵉ Qᵉ
```

Theᵉ mapᵉ goingᵉ downᵉ isᵉ definedᵉ byᵉ theᵉ joinᵉ operationᵉ onᵉ copartialᵉ elements,ᵉ i.e.,ᵉ
theᵉ pushout-productᵉ algebraᵉ structureᵉ ofᵉ theᵉ mapᵉ `Tᵉ : 1 → Prop`.ᵉ Theᵉ mainᵉ ideaᵉ
behindᵉ compositionᵉ ofᵉ copartialᵉ functionsᵉ isᵉ thatᵉ aᵉ compositeᵉ ofᵉ copartialᵉ
functionᵉ isᵉ deniedᵉ onᵉ theᵉ unionᵉ ofᵉ theᵉ subtypesᵉ where eachᵉ factorᵉ isᵉ denied.ᵉ
Indeed,ᵉ ifᵉ `f`ᵉ isᵉ deniedᵉ atᵉ `a`ᵉ orᵉ `map-copartial-elementᵉ g`ᵉ isᵉ deniedᵉ atᵉ theᵉ
copartialᵉ elementᵉ `fᵉ a`ᵉ ofᵉ `B`,ᵉ thenᵉ theᵉ compositeᵉ ofᵉ copartialᵉ functionsᵉ
`gᵉ ∘ᵉ f`ᵉ shouldᵉ beᵉ deniedᵉ atᵉ `a`.ᵉ

**Note:**ᵉ Theᵉ topicᵉ ofᵉ copartialᵉ functionsᵉ wasᵉ notᵉ knownᵉ to usᵉ in theᵉ
literature,ᵉ andᵉ ourᵉ formalizationᵉ onᵉ thisᵉ topicᵉ shouldᵉ beᵉ consideredᵉ
experimental.ᵉ

## Definitions

### Copartial dependent functions

```agda
copartial-dependent-functionᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → (Aᵉ → UUᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
copartial-dependent-functionᵉ l3ᵉ Aᵉ Bᵉ = (xᵉ : Aᵉ) → copartial-elementᵉ l3ᵉ (Bᵉ xᵉ)
```

### Copartial functions

```agda
copartial-functionᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
copartial-functionᵉ l3ᵉ Aᵉ Bᵉ = copartial-dependent-functionᵉ l3ᵉ Aᵉ (λ _ → Bᵉ)
```

### Denied values of copartial dependent functions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ : copartial-dependent-functionᵉ l3ᵉ Aᵉ Bᵉ) (aᵉ : Aᵉ)
  where

  is-denied-prop-copartial-dependent-functionᵉ : Propᵉ l3ᵉ
  is-denied-prop-copartial-dependent-functionᵉ =
    is-denied-prop-copartial-elementᵉ (fᵉ aᵉ)

  is-denied-copartial-dependent-functionᵉ : UUᵉ l3ᵉ
  is-denied-copartial-dependent-functionᵉ = is-denied-copartial-elementᵉ (fᵉ aᵉ)
```

### Denied values of copartial functions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : copartial-functionᵉ l3ᵉ Aᵉ Bᵉ)
  (aᵉ : Aᵉ)
  where

  is-denied-prop-copartial-functionᵉ : Propᵉ l3ᵉ
  is-denied-prop-copartial-functionᵉ =
    is-denied-prop-copartial-dependent-functionᵉ fᵉ aᵉ

  is-denied-copartial-functionᵉ : UUᵉ l3ᵉ
  is-denied-copartial-functionᵉ =
    is-denied-copartial-dependent-functionᵉ fᵉ aᵉ
```

### Copartial dependent functions obtained from dependent functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
  where

  copartial-dependent-function-dependent-functionᵉ :
    copartial-dependent-functionᵉ lzero Aᵉ Bᵉ
  copartial-dependent-function-dependent-functionᵉ aᵉ =
    unit-copartial-elementᵉ (fᵉ aᵉ)
```

### Copartial functions obtained from functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  copartial-function-functionᵉ : copartial-functionᵉ lzero Aᵉ Bᵉ
  copartial-function-functionᵉ =
    copartial-dependent-function-dependent-functionᵉ fᵉ
```

## Properties

### The underlying partial dependent function of a copartial dependent function

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ : copartial-dependent-functionᵉ l3ᵉ Aᵉ Bᵉ)
  where

  partial-dependent-function-copartial-dependent-functionᵉ :
    partial-dependent-functionᵉ l3ᵉ Aᵉ Bᵉ
  partial-dependent-function-copartial-dependent-functionᵉ aᵉ =
    partial-element-copartial-elementᵉ (fᵉ aᵉ)
```

### The underlying partial function of a copartial function

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : copartial-functionᵉ l3ᵉ Aᵉ Bᵉ)
  where

  partial-function-copartial-functionᵉ : partial-functionᵉ l3ᵉ Aᵉ Bᵉ
  partial-function-copartial-functionᵉ aᵉ =
    partial-element-copartial-elementᵉ (fᵉ aᵉ)
```

## See also

-ᵉ [Partialᵉ functions](foundation.partial-functions.mdᵉ)