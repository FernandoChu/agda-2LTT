# The maybe modality

```agda
module foundation.maybeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.negationᵉ
```

</details>

## Idea

Theᵉ maybeᵉ modalityᵉ isᵉ anᵉ operationᵉ onᵉ typesᵉ thatᵉ addsᵉ oneᵉ point.ᵉ Thisᵉ isᵉ used,ᵉ
forᵉ example,ᵉ to defineᵉ partialᵉ functions,ᵉ where aᵉ partialᵉ functionᵉ `fᵉ : Xᵉ ⇀ᵉ Y`ᵉ
isᵉ aᵉ mapᵉ `fᵉ : Xᵉ → Maybeᵉ Y`.ᵉ

## Definitions

### The Maybe modality

```agda
Maybeᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
Maybeᵉ Xᵉ = Xᵉ +ᵉ unitᵉ

data Maybe'ᵉ {lᵉ} (Xᵉ : UUᵉ lᵉ) : UUᵉ lᵉ where
  unit-Maybe'ᵉ : Xᵉ → Maybe'ᵉ Xᵉ
  exception-Maybe'ᵉ : Maybe'ᵉ Xᵉ



unit-Maybeᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → Xᵉ → Maybeᵉ Xᵉ
unit-Maybeᵉ = inlᵉ

exception-Maybeᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → Maybeᵉ Xᵉ
exception-Maybeᵉ {lᵉ} {Xᵉ} = inrᵉ starᵉ
```

### The predicate of being an exception

```agda
is-exception-Maybeᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → Maybeᵉ Xᵉ → UUᵉ lᵉ
is-exception-Maybeᵉ {lᵉ} {Xᵉ} xᵉ = (xᵉ ＝ᵉ exception-Maybeᵉ)

is-not-exception-Maybeᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → Maybeᵉ Xᵉ → UUᵉ lᵉ
is-not-exception-Maybeᵉ xᵉ = ¬ᵉ (is-exception-Maybeᵉ xᵉ)
```

### The predicate of being a value

```agda
is-value-Maybeᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → Maybeᵉ Xᵉ → UUᵉ lᵉ
is-value-Maybeᵉ {lᵉ} {Xᵉ} xᵉ = Σᵉ Xᵉ (λ yᵉ → inlᵉ yᵉ ＝ᵉ xᵉ)

value-is-value-Maybeᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : Maybeᵉ Xᵉ) → is-value-Maybeᵉ xᵉ → Xᵉ
value-is-value-Maybeᵉ xᵉ = pr1ᵉ

eq-is-value-Maybeᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : Maybeᵉ Xᵉ) (Hᵉ : is-value-Maybeᵉ xᵉ) →
  inlᵉ (value-is-value-Maybeᵉ xᵉ Hᵉ) ＝ᵉ xᵉ
eq-is-value-Maybeᵉ xᵉ Hᵉ = pr2ᵉ Hᵉ
```

### Maybe structure on a type

```agda
maybe-structureᵉ : {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → UUᵉ (lsuc l1ᵉ)
maybe-structureᵉ {l1ᵉ} Xᵉ = Σᵉ (UUᵉ l1ᵉ) (λ Yᵉ → Maybeᵉ Yᵉ ≃ᵉ Xᵉ)
```

## Properties

### The unit of Maybe is an embedding

```agda
abstract
  is-emb-unit-Maybeᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-embᵉ (unit-Maybeᵉ {Xᵉ = Xᵉ})
  is-emb-unit-Maybeᵉ {lᵉ} {Xᵉ} = is-emb-inlᵉ Xᵉ unitᵉ

emb-unit-Maybeᵉ : {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → Xᵉ ↪ᵉ Maybeᵉ Xᵉ
pr1ᵉ (emb-unit-Maybeᵉ Xᵉ) = unit-Maybeᵉ
pr2ᵉ (emb-unit-Maybeᵉ Xᵉ) = is-emb-unit-Maybeᵉ

abstract
  is-injective-unit-Maybeᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-injectiveᵉ (unit-Maybeᵉ {Xᵉ = Xᵉ})
  is-injective-unit-Maybeᵉ = is-injective-inlᵉ
```

### Being an exception is decidable

```agda
is-decidable-is-exception-Maybeᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : Maybeᵉ Xᵉ) → is-decidableᵉ (is-exception-Maybeᵉ xᵉ)
is-decidable-is-exception-Maybeᵉ {lᵉ} {Xᵉ} (inlᵉ xᵉ) =
  inrᵉ (λ pᵉ → ex-falsoᵉ (is-empty-eq-coproduct-inl-inrᵉ xᵉ starᵉ pᵉ))
is-decidable-is-exception-Maybeᵉ (inrᵉ starᵉ) = inlᵉ reflᵉ

is-decidable-is-not-exception-Maybeᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : Maybeᵉ Xᵉ) → is-decidableᵉ (is-not-exception-Maybeᵉ xᵉ)
is-decidable-is-not-exception-Maybeᵉ xᵉ =
  is-decidable-negᵉ (is-decidable-is-exception-Maybeᵉ xᵉ)
```

### The values of the unit of the Maybe modality are not exceptions

```agda
abstract
  is-not-exception-unit-Maybeᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : Xᵉ) → is-not-exception-Maybeᵉ (unit-Maybeᵉ xᵉ)
  is-not-exception-unit-Maybeᵉ {lᵉ} {Xᵉ} xᵉ ()
```

### For any element of type `Maybe X` we can decide whether it is a value or an exception

```agda
decide-Maybeᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : Maybeᵉ Xᵉ) → is-value-Maybeᵉ xᵉ +ᵉ is-exception-Maybeᵉ xᵉ
decide-Maybeᵉ (inlᵉ xᵉ) = inlᵉ (pairᵉ xᵉ reflᵉ)
decide-Maybeᵉ (inrᵉ starᵉ) = inrᵉ reflᵉ
```

### Values are not exceptions

```agda
abstract
  is-not-exception-is-value-Maybeᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Maybeᵉ Xᵉ) →
    is-value-Maybeᵉ xᵉ → is-not-exception-Maybeᵉ xᵉ
  is-not-exception-is-value-Maybeᵉ {l1ᵉ} {Xᵉ} .(inlᵉ xᵉ) (pairᵉ xᵉ reflᵉ) =
    is-not-exception-unit-Maybeᵉ xᵉ
```

### If a point is not an exception, then it is a value

```agda
is-value-is-not-exception-Maybeᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Maybeᵉ Xᵉ) →
  is-not-exception-Maybeᵉ xᵉ → is-value-Maybeᵉ xᵉ
is-value-is-not-exception-Maybeᵉ xᵉ Hᵉ =
  map-right-unit-law-coproduct-is-emptyᵉ
    ( is-value-Maybeᵉ xᵉ)
    ( is-exception-Maybeᵉ xᵉ)
    ( Hᵉ)
    ( decide-Maybeᵉ xᵉ)

value-is-not-exception-Maybeᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Maybeᵉ Xᵉ) → is-not-exception-Maybeᵉ xᵉ → Xᵉ
value-is-not-exception-Maybeᵉ xᵉ Hᵉ =
  value-is-value-Maybeᵉ xᵉ (is-value-is-not-exception-Maybeᵉ xᵉ Hᵉ)

eq-is-not-exception-Maybeᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Maybeᵉ Xᵉ) (Hᵉ : is-not-exception-Maybeᵉ xᵉ) →
  inlᵉ (value-is-not-exception-Maybeᵉ xᵉ Hᵉ) ＝ᵉ xᵉ
eq-is-not-exception-Maybeᵉ xᵉ Hᵉ =
  eq-is-value-Maybeᵉ xᵉ (is-value-is-not-exception-Maybeᵉ xᵉ Hᵉ)
```

### The two definitions of `Maybe` are equal

```agda
equiv-Maybe-Maybe'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → Maybeᵉ Xᵉ ≃ᵉ Maybe'ᵉ Xᵉ
pr1ᵉ equiv-Maybe-Maybe'ᵉ (inlᵉ xᵉ) = unit-Maybe'ᵉ xᵉ
pr1ᵉ equiv-Maybe-Maybe'ᵉ (inrᵉ starᵉ) = exception-Maybe'ᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ equiv-Maybe-Maybe'ᵉ)) (unit-Maybe'ᵉ xᵉ) = inlᵉ xᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ equiv-Maybe-Maybe'ᵉ)) exception-Maybe'ᵉ = inrᵉ starᵉ
pr2ᵉ (pr1ᵉ (pr2ᵉ equiv-Maybe-Maybe'ᵉ)) (unit-Maybe'ᵉ xᵉ) = reflᵉ
pr2ᵉ (pr1ᵉ (pr2ᵉ equiv-Maybe-Maybe'ᵉ)) exception-Maybe'ᵉ = reflᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ equiv-Maybe-Maybe'ᵉ)) (unit-Maybe'ᵉ xᵉ) = inlᵉ xᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ equiv-Maybe-Maybe'ᵉ)) exception-Maybe'ᵉ = inrᵉ starᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ equiv-Maybe-Maybe'ᵉ)) (inlᵉ xᵉ) = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ equiv-Maybe-Maybe'ᵉ)) (inrᵉ starᵉ) = reflᵉ
```