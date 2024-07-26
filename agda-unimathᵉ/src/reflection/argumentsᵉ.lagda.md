# Arguments

```agda
module reflection.argumentsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ argumentᵉ to aᵉ functionᵉ isᵉ aᵉ termᵉ togetherᵉ with someᵉ informationᵉ aboutᵉ it.ᵉ Theᵉ
argumentᵉ hasᵉ threeᵉ propertiesᵉ:

1.ᵉ Visibilityᵉ: whetherᵉ theyᵉ areᵉ visible,ᵉ hidden,ᵉ orᵉ anᵉ instance
2.ᵉ Relevanceᵉ: whetherᵉ theyᵉ areᵉ relevantᵉ orᵉ notᵉ (see,ᵉ
   [docs](https://agda.readthedocs.io/en/latest/language/irrelevance.htmlᵉ))
3.ᵉ Quantityᵉ: whetherᵉ theyᵉ areᵉ run-timeᵉ relevantᵉ orᵉ notᵉ (see,ᵉ
   [docs](https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.htmlᵉ))

Theᵉ propertiesᵉ ofᵉ `Relevance-Argument-Agda`ᵉ andᵉ `Quantity-Argument-Agda`ᵉ areᵉ
combinedᵉ in one,ᵉ calledᵉ `Modality-Argument-Agda`.ᵉ

Forᵉ concreteᵉ examples,ᵉ seeᵉ
[`reflection.definitions`](reflection.definitions.md).ᵉ

## Definitions

```agda
data Visibility-Argument-Agdaᵉ : UUᵉ lzero where
  visible-Visibility-Argument-Agdaᵉ : Visibility-Argument-Agdaᵉ
  hidden-Visibility-Argument-Agdaᵉ : Visibility-Argument-Agdaᵉ
  instance-Visibility-Argument-Agdaᵉ : Visibility-Argument-Agdaᵉ

data Relevance-Argument-Agdaᵉ : UUᵉ lzero where
  relevant-Relevance-Argument-Agdaᵉ : Relevance-Argument-Agdaᵉ
  irrelevant-Relevance-Argument-Agdaᵉ : Relevance-Argument-Agdaᵉ

data Quantity-Argument-Agdaᵉ : UUᵉ lzero where
  zero-Quantity-Argument-Agdaᵉ : Quantity-Argument-Agdaᵉ
  omega-Quantity-Argument-Agdaᵉ : Quantity-Argument-Agdaᵉ

data Modality-Argument-Agdaᵉ : UUᵉ lzero where
  cons-Modality-Argument-Agdaᵉ :
    Relevance-Argument-Agdaᵉ → Quantity-Argument-Agdaᵉ → Modality-Argument-Agdaᵉ

data Info-Argument-Agdaᵉ : UUᵉ lzero where
  cons-Info-Argument-Agdaᵉ :
    Visibility-Argument-Agdaᵉ → Modality-Argument-Agdaᵉ → Info-Argument-Agdaᵉ

data Argument-Agdaᵉ {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) : UUᵉ lᵉ where
  cons-Argument-Agdaᵉ : Info-Argument-Agdaᵉ → Aᵉ → Argument-Agdaᵉ Aᵉ
```

<details><summary>Bindings</summary>

```agda





















```

</details>

## Helpers

Weᵉ createᵉ helperᵉ patternsᵉ forᵉ theᵉ twoᵉ mostᵉ commonᵉ typeᵉ ofᵉ arguments.ᵉ

```agda
--ᵉ visible-Argument-Agdaᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → Argument-Agdaᵉ Aᵉ
pattern visible-Argument-Agdaᵉ tᵉ =
  cons-Argument-Agdaᵉ
    ( cons-Info-Argument-Agdaᵉ
      ( visible-Visibility-Argument-Agdaᵉ)
      ( cons-Modality-Argument-Agdaᵉ
        ( relevant-Relevance-Argument-Agdaᵉ)
        ( omega-Quantity-Argument-Agdaᵉ)))
    ( tᵉ)

--ᵉ hidden-Argument-Agdaᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → Argument-Agdaᵉ Aᵉ
pattern hidden-Argument-Agdaᵉ tᵉ =
  cons-Argument-Agdaᵉ
    ( cons-Info-Argument-Agdaᵉ
      ( hidden-Visibility-Argument-Agdaᵉ)
      ( cons-Modality-Argument-Agdaᵉ
        ( relevant-Relevance-Argument-Agdaᵉ)
        ( omega-Quantity-Argument-Agdaᵉ)))
    ( tᵉ)
```