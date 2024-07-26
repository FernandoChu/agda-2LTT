# Injective maps

```agda
module foundation.injective-mapsᵉ where

open import foundation-core.injective-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.negationᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ **injective**ᵉ ifᵉ `fᵉ xᵉ ＝ᵉ fᵉ y`ᵉ impliesᵉ `xᵉ ＝ᵉ y`.ᵉ

## Warning

Theᵉ notionᵉ ofᵉ injectiveᵉ mapᵉ is,ᵉ however,ᵉ notᵉ homotopicallyᵉ coherent.ᵉ Itᵉ isᵉ fineᵉ
to useᵉ injectivityᵉ forᵉ mapsᵉ betweenᵉ [sets](foundation-core.sets.md),ᵉ butᵉ forᵉ
mapsᵉ betweenᵉ generalᵉ typesᵉ itᵉ isᵉ recommendedᵉ to useᵉ theᵉ notionᵉ ofᵉ
[embedding](foundation-core.embeddings.md).ᵉ

## Definitions

### Noninjective maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-not-injectiveᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-not-injectiveᵉ fᵉ = ¬ᵉ (is-injectiveᵉ fᵉ)
```

### Any map out of an empty type is injective

```agda
is-injective-is-emptyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-emptyᵉ Aᵉ → is-injectiveᵉ fᵉ
is-injective-is-emptyᵉ fᵉ is-empty-Aᵉ {xᵉ} = ex-falsoᵉ (is-empty-Aᵉ xᵉ)
```

### Any injective map between sets is an embedding

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-emb-is-injective'ᵉ :
      (is-set-Aᵉ : is-setᵉ Aᵉ) (is-set-Bᵉ : is-setᵉ Bᵉ) (fᵉ : Aᵉ → Bᵉ) →
      is-injectiveᵉ fᵉ → is-embᵉ fᵉ
    is-emb-is-injective'ᵉ is-set-Aᵉ is-set-Bᵉ fᵉ is-injective-fᵉ xᵉ yᵉ =
      is-equiv-has-converse-is-propᵉ
        ( is-set-Aᵉ xᵉ yᵉ)
        ( is-set-Bᵉ (fᵉ xᵉ) (fᵉ yᵉ))
        ( is-injective-fᵉ)

    is-emb-is-injectiveᵉ :
      {fᵉ : Aᵉ → Bᵉ} → is-setᵉ Bᵉ → is-injectiveᵉ fᵉ → is-embᵉ fᵉ
    is-emb-is-injectiveᵉ {fᵉ} Hᵉ Iᵉ =
      is-emb-is-injective'ᵉ (is-set-is-injectiveᵉ Hᵉ Iᵉ) Hᵉ fᵉ Iᵉ

    is-prop-map-is-injectiveᵉ :
      {fᵉ : Aᵉ → Bᵉ} → is-setᵉ Bᵉ → is-injectiveᵉ fᵉ → is-prop-mapᵉ fᵉ
    is-prop-map-is-injectiveᵉ {fᵉ} Hᵉ Iᵉ =
      is-prop-map-is-embᵉ (is-emb-is-injectiveᵉ Hᵉ Iᵉ)
```

### For a map between sets, being injective is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-prop-is-injectiveᵉ :
    is-setᵉ Aᵉ → (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-injectiveᵉ fᵉ)
  is-prop-is-injectiveᵉ Hᵉ fᵉ =
    is-prop-implicit-Πᵉ
      ( λ xᵉ →
        is-prop-implicit-Πᵉ
          ( λ yᵉ → is-prop-function-typeᵉ (Hᵉ xᵉ yᵉ)))

  is-injective-Propᵉ : is-setᵉ Aᵉ → (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (is-injective-Propᵉ Hᵉ fᵉ) = is-injectiveᵉ fᵉ
  pr2ᵉ (is-injective-Propᵉ Hᵉ fᵉ) = is-prop-is-injectiveᵉ Hᵉ fᵉ
```

## See also

-ᵉ [Embeddings](foundation-core.embeddings.mdᵉ)
-ᵉ [Path-cosplitᵉ maps](foundation.path-cosplit-maps.mdᵉ)