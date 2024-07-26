# Injective maps

```agda
module foundation-core.injective-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ **injective**ᵉ ifᵉ `fᵉ xᵉ ＝ᵉ fᵉ y`ᵉ impliesᵉ `xᵉ ＝ᵉ y`.ᵉ

## Warning

Theᵉ notionᵉ ofᵉ injectiveᵉ mapᵉ is,ᵉ however,ᵉ notᵉ homotopicallyᵉ coherent.ᵉ Itᵉ isᵉ fineᵉ
to useᵉ injectivityᵉ forᵉ mapsᵉ betweenᵉ [sets](foundation-core.sets.md),ᵉ butᵉ forᵉ
mapsᵉ betweenᵉ generalᵉ typesᵉ itᵉ isᵉ recommendedᵉ to useᵉ theᵉ notionᵉ ofᵉ
[embedding](foundation-core.embeddings.md).ᵉ

## Definition

```agda
is-injectiveᵉ : {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-injectiveᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} fᵉ = {xᵉ yᵉ : Aᵉ} → fᵉ xᵉ ＝ᵉ fᵉ yᵉ → xᵉ ＝ᵉ yᵉ

injectionᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
injectionᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) is-injectiveᵉ
```

## Examples

### The identity function is injective

```agda
is-injective-idᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-injectiveᵉ (idᵉ {Aᵉ = Aᵉ})
is-injective-idᵉ pᵉ = pᵉ

id-injectionᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → injectionᵉ Aᵉ Aᵉ
pr1ᵉ id-injectionᵉ = idᵉ
pr2ᵉ id-injectionᵉ = is-injective-idᵉ
```

## Properties

### If a composite is injective, then so is its right factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-injective-right-factorᵉ :
    (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-injectiveᵉ (gᵉ ∘ᵉ hᵉ) → is-injectiveᵉ hᵉ
  is-injective-right-factorᵉ gᵉ hᵉ is-inj-ghᵉ pᵉ = is-inj-ghᵉ (apᵉ gᵉ pᵉ)

  is-injective-top-map-triangleᵉ :
    (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
    is-injectiveᵉ fᵉ → is-injectiveᵉ hᵉ
  is-injective-top-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ is-inj-fᵉ {xᵉ} {x'ᵉ} pᵉ =
    is-inj-fᵉ {xᵉ} {x'ᵉ} ((Hᵉ xᵉ) ∙ᵉ ((apᵉ gᵉ pᵉ) ∙ᵉ (invᵉ (Hᵉ x'ᵉ))))
```

### Injective maps are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-injective-compᵉ :
    {gᵉ : Bᵉ → Cᵉ} {hᵉ : Aᵉ → Bᵉ} →
    is-injectiveᵉ hᵉ → is-injectiveᵉ gᵉ → is-injectiveᵉ (gᵉ ∘ᵉ hᵉ)
  is-injective-compᵉ is-inj-hᵉ is-inj-gᵉ = is-inj-hᵉ ∘ᵉ is-inj-gᵉ

  is-injective-left-map-triangleᵉ :
    (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ) → fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ) →
    is-injectiveᵉ hᵉ → is-injectiveᵉ gᵉ → is-injectiveᵉ fᵉ
  is-injective-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ is-inj-hᵉ is-inj-gᵉ {xᵉ} {x'ᵉ} pᵉ =
    is-inj-hᵉ (is-inj-gᵉ ((invᵉ (Hᵉ xᵉ)) ∙ᵉ (pᵉ ∙ᵉ (Hᵉ x'ᵉ))))
```

### Equivalences are injective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-injective-is-equivᵉ : {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-injectiveᵉ fᵉ
  is-injective-is-equivᵉ {fᵉ} Hᵉ =
    is-injective-retractionᵉ fᵉ (retraction-is-equivᵉ Hᵉ)

  is-injective-equivᵉ : (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-injectiveᵉ (map-equivᵉ eᵉ)
  is-injective-equivᵉ eᵉ = is-injective-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

abstract
  is-injective-map-inv-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-injectiveᵉ (map-inv-equivᵉ eᵉ)
  is-injective-map-inv-equivᵉ eᵉ =
    is-injective-is-equivᵉ (is-equiv-map-inv-equivᵉ eᵉ)
```

### Injective maps that have a section are equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-equiv-is-injectiveᵉ : {fᵉ : Aᵉ → Bᵉ} → sectionᵉ fᵉ → is-injectiveᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-injectiveᵉ {fᵉ} (pairᵉ gᵉ Gᵉ) Hᵉ =
    is-equiv-is-invertibleᵉ gᵉ Gᵉ (λ xᵉ → Hᵉ (Gᵉ (fᵉ xᵉ)))
```

### Any embedding is injective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-injective-is-embᵉ : {fᵉ : Aᵉ → Bᵉ} → is-embᵉ fᵉ → is-injectiveᵉ fᵉ
  is-injective-is-embᵉ is-emb-fᵉ {xᵉ} {yᵉ} = map-inv-is-equivᵉ (is-emb-fᵉ xᵉ yᵉ)

  is-injective-embᵉ : (eᵉ : Aᵉ ↪ᵉ Bᵉ) → is-injectiveᵉ (map-embᵉ eᵉ)
  is-injective-embᵉ eᵉ {xᵉ} {yᵉ} = map-inv-is-equivᵉ (is-emb-map-embᵉ eᵉ xᵉ yᵉ)
```

### Any map out of a contractible type is injective

```agda
is-injective-is-contrᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-contrᵉ Aᵉ → is-injectiveᵉ fᵉ
is-injective-is-contrᵉ fᵉ Hᵉ pᵉ = eq-is-contrᵉ Hᵉ
```

## See also

-ᵉ [Embeddings](foundation-core.embeddings.mdᵉ)
-ᵉ [Path-cosplitᵉ maps](foundation.path-cosplit-maps.mdᵉ)