# Functoriality of set truncation

```agda
module foundation.functoriality-set-truncationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-truncationᵉ
open import foundation.imagesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.sliceᵉ
open import foundation.surjective-mapsᵉ
open import foundation.uniqueness-imageᵉ
open import foundation.uniqueness-set-truncationsᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universal-property-set-truncationᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ
[universalᵉ propertyᵉ ofᵉ theᵉ setᵉ truncation](foundation.universal-property-set-truncation.mdᵉ)
impliesᵉ thatᵉ theᵉ [setᵉ truncation](foundation.set-truncations.mdᵉ) actsᵉ
functoriallyᵉ onᵉ mapsᵉ betweenᵉ types.ᵉ

## Definitions

### The functorial action of set-truncations on maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    unique-map-trunc-Setᵉ :
      is-contrᵉ
        ( Σᵉ ( type-trunc-Setᵉ Aᵉ → type-trunc-Setᵉ Bᵉ)
            ( λ hᵉ → (hᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ (unit-trunc-Setᵉ ∘ᵉ fᵉ)))
    unique-map-trunc-Setᵉ = unique-map-truncᵉ zero-𝕋ᵉ fᵉ

  map-trunc-Setᵉ : type-trunc-Setᵉ Aᵉ → type-trunc-Setᵉ Bᵉ
  map-trunc-Setᵉ = map-truncᵉ zero-𝕋ᵉ fᵉ

  naturality-unit-trunc-Setᵉ :
    map-trunc-Setᵉ ∘ᵉ unit-trunc-Setᵉ ~ᵉ unit-trunc-Setᵉ ∘ᵉ fᵉ
  naturality-unit-trunc-Setᵉ = naturality-unit-truncᵉ zero-𝕋ᵉ fᵉ

  htpy-uniqueness-map-trunc-Setᵉ :
    (hᵉ : type-trunc-Setᵉ Aᵉ → type-trunc-Setᵉ Bᵉ) →
    (Hᵉ : hᵉ ∘ᵉ unit-trunc-Setᵉ ~ᵉ unit-trunc-Setᵉ ∘ᵉ fᵉ) →
    map-trunc-Setᵉ ~ᵉ hᵉ
  htpy-uniqueness-map-trunc-Setᵉ = htpy-uniqueness-map-truncᵉ zero-𝕋ᵉ fᵉ
```

### Functorial action of set-truncation on binary maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  binary-map-trunc-Setᵉ :
    type-trunc-Setᵉ Aᵉ → type-trunc-Setᵉ Bᵉ → type-trunc-Setᵉ Cᵉ
  binary-map-trunc-Setᵉ xᵉ yᵉ =
    map-trunc-Setᵉ
      ( λ (x'ᵉ ,ᵉ y'ᵉ) → fᵉ x'ᵉ y'ᵉ)
      ( map-inv-equiv-distributive-trunc-product-Setᵉ Aᵉ Bᵉ (xᵉ ,ᵉ yᵉ))
```

## Properties

### The functorial action of set truncations preserves identity maps

```agda
id-map-trunc-Setᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → map-trunc-Setᵉ (idᵉ {Aᵉ = Aᵉ}) ~ᵉ idᵉ
id-map-trunc-Setᵉ = id-map-truncᵉ zero-𝕋ᵉ
```

### The functorial action of set truncations preserves composition

```agda
preserves-comp-map-trunc-Setᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) →
  map-trunc-Setᵉ (gᵉ ∘ᵉ fᵉ) ~ᵉ (map-trunc-Setᵉ gᵉ ∘ᵉ map-trunc-Setᵉ fᵉ)
preserves-comp-map-trunc-Setᵉ = preserves-comp-map-truncᵉ zero-𝕋ᵉ
```

### The functorial action of set truncations preserves homotopies

```agda
htpy-trunc-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} →
  (fᵉ ~ᵉ gᵉ) → (map-trunc-Setᵉ fᵉ ~ᵉ map-trunc-Setᵉ gᵉ)
htpy-trunc-Setᵉ = htpy-truncᵉ
```

### The functorial action of set truncations preserves equivalences

```agda
map-equiv-trunc-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ ≃ᵉ Bᵉ) → type-trunc-Setᵉ Aᵉ → type-trunc-Setᵉ Bᵉ
map-equiv-trunc-Setᵉ = map-equiv-truncᵉ zero-𝕋ᵉ

is-equiv-map-trunc-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-equivᵉ (map-equiv-trunc-Setᵉ eᵉ)
is-equiv-map-trunc-Setᵉ = is-equiv-map-equiv-truncᵉ zero-𝕋ᵉ

equiv-trunc-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ ≃ᵉ Bᵉ) → (type-trunc-Setᵉ Aᵉ ≃ᵉ type-trunc-Setᵉ Bᵉ)
equiv-trunc-Setᵉ = equiv-truncᵉ zero-𝕋ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  square-trunc-Σ-Setᵉ :
    ( map-equiv-trunc-Σ-Setᵉ Aᵉ Bᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
    ( unit-trunc-Setᵉ ∘ᵉ totᵉ (λ xᵉ → unit-trunc-Setᵉ))
  square-trunc-Σ-Setᵉ =
    pr2ᵉ (centerᵉ (trunc-Σ-Setᵉ Aᵉ Bᵉ))

  htpy-map-equiv-trunc-Σ-Setᵉ :
    map-trunc-Setᵉ (totᵉ (λ xᵉ → unit-trunc-Setᵉ)) ~ᵉ (map-equiv-trunc-Σ-Setᵉ Aᵉ Bᵉ)
  htpy-map-equiv-trunc-Σ-Setᵉ =
    htpy-uniqueness-map-trunc-Setᵉ
      ( totᵉ (λ xᵉ → unit-trunc-Setᵉ))
      ( map-equiv-trunc-Σ-Setᵉ Aᵉ Bᵉ)
      ( square-trunc-Σ-Setᵉ)

  abstract
    is-equiv-map-trunc-tot-unit-trunc-Setᵉ :
      is-equivᵉ (map-trunc-Setᵉ (totᵉ (λ (xᵉ : Aᵉ) → unit-trunc-Setᵉ {Aᵉ = Bᵉ xᵉ})))
    is-equiv-map-trunc-tot-unit-trunc-Setᵉ =
      is-equiv-htpy-equivᵉ
        ( equiv-trunc-Σ-Setᵉ Aᵉ Bᵉ)
        ( htpy-map-equiv-trunc-Σ-Setᵉ)
```

### The set truncation functor preserves injective maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-injective-map-trunc-Setᵉ :
      is-injectiveᵉ fᵉ → is-injectiveᵉ (map-trunc-Setᵉ fᵉ)
    is-injective-map-trunc-Setᵉ Hᵉ {xᵉ} {yᵉ} =
      apply-dependent-universal-property-trunc-Set'ᵉ
        ( λ uᵉ →
          set-Propᵉ
            ( function-Propᵉ (map-trunc-Setᵉ fᵉ uᵉ ＝ᵉ map-trunc-Setᵉ fᵉ yᵉ)
            ( Id-Propᵉ (trunc-Setᵉ Aᵉ) uᵉ yᵉ)))
        ( λ aᵉ →
          apply-dependent-universal-property-trunc-Set'ᵉ
          ( λ vᵉ →
            set-Propᵉ
              ( function-Propᵉ
                ( map-trunc-Setᵉ fᵉ (unit-trunc-Setᵉ aᵉ) ＝ᵉ map-trunc-Setᵉ fᵉ vᵉ)
                ( Id-Propᵉ (trunc-Setᵉ Aᵉ) (unit-trunc-Setᵉ aᵉ) vᵉ)))
          ( λ bᵉ pᵉ →
            apply-universal-property-trunc-Propᵉ
              ( apply-effectiveness-unit-trunc-Setᵉ
                ( ( invᵉ (naturality-unit-trunc-Setᵉ fᵉ aᵉ)) ∙ᵉ
                  ( pᵉ ∙ᵉ (naturality-unit-trunc-Setᵉ fᵉ bᵉ))))
              ( Id-Propᵉ (trunc-Setᵉ Aᵉ) (unit-trunc-Setᵉ aᵉ) (unit-trunc-Setᵉ bᵉ))
              ( λ qᵉ → apᵉ unit-trunc-Setᵉ (Hᵉ qᵉ)))
          ( yᵉ))
        ( xᵉ)
```

### The set truncation functor preserves surjective maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-surjective-map-trunc-Setᵉ :
      is-surjectiveᵉ fᵉ → is-surjectiveᵉ (map-trunc-Setᵉ fᵉ)
    is-surjective-map-trunc-Setᵉ Hᵉ =
      apply-dependent-universal-property-trunc-Set'ᵉ
        ( λ xᵉ → set-Propᵉ (trunc-Propᵉ (fiberᵉ (map-trunc-Setᵉ fᵉ) xᵉ)))
        ( λ bᵉ →
          apply-universal-property-trunc-Propᵉ
            ( Hᵉ bᵉ)
            ( trunc-Propᵉ (fiberᵉ (map-trunc-Setᵉ fᵉ) (unit-trunc-Setᵉ bᵉ)))
            ( λ (aᵉ ,ᵉ pᵉ) →
              unit-trunc-Propᵉ
                ( ( unit-trunc-Setᵉ aᵉ) ,ᵉ
                  ( naturality-unit-trunc-Setᵉ fᵉ aᵉ ∙ᵉ apᵉ unit-trunc-Setᵉ pᵉ))))
```

### If the set truncation of a map `f` is surjective, then `f` is surjective

```agda
  abstract
    is-surjective-is-surjective-map-trunc-Setᵉ :
      is-surjectiveᵉ (map-trunc-Setᵉ fᵉ) → is-surjectiveᵉ fᵉ
    is-surjective-is-surjective-map-trunc-Setᵉ Hᵉ bᵉ =
      apply-universal-property-trunc-Propᵉ
        ( Hᵉ (unit-trunc-Setᵉ bᵉ))
        ( trunc-Propᵉ (fiberᵉ fᵉ bᵉ))
        ( λ (xᵉ ,ᵉ pᵉ) →
          apply-universal-property-trunc-Propᵉ
            ( is-surjective-unit-trunc-Setᵉ Aᵉ xᵉ)
            ( trunc-Propᵉ (fiberᵉ fᵉ bᵉ))
            ( λ where
              ( aᵉ ,ᵉ reflᵉ) →
                apply-universal-property-trunc-Propᵉ
                  ( apply-effectiveness-unit-trunc-Setᵉ
                    ( invᵉ (naturality-unit-trunc-Setᵉ fᵉ aᵉ) ∙ᵉ pᵉ))
                  ( trunc-Propᵉ (fiberᵉ fᵉ bᵉ))
                  ( λ qᵉ → unit-trunc-Propᵉ (aᵉ ,ᵉ qᵉ))))
```

### Set truncation preserves the image of a map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  inclusion-trunc-im-Setᵉ : type-trunc-Setᵉ (imᵉ fᵉ) → type-trunc-Setᵉ Bᵉ
  inclusion-trunc-im-Setᵉ = map-trunc-Setᵉ (inclusion-imᵉ fᵉ)

  abstract
    is-emb-inclusion-trunc-im-Setᵉ : is-embᵉ inclusion-trunc-im-Setᵉ
    is-emb-inclusion-trunc-im-Setᵉ =
      is-emb-is-injectiveᵉ
        ( is-set-type-trunc-Setᵉ)
        ( is-injective-map-trunc-Setᵉ
          ( inclusion-imᵉ fᵉ)
          ( is-injective-is-embᵉ (is-emb-inclusion-imᵉ fᵉ)))

  emb-trunc-im-Setᵉ : type-trunc-Setᵉ (imᵉ fᵉ) ↪ᵉ type-trunc-Setᵉ Bᵉ
  pr1ᵉ emb-trunc-im-Setᵉ = inclusion-trunc-im-Setᵉ
  pr2ᵉ emb-trunc-im-Setᵉ = is-emb-inclusion-trunc-im-Setᵉ

  abstract
    is-injective-inclusion-trunc-im-Setᵉ : is-injectiveᵉ inclusion-trunc-im-Setᵉ
    is-injective-inclusion-trunc-im-Setᵉ =
      is-injective-is-embᵉ is-emb-inclusion-trunc-im-Setᵉ

  map-hom-slice-trunc-im-Setᵉ : type-trunc-Setᵉ Aᵉ → type-trunc-Setᵉ (imᵉ fᵉ)
  map-hom-slice-trunc-im-Setᵉ = map-trunc-Setᵉ (map-unit-imᵉ fᵉ)

  triangle-hom-slice-trunc-im-Setᵉ :
    map-trunc-Setᵉ fᵉ ~ᵉ (inclusion-trunc-im-Setᵉ ∘ᵉ map-trunc-Setᵉ (map-unit-imᵉ fᵉ))
  triangle-hom-slice-trunc-im-Setᵉ =
    ( htpy-trunc-Setᵉ (triangle-unit-imᵉ fᵉ)) ∙hᵉ
    ( preserves-comp-map-trunc-Setᵉ (inclusion-imᵉ fᵉ) (map-unit-imᵉ fᵉ))

  hom-slice-trunc-im-Setᵉ : hom-sliceᵉ (map-trunc-Setᵉ fᵉ) inclusion-trunc-im-Setᵉ
  pr1ᵉ hom-slice-trunc-im-Setᵉ = map-hom-slice-trunc-im-Setᵉ
  pr2ᵉ hom-slice-trunc-im-Setᵉ = triangle-hom-slice-trunc-im-Setᵉ

  abstract
    is-surjective-map-hom-slice-trunc-im-Setᵉ :
      is-surjectiveᵉ map-hom-slice-trunc-im-Setᵉ
    is-surjective-map-hom-slice-trunc-im-Setᵉ =
      is-surjective-map-trunc-Setᵉ
        ( map-unit-imᵉ fᵉ)
        ( is-surjective-map-unit-imᵉ fᵉ)

  abstract
    is-image-trunc-im-Setᵉ :
      is-imageᵉ
        ( map-trunc-Setᵉ fᵉ)
        ( emb-trunc-im-Setᵉ)
        ( hom-slice-trunc-im-Setᵉ)
    is-image-trunc-im-Setᵉ =
      is-image-is-surjectiveᵉ
        ( map-trunc-Setᵉ fᵉ)
        ( emb-trunc-im-Setᵉ)
        ( hom-slice-trunc-im-Setᵉ)
        ( is-surjective-map-hom-slice-trunc-im-Setᵉ)

  abstract
    unique-equiv-trunc-im-Setᵉ :
      is-contrᵉ
        ( Σᵉ ( equiv-sliceᵉ
              ( inclusion-imᵉ (map-trunc-Setᵉ fᵉ))
              ( inclusion-trunc-im-Setᵉ))
            ( λ eᵉ →
              htpy-hom-sliceᵉ (map-trunc-Setᵉ fᵉ)
                ( inclusion-trunc-im-Setᵉ)
                ( comp-hom-sliceᵉ (map-trunc-Setᵉ fᵉ)
                  ( inclusion-imᵉ (map-trunc-Setᵉ fᵉ))
                  ( inclusion-trunc-im-Setᵉ)
                  ( hom-equiv-sliceᵉ
                    ( inclusion-imᵉ (map-trunc-Setᵉ fᵉ))
                    ( inclusion-trunc-im-Setᵉ)
                    ( eᵉ))
                  ( unit-imᵉ (map-trunc-Setᵉ fᵉ)))
                ( hom-slice-trunc-im-Setᵉ)))
    unique-equiv-trunc-im-Setᵉ =
      uniqueness-imᵉ
        ( map-trunc-Setᵉ fᵉ)
        ( emb-trunc-im-Setᵉ)
        ( hom-slice-trunc-im-Setᵉ)
        ( is-image-trunc-im-Setᵉ)

  equiv-slice-trunc-im-Setᵉ :
    equiv-sliceᵉ (inclusion-imᵉ (map-trunc-Setᵉ fᵉ)) inclusion-trunc-im-Setᵉ
  equiv-slice-trunc-im-Setᵉ = pr1ᵉ (centerᵉ unique-equiv-trunc-im-Setᵉ)

  equiv-trunc-im-Setᵉ : imᵉ (map-trunc-Setᵉ fᵉ) ≃ᵉ type-trunc-Setᵉ (imᵉ fᵉ)
  equiv-trunc-im-Setᵉ = pr1ᵉ equiv-slice-trunc-im-Setᵉ

  map-equiv-trunc-im-Setᵉ : imᵉ (map-trunc-Setᵉ fᵉ) → type-trunc-Setᵉ (imᵉ fᵉ)
  map-equiv-trunc-im-Setᵉ = map-equivᵉ equiv-trunc-im-Setᵉ

  triangle-trunc-im-Setᵉ :
    ( inclusion-imᵉ (map-trunc-Setᵉ fᵉ)) ~ᵉ
    ( inclusion-trunc-im-Setᵉ ∘ᵉ map-equiv-trunc-im-Setᵉ)
  triangle-trunc-im-Setᵉ = pr2ᵉ equiv-slice-trunc-im-Setᵉ

  htpy-hom-slice-trunc-im-Setᵉ :
    htpy-hom-sliceᵉ
      ( map-trunc-Setᵉ fᵉ)
      ( inclusion-trunc-im-Setᵉ)
      ( comp-hom-sliceᵉ
        ( map-trunc-Setᵉ fᵉ)
        ( inclusion-imᵉ (map-trunc-Setᵉ fᵉ))
        ( inclusion-trunc-im-Setᵉ)
        ( hom-equiv-sliceᵉ
          ( inclusion-imᵉ (map-trunc-Setᵉ fᵉ))
          ( inclusion-trunc-im-Setᵉ)
          ( equiv-slice-trunc-im-Setᵉ))
        ( unit-imᵉ (map-trunc-Setᵉ fᵉ)))
      ( hom-slice-trunc-im-Setᵉ)
  htpy-hom-slice-trunc-im-Setᵉ =
    pr2ᵉ (centerᵉ unique-equiv-trunc-im-Setᵉ)

  htpy-map-hom-slice-trunc-im-Setᵉ :
    ( map-equiv-trunc-im-Setᵉ ∘ᵉ (map-unit-imᵉ (map-trunc-Setᵉ fᵉ))) ~ᵉ
    ( map-hom-slice-trunc-im-Setᵉ)
  htpy-map-hom-slice-trunc-im-Setᵉ =
    pr1ᵉ htpy-hom-slice-trunc-im-Setᵉ

  tetrahedron-map-hom-slice-trunc-im-Setᵉ :
    ( ( triangle-trunc-im-Setᵉ ·rᵉ map-unit-imᵉ (map-trunc-Setᵉ fᵉ)) ∙hᵉ
      ( inclusion-trunc-im-Setᵉ ·lᵉ htpy-map-hom-slice-trunc-im-Setᵉ)) ~ᵉ
    ( triangle-hom-slice-trunc-im-Setᵉ)
  tetrahedron-map-hom-slice-trunc-im-Setᵉ =
    pr2ᵉ htpy-hom-slice-trunc-im-Setᵉ

  unit-im-map-trunc-Setᵉ :
    imᵉ fᵉ → imᵉ (map-trunc-Setᵉ fᵉ)
  pr1ᵉ (unit-im-map-trunc-Setᵉ xᵉ) = unit-trunc-Setᵉ (pr1ᵉ xᵉ)
  pr2ᵉ (unit-im-map-trunc-Setᵉ xᵉ) =
    apply-universal-property-trunc-Propᵉ (pr2ᵉ xᵉ)
      ( trunc-Propᵉ (fiberᵉ (map-trunc-Setᵉ fᵉ) (unit-trunc-Setᵉ (pr1ᵉ xᵉ))))
      ( λ uᵉ →
        unit-trunc-Propᵉ
          ( ( unit-trunc-Setᵉ (pr1ᵉ uᵉ)) ,ᵉ
            ( naturality-unit-trunc-Setᵉ fᵉ (pr1ᵉ uᵉ) ∙ᵉ
              apᵉ unit-trunc-Setᵉ (pr2ᵉ uᵉ))))

  left-square-unit-im-map-trunc-Setᵉ :
    ( map-unit-imᵉ (map-trunc-Setᵉ fᵉ) ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
    ( unit-im-map-trunc-Setᵉ ∘ᵉ map-unit-imᵉ fᵉ)
  left-square-unit-im-map-trunc-Setᵉ aᵉ =
    eq-Eq-imᵉ
      ( map-trunc-Setᵉ fᵉ)
      ( map-unit-imᵉ (map-trunc-Setᵉ fᵉ) (unit-trunc-Setᵉ aᵉ))
      ( unit-im-map-trunc-Setᵉ (map-unit-imᵉ fᵉ aᵉ))
      ( naturality-unit-trunc-Setᵉ fᵉ aᵉ)

  right-square-unit-im-map-trunc-Setᵉ :
    ( inclusion-imᵉ (map-trunc-Setᵉ fᵉ) ∘ᵉ unit-im-map-trunc-Setᵉ) ~ᵉ
    ( unit-trunc-Setᵉ ∘ᵉ inclusion-imᵉ fᵉ)
  right-square-unit-im-map-trunc-Setᵉ xᵉ = reflᵉ

  abstract
    is-set-truncation-im-map-trunc-Setᵉ :
      is-set-truncationᵉ
        ( im-Setᵉ (trunc-Setᵉ Bᵉ) (map-trunc-Setᵉ fᵉ))
        ( unit-im-map-trunc-Setᵉ)
    is-set-truncation-im-map-trunc-Setᵉ =
      is-set-truncation-is-equiv-is-set-truncationᵉ
        ( im-Setᵉ (trunc-Setᵉ Bᵉ) (map-trunc-Setᵉ fᵉ))
        ( unit-im-map-trunc-Setᵉ)
        ( trunc-Setᵉ (imᵉ fᵉ))
        ( unit-trunc-Setᵉ)
        ( λ bᵉ →
          is-injective-inclusion-trunc-im-Setᵉ
            ( ( invᵉ (triangle-trunc-im-Setᵉ (unit-im-map-trunc-Setᵉ bᵉ))) ∙ᵉ
              ( invᵉ (naturality-unit-trunc-Setᵉ (inclusion-imᵉ fᵉ) bᵉ))))
        ( is-set-truncation-trunc-Setᵉ (imᵉ fᵉ))
        ( is-equiv-map-equivᵉ equiv-trunc-im-Setᵉ)
```