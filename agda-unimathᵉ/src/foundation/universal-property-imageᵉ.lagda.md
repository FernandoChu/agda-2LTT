# The universal property of the image of a map

```agda
module foundation.universal-property-imageᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.imagesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.sliceᵉ
open import foundation.surjective-mapsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universal-property-family-of-fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "universalᵉ propertyᵉ ofᵉ theᵉ image"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ Agda=is-imageᵉ}}
ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → X`ᵉ statesᵉ thatᵉ theᵉ [image](foundation.images.mdᵉ) isᵉ theᵉ leastᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ `X`ᵉ containingᵉ allᵉ theᵉ valuesᵉ ofᵉ `f`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (iᵉ : Bᵉ ↪ᵉ Xᵉ) (qᵉ : hom-sliceᵉ fᵉ (map-embᵉ iᵉ))
  where

  precomp-embᵉ :
    {l4ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} (jᵉ : Cᵉ ↪ᵉ Xᵉ) →
    hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ jᵉ) → hom-sliceᵉ fᵉ (map-embᵉ jᵉ)
  pr1ᵉ (precomp-embᵉ jᵉ rᵉ) =
    map-hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ jᵉ) rᵉ ∘ᵉ map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ
  pr2ᵉ (precomp-embᵉ jᵉ rᵉ) =
    ( triangle-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) ∙hᵉ
    ( ( triangle-hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ jᵉ) rᵉ) ·rᵉ
      ( map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ))

  is-imageᵉ : UUωᵉ
  is-imageᵉ = {lᵉ : Level} (Cᵉ : UUᵉ lᵉ) (jᵉ : Cᵉ ↪ᵉ Xᵉ) → is-equivᵉ (precomp-embᵉ jᵉ)
```

### Simplified variant of `is-image`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (iᵉ : Bᵉ ↪ᵉ Xᵉ) (qᵉ : hom-sliceᵉ fᵉ (map-embᵉ iᵉ))
  where

  is-image'ᵉ : UUωᵉ
  is-image'ᵉ =
    {lᵉ : Level} (Cᵉ : UUᵉ lᵉ) (jᵉ : Cᵉ ↪ᵉ Xᵉ) →
    hom-sliceᵉ fᵉ (map-embᵉ jᵉ) → hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ jᵉ)
```

### The universal property of the image subtype

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  (Bᵉ : subtypeᵉ l3ᵉ Xᵉ)
  where

  is-image-subtypeᵉ : UUωᵉ
  is-image-subtypeᵉ =
    {lᵉ : Level} (Cᵉ : subtypeᵉ lᵉ Xᵉ) → (Bᵉ ⊆ᵉ Cᵉ) ↔ᵉ ((aᵉ : Aᵉ) → is-in-subtypeᵉ Cᵉ (fᵉ aᵉ))
```

## Properties

### The two universal properties of the image of a map are equivalent

```agda
abstract
  is-image-is-image'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    { Bᵉ : UUᵉ l3ᵉ} (iᵉ : Bᵉ ↪ᵉ Xᵉ) (qᵉ : hom-sliceᵉ fᵉ (map-embᵉ iᵉ)) →
    is-image'ᵉ fᵉ iᵉ qᵉ → is-imageᵉ fᵉ iᵉ qᵉ
  is-image-is-image'ᵉ fᵉ iᵉ qᵉ up'ᵉ Cᵉ jᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-hom-sliceᵉ (map-embᵉ iᵉ) jᵉ)
      ( is-prop-hom-sliceᵉ fᵉ jᵉ)
      ( up'ᵉ Cᵉ jᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (iᵉ : Bᵉ ↪ᵉ Xᵉ) (qᵉ : hom-sliceᵉ fᵉ (map-embᵉ iᵉ))
  (Hᵉ : is-imageᵉ fᵉ iᵉ qᵉ)
  {Cᵉ : UUᵉ l4ᵉ} (jᵉ : Cᵉ ↪ᵉ Xᵉ) (rᵉ : hom-sliceᵉ fᵉ (map-embᵉ jᵉ))
  where

  abstract
    universal-property-imageᵉ :
      is-contrᵉ
        ( Σᵉ ( hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ jᵉ))
            ( λ hᵉ →
              htpy-hom-sliceᵉ fᵉ
                ( map-embᵉ jᵉ)
                ( comp-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) (map-embᵉ jᵉ) hᵉ qᵉ)
                ( rᵉ)))
    universal-property-imageᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ (precomp-embᵉ fᵉ iᵉ qᵉ jᵉ) rᵉ)
        ( equiv-totᵉ
          ( λ hᵉ →
            extensionality-hom-sliceᵉ fᵉ (map-embᵉ jᵉ) (precomp-embᵉ fᵉ iᵉ qᵉ jᵉ hᵉ) rᵉ))
        ( is-contr-map-is-equivᵉ (Hᵉ Cᵉ jᵉ) rᵉ)

  hom-slice-universal-property-imageᵉ : hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ jᵉ)
  hom-slice-universal-property-imageᵉ =
    pr1ᵉ (centerᵉ universal-property-imageᵉ)

  map-hom-slice-universal-property-imageᵉ : Bᵉ → Cᵉ
  map-hom-slice-universal-property-imageᵉ =
    map-hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ jᵉ) hom-slice-universal-property-imageᵉ

  triangle-hom-slice-universal-property-imageᵉ :
    map-embᵉ iᵉ ~ᵉ map-embᵉ jᵉ ∘ᵉ map-hom-slice-universal-property-imageᵉ
  triangle-hom-slice-universal-property-imageᵉ =
    triangle-hom-sliceᵉ
      ( map-embᵉ iᵉ)
      ( map-embᵉ jᵉ)
      ( hom-slice-universal-property-imageᵉ)

  htpy-hom-slice-universal-property-imageᵉ :
    htpy-hom-sliceᵉ fᵉ
      ( map-embᵉ jᵉ)
      ( comp-hom-sliceᵉ fᵉ
        ( map-embᵉ iᵉ)
        ( map-embᵉ jᵉ)
        ( hom-slice-universal-property-imageᵉ)
        ( qᵉ))
      ( rᵉ)
  htpy-hom-slice-universal-property-imageᵉ =
    pr2ᵉ (centerᵉ universal-property-imageᵉ)

  abstract
    htpy-map-hom-slice-universal-property-imageᵉ :
      map-hom-sliceᵉ fᵉ
        ( map-embᵉ jᵉ)
        ( comp-hom-sliceᵉ fᵉ
          ( map-embᵉ iᵉ)
          ( map-embᵉ jᵉ)
          ( hom-slice-universal-property-imageᵉ)
          ( qᵉ)) ~ᵉ
      map-hom-sliceᵉ fᵉ (map-embᵉ jᵉ) rᵉ
    htpy-map-hom-slice-universal-property-imageᵉ =
      pr1ᵉ htpy-hom-slice-universal-property-imageᵉ

    tetrahedron-hom-slice-universal-property-imageᵉ :
      ( ( ( triangle-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) ∙hᵉ
          ( ( triangle-hom-slice-universal-property-imageᵉ) ·rᵉ
            ( map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ))) ∙hᵉ
        ( map-embᵉ jᵉ ·lᵉ htpy-map-hom-slice-universal-property-imageᵉ)) ~ᵉ
      ( triangle-hom-sliceᵉ fᵉ (map-embᵉ jᵉ) rᵉ)
    tetrahedron-hom-slice-universal-property-imageᵉ =
      pr2ᵉ htpy-hom-slice-universal-property-imageᵉ
```

### The image subtype satisfies the universal property of the image subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  where abstract

  forward-implication-is-image-subtype-subtype-imᵉ :
    {lᵉ : Level} (Bᵉ : subtypeᵉ lᵉ Xᵉ) →
    subtype-imᵉ fᵉ ⊆ᵉ Bᵉ → (aᵉ : Aᵉ) → is-in-subtypeᵉ Bᵉ (fᵉ aᵉ)
  forward-implication-is-image-subtype-subtype-imᵉ Bᵉ Hᵉ aᵉ =
    Hᵉ (fᵉ aᵉ) (unit-trunc-Propᵉ (aᵉ ,ᵉ reflᵉ))

  backward-implication-is-image-subtype-subtype-imᵉ :
    {lᵉ : Level} (Bᵉ : subtypeᵉ lᵉ Xᵉ) →
    ((aᵉ : Aᵉ) → is-in-subtypeᵉ Bᵉ (fᵉ aᵉ)) → subtype-imᵉ fᵉ ⊆ᵉ Bᵉ
  backward-implication-is-image-subtype-subtype-imᵉ Bᵉ Hᵉ xᵉ Kᵉ =
    apply-universal-property-trunc-Propᵉ Kᵉ (Bᵉ xᵉ) (λ where (aᵉ ,ᵉ reflᵉ) → Hᵉ aᵉ)

  is-image-subtype-subtype-imᵉ : is-image-subtypeᵉ fᵉ (subtype-imᵉ fᵉ)
  pr1ᵉ (is-image-subtype-subtype-imᵉ Bᵉ) =
    forward-implication-is-image-subtype-subtype-imᵉ Bᵉ
  pr2ᵉ (is-image-subtype-subtype-imᵉ Bᵉ) =
    backward-implication-is-image-subtype-subtype-imᵉ Bᵉ
```

### The identity embedding is the image inclusion of any map that has a section

```agda
abstract
  is-image-has-sectionᵉ :
    (lᵉ : Level) {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    sectionᵉ fᵉ → is-imageᵉ fᵉ id-embᵉ (fᵉ ,ᵉ refl-htpyᵉ)
  is-image-has-sectionᵉ lᵉ fᵉ (gᵉ ,ᵉ Hᵉ) =
    is-image-is-image'ᵉ
      ( fᵉ)
      ( id-embᵉ)
      ( fᵉ ,ᵉ refl-htpyᵉ)
      ( λ Bᵉ mᵉ hᵉ → ((pr1ᵉ hᵉ ∘ᵉ gᵉ) ,ᵉ (λ xᵉ → invᵉ (Hᵉ xᵉ) ∙ᵉ pr2ᵉ hᵉ (gᵉ xᵉ))))
```

### Any embedding is its own image inclusion

```agda
abstract
  is-image-is-embᵉ :
    (lᵉ : Level) {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    (Hᵉ : is-embᵉ fᵉ) → is-imageᵉ fᵉ (fᵉ ,ᵉ Hᵉ) (idᵉ ,ᵉ refl-htpyᵉ)
  is-image-is-embᵉ lᵉ fᵉ Hᵉ =
    is-image-is-image'ᵉ fᵉ (fᵉ ,ᵉ Hᵉ) (idᵉ ,ᵉ refl-htpyᵉ) (λ Bᵉ mᵉ hᵉ → hᵉ)
```

### The image of `f` is the image of `f`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ)
  (mᵉ : Bᵉ ↪ᵉ Xᵉ) (hᵉ : hom-sliceᵉ fᵉ (map-embᵉ mᵉ))
  where abstract

  fiberwise-map-is-image-imᵉ :
    (xᵉ : Xᵉ) → type-trunc-Propᵉ (fiberᵉ fᵉ xᵉ) → fiberᵉ (map-embᵉ mᵉ) xᵉ
  fiberwise-map-is-image-imᵉ xᵉ =
    map-universal-property-trunc-Propᵉ
      { Aᵉ = fiberᵉ fᵉ xᵉ}
      ( fiber-emb-Propᵉ mᵉ xᵉ)
      ( λ tᵉ →
        ( map-hom-sliceᵉ fᵉ (map-embᵉ mᵉ) hᵉ (pr1ᵉ tᵉ)) ,ᵉ
        ( ( invᵉ (triangle-hom-sliceᵉ fᵉ (map-embᵉ mᵉ) hᵉ (pr1ᵉ tᵉ))) ∙ᵉ ( pr2ᵉ tᵉ)))

  map-is-image-imᵉ : imᵉ fᵉ → Bᵉ
  map-is-image-imᵉ (xᵉ ,ᵉ tᵉ) = pr1ᵉ (fiberwise-map-is-image-imᵉ xᵉ tᵉ)

  inv-triangle-is-image-imᵉ :
    map-embᵉ mᵉ ∘ᵉ map-is-image-imᵉ ~ᵉ inclusion-imᵉ fᵉ
  inv-triangle-is-image-imᵉ (xᵉ ,ᵉ tᵉ) = pr2ᵉ (fiberwise-map-is-image-imᵉ xᵉ tᵉ)

  triangle-is-image-imᵉ :
    inclusion-imᵉ fᵉ ~ᵉ map-embᵉ mᵉ ∘ᵉ map-is-image-imᵉ
  triangle-is-image-imᵉ = inv-htpyᵉ inv-triangle-is-image-imᵉ

abstract
  is-image-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    is-imageᵉ fᵉ (emb-imᵉ fᵉ) (unit-imᵉ fᵉ)
  is-image-imᵉ fᵉ =
    is-image-is-image'ᵉ
      ( fᵉ)
      ( emb-imᵉ fᵉ)
      ( unit-imᵉ fᵉ)
      ( λ Bᵉ mᵉ hᵉ → (map-is-image-imᵉ fᵉ mᵉ hᵉ ,ᵉ triangle-is-image-imᵉ fᵉ mᵉ hᵉ))
```

### A factorization of a map through an embedding is the image factorization if and only if the right factor is surjective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (iᵉ : Bᵉ ↪ᵉ Xᵉ) (qᵉ : hom-sliceᵉ fᵉ (map-embᵉ iᵉ))
  where abstract

  is-surjective-is-imageᵉ :
    is-imageᵉ fᵉ iᵉ qᵉ → is-surjectiveᵉ (map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ)
  is-surjective-is-imageᵉ up-iᵉ bᵉ =
    apply-universal-property-trunc-Propᵉ βᵉ
      ( trunc-Propᵉ (fiberᵉ (map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) bᵉ))
      ( γᵉ)
    where
    gᵉ : type-subtypeᵉ (trunc-Propᵉ ∘ᵉ fiberᵉ (map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ)) → Xᵉ
    gᵉ = map-embᵉ iᵉ ∘ᵉ pr1ᵉ
    is-emb-gᵉ : is-embᵉ gᵉ
    is-emb-gᵉ = is-emb-compᵉ (map-embᵉ iᵉ) pr1ᵉ
      ( is-emb-map-embᵉ iᵉ)
      ( is-emb-inclusion-subtypeᵉ (λ xᵉ → trunc-Propᵉ _))
    αᵉ : hom-sliceᵉ (map-embᵉ iᵉ) gᵉ
    αᵉ = map-inv-is-equivᵉ
          ( up-iᵉ
            ( Σᵉ Bᵉ ( λ bᵉ →
                    type-trunc-Propᵉ (fiberᵉ (map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) bᵉ)))
            ( gᵉ ,ᵉ is-emb-gᵉ))
          ( map-unit-imᵉ (pr1ᵉ qᵉ) ,ᵉ pr2ᵉ qᵉ)
    βᵉ : type-trunc-Propᵉ (fiberᵉ (map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) (pr1ᵉ (pr1ᵉ αᵉ bᵉ)))
    βᵉ = pr2ᵉ (pr1ᵉ αᵉ bᵉ)
    γᵉ :
      fiberᵉ (map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) (pr1ᵉ (pr1ᵉ αᵉ bᵉ)) →
      type-Propᵉ (trunc-Propᵉ (fiberᵉ (pr1ᵉ qᵉ) bᵉ))
    γᵉ (aᵉ ,ᵉ pᵉ) =
      unit-trunc-Propᵉ
        ( aᵉ ,ᵉ pᵉ ∙ᵉ invᵉ (is-injective-is-embᵉ (is-emb-map-embᵉ iᵉ) (pr2ᵉ αᵉ bᵉ)))

  is-image-is-surjective'ᵉ :
    is-surjectiveᵉ (map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) →
    is-image'ᵉ fᵉ iᵉ qᵉ
  is-image-is-surjective'ᵉ Hᵉ B'ᵉ mᵉ =
    map-equivᵉ
      ( ( equiv-hom-slice-fiberwise-homᵉ (map-embᵉ iᵉ) (map-embᵉ mᵉ)) ∘eᵉ
        ( inv-equivᵉ
          ( equiv-universal-property-family-of-fibersᵉ
            ( map-embᵉ iᵉ)
            ( fiberᵉ (map-embᵉ mᵉ)))) ∘eᵉ
        ( inv-equivᵉ
          ( equiv-dependent-universal-property-surjection-is-surjectiveᵉ
            ( pr1ᵉ qᵉ)
            ( Hᵉ)
            ( λ bᵉ →
              ( fiberᵉ (map-embᵉ mᵉ) (pr1ᵉ iᵉ bᵉ)) ,ᵉ
              ( is-prop-map-embᵉ mᵉ (pr1ᵉ iᵉ bᵉ))))) ∘eᵉ
        ( equiv-Π-equiv-familyᵉ
          ( λ aᵉ → equiv-trᵉ (fiberᵉ (map-embᵉ mᵉ)) (pr2ᵉ qᵉ aᵉ))) ∘eᵉ
        ( equiv-universal-property-family-of-fibersᵉ fᵉ (fiberᵉ (map-embᵉ mᵉ))) ∘eᵉ
        ( equiv-fiberwise-hom-hom-sliceᵉ fᵉ (map-embᵉ mᵉ)))

  is-image-is-surjectiveᵉ :
    is-surjectiveᵉ (map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) →
    is-imageᵉ fᵉ iᵉ qᵉ
  is-image-is-surjectiveᵉ Hᵉ =
    is-image-is-image'ᵉ fᵉ iᵉ qᵉ (is-image-is-surjective'ᵉ Hᵉ)
```