# Uniqueness of the image of a map

```agda
module foundation.uniqueness-imageᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.imagesᵉ
open import foundation.sliceᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
```

</details>

### Uniqueness of the image

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (iᵉ : Bᵉ ↪ᵉ Xᵉ) (qᵉ : hom-sliceᵉ fᵉ (map-embᵉ iᵉ))
  {B'ᵉ : UUᵉ l4ᵉ} (i'ᵉ : B'ᵉ ↪ᵉ Xᵉ) (q'ᵉ : hom-sliceᵉ fᵉ (map-embᵉ i'ᵉ))
  (hᵉ : hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ))
  where

  abstract
    is-equiv-is-image-is-imageᵉ :
      is-imageᵉ fᵉ iᵉ qᵉ →
      is-imageᵉ fᵉ i'ᵉ q'ᵉ →
      is-equivᵉ (map-hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) hᵉ)
    is-equiv-is-image-is-imageᵉ up-iᵉ up-i'ᵉ =
      is-equiv-hom-slice-embᵉ iᵉ i'ᵉ hᵉ (map-inv-is-equivᵉ (up-i'ᵉ Bᵉ iᵉ) qᵉ)

  abstract
    is-image-is-image-is-equivᵉ :
      is-equivᵉ (map-hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) hᵉ) →
      is-imageᵉ fᵉ iᵉ qᵉ →
      is-imageᵉ fᵉ i'ᵉ q'ᵉ
    is-image-is-image-is-equivᵉ is-equiv-hᵉ up-iᵉ {lᵉ} =
      is-image-is-image'ᵉ fᵉ i'ᵉ q'ᵉ
        ( λ Cᵉ jᵉ rᵉ →
          comp-hom-sliceᵉ
            ( map-embᵉ i'ᵉ)
            ( map-embᵉ iᵉ)
            ( map-embᵉ jᵉ)
            ( map-inv-is-equivᵉ (up-iᵉ Cᵉ jᵉ) rᵉ)
            ( pairᵉ
              ( map-inv-is-equivᵉ is-equiv-hᵉ)
              ( triangle-sectionᵉ
                ( map-embᵉ iᵉ)
                ( map-embᵉ i'ᵉ)
                ( map-hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) hᵉ)
                ( triangle-hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) hᵉ)
                ( pairᵉ
                  ( map-inv-is-equivᵉ is-equiv-hᵉ)
                  ( is-section-map-inv-is-equivᵉ is-equiv-hᵉ)))))

  abstract
    is-image-is-equiv-is-imageᵉ :
      is-imageᵉ fᵉ i'ᵉ q'ᵉ →
      is-equivᵉ (map-hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) hᵉ) →
      is-imageᵉ fᵉ iᵉ qᵉ
    is-image-is-equiv-is-imageᵉ up-i'ᵉ is-equiv-hᵉ {lᵉ} =
      is-image-is-image'ᵉ fᵉ iᵉ qᵉ
        ( λ Cᵉ jᵉ rᵉ →
          comp-hom-sliceᵉ
            ( map-embᵉ iᵉ)
            ( map-embᵉ i'ᵉ)
            ( map-embᵉ jᵉ)
            ( map-inv-is-equivᵉ (up-i'ᵉ Cᵉ jᵉ) rᵉ)
            ( hᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (iᵉ : Bᵉ ↪ᵉ Xᵉ) (qᵉ : hom-sliceᵉ fᵉ (map-embᵉ iᵉ))
  (Hiᵉ : is-imageᵉ fᵉ iᵉ qᵉ)
  {B'ᵉ : UUᵉ l4ᵉ} (i'ᵉ : B'ᵉ ↪ᵉ Xᵉ) (q'ᵉ : hom-sliceᵉ fᵉ (map-embᵉ i'ᵉ))
  (Hi'ᵉ : is-imageᵉ fᵉ i'ᵉ q'ᵉ)
  where

  abstract
    uniqueness-imageᵉ :
      is-contrᵉ
        ( Σᵉ ( equiv-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ))
            ( λ eᵉ →
              htpy-hom-sliceᵉ fᵉ
                ( map-embᵉ i'ᵉ)
                ( comp-hom-sliceᵉ fᵉ
                  ( map-embᵉ iᵉ)
                  ( map-embᵉ i'ᵉ)
                  ( hom-equiv-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) eᵉ)
                  ( qᵉ))
                ( q'ᵉ)))
    uniqueness-imageᵉ =
      is-contr-equivᵉ
        ( Σᵉ ( Σᵉ ( hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ))
                ( λ hᵉ →
                  htpy-hom-sliceᵉ fᵉ
                    ( map-embᵉ i'ᵉ)
                    ( comp-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) hᵉ qᵉ)
                    ( q'ᵉ)))
            ( λ hᵉ → is-equivᵉ (pr1ᵉ (pr1ᵉ hᵉ))))
        ( ( equiv-right-swap-Σᵉ) ∘eᵉ
          ( equiv-Σᵉ
            ( λ hᵉ →
              htpy-hom-sliceᵉ fᵉ
                ( map-embᵉ i'ᵉ)
                ( comp-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) (pr1ᵉ hᵉ) qᵉ)
                ( q'ᵉ))
            ( equiv-right-swap-Σᵉ)
            ( λ ((eᵉ ,ᵉ Eᵉ) ,ᵉ Hᵉ) → id-equivᵉ)))
        ( is-contr-equivᵉ
          ( is-equivᵉ
            ( map-hom-slice-universal-property-imageᵉ fᵉ iᵉ qᵉ Hiᵉ i'ᵉ q'ᵉ))
          ( left-unit-law-Σ-is-contrᵉ
            ( universal-property-imageᵉ fᵉ iᵉ qᵉ Hiᵉ i'ᵉ q'ᵉ)
            ( centerᵉ (universal-property-imageᵉ fᵉ iᵉ qᵉ Hiᵉ i'ᵉ q'ᵉ)))
          ( is-proof-irrelevant-is-propᵉ
            ( is-property-is-equivᵉ
              ( map-hom-slice-universal-property-imageᵉ fᵉ iᵉ qᵉ Hiᵉ i'ᵉ q'ᵉ))
            ( is-equiv-is-image-is-imageᵉ fᵉ iᵉ qᵉ i'ᵉ q'ᵉ
              ( hom-slice-universal-property-imageᵉ fᵉ iᵉ qᵉ Hiᵉ i'ᵉ q'ᵉ)
              ( Hiᵉ)
              ( Hi'ᵉ))))

  equiv-slice-uniqueness-imageᵉ : equiv-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ)
  equiv-slice-uniqueness-imageᵉ =
    pr1ᵉ (centerᵉ uniqueness-imageᵉ)

  hom-equiv-slice-uniqueness-imageᵉ : hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ)
  hom-equiv-slice-uniqueness-imageᵉ =
    hom-equiv-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) (equiv-slice-uniqueness-imageᵉ)

  map-hom-equiv-slice-uniqueness-imageᵉ : Bᵉ → B'ᵉ
  map-hom-equiv-slice-uniqueness-imageᵉ =
    map-hom-sliceᵉ (map-embᵉ iᵉ) (map-embᵉ i'ᵉ) (hom-equiv-slice-uniqueness-imageᵉ)

  abstract
    is-equiv-map-hom-equiv-slice-uniqueness-imageᵉ :
      is-equivᵉ map-hom-equiv-slice-uniqueness-imageᵉ
    is-equiv-map-hom-equiv-slice-uniqueness-imageᵉ =
      is-equiv-map-equivᵉ (pr1ᵉ equiv-slice-uniqueness-imageᵉ)

  equiv-equiv-slice-uniqueness-imageᵉ : Bᵉ ≃ᵉ B'ᵉ
  pr1ᵉ equiv-equiv-slice-uniqueness-imageᵉ = map-hom-equiv-slice-uniqueness-imageᵉ
  pr2ᵉ equiv-equiv-slice-uniqueness-imageᵉ =
    is-equiv-map-hom-equiv-slice-uniqueness-imageᵉ

  triangle-hom-equiv-slice-uniqueness-imageᵉ :
    (map-embᵉ iᵉ) ~ᵉ (map-embᵉ i'ᵉ ∘ᵉ map-hom-equiv-slice-uniqueness-imageᵉ)
  triangle-hom-equiv-slice-uniqueness-imageᵉ =
    triangle-hom-sliceᵉ
      ( map-embᵉ iᵉ)
      ( map-embᵉ i'ᵉ)
      ( hom-equiv-slice-uniqueness-imageᵉ)

  htpy-equiv-slice-uniqueness-imageᵉ :
    htpy-hom-sliceᵉ fᵉ
      ( map-embᵉ i'ᵉ)
      ( comp-hom-sliceᵉ fᵉ
        ( map-embᵉ iᵉ)
        ( map-embᵉ i'ᵉ)
        ( hom-equiv-slice-uniqueness-imageᵉ)
        ( qᵉ))
      ( q'ᵉ)
  htpy-equiv-slice-uniqueness-imageᵉ =
    pr2ᵉ (centerᵉ uniqueness-imageᵉ)

  htpy-map-hom-equiv-slice-uniqueness-imageᵉ :
    ( map-hom-equiv-slice-uniqueness-imageᵉ ∘ᵉ map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) ~ᵉ
    ( map-hom-sliceᵉ fᵉ (map-embᵉ i'ᵉ) q'ᵉ)
  htpy-map-hom-equiv-slice-uniqueness-imageᵉ =
    pr1ᵉ htpy-equiv-slice-uniqueness-imageᵉ

  tetrahedron-hom-equiv-slice-uniqueness-imageᵉ :
    ( ( ( triangle-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ) ∙hᵉ
        ( ( triangle-hom-equiv-slice-uniqueness-imageᵉ) ·rᵉ
          ( map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ))) ∙hᵉ
      ( map-embᵉ i'ᵉ ·lᵉ htpy-map-hom-equiv-slice-uniqueness-imageᵉ)) ~ᵉ
    ( triangle-hom-sliceᵉ fᵉ (map-embᵉ i'ᵉ) q'ᵉ)
  tetrahedron-hom-equiv-slice-uniqueness-imageᵉ =
    pr2ᵉ htpy-equiv-slice-uniqueness-imageᵉ
```

### Uniqueness of the image

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (iᵉ : Bᵉ ↪ᵉ Xᵉ) (qᵉ : hom-sliceᵉ fᵉ (map-embᵉ iᵉ))
  (Hᵉ : is-imageᵉ fᵉ iᵉ qᵉ)
  where

  abstract
    uniqueness-imᵉ :
      is-contrᵉ
        ( Σᵉ ( equiv-sliceᵉ (inclusion-imᵉ fᵉ) (map-embᵉ iᵉ))
            ( λ eᵉ →
              htpy-hom-sliceᵉ fᵉ
                ( map-embᵉ iᵉ)
                ( comp-hom-sliceᵉ fᵉ
                  ( inclusion-imᵉ fᵉ)
                  ( map-embᵉ iᵉ)
                  ( hom-equiv-sliceᵉ (inclusion-imᵉ fᵉ) (map-embᵉ iᵉ) eᵉ)
                  ( unit-imᵉ fᵉ))
                ( qᵉ)))
    uniqueness-imᵉ =
      uniqueness-imageᵉ fᵉ (emb-imᵉ fᵉ) (unit-imᵉ fᵉ) (is-image-imᵉ fᵉ) iᵉ qᵉ Hᵉ

  equiv-slice-uniqueness-imᵉ : equiv-sliceᵉ (inclusion-imᵉ fᵉ) (map-embᵉ iᵉ)
  equiv-slice-uniqueness-imᵉ =
    pr1ᵉ (centerᵉ uniqueness-imᵉ)

  hom-equiv-slice-uniqueness-imᵉ : hom-sliceᵉ (inclusion-imᵉ fᵉ) (map-embᵉ iᵉ)
  hom-equiv-slice-uniqueness-imᵉ =
    hom-equiv-sliceᵉ (inclusion-imᵉ fᵉ) (map-embᵉ iᵉ) equiv-slice-uniqueness-imᵉ

  map-hom-equiv-slice-uniqueness-imᵉ : imᵉ fᵉ → Bᵉ
  map-hom-equiv-slice-uniqueness-imᵉ =
    map-hom-sliceᵉ (inclusion-imᵉ fᵉ) (map-embᵉ iᵉ) hom-equiv-slice-uniqueness-imᵉ

  abstract
    is-equiv-map-hom-equiv-slice-uniqueness-imᵉ :
      is-equivᵉ map-hom-equiv-slice-uniqueness-imᵉ
    is-equiv-map-hom-equiv-slice-uniqueness-imᵉ =
      is-equiv-map-equivᵉ (pr1ᵉ equiv-slice-uniqueness-imᵉ)

  equiv-equiv-slice-uniqueness-imᵉ : imᵉ fᵉ ≃ᵉ Bᵉ
  pr1ᵉ equiv-equiv-slice-uniqueness-imᵉ = map-hom-equiv-slice-uniqueness-imᵉ
  pr2ᵉ equiv-equiv-slice-uniqueness-imᵉ =
    is-equiv-map-hom-equiv-slice-uniqueness-imᵉ

  triangle-hom-equiv-slice-uniqueness-imᵉ :
    (inclusion-imᵉ fᵉ) ~ᵉ (map-embᵉ iᵉ ∘ᵉ map-hom-equiv-slice-uniqueness-imᵉ)
  triangle-hom-equiv-slice-uniqueness-imᵉ =
    triangle-hom-sliceᵉ
      ( inclusion-imᵉ fᵉ)
      ( map-embᵉ iᵉ)
      ( hom-equiv-slice-uniqueness-imᵉ)

  htpy-equiv-slice-uniqueness-imᵉ :
    htpy-hom-sliceᵉ fᵉ
      ( map-embᵉ iᵉ)
      ( comp-hom-sliceᵉ fᵉ
        ( inclusion-imᵉ fᵉ)
        ( map-embᵉ iᵉ)
        ( hom-equiv-slice-uniqueness-imᵉ)
        ( unit-imᵉ fᵉ))
      ( qᵉ)
  htpy-equiv-slice-uniqueness-imᵉ =
    pr2ᵉ (centerᵉ uniqueness-imᵉ)

  htpy-map-hom-equiv-slice-uniqueness-imᵉ :
    ( ( map-hom-equiv-slice-uniqueness-imᵉ) ∘ᵉ
      ( map-hom-sliceᵉ fᵉ (inclusion-imᵉ fᵉ) (unit-imᵉ fᵉ))) ~ᵉ
    ( map-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ)
  htpy-map-hom-equiv-slice-uniqueness-imᵉ =
    pr1ᵉ htpy-equiv-slice-uniqueness-imᵉ

  tetrahedron-hom-equiv-slice-uniqueness-imᵉ :
    ( ( ( triangle-hom-sliceᵉ fᵉ (inclusion-imᵉ fᵉ) (unit-imᵉ fᵉ)) ∙hᵉ
        ( ( triangle-hom-equiv-slice-uniqueness-imᵉ) ·rᵉ
          ( map-hom-sliceᵉ fᵉ (inclusion-imᵉ fᵉ) (unit-imᵉ fᵉ)))) ∙hᵉ
      ( map-embᵉ iᵉ ·lᵉ htpy-map-hom-equiv-slice-uniqueness-imᵉ)) ~ᵉ
    ( triangle-hom-sliceᵉ fᵉ (map-embᵉ iᵉ) qᵉ)
  tetrahedron-hom-equiv-slice-uniqueness-imᵉ =
    pr2ᵉ htpy-equiv-slice-uniqueness-imᵉ
```