# Functoriality of the loop space operation

```agda
module synthetic-homotopy-theory.functoriality-loop-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.faithful-mapsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.faithful-pointed-mapsᵉ
open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Anyᵉ [pointedᵉ map](structured-types.pointed-maps.mdᵉ) `fᵉ : Aᵉ →∗ᵉ B`ᵉ inducesᵉ aᵉ
pointedᵉ mapᵉ `pointed-map-Ωᵉ fᵉ : Ωᵉ Aᵉ →∗ᵉ Ωᵉ B``ᵉ onᵉ
[loopᵉ spaces](synthetic-homotopy-theory.loop-spaces.md).ᵉ Furthermore,ᵉ thisᵉ
operationᵉ respectsᵉ theᵉ groupoidalᵉ operationsᵉ onᵉ loopᵉ spaces.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  map-Ωᵉ : type-Ωᵉ Aᵉ → type-Ωᵉ Bᵉ
  map-Ωᵉ pᵉ =
    tr-type-Ωᵉ
      ( preserves-point-pointed-mapᵉ fᵉ)
      ( apᵉ (map-pointed-mapᵉ fᵉ) pᵉ)

  preserves-refl-map-Ωᵉ : map-Ωᵉ reflᵉ ＝ᵉ reflᵉ
  preserves-refl-map-Ωᵉ = preserves-refl-tr-Ωᵉ (pr2ᵉ fᵉ)

  pointed-map-Ωᵉ : Ωᵉ Aᵉ →∗ᵉ Ωᵉ Bᵉ
  pr1ᵉ pointed-map-Ωᵉ = map-Ωᵉ
  pr2ᵉ pointed-map-Ωᵉ = preserves-refl-map-Ωᵉ

  preserves-mul-map-Ωᵉ :
    {xᵉ yᵉ : type-Ωᵉ Aᵉ} → map-Ωᵉ (mul-Ωᵉ Aᵉ xᵉ yᵉ) ＝ᵉ mul-Ωᵉ Bᵉ (map-Ωᵉ xᵉ) (map-Ωᵉ yᵉ)
  preserves-mul-map-Ωᵉ {xᵉ} {yᵉ} =
    ( apᵉ
      ( tr-type-Ωᵉ (preserves-point-pointed-mapᵉ fᵉ))
      ( ap-concatᵉ (map-pointed-mapᵉ fᵉ) xᵉ yᵉ)) ∙ᵉ
    ( preserves-mul-tr-Ωᵉ
      ( preserves-point-pointed-mapᵉ fᵉ)
      ( apᵉ (map-pointed-mapᵉ fᵉ) xᵉ)
      ( apᵉ (map-pointed-mapᵉ fᵉ) yᵉ))

  preserves-inv-map-Ωᵉ :
    (xᵉ : type-Ωᵉ Aᵉ) → map-Ωᵉ (inv-Ωᵉ Aᵉ xᵉ) ＝ᵉ inv-Ωᵉ Bᵉ (map-Ωᵉ xᵉ)
  preserves-inv-map-Ωᵉ xᵉ =
    ( apᵉ
      ( tr-type-Ωᵉ (preserves-point-pointed-mapᵉ fᵉ))
      ( ap-invᵉ (map-pointed-mapᵉ fᵉ) xᵉ)) ∙ᵉ
    ( preserves-inv-tr-Ωᵉ
      ( preserves-point-pointed-mapᵉ fᵉ)
      ( apᵉ (map-pointed-mapᵉ fᵉ) xᵉ))
```

### Faithful pointed maps induce embeddings on loop spaces

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  where

  is-emb-map-Ωᵉ :
    (fᵉ : Aᵉ →∗ᵉ Bᵉ) → is-faithfulᵉ (map-pointed-mapᵉ fᵉ) → is-embᵉ (map-Ωᵉ fᵉ)
  is-emb-map-Ωᵉ fᵉ Hᵉ =
    is-emb-compᵉ
      ( tr-type-Ωᵉ (preserves-point-pointed-mapᵉ fᵉ))
      ( apᵉ (map-pointed-mapᵉ fᵉ))
      ( is-emb-is-equivᵉ (is-equiv-tr-type-Ωᵉ (preserves-point-pointed-mapᵉ fᵉ)))
      ( Hᵉ (point-Pointed-Typeᵉ Aᵉ) (point-Pointed-Typeᵉ Aᵉ))

  emb-Ωᵉ :
    faithful-pointed-mapᵉ Aᵉ Bᵉ → type-Ωᵉ Aᵉ ↪ᵉ type-Ωᵉ Bᵉ
  pr1ᵉ (emb-Ωᵉ fᵉ) = map-Ωᵉ (pointed-map-faithful-pointed-mapᵉ fᵉ)
  pr2ᵉ (emb-Ωᵉ fᵉ) =
    is-emb-map-Ωᵉ
      ( pointed-map-faithful-pointed-mapᵉ fᵉ)
      ( is-faithful-faithful-pointed-mapᵉ fᵉ)
```

### Pointed embeddings induce pointed equivalences on loop spaces

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (is-emb-fᵉ : is-embᵉ (map-pointed-mapᵉ fᵉ))
  where

  is-equiv-map-Ω-is-embᵉ : is-equivᵉ (map-Ωᵉ fᵉ)
  is-equiv-map-Ω-is-embᵉ =
    is-equiv-compᵉ
      ( tr-type-Ωᵉ (preserves-point-pointed-mapᵉ fᵉ))
      ( apᵉ (map-pointed-mapᵉ fᵉ))
      ( is-emb-fᵉ (point-Pointed-Typeᵉ Aᵉ) (point-Pointed-Typeᵉ Aᵉ))
      ( is-equiv-tr-type-Ωᵉ (preserves-point-pointed-mapᵉ fᵉ))

  equiv-map-Ω-is-embᵉ : type-Ωᵉ Aᵉ ≃ᵉ type-Ωᵉ Bᵉ
  pr1ᵉ equiv-map-Ω-is-embᵉ = map-Ωᵉ fᵉ
  pr2ᵉ equiv-map-Ω-is-embᵉ = is-equiv-map-Ω-is-embᵉ

  pointed-equiv-pointed-map-Ω-is-embᵉ : Ωᵉ Aᵉ ≃∗ᵉ Ωᵉ Bᵉ
  pr1ᵉ pointed-equiv-pointed-map-Ω-is-embᵉ = equiv-map-Ω-is-embᵉ
  pr2ᵉ pointed-equiv-pointed-map-Ω-is-embᵉ = preserves-refl-map-Ωᵉ fᵉ
```

### The operator `pointed-map-Ω` preserves equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (eᵉ : Aᵉ ≃∗ᵉ Bᵉ)
  where

  equiv-map-Ω-pointed-equivᵉ :
    type-Ωᵉ Aᵉ ≃ᵉ type-Ωᵉ Bᵉ
  equiv-map-Ω-pointed-equivᵉ =
    equiv-map-Ω-is-embᵉ
      ( pointed-map-pointed-equivᵉ eᵉ)
      ( is-emb-is-equivᵉ (is-equiv-map-pointed-equivᵉ eᵉ))
```

### `pointed-map-Ω` preserves pointed equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (eᵉ : Aᵉ ≃∗ᵉ Bᵉ)
  where

  pointed-equiv-Ω-pointed-equivᵉ :
    Ωᵉ Aᵉ ≃∗ᵉ Ωᵉ Bᵉ
  pr1ᵉ pointed-equiv-Ω-pointed-equivᵉ = equiv-map-Ω-pointed-equivᵉ eᵉ
  pr2ᵉ pointed-equiv-Ω-pointed-equivᵉ =
    preserves-refl-map-Ωᵉ (pointed-map-pointed-equivᵉ eᵉ)
```