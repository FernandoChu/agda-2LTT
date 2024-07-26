# Fibered involutions

```agda
module foundation.fibered-involutionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fibered-mapsᵉ
open import foundation.involutionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Aᵉ fiberedᵉ involutionᵉ isᵉ aᵉ fiberedᵉ mapᵉ

```text
       hᵉ
  Aᵉ ------->ᵉ Aᵉ
  |          |
 f|ᵉ          |gᵉ
  |          |
  ∨ᵉ          ∨ᵉ
  Xᵉ ------->ᵉ Xᵉ
       iᵉ
```

suchᵉ thatᵉ bothᵉ `i`ᵉ andᵉ `h`ᵉ areᵉ involutions.ᵉ

## Definition

```agda
involution-overᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ} →
  (Aᵉ → Xᵉ) → (Aᵉ → Yᵉ) → (Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
involution-overᵉ {Aᵉ = Aᵉ} fᵉ gᵉ iᵉ =
  Σᵉ (involutionᵉ Aᵉ) (is-map-overᵉ fᵉ gᵉ iᵉ ∘ᵉ map-involutionᵉ)

fibered-involutionᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} →
  (Aᵉ → Xᵉ) → (Aᵉ → Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
fibered-involutionᵉ {Xᵉ = Xᵉ} fᵉ gᵉ =
  Σᵉ (involutionᵉ Xᵉ) (involution-overᵉ fᵉ gᵉ ∘ᵉ map-involutionᵉ)

is-fiberwise-involutionᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Pᵉ : Xᵉ → UUᵉ l2ᵉ} →
  ((xᵉ : Xᵉ) → Pᵉ xᵉ → Pᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-fiberwise-involutionᵉ {Xᵉ = Xᵉ} fᵉ = (xᵉ : Xᵉ) → is-involutionᵉ (fᵉ xᵉ)

fam-involutionᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : Xᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
fam-involutionᵉ {Xᵉ = Xᵉ} Pᵉ = (xᵉ : Xᵉ) → involutionᵉ (Pᵉ xᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  (fᵉ gᵉ : Aᵉ → Xᵉ)
  where

  is-fibered-involution-fibered-mapᵉ : fibered-mapᵉ fᵉ gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-fibered-involution-fibered-mapᵉ (iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) =
    is-involutionᵉ iᵉ ×ᵉ is-involutionᵉ hᵉ

  map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ :
    (fibered-involutionᵉ fᵉ gᵉ) →
    Σᵉ (fibered-mapᵉ fᵉ gᵉ) (is-fibered-involution-fibered-mapᵉ)
  pr1ᵉ (pr1ᵉ (map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ
    ((iᵉ ,ᵉ is-involution-iᵉ) ,ᵉ (hᵉ ,ᵉ is-involution-hᵉ) ,ᵉ Hᵉ))) = iᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ
    ((iᵉ ,ᵉ is-involution-iᵉ) ,ᵉ (hᵉ ,ᵉ is-involution-hᵉ) ,ᵉ Hᵉ)))) = hᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ
    ((iᵉ ,ᵉ is-involution-iᵉ) ,ᵉ (hᵉ ,ᵉ is-involution-hᵉ) ,ᵉ Hᵉ)))) = Hᵉ
  pr1ᵉ (pr2ᵉ (map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ
    ((iᵉ ,ᵉ is-involution-iᵉ) ,ᵉ (hᵉ ,ᵉ is-involution-hᵉ) ,ᵉ Hᵉ))) = is-involution-iᵉ
  pr2ᵉ (pr2ᵉ (map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ
    ((iᵉ ,ᵉ is-involution-iᵉ) ,ᵉ (hᵉ ,ᵉ is-involution-hᵉ) ,ᵉ Hᵉ))) = is-involution-hᵉ

  map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ :
    Σᵉ (fibered-mapᵉ fᵉ gᵉ) (is-fibered-involution-fibered-mapᵉ) →
    fibered-involutionᵉ fᵉ gᵉ
  pr1ᵉ (pr1ᵉ (map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-involution-iᵉ ,ᵉ is-involution-hᵉ))) = iᵉ
  pr2ᵉ (pr1ᵉ (map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-involution-iᵉ ,ᵉ is-involution-hᵉ))) = is-involution-iᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-involution-iᵉ ,ᵉ is-involution-hᵉ)))) = hᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ (map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-involution-iᵉ ,ᵉ is-involution-hᵉ)))) = is-involution-hᵉ
  pr2ᵉ (pr2ᵉ (map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-involution-iᵉ ,ᵉ is-involution-hᵉ))) = Hᵉ

  is-equiv-map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ :
    is-equivᵉ (map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ)
  is-equiv-map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ =
    is-equiv-is-invertibleᵉ
      ( map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)

  equiv-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ :
    ( fibered-involutionᵉ fᵉ gᵉ) ≃ᵉ
    ( Σᵉ (fibered-mapᵉ fᵉ gᵉ) (is-fibered-involution-fibered-mapᵉ))
  pr1ᵉ equiv-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ =
    map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ
  pr2ᵉ equiv-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ =
    is-equiv-map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ

  is-equiv-map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ :
    is-equivᵉ (map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ)
  is-equiv-map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ =
    is-equiv-is-invertibleᵉ
      ( map-Σ-is-fibered-involution-fibered-map-fibered-involutionᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)

  equiv-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ :
    ( Σᵉ (fibered-mapᵉ fᵉ gᵉ) (is-fibered-involution-fibered-mapᵉ)) ≃ᵉ
    ( fibered-involutionᵉ fᵉ gᵉ)
  pr1ᵉ equiv-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ =
    map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ
  pr2ᵉ equiv-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ =
    is-equiv-map-fibered-involution-Σ-is-fibered-involution-fibered-mapᵉ
```

## Examples

```agda
self-fibered-involutionᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → involutionᵉ Aᵉ → fibered-involutionᵉ idᵉ idᵉ
pr1ᵉ (self-fibered-involutionᵉ eᵉ) = eᵉ
pr1ᵉ (pr2ᵉ (self-fibered-involutionᵉ eᵉ)) = eᵉ
pr2ᵉ (pr2ᵉ (self-fibered-involutionᵉ eᵉ)) = refl-htpyᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  id-fibered-involutionᵉ : (fᵉ : Aᵉ → Bᵉ) → fibered-involutionᵉ fᵉ fᵉ
  pr1ᵉ (id-fibered-involutionᵉ fᵉ) = id-involutionᵉ
  pr1ᵉ (pr2ᵉ (id-fibered-involutionᵉ fᵉ)) = id-involutionᵉ
  pr2ᵉ (pr2ᵉ (id-fibered-involutionᵉ fᵉ)) = refl-htpyᵉ

  id-fibered-involution-htpyᵉ : (fᵉ gᵉ : Aᵉ → Bᵉ) → fᵉ ~ᵉ gᵉ → fibered-involutionᵉ fᵉ gᵉ
  pr1ᵉ (id-fibered-involution-htpyᵉ fᵉ gᵉ Hᵉ) = id-involutionᵉ
  pr1ᵉ (pr2ᵉ (id-fibered-involution-htpyᵉ fᵉ gᵉ Hᵉ)) = id-involutionᵉ
  pr2ᵉ (pr2ᵉ (id-fibered-involution-htpyᵉ fᵉ gᵉ Hᵉ)) = Hᵉ
```