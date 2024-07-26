# Fibered equivalences

```agda
module foundation.fibered-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.fibered-mapsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.pullbacksᵉ
open import foundation.sliceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Aᵉ fiberedᵉ equivalenceᵉ isᵉ aᵉ fiberedᵉ mapᵉ

```text
       hᵉ
  Aᵉ ------->ᵉ Bᵉ
  |          |
 f|ᵉ          |gᵉ
  |          |
  ∨ᵉ          ∨ᵉ
  Xᵉ ------->ᵉ Yᵉ
       iᵉ
```

suchᵉ thatᵉ bothᵉ `i`ᵉ andᵉ `h`ᵉ areᵉ equivalences.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  equiv-overᵉ : (Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  equiv-overᵉ iᵉ = Σᵉ (Aᵉ ≃ᵉ Bᵉ) (is-map-overᵉ fᵉ gᵉ iᵉ ∘ᵉ map-equivᵉ)

  fibered-equivᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  fibered-equivᵉ = Σᵉ (Xᵉ ≃ᵉ Yᵉ) (equiv-overᵉ ∘ᵉ map-equivᵉ)

  fiberwise-equiv-overᵉ : (Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  fiberwise-equiv-overᵉ iᵉ =
    Σᵉ (fiberwise-map-overᵉ fᵉ gᵉ iᵉ) is-fiberwise-equivᵉ

  fam-equiv-overᵉ : (Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  fam-equiv-overᵉ iᵉ = (xᵉ : Xᵉ) → (fiberᵉ fᵉ xᵉ) ≃ᵉ (fiberᵉ gᵉ (iᵉ xᵉ))
```

## Properties

### The induced maps on fibers are equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ)
  where

  eq-equiv-over-equiv-sliceᵉ : equiv-sliceᵉ (iᵉ ∘ᵉ fᵉ) gᵉ ＝ᵉ equiv-overᵉ fᵉ gᵉ iᵉ
  eq-equiv-over-equiv-sliceᵉ = reflᵉ

  eq-equiv-slice-equiv-overᵉ : equiv-overᵉ fᵉ gᵉ iᵉ ＝ᵉ equiv-sliceᵉ (iᵉ ∘ᵉ fᵉ) gᵉ
  eq-equiv-slice-equiv-overᵉ = reflᵉ

  equiv-equiv-over-fiberwise-equivᵉ :
    fiberwise-equivᵉ (fiberᵉ (iᵉ ∘ᵉ fᵉ)) (fiberᵉ gᵉ) ≃ᵉ equiv-overᵉ fᵉ gᵉ iᵉ
  equiv-equiv-over-fiberwise-equivᵉ =
    equiv-equiv-slice-fiberwise-equivᵉ (iᵉ ∘ᵉ fᵉ) gᵉ
```

### Fibered equivalences embed into the type of fibered maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ)
  where

  map-Σ-is-equiv-equiv-overᵉ :
    (equiv-overᵉ fᵉ gᵉ iᵉ) → Σᵉ (map-overᵉ fᵉ gᵉ iᵉ) (is-equivᵉ ∘ᵉ pr1ᵉ)
  pr1ᵉ (pr1ᵉ (map-Σ-is-equiv-equiv-overᵉ ((hᵉ ,ᵉ is-equiv-hᵉ) ,ᵉ Hᵉ))) = hᵉ
  pr2ᵉ (pr1ᵉ (map-Σ-is-equiv-equiv-overᵉ ((hᵉ ,ᵉ is-equiv-hᵉ) ,ᵉ Hᵉ))) = Hᵉ
  pr2ᵉ (map-Σ-is-equiv-equiv-overᵉ ((hᵉ ,ᵉ is-equiv-hᵉ) ,ᵉ Hᵉ)) = is-equiv-hᵉ

  map-equiv-over-Σ-is-equivᵉ :
    Σᵉ (map-overᵉ fᵉ gᵉ iᵉ) (is-equivᵉ ∘ᵉ pr1ᵉ) → (equiv-overᵉ fᵉ gᵉ iᵉ)
  pr1ᵉ (pr1ᵉ (map-equiv-over-Σ-is-equivᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ is-equiv-hᵉ))) = hᵉ
  pr2ᵉ (pr1ᵉ (map-equiv-over-Σ-is-equivᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ is-equiv-hᵉ))) = is-equiv-hᵉ
  pr2ᵉ (map-equiv-over-Σ-is-equivᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ is-equiv-hᵉ)) = Hᵉ

  is-equiv-map-Σ-is-equiv-equiv-overᵉ : is-equivᵉ map-Σ-is-equiv-equiv-overᵉ
  is-equiv-map-Σ-is-equiv-equiv-overᵉ =
    is-equiv-is-invertibleᵉ map-equiv-over-Σ-is-equivᵉ refl-htpyᵉ refl-htpyᵉ

  equiv-Σ-is-equiv-equiv-overᵉ :
    (equiv-overᵉ fᵉ gᵉ iᵉ) ≃ᵉ Σᵉ (map-overᵉ fᵉ gᵉ iᵉ) (is-equivᵉ ∘ᵉ pr1ᵉ)
  pr1ᵉ equiv-Σ-is-equiv-equiv-overᵉ = map-Σ-is-equiv-equiv-overᵉ
  pr2ᵉ equiv-Σ-is-equiv-equiv-overᵉ = is-equiv-map-Σ-is-equiv-equiv-overᵉ

  is-equiv-map-equiv-over-Σ-is-equivᵉ : is-equivᵉ map-equiv-over-Σ-is-equivᵉ
  is-equiv-map-equiv-over-Σ-is-equivᵉ =
    is-equiv-is-invertibleᵉ map-Σ-is-equiv-equiv-overᵉ refl-htpyᵉ refl-htpyᵉ

  equiv-equiv-over-Σ-is-equivᵉ :
    Σᵉ (map-overᵉ fᵉ gᵉ iᵉ) (is-equivᵉ ∘ᵉ pr1ᵉ) ≃ᵉ (equiv-overᵉ fᵉ gᵉ iᵉ)
  pr1ᵉ equiv-equiv-over-Σ-is-equivᵉ = map-equiv-over-Σ-is-equivᵉ
  pr2ᵉ equiv-equiv-over-Σ-is-equivᵉ = is-equiv-map-equiv-over-Σ-is-equivᵉ

  emb-map-over-equiv-overᵉ : equiv-overᵉ fᵉ gᵉ iᵉ ↪ᵉ map-overᵉ fᵉ gᵉ iᵉ
  emb-map-over-equiv-overᵉ =
    comp-embᵉ
      ( emb-subtypeᵉ (is-equiv-Propᵉ ∘ᵉ pr1ᵉ))
      ( emb-equivᵉ equiv-Σ-is-equiv-equiv-overᵉ)

  map-over-equiv-overᵉ : equiv-overᵉ fᵉ gᵉ iᵉ → map-overᵉ fᵉ gᵉ iᵉ
  map-over-equiv-overᵉ = map-embᵉ emb-map-over-equiv-overᵉ

  is-emb-map-over-equiv-overᵉ : is-embᵉ map-over-equiv-overᵉ
  is-emb-map-over-equiv-overᵉ = is-emb-map-embᵉ emb-map-over-equiv-overᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  is-fibered-equiv-fibered-mapᵉ : fibered-mapᵉ fᵉ gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-fibered-equiv-fibered-mapᵉ (iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) = is-equivᵉ iᵉ ×ᵉ is-equivᵉ hᵉ

  map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ :
    (fibered-equivᵉ fᵉ gᵉ) → Σᵉ (fibered-mapᵉ fᵉ gᵉ) (is-fibered-equiv-fibered-mapᵉ)
  pr1ᵉ (pr1ᵉ (map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ
    ((iᵉ ,ᵉ is-equiv-iᵉ) ,ᵉ (hᵉ ,ᵉ is-equiv-hᵉ) ,ᵉ Hᵉ))) = iᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ
    ((iᵉ ,ᵉ is-equiv-iᵉ) ,ᵉ (hᵉ ,ᵉ is-equiv-hᵉ) ,ᵉ Hᵉ)))) = hᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ
    ((iᵉ ,ᵉ is-equiv-iᵉ) ,ᵉ (hᵉ ,ᵉ is-equiv-hᵉ) ,ᵉ Hᵉ)))) = Hᵉ
  pr1ᵉ (pr2ᵉ (map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ
    ((iᵉ ,ᵉ is-equiv-iᵉ) ,ᵉ (hᵉ ,ᵉ is-equiv-hᵉ) ,ᵉ Hᵉ))) = is-equiv-iᵉ
  pr2ᵉ (pr2ᵉ (map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ
    ((iᵉ ,ᵉ is-equiv-iᵉ) ,ᵉ (hᵉ ,ᵉ is-equiv-hᵉ) ,ᵉ Hᵉ))) = is-equiv-hᵉ

  map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ :
    (Σᵉ (fibered-mapᵉ fᵉ gᵉ) (is-fibered-equiv-fibered-mapᵉ)) → (fibered-equivᵉ fᵉ gᵉ)
  pr1ᵉ (pr1ᵉ (map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-equiv-iᵉ ,ᵉ is-equiv-hᵉ))) = iᵉ
  pr2ᵉ (pr1ᵉ (map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-equiv-iᵉ ,ᵉ is-equiv-hᵉ))) = is-equiv-iᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-equiv-iᵉ ,ᵉ is-equiv-hᵉ)))) = hᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ (map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-equiv-iᵉ ,ᵉ is-equiv-hᵉ)))) = is-equiv-hᵉ
  pr2ᵉ (pr2ᵉ (map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ
    ((iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) ,ᵉ is-equiv-iᵉ ,ᵉ is-equiv-hᵉ))) = Hᵉ

  is-equiv-map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ :
    is-equivᵉ (map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ)
  is-equiv-map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ =
    is-equiv-is-invertibleᵉ
      ( map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)

  equiv-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ :
    (fibered-equivᵉ fᵉ gᵉ) ≃ᵉ Σᵉ (fibered-mapᵉ fᵉ gᵉ) (is-fibered-equiv-fibered-mapᵉ)
  pr1ᵉ equiv-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ =
    map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ
  pr2ᵉ equiv-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ =
    is-equiv-map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ

  is-equiv-map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ :
    is-equivᵉ (map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ)
  is-equiv-map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ =
    is-equiv-is-invertibleᵉ
      ( map-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)

  equiv-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ :
    Σᵉ (fibered-mapᵉ fᵉ gᵉ) (is-fibered-equiv-fibered-mapᵉ) ≃ᵉ (fibered-equivᵉ fᵉ gᵉ)
  pr1ᵉ equiv-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ =
    map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ
  pr2ᵉ equiv-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ =
    is-equiv-map-fibered-equiv-Σ-is-fibered-equiv-fibered-mapᵉ

  is-prop-is-fibered-equiv-fibered-mapᵉ :
    (ihHᵉ : fibered-mapᵉ fᵉ gᵉ) → is-propᵉ (is-fibered-equiv-fibered-mapᵉ ihHᵉ)
  is-prop-is-fibered-equiv-fibered-mapᵉ (iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) =
    is-prop-productᵉ (is-property-is-equivᵉ iᵉ) (is-property-is-equivᵉ hᵉ)

  is-fibered-equiv-fibered-map-Propᵉ :
    fibered-mapᵉ fᵉ gᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ (is-fibered-equiv-fibered-map-Propᵉ ihHᵉ) =
    is-fibered-equiv-fibered-mapᵉ ihHᵉ
  pr2ᵉ (is-fibered-equiv-fibered-map-Propᵉ ihHᵉ) =
    is-prop-is-fibered-equiv-fibered-mapᵉ ihHᵉ

  emb-fibered-map-fibered-equivᵉ : fibered-equivᵉ fᵉ gᵉ ↪ᵉ fibered-mapᵉ fᵉ gᵉ
  emb-fibered-map-fibered-equivᵉ =
    comp-embᵉ
      ( emb-subtypeᵉ is-fibered-equiv-fibered-map-Propᵉ)
      ( emb-equivᵉ equiv-Σ-is-fibered-equiv-fibered-map-fibered-equivᵉ)

  fibered-map-fibered-equivᵉ : fibered-equivᵉ fᵉ gᵉ → fibered-mapᵉ fᵉ gᵉ
  fibered-map-fibered-equivᵉ = map-embᵉ emb-fibered-map-fibered-equivᵉ

  is-emb-fibered-map-fibered-equivᵉ : is-embᵉ fibered-map-fibered-equivᵉ
  is-emb-fibered-map-fibered-equivᵉ =
    is-emb-map-embᵉ emb-fibered-map-fibered-equivᵉ
```

### Extensionality for equivalences over

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ)
  where

  extensionality-equiv-overᵉ :
    (eᵉ e'ᵉ : equiv-overᵉ fᵉ gᵉ iᵉ) →
    ( eᵉ ＝ᵉ e'ᵉ) ≃ᵉ
    ( htpy-map-overᵉ fᵉ gᵉ iᵉ
      ( map-over-equiv-overᵉ fᵉ gᵉ iᵉ eᵉ)
      ( map-over-equiv-overᵉ fᵉ gᵉ iᵉ e'ᵉ))
  extensionality-equiv-overᵉ eᵉ e'ᵉ =
    ( extensionality-map-overᵉ fᵉ gᵉ iᵉ
      ( map-over-equiv-overᵉ fᵉ gᵉ iᵉ eᵉ)
      ( map-over-equiv-overᵉ fᵉ gᵉ iᵉ e'ᵉ)) ∘eᵉ
    ( equiv-ap-embᵉ (emb-map-over-equiv-overᵉ fᵉ gᵉ iᵉ))

  htpy-eq-equiv-overᵉ :
    (eᵉ e'ᵉ : equiv-overᵉ fᵉ gᵉ iᵉ) →
    ( eᵉ ＝ᵉ e'ᵉ) →
    ( htpy-map-overᵉ fᵉ gᵉ iᵉ
      ( map-over-equiv-overᵉ fᵉ gᵉ iᵉ eᵉ)
      ( map-over-equiv-overᵉ fᵉ gᵉ iᵉ e'ᵉ))
  htpy-eq-equiv-overᵉ eᵉ e'ᵉ = map-equivᵉ (extensionality-equiv-overᵉ eᵉ e'ᵉ)

  eq-htpy-equiv-overᵉ :
    (eᵉ e'ᵉ : equiv-overᵉ fᵉ gᵉ iᵉ) →
    htpy-map-overᵉ fᵉ gᵉ iᵉ
      ( map-over-equiv-overᵉ fᵉ gᵉ iᵉ eᵉ)
      ( map-over-equiv-overᵉ fᵉ gᵉ iᵉ e'ᵉ) →
    eᵉ ＝ᵉ e'ᵉ
  eq-htpy-equiv-overᵉ eᵉ e'ᵉ = map-inv-equivᵉ (extensionality-equiv-overᵉ eᵉ e'ᵉ)
```

### Extensionality for fibered equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  extensionality-fibered-equivᵉ :
    (eᵉ e'ᵉ : fibered-equivᵉ fᵉ gᵉ) →
    ( eᵉ ＝ᵉ e'ᵉ) ≃ᵉ
    ( htpy-fibered-mapᵉ fᵉ gᵉ
      ( fibered-map-fibered-equivᵉ fᵉ gᵉ eᵉ)
      ( fibered-map-fibered-equivᵉ fᵉ gᵉ e'ᵉ))
  extensionality-fibered-equivᵉ eᵉ e'ᵉ =
    ( extensionality-fibered-mapᵉ fᵉ gᵉ
      ( fibered-map-fibered-equivᵉ fᵉ gᵉ eᵉ)
      ( fibered-map-fibered-equivᵉ fᵉ gᵉ e'ᵉ)) ∘eᵉ
    ( equiv-ap-embᵉ (emb-fibered-map-fibered-equivᵉ fᵉ gᵉ))

  htpy-eq-fibered-equivᵉ :
    (eᵉ e'ᵉ : fibered-equivᵉ fᵉ gᵉ) →
    ( eᵉ ＝ᵉ e'ᵉ) →
    ( htpy-fibered-mapᵉ fᵉ gᵉ
      ( fibered-map-fibered-equivᵉ fᵉ gᵉ eᵉ)
      ( fibered-map-fibered-equivᵉ fᵉ gᵉ e'ᵉ))
  htpy-eq-fibered-equivᵉ eᵉ e'ᵉ = map-equivᵉ (extensionality-fibered-equivᵉ eᵉ e'ᵉ)

  eq-htpy-fibered-equivᵉ :
    (eᵉ e'ᵉ : fibered-equivᵉ fᵉ gᵉ) →
    htpy-fibered-mapᵉ fᵉ gᵉ
      ( fibered-map-fibered-equivᵉ fᵉ gᵉ eᵉ)
      ( fibered-map-fibered-equivᵉ fᵉ gᵉ e'ᵉ) →
    eᵉ ＝ᵉ e'ᵉ
  eq-htpy-fibered-equivᵉ eᵉ e'ᵉ = map-inv-equivᵉ (extensionality-fibered-equivᵉ eᵉ e'ᵉ)
```

### Fibered equivalences are pullback squares

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  {Yᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (ihHᵉ : fibered-mapᵉ fᵉ gᵉ)
  where

  is-fibered-equiv-is-pullbackᵉ :
    is-equivᵉ (pr1ᵉ ihHᵉ) →
    is-pullbackᵉ (pr1ᵉ ihHᵉ) gᵉ (cone-fibered-mapᵉ fᵉ gᵉ ihHᵉ) →
    is-fibered-equiv-fibered-mapᵉ fᵉ gᵉ ihHᵉ
  pr1ᵉ (is-fibered-equiv-is-pullbackᵉ is-equiv-iᵉ pbᵉ) = is-equiv-iᵉ
  pr2ᵉ (is-fibered-equiv-is-pullbackᵉ is-equiv-iᵉ pbᵉ) =
    is-equiv-horizontal-map-is-pullbackᵉ (pr1ᵉ ihHᵉ) gᵉ
      ( cone-fibered-mapᵉ fᵉ gᵉ ihHᵉ)
      ( is-equiv-iᵉ)
      ( pbᵉ)

  is-pullback-is-fibered-equivᵉ :
    is-fibered-equiv-fibered-mapᵉ fᵉ gᵉ ihHᵉ →
    is-pullbackᵉ (pr1ᵉ ihHᵉ) gᵉ (cone-fibered-mapᵉ fᵉ gᵉ ihHᵉ)
  is-pullback-is-fibered-equivᵉ (is-equiv-iᵉ ,ᵉ is-equiv-hᵉ) =
    is-pullback-is-equiv-horizontal-mapsᵉ
      (pr1ᵉ ihHᵉ) gᵉ (cone-fibered-mapᵉ fᵉ gᵉ ihHᵉ) is-equiv-iᵉ is-equiv-hᵉ

  equiv-is-fibered-equiv-is-pullbackᵉ :
    is-equivᵉ (pr1ᵉ ihHᵉ) →
    is-pullbackᵉ (pr1ᵉ ihHᵉ) gᵉ (cone-fibered-mapᵉ fᵉ gᵉ ihHᵉ) ≃ᵉ
    is-fibered-equiv-fibered-mapᵉ fᵉ gᵉ ihHᵉ
  equiv-is-fibered-equiv-is-pullbackᵉ is-equiv-iᵉ =
    equiv-iff-is-propᵉ
      ( is-prop-is-pullbackᵉ (pr1ᵉ ihHᵉ) gᵉ (cone-fibered-mapᵉ fᵉ gᵉ ihHᵉ))
      ( is-prop-is-fibered-equiv-fibered-mapᵉ fᵉ gᵉ ihHᵉ)
      ( is-fibered-equiv-is-pullbackᵉ is-equiv-iᵉ)
      ( is-pullback-is-fibered-equivᵉ)

  equiv-is-pullback-is-fibered-equivᵉ :
    is-equivᵉ (pr1ᵉ ihHᵉ) →
    is-fibered-equiv-fibered-mapᵉ fᵉ gᵉ ihHᵉ ≃ᵉ
    is-pullbackᵉ (pr1ᵉ ihHᵉ) gᵉ (cone-fibered-mapᵉ fᵉ gᵉ ihHᵉ)
  equiv-is-pullback-is-fibered-equivᵉ is-equiv-iᵉ =
    inv-equivᵉ (equiv-is-fibered-equiv-is-pullbackᵉ is-equiv-iᵉ)

  fibered-equiv-is-pullbackᵉ :
    is-equivᵉ (pr1ᵉ ihHᵉ) →
    is-pullbackᵉ (pr1ᵉ ihHᵉ) gᵉ (cone-fibered-mapᵉ fᵉ gᵉ ihHᵉ) →
    fibered-equivᵉ fᵉ gᵉ
  pr1ᵉ (pr1ᵉ (fibered-equiv-is-pullbackᵉ is-equiv-iᵉ pbᵉ)) = pr1ᵉ ihHᵉ
  pr2ᵉ (pr1ᵉ (fibered-equiv-is-pullbackᵉ is-equiv-iᵉ pbᵉ)) = is-equiv-iᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (fibered-equiv-is-pullbackᵉ is-equiv-iᵉ pbᵉ))) = pr1ᵉ (pr2ᵉ ihHᵉ)
  pr2ᵉ (pr1ᵉ (pr2ᵉ (fibered-equiv-is-pullbackᵉ is-equiv-iᵉ pbᵉ))) =
    pr2ᵉ (is-fibered-equiv-is-pullbackᵉ is-equiv-iᵉ pbᵉ)
  pr2ᵉ (pr2ᵉ (fibered-equiv-is-pullbackᵉ is-equiv-iᵉ pbᵉ)) = pr2ᵉ (pr2ᵉ ihHᵉ)

is-pullback-fibered-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  {Yᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  (eᵉ : fibered-equivᵉ fᵉ gᵉ) →
  is-pullbackᵉ
    ( pr1ᵉ (pr1ᵉ eᵉ))
    ( gᵉ)
    ( cone-fibered-mapᵉ fᵉ gᵉ (fibered-map-fibered-equivᵉ fᵉ gᵉ eᵉ))
is-pullback-fibered-equivᵉ fᵉ gᵉ ((iᵉ ,ᵉ is-equiv-iᵉ) ,ᵉ (hᵉ ,ᵉ is-equiv-hᵉ) ,ᵉ Hᵉ) =
  is-pullback-is-fibered-equivᵉ fᵉ gᵉ (iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ) (is-equiv-iᵉ ,ᵉ is-equiv-hᵉ)
```

## Examples

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  self-fibered-equivᵉ : Aᵉ ≃ᵉ Bᵉ → fibered-equivᵉ idᵉ idᵉ
  pr1ᵉ (self-fibered-equivᵉ eᵉ) = eᵉ
  pr1ᵉ (pr2ᵉ (self-fibered-equivᵉ eᵉ)) = eᵉ
  pr2ᵉ (pr2ᵉ (self-fibered-equivᵉ eᵉ)) = refl-htpyᵉ

  id-fibered-equivᵉ : (fᵉ : Aᵉ → Bᵉ) → fibered-equivᵉ fᵉ fᵉ
  pr1ᵉ (id-fibered-equivᵉ fᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (id-fibered-equivᵉ fᵉ)) = id-equivᵉ
  pr2ᵉ (pr2ᵉ (id-fibered-equivᵉ fᵉ)) = refl-htpyᵉ

  id-fibered-equiv-htpyᵉ : (fᵉ gᵉ : Aᵉ → Bᵉ) → fᵉ ~ᵉ gᵉ → fibered-equivᵉ fᵉ gᵉ
  pr1ᵉ (id-fibered-equiv-htpyᵉ fᵉ gᵉ Hᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (id-fibered-equiv-htpyᵉ fᵉ gᵉ Hᵉ)) = id-equivᵉ
  pr2ᵉ (pr2ᵉ (id-fibered-equiv-htpyᵉ fᵉ gᵉ Hᵉ)) = Hᵉ
```

## See also

-ᵉ [Equivalencesᵉ ofᵉ arrows](foundation.equivalences-arrows.mdᵉ) forᵉ theᵉ sameᵉ
  conceptᵉ underᵉ aᵉ differentᵉ name.ᵉ