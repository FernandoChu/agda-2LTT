# Functoriality of cartesian product types

```agda
module foundation.functoriality-cartesian-product-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ **functorialᵉ action**ᵉ ofᵉ theᵉ
[cartesianᵉ product](foundation-core.cartesian-product-types.mdᵉ) takesᵉ twoᵉ mapsᵉ
`fᵉ : Aᵉ → B`ᵉ andᵉ `gᵉ : Cᵉ → D`ᵉ andᵉ returnsᵉ aᵉ mapᵉ

```text
  fᵉ ×ᵉ gᵉ : Aᵉ ×ᵉ Bᵉ → Cᵉ ×ᵉ D`ᵉ
```

betweenᵉ theᵉ cartesianᵉ productᵉ types.ᵉ Thisᵉ functorialᵉ actionᵉ isᵉ _bifunctorialᵉ_ in
theᵉ senseᵉ thatᵉ forᵉ anyᵉ twoᵉ mapsᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ `gᵉ : Cᵉ → D`ᵉ theᵉ diagramᵉ

```text
          f×1ᵉ
    Aᵉ ×ᵉ Cᵉ --->ᵉ Bᵉ ×ᵉ Cᵉ
      |   \ᵉ      |
  1×gᵉ |    \f×gᵉ  | 1×gᵉ
      |     \ᵉ    |
      ∨ᵉ      ∨ᵉ   ∨ᵉ
    Aᵉ ×ᵉ Dᵉ --->ᵉ Bᵉ ×ᵉ Dᵉ
          f×1ᵉ
```

commutes.ᵉ

## Definitions

### The functorial action of cartesian product types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Cᵉ → Dᵉ)
  where

  map-productᵉ : (Aᵉ ×ᵉ Cᵉ) → (Bᵉ ×ᵉ Dᵉ)

  pr1ᵉ (map-productᵉ tᵉ) = fᵉ (pr1ᵉ tᵉ)
  pr2ᵉ (map-productᵉ tᵉ) = gᵉ (pr2ᵉ tᵉ)

  map-product-pr1ᵉ : pr1ᵉ ∘ᵉ map-productᵉ ~ᵉ fᵉ ∘ᵉ pr1ᵉ
  map-product-pr1ᵉ (aᵉ ,ᵉ cᵉ) = reflᵉ

  map-product-pr2ᵉ : pr2ᵉ ∘ᵉ map-productᵉ ~ᵉ gᵉ ∘ᵉ pr2ᵉ
  map-product-pr2ᵉ (aᵉ ,ᵉ cᵉ) = reflᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Cᵉ → Dᵉ)
  where

  coherence-square-map-productᵉ :
    coherence-square-mapsᵉ
      ( map-productᵉ fᵉ idᵉ)
      ( map-productᵉ idᵉ gᵉ)
      ( map-productᵉ idᵉ gᵉ)
      ( map-productᵉ fᵉ idᵉ)
  coherence-square-map-productᵉ tᵉ = reflᵉ
```

## Properties

### Functoriality of products preserves identity maps

```agda
map-product-idᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  map-productᵉ (idᵉ {Aᵉ = Aᵉ}) (idᵉ {Aᵉ = Bᵉ}) ~ᵉ idᵉ
map-product-idᵉ (aᵉ ,ᵉ bᵉ) = reflᵉ
```

### Functoriality of products preserves composition

```agda
preserves-comp-map-productᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  {Eᵉ : UUᵉ l5ᵉ} {Fᵉ : UUᵉ l6ᵉ} (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Dᵉ) (hᵉ : Cᵉ → Eᵉ) (kᵉ : Dᵉ → Fᵉ) →
  map-productᵉ (hᵉ ∘ᵉ fᵉ) (kᵉ ∘ᵉ gᵉ) ~ᵉ map-productᵉ hᵉ kᵉ ∘ᵉ map-productᵉ fᵉ gᵉ
preserves-comp-map-productᵉ fᵉ gᵉ hᵉ kᵉ tᵉ = reflᵉ
```

### Functoriality of products preserves homotopies

```agda
htpy-map-productᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  {fᵉ f'ᵉ : Aᵉ → Cᵉ} (Hᵉ : fᵉ ~ᵉ f'ᵉ) {gᵉ g'ᵉ : Bᵉ → Dᵉ} (Kᵉ : gᵉ ~ᵉ g'ᵉ) →
  map-productᵉ fᵉ gᵉ ~ᵉ map-productᵉ f'ᵉ g'ᵉ
htpy-map-productᵉ Hᵉ Kᵉ (aᵉ ,ᵉ bᵉ) = eq-pairᵉ (Hᵉ aᵉ) (Kᵉ bᵉ)
```

### Functoriality of products preserves equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  where

  map-inv-map-productᵉ :
    (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Dᵉ) → is-equivᵉ fᵉ → is-equivᵉ gᵉ → Cᵉ ×ᵉ Dᵉ → Aᵉ ×ᵉ Bᵉ
  pr1ᵉ (map-inv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ (cᵉ ,ᵉ dᵉ)) = map-inv-is-equivᵉ Hᵉ cᵉ
  pr2ᵉ (map-inv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ (cᵉ ,ᵉ dᵉ)) = map-inv-is-equivᵉ Kᵉ dᵉ

  is-section-map-inv-map-productᵉ :
    (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Dᵉ) (Hᵉ : is-equivᵉ fᵉ) (Kᵉ : is-equivᵉ gᵉ) →
    map-productᵉ fᵉ gᵉ ∘ᵉ map-inv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ ~ᵉ idᵉ
  is-section-map-inv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ =
    htpy-map-productᵉ
      ( is-section-map-inv-is-equivᵉ Hᵉ)
      ( is-section-map-inv-is-equivᵉ Kᵉ)

  is-retraction-map-inv-map-productᵉ :
    (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Dᵉ) (Hᵉ : is-equivᵉ fᵉ) (Kᵉ : is-equivᵉ gᵉ) →
    map-inv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ ∘ᵉ map-productᵉ fᵉ gᵉ ~ᵉ idᵉ
  is-retraction-map-inv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ =
    htpy-map-productᵉ
      ( is-retraction-map-inv-is-equivᵉ Hᵉ)
      ( is-retraction-map-inv-is-equivᵉ Kᵉ)

  is-equiv-map-productᵉ :
    (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Dᵉ) →
    is-equivᵉ fᵉ → is-equivᵉ gᵉ → is-equivᵉ (map-productᵉ fᵉ gᵉ)
  is-equiv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ)
      ( is-section-map-inv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ)
      ( is-retraction-map-inv-map-productᵉ fᵉ gᵉ Hᵉ Kᵉ)

  equiv-productᵉ : Aᵉ ≃ᵉ Cᵉ → Bᵉ ≃ᵉ Dᵉ → Aᵉ ×ᵉ Bᵉ ≃ᵉ Cᵉ ×ᵉ Dᵉ
  pr1ᵉ (equiv-productᵉ (fᵉ ,ᵉ is-equiv-fᵉ) (gᵉ ,ᵉ is-equiv-gᵉ)) = map-productᵉ fᵉ gᵉ
  pr2ᵉ (equiv-productᵉ (fᵉ ,ᵉ is-equiv-fᵉ) (gᵉ ,ᵉ is-equiv-gᵉ)) =
    is-equiv-map-productᵉ fᵉ gᵉ is-equiv-fᵉ is-equiv-gᵉ
```

### Functoriality of products preserves equivalences in either factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  equiv-product-leftᵉ : Aᵉ ≃ᵉ Cᵉ → Aᵉ ×ᵉ Bᵉ ≃ᵉ Cᵉ ×ᵉ Bᵉ
  equiv-product-leftᵉ fᵉ = equiv-productᵉ fᵉ id-equivᵉ

  equiv-product-rightᵉ : Bᵉ ≃ᵉ Cᵉ → Aᵉ ×ᵉ Bᵉ ≃ᵉ Aᵉ ×ᵉ Cᵉ
  equiv-product-rightᵉ = equiv-productᵉ id-equivᵉ
```

### The fibers of `map-product f g`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Dᵉ) (tᵉ : Cᵉ ×ᵉ Dᵉ)
  where

  map-compute-fiber-map-productᵉ :
    fiberᵉ (map-productᵉ fᵉ gᵉ) tᵉ → fiberᵉ fᵉ (pr1ᵉ tᵉ) ×ᵉ fiberᵉ gᵉ (pr2ᵉ tᵉ)
  pr1ᵉ (pr1ᵉ (map-compute-fiber-map-productᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ reflᵉ))) = aᵉ
  pr2ᵉ (pr1ᵉ (map-compute-fiber-map-productᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ reflᵉ))) = reflᵉ
  pr1ᵉ (pr2ᵉ (map-compute-fiber-map-productᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ reflᵉ))) = bᵉ
  pr2ᵉ (pr2ᵉ (map-compute-fiber-map-productᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ reflᵉ))) = reflᵉ

  map-inv-compute-fiber-map-productᵉ :
    fiberᵉ fᵉ (pr1ᵉ tᵉ) ×ᵉ fiberᵉ gᵉ (pr2ᵉ tᵉ) → fiberᵉ (map-productᵉ fᵉ gᵉ) tᵉ
  pr1ᵉ (pr1ᵉ (map-inv-compute-fiber-map-productᵉ ((xᵉ ,ᵉ reflᵉ) ,ᵉ (yᵉ ,ᵉ reflᵉ)))) = xᵉ
  pr2ᵉ (pr1ᵉ (map-inv-compute-fiber-map-productᵉ ((xᵉ ,ᵉ reflᵉ) ,ᵉ (yᵉ ,ᵉ reflᵉ)))) = yᵉ
  pr2ᵉ (map-inv-compute-fiber-map-productᵉ ((xᵉ ,ᵉ reflᵉ) ,ᵉ (yᵉ ,ᵉ reflᵉ))) = reflᵉ

  is-section-map-inv-compute-fiber-map-productᵉ :
    map-compute-fiber-map-productᵉ ∘ᵉ map-inv-compute-fiber-map-productᵉ ~ᵉ idᵉ
  is-section-map-inv-compute-fiber-map-productᵉ ((xᵉ ,ᵉ reflᵉ) ,ᵉ (yᵉ ,ᵉ reflᵉ)) = reflᵉ

  is-retraction-map-inv-compute-fiber-map-productᵉ :
    map-inv-compute-fiber-map-productᵉ ∘ᵉ map-compute-fiber-map-productᵉ ~ᵉ idᵉ
  is-retraction-map-inv-compute-fiber-map-productᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ reflᵉ) = reflᵉ

  is-equiv-map-compute-fiber-map-productᵉ :
    is-equivᵉ map-compute-fiber-map-productᵉ
  is-equiv-map-compute-fiber-map-productᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-compute-fiber-map-productᵉ)
      ( is-section-map-inv-compute-fiber-map-productᵉ)
      ( is-retraction-map-inv-compute-fiber-map-productᵉ)

  compute-fiber-map-productᵉ :
    fiberᵉ (map-productᵉ fᵉ gᵉ) tᵉ ≃ᵉ (fiberᵉ fᵉ (pr1ᵉ tᵉ) ×ᵉ fiberᵉ gᵉ (pr2ᵉ tᵉ))
  pr1ᵉ compute-fiber-map-productᵉ = map-compute-fiber-map-productᵉ
  pr2ᵉ compute-fiber-map-productᵉ = is-equiv-map-compute-fiber-map-productᵉ
```

### If `map-product f g : A × B → C × D` is an equivalence, then we have `D → is-equiv f` and `C → is-equiv g`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Dᵉ)
  where

  is-equiv-left-factor-is-equiv-map-product'ᵉ :
    Dᵉ → is-equivᵉ (map-productᵉ fᵉ gᵉ) → is-equivᵉ fᵉ
  is-equiv-left-factor-is-equiv-map-product'ᵉ
    dᵉ is-equiv-fgᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ xᵉ →
        is-contr-left-factor-productᵉ
          ( fiberᵉ fᵉ xᵉ)
          ( fiberᵉ gᵉ dᵉ)
          ( is-contr-is-equiv'ᵉ
            ( fiberᵉ (map-productᵉ fᵉ gᵉ) (xᵉ ,ᵉ dᵉ))
            ( map-compute-fiber-map-productᵉ fᵉ gᵉ (xᵉ ,ᵉ dᵉ))
            ( is-equiv-map-compute-fiber-map-productᵉ fᵉ gᵉ (xᵉ ,ᵉ dᵉ))
            ( is-contr-map-is-equivᵉ is-equiv-fgᵉ (xᵉ ,ᵉ dᵉ))))

  is-equiv-right-factor-is-equiv-map-product'ᵉ :
    Cᵉ → is-equivᵉ (map-productᵉ fᵉ gᵉ) → is-equivᵉ gᵉ
  is-equiv-right-factor-is-equiv-map-product'ᵉ
    cᵉ is-equiv-fgᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ yᵉ →
        is-contr-right-factor-productᵉ
          ( fiberᵉ fᵉ cᵉ)
          ( fiberᵉ gᵉ yᵉ)
          ( is-contr-is-equiv'ᵉ
            ( fiberᵉ (map-productᵉ fᵉ gᵉ) (cᵉ ,ᵉ yᵉ))
            ( map-compute-fiber-map-productᵉ fᵉ gᵉ (cᵉ ,ᵉ yᵉ))
            ( is-equiv-map-compute-fiber-map-productᵉ fᵉ gᵉ (cᵉ ,ᵉ yᵉ))
            ( is-contr-map-is-equivᵉ is-equiv-fgᵉ (cᵉ ,ᵉ yᵉ))))
```

### The functorial action of products on arrows

Givenᵉ aᵉ pairᵉ ofᵉ [morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ)
`αᵉ : fᵉ → g`ᵉ andᵉ `βᵉ : hᵉ → i`,ᵉ thereᵉ isᵉ anᵉ inducedᵉ morphismᵉ ofᵉ arrowsᵉ
`αᵉ ×ᵉ βᵉ : fᵉ ×ᵉ hᵉ → gᵉ ×ᵉ i`ᵉ andᵉ thisᵉ constructionᵉ isᵉ functorial.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {Cᵉ : UUᵉ l5ᵉ} {Dᵉ : UUᵉ l6ᵉ} {Zᵉ : UUᵉ l7ᵉ} {Wᵉ : UUᵉ l8ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Cᵉ → Dᵉ) (iᵉ : Zᵉ → Wᵉ)
  (αᵉ : hom-arrowᵉ fᵉ gᵉ) (βᵉ : hom-arrowᵉ hᵉ iᵉ)
  where

  product-hom-arrowᵉ : hom-arrowᵉ (map-productᵉ fᵉ hᵉ) (map-productᵉ gᵉ iᵉ)
  product-hom-arrowᵉ =
    ( ( map-productᵉ
        ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( map-domain-hom-arrowᵉ hᵉ iᵉ βᵉ)) ,ᵉ
      ( map-productᵉ
        ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( map-codomain-hom-arrowᵉ hᵉ iᵉ βᵉ)) ,ᵉ
      ( htpy-map-productᵉ
        ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( coh-hom-arrowᵉ hᵉ iᵉ βᵉ)))
```

## See also

-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ cartesianᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in cartesianᵉ productᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).ᵉ
-ᵉ Theᵉ universalᵉ propertyᵉ ofᵉ cartesianᵉ productᵉ typesᵉ isᵉ treatedᵉ in
  [`foundation.universal-property-cartesian-product-types`](foundation.universal-property-cartesian-product-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ coproductᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-coproduct-types`](foundation.functoriality-coproduct-types.md).ᵉ