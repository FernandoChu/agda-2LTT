# Functoriality of dependent pair types

```agda
module foundation-core.functoriality-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ anyᵉ familyᵉ ofᵉ mapsᵉ `gᵉ : (aᵉ : Aᵉ) → Cᵉ aᵉ → Dᵉ (fᵉ a)`ᵉ
togetherᵉ induceᵉ aᵉ mapᵉ `map-Σᵉ Dᵉ fᵉ gᵉ : Σᵉ Aᵉ Cᵉ → Σᵉ Bᵉ D`.ᵉ Specificᵉ instancesᵉ ofᵉ thisᵉ
constructionᵉ areᵉ alsoᵉ veryᵉ usefulᵉ: ifᵉ weᵉ takeᵉ `f`ᵉ to beᵉ theᵉ identityᵉ map,ᵉ thenᵉ
weᵉ seeᵉ thatᵉ anyᵉ familyᵉ ofᵉ mapsᵉ `gᵉ : (aᵉ : Aᵉ) → Cᵉ aᵉ → Dᵉ a`ᵉ inducesᵉ aᵉ mapᵉ onᵉ totalᵉ
spacesᵉ `Σᵉ Aᵉ Cᵉ → Σᵉ Aᵉ D`;ᵉ ifᵉ weᵉ takeᵉ `g`ᵉ to beᵉ theᵉ familyᵉ ofᵉ identityᵉ maps,ᵉ thenᵉ
weᵉ seeᵉ thatᵉ forᵉ anyᵉ familyᵉ `D`ᵉ overᵉ `B`,ᵉ anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ inducesᵉ aᵉ mapᵉ
`Σᵉ Aᵉ (Dᵉ ∘ᵉ fᵉ) → Σᵉ Bᵉ D`.ᵉ

## Definitions

### The induced map on total spaces

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ)
  where
```

Anyᵉ familyᵉ ofᵉ mapsᵉ inducesᵉ aᵉ mapᵉ onᵉ theᵉ totalᵉ spaces.ᵉ

```agda
  totᵉ : Σᵉ Aᵉ Bᵉ → Σᵉ Aᵉ Cᵉ
  pr1ᵉ (totᵉ tᵉ) = pr1ᵉ tᵉ
  pr2ᵉ (totᵉ tᵉ) = fᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ)
```

### Any map `f : A → B` induces a map `Σ A (C ∘ f) → Σ B C`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ)
  where

  map-Σ-map-baseᵉ : Σᵉ Aᵉ (λ xᵉ → Cᵉ (fᵉ xᵉ)) → Σᵉ Bᵉ Cᵉ
  pr1ᵉ (map-Σ-map-baseᵉ sᵉ) = fᵉ (pr1ᵉ sᵉ)
  pr2ᵉ (map-Σ-map-baseᵉ sᵉ) = pr2ᵉ sᵉ
```

### The functorial action of dependent pair types, and its defining homotopy

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Dᵉ : Bᵉ → UUᵉ l4ᵉ)
  where

  map-Σᵉ :
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)) → Σᵉ Aᵉ Cᵉ → Σᵉ Bᵉ Dᵉ
  pr1ᵉ (map-Σᵉ fᵉ gᵉ tᵉ) = fᵉ (pr1ᵉ tᵉ)
  pr2ᵉ (map-Σᵉ fᵉ gᵉ tᵉ) = gᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ)

  triangle-map-Σᵉ :
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)) →
    (map-Σᵉ fᵉ gᵉ) ~ᵉ (map-Σ-map-baseᵉ fᵉ Dᵉ ∘ᵉ totᵉ gᵉ)
  triangle-map-Σᵉ fᵉ gᵉ tᵉ = reflᵉ
```

## Properties

### The map `map-Σ` preserves homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Dᵉ : Bᵉ → UUᵉ l4ᵉ)
  where

  htpy-map-Σᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ f'ᵉ)
    (gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)) {g'ᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (f'ᵉ xᵉ)}
    (Kᵉ : (xᵉ : Aᵉ) → ((trᵉ Dᵉ (Hᵉ xᵉ)) ∘ᵉ (gᵉ xᵉ)) ~ᵉ (g'ᵉ xᵉ)) →
    (map-Σᵉ Dᵉ fᵉ gᵉ) ~ᵉ (map-Σᵉ Dᵉ f'ᵉ g'ᵉ)
  htpy-map-Σᵉ Hᵉ gᵉ Kᵉ tᵉ = eq-pair-Σ'ᵉ (pairᵉ (Hᵉ (pr1ᵉ tᵉ)) (Kᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ)))
```

### The map `tot` preserves homotopies

```agda
tot-htpyᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ} → (Hᵉ : (xᵉ : Aᵉ) → fᵉ xᵉ ~ᵉ gᵉ xᵉ) → totᵉ fᵉ ~ᵉ totᵉ gᵉ
tot-htpyᵉ Hᵉ (pairᵉ xᵉ yᵉ) = eq-pair-eq-fiberᵉ (Hᵉ xᵉ yᵉ)
```

### The map `tot` preserves identity maps

```agda
tot-idᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  (totᵉ (λ xᵉ (yᵉ : Bᵉ xᵉ) → yᵉ)) ~ᵉ idᵉ
tot-idᵉ Bᵉ (pairᵉ xᵉ yᵉ) = reflᵉ
```

### The map `tot` preserves composition

```agda
preserves-comp-totᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {B'ᵉ : Aᵉ → UUᵉ l3ᵉ} {B''ᵉ : Aᵉ → UUᵉ l4ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → B'ᵉ xᵉ) (gᵉ : (xᵉ : Aᵉ) → B'ᵉ xᵉ → B''ᵉ xᵉ) →
  totᵉ (λ xᵉ → (gᵉ xᵉ) ∘ᵉ (fᵉ xᵉ)) ~ᵉ ((totᵉ gᵉ) ∘ᵉ (totᵉ fᵉ))
preserves-comp-totᵉ fᵉ gᵉ (pairᵉ xᵉ yᵉ) = reflᵉ
```

### The fibers of `tot`

Weᵉ showᵉ thatᵉ forᵉ anyᵉ familyᵉ ofᵉ maps,ᵉ theᵉ fiberᵉ ofᵉ theᵉ inducedᵉ mapᵉ onᵉ totalᵉ
spacesᵉ areᵉ equivalentᵉ to theᵉ fibersᵉ ofᵉ theᵉ mapsᵉ in theᵉ family.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ)
  where

  map-compute-fiber-totᵉ :
    (tᵉ : Σᵉ Aᵉ Cᵉ) → fiberᵉ (totᵉ fᵉ) tᵉ → fiberᵉ (fᵉ (pr1ᵉ tᵉ)) (pr2ᵉ tᵉ)
  pr1ᵉ (map-compute-fiber-totᵉ .(totᵉ fᵉ (pairᵉ xᵉ yᵉ)) (pairᵉ (pairᵉ xᵉ yᵉ) reflᵉ)) = yᵉ
  pr2ᵉ (map-compute-fiber-totᵉ .(totᵉ fᵉ (pairᵉ xᵉ yᵉ)) (pairᵉ (pairᵉ xᵉ yᵉ) reflᵉ)) = reflᵉ

  map-inv-compute-fiber-totᵉ :
    (tᵉ : Σᵉ Aᵉ Cᵉ) → fiberᵉ (fᵉ (pr1ᵉ tᵉ)) (pr2ᵉ tᵉ) → fiberᵉ (totᵉ fᵉ) tᵉ
  pr1ᵉ (pr1ᵉ (map-inv-compute-fiber-totᵉ (pairᵉ aᵉ .(fᵉ aᵉ yᵉ)) (pairᵉ yᵉ reflᵉ))) = aᵉ
  pr2ᵉ (pr1ᵉ (map-inv-compute-fiber-totᵉ (pairᵉ aᵉ .(fᵉ aᵉ yᵉ)) (pairᵉ yᵉ reflᵉ))) = yᵉ
  pr2ᵉ (map-inv-compute-fiber-totᵉ (pairᵉ aᵉ .(fᵉ aᵉ yᵉ)) (pairᵉ yᵉ reflᵉ)) = reflᵉ

  is-section-map-inv-compute-fiber-totᵉ :
    (tᵉ : Σᵉ Aᵉ Cᵉ) → (map-compute-fiber-totᵉ tᵉ ∘ᵉ map-inv-compute-fiber-totᵉ tᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-fiber-totᵉ (pairᵉ xᵉ .(fᵉ xᵉ yᵉ)) (pairᵉ yᵉ reflᵉ) = reflᵉ

  is-retraction-map-inv-compute-fiber-totᵉ :
    (tᵉ : Σᵉ Aᵉ Cᵉ) → (map-inv-compute-fiber-totᵉ tᵉ ∘ᵉ map-compute-fiber-totᵉ tᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-fiber-totᵉ ._ (pairᵉ (pairᵉ xᵉ yᵉ) reflᵉ) =
    reflᵉ

  abstract
    is-equiv-map-compute-fiber-totᵉ :
      (tᵉ : Σᵉ Aᵉ Cᵉ) → is-equivᵉ (map-compute-fiber-totᵉ tᵉ)
    is-equiv-map-compute-fiber-totᵉ tᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-compute-fiber-totᵉ tᵉ)
        ( is-section-map-inv-compute-fiber-totᵉ tᵉ)
        ( is-retraction-map-inv-compute-fiber-totᵉ tᵉ)

  compute-fiber-totᵉ : (tᵉ : Σᵉ Aᵉ Cᵉ) → fiberᵉ (totᵉ fᵉ) tᵉ ≃ᵉ fiberᵉ (fᵉ (pr1ᵉ tᵉ)) (pr2ᵉ tᵉ)
  pr1ᵉ (compute-fiber-totᵉ tᵉ) = map-compute-fiber-totᵉ tᵉ
  pr2ᵉ (compute-fiber-totᵉ tᵉ) = is-equiv-map-compute-fiber-totᵉ tᵉ

  abstract
    is-equiv-map-inv-compute-fiber-totᵉ :
      (tᵉ : Σᵉ Aᵉ Cᵉ) → is-equivᵉ (map-inv-compute-fiber-totᵉ tᵉ)
    is-equiv-map-inv-compute-fiber-totᵉ tᵉ =
      is-equiv-is-invertibleᵉ
        ( map-compute-fiber-totᵉ tᵉ)
        ( is-retraction-map-inv-compute-fiber-totᵉ tᵉ)
        ( is-section-map-inv-compute-fiber-totᵉ tᵉ)

  inv-compute-fiber-totᵉ :
    (tᵉ : Σᵉ Aᵉ Cᵉ) → fiberᵉ (fᵉ (pr1ᵉ tᵉ)) (pr2ᵉ tᵉ) ≃ᵉ fiberᵉ (totᵉ fᵉ) tᵉ
  pr1ᵉ (inv-compute-fiber-totᵉ tᵉ) = map-inv-compute-fiber-totᵉ tᵉ
  pr2ᵉ (inv-compute-fiber-totᵉ tᵉ) = is-equiv-map-inv-compute-fiber-totᵉ tᵉ
```

### A family of maps `f` is a family of equivalences if and only if `tot f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ}
  where

  abstract
    is-equiv-tot-is-fiberwise-equivᵉ : is-fiberwise-equivᵉ fᵉ → is-equivᵉ (totᵉ fᵉ)
    is-equiv-tot-is-fiberwise-equivᵉ Hᵉ =
      is-equiv-is-contr-mapᵉ
        ( λ tᵉ →
          is-contr-is-equivᵉ
            ( fiberᵉ (fᵉ (pr1ᵉ tᵉ)) (pr2ᵉ tᵉ))
            ( map-compute-fiber-totᵉ fᵉ tᵉ)
            ( is-equiv-map-compute-fiber-totᵉ fᵉ tᵉ)
            ( is-contr-map-is-equivᵉ (Hᵉ (pr1ᵉ tᵉ)) (pr2ᵉ tᵉ)))

  abstract
    is-fiberwise-equiv-is-equiv-totᵉ : is-equivᵉ (totᵉ fᵉ) → is-fiberwise-equivᵉ fᵉ
    is-fiberwise-equiv-is-equiv-totᵉ is-equiv-tot-fᵉ xᵉ =
      is-equiv-is-contr-mapᵉ
        ( λ zᵉ →
          is-contr-is-equiv'ᵉ
            ( fiberᵉ (totᵉ fᵉ) (pairᵉ xᵉ zᵉ))
            ( map-compute-fiber-totᵉ fᵉ (pairᵉ xᵉ zᵉ))
            ( is-equiv-map-compute-fiber-totᵉ fᵉ (pairᵉ xᵉ zᵉ))
            ( is-contr-map-is-equivᵉ is-equiv-tot-fᵉ (pairᵉ xᵉ zᵉ)))
```

### The action of `tot` on equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  equiv-totᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Cᵉ xᵉ) → (Σᵉ Aᵉ Bᵉ) ≃ᵉ (Σᵉ Aᵉ Cᵉ)
  pr1ᵉ (equiv-totᵉ eᵉ) = totᵉ (λ xᵉ → map-equivᵉ (eᵉ xᵉ))
  pr2ᵉ (equiv-totᵉ eᵉ) =
    is-equiv-tot-is-fiberwise-equivᵉ (λ xᵉ → is-equiv-map-equivᵉ (eᵉ xᵉ))
```

### The fibers of `map-Σ-map-base`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ)
  where

  fiber-map-Σ-map-base-fiberᵉ :
    (tᵉ : Σᵉ Bᵉ Cᵉ) → fiberᵉ fᵉ (pr1ᵉ tᵉ) → fiberᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ) tᵉ
  pr1ᵉ (pr1ᵉ (fiber-map-Σ-map-base-fiberᵉ (pairᵉ .(fᵉ xᵉ) zᵉ) (pairᵉ xᵉ reflᵉ))) = xᵉ
  pr2ᵉ (pr1ᵉ (fiber-map-Σ-map-base-fiberᵉ (pairᵉ .(fᵉ xᵉ) zᵉ) (pairᵉ xᵉ reflᵉ))) = zᵉ
  pr2ᵉ (fiber-map-Σ-map-base-fiberᵉ (pairᵉ .(fᵉ xᵉ) zᵉ) (pairᵉ xᵉ reflᵉ)) = reflᵉ

  fiber-fiber-map-Σ-map-baseᵉ :
    (tᵉ : Σᵉ Bᵉ Cᵉ) → fiberᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ) tᵉ → fiberᵉ fᵉ (pr1ᵉ tᵉ)
  pr1ᵉ
    ( fiber-fiber-map-Σ-map-baseᵉ
      .(map-Σ-map-baseᵉ fᵉ Cᵉ (pairᵉ xᵉ zᵉ)) (pairᵉ (pairᵉ xᵉ zᵉ) reflᵉ)) = xᵉ
  pr2ᵉ
    ( fiber-fiber-map-Σ-map-baseᵉ
      .(map-Σ-map-baseᵉ fᵉ Cᵉ (pairᵉ xᵉ zᵉ)) (pairᵉ (pairᵉ xᵉ zᵉ) reflᵉ)) = reflᵉ

  is-section-fiber-fiber-map-Σ-map-baseᵉ :
    (tᵉ : Σᵉ Bᵉ Cᵉ) →
    (fiber-map-Σ-map-base-fiberᵉ tᵉ ∘ᵉ fiber-fiber-map-Σ-map-baseᵉ tᵉ) ~ᵉ idᵉ
  is-section-fiber-fiber-map-Σ-map-baseᵉ .(pairᵉ (fᵉ xᵉ) zᵉ) (pairᵉ (pairᵉ xᵉ zᵉ) reflᵉ) =
    reflᵉ

  is-retraction-fiber-fiber-map-Σ-map-baseᵉ :
    (tᵉ : Σᵉ Bᵉ Cᵉ) →
    (fiber-fiber-map-Σ-map-baseᵉ tᵉ ∘ᵉ fiber-map-Σ-map-base-fiberᵉ tᵉ) ~ᵉ idᵉ
  is-retraction-fiber-fiber-map-Σ-map-baseᵉ (pairᵉ .(fᵉ xᵉ) zᵉ) (pairᵉ xᵉ reflᵉ) = reflᵉ

  abstract
    is-equiv-fiber-map-Σ-map-base-fiberᵉ :
      (tᵉ : Σᵉ Bᵉ Cᵉ) → is-equivᵉ (fiber-map-Σ-map-base-fiberᵉ tᵉ)
    is-equiv-fiber-map-Σ-map-base-fiberᵉ tᵉ =
      is-equiv-is-invertibleᵉ
        ( fiber-fiber-map-Σ-map-baseᵉ tᵉ)
        ( is-section-fiber-fiber-map-Σ-map-baseᵉ tᵉ)
        ( is-retraction-fiber-fiber-map-Σ-map-baseᵉ tᵉ)

  equiv-fiber-map-Σ-map-base-fiberᵉ :
    (tᵉ : Σᵉ Bᵉ Cᵉ) → fiberᵉ fᵉ (pr1ᵉ tᵉ) ≃ᵉ fiberᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ) tᵉ
  pr1ᵉ (equiv-fiber-map-Σ-map-base-fiberᵉ tᵉ) = fiber-map-Σ-map-base-fiberᵉ tᵉ
  pr2ᵉ (equiv-fiber-map-Σ-map-base-fiberᵉ tᵉ) =
    is-equiv-fiber-map-Σ-map-base-fiberᵉ tᵉ
```

### If `f : A → B` is a contractible map, then so is `map-Σ-map-base f C`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ)
  where

  abstract
    is-contr-map-map-Σ-map-baseᵉ :
      is-contr-mapᵉ fᵉ → is-contr-mapᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ)
    is-contr-map-map-Σ-map-baseᵉ is-contr-fᵉ (pairᵉ yᵉ zᵉ) =
      is-contr-equiv'ᵉ
        ( fiberᵉ fᵉ yᵉ)
        ( equiv-fiber-map-Σ-map-base-fiberᵉ fᵉ Cᵉ (pairᵉ yᵉ zᵉ))
        ( is-contr-fᵉ yᵉ)
```

### If `f : A → B` is an equivalence, then so is `map-Σ-map-base f C`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ)
  where

  abstract
    is-equiv-map-Σ-map-baseᵉ : is-equivᵉ fᵉ → is-equivᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ)
    is-equiv-map-Σ-map-baseᵉ is-equiv-fᵉ =
      is-equiv-is-contr-mapᵉ
        ( is-contr-map-map-Σ-map-baseᵉ fᵉ Cᵉ (is-contr-map-is-equivᵉ is-equiv-fᵉ))

equiv-Σ-equiv-baseᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Cᵉ : Bᵉ → UUᵉ l3ᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
  Σᵉ Aᵉ (Cᵉ ∘ᵉ map-equivᵉ eᵉ) ≃ᵉ Σᵉ Bᵉ Cᵉ
pr1ᵉ (equiv-Σ-equiv-baseᵉ Cᵉ (pairᵉ fᵉ is-equiv-fᵉ)) = map-Σ-map-baseᵉ fᵉ Cᵉ
pr2ᵉ (equiv-Σ-equiv-baseᵉ Cᵉ (pairᵉ fᵉ is-equiv-fᵉ)) =
  is-equiv-map-Σ-map-baseᵉ fᵉ Cᵉ is-equiv-fᵉ
```

### The functorial action of dependent pair types preserves equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Dᵉ : Bᵉ → UUᵉ l4ᵉ)
  where

  abstract
    is-equiv-map-Σᵉ :
      {fᵉ : Aᵉ → Bᵉ} {gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)} →
      is-equivᵉ fᵉ → is-fiberwise-equivᵉ gᵉ → is-equivᵉ (map-Σᵉ Dᵉ fᵉ gᵉ)
    is-equiv-map-Σᵉ {fᵉ} {gᵉ} is-equiv-fᵉ is-fiberwise-equiv-gᵉ =
      is-equiv-left-map-triangleᵉ
        ( map-Σᵉ Dᵉ fᵉ gᵉ)
        ( map-Σ-map-baseᵉ fᵉ Dᵉ)
        ( totᵉ gᵉ)
        ( triangle-map-Σᵉ Dᵉ fᵉ gᵉ)
        ( is-equiv-tot-is-fiberwise-equivᵉ is-fiberwise-equiv-gᵉ)
        ( is-equiv-map-Σ-map-baseᵉ fᵉ Dᵉ is-equiv-fᵉ)

  equiv-Σᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ ≃ᵉ Dᵉ (map-equivᵉ eᵉ xᵉ)) → Σᵉ Aᵉ Cᵉ ≃ᵉ Σᵉ Bᵉ Dᵉ
  pr1ᵉ (equiv-Σᵉ eᵉ gᵉ) = map-Σᵉ Dᵉ (map-equivᵉ eᵉ) (λ xᵉ → map-equivᵉ (gᵉ xᵉ))
  pr2ᵉ (equiv-Σᵉ eᵉ gᵉ) =
    is-equiv-map-Σᵉ
      ( is-equiv-map-equivᵉ eᵉ)
      ( λ xᵉ → is-equiv-map-equivᵉ (gᵉ xᵉ))

  abstract
    is-fiberwise-equiv-is-equiv-map-Σᵉ :
      (fᵉ : Aᵉ → Bᵉ) (gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)) →
      is-equivᵉ fᵉ → is-equivᵉ (map-Σᵉ Dᵉ fᵉ gᵉ) → is-fiberwise-equivᵉ gᵉ
    is-fiberwise-equiv-is-equiv-map-Σᵉ fᵉ gᵉ Hᵉ Kᵉ =
      is-fiberwise-equiv-is-equiv-totᵉ
        ( is-equiv-top-map-triangleᵉ
          ( map-Σᵉ Dᵉ fᵉ gᵉ)
          ( map-Σ-map-baseᵉ fᵉ Dᵉ)
          ( totᵉ gᵉ)
          ( triangle-map-Σᵉ Dᵉ fᵉ gᵉ)
          ( is-equiv-map-Σ-map-baseᵉ fᵉ Dᵉ Hᵉ)
          ( Kᵉ))

  map-equiv-Σᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ ≃ᵉ Dᵉ (map-equivᵉ eᵉ xᵉ)) → Σᵉ Aᵉ Cᵉ → Σᵉ Bᵉ Dᵉ
  map-equiv-Σᵉ eᵉ gᵉ = map-equivᵉ (equiv-Σᵉ eᵉ gᵉ)
```

### Any commuting triangle induces a map on fibers

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ))
  where

  fiber-triangleᵉ :
    (xᵉ : Xᵉ) → (fiberᵉ fᵉ xᵉ) → (fiberᵉ gᵉ xᵉ)
  pr1ᵉ (fiber-triangleᵉ .(fᵉ aᵉ) (pairᵉ aᵉ reflᵉ)) = hᵉ aᵉ
  pr2ᵉ (fiber-triangleᵉ .(fᵉ aᵉ) (pairᵉ aᵉ reflᵉ)) = invᵉ (Hᵉ aᵉ)

  square-tot-fiber-triangleᵉ :
    ( hᵉ ∘ᵉ (map-equiv-total-fiberᵉ fᵉ)) ~ᵉ
    ( map-equiv-total-fiberᵉ gᵉ ∘ᵉ totᵉ fiber-triangleᵉ)
  square-tot-fiber-triangleᵉ (pairᵉ .(fᵉ aᵉ) (pairᵉ aᵉ reflᵉ)) = reflᵉ
```

### In a commuting triangle, the top map is an equivalence if and only if it induces an equivalence on fibers

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ))
  where

  abstract
    is-fiberwise-equiv-is-equiv-triangleᵉ :
      (Eᵉ : is-equivᵉ hᵉ) → is-fiberwise-equivᵉ (fiber-triangleᵉ fᵉ gᵉ hᵉ Hᵉ)
    is-fiberwise-equiv-is-equiv-triangleᵉ Eᵉ =
      is-fiberwise-equiv-is-equiv-totᵉ
        ( is-equiv-top-is-equiv-bottom-squareᵉ
          ( map-equiv-total-fiberᵉ fᵉ)
          ( map-equiv-total-fiberᵉ gᵉ)
          ( totᵉ (fiber-triangleᵉ fᵉ gᵉ hᵉ Hᵉ))
          ( hᵉ)
          ( square-tot-fiber-triangleᵉ fᵉ gᵉ hᵉ Hᵉ)
          ( is-equiv-map-equiv-total-fiberᵉ fᵉ)
          ( is-equiv-map-equiv-total-fiberᵉ gᵉ)
          ( Eᵉ))

  abstract
    is-equiv-triangle-is-fiberwise-equivᵉ :
      is-fiberwise-equivᵉ (fiber-triangleᵉ fᵉ gᵉ hᵉ Hᵉ) → is-equivᵉ hᵉ
    is-equiv-triangle-is-fiberwise-equivᵉ Eᵉ =
      is-equiv-bottom-is-equiv-top-squareᵉ
        ( map-equiv-total-fiberᵉ fᵉ)
        ( map-equiv-total-fiberᵉ gᵉ)
        ( totᵉ (fiber-triangleᵉ fᵉ gᵉ hᵉ Hᵉ))
        ( hᵉ)
        ( square-tot-fiber-triangleᵉ fᵉ gᵉ hᵉ Hᵉ)
        ( is-equiv-map-equiv-total-fiberᵉ fᵉ)
        ( is-equiv-map-equiv-total-fiberᵉ gᵉ)
        ( is-equiv-tot-is-fiberwise-equivᵉ Eᵉ)
```

### `map-Σ` preserves identity maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  compute-map-Σ-idᵉ : map-Σᵉ Bᵉ idᵉ (λ xᵉ → idᵉ) ~ᵉ idᵉ
  compute-map-Σ-idᵉ = refl-htpyᵉ
```

## See also

-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ pairᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).ᵉ
-ᵉ Theᵉ universalᵉ propertyᵉ ofᵉ dependentᵉ pairᵉ typesᵉ isᵉ treatedᵉ in
  [`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ cartesianᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).ᵉ