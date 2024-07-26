# Repetitions of values of maps

```agda
module foundation.repetitions-of-valuesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.pairs-of-distinct-elementsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.injective-mapsᵉ
```

</details>

## Idea

Aᵉ repetitionᵉ ofᵉ valuesᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ consistsᵉ ofᵉ aᵉ pairᵉ ofᵉ distinctᵉ
pointsᵉ in `A`ᵉ thatᵉ getᵉ mappedᵉ to theᵉ sameᵉ pointᵉ in `B`.ᵉ

## Definitions

### The predicate that a pair of distinct elements is a repetition of values

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-repetition-of-valuesᵉ :
    (fᵉ : Aᵉ → Bᵉ) (pᵉ : pair-of-distinct-elementsᵉ Aᵉ) → UUᵉ l2ᵉ
  is-repetition-of-valuesᵉ fᵉ pᵉ =
    fᵉ (first-pair-of-distinct-elementsᵉ pᵉ) ＝ᵉ
    fᵉ (second-pair-of-distinct-elementsᵉ pᵉ)

  repetition-of-valuesᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  repetition-of-valuesᵉ fᵉ =
    Σᵉ ( pair-of-distinct-elementsᵉ Aᵉ)
      ( is-repetition-of-valuesᵉ fᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (rᵉ : repetition-of-valuesᵉ fᵉ)
  where

  pair-of-distinct-elements-repetition-of-valuesᵉ : pair-of-distinct-elementsᵉ Aᵉ
  pair-of-distinct-elements-repetition-of-valuesᵉ = pr1ᵉ rᵉ

  first-repetition-of-valuesᵉ : Aᵉ
  first-repetition-of-valuesᵉ =
    first-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-valuesᵉ

  second-repetition-of-valuesᵉ : Aᵉ
  second-repetition-of-valuesᵉ =
    second-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-valuesᵉ

  distinction-repetition-of-valuesᵉ :
    first-repetition-of-valuesᵉ ≠ᵉ second-repetition-of-valuesᵉ
  distinction-repetition-of-valuesᵉ =
    distinction-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-valuesᵉ

  is-repetition-of-values-repetition-of-valuesᵉ :
    is-repetition-of-valuesᵉ fᵉ
      pair-of-distinct-elements-repetition-of-valuesᵉ
  is-repetition-of-values-repetition-of-valuesᵉ = pr2ᵉ rᵉ
```

### The predicate that an element is repeated

```agda
is-repeated-valueᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (aᵉ : Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-repeated-valueᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} fᵉ aᵉ =
  Σᵉ (Σᵉ Aᵉ (λ xᵉ → aᵉ ≠ᵉ xᵉ)) (λ xᵉ → fᵉ aᵉ ＝ᵉ fᵉ (pr1ᵉ xᵉ))
```

## Properties

### Repetitions of values of composite maps

```agda
repetition-of-values-compᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (gᵉ : Bᵉ → Cᵉ)
  {fᵉ : Aᵉ → Bᵉ} → repetition-of-valuesᵉ fᵉ → repetition-of-valuesᵉ (gᵉ ∘ᵉ fᵉ)
repetition-of-values-compᵉ gᵉ ((xᵉ ,ᵉ yᵉ ,ᵉ sᵉ) ,ᵉ tᵉ) =
  ((xᵉ ,ᵉ yᵉ ,ᵉ sᵉ) ,ᵉ apᵉ gᵉ tᵉ)

repetition-of-values-left-factorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {gᵉ : Bᵉ → Cᵉ}
  {fᵉ : Aᵉ → Bᵉ} → is-embᵉ fᵉ → repetition-of-valuesᵉ (gᵉ ∘ᵉ fᵉ) → repetition-of-valuesᵉ gᵉ
repetition-of-values-left-factorᵉ {gᵉ = gᵉ} {fᵉ} Hᵉ ((aᵉ ,ᵉ bᵉ ,ᵉ Kᵉ) ,ᵉ pᵉ) =
  ((fᵉ aᵉ ,ᵉ fᵉ bᵉ ,ᵉ λ qᵉ → Kᵉ (is-injective-is-embᵉ Hᵉ qᵉ)) ,ᵉ pᵉ)

repetition-of-values-right-factorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {gᵉ : Bᵉ → Cᵉ}
  {fᵉ : Aᵉ → Bᵉ} → is-embᵉ gᵉ → repetition-of-valuesᵉ (gᵉ ∘ᵉ fᵉ) → repetition-of-valuesᵉ fᵉ
repetition-of-values-right-factorᵉ {gᵉ = gᵉ} {fᵉ} Hᵉ ((aᵉ ,ᵉ bᵉ ,ᵉ Kᵉ) ,ᵉ pᵉ) =
  ((aᵉ ,ᵉ bᵉ ,ᵉ Kᵉ) ,ᵉ is-injective-is-embᵉ Hᵉ pᵉ)
```

### The type of repetitions of values is invariant under equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Cᵉ → Dᵉ) (eᵉ : Aᵉ ≃ᵉ Cᵉ) (dᵉ : Bᵉ ≃ᵉ Dᵉ)
  (Hᵉ : coherence-square-mapsᵉ (map-equivᵉ eᵉ) fᵉ gᵉ (map-equivᵉ dᵉ))
  where

  equiv-repetition-of-valuesᵉ : repetition-of-valuesᵉ fᵉ ≃ᵉ repetition-of-valuesᵉ gᵉ
  equiv-repetition-of-valuesᵉ =
    equiv-Σᵉ
      ( λ pᵉ →
        ( gᵉ (first-pair-of-distinct-elementsᵉ pᵉ)) ＝ᵉ
        ( gᵉ (second-pair-of-distinct-elementsᵉ pᵉ)))
      ( equiv-pair-of-distinct-elementsᵉ eᵉ)
      ( λ pᵉ →
        ( ( equiv-concat'ᵉ
            ( gᵉ (map-equivᵉ eᵉ (first-pair-of-distinct-elementsᵉ pᵉ)))
            ( Hᵉ (second-pair-of-distinct-elementsᵉ pᵉ))) ∘eᵉ
          ( equiv-concatᵉ
            ( invᵉ (Hᵉ (first-pair-of-distinct-elementsᵉ pᵉ)))
            ( map-equivᵉ dᵉ (fᵉ (second-pair-of-distinct-elementsᵉ pᵉ))))) ∘eᵉ
        ( equiv-apᵉ dᵉ
          ( fᵉ (first-pair-of-distinct-elementsᵉ pᵉ))
          ( fᵉ (second-pair-of-distinct-elementsᵉ pᵉ))))

  map-equiv-repetition-of-valuesᵉ :
    repetition-of-valuesᵉ fᵉ → repetition-of-valuesᵉ gᵉ
  map-equiv-repetition-of-valuesᵉ =
    map-equivᵉ equiv-repetition-of-valuesᵉ

  map-inv-equiv-repetition-of-valuesᵉ :
    repetition-of-valuesᵉ gᵉ → repetition-of-valuesᵉ fᵉ
  map-inv-equiv-repetition-of-valuesᵉ = map-inv-equivᵉ equiv-repetition-of-valuesᵉ

  is-section-map-inv-equiv-repetition-of-valuesᵉ :
    ( map-equiv-repetition-of-valuesᵉ ∘ᵉ map-inv-equiv-repetition-of-valuesᵉ) ~ᵉ idᵉ
  is-section-map-inv-equiv-repetition-of-valuesᵉ =
    is-section-map-inv-equivᵉ equiv-repetition-of-valuesᵉ

  is-retraction-map-inv-equiv-repetition-of-valuesᵉ :
    ( map-inv-equiv-repetition-of-valuesᵉ ∘ᵉ map-equiv-repetition-of-valuesᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-equiv-repetition-of-valuesᵉ =
    is-retraction-map-inv-equivᵉ equiv-repetition-of-valuesᵉ
```

### Embeddings of repetitions values

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Cᵉ → Dᵉ) (eᵉ : Aᵉ ↪ᵉ Cᵉ) (dᵉ : Bᵉ ↪ᵉ Dᵉ)
  (Hᵉ : coherence-square-mapsᵉ (map-embᵉ eᵉ) fᵉ gᵉ (map-embᵉ dᵉ))
  where

  emb-repetition-of-valuesᵉ : repetition-of-valuesᵉ fᵉ ↪ᵉ repetition-of-valuesᵉ gᵉ
  emb-repetition-of-valuesᵉ =
    emb-Σᵉ
      ( λ pᵉ →
        ( gᵉ (first-pair-of-distinct-elementsᵉ pᵉ)) ＝ᵉ
        ( gᵉ (second-pair-of-distinct-elementsᵉ pᵉ)))
      ( emb-pair-of-distinct-elementsᵉ eᵉ)
      ( λ pᵉ →
        emb-equivᵉ
          ( ( ( equiv-concat'ᵉ
                ( gᵉ (map-embᵉ eᵉ (first-pair-of-distinct-elementsᵉ pᵉ)))
                ( Hᵉ (second-pair-of-distinct-elementsᵉ pᵉ))) ∘eᵉ
              ( equiv-concatᵉ
                ( invᵉ (Hᵉ (first-pair-of-distinct-elementsᵉ pᵉ)))
                ( map-embᵉ dᵉ (fᵉ (second-pair-of-distinct-elementsᵉ pᵉ))))) ∘eᵉ
            ( equiv-ap-embᵉ dᵉ)))

  map-emb-repetition-of-valuesᵉ : repetition-of-valuesᵉ fᵉ → repetition-of-valuesᵉ gᵉ
  map-emb-repetition-of-valuesᵉ = map-embᵉ emb-repetition-of-valuesᵉ

  is-emb-map-emb-repetition-of-valuesᵉ : is-embᵉ map-emb-repetition-of-valuesᵉ
  is-emb-map-emb-repetition-of-valuesᵉ = is-emb-map-embᵉ emb-repetition-of-valuesᵉ
```