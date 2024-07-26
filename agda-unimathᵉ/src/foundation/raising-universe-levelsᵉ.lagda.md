# Raising universe levels

```agda
module foundation.raising-universe-levelsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
```

</details>

## Idea

Inᵉ Agda,ᵉ typesᵉ haveᵉ aᵉ designatedᵉ universeᵉ levels,ᵉ andᵉ universesᵉ in Agdaᵉ don'tᵉ
overlap.ᵉ Usingᵉ `data`ᵉ typesᵉ weᵉ canᵉ constructᵉ forᵉ anyᵉ typeᵉ `A`ᵉ ofᵉ universeᵉ levelᵉ
`l`ᵉ anᵉ equivalentᵉ typeᵉ in anyᵉ higherᵉ universe.ᵉ

## Definition

```agda
data raiseᵉ (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) : UUᵉ (l1ᵉ ⊔ lᵉ) where
  map-raiseᵉ : Aᵉ → raiseᵉ lᵉ Aᵉ

data raiseωᵉ {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) : UUωᵉ where
  map-raiseωᵉ : Aᵉ → raiseωᵉ Aᵉ
```

## Properties

### Types are equivalent to their raised equivalents

```agda
module _
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  map-inv-raiseᵉ : raiseᵉ lᵉ Aᵉ → Aᵉ
  map-inv-raiseᵉ (map-raiseᵉ xᵉ) = xᵉ

  is-section-map-inv-raiseᵉ : (map-raiseᵉ ∘ᵉ map-inv-raiseᵉ) ~ᵉ idᵉ
  is-section-map-inv-raiseᵉ (map-raiseᵉ xᵉ) = reflᵉ

  is-retraction-map-inv-raiseᵉ : (map-inv-raiseᵉ ∘ᵉ map-raiseᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-raiseᵉ xᵉ = reflᵉ

  is-equiv-map-raiseᵉ : is-equivᵉ (map-raiseᵉ {lᵉ} {l1ᵉ} {Aᵉ})
  is-equiv-map-raiseᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-raiseᵉ
      is-section-map-inv-raiseᵉ
      is-retraction-map-inv-raiseᵉ

compute-raiseᵉ : (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → Aᵉ ≃ᵉ raiseᵉ lᵉ Aᵉ
pr1ᵉ (compute-raiseᵉ lᵉ Aᵉ) = map-raiseᵉ
pr2ᵉ (compute-raiseᵉ lᵉ Aᵉ) = is-equiv-map-raiseᵉ

Raiseᵉ : (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → Σᵉ (UUᵉ (l1ᵉ ⊔ lᵉ)) (λ Xᵉ → Aᵉ ≃ᵉ Xᵉ)
pr1ᵉ (Raiseᵉ lᵉ Aᵉ) = raiseᵉ lᵉ Aᵉ
pr2ᵉ (Raiseᵉ lᵉ Aᵉ) = compute-raiseᵉ lᵉ Aᵉ
```

### Raising universe levels of propositions

```agda
raise-Propᵉ : (lᵉ : Level) {l1ᵉ : Level} → Propᵉ l1ᵉ → Propᵉ (lᵉ ⊔ l1ᵉ)
pr1ᵉ (raise-Propᵉ lᵉ Pᵉ) = raiseᵉ lᵉ (type-Propᵉ Pᵉ)
pr2ᵉ (raise-Propᵉ lᵉ Pᵉ) =
  is-prop-equiv'ᵉ (compute-raiseᵉ lᵉ (type-Propᵉ Pᵉ)) (is-prop-type-Propᵉ Pᵉ)
```

### Raising universe levels of sets

```agda
raise-Setᵉ : (lᵉ : Level) {l1ᵉ : Level} → Setᵉ l1ᵉ → Setᵉ (lᵉ ⊔ l1ᵉ)
pr1ᵉ (raise-Setᵉ lᵉ Aᵉ) = raiseᵉ lᵉ (type-Setᵉ Aᵉ)
pr2ᵉ (raise-Setᵉ lᵉ Aᵉ) =
  is-set-equiv'ᵉ (type-Setᵉ Aᵉ) (compute-raiseᵉ lᵉ (type-Setᵉ Aᵉ)) (is-set-type-Setᵉ Aᵉ)
```

### Raising equivalent types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  map-equiv-raiseᵉ : raiseᵉ l3ᵉ Aᵉ → raiseᵉ l4ᵉ Bᵉ
  map-equiv-raiseᵉ (map-raiseᵉ xᵉ) = map-raiseᵉ (map-equivᵉ eᵉ xᵉ)

  map-inv-equiv-raiseᵉ : raiseᵉ l4ᵉ Bᵉ → raiseᵉ l3ᵉ Aᵉ
  map-inv-equiv-raiseᵉ (map-raiseᵉ yᵉ) = map-raiseᵉ (map-inv-equivᵉ eᵉ yᵉ)

  is-section-map-inv-equiv-raiseᵉ :
    ( map-equiv-raiseᵉ ∘ᵉ map-inv-equiv-raiseᵉ) ~ᵉ idᵉ
  is-section-map-inv-equiv-raiseᵉ (map-raiseᵉ yᵉ) =
    apᵉ map-raiseᵉ (is-section-map-inv-equivᵉ eᵉ yᵉ)

  is-retraction-map-inv-equiv-raiseᵉ :
    ( map-inv-equiv-raiseᵉ ∘ᵉ map-equiv-raiseᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-equiv-raiseᵉ (map-raiseᵉ xᵉ) =
    apᵉ map-raiseᵉ (is-retraction-map-inv-equivᵉ eᵉ xᵉ)

  is-equiv-map-equiv-raiseᵉ : is-equivᵉ map-equiv-raiseᵉ
  is-equiv-map-equiv-raiseᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-raiseᵉ
      is-section-map-inv-equiv-raiseᵉ
      is-retraction-map-inv-equiv-raiseᵉ

  equiv-raiseᵉ : raiseᵉ l3ᵉ Aᵉ ≃ᵉ raiseᵉ l4ᵉ Bᵉ
  pr1ᵉ equiv-raiseᵉ = map-equiv-raiseᵉ
  pr2ᵉ equiv-raiseᵉ = is-equiv-map-equiv-raiseᵉ
```

### Raising universe levels from `l1` to `l ⊔ l1` is an embedding from `UU l1` to `UU (l ⊔ l1)`

```agda
abstract
  is-emb-raiseᵉ : (lᵉ : Level) {l1ᵉ : Level} → is-embᵉ (raiseᵉ lᵉ {l1ᵉ})
  is-emb-raiseᵉ lᵉ {l1ᵉ} =
    is-emb-is-prop-mapᵉ
      ( λ Xᵉ →
        is-prop-is-proof-irrelevantᵉ
          ( λ (Aᵉ ,ᵉ pᵉ) →
            is-contr-equivᵉ
              ( Σᵉ (UUᵉ l1ᵉ) (λ A'ᵉ → A'ᵉ ≃ᵉ Aᵉ))
              ( equiv-totᵉ
                ( λ A'ᵉ →
                  ( equiv-postcomp-equivᵉ (inv-equivᵉ (compute-raiseᵉ lᵉ Aᵉ)) A'ᵉ) ∘eᵉ
                  ( equiv-precomp-equivᵉ (compute-raiseᵉ lᵉ A'ᵉ) (raiseᵉ lᵉ Aᵉ)) ∘eᵉ
                  ( equiv-univalenceᵉ) ∘eᵉ
                  ( equiv-concat'ᵉ (raiseᵉ lᵉ A'ᵉ) (invᵉ pᵉ))))
              ( is-torsorial-equiv'ᵉ Aᵉ)))

emb-raiseᵉ : (lᵉ : Level) {l1ᵉ : Level} → UUᵉ l1ᵉ ↪ᵉ UUᵉ (l1ᵉ ⊔ lᵉ)
pr1ᵉ (emb-raiseᵉ lᵉ) = raiseᵉ lᵉ
pr2ᵉ (emb-raiseᵉ lᵉ) = is-emb-raiseᵉ lᵉ
```