# Lifts of maps

```agda
module orthogonal-factorization-systems.lifts-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.small-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
```

</details>

## Idea

Aᵉ **lift**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : Xᵉ → B`ᵉ alongᵉ aᵉ mapᵉ `iᵉ : Aᵉ → B`ᵉ isᵉ aᵉ mapᵉ `gᵉ : Xᵉ → A`ᵉ
suchᵉ thatᵉ theᵉ compositionᵉ `iᵉ ∘ᵉ g`ᵉ isᵉ `f`.ᵉ

```text
           Aᵉ
          ∧|ᵉ
        /ᵉ  iᵉ
      gᵉ    |
    /ᵉ      ∨ᵉ
  Xᵉ -ᵉ fᵉ ->ᵉ Bᵉ
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  where

  is-liftᵉ : {Xᵉ : UUᵉ l3ᵉ} → (Xᵉ → Bᵉ) → (Xᵉ → Aᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-liftᵉ fᵉ gᵉ = fᵉ ~ᵉ (iᵉ ∘ᵉ gᵉ)

  liftᵉ : {Xᵉ : UUᵉ l3ᵉ} → (Xᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  liftᵉ {Xᵉ} fᵉ = Σᵉ (Xᵉ → Aᵉ) (is-liftᵉ fᵉ)

  total-liftᵉ : (Xᵉ : UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  total-liftᵉ Xᵉ = Σᵉ (Xᵉ → Bᵉ) liftᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  {Xᵉ : UUᵉ l3ᵉ} {fᵉ : Xᵉ → Bᵉ}
  where

  map-liftᵉ : liftᵉ iᵉ fᵉ → Xᵉ → Aᵉ
  map-liftᵉ = pr1ᵉ

  is-lift-map-liftᵉ : (lᵉ : liftᵉ iᵉ fᵉ) → is-liftᵉ iᵉ fᵉ (map-liftᵉ lᵉ)
  is-lift-map-liftᵉ = pr2ᵉ
```

## Operations

### Vertical composition of lifts of maps

```text
           Aᵉ
          ∧|ᵉ
        /ᵉ  iᵉ
      gᵉ    |
    /ᵉ      ∨ᵉ
  Xᵉ -ᵉ fᵉ ->ᵉ Bᵉ
    \ᵉ      |
      hᵉ    jᵉ
       \ᵉ   |
         ∨ᵉ ∨ᵉ
           Cᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {iᵉ : Aᵉ → Bᵉ} {jᵉ : Bᵉ → Cᵉ} {fᵉ : Xᵉ → Bᵉ} {hᵉ : Xᵉ → Cᵉ} {gᵉ : Xᵉ → Aᵉ}
  where

  is-lift-comp-verticalᵉ : is-liftᵉ iᵉ fᵉ gᵉ → is-liftᵉ jᵉ hᵉ fᵉ → is-liftᵉ (jᵉ ∘ᵉ iᵉ) hᵉ gᵉ
  is-lift-comp-verticalᵉ Fᵉ Hᵉ xᵉ = Hᵉ xᵉ ∙ᵉ apᵉ jᵉ (Fᵉ xᵉ)
```

### Horizontal composition of lifts of maps

```text
  Aᵉ -ᵉ fᵉ ->ᵉ Bᵉ -ᵉ gᵉ ->ᵉ Cᵉ
    \ᵉ      |      /ᵉ
      hᵉ    iᵉ    jᵉ
        \ᵉ  |  /ᵉ
         ∨ᵉ ∨ᵉ ∨ᵉ
           Xᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Cᵉ} {hᵉ : Aᵉ → Xᵉ} {iᵉ : Bᵉ → Xᵉ} {jᵉ : Cᵉ → Xᵉ}
  where

  is-lift-comp-horizontalᵉ :
    is-liftᵉ jᵉ iᵉ gᵉ → is-liftᵉ iᵉ hᵉ fᵉ → is-liftᵉ jᵉ hᵉ (gᵉ ∘ᵉ fᵉ)
  is-lift-comp-horizontalᵉ Jᵉ Iᵉ xᵉ = Iᵉ xᵉ ∙ᵉ Jᵉ (fᵉ xᵉ)
```

## Left whiskering of lifts of maps

```text
           Aᵉ
          ∧|ᵉ
        /ᵉ  iᵉ
      gᵉ    |
    /ᵉ      ∨ᵉ
  Xᵉ -ᵉ fᵉ ->ᵉ Bᵉ -ᵉ hᵉ ->ᵉ Sᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Sᵉ : UUᵉ l4ᵉ}
  {iᵉ : Aᵉ → Bᵉ} {fᵉ : Xᵉ → Bᵉ} {gᵉ : Xᵉ → Aᵉ}
  where

  is-lift-left-whiskerᵉ : (hᵉ : Bᵉ → Sᵉ) → is-liftᵉ iᵉ fᵉ gᵉ → is-liftᵉ (hᵉ ∘ᵉ iᵉ) (hᵉ ∘ᵉ fᵉ) gᵉ
  is-lift-left-whiskerᵉ hᵉ Hᵉ xᵉ = apᵉ hᵉ (Hᵉ xᵉ)
```

## Right whiskering of lifts of maps

```text
                    Aᵉ
                   ∧|ᵉ
                 /ᵉ  iᵉ
               gᵉ    |
             /ᵉ      ∨ᵉ
  Sᵉ -ᵉ hᵉ ->ᵉ Xᵉ -ᵉ fᵉ ->ᵉ Bᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Sᵉ : UUᵉ l4ᵉ}
  {iᵉ : Aᵉ → Bᵉ} {fᵉ : Xᵉ → Bᵉ} {gᵉ : Xᵉ → Aᵉ}
  where

  is-lift-right-whiskerᵉ :
    is-liftᵉ iᵉ fᵉ gᵉ → (hᵉ : Sᵉ → Xᵉ) → is-liftᵉ iᵉ (fᵉ ∘ᵉ hᵉ) (gᵉ ∘ᵉ hᵉ)
  is-lift-right-whiskerᵉ Hᵉ hᵉ sᵉ = Hᵉ (hᵉ sᵉ)
```

## Properties

### Characterizing identifications of lifts of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Xᵉ → Bᵉ)
  where

  coherence-htpy-liftᵉ :
    (lᵉ l'ᵉ : liftᵉ iᵉ fᵉ) → map-liftᵉ iᵉ lᵉ ~ᵉ map-liftᵉ iᵉ l'ᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  coherence-htpy-liftᵉ lᵉ l'ᵉ Kᵉ =
    (is-lift-map-liftᵉ iᵉ lᵉ ∙hᵉ (iᵉ ·lᵉ Kᵉ)) ~ᵉ is-lift-map-liftᵉ iᵉ l'ᵉ

  htpy-liftᵉ : (lᵉ l'ᵉ : liftᵉ iᵉ fᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-liftᵉ lᵉ l'ᵉ =
    Σᵉ ( map-liftᵉ iᵉ lᵉ ~ᵉ map-liftᵉ iᵉ l'ᵉ)
      ( coherence-htpy-liftᵉ lᵉ l'ᵉ)

  refl-htpy-liftᵉ : (lᵉ : liftᵉ iᵉ fᵉ) → htpy-liftᵉ lᵉ lᵉ
  pr1ᵉ (refl-htpy-liftᵉ lᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-liftᵉ lᵉ) = right-unit-htpyᵉ

  htpy-eq-liftᵉ : (lᵉ l'ᵉ : liftᵉ iᵉ fᵉ) → lᵉ ＝ᵉ l'ᵉ → htpy-liftᵉ lᵉ l'ᵉ
  htpy-eq-liftᵉ lᵉ .lᵉ reflᵉ = refl-htpy-liftᵉ lᵉ

  is-torsorial-htpy-liftᵉ :
    (lᵉ : liftᵉ iᵉ fᵉ) → is-torsorialᵉ (htpy-liftᵉ lᵉ)
  is-torsorial-htpy-liftᵉ lᵉ =
    is-torsorial-Eq-structureᵉ
      (is-torsorial-htpyᵉ (map-liftᵉ iᵉ lᵉ))
      (map-liftᵉ iᵉ lᵉ ,ᵉ refl-htpyᵉ)
      (is-torsorial-htpyᵉ (is-lift-map-liftᵉ iᵉ lᵉ ∙hᵉ refl-htpyᵉ))

  is-equiv-htpy-eq-liftᵉ :
    (lᵉ l'ᵉ : liftᵉ iᵉ fᵉ) → is-equivᵉ (htpy-eq-liftᵉ lᵉ l'ᵉ)
  is-equiv-htpy-eq-liftᵉ lᵉ =
    fundamental-theorem-idᵉ (is-torsorial-htpy-liftᵉ lᵉ) (htpy-eq-liftᵉ lᵉ)

  extensionality-liftᵉ :
    (lᵉ l'ᵉ : liftᵉ iᵉ fᵉ) → (lᵉ ＝ᵉ l'ᵉ) ≃ᵉ (htpy-liftᵉ lᵉ l'ᵉ)
  pr1ᵉ (extensionality-liftᵉ lᵉ l'ᵉ) = htpy-eq-liftᵉ lᵉ l'ᵉ
  pr2ᵉ (extensionality-liftᵉ lᵉ l'ᵉ) = is-equiv-htpy-eq-liftᵉ lᵉ l'ᵉ

  eq-htpy-liftᵉ : (lᵉ l'ᵉ : liftᵉ iᵉ fᵉ) → htpy-liftᵉ lᵉ l'ᵉ → lᵉ ＝ᵉ l'ᵉ
  eq-htpy-liftᵉ lᵉ l'ᵉ = map-inv-equivᵉ (extensionality-liftᵉ lᵉ l'ᵉ)
```

### The total type of lifts of maps is equivalent to `X → A`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ) (Xᵉ : UUᵉ l3ᵉ)
  where

  inv-compute-total-liftᵉ : total-liftᵉ iᵉ Xᵉ ≃ᵉ (Xᵉ → Aᵉ)
  inv-compute-total-liftᵉ =
    ( right-unit-law-Σ-is-contrᵉ ( λ fᵉ → is-torsorial-htpy'ᵉ (iᵉ ∘ᵉ fᵉ))) ∘eᵉ
    ( equiv-left-swap-Σᵉ)

  compute-total-liftᵉ : (Xᵉ → Aᵉ) ≃ᵉ total-liftᵉ iᵉ Xᵉ
  compute-total-liftᵉ = inv-equivᵉ inv-compute-total-liftᵉ

  is-small-total-liftᵉ : is-smallᵉ (l1ᵉ ⊔ l3ᵉ) (total-liftᵉ iᵉ Xᵉ)
  pr1ᵉ (is-small-total-liftᵉ) = Xᵉ → Aᵉ
  pr2ᵉ (is-small-total-liftᵉ) = inv-compute-total-liftᵉ
```

### The truncation level of the type of lifts is bounded by the truncation level of the codomains

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  where

  is-trunc-is-liftᵉ :
    {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Xᵉ → Bᵉ) →
    is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ → (gᵉ : Xᵉ → Aᵉ) → is-truncᵉ kᵉ (is-liftᵉ iᵉ fᵉ gᵉ)
  is-trunc-is-liftᵉ fᵉ is-trunc-Bᵉ gᵉ =
    is-trunc-Πᵉ kᵉ (λ xᵉ → is-trunc-Bᵉ (fᵉ xᵉ) (iᵉ (gᵉ xᵉ)))

  is-trunc-liftᵉ :
    {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Xᵉ → Bᵉ) →
    is-truncᵉ kᵉ Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ → is-truncᵉ kᵉ (liftᵉ iᵉ fᵉ)
  is-trunc-liftᵉ fᵉ is-trunc-Aᵉ is-trunc-Bᵉ =
    is-trunc-Σᵉ
      ( is-trunc-function-typeᵉ kᵉ is-trunc-Aᵉ)
      ( is-trunc-is-liftᵉ fᵉ is-trunc-Bᵉ)

  is-trunc-total-liftᵉ :
    (Xᵉ : UUᵉ l3ᵉ) → is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ (total-liftᵉ iᵉ Xᵉ)
  is-trunc-total-liftᵉ Xᵉ is-trunc-Aᵉ =
    is-trunc-equiv'ᵉ kᵉ
      ( Xᵉ → Aᵉ)
      ( compute-total-liftᵉ iᵉ Xᵉ)
      ( is-trunc-function-typeᵉ kᵉ is-trunc-Aᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  where

  is-contr-is-liftᵉ :
    {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Xᵉ → Bᵉ) →
    is-propᵉ Bᵉ → (gᵉ : Xᵉ → Aᵉ) → is-contrᵉ (is-liftᵉ iᵉ fᵉ gᵉ)
  is-contr-is-liftᵉ fᵉ is-prop-Bᵉ gᵉ = is-contr-Πᵉ λ xᵉ → is-prop-Bᵉ (fᵉ xᵉ) (iᵉ (gᵉ xᵉ))

  is-prop-is-liftᵉ :
    {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Xᵉ → Bᵉ) →
    is-setᵉ Bᵉ → (gᵉ : Xᵉ → Aᵉ) → is-propᵉ (is-liftᵉ iᵉ fᵉ gᵉ)
  is-prop-is-liftᵉ fᵉ is-set-Bᵉ gᵉ = is-prop-Πᵉ λ xᵉ → is-set-Bᵉ (fᵉ xᵉ) (iᵉ (gᵉ xᵉ))
```

## See also

-ᵉ [`orthogonal-factorization-systems.extensions-of-maps`](orthogonal-factorization-systems.extensions-of-maps.mdᵉ)
  forᵉ theᵉ dualᵉ notion.ᵉ