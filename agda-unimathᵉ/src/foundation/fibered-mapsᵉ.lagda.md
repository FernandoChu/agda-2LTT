# Maps fibered over a map

```agda
module foundation.fibered-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.sliceᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.small-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
    Aᵉ         Bᵉ
    |         |
  fᵉ |         | gᵉ
    ∨ᵉ         ∨ᵉ
    Xᵉ ------>ᵉ Yᵉ
         iᵉ
```

Aᵉ **fiberedᵉ map**ᵉ fromᵉ `f`ᵉ to `g`ᵉ overᵉ `i`ᵉ isᵉ aᵉ mapᵉ `hᵉ : Aᵉ → B`ᵉ suchᵉ thatᵉ theᵉ
squareᵉ `iᵉ ∘ᵉ fᵉ ~ᵉ gᵉ ∘ᵉ h`ᵉ [commutes](foundation-core.commuting-squares-of-maps.md).ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  is-map-overᵉ : (Xᵉ → Yᵉ) → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  is-map-overᵉ iᵉ hᵉ = coherence-square-mapsᵉ hᵉ fᵉ gᵉ iᵉ

  map-overᵉ : (Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  map-overᵉ iᵉ = Σᵉ (Aᵉ → Bᵉ) (is-map-overᵉ iᵉ)

  fibered-mapᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  fibered-mapᵉ = Σᵉ (Xᵉ → Yᵉ) (map-overᵉ)

  fiberwise-map-overᵉ : (Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  fiberwise-map-overᵉ iᵉ = (xᵉ : Xᵉ) → fiberᵉ fᵉ xᵉ → fiberᵉ gᵉ (iᵉ xᵉ)

  cone-fibered-mapᵉ : (ihHᵉ : fibered-mapᵉ) → coneᵉ (pr1ᵉ ihHᵉ) gᵉ Aᵉ
  pr1ᵉ (cone-fibered-mapᵉ ihHᵉ) = fᵉ
  pr1ᵉ (pr2ᵉ (cone-fibered-mapᵉ (iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ))) = hᵉ
  pr2ᵉ (pr2ᵉ (cone-fibered-mapᵉ (iᵉ ,ᵉ hᵉ ,ᵉ Hᵉ))) = Hᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  map-total-map-overᵉ : (iᵉ : Xᵉ → Yᵉ) → map-overᵉ fᵉ gᵉ iᵉ → Aᵉ → Bᵉ
  map-total-map-overᵉ iᵉ = pr1ᵉ

  is-map-over-map-total-map-overᵉ :
    (iᵉ : Xᵉ → Yᵉ) (mᵉ : map-overᵉ fᵉ gᵉ iᵉ) →
    is-map-overᵉ fᵉ gᵉ iᵉ (map-total-map-overᵉ iᵉ mᵉ)
  is-map-over-map-total-map-overᵉ iᵉ = pr2ᵉ

  map-over-fibered-mapᵉ : (mᵉ : fibered-mapᵉ fᵉ gᵉ) → map-overᵉ fᵉ gᵉ (pr1ᵉ mᵉ)
  map-over-fibered-mapᵉ = pr2ᵉ

  map-base-fibered-mapᵉ : (mᵉ : fibered-mapᵉ fᵉ gᵉ) → Xᵉ → Yᵉ
  map-base-fibered-mapᵉ = pr1ᵉ

  map-total-fibered-mapᵉ : (mᵉ : fibered-mapᵉ fᵉ gᵉ) → Aᵉ → Bᵉ
  map-total-fibered-mapᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  is-map-over-map-total-fibered-mapᵉ :
    (mᵉ : fibered-mapᵉ fᵉ gᵉ) →
    is-map-overᵉ fᵉ gᵉ (map-base-fibered-mapᵉ mᵉ) (map-total-fibered-mapᵉ mᵉ)
  is-map-over-map-total-fibered-mapᵉ = pr2ᵉ ∘ᵉ pr2ᵉ
```

## Properties

### Identifications of maps over

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ)
  where

  coherence-htpy-map-overᵉ :
    (mᵉ m'ᵉ : map-overᵉ fᵉ gᵉ iᵉ) →
    map-total-map-overᵉ fᵉ gᵉ iᵉ mᵉ ~ᵉ map-total-map-overᵉ fᵉ gᵉ iᵉ m'ᵉ → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-htpy-map-overᵉ mᵉ m'ᵉ Kᵉ =
    ( is-map-over-map-total-map-overᵉ fᵉ gᵉ iᵉ mᵉ ∙hᵉ (gᵉ ·lᵉ Kᵉ)) ~ᵉ
    ( is-map-over-map-total-map-overᵉ fᵉ gᵉ iᵉ m'ᵉ)

  htpy-map-overᵉ : (mᵉ m'ᵉ : map-overᵉ fᵉ gᵉ iᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  htpy-map-overᵉ mᵉ m'ᵉ =
    Σᵉ ( map-total-map-overᵉ fᵉ gᵉ iᵉ mᵉ ~ᵉ map-total-map-overᵉ fᵉ gᵉ iᵉ m'ᵉ)
      ( coherence-htpy-map-overᵉ mᵉ m'ᵉ)

  refl-htpy-map-overᵉ : (mᵉ : map-overᵉ fᵉ gᵉ iᵉ) → htpy-map-overᵉ mᵉ mᵉ
  pr1ᵉ (refl-htpy-map-overᵉ mᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-map-overᵉ mᵉ) = right-unit-htpyᵉ

  htpy-eq-map-overᵉ : (mᵉ m'ᵉ : map-overᵉ fᵉ gᵉ iᵉ) → mᵉ ＝ᵉ m'ᵉ → htpy-map-overᵉ mᵉ m'ᵉ
  htpy-eq-map-overᵉ mᵉ .mᵉ reflᵉ = refl-htpy-map-overᵉ mᵉ

  is-torsorial-htpy-map-overᵉ :
    (mᵉ : map-overᵉ fᵉ gᵉ iᵉ) → is-torsorialᵉ (htpy-map-overᵉ mᵉ)
  is-torsorial-htpy-map-overᵉ mᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-total-map-overᵉ fᵉ gᵉ iᵉ mᵉ))
      ( map-total-map-overᵉ fᵉ gᵉ iᵉ mᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-htpyᵉ (is-map-over-map-total-map-overᵉ fᵉ gᵉ iᵉ mᵉ ∙hᵉ refl-htpyᵉ))

  is-equiv-htpy-eq-map-overᵉ :
    (mᵉ m'ᵉ : map-overᵉ fᵉ gᵉ iᵉ) → is-equivᵉ (htpy-eq-map-overᵉ mᵉ m'ᵉ)
  is-equiv-htpy-eq-map-overᵉ mᵉ =
    fundamental-theorem-idᵉ (is-torsorial-htpy-map-overᵉ mᵉ) (htpy-eq-map-overᵉ mᵉ)

  extensionality-map-overᵉ :
    (mᵉ m'ᵉ : map-overᵉ fᵉ gᵉ iᵉ) → (mᵉ ＝ᵉ m'ᵉ) ≃ᵉ (htpy-map-overᵉ mᵉ m'ᵉ)
  pr1ᵉ (extensionality-map-overᵉ mᵉ m'ᵉ) = htpy-eq-map-overᵉ mᵉ m'ᵉ
  pr2ᵉ (extensionality-map-overᵉ mᵉ m'ᵉ) = is-equiv-htpy-eq-map-overᵉ mᵉ m'ᵉ

  eq-htpy-map-overᵉ : (mᵉ m'ᵉ : map-overᵉ fᵉ gᵉ iᵉ) → htpy-map-overᵉ mᵉ m'ᵉ → mᵉ ＝ᵉ m'ᵉ
  eq-htpy-map-overᵉ mᵉ m'ᵉ = map-inv-equivᵉ (extensionality-map-overᵉ mᵉ m'ᵉ)
```

### Identifications of fibered maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  coherence-htpy-fibered-mapᵉ :
    (mᵉ m'ᵉ : fibered-mapᵉ fᵉ gᵉ) →
    map-base-fibered-mapᵉ fᵉ gᵉ mᵉ ~ᵉ map-base-fibered-mapᵉ fᵉ gᵉ m'ᵉ →
    map-total-fibered-mapᵉ fᵉ gᵉ mᵉ ~ᵉ map-total-fibered-mapᵉ fᵉ gᵉ m'ᵉ → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-htpy-fibered-mapᵉ mᵉ m'ᵉ Iᵉ Hᵉ =
    ( is-map-over-map-total-fibered-mapᵉ fᵉ gᵉ mᵉ ∙hᵉ (gᵉ ·lᵉ Hᵉ)) ~ᵉ
    ( (Iᵉ ·rᵉ fᵉ) ∙hᵉ is-map-over-map-total-fibered-mapᵉ fᵉ gᵉ m'ᵉ)

  htpy-fibered-mapᵉ : (mᵉ m'ᵉ : fibered-mapᵉ fᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-fibered-mapᵉ mᵉ m'ᵉ =
    Σᵉ ( map-base-fibered-mapᵉ fᵉ gᵉ mᵉ ~ᵉ map-base-fibered-mapᵉ fᵉ gᵉ m'ᵉ)
      ( λ Iᵉ →
      Σᵉ ( map-total-fibered-mapᵉ fᵉ gᵉ mᵉ ~ᵉ map-total-fibered-mapᵉ fᵉ gᵉ m'ᵉ)
        ( coherence-htpy-fibered-mapᵉ mᵉ m'ᵉ Iᵉ))

  refl-htpy-fibered-mapᵉ : (mᵉ : fibered-mapᵉ fᵉ gᵉ) → htpy-fibered-mapᵉ mᵉ mᵉ
  pr1ᵉ (refl-htpy-fibered-mapᵉ mᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (refl-htpy-fibered-mapᵉ mᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (refl-htpy-fibered-mapᵉ mᵉ)) =
    inv-htpy-left-unit-htpyᵉ ∙hᵉ right-unit-htpyᵉ

  htpy-eq-fibered-mapᵉ :
    (mᵉ m'ᵉ : fibered-mapᵉ fᵉ gᵉ) → mᵉ ＝ᵉ m'ᵉ → htpy-fibered-mapᵉ mᵉ m'ᵉ
  htpy-eq-fibered-mapᵉ mᵉ .mᵉ reflᵉ = refl-htpy-fibered-mapᵉ mᵉ

  is-torsorial-htpy-fibered-mapᵉ :
    (mᵉ : fibered-mapᵉ fᵉ gᵉ) → is-torsorialᵉ (htpy-fibered-mapᵉ mᵉ)
  is-torsorial-htpy-fibered-mapᵉ mᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-base-fibered-mapᵉ fᵉ gᵉ mᵉ))
      ( map-base-fibered-mapᵉ fᵉ gᵉ mᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (map-total-fibered-mapᵉ fᵉ gᵉ mᵉ))
        ( map-total-fibered-mapᵉ fᵉ gᵉ mᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-htpyᵉ
          ( is-map-over-map-total-fibered-mapᵉ fᵉ gᵉ mᵉ ∙hᵉ refl-htpyᵉ)))

  is-equiv-htpy-eq-fibered-mapᵉ :
    (mᵉ m'ᵉ : fibered-mapᵉ fᵉ gᵉ) → is-equivᵉ (htpy-eq-fibered-mapᵉ mᵉ m'ᵉ)
  is-equiv-htpy-eq-fibered-mapᵉ mᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-fibered-mapᵉ mᵉ)
      ( htpy-eq-fibered-mapᵉ mᵉ)

  extensionality-fibered-mapᵉ :
    (mᵉ m'ᵉ : fibered-mapᵉ fᵉ gᵉ) → (mᵉ ＝ᵉ m'ᵉ) ≃ᵉ (htpy-fibered-mapᵉ mᵉ m'ᵉ)
  pr1ᵉ (extensionality-fibered-mapᵉ mᵉ m'ᵉ) = htpy-eq-fibered-mapᵉ mᵉ m'ᵉ
  pr2ᵉ (extensionality-fibered-mapᵉ mᵉ m'ᵉ) = is-equiv-htpy-eq-fibered-mapᵉ mᵉ m'ᵉ

  eq-htpy-fibered-mapᵉ :
    (mᵉ m'ᵉ : fibered-mapᵉ fᵉ gᵉ) → htpy-fibered-mapᵉ mᵉ m'ᵉ → mᵉ ＝ᵉ m'ᵉ
  eq-htpy-fibered-mapᵉ mᵉ m'ᵉ = map-inv-equivᵉ (extensionality-fibered-mapᵉ mᵉ m'ᵉ)
```

### Fibered maps and fiberwise maps over are equivalent notions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ)
  where

  fiberwise-map-over-map-overᵉ :
    map-overᵉ fᵉ gᵉ iᵉ → fiberwise-map-overᵉ fᵉ gᵉ iᵉ
  pr1ᵉ (fiberwise-map-over-map-overᵉ (hᵉ ,ᵉ Hᵉ) .(fᵉ aᵉ) (aᵉ ,ᵉ reflᵉ)) = hᵉ aᵉ
  pr2ᵉ (fiberwise-map-over-map-overᵉ (hᵉ ,ᵉ Hᵉ) .(fᵉ aᵉ) (aᵉ ,ᵉ reflᵉ)) = invᵉ (Hᵉ aᵉ)

  map-over-fiberwise-map-overᵉ :
    fiberwise-map-overᵉ fᵉ gᵉ iᵉ → map-overᵉ fᵉ gᵉ iᵉ
  pr1ᵉ (map-over-fiberwise-map-overᵉ αᵉ) aᵉ = pr1ᵉ (αᵉ (fᵉ aᵉ) (pairᵉ aᵉ reflᵉ))
  pr2ᵉ (map-over-fiberwise-map-overᵉ αᵉ) aᵉ = invᵉ (pr2ᵉ (αᵉ (fᵉ aᵉ) (pairᵉ aᵉ reflᵉ)))

  is-section-map-over-fiberwise-map-over-eq-htpyᵉ :
    (αᵉ : fiberwise-map-overᵉ fᵉ gᵉ iᵉ) (xᵉ : Xᵉ) →
    fiberwise-map-over-map-overᵉ (map-over-fiberwise-map-overᵉ αᵉ) xᵉ ~ᵉ αᵉ xᵉ
  is-section-map-over-fiberwise-map-over-eq-htpyᵉ αᵉ .(fᵉ aᵉ) (pairᵉ aᵉ reflᵉ) =
    eq-pair-eq-fiberᵉ (inv-invᵉ (pr2ᵉ (αᵉ (fᵉ aᵉ) (pairᵉ aᵉ reflᵉ))))

  is-section-map-over-fiberwise-map-overᵉ :
    fiberwise-map-over-map-overᵉ ∘ᵉ map-over-fiberwise-map-overᵉ ~ᵉ idᵉ
  is-section-map-over-fiberwise-map-overᵉ αᵉ =
    eq-htpyᵉ (eq-htpyᵉ ∘ᵉ is-section-map-over-fiberwise-map-over-eq-htpyᵉ αᵉ)

  is-retraction-map-over-fiberwise-map-overᵉ :
    map-over-fiberwise-map-overᵉ ∘ᵉ fiberwise-map-over-map-overᵉ ~ᵉ idᵉ
  is-retraction-map-over-fiberwise-map-overᵉ (pairᵉ hᵉ Hᵉ) =
    eq-pair-eq-fiberᵉ (eq-htpyᵉ (inv-invᵉ ∘ᵉ Hᵉ))

  abstract
    is-equiv-fiberwise-map-over-map-overᵉ :
      is-equivᵉ (fiberwise-map-over-map-overᵉ)
    is-equiv-fiberwise-map-over-map-overᵉ =
      is-equiv-is-invertibleᵉ
        ( map-over-fiberwise-map-overᵉ)
        ( is-section-map-over-fiberwise-map-overᵉ)
        ( is-retraction-map-over-fiberwise-map-overᵉ)

  abstract
    is-equiv-map-over-fiberwise-map-overᵉ :
      is-equivᵉ (map-over-fiberwise-map-overᵉ)
    is-equiv-map-over-fiberwise-map-overᵉ =
      is-equiv-is-invertibleᵉ
        ( fiberwise-map-over-map-overᵉ)
        ( is-retraction-map-over-fiberwise-map-overᵉ)
        ( is-section-map-over-fiberwise-map-overᵉ)

  equiv-fiberwise-map-over-map-overᵉ :
    map-overᵉ fᵉ gᵉ iᵉ ≃ᵉ fiberwise-map-overᵉ fᵉ gᵉ iᵉ
  pr1ᵉ equiv-fiberwise-map-over-map-overᵉ =
    fiberwise-map-over-map-overᵉ
  pr2ᵉ equiv-fiberwise-map-over-map-overᵉ =
    is-equiv-fiberwise-map-over-map-overᵉ

  equiv-map-over-fiberwise-map-overᵉ :
    fiberwise-map-overᵉ fᵉ gᵉ iᵉ ≃ᵉ map-overᵉ fᵉ gᵉ iᵉ
  pr1ᵉ equiv-map-over-fiberwise-map-overᵉ =
    map-over-fiberwise-map-overᵉ
  pr2ᵉ equiv-map-over-fiberwise-map-overᵉ =
    is-equiv-map-over-fiberwise-map-overᵉ

  equiv-map-over-fiberwise-homᵉ :
    fiberwise-homᵉ (iᵉ ∘ᵉ fᵉ) gᵉ ≃ᵉ map-overᵉ fᵉ gᵉ iᵉ
  equiv-map-over-fiberwise-homᵉ =
    equiv-hom-slice-fiberwise-homᵉ (iᵉ ∘ᵉ fᵉ) gᵉ

  equiv-fiberwise-map-over-fiberwise-homᵉ :
    fiberwise-homᵉ (iᵉ ∘ᵉ fᵉ) gᵉ ≃ᵉ fiberwise-map-overᵉ fᵉ gᵉ iᵉ
  equiv-fiberwise-map-over-fiberwise-homᵉ =
    equiv-fiberwise-map-over-map-overᵉ ∘eᵉ equiv-map-over-fiberwise-homᵉ

  is-small-fiberwise-map-overᵉ :
    is-smallᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ) (fiberwise-map-overᵉ fᵉ gᵉ iᵉ)
  pr1ᵉ is-small-fiberwise-map-overᵉ = map-overᵉ fᵉ gᵉ iᵉ
  pr2ᵉ is-small-fiberwise-map-overᵉ = equiv-map-over-fiberwise-map-overᵉ
```

### Slice maps are equal to fibered maps over

```agda
eq-map-over-id-hom-sliceᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) → hom-sliceᵉ fᵉ gᵉ ＝ᵉ map-overᵉ fᵉ gᵉ idᵉ
eq-map-over-id-hom-sliceᵉ fᵉ gᵉ = reflᵉ

eq-map-over-hom-sliceᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ) → hom-sliceᵉ (iᵉ ∘ᵉ fᵉ) gᵉ ＝ᵉ map-overᵉ fᵉ gᵉ iᵉ
eq-map-over-hom-sliceᵉ fᵉ gᵉ iᵉ = reflᵉ
```

### Horizontal composition for fibered maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  {fᵉ : Aᵉ → Xᵉ} {gᵉ : Bᵉ → Yᵉ} {hᵉ : Cᵉ → Zᵉ}
  where

  is-map-over-pasting-horizontalᵉ :
    {kᵉ : Xᵉ → Yᵉ} {lᵉ : Yᵉ → Zᵉ} {iᵉ : Aᵉ → Bᵉ} {jᵉ : Bᵉ → Cᵉ} →
    is-map-overᵉ fᵉ gᵉ kᵉ iᵉ → is-map-overᵉ gᵉ hᵉ lᵉ jᵉ →
    is-map-overᵉ fᵉ hᵉ (lᵉ ∘ᵉ kᵉ) (jᵉ ∘ᵉ iᵉ)
  is-map-over-pasting-horizontalᵉ {kᵉ} {lᵉ} {iᵉ} {jᵉ} =
    pasting-horizontal-coherence-square-mapsᵉ iᵉ jᵉ fᵉ gᵉ hᵉ kᵉ lᵉ

  map-over-pasting-horizontalᵉ :
    {kᵉ : Xᵉ → Yᵉ} {lᵉ : Yᵉ → Zᵉ} →
    map-overᵉ fᵉ gᵉ kᵉ → map-overᵉ gᵉ hᵉ lᵉ → map-overᵉ fᵉ hᵉ (lᵉ ∘ᵉ kᵉ)
  pr1ᵉ (map-over-pasting-horizontalᵉ {kᵉ} {lᵉ} (iᵉ ,ᵉ Iᵉ) (jᵉ ,ᵉ Jᵉ)) = jᵉ ∘ᵉ iᵉ
  pr2ᵉ (map-over-pasting-horizontalᵉ {kᵉ} {lᵉ} (iᵉ ,ᵉ Iᵉ) (jᵉ ,ᵉ Jᵉ)) =
    is-map-over-pasting-horizontalᵉ {kᵉ} {lᵉ} Iᵉ Jᵉ

  fibered-map-pasting-horizontalᵉ :
    fibered-mapᵉ fᵉ gᵉ → fibered-mapᵉ gᵉ hᵉ → fibered-mapᵉ fᵉ hᵉ
  pr1ᵉ (fibered-map-pasting-horizontalᵉ (kᵉ ,ᵉ iIᵉ) (lᵉ ,ᵉ jJᵉ)) = lᵉ ∘ᵉ kᵉ
  pr2ᵉ (fibered-map-pasting-horizontalᵉ (kᵉ ,ᵉ iIᵉ) (lᵉ ,ᵉ jJᵉ)) =
    map-over-pasting-horizontalᵉ {kᵉ} {lᵉ} iIᵉ jJᵉ
```

### Vertical composition for fibered maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  {Xᵉ : UUᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ}
  {iᵉ : Aᵉ → Bᵉ} {jᵉ : Cᵉ → Dᵉ} {kᵉ : Xᵉ → Yᵉ}
  where

  is-map-over-pasting-verticalᵉ :
    {fᵉ : Aᵉ → Cᵉ} {gᵉ : Bᵉ → Dᵉ}
    {f'ᵉ : Cᵉ → Xᵉ} {g'ᵉ : Dᵉ → Yᵉ} →
    is-map-overᵉ fᵉ gᵉ jᵉ iᵉ → is-map-overᵉ f'ᵉ g'ᵉ kᵉ jᵉ →
    is-map-overᵉ (f'ᵉ ∘ᵉ fᵉ) (g'ᵉ ∘ᵉ gᵉ) kᵉ iᵉ
  is-map-over-pasting-verticalᵉ {fᵉ} {gᵉ} {f'ᵉ} {g'ᵉ} =
    pasting-vertical-coherence-square-mapsᵉ iᵉ fᵉ gᵉ jᵉ f'ᵉ g'ᵉ kᵉ
```

### The truncation level of the types of fibered maps is bounded by the truncation level of the codomains

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  is-trunc-is-map-overᵉ :
    (kᵉ : 𝕋ᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) Yᵉ →
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-truncᵉ kᵉ (is-map-overᵉ fᵉ gᵉ iᵉ hᵉ)
  is-trunc-is-map-overᵉ kᵉ is-trunc-Yᵉ fᵉ gᵉ iᵉ hᵉ =
    is-trunc-Πᵉ kᵉ (λ xᵉ → is-trunc-Yᵉ (iᵉ (fᵉ xᵉ)) (gᵉ (hᵉ xᵉ)))

  is-trunc-map-overᵉ :
    (kᵉ : 𝕋ᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) Yᵉ → is-truncᵉ kᵉ Bᵉ →
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ) → is-truncᵉ kᵉ (map-overᵉ fᵉ gᵉ iᵉ)
  is-trunc-map-overᵉ kᵉ is-trunc-Yᵉ is-trunc-Bᵉ fᵉ gᵉ iᵉ =
    is-trunc-Σᵉ
      ( is-trunc-function-typeᵉ kᵉ is-trunc-Bᵉ)
      ( is-trunc-is-map-overᵉ kᵉ is-trunc-Yᵉ fᵉ gᵉ iᵉ)

  is-trunc-fibered-mapᵉ :
    (kᵉ : 𝕋ᵉ) → is-truncᵉ kᵉ Yᵉ → is-truncᵉ kᵉ Bᵉ →
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) → is-truncᵉ kᵉ (fibered-mapᵉ fᵉ gᵉ)
  is-trunc-fibered-mapᵉ kᵉ is-trunc-Yᵉ is-trunc-Bᵉ fᵉ gᵉ =
    is-trunc-Σᵉ
      ( is-trunc-function-typeᵉ kᵉ is-trunc-Yᵉ)
      ( is-trunc-map-overᵉ
        ( kᵉ)
        ( is-trunc-succ-is-truncᵉ kᵉ is-trunc-Yᵉ)
        ( is-trunc-Bᵉ)
        ( fᵉ)
        ( gᵉ))
```

### The transpose of a fibered map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  transpose-is-map-overᵉ :
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-map-overᵉ fᵉ gᵉ iᵉ hᵉ → is-map-overᵉ hᵉ iᵉ gᵉ fᵉ
  transpose-is-map-overᵉ fᵉ gᵉ iᵉ hᵉ = inv-htpyᵉ

  transpose-map-overᵉ :
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (iᵉ : Xᵉ → Yᵉ)
    (hHᵉ : map-overᵉ fᵉ gᵉ iᵉ) → map-overᵉ (pr1ᵉ hHᵉ) iᵉ gᵉ
  pr1ᵉ (transpose-map-overᵉ fᵉ gᵉ iᵉ hHᵉ) = fᵉ
  pr2ᵉ (transpose-map-overᵉ fᵉ gᵉ iᵉ (hᵉ ,ᵉ Hᵉ)) =
    transpose-is-map-overᵉ fᵉ gᵉ iᵉ hᵉ Hᵉ

  transpose-fibered-mapᵉ :
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
    (ihHᵉ : fibered-mapᵉ fᵉ gᵉ) → fibered-mapᵉ (pr1ᵉ (pr2ᵉ ihHᵉ)) (pr1ᵉ ihHᵉ)
  pr1ᵉ (transpose-fibered-mapᵉ fᵉ gᵉ ihHᵉ) = gᵉ
  pr2ᵉ (transpose-fibered-mapᵉ fᵉ gᵉ (iᵉ ,ᵉ hHᵉ)) =
    transpose-map-overᵉ fᵉ gᵉ iᵉ hHᵉ
```

### If the top left corner is empty, the type of fibered maps is equivalent to maps `X → Y`

```text
         !ᵉ
  emptyᵉ --->ᵉ Bᵉ
    |        |
  !ᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Xᵉ ----->ᵉ Yᵉ
        iᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (is-empty-Aᵉ : is-emptyᵉ Aᵉ)
  where

  inv-compute-fibered-map-is-emptyᵉ : (fibered-mapᵉ fᵉ gᵉ) ≃ᵉ (Xᵉ → Yᵉ)
  inv-compute-fibered-map-is-emptyᵉ =
    right-unit-law-Σ-is-contrᵉ
      ( λ iᵉ →
        is-contr-Σᵉ
          ( universal-property-empty-is-emptyᵉ Aᵉ is-empty-Aᵉ Bᵉ)
          ( ex-falsoᵉ ∘ᵉ is-empty-Aᵉ)
          ( dependent-universal-property-empty-is-emptyᵉ Aᵉ is-empty-Aᵉ
            ( eq-valueᵉ (iᵉ ∘ᵉ fᵉ) (gᵉ ∘ᵉ ex-falsoᵉ ∘ᵉ is-empty-Aᵉ))))

  compute-fibered-map-is-emptyᵉ : (Xᵉ → Yᵉ) ≃ᵉ (fibered-mapᵉ fᵉ gᵉ)
  compute-fibered-map-is-emptyᵉ = inv-equivᵉ inv-compute-fibered-map-is-emptyᵉ

module _
  { l2ᵉ l3ᵉ l4ᵉ : Level} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {fᵉ : emptyᵉ → Xᵉ} (gᵉ : Bᵉ → Yᵉ)
  where

  inv-compute-fibered-map-emptyᵉ : (fibered-mapᵉ fᵉ gᵉ) ≃ᵉ (Xᵉ → Yᵉ)
  inv-compute-fibered-map-emptyᵉ = inv-compute-fibered-map-is-emptyᵉ fᵉ gᵉ idᵉ

  compute-fibered-map-emptyᵉ : (Xᵉ → Yᵉ) ≃ᵉ (fibered-mapᵉ fᵉ gᵉ)
  compute-fibered-map-emptyᵉ = compute-fibered-map-is-emptyᵉ fᵉ gᵉ idᵉ
```

### If the bottom right corner is contractible, the type of fibered maps is equivalent to maps `A → B`

```text
    Aᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |        | !ᵉ
    ∨ᵉ        ∨ᵉ
    Xᵉ --->ᵉ unitᵉ
       !ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ) (is-contr-Yᵉ : is-contrᵉ Yᵉ)
  where

  inv-compute-fibered-map-is-contrᵉ : (fibered-mapᵉ fᵉ gᵉ) ≃ᵉ (Aᵉ → Bᵉ)
  inv-compute-fibered-map-is-contrᵉ =
    ( right-unit-law-Σ-is-contrᵉ
      ( λ jᵉ →
        is-contr-Πᵉ
          ( λ xᵉ →
            is-prop-is-contrᵉ is-contr-Yᵉ (centerᵉ is-contr-Yᵉ) (gᵉ (jᵉ xᵉ))))) ∘eᵉ
    ( left-unit-law-Σ-is-contrᵉ
      ( is-contr-function-typeᵉ is-contr-Yᵉ)
      ( λ _ → centerᵉ is-contr-Yᵉ))

  compute-fibered-map-is-contrᵉ : (Aᵉ → Bᵉ) ≃ᵉ (fibered-mapᵉ fᵉ gᵉ)
  compute-fibered-map-is-contrᵉ = inv-equivᵉ inv-compute-fibered-map-is-contrᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) {gᵉ : Bᵉ → unitᵉ}
  where

  inv-compute-fibered-map-unitᵉ : (fibered-mapᵉ fᵉ gᵉ) ≃ᵉ (Aᵉ → Bᵉ)
  inv-compute-fibered-map-unitᵉ =
    inv-compute-fibered-map-is-contrᵉ fᵉ gᵉ is-contr-unitᵉ

  compute-fibered-map-unitᵉ : (Aᵉ → Bᵉ) ≃ᵉ (fibered-mapᵉ fᵉ gᵉ)
  compute-fibered-map-unitᵉ = compute-fibered-map-is-contrᵉ fᵉ gᵉ is-contr-unitᵉ
```

## Examples

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (hᵉ : Aᵉ → Bᵉ)
  where

  is-fibered-over-selfᵉ : is-map-overᵉ idᵉ idᵉ hᵉ hᵉ
  is-fibered-over-selfᵉ = refl-htpyᵉ

  self-map-overᵉ : map-overᵉ idᵉ idᵉ hᵉ
  pr1ᵉ self-map-overᵉ = hᵉ
  pr2ᵉ self-map-overᵉ = is-fibered-over-selfᵉ

  self-fibered-mapᵉ : fibered-mapᵉ idᵉ idᵉ
  pr1ᵉ self-fibered-mapᵉ = hᵉ
  pr2ᵉ self-fibered-mapᵉ = self-map-overᵉ

  is-map-over-idᵉ : is-map-overᵉ hᵉ hᵉ idᵉ idᵉ
  is-map-over-idᵉ = refl-htpyᵉ

  id-map-overᵉ : map-overᵉ hᵉ hᵉ idᵉ
  pr1ᵉ id-map-overᵉ = idᵉ
  pr2ᵉ id-map-overᵉ = is-map-over-idᵉ

  id-fibered-mapᵉ : fibered-mapᵉ hᵉ hᵉ
  pr1ᵉ id-fibered-mapᵉ = idᵉ
  pr2ᵉ id-fibered-mapᵉ = id-map-overᵉ
```

## See also

-ᵉ [Morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) forᵉ theᵉ sameᵉ conceptᵉ
  underᵉ aᵉ differentᵉ name.ᵉ
-ᵉ Forᵉ theᵉ pullbackᵉ propertyᵉ ofᵉ theᵉ typeᵉ ofᵉ fiberedᵉ maps,ᵉ seeᵉ
  [theᵉ pullback-hom](orthogonal-factorization-systems.pullback-hom.mdᵉ)