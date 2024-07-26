# Binary type duality

```agda
module foundation.binary-type-dualityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-spansᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.multivariable-homotopiesᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.spansᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ principleᵉ ofᵉ {{#conceptᵉ "binaryᵉ typeᵉ duality"ᵉ Agda=binary-type-dualityᵉ}}
assertsᵉ thatᵉ theᵉ typeᵉ ofᵉ [binaryᵉ relations](foundation.binary-relations.mdᵉ)
`Aᵉ → Bᵉ → 𝒰`ᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ ofᵉ
[binaryᵉ spans](foundation.spans.mdᵉ) fromᵉ `A`ᵉ to `B`.ᵉ Theᵉ binaryᵉ typeᵉ dualityᵉ
principleᵉ isᵉ aᵉ binaryᵉ versionᵉ ofᵉ theᵉ [typeᵉ duality](foundation.type-duality.mdᵉ)
principle,ᵉ whichᵉ assertsᵉ thatᵉ typeᵉ familiesᵉ overᵉ aᵉ typeᵉ `A`ᵉ areᵉ equivalentlyᵉ
describedᵉ asᵉ mapsᵉ intoᵉ `A`,ᵉ andᵉ makesᵉ essentialᵉ useᵉ ofᵉ theᵉ
[univalenceᵉ axiom](foundation.univalence.md).ᵉ

Theᵉ equivalenceᵉ ofᵉ binaryᵉ typeᵉ dualityᵉ takesᵉ aᵉ binaryᵉ relationᵉ `Rᵉ : Aᵉ → Bᵉ → 𝒰`ᵉ
to theᵉ spanᵉ

```text
  Aᵉ <-----ᵉ Σᵉ (aᵉ : A),ᵉ Σᵉ (bᵉ : B),ᵉ Rᵉ aᵉ bᵉ ----->ᵉ B.ᵉ
```

andᵉ itsᵉ inverseᵉ takesᵉ aᵉ spanᵉ `Aᵉ <-f-ᵉ Sᵉ -g->ᵉ B`ᵉ to theᵉ binaryᵉ relationᵉ

```text
  aᵉ bᵉ ↦ᵉ Σᵉ (sᵉ : S),ᵉ (fᵉ sᵉ ＝ᵉ aᵉ) ×ᵉ (gᵉ sᵉ ＝ᵉ b).ᵉ
```

## Definitions

### The span associated to a binary relation

Givenᵉ aᵉ binaryᵉ relationᵉ `Rᵉ : Aᵉ → Bᵉ → 𝒰`,ᵉ weᵉ obtainᵉ aᵉ spanᵉ

```text
  Aᵉ <-----ᵉ Σᵉ (aᵉ : A),ᵉ Σᵉ (bᵉ : B),ᵉ Rᵉ aᵉ bᵉ ----->ᵉ B.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Rᵉ : Aᵉ → Bᵉ → UUᵉ l3ᵉ)
  where

  spanning-type-span-binary-relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  spanning-type-span-binary-relationᵉ = Σᵉ Aᵉ (λ aᵉ → Σᵉ Bᵉ (λ bᵉ → Rᵉ aᵉ bᵉ))

  left-map-span-binary-relationᵉ : spanning-type-span-binary-relationᵉ → Aᵉ
  left-map-span-binary-relationᵉ = pr1ᵉ

  right-map-span-binary-relationᵉ : spanning-type-span-binary-relationᵉ → Bᵉ
  right-map-span-binary-relationᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  span-binary-relationᵉ : spanᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ Bᵉ
  pr1ᵉ span-binary-relationᵉ = spanning-type-span-binary-relationᵉ
  pr1ᵉ (pr2ᵉ span-binary-relationᵉ) = left-map-span-binary-relationᵉ
  pr2ᵉ (pr2ᵉ span-binary-relationᵉ) = right-map-span-binary-relationᵉ
```

### The binary relation associated to a span

Givenᵉ aᵉ spanᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

weᵉ obtainᵉ theᵉ binaryᵉ relationᵉ `aᵉ bᵉ ↦ᵉ Σᵉ (sᵉ : S),ᵉ (fᵉ sᵉ ＝ᵉ aᵉ) ×ᵉ (gᵉ sᵉ ＝ᵉ b)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  binary-relation-spanᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ → Aᵉ → Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  binary-relation-spanᵉ Sᵉ aᵉ bᵉ =
    Σᵉ ( spanning-type-spanᵉ Sᵉ)
      ( λ sᵉ → (left-map-spanᵉ Sᵉ sᵉ ＝ᵉ aᵉ) ×ᵉ (right-map-spanᵉ Sᵉ sᵉ ＝ᵉ bᵉ))
```

## Properties

### Any span `S` is equivalent to the span associated to the binary relation associated to `S`

Theᵉ constructionᵉ ofᵉ thisᵉ equivalenceᵉ ofᵉ spanᵉ diagramsᵉ isᵉ simplyᵉ byᵉ pattern
matchingᵉ allᵉ theᵉ way.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ)
  where

  map-equiv-spanning-type-span-binary-relation-spanᵉ :
    spanning-type-spanᵉ Sᵉ →
    spanning-type-span-binary-relationᵉ (binary-relation-spanᵉ Sᵉ)
  map-equiv-spanning-type-span-binary-relation-spanᵉ sᵉ =
    ( left-map-spanᵉ Sᵉ sᵉ ,ᵉ right-map-spanᵉ Sᵉ sᵉ ,ᵉ sᵉ ,ᵉ reflᵉ ,ᵉ reflᵉ)

  map-inv-equiv-spanning-type-span-binary-relation-spanᵉ :
    spanning-type-span-binary-relationᵉ (binary-relation-spanᵉ Sᵉ) →
    spanning-type-spanᵉ Sᵉ
  map-inv-equiv-spanning-type-span-binary-relation-spanᵉ (aᵉ ,ᵉ bᵉ ,ᵉ sᵉ ,ᵉ _) = sᵉ

  is-section-map-inv-equiv-spanning-type-span-binary-relation-spanᵉ :
    is-sectionᵉ
      ( map-equiv-spanning-type-span-binary-relation-spanᵉ)
      ( map-inv-equiv-spanning-type-span-binary-relation-spanᵉ)
  is-section-map-inv-equiv-spanning-type-span-binary-relation-spanᵉ
    ( ._ ,ᵉ ._ ,ᵉ sᵉ ,ᵉ reflᵉ ,ᵉ reflᵉ) =
    reflᵉ

  is-retraction-map-inv-equiv-spanning-type-span-binary-relation-spanᵉ :
    is-retractionᵉ
      ( map-equiv-spanning-type-span-binary-relation-spanᵉ)
      ( map-inv-equiv-spanning-type-span-binary-relation-spanᵉ)
  is-retraction-map-inv-equiv-spanning-type-span-binary-relation-spanᵉ sᵉ = reflᵉ

  is-equiv-map-equiv-spanning-type-span-binary-relation-spanᵉ :
    is-equivᵉ
      ( map-equiv-spanning-type-span-binary-relation-spanᵉ)
  is-equiv-map-equiv-spanning-type-span-binary-relation-spanᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-equiv-spanning-type-span-binary-relation-spanᵉ)
      ( is-section-map-inv-equiv-spanning-type-span-binary-relation-spanᵉ)
      ( is-retraction-map-inv-equiv-spanning-type-span-binary-relation-spanᵉ)

  equiv-spanning-type-span-binary-relation-spanᵉ :
    spanning-type-spanᵉ Sᵉ ≃ᵉ
    spanning-type-span-binary-relationᵉ (binary-relation-spanᵉ Sᵉ)
  pr1ᵉ equiv-spanning-type-span-binary-relation-spanᵉ =
    map-equiv-spanning-type-span-binary-relation-spanᵉ
  pr2ᵉ equiv-spanning-type-span-binary-relation-spanᵉ =
    is-equiv-map-equiv-spanning-type-span-binary-relation-spanᵉ

  equiv-span-binary-relation-spanᵉ :
    equiv-spanᵉ Sᵉ (span-binary-relationᵉ (binary-relation-spanᵉ Sᵉ))
  pr1ᵉ equiv-span-binary-relation-spanᵉ =
    equiv-spanning-type-span-binary-relation-spanᵉ
  pr1ᵉ (pr2ᵉ equiv-span-binary-relation-spanᵉ) =
    refl-htpyᵉ
  pr2ᵉ (pr2ᵉ equiv-span-binary-relation-spanᵉ) =
    refl-htpyᵉ
```

### Any binary relation `R` is equivalent to the binary relation associated to the span associated to `R`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Rᵉ : Aᵉ → Bᵉ → UUᵉ l3ᵉ)
  (aᵉ : Aᵉ) (bᵉ : Bᵉ)
  where

  map-equiv-binary-relation-span-binary-relationᵉ :
    Rᵉ aᵉ bᵉ → binary-relation-spanᵉ (span-binary-relationᵉ Rᵉ) aᵉ bᵉ
  map-equiv-binary-relation-span-binary-relationᵉ rᵉ =
    ((aᵉ ,ᵉ bᵉ ,ᵉ rᵉ) ,ᵉ reflᵉ ,ᵉ reflᵉ)

  map-inv-equiv-binary-relation-span-binary-relationᵉ :
    binary-relation-spanᵉ (span-binary-relationᵉ Rᵉ) aᵉ bᵉ → Rᵉ aᵉ bᵉ
  map-inv-equiv-binary-relation-span-binary-relationᵉ
    ((.aᵉ ,ᵉ .bᵉ ,ᵉ rᵉ) ,ᵉ reflᵉ ,ᵉ reflᵉ) =
    rᵉ

  is-section-map-inv-equiv-binary-relation-span-binary-relationᵉ :
    is-sectionᵉ
      ( map-equiv-binary-relation-span-binary-relationᵉ)
      ( map-inv-equiv-binary-relation-span-binary-relationᵉ)
  is-section-map-inv-equiv-binary-relation-span-binary-relationᵉ
    ((.aᵉ ,ᵉ .bᵉ ,ᵉ rᵉ) ,ᵉ reflᵉ ,ᵉ reflᵉ) =
    reflᵉ

  is-retraction-map-inv-equiv-binary-relation-span-binary-relationᵉ :
    is-retractionᵉ
      ( map-equiv-binary-relation-span-binary-relationᵉ)
      ( map-inv-equiv-binary-relation-span-binary-relationᵉ)
  is-retraction-map-inv-equiv-binary-relation-span-binary-relationᵉ rᵉ = reflᵉ

  is-equiv-map-equiv-binary-relation-span-binary-relationᵉ :
    is-equivᵉ map-equiv-binary-relation-span-binary-relationᵉ
  is-equiv-map-equiv-binary-relation-span-binary-relationᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-binary-relation-span-binary-relationᵉ
      is-section-map-inv-equiv-binary-relation-span-binary-relationᵉ
      is-retraction-map-inv-equiv-binary-relation-span-binary-relationᵉ

  equiv-binary-relation-span-binary-relationᵉ :
    Rᵉ aᵉ bᵉ ≃ᵉ binary-relation-spanᵉ (span-binary-relationᵉ Rᵉ) aᵉ bᵉ
  pr1ᵉ equiv-binary-relation-span-binary-relationᵉ =
    map-equiv-binary-relation-span-binary-relationᵉ
  pr2ᵉ equiv-binary-relation-span-binary-relationᵉ =
    is-equiv-map-equiv-binary-relation-span-binary-relationᵉ
```

## Theorem

### Binary spans are equivalent to binary relations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  is-section-binary-relation-spanᵉ :
    is-sectionᵉ
      ( span-binary-relationᵉ {l3ᵉ = l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ} {Aᵉ} {Bᵉ})
      ( binary-relation-spanᵉ {l3ᵉ = l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ} {Aᵉ} {Bᵉ})
  is-section-binary-relation-spanᵉ Sᵉ =
    invᵉ
      ( eq-equiv-spanᵉ
        ( Sᵉ)
        ( span-binary-relationᵉ (binary-relation-spanᵉ Sᵉ))
        ( equiv-span-binary-relation-spanᵉ Sᵉ))

  is-retraction-binary-relation-spanᵉ :
    is-retractionᵉ
      ( span-binary-relationᵉ {l3ᵉ = l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ} {Aᵉ} {Bᵉ})
      ( binary-relation-spanᵉ {l3ᵉ = l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ} {Aᵉ} {Bᵉ})
  is-retraction-binary-relation-spanᵉ Rᵉ =
    invᵉ
      ( eq-multivariable-htpyᵉ 2
        ( λ aᵉ bᵉ → eq-equivᵉ (equiv-binary-relation-span-binary-relationᵉ Rᵉ aᵉ bᵉ)))

  is-equiv-span-binary-relationᵉ :
    is-equivᵉ (span-binary-relationᵉ {l3ᵉ = l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ} {Aᵉ} {Bᵉ})
  is-equiv-span-binary-relationᵉ =
    is-equiv-is-invertibleᵉ
      ( binary-relation-spanᵉ)
      ( is-section-binary-relation-spanᵉ)
      ( is-retraction-binary-relation-spanᵉ)

  binary-type-dualityᵉ : (Aᵉ → Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)) ≃ᵉ spanᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ Bᵉ
  pr1ᵉ binary-type-dualityᵉ = span-binary-relationᵉ
  pr2ᵉ binary-type-dualityᵉ = is-equiv-span-binary-relationᵉ

  is-equiv-binary-relation-spanᵉ :
    is-equivᵉ (binary-relation-spanᵉ {l3ᵉ = l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ} {Aᵉ} {Bᵉ})
  is-equiv-binary-relation-spanᵉ =
    is-equiv-is-invertibleᵉ
      ( span-binary-relationᵉ)
      ( is-retraction-binary-relation-spanᵉ)
      ( is-section-binary-relation-spanᵉ)

  inv-binary-type-dualityᵉ :
    spanᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ Bᵉ ≃ᵉ (Aᵉ → Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
  pr1ᵉ inv-binary-type-dualityᵉ = binary-relation-spanᵉ
  pr2ᵉ inv-binary-type-dualityᵉ = is-equiv-binary-relation-spanᵉ
```