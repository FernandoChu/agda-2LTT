# Pointed span diagrams

```agda
module structured-types.pointed-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.morphisms-pointed-arrowsᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-spansᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "(binaryᵉ) pointedᵉ spanᵉ diagram"ᵉ Agda=pointed-span-diagramᵉ}} isᵉ aᵉ
diagramᵉ ofᵉ [pointedᵉ maps](structured-types.pointed-maps.mdᵉ) ofᵉ theᵉ formᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ B.ᵉ
```

Inᵉ otherᵉ words,ᵉ aᵉ pointedᵉ spanᵉ diagramᵉ consistsᵉ ofᵉ twoᵉ
[pointedᵉ types](structured-types.pointed-types.mdᵉ) `A`ᵉ andᵉ `B`ᵉ andᵉ aᵉ
[pointedᵉ span](structured-types.pointed-spans.mdᵉ) fromᵉ `A`ᵉ to `B`.ᵉ

### (Binary) span diagrams of pointed types

```agda
pointed-span-diagramᵉ :
  (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
pointed-span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ =
  Σᵉ ( Pointed-Typeᵉ l1ᵉ)
    ( λ Aᵉ → Σᵉ (Pointed-Typeᵉ l2ᵉ) (pointed-spanᵉ l3ᵉ Aᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Sᵉ : Pointed-Typeᵉ l1ᵉ}
  {Aᵉ : Pointed-Typeᵉ l2ᵉ} {Bᵉ : Pointed-Typeᵉ l3ᵉ}
  where

  make-pointed-span-diagramᵉ :
    (Sᵉ →∗ᵉ Aᵉ) → (Sᵉ →∗ᵉ Bᵉ) → pointed-span-diagramᵉ l2ᵉ l3ᵉ l1ᵉ
  make-pointed-span-diagramᵉ fᵉ gᵉ = (Aᵉ ,ᵉ Bᵉ ,ᵉ Sᵉ ,ᵉ fᵉ ,ᵉ gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (𝒮ᵉ : pointed-span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  pointed-domain-pointed-span-diagramᵉ : Pointed-Typeᵉ l1ᵉ
  pointed-domain-pointed-span-diagramᵉ = pr1ᵉ 𝒮ᵉ

  domain-pointed-span-diagramᵉ : UUᵉ l1ᵉ
  domain-pointed-span-diagramᵉ =
    type-Pointed-Typeᵉ pointed-domain-pointed-span-diagramᵉ

  point-domain-pointed-span-diagramᵉ :
    domain-pointed-span-diagramᵉ
  point-domain-pointed-span-diagramᵉ =
    point-Pointed-Typeᵉ pointed-domain-pointed-span-diagramᵉ

  pointed-codomain-pointed-span-diagramᵉ : Pointed-Typeᵉ l2ᵉ
  pointed-codomain-pointed-span-diagramᵉ = pr1ᵉ (pr2ᵉ 𝒮ᵉ)

  codomain-pointed-span-diagramᵉ : UUᵉ l2ᵉ
  codomain-pointed-span-diagramᵉ =
    type-Pointed-Typeᵉ pointed-codomain-pointed-span-diagramᵉ

  point-codomain-pointed-span-diagramᵉ :
    codomain-pointed-span-diagramᵉ
  point-codomain-pointed-span-diagramᵉ =
    point-Pointed-Typeᵉ pointed-codomain-pointed-span-diagramᵉ

  pointed-span-pointed-span-diagramᵉ :
    pointed-spanᵉ l3ᵉ
      ( pointed-domain-pointed-span-diagramᵉ)
      ( pointed-codomain-pointed-span-diagramᵉ)
  pointed-span-pointed-span-diagramᵉ = pr2ᵉ (pr2ᵉ 𝒮ᵉ)

  spanning-pointed-type-pointed-span-diagramᵉ : Pointed-Typeᵉ l3ᵉ
  spanning-pointed-type-pointed-span-diagramᵉ =
    spanning-pointed-type-pointed-spanᵉ
      ( pointed-span-pointed-span-diagramᵉ)

  spanning-type-pointed-span-diagramᵉ : UUᵉ l3ᵉ
  spanning-type-pointed-span-diagramᵉ =
    type-Pointed-Typeᵉ spanning-pointed-type-pointed-span-diagramᵉ

  point-spanning-type-pointed-span-diagramᵉ :
    spanning-type-pointed-span-diagramᵉ
  point-spanning-type-pointed-span-diagramᵉ =
    point-Pointed-Typeᵉ spanning-pointed-type-pointed-span-diagramᵉ

  left-pointed-map-pointed-span-diagramᵉ :
    spanning-pointed-type-pointed-span-diagramᵉ →∗ᵉ
    pointed-domain-pointed-span-diagramᵉ
  left-pointed-map-pointed-span-diagramᵉ =
    left-pointed-map-pointed-spanᵉ
      ( pointed-span-pointed-span-diagramᵉ)

  left-map-pointed-span-diagramᵉ :
    spanning-type-pointed-span-diagramᵉ → domain-pointed-span-diagramᵉ
  left-map-pointed-span-diagramᵉ =
    left-map-pointed-spanᵉ
      ( pointed-span-pointed-span-diagramᵉ)

  preserves-point-left-map-pointed-span-diagramᵉ :
    left-map-pointed-span-diagramᵉ
      ( point-spanning-type-pointed-span-diagramᵉ) ＝ᵉ
    point-domain-pointed-span-diagramᵉ
  preserves-point-left-map-pointed-span-diagramᵉ =
    preserves-point-left-map-pointed-spanᵉ
      ( pointed-span-pointed-span-diagramᵉ)

  right-pointed-map-pointed-span-diagramᵉ :
    spanning-pointed-type-pointed-span-diagramᵉ →∗ᵉ
    pointed-codomain-pointed-span-diagramᵉ
  right-pointed-map-pointed-span-diagramᵉ =
    right-pointed-map-pointed-spanᵉ
      ( pointed-span-pointed-span-diagramᵉ)

  right-map-pointed-span-diagramᵉ :
    spanning-type-pointed-span-diagramᵉ → codomain-pointed-span-diagramᵉ
  right-map-pointed-span-diagramᵉ =
    right-map-pointed-spanᵉ
      ( pointed-span-pointed-span-diagramᵉ)

  preserves-point-right-map-pointed-span-diagramᵉ :
    right-map-pointed-span-diagramᵉ
      ( point-spanning-type-pointed-span-diagramᵉ) ＝ᵉ
    point-codomain-pointed-span-diagramᵉ
  preserves-point-right-map-pointed-span-diagramᵉ =
    preserves-point-right-map-pointed-spanᵉ
      ( pointed-span-pointed-span-diagramᵉ)
```

### The pointed span diagram obtained from a morphism of pointed arrows

Givenᵉ pointedᵉ mapsᵉ `fᵉ : Aᵉ →∗ᵉ B`ᵉ andᵉ `gᵉ : Xᵉ →∗ᵉ Y`ᵉ andᵉ aᵉ morphismᵉ ofᵉ pointedᵉ
arrowsᵉ `αᵉ : fᵉ →∗ᵉ g`,ᵉ theᵉ pointedᵉ spanᵉ diagramᵉ associatedᵉ to `α`ᵉ isᵉ theᵉ pointedᵉ
spanᵉ diagramᵉ

```text
       fᵉ       α₀ᵉ
  Bᵉ <-----ᵉ Aᵉ ----->ᵉ X.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (gᵉ : Xᵉ →∗ᵉ Yᵉ) (αᵉ : hom-pointed-arrowᵉ fᵉ gᵉ)
  where

  domain-span-diagram-hom-pointed-arrowᵉ : Pointed-Typeᵉ l2ᵉ
  domain-span-diagram-hom-pointed-arrowᵉ = Bᵉ

  type-domain-span-diagram-hom-pointed-arrowᵉ : UUᵉ l2ᵉ
  type-domain-span-diagram-hom-pointed-arrowᵉ =
    type-Pointed-Typeᵉ domain-span-diagram-hom-pointed-arrowᵉ

  point-domain-span-diagram-hom-pointed-arrowᵉ :
    type-domain-span-diagram-hom-pointed-arrowᵉ
  point-domain-span-diagram-hom-pointed-arrowᵉ =
    point-Pointed-Typeᵉ domain-span-diagram-hom-pointed-arrowᵉ

  codomain-span-diagram-hom-pointed-arrowᵉ : Pointed-Typeᵉ l3ᵉ
  codomain-span-diagram-hom-pointed-arrowᵉ = Xᵉ

  type-codomain-span-diagram-hom-pointed-arrowᵉ : UUᵉ l3ᵉ
  type-codomain-span-diagram-hom-pointed-arrowᵉ =
    type-Pointed-Typeᵉ codomain-span-diagram-hom-pointed-arrowᵉ

  point-codomain-span-diagram-hom-pointed-arrowᵉ :
    type-codomain-span-diagram-hom-pointed-arrowᵉ
  point-codomain-span-diagram-hom-pointed-arrowᵉ =
    point-Pointed-Typeᵉ codomain-span-diagram-hom-pointed-arrowᵉ

  pointed-spanning-type-hom-pointed-arrowᵉ : Pointed-Typeᵉ l1ᵉ
  pointed-spanning-type-hom-pointed-arrowᵉ = Aᵉ

  spanning-type-hom-pointed-arrowᵉ : UUᵉ l1ᵉ
  spanning-type-hom-pointed-arrowᵉ =
    type-Pointed-Typeᵉ pointed-spanning-type-hom-pointed-arrowᵉ

  point-spanning-type-hom-pointed-arrowᵉ :
    spanning-type-hom-pointed-arrowᵉ
  point-spanning-type-hom-pointed-arrowᵉ =
    point-Pointed-Typeᵉ pointed-spanning-type-hom-pointed-arrowᵉ

  left-pointed-map-span-diagram-hom-pointed-arrowᵉ :
    pointed-spanning-type-hom-pointed-arrowᵉ →∗ᵉ
    domain-span-diagram-hom-pointed-arrowᵉ
  left-pointed-map-span-diagram-hom-pointed-arrowᵉ = fᵉ

  left-map-span-diagram-hom-pointed-arrowᵉ :
    spanning-type-hom-pointed-arrowᵉ → type-domain-span-diagram-hom-pointed-arrowᵉ
  left-map-span-diagram-hom-pointed-arrowᵉ =
    map-pointed-mapᵉ left-pointed-map-span-diagram-hom-pointed-arrowᵉ

  preserves-point-left-map-span-diagram-hom-pointed-arrowᵉ :
    left-map-span-diagram-hom-pointed-arrowᵉ
      ( point-spanning-type-hom-pointed-arrowᵉ) ＝ᵉ
    point-domain-span-diagram-hom-pointed-arrowᵉ
  preserves-point-left-map-span-diagram-hom-pointed-arrowᵉ =
    preserves-point-pointed-mapᵉ
      ( left-pointed-map-span-diagram-hom-pointed-arrowᵉ)

  right-pointed-map-span-diagram-hom-pointed-arrowᵉ :
    pointed-spanning-type-hom-pointed-arrowᵉ →∗ᵉ
    codomain-span-diagram-hom-pointed-arrowᵉ
  right-pointed-map-span-diagram-hom-pointed-arrowᵉ =
    pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ

  right-map-span-diagram-hom-pointed-arrowᵉ :
    spanning-type-hom-pointed-arrowᵉ →
    type-codomain-span-diagram-hom-pointed-arrowᵉ
  right-map-span-diagram-hom-pointed-arrowᵉ =
    map-pointed-mapᵉ right-pointed-map-span-diagram-hom-pointed-arrowᵉ

  preserves-point-right-map-span-diagram-hom-pointed-arrowᵉ :
    right-map-span-diagram-hom-pointed-arrowᵉ
      ( point-spanning-type-hom-pointed-arrowᵉ) ＝ᵉ
    point-codomain-span-diagram-hom-pointed-arrowᵉ
  preserves-point-right-map-span-diagram-hom-pointed-arrowᵉ =
    preserves-point-pointed-mapᵉ
      ( right-pointed-map-span-diagram-hom-pointed-arrowᵉ)

  span-hom-pointed-arrowᵉ :
    pointed-spanᵉ l1ᵉ Bᵉ Xᵉ
  pr1ᵉ span-hom-pointed-arrowᵉ =
    Aᵉ
  pr1ᵉ (pr2ᵉ span-hom-pointed-arrowᵉ) =
    left-pointed-map-span-diagram-hom-pointed-arrowᵉ
  pr2ᵉ (pr2ᵉ span-hom-pointed-arrowᵉ) =
    right-pointed-map-span-diagram-hom-pointed-arrowᵉ

  span-diagram-hom-pointed-arrowᵉ : pointed-span-diagramᵉ l2ᵉ l3ᵉ l1ᵉ
  pr1ᵉ span-diagram-hom-pointed-arrowᵉ =
    domain-span-diagram-hom-pointed-arrowᵉ
  pr1ᵉ (pr2ᵉ span-diagram-hom-pointed-arrowᵉ) =
    codomain-span-diagram-hom-pointed-arrowᵉ
  pr2ᵉ (pr2ᵉ span-diagram-hom-pointed-arrowᵉ) =
    span-hom-pointed-arrowᵉ
```

## See also

-ᵉ [Transpositionᵉ ofᵉ pointedᵉ spanᵉ diagrams](structured-types.transposition-pointed-span-diagrams.mdᵉ)