# Pullbacks of subtypes

```agda
module foundation.pullbacks-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalencesᵉ
open import foundation.powersetsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ

open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
```

</details>

## Idea

Considerᵉ aᵉ [subtype](foundation-core.subtypes.mdᵉ) `T`ᵉ ofᵉ aᵉ typeᵉ `B`ᵉ andᵉ aᵉ mapᵉ
`fᵉ : Aᵉ → B`.ᵉ Thenᵉ theᵉ {{#conceptᵉ "pullbackᵉ subtype"ᵉ Agda=pullback-subtypeᵉ}}
`pullbackᵉ fᵉ T`ᵉ ofᵉ `A`ᵉ isᵉ definedᵉ to beᵉ `Tᵉ ∘ᵉ f`.ᵉ Thisᵉ fitsᵉ in aᵉ
[pullbackᵉ diagram](foundation-core.pullbacks.mdᵉ)

```text
                 π₂ᵉ
  pullbackᵉ fᵉ Tᵉ ----->ᵉ Tᵉ
       | ⌟ᵉ            |
    π₁ᵉ |              | iᵉ
       |              |
       ∨ᵉ              ∨ᵉ
       Aᵉ ----------->ᵉ Bᵉ
               fᵉ
```

Theᵉ
[universalᵉ propertyᵉ ofᵉ pullbacks](foundation.universal-property-pullbacks.mdᵉ)
quiteᵉ literallyᵉ returnsᵉ theᵉ definitionᵉ ofᵉ theᵉ subtypeᵉ `pullbackᵉ fᵉ T`,ᵉ becauseᵉ itᵉ
essentiallyᵉ assertsᵉ thatᵉ

```text
  (Sᵉ ⊆ᵉ pullbackᵉ fᵉ Tᵉ) ↔ᵉ ((xᵉ : Aᵉ) → is-in-subtypeᵉ Sᵉ xᵉ → is-in-subtypeᵉ Tᵉ (fᵉ x)).ᵉ
```

Theᵉ operationᵉ `pullbackᵉ fᵉ : subtypeᵉ Bᵉ → subtypeᵉ A`ᵉ isᵉ anᵉ
[orderᵉ preservingᵉ map](order-theory.order-preserving-maps-large-posets.mdᵉ)
betweenᵉ theᵉ [powersets](foundation.powersets.mdᵉ) ofᵉ `B`ᵉ andᵉ `A`.ᵉ

Inᵉ theᵉ fileᵉ [Imagesᵉ ofᵉ subtypes](foundation.images-subtypes.mdᵉ) weᵉ showᵉ thatᵉ theᵉ
pullbackᵉ operationᵉ onᵉ subtypesᵉ isᵉ theᵉ upperᵉ adjointᵉ ofᵉ aᵉ
[Galoisᵉ connection](order-theory.galois-connections-large-posets.md).ᵉ

## Definitions

### The predicate of being a pullback of subtypes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (Tᵉ : subtypeᵉ l3ᵉ Bᵉ) (Sᵉ : subtypeᵉ l4ᵉ Aᵉ)
  where

  is-pullback-subtypeᵉ : UUωᵉ
  is-pullback-subtypeᵉ =
    {lᵉ : Level} (Uᵉ : subtypeᵉ lᵉ Aᵉ) →
    (Uᵉ ⊆ᵉ Sᵉ) ↔ᵉ ((xᵉ : Aᵉ) → is-in-subtypeᵉ Uᵉ xᵉ → is-in-subtypeᵉ Tᵉ (fᵉ xᵉ))
```

### Pullbacks of subtypes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Tᵉ : subtypeᵉ l3ᵉ Bᵉ)
  where

  pullback-subtypeᵉ : subtypeᵉ l3ᵉ Aᵉ
  pullback-subtypeᵉ = Tᵉ ∘ᵉ fᵉ

  is-in-pullback-subtypeᵉ : Aᵉ → UUᵉ l3ᵉ
  is-in-pullback-subtypeᵉ = is-in-subtypeᵉ pullback-subtypeᵉ

  is-prop-is-in-pullback-subtypeᵉ :
    (xᵉ : Aᵉ) → is-propᵉ (is-in-pullback-subtypeᵉ xᵉ)
  is-prop-is-in-pullback-subtypeᵉ = is-prop-is-in-subtypeᵉ pullback-subtypeᵉ

  type-pullback-subtypeᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-pullback-subtypeᵉ = type-subtypeᵉ pullback-subtypeᵉ

  inclusion-pullback-subtypeᵉ : type-pullback-subtypeᵉ → Aᵉ
  inclusion-pullback-subtypeᵉ = inclusion-subtypeᵉ pullback-subtypeᵉ
```

### The order preserving pullback operation on subtypes

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  preserves-order-pullback-subtypeᵉ :
    preserves-order-map-Large-Posetᵉ
      ( powerset-Large-Posetᵉ Bᵉ)
      ( powerset-Large-Posetᵉ Aᵉ)
      ( pullback-subtypeᵉ fᵉ)
  preserves-order-pullback-subtypeᵉ Sᵉ Tᵉ Hᵉ xᵉ = Hᵉ (fᵉ xᵉ)

  pullback-subtype-hom-Large-Posetᵉ :
    hom-Large-Posetᵉ (λ lᵉ → lᵉ) (powerset-Large-Posetᵉ Bᵉ) (powerset-Large-Posetᵉ Aᵉ)
  map-hom-Large-Preorderᵉ pullback-subtype-hom-Large-Posetᵉ =
    pullback-subtypeᵉ fᵉ
  preserves-order-hom-Large-Preorderᵉ pullback-subtype-hom-Large-Posetᵉ =
    preserves-order-pullback-subtypeᵉ
```

## See also

-ᵉ Theᵉ [imageᵉ ofᵉ aᵉ subtype](foundation.images-subtypes.mdᵉ)