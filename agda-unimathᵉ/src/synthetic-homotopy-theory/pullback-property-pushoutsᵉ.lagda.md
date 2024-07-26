# The pullback property of pushouts

```agda
module synthetic-homotopy-theory.pullback-property-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.pullbacksᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
```

</details>

## Idea

Theᵉ
[universalᵉ propertyᵉ ofᵉ theᵉ pushout](synthetic-homotopy-theory.universal-property-pushouts.mdᵉ)
ofᵉ aᵉ spanᵉ `S`ᵉ canᵉ alsoᵉ beᵉ statedᵉ asᵉ aᵉ
[pullbackᵉ property](foundation-core.universal-property-pullbacks.mdᵉ): aᵉ coconeᵉ
`cᵉ ≐ᵉ (iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ with vertexᵉ `X`ᵉ satisfiesᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ
pushoutᵉ ofᵉ `S`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ squareᵉ

```text
  Y^Xᵉ ----->ᵉ Y^Bᵉ
   | ⌟ᵉ        |
   |          |
   ∨ᵉ          ∨ᵉ
  Y^Aᵉ ----->ᵉ Y^Sᵉ
```

isᵉ aᵉ [pullback](foundation.pullbacks.mdᵉ) squareᵉ forᵉ everyᵉ typeᵉ `Y`.ᵉ Below,ᵉ weᵉ
firstᵉ defineᵉ theᵉ [cone](foundation.cones-over-cospan-diagrams.mdᵉ) ofᵉ thisᵉ
[commutingᵉ square](foundation.commuting-squares-of-maps.md),ᵉ andᵉ thenᵉ weᵉ
introduceᵉ theᵉ typeᵉ `pullback-property-pushout`,ᵉ whichᵉ statesᵉ thatᵉ theᵉ aboveᵉ
squareᵉ isᵉ aᵉ [pullback](foundation-core.universal-property-pullbacks.md).ᵉ

## Definition

### The pullback property of pushouts

```agda
cone-pullback-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ lᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Yᵉ : UUᵉ lᵉ) →
  coneᵉ (_∘ᵉ fᵉ) (_∘ᵉ gᵉ) (Xᵉ → Yᵉ)
pr1ᵉ (cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ) =
  precompᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) Yᵉ
pr1ᵉ (pr2ᵉ (cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ)) =
  precompᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) Yᵉ
pr2ᵉ (pr2ᵉ (cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ)) =
  precomp-coherence-square-mapsᵉ
    ( gᵉ)
    ( fᵉ)
    ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
    ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
    ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)
    ( Yᵉ)

pullback-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  UUωᵉ
pullback-property-pushoutᵉ fᵉ gᵉ cᵉ =
  {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) →
  is-pullbackᵉ
    ( precompᵉ fᵉ Yᵉ)
    ( precompᵉ gᵉ Yᵉ)
    ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ)
```