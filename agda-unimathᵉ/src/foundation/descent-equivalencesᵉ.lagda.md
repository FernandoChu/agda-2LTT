# Descent for equivalences

```agda
module foundation.descent-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.pullbacksᵉ
```

</details>

## Idea

Theᵉ descentᵉ propertyᵉ ofᵉ equivalencesᵉ isᵉ aᵉ somewhatᵉ degenerateᵉ formᵉ ofᵉ aᵉ descentᵉ
property.ᵉ Itᵉ assertsᵉ thatᵉ in aᵉ commutingᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
     pᵉ        qᵉ
 Aᵉ ----->ᵉ Bᵉ ----->ᵉ Cᵉ
 |        |        |
f|ᵉ       g|ᵉ        |hᵉ
 ∨ᵉ        ∨ᵉ        ∨ᵉ
 Xᵉ ----->ᵉ Yᵉ ----->ᵉ Z,ᵉ
     iᵉ        jᵉ
```

ifᵉ theᵉ mapsᵉ `i`ᵉ andᵉ `p`ᵉ areᵉ equivalences,ᵉ thenᵉ theᵉ rightᵉ squareᵉ isᵉ aᵉ pullbackᵉ ifᵉ
andᵉ onlyᵉ ifᵉ theᵉ outerᵉ rectangleᵉ isᵉ aᵉ pullback.ᵉ

## Theorem

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  where

  descent-is-equivᵉ :
    (iᵉ : Xᵉ → Yᵉ) (jᵉ : Yᵉ → Zᵉ) (hᵉ : Cᵉ → Zᵉ)
    (cᵉ : coneᵉ jᵉ hᵉ Bᵉ) (dᵉ : coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) Aᵉ) →
    is-equivᵉ iᵉ → is-equivᵉ (horizontal-map-coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ) →
    is-pullbackᵉ (jᵉ ∘ᵉ iᵉ) hᵉ (pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ) →
    is-pullbackᵉ jᵉ hᵉ cᵉ
  descent-is-equivᵉ iᵉ jᵉ hᵉ cᵉ dᵉ
    is-equiv-iᵉ is-equiv-kᵉ is-pb-rectangleᵉ =
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ jᵉ hᵉ cᵉ
      ( map-inv-is-equiv-precomp-Π-is-equivᵉ
        ( is-equiv-iᵉ)
        ( λ yᵉ → is-equivᵉ (map-fiber-vertical-map-coneᵉ jᵉ hᵉ cᵉ yᵉ))
        ( λ xᵉ →
          is-equiv-right-map-triangleᵉ
          ( map-fiber-vertical-map-coneᵉ (jᵉ ∘ᵉ iᵉ) hᵉ
            ( pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ) xᵉ)
          ( map-fiber-vertical-map-coneᵉ jᵉ hᵉ cᵉ (iᵉ xᵉ))
          ( map-fiber-vertical-map-coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ xᵉ)
          ( preserves-pasting-horizontal-map-fiber-vertical-map-coneᵉ
            ( iᵉ)
            ( jᵉ)
            ( hᵉ)
            ( cᵉ)
            ( dᵉ)
            ( xᵉ))
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ (jᵉ ∘ᵉ iᵉ) hᵉ
            ( pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ)
            ( is-pb-rectangleᵉ)
            ( xᵉ))
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ iᵉ
            ( vertical-map-coneᵉ jᵉ hᵉ cᵉ)
            ( dᵉ)
            ( is-pullback-is-equiv-horizontal-mapsᵉ iᵉ
              ( vertical-map-coneᵉ jᵉ hᵉ cᵉ)
              ( dᵉ)
              ( is-equiv-iᵉ)
              ( is-equiv-kᵉ))
            ( xᵉ))))

  descent-equivᵉ :
    (iᵉ : Xᵉ ≃ᵉ Yᵉ) (jᵉ : Yᵉ → Zᵉ) (hᵉ : Cᵉ → Zᵉ)
    (cᵉ : coneᵉ jᵉ hᵉ Bᵉ) (dᵉ : coneᵉ (map-equivᵉ iᵉ) (vertical-map-coneᵉ jᵉ hᵉ cᵉ) Aᵉ) →
    is-equivᵉ (horizontal-map-coneᵉ (map-equivᵉ iᵉ) (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ) →
    is-pullbackᵉ
      ( jᵉ ∘ᵉ map-equivᵉ iᵉ)
      ( hᵉ)
      ( pasting-horizontal-coneᵉ (map-equivᵉ iᵉ) jᵉ hᵉ cᵉ dᵉ) →
    is-pullbackᵉ jᵉ hᵉ cᵉ
  descent-equivᵉ iᵉ jᵉ hᵉ cᵉ dᵉ =
    descent-is-equivᵉ (map-equivᵉ iᵉ) jᵉ hᵉ cᵉ dᵉ (is-equiv-map-equivᵉ iᵉ)
```