# Coequalizers

```agda
module synthetic-homotopy-theory.coequalizersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-arrowsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-universal-property-coequalizersᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-coequalizersᵉ
```

</details>

## Idea

Theᵉ **coequalizer**ᵉ ofᵉ aᵉ [doubleᵉ arrow](foundation.double-arrows.mdᵉ)
`f,ᵉ gᵉ : Aᵉ → B`ᵉ isᵉ theᵉ colimitingᵉ [cofork](synthetic-homotopy-theory.coforks.md),ᵉ
i.e.ᵉ aᵉ coforkᵉ with theᵉ
[universalᵉ propertyᵉ ofᵉ coequalizers](synthetic-homotopy-theory.universal-property-coequalizers.md).ᵉ

## Properties

### All double arrows admit a coequalizer

Theᵉ
{{#conceptᵉ "standardᵉ coequalizer"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=standard-coequalizerᵉ}}
mayᵉ beᵉ obtainedᵉ asᵉ aᵉ [pushout](synthetic-homotopy-theory.pushouts.mdᵉ) ofᵉ theᵉ
spanᵉ

```text
     ∇ᵉ         [f,gᵉ]
Aᵉ <-----ᵉ Aᵉ +ᵉ Aᵉ ----->ᵉ Bᵉ
```

where theᵉ leftᵉ mapᵉ isᵉ theᵉ
[codiagonalᵉ map](foundation.codiagonal-maps-of-types.md),ᵉ sendingᵉ `inl(a)`ᵉ andᵉ
`inr(a)`ᵉ to `a`,ᵉ andᵉ theᵉ rightᵉ mapᵉ isᵉ definedᵉ byᵉ theᵉ universalᵉ propertyᵉ ofᵉ
[coproducts](foundation.coproduct-types.mdᵉ) to sendᵉ `inl(a)`ᵉ to `f(a)`ᵉ andᵉ
`inr(a)`ᵉ to `g(a)`.ᵉ

Theᵉ pushoutᵉ thusᵉ constructedᵉ willᵉ consistᵉ ofᵉ aᵉ copyᵉ ofᵉ `B`,ᵉ aᵉ copyᵉ ofᵉ `A`,ᵉ andᵉ
forᵉ everyᵉ pointᵉ `a`ᵉ ofᵉ `A`ᵉ thereᵉ willᵉ beᵉ aᵉ pathᵉ fromᵉ `f(a)`ᵉ to `a`ᵉ andᵉ to
`g(a)`,ᵉ whichᵉ correspondsᵉ to havingᵉ aᵉ copyᵉ ofᵉ `B`ᵉ with pathsᵉ connectingᵉ everyᵉ
`f(a)`ᵉ to `g(a)`.ᵉ

Theᵉ constructionᵉ fromᵉ pushoutsᵉ itselfᵉ isᵉ anᵉ implementationᵉ detail,ᵉ whichᵉ isᵉ whyᵉ
theᵉ definitionᵉ isᵉ markedᵉ abstract.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ)
  where

  abstract
    standard-coequalizerᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    standard-coequalizerᵉ =
      pushoutᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)

    cofork-standard-coequalizerᵉ : coforkᵉ aᵉ standard-coequalizerᵉ
    cofork-standard-coequalizerᵉ =
      cofork-cocone-codiagonalᵉ aᵉ
        ( cocone-pushoutᵉ
          ( vertical-map-span-cocone-coforkᵉ aᵉ)
          ( horizontal-map-span-cocone-coforkᵉ aᵉ))

    dup-standard-coequalizerᵉ :
      dependent-universal-property-coequalizerᵉ aᵉ cofork-standard-coequalizerᵉ
    dup-standard-coequalizerᵉ =
      dependent-universal-property-coequalizer-dependent-universal-property-pushoutᵉ
        ( aᵉ)
        ( cofork-standard-coequalizerᵉ)
        ( λ Pᵉ →
          trᵉ
            ( λ cᵉ →
              is-equivᵉ
                ( dependent-cocone-mapᵉ
                  ( vertical-map-span-cocone-coforkᵉ aᵉ)
                  ( horizontal-map-span-cocone-coforkᵉ aᵉ)
                  ( cᵉ)
                  ( Pᵉ)))
            ( invᵉ
              ( is-retraction-map-inv-is-equivᵉ
                ( is-equiv-cofork-cocone-codiagonalᵉ aᵉ)
                ( cocone-pushoutᵉ
                  ( vertical-map-span-cocone-coforkᵉ aᵉ)
                  ( horizontal-map-span-cocone-coforkᵉ aᵉ))))
            ( dup-pushoutᵉ
              ( vertical-map-span-cocone-coforkᵉ aᵉ)
              ( horizontal-map-span-cocone-coforkᵉ aᵉ)
              ( Pᵉ)))

    up-standard-coequalizerᵉ :
      universal-property-coequalizerᵉ aᵉ cofork-standard-coequalizerᵉ
    up-standard-coequalizerᵉ =
      universal-property-dependent-universal-property-coequalizerᵉ aᵉ
        ( cofork-standard-coequalizerᵉ)
        ( dup-standard-coequalizerᵉ)
```