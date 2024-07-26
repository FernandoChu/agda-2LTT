# Tangent spheres

```agda
module synthetic-homotopy-theory.tangent-spheresᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.mere-spheresᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.spheresᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `X`ᵉ andᵉ aᵉ pointᵉ `xᵉ : X`.ᵉ Weᵉ sayᵉ thatᵉ `x`ᵉ **hasᵉ aᵉ tangentᵉ
`n`-sphere**ᵉ ifᵉ weᵉ canᵉ constructᵉ theᵉ followingᵉ dataᵉ:

-ᵉ Aᵉ [mereᵉ sphere](synthetic-homotopy-theory.mere-spheres.mdᵉ) `T`,ᵉ whichᵉ weᵉ alsoᵉ
  referᵉ to asᵉ theᵉ **tangentᵉ sphere**ᵉ ofᵉ `x`.ᵉ
-ᵉ Aᵉ typeᵉ `C`,ᵉ whichᵉ weᵉ callᵉ theᵉ **complement**ᵉ ofᵉ `x`.ᵉ
-ᵉ Aᵉ mapᵉ `jᵉ : Tᵉ → C`ᵉ includingᵉ theᵉ tangentᵉ sphereᵉ intoᵉ theᵉ complement.ᵉ
-ᵉ Aᵉ mapᵉ `iᵉ : Cᵉ → X`ᵉ includingᵉ theᵉ complementᵉ intoᵉ theᵉ typeᵉ `X`.ᵉ
-ᵉ Aᵉ [homotopy](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ squareᵉ
  ```text
        jᵉ
    Tᵉ ----->ᵉ Cᵉ
    |        |
    |        | iᵉ
    ∨ᵉ      ⌜ᵉ ∨ᵉ
    1 ----->ᵉ Xᵉ
        xᵉ
  ```
  [commutes](foundation.commuting-squares-of-maps.md),ᵉ andᵉ isᵉ aᵉ
  [pushout](synthetic-homotopy-theory.pushouts.md).ᵉ

Inᵉ otherᵉ words,ᵉ aᵉ tangentᵉ `n`-sphereᵉ atᵉ aᵉ pointᵉ `x`ᵉ consiststᵉ ofᵉ aᵉ mereᵉ sphereᵉ
andᵉ aᵉ complementᵉ suchᵉ thatᵉ theᵉ spaceᵉ `X`ᵉ canᵉ beᵉ reconstructedᵉ byᵉ attachingᵉ theᵉ
pointᵉ to theᵉ complementᵉ viaᵉ theᵉ inclusionᵉ ofᵉ theᵉ tangentᵉ sphereᵉ intoᵉ theᵉ
complement.ᵉ

## Definitions

### The predicate of having a tangent sphere

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ) {Xᵉ : UUᵉ lᵉ} (xᵉ : Xᵉ)
  where

  has-tangent-sphereᵉ : UUᵉ (lsuc lᵉ)
  has-tangent-sphereᵉ =
    Σᵉ ( mere-sphereᵉ lzero nᵉ)
      ( λ Tᵉ →
        Σᵉ ( UUᵉ lᵉ)
          ( λ Cᵉ →
            Σᵉ ( type-mere-sphereᵉ nᵉ Tᵉ → Cᵉ)
              ( λ jᵉ →
                Σᵉ ( Cᵉ → Xᵉ)
                  ( λ iᵉ →
                    Σᵉ ( coherence-square-mapsᵉ
                        ( jᵉ)
                        ( terminal-mapᵉ (type-mere-sphereᵉ nᵉ Tᵉ))
                        ( iᵉ)
                        ( pointᵉ xᵉ))
                      ( λ Hᵉ →
                        is-pushoutᵉ
                          ( terminal-mapᵉ (type-mere-sphereᵉ nᵉ Tᵉ))
                          ( jᵉ)
                          ( pointᵉ xᵉ ,ᵉ iᵉ ,ᵉ Hᵉ))))))

module _
  {lᵉ : Level} (nᵉ : ℕᵉ) {Xᵉ : UUᵉ lᵉ} {xᵉ : Xᵉ} (Tᵉ : has-tangent-sphereᵉ nᵉ xᵉ)
  where

  tangent-sphere-has-tangent-sphereᵉ : mere-sphereᵉ lzero nᵉ
  tangent-sphere-has-tangent-sphereᵉ = pr1ᵉ Tᵉ

  type-tangent-sphere-has-tangent-sphereᵉ : UUᵉ lzero
  type-tangent-sphere-has-tangent-sphereᵉ =
    type-mere-sphereᵉ nᵉ tangent-sphere-has-tangent-sphereᵉ

  mere-equiv-tangent-sphere-has-tangent-sphereᵉ :
    mere-equivᵉ (sphereᵉ nᵉ) type-tangent-sphere-has-tangent-sphereᵉ
  mere-equiv-tangent-sphere-has-tangent-sphereᵉ =
    mere-equiv-mere-sphereᵉ nᵉ tangent-sphere-has-tangent-sphereᵉ

  complement-has-tangent-sphereᵉ : UUᵉ lᵉ
  complement-has-tangent-sphereᵉ = pr1ᵉ (pr2ᵉ Tᵉ)

  inclusion-tangent-sphere-has-tangent-sphereᵉ :
    type-tangent-sphere-has-tangent-sphereᵉ → complement-has-tangent-sphereᵉ
  inclusion-tangent-sphere-has-tangent-sphereᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Tᵉ))

  inclusion-complement-has-tangent-sphereᵉ :
    complement-has-tangent-sphereᵉ → Xᵉ
  inclusion-complement-has-tangent-sphereᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Tᵉ)))

  coherence-square-has-tangent-sphereᵉ :
    coherence-square-mapsᵉ
      ( inclusion-tangent-sphere-has-tangent-sphereᵉ)
      ( terminal-mapᵉ type-tangent-sphere-has-tangent-sphereᵉ)
      ( inclusion-complement-has-tangent-sphereᵉ)
      ( pointᵉ xᵉ)
  coherence-square-has-tangent-sphereᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Tᵉ))))

  cocone-has-tangent-sphereᵉ :
    coconeᵉ
      ( terminal-mapᵉ type-tangent-sphere-has-tangent-sphereᵉ)
      ( inclusion-tangent-sphere-has-tangent-sphereᵉ)
      ( Xᵉ)
  pr1ᵉ cocone-has-tangent-sphereᵉ = pointᵉ xᵉ
  pr1ᵉ (pr2ᵉ cocone-has-tangent-sphereᵉ) = inclusion-complement-has-tangent-sphereᵉ
  pr2ᵉ (pr2ᵉ cocone-has-tangent-sphereᵉ) = coherence-square-has-tangent-sphereᵉ

  is-pushout-has-tangent-sphereᵉ :
    is-pushoutᵉ
      ( terminal-mapᵉ type-tangent-sphere-has-tangent-sphereᵉ)
      ( inclusion-tangent-sphere-has-tangent-sphereᵉ)
      ( cocone-has-tangent-sphereᵉ)
  is-pushout-has-tangent-sphereᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Tᵉ))))
```