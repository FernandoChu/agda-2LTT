# Descent data for type families of identity types over pushouts

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module synthetic-homotopy-theory.descent-data-identity-types-over-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.span-diagramsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.equivalences-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.families-descent-data-pushoutsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [cocone](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) underᵉ aᵉ
[spanᵉ diagram](foundation.span-diagrams.mdᵉ)

```text
        gᵉ
    Sᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |        | jᵉ
    ∨ᵉ        ∨ᵉ
    Aᵉ ----->ᵉ Xᵉ
        iᵉ
```

andᵉ aᵉ pointᵉ `x₀ᵉ : X`,ᵉ theᵉ typeᵉ familyᵉ ofᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) basedᵉ atᵉ `x₀`,ᵉ
`xᵉ ↦ᵉ (x₀ᵉ = x)`,ᵉ isᵉ
[characterized](synthetic-homotopy-theory.families-descent-data-pushouts.mdᵉ) byᵉ
theᵉ [descentᵉ data](synthetic-homotopy-theory.descent-data-pushouts.mdᵉ)
`(IA,ᵉ IB,ᵉ IS)`,ᵉ where `IA`ᵉ andᵉ `IB`ᵉ areᵉ familiesᵉ ofᵉ identityᵉ typesᵉ

```text
  IAᵉ aᵉ :=ᵉ (x₀ᵉ = iaᵉ)
  IBᵉ bᵉ :=ᵉ (x₀ᵉ = jb),ᵉ
```

andᵉ theᵉ gluingᵉ data `ISᵉ sᵉ : (x₀ᵉ = ifsᵉ) ≃ᵉ (x₀ᵉ = jgs)`ᵉ isᵉ givenᵉ byᵉ concatenationᵉ
with theᵉ coherenceᵉ ofᵉ theᵉ coconeᵉ `Hᵉ sᵉ : ifsᵉ = jgs`.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ)
  (x₀ᵉ : Xᵉ)
  where

  family-cocone-identity-type-pushoutᵉ : Xᵉ → UUᵉ l4ᵉ
  family-cocone-identity-type-pushoutᵉ xᵉ = x₀ᵉ ＝ᵉ xᵉ

  descent-data-identity-type-pushoutᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ
  pr1ᵉ descent-data-identity-type-pushoutᵉ aᵉ =
    x₀ᵉ ＝ᵉ horizontal-map-coconeᵉ _ _ cᵉ aᵉ
  pr1ᵉ (pr2ᵉ descent-data-identity-type-pushoutᵉ) bᵉ =
    x₀ᵉ ＝ᵉ vertical-map-coconeᵉ _ _ cᵉ bᵉ
  pr2ᵉ (pr2ᵉ descent-data-identity-type-pushoutᵉ) sᵉ =
    equiv-concat'ᵉ x₀ᵉ (coherence-square-coconeᵉ _ _ cᵉ sᵉ)

  equiv-descent-data-identity-type-pushoutᵉ :
    equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-identity-type-pushoutᵉ))
      ( descent-data-identity-type-pushoutᵉ)
  pr1ᵉ equiv-descent-data-identity-type-pushoutᵉ aᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ equiv-descent-data-identity-type-pushoutᵉ) bᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ equiv-descent-data-identity-type-pushoutᵉ) sᵉ =
    tr-Id-rightᵉ (coherence-square-coconeᵉ _ _ cᵉ sᵉ)

  family-with-descent-data-identity-type-pushoutᵉ :
    family-with-descent-data-pushoutᵉ cᵉ l4ᵉ
  pr1ᵉ family-with-descent-data-identity-type-pushoutᵉ =
    family-cocone-identity-type-pushoutᵉ
  pr1ᵉ (pr2ᵉ family-with-descent-data-identity-type-pushoutᵉ) =
    descent-data-identity-type-pushoutᵉ
  pr2ᵉ (pr2ᵉ family-with-descent-data-identity-type-pushoutᵉ) =
    equiv-descent-data-identity-type-pushoutᵉ
```