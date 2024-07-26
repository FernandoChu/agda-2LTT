# Alcohols

```agda
module organic-chemistry.alcoholsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import organic-chemistry.hydrocarbonsᵉ
open import organic-chemistry.saturated-carbonsᵉ
```

</details>

## Idea

Anᵉ alcoholᵉ isᵉ aᵉ hydrocarbonᵉ with atᵉ leastᵉ oneᵉ `-OH`ᵉ group.ᵉ Theᵉ typeᵉ ofᵉ alcoholsᵉ
canᵉ thereforeᵉ beᵉ definedᵉ asᵉ theᵉ typeᵉ ofᵉ hydrocarbonsᵉ equippedᵉ with aᵉ
distinguishedᵉ subsetᵉ ofᵉ theᵉ availableᵉ (unbondedᵉ) electronsᵉ ofᵉ theᵉ carbonᵉ atoms.ᵉ

## Definition

```agda
alcoholᵉ : UUᵉ (lsuc lzero)
alcoholᵉ =
  Σᵉ ( hydrocarbonᵉ lzero lzero)
    ( λ Xᵉ →
      Σᵉ ( (cᵉ : vertex-hydrocarbonᵉ Xᵉ) →
          decidable-subtypeᵉ lzero (electron-carbon-atom-hydrocarbonᵉ Xᵉ cᵉ))
        ( λ OHᵉ →
          ( ( cᵉ c'ᵉ : vertex-hydrocarbonᵉ Xᵉ) →
            ( bᵉ : edge-hydrocarbonᵉ Xᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ)) →
            ¬ᵉ (is-in-decidable-subtypeᵉ (OHᵉ cᵉ) (bonding-hydrocarbonᵉ Xᵉ bᵉ))) ×ᵉ
          ( ( type-trunc-Propᵉ
            ( Σᵉ ( vertex-hydrocarbonᵉ Xᵉ)
                ( λ cᵉ → type-decidable-subtypeᵉ (OHᵉ cᵉ)))) ×ᵉ
            ( ( cᵉ : vertex-hydrocarbonᵉ Xᵉ) →
              type-decidable-subtypeᵉ (OHᵉ cᵉ) →
              is-saturated-carbon-hydrocarbonᵉ Xᵉ cᵉ
              ))))
```

Moreᵉ explicitly,ᵉ anᵉ alcoholᵉ isᵉ aᵉ hydrocarbonᵉ equippedᵉ with,ᵉ forᵉ eachᵉ ofᵉ itsᵉ
carbons,ᵉ aᵉ subsetᵉ ofᵉ itsᵉ electrons,ᵉ where membershipᵉ in thatᵉ subsetᵉ indicatesᵉ
whetherᵉ orᵉ notᵉ aᵉ hydroxylᵉ groupᵉ isᵉ bondedᵉ to thatᵉ specificᵉ electron.ᵉ Weᵉ requireᵉ
theᵉ followingᵉ conditionsᵉ:

-ᵉ Theᵉ electronᵉ sharedᵉ betweenᵉ aᵉ carbonᵉ atomᵉ andᵉ aᵉ hydroxylᵉ groupᵉ canᵉ notᵉ alsoᵉ beᵉ
  sharedᵉ betweenᵉ thatᵉ carbonᵉ atomᵉ andᵉ aᵉ differentᵉ carbon.ᵉ
-ᵉ Thereᵉ mustᵉ beᵉ atᵉ leastᵉ oneᵉ hydroxylᵉ group.ᵉ
-ᵉ Atomsᵉ to whichᵉ hydroxylᵉ groupsᵉ areᵉ bondedᵉ mustᵉ beᵉ saturated.ᵉ