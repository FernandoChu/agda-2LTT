# Saturated carbons

```agda
module organic-chemistry.saturated-carbonsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import organic-chemistry.hydrocarbonsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Anᵉ importantᵉ distinguishingᵉ propertyᵉ ofᵉ organicᵉ compoundsᵉ isᵉ theᵉ presenceᵉ ofᵉ
doubleᵉ orᵉ tripleᵉ carbon-carbonᵉ bonds,ᵉ i.e.,ᵉ theᵉ presenceᵉ orᵉ absenceᵉ ofᵉ
_unsaturatedᵉ carbons_.ᵉ Inᵉ thisᵉ module weᵉ defineᵉ whatᵉ itᵉ meansᵉ forᵉ aᵉ carbonᵉ atomᵉ
to beᵉ saturated,ᵉ andᵉ whatᵉ itᵉ meansᵉ forᵉ carbonᵉ atomsᵉ to haveᵉ doubleᵉ andᵉ tripleᵉ
bonds.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Hᵉ : hydrocarbonᵉ l1ᵉ l2ᵉ)
  where
  is-saturated-carbon-hydrocarbonᵉ : vertex-hydrocarbonᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-saturated-carbon-hydrocarbonᵉ cᵉ =
      (c'ᵉ : vertex-hydrocarbonᵉ Hᵉ) →
      is-propᵉ (edge-hydrocarbonᵉ Hᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ))
```

Type-theoretically,ᵉ theᵉ saturationᵉ conditionᵉ onᵉ aᵉ carbonᵉ atomᵉ (fixᵉ oneᵉ andᵉ callᵉ
itᵉ `c`ᵉ) isᵉ incarnatedᵉ byᵉ askingᵉ that,ᵉ forᵉ everyᵉ otherᵉ carbonᵉ atomᵉ `c'`,ᵉ theᵉ typeᵉ
ofᵉ edgesᵉ `cᵉ ---ᵉ c'`ᵉ isᵉ aᵉ proposition.ᵉ Sinceᵉ edgesᵉ incidentᵉ onᵉ `c`ᵉ areᵉ aᵉ subtypeᵉ
ofᵉ theᵉ typeᵉ representingᵉ electronsᵉ ofᵉ `c`,ᵉ thisᵉ guaranteesᵉ thatᵉ `c`ᵉ sharesᵉ noᵉ
moreᵉ thanᵉ 1 electronᵉ with anyᵉ otherᵉ carbonᵉ in theᵉ structure.ᵉ Anᵉ **alkane**ᵉ isᵉ aᵉ
hydrocarbonᵉ suchᵉ thatᵉ everyᵉ carbonᵉ isᵉ saturated.ᵉ

```agda
  double-bond-on-hydrocarbonᵉ : vertex-hydrocarbonᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  double-bond-on-hydrocarbonᵉ cᵉ = Σᵉ (vertex-hydrocarbonᵉ Hᵉ) λ c'ᵉ →
    has-cardinalityᵉ 2 (edge-hydrocarbonᵉ Hᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ))

  has-double-bond-hydrocarbonᵉ : vertex-hydrocarbonᵉ Hᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  has-double-bond-hydrocarbonᵉ cᵉ = trunc-Propᵉ (double-bond-on-hydrocarbonᵉ cᵉ)

  has-triple-bond-hydrocarbonᵉ : vertex-hydrocarbonᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-triple-bond-hydrocarbonᵉ cᵉ = Σᵉ (vertex-hydrocarbonᵉ Hᵉ) λ c'ᵉ →
    has-cardinalityᵉ 3 (edge-hydrocarbonᵉ Hᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ))
```

Forᵉ aᵉ carbonᵉ atomᵉ `c`ᵉ to haveᵉ aᵉ doubleᵉ (respectively,ᵉ aᵉ tripleᵉ) bond,ᵉ weᵉ mustᵉ
findᵉ anotherᵉ carbonᵉ `c'`ᵉ suchᵉ thatᵉ theᵉ typeᵉ ofᵉ edgesᵉ `cᵉ ---ᵉ c'`ᵉ hasᵉ cardinalityᵉ
2 (respectively,ᵉ 3).ᵉ Ifᵉ allᵉ weᵉ careᵉ aboutᵉ isᵉ thatᵉ theᵉ carbonᵉ atomᵉ hasᵉ _someᵉ_
doubleᵉ bond,ᵉ weᵉ useᵉ theᵉ truncatedᵉ version.ᵉ Weᵉ noteᵉ that,ᵉ sinceᵉ in theᵉ graphᵉ
representationᵉ ofᵉ hydrocarbons,ᵉ verticesᵉ canᵉ haveᵉ atᵉ mostᵉ threeᵉ incidentᵉ edges,ᵉ
ifᵉ aᵉ carbonᵉ atomᵉ canᵉ haveᵉ atᵉ mostᵉ oneᵉ tripleᵉ bond.ᵉ