# Contractible types

```agda
module foundation-core.contractible-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.implicit-function-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retracts-of-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Contractibleᵉ typesᵉ areᵉ typesᵉ thatᵉ have,ᵉ upᵉ to identification,ᵉ exactlyᵉ oneᵉ
element.ᵉ

## Definition

```agda
is-contrᵉ :
  {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-contrᵉ Aᵉ = Σᵉ Aᵉ (λ aᵉ → (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ)

abstract
  centerᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-contrᵉ Aᵉ → Aᵉ
  centerᵉ (pairᵉ cᵉ is-contr-Aᵉ) = cᵉ

eq-is-contr'ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-contrᵉ Aᵉ → (xᵉ yᵉ : Aᵉ) → xᵉ ＝ᵉ yᵉ
eq-is-contr'ᵉ (pairᵉ cᵉ Cᵉ) xᵉ yᵉ = (invᵉ (Cᵉ xᵉ)) ∙ᵉ (Cᵉ yᵉ)

eq-is-contrᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-contrᵉ Aᵉ → {xᵉ yᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ
eq-is-contrᵉ Cᵉ {xᵉ} {yᵉ} = eq-is-contr'ᵉ Cᵉ xᵉ yᵉ

abstract
  contractionᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (is-contr-Aᵉ : is-contrᵉ Aᵉ) →
    (xᵉ : Aᵉ) → (centerᵉ is-contr-Aᵉ) ＝ᵉ xᵉ
  contractionᵉ Cᵉ xᵉ = eq-is-contrᵉ Cᵉ

  coh-contractionᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (is-contr-Aᵉ : is-contrᵉ Aᵉ) →
    (contractionᵉ is-contr-Aᵉ (centerᵉ is-contr-Aᵉ)) ＝ᵉ reflᵉ
  coh-contractionᵉ (pairᵉ cᵉ Cᵉ) = left-invᵉ (Cᵉ cᵉ)
```

## Properties

### Retracts of contractible types are contractible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ)
  where

  abstract
    is-contr-retract-ofᵉ : Aᵉ retract-ofᵉ Bᵉ → is-contrᵉ Bᵉ → is-contrᵉ Aᵉ
    pr1ᵉ (is-contr-retract-ofᵉ (pairᵉ iᵉ (pairᵉ rᵉ is-retraction-rᵉ)) Hᵉ) = rᵉ (centerᵉ Hᵉ)
    pr2ᵉ (is-contr-retract-ofᵉ (pairᵉ iᵉ (pairᵉ rᵉ is-retraction-rᵉ)) Hᵉ) xᵉ =
      apᵉ rᵉ (contractionᵉ Hᵉ (iᵉ xᵉ)) ∙ᵉ (is-retraction-rᵉ xᵉ)
```

### Contractible types are closed under equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ)
  where

  abstract
    is-contr-is-equivᵉ :
      (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ → is-contrᵉ Bᵉ → is-contrᵉ Aᵉ
    is-contr-is-equivᵉ fᵉ is-equiv-fᵉ =
      is-contr-retract-ofᵉ Bᵉ (fᵉ ,ᵉ retraction-is-equivᵉ is-equiv-fᵉ)

  abstract
    is-contr-equivᵉ : (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-contrᵉ Bᵉ → is-contrᵉ Aᵉ
    is-contr-equivᵉ (pairᵉ eᵉ is-equiv-eᵉ) is-contr-Bᵉ =
      is-contr-is-equivᵉ eᵉ is-equiv-eᵉ is-contr-Bᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-contr-is-equiv'ᵉ :
      (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ → is-contrᵉ Aᵉ → is-contrᵉ Bᵉ
    is-contr-is-equiv'ᵉ fᵉ is-equiv-fᵉ is-contr-Aᵉ =
      is-contr-is-equivᵉ Aᵉ
        ( map-inv-is-equivᵉ is-equiv-fᵉ)
        ( is-equiv-map-inv-is-equivᵉ is-equiv-fᵉ)
        ( is-contr-Aᵉ)

  abstract
    is-contr-equiv'ᵉ : (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-contrᵉ Aᵉ → is-contrᵉ Bᵉ
    is-contr-equiv'ᵉ (pairᵉ eᵉ is-equiv-eᵉ) is-contr-Aᵉ =
      is-contr-is-equiv'ᵉ eᵉ is-equiv-eᵉ is-contr-Aᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-equiv-is-contrᵉ :
      (fᵉ : Aᵉ → Bᵉ) → is-contrᵉ Aᵉ → is-contrᵉ Bᵉ → is-equivᵉ fᵉ
    is-equiv-is-contrᵉ fᵉ is-contr-Aᵉ is-contr-Bᵉ =
      is-equiv-is-invertibleᵉ
        ( λ yᵉ → centerᵉ is-contr-Aᵉ)
        ( λ yᵉ → eq-is-contrᵉ is-contr-Bᵉ)
        ( contractionᵉ is-contr-Aᵉ)

  equiv-is-contrᵉ : is-contrᵉ Aᵉ → is-contrᵉ Bᵉ → Aᵉ ≃ᵉ Bᵉ
  pr1ᵉ (equiv-is-contrᵉ is-contr-Aᵉ is-contr-Bᵉ) aᵉ = centerᵉ is-contr-Bᵉ
  pr2ᵉ (equiv-is-contrᵉ is-contr-Aᵉ is-contr-Bᵉ) =
    is-equiv-is-contrᵉ _ is-contr-Aᵉ is-contr-Bᵉ
```

### Contractibility of cartesian product types

Givenᵉ twoᵉ typesᵉ `A`ᵉ andᵉ `B`,ᵉ theᵉ followingᵉ areᵉ equivalentᵉ:

1.ᵉ Theᵉ typeᵉ `Aᵉ ×ᵉ B`ᵉ isᵉ contractible.ᵉ
2.ᵉ Bothᵉ `A`ᵉ andᵉ `B`ᵉ areᵉ contractible.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  abstract
    is-contr-left-factor-productᵉ : is-contrᵉ (Aᵉ ×ᵉ Bᵉ) → is-contrᵉ Aᵉ
    is-contr-left-factor-productᵉ is-contr-ABᵉ =
      is-contr-retract-ofᵉ
        ( Aᵉ ×ᵉ Bᵉ)
        ( pairᵉ
          ( λ xᵉ → pairᵉ xᵉ (pr2ᵉ (centerᵉ is-contr-ABᵉ)))
          ( pairᵉ pr1ᵉ refl-htpyᵉ))
        ( is-contr-ABᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  abstract
    is-contr-right-factor-productᵉ : is-contrᵉ (Aᵉ ×ᵉ Bᵉ) → is-contrᵉ Bᵉ
    is-contr-right-factor-productᵉ is-contr-ABᵉ =
      is-contr-retract-ofᵉ
        ( Aᵉ ×ᵉ Bᵉ)
        ( pairᵉ
          ( pairᵉ (pr1ᵉ (centerᵉ is-contr-ABᵉ)))
          ( pairᵉ pr2ᵉ refl-htpyᵉ))
        ( is-contr-ABᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-contr-productᵉ : is-contrᵉ Aᵉ → is-contrᵉ Bᵉ → is-contrᵉ (Aᵉ ×ᵉ Bᵉ)
    pr1ᵉ (pr1ᵉ (is-contr-productᵉ (pairᵉ aᵉ Cᵉ) (pairᵉ bᵉ Dᵉ))) = aᵉ
    pr2ᵉ (pr1ᵉ (is-contr-productᵉ (pairᵉ aᵉ Cᵉ) (pairᵉ bᵉ Dᵉ))) = bᵉ
    pr2ᵉ (is-contr-productᵉ (pairᵉ aᵉ Cᵉ) (pairᵉ bᵉ Dᵉ)) (pairᵉ xᵉ yᵉ) =
      eq-pairᵉ (Cᵉ xᵉ) (Dᵉ yᵉ)
```

### Contractibility of Σ-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  abstract
    is-contr-Σ'ᵉ :
      is-contrᵉ Aᵉ → ((xᵉ : Aᵉ) → is-contrᵉ (Bᵉ xᵉ)) → is-contrᵉ (Σᵉ Aᵉ Bᵉ)
    pr1ᵉ (pr1ᵉ (is-contr-Σ'ᵉ (pairᵉ aᵉ Hᵉ) is-contr-Bᵉ)) = aᵉ
    pr2ᵉ (pr1ᵉ (is-contr-Σ'ᵉ (pairᵉ aᵉ Hᵉ) is-contr-Bᵉ)) = centerᵉ (is-contr-Bᵉ aᵉ)
    pr2ᵉ (is-contr-Σ'ᵉ (pairᵉ aᵉ Hᵉ) is-contr-Bᵉ) (pairᵉ xᵉ yᵉ) =
      eq-pair-Σᵉ
        ( invᵉ (invᵉ (Hᵉ xᵉ)))
        ( eq-transpose-trᵉ (invᵉ (Hᵉ xᵉ)) (eq-is-contrᵉ (is-contr-Bᵉ aᵉ)))

  abstract
    is-contr-Σᵉ :
      is-contrᵉ Aᵉ → (aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ) → is-contrᵉ (Σᵉ Aᵉ Bᵉ)
    pr1ᵉ (pr1ᵉ (is-contr-Σᵉ Hᵉ aᵉ Kᵉ)) = aᵉ
    pr2ᵉ (pr1ᵉ (is-contr-Σᵉ Hᵉ aᵉ Kᵉ)) = centerᵉ Kᵉ
    pr2ᵉ (is-contr-Σᵉ Hᵉ aᵉ Kᵉ) (pairᵉ xᵉ yᵉ) =
      eq-pair-Σᵉ
        ( invᵉ (eq-is-contrᵉ Hᵉ))
        ( eq-transpose-trᵉ (eq-is-contrᵉ Hᵉ) (eq-is-contrᵉ Kᵉ))
```

**Note**ᵉ: Inᵉ theᵉ previousᵉ construction,ᵉ weᵉ showedᵉ thatᵉ `Σᵉ Aᵉ B`ᵉ isᵉ contractibleᵉ
wheneverᵉ `A`ᵉ isᵉ contractibleᵉ andᵉ wheneverᵉ `Bᵉ a`ᵉ isᵉ contractibleᵉ forᵉ aᵉ specifiedᵉ
termᵉ `aᵉ : A`.ᵉ Weᵉ _couldᵉ_ haveᵉ chosenᵉ thisᵉ termᵉ `a`ᵉ to beᵉ theᵉ centerᵉ ofᵉ
contractionᵉ ofᵉ `A`.ᵉ However,ᵉ itᵉ turnsᵉ outᵉ to beᵉ betterᵉ notᵉ to do soᵉ in theᵉ
constructionᵉ ofᵉ `is-contr-Σ`.ᵉ Theᵉ reasonᵉ isᵉ thatᵉ proofsᵉ ofᵉ contractibilityᵉ couldᵉ
beᵉ quiteᵉ complicatedᵉ andᵉ difficultᵉ to normalize.ᵉ Ifᵉ weᵉ wouldᵉ requireᵉ in theᵉ
definitionᵉ ofᵉ `is-contr-Σ`ᵉ thatᵉ `Bᵉ (centerᵉ c)`ᵉ isᵉ contractible,ᵉ givenᵉ theᵉ proofᵉ
`c`ᵉ ofᵉ contractibilityᵉ ofᵉ `A`,ᵉ thenᵉ theᵉ typeᵉ inferenceᵉ algorithmᵉ ofᵉ Agdaᵉ willᵉ beᵉ
forcedᵉ to normalizeᵉ theᵉ proofᵉ `c`ᵉ includingᵉ theᵉ contraction.ᵉ Byᵉ insteadᵉ
providingᵉ aᵉ centerᵉ ofᵉ contractionᵉ byᵉ hand,ᵉ weᵉ avoidᵉ thisᵉ unnecessaryᵉ loadᵉ onᵉ theᵉ
typeᵉ inferenceᵉ algorithm,ᵉ andᵉ henceᵉ anyᵉ instance ofᵉ `is-contr-Σ`ᵉ willᵉ typeᵉ checkᵉ
moreᵉ efficiently.ᵉ

Theᵉ generalᵉ themeᵉ isᵉ thatᵉ itᵉ mayᵉ beᵉ computationallyᵉ expensiveᵉ to extractᵉ
informationᵉ fromᵉ proofsᵉ ofᵉ propositions,ᵉ suchᵉ asᵉ theᵉ centerᵉ ofᵉ contractionᵉ ofᵉ aᵉ
proofᵉ ofᵉ contractibility.ᵉ Theᵉ reasonᵉ forᵉ thatᵉ isᵉ thatᵉ whenᵉ Agdaᵉ normalizesᵉ anᵉ
elementᵉ (asᵉ itᵉ inevitablyᵉ willᵉ do sometimesᵉ) thenᵉ in suchᵉ casesᵉ itᵉ willᵉ notᵉ justᵉ
normalizeᵉ theᵉ extractedᵉ informationᵉ (inᵉ thisᵉ caseᵉ theᵉ firstᵉ projectionᵉ ofᵉ theᵉ
proofᵉ ofᵉ contractibility),ᵉ butᵉ itᵉ willᵉ normalizeᵉ theᵉ entireᵉ proofᵉ ofᵉ
contractibilityᵉ first,ᵉ andᵉ thenᵉ applyᵉ theᵉ projection.ᵉ

### Contractible types are propositions

```agda
is-prop-is-contrᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-contrᵉ Aᵉ → (xᵉ yᵉ : Aᵉ) → is-contrᵉ (xᵉ ＝ᵉ yᵉ)
pr1ᵉ (is-prop-is-contrᵉ Hᵉ xᵉ yᵉ) = eq-is-contrᵉ Hᵉ
pr2ᵉ (is-prop-is-contrᵉ Hᵉ xᵉ .xᵉ) reflᵉ = left-invᵉ (pr2ᵉ Hᵉ xᵉ)
```

### Products of families of contractible types are contractible

```agda
abstract
  is-contr-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → is-contrᵉ (Bᵉ xᵉ)) → is-contrᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
  pr1ᵉ (is-contr-Πᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} Hᵉ) xᵉ = centerᵉ (Hᵉ xᵉ)
  pr2ᵉ (is-contr-Πᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} Hᵉ) fᵉ =
    eq-htpyᵉ (λ xᵉ → contractionᵉ (Hᵉ xᵉ) (fᵉ xᵉ))

abstract
  is-contr-implicit-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → is-contrᵉ (Bᵉ xᵉ)) → is-contrᵉ ({xᵉ : Aᵉ} → Bᵉ xᵉ)
  is-contr-implicit-Πᵉ Hᵉ =
    is-contr-equivᵉ _ equiv-explicit-implicit-Πᵉ (is-contr-Πᵉ Hᵉ)
```

### The type of functions into a contractible type is contractible

```agda
is-contr-function-typeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-contrᵉ Bᵉ → is-contrᵉ (Aᵉ → Bᵉ)
is-contr-function-typeᵉ is-contr-Bᵉ = is-contr-Πᵉ (λ _ → is-contr-Bᵉ)
```

### The type of equivalences between contractible types is contractible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-contr-equiv-is-contrᵉ :
    is-contrᵉ Aᵉ → is-contrᵉ Bᵉ → is-contrᵉ (Aᵉ ≃ᵉ Bᵉ)
  is-contr-equiv-is-contrᵉ (pairᵉ aᵉ αᵉ) (pairᵉ bᵉ βᵉ) =
    is-contr-Σᵉ
      ( is-contr-function-typeᵉ (pairᵉ bᵉ βᵉ))
      ( λ xᵉ → bᵉ)
      ( is-contr-productᵉ
        ( is-contr-Σᵉ
          ( is-contr-function-typeᵉ (pairᵉ aᵉ αᵉ))
          ( λ yᵉ → aᵉ)
          ( is-contr-Πᵉ (is-prop-is-contrᵉ (pairᵉ bᵉ βᵉ) bᵉ)))
        ( is-contr-Σᵉ
          ( is-contr-function-typeᵉ (pairᵉ aᵉ αᵉ))
          ( λ yᵉ → aᵉ)
          ( is-contr-Πᵉ (is-prop-is-contrᵉ (pairᵉ aᵉ αᵉ) aᵉ))))
```

### Being contractible is a proposition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-contr-is-contrᵉ : is-contrᵉ Aᵉ → is-contrᵉ (is-contrᵉ Aᵉ)
    is-contr-is-contrᵉ (pairᵉ aᵉ αᵉ) =
      is-contr-Σᵉ
        ( pairᵉ aᵉ αᵉ)
        ( aᵉ)
        ( is-contr-Πᵉ (is-prop-is-contrᵉ (pairᵉ aᵉ αᵉ) aᵉ))

  abstract
    is-property-is-contrᵉ : (Hᵉ Kᵉ : is-contrᵉ Aᵉ) → is-contrᵉ (Hᵉ ＝ᵉ Kᵉ)
    is-property-is-contrᵉ Hᵉ = is-prop-is-contrᵉ (is-contr-is-contrᵉ Hᵉ) Hᵉ
```