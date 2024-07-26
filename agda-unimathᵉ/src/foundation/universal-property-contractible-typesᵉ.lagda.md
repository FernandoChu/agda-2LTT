# Universal property of contractible types

```agda
module foundation.universal-property-contractible-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.singleton-inductionᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "dependentᵉ universalᵉ propertyᵉ ofᵉ [contractibleᵉ types](foundation-core.contractible-types.md)"ᵉ Agda=dependent-universal-property-contrᵉ}}
statesᵉ that,ᵉ givenᵉ aᵉ pointᵉ `aᵉ : A`,ᵉ theᵉ evaluatingᵉ mapᵉ

```text
  ev-pointᵉ aᵉ Pᵉ : ((xᵉ : Aᵉ) → Pᵉ xᵉ) → Pᵉ aᵉ
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) forᵉ everyᵉ typeᵉ familyᵉ
`Pᵉ : Aᵉ → 𝒰`.ᵉ

Theᵉ conditionᵉ thatᵉ `ev-point`ᵉ hasᵉ aᵉ [section](foundation-core.sections.mdᵉ)

```text
  Pᵉ aᵉ → ((xᵉ : Aᵉ) → Pᵉ xᵉ)
```

isᵉ anotherᵉ wayᵉ ofᵉ phrasingᵉ thatᵉ theᵉ typeᵉ satisfiesᵉ
[singletonᵉ induction](foundation.singleton-induction.md).ᵉ Furthermore,ᵉ theᵉ
conditionᵉ thatᵉ `ev-point`ᵉ hasᵉ aᵉ [retraction](foundation-core.retractions.mdᵉ)
assertsᵉ thatᵉ allᵉ dependentᵉ functionsᵉ `(xᵉ : Aᵉ) → Pᵉ x`ᵉ areᵉ fullyᵉ determinedᵉ byᵉ
theirᵉ valueᵉ atᵉ `a`,ᵉ thus,ᵉ in particular,ᵉ thatᵉ theᵉ sectionᵉ ofᵉ `ev-point`ᵉ isᵉ
unique.ᵉ

## Definitions

### The dependent universal property of contractible types

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  dependent-universal-property-contrᵉ : UUωᵉ
  dependent-universal-property-contrᵉ =
    {lᵉ : Level} (Pᵉ : Aᵉ → UUᵉ lᵉ) → is-equivᵉ (ev-pointᵉ aᵉ {Pᵉ})
```

### The universal property of contractible types

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  universal-property-contrᵉ : UUωᵉ
  universal-property-contrᵉ = {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (ev-point'ᵉ aᵉ {Xᵉ})
```

## Properties

### The universal property of contractible types follows from the dependent universal property

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  universal-property-dependent-universal-property-contrᵉ :
    dependent-universal-property-contrᵉ aᵉ → universal-property-contrᵉ aᵉ
  universal-property-dependent-universal-property-contrᵉ dup-contrᵉ {lᵉ} Xᵉ =
    dup-contrᵉ (λ _ → Xᵉ)
```

### Types satisfying the universal property of contractible types are contractible

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  abstract
    is-contr-is-equiv-ev-pointᵉ :
      is-equivᵉ (ev-point'ᵉ aᵉ {Aᵉ}) → is-contrᵉ Aᵉ
    pr1ᵉ (is-contr-is-equiv-ev-pointᵉ Hᵉ) = aᵉ
    pr2ᵉ (is-contr-is-equiv-ev-pointᵉ Hᵉ) =
      htpy-eqᵉ
        ( apᵉ
          ( pr1ᵉ)
          ( eq-is-contr'ᵉ
            ( is-contr-map-is-equivᵉ Hᵉ aᵉ)
            ( (λ _ → aᵉ) ,ᵉ reflᵉ)
            ( idᵉ ,ᵉ reflᵉ)))

  abstract
    is-contr-universal-property-contrᵉ :
      universal-property-contrᵉ aᵉ → is-contrᵉ Aᵉ
    is-contr-universal-property-contrᵉ up-contrᵉ =
      is-contr-is-equiv-ev-pointᵉ (up-contrᵉ Aᵉ)
```

### Types satisfying the dependent universal property of contractible types are contractible

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  abstract
    is-contr-dependent-universal-property-contrᵉ :
      dependent-universal-property-contrᵉ aᵉ → is-contrᵉ Aᵉ
    is-contr-dependent-universal-property-contrᵉ dup-contrᵉ =
      is-contr-universal-property-contrᵉ aᵉ
        ( universal-property-dependent-universal-property-contrᵉ aᵉ dup-contrᵉ)
```

### Types that are contractible satisfy the dependent universal property

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  abstract
    dependent-universal-property-contr-is-contrᵉ :
      is-contrᵉ Aᵉ → dependent-universal-property-contrᵉ aᵉ
    dependent-universal-property-contr-is-contrᵉ Hᵉ Pᵉ =
      is-equiv-is-invertibleᵉ
        ( ind-singletonᵉ aᵉ Hᵉ Pᵉ)
        ( compute-ind-singletonᵉ aᵉ Hᵉ Pᵉ)
        ( λ fᵉ →
          eq-htpyᵉ
            ( ind-singletonᵉ aᵉ Hᵉ
              ( λ xᵉ → ind-singletonᵉ aᵉ Hᵉ Pᵉ (fᵉ aᵉ) xᵉ ＝ᵉ fᵉ xᵉ)
              ( compute-ind-singletonᵉ aᵉ Hᵉ Pᵉ (fᵉ aᵉ))))

  equiv-dependent-universal-property-contrᵉ :
    is-contrᵉ Aᵉ → {lᵉ : Level} (Bᵉ : Aᵉ → UUᵉ lᵉ) → ((xᵉ : Aᵉ) → Bᵉ xᵉ) ≃ᵉ Bᵉ aᵉ
  pr1ᵉ (equiv-dependent-universal-property-contrᵉ Hᵉ Pᵉ) = ev-pointᵉ aᵉ
  pr2ᵉ (equiv-dependent-universal-property-contrᵉ Hᵉ Pᵉ) =
    dependent-universal-property-contr-is-contrᵉ Hᵉ Pᵉ

  apply-dependent-universal-property-contrᵉ :
    is-contrᵉ Aᵉ → {lᵉ : Level} (Bᵉ : Aᵉ → UUᵉ lᵉ) → (Bᵉ aᵉ → ((xᵉ : Aᵉ) → Bᵉ xᵉ))
  apply-dependent-universal-property-contrᵉ Hᵉ Pᵉ =
    map-inv-equivᵉ (equiv-dependent-universal-property-contrᵉ Hᵉ Pᵉ)
```

### Types that are contractible satisfy the universal property

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  abstract
    universal-property-contr-is-contrᵉ :
      is-contrᵉ Aᵉ → universal-property-contrᵉ aᵉ
    universal-property-contr-is-contrᵉ Hᵉ =
      universal-property-dependent-universal-property-contrᵉ aᵉ
        ( dependent-universal-property-contr-is-contrᵉ aᵉ Hᵉ)

  equiv-universal-property-contrᵉ :
    is-contrᵉ Aᵉ → {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → (Aᵉ → Xᵉ) ≃ᵉ Xᵉ
  pr1ᵉ (equiv-universal-property-contrᵉ Hᵉ Xᵉ) = ev-point'ᵉ aᵉ
  pr2ᵉ (equiv-universal-property-contrᵉ Hᵉ Xᵉ) =
    universal-property-contr-is-contrᵉ Hᵉ Xᵉ

  apply-universal-property-contrᵉ :
    is-contrᵉ Aᵉ → {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → Xᵉ → (Aᵉ → Xᵉ)
  apply-universal-property-contrᵉ Hᵉ Xᵉ =
    map-inv-equivᵉ (equiv-universal-property-contrᵉ Hᵉ Xᵉ)
```

## See also

-ᵉ [Singletonᵉ induction](foundation.singleton-induction.mdᵉ)
-ᵉ [Universalᵉ propertyᵉ ofᵉ contractibleᵉ typesᵉ with respectᵉ to pointedᵉ typesᵉ andᵉ maps](structured-types.pointed-universal-property-contractible-types.mdᵉ)