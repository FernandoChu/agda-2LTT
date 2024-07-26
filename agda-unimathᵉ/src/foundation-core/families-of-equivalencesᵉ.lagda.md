# Families of equivalences

```agda
module foundation-core.families-of-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Aᵉ **familyᵉ ofᵉ equivalences**ᵉ isᵉ aᵉ familyᵉ

```text
  eᵢᵉ : Aᵉ iᵉ ≃ᵉ Bᵉ iᵉ
```

ofᵉ [equivalences](foundation-core.equivalences.md).ᵉ Familiesᵉ ofᵉ equivalencesᵉ areᵉ
alsoᵉ calledᵉ **fiberwiseᵉ equivalences**.ᵉ

## Definitions

### The predicate of being a fiberwise equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  is-fiberwise-equivᵉ : (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-fiberwise-equivᵉ fᵉ = (xᵉ : Aᵉ) → is-equivᵉ (fᵉ xᵉ)
```

### Fiberwise equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  fiberwise-equivᵉ : (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  fiberwise-equivᵉ Bᵉ Cᵉ = Σᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ) is-fiberwise-equivᵉ

  map-fiberwise-equivᵉ :
    {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} →
    fiberwise-equivᵉ Bᵉ Cᵉ → (aᵉ : Aᵉ) → Bᵉ aᵉ → Cᵉ aᵉ
  map-fiberwise-equivᵉ = pr1ᵉ

  is-fiberwise-equiv-fiberwise-equivᵉ :
    {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} →
    (eᵉ : fiberwise-equivᵉ Bᵉ Cᵉ) →
    is-fiberwise-equivᵉ (map-fiberwise-equivᵉ eᵉ)
  is-fiberwise-equiv-fiberwise-equivᵉ = pr2ᵉ
```

### Families of equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  fam-equivᵉ : (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  fam-equivᵉ Bᵉ Cᵉ = (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Cᵉ xᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (eᵉ : fam-equivᵉ Bᵉ Cᵉ)
  where

  map-fam-equivᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ
  map-fam-equivᵉ xᵉ = map-equivᵉ (eᵉ xᵉ)

  is-equiv-map-fam-equivᵉ : is-fiberwise-equivᵉ map-fam-equivᵉ
  is-equiv-map-fam-equivᵉ xᵉ = is-equiv-map-equivᵉ (eᵉ xᵉ)
```

## Properties

### Families of equivalences are equivalent to fiberwise equivalences

```agda
equiv-fiberwise-equiv-fam-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ) →
  fam-equivᵉ Bᵉ Cᵉ ≃ᵉ fiberwise-equivᵉ Bᵉ Cᵉ
equiv-fiberwise-equiv-fam-equivᵉ Bᵉ Cᵉ = distributive-Π-Σᵉ
```

## See also

-ᵉ Inᵉ
  [Functorialityᵉ ofᵉ dependentᵉ pairᵉ types](foundation-core.functoriality-dependent-pair-types.mdᵉ)
  weᵉ showᵉ thatᵉ aᵉ familyᵉ ofᵉ mapsᵉ isᵉ aᵉ fiberwiseᵉ equivalenceᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ
  inducesᵉ anᵉ equivalenceᵉ onᵉ [totalᵉ spaces](foundation.dependent-pair-types.md).ᵉ