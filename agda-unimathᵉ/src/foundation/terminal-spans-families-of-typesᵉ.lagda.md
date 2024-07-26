# Terminal spans on families of types

```agda
module foundation.terminal-spans-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.morphisms-spans-families-of-typesᵉ
open import foundation.spans-families-of-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [span](foundation.spans-families-of-types.mdᵉ) `𝒮`ᵉ onᵉ aᵉ familyᵉ ofᵉ typesᵉ
`Aᵉ : Iᵉ → 𝒰`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "terminal"ᵉ Disambiguation="spanᵉ onᵉ aᵉ familyᵉ ofᵉ types"ᵉ Agda=is-terminal-span-type-familyᵉ}}
ifᵉ forᵉ eachᵉ spanᵉ `𝒯`ᵉ onᵉ `A`ᵉ theᵉ typeᵉ ofᵉ
[morphismsᵉ ofᵉ spans](foundation.morphisms-spans-families-of-types.mdᵉ) `𝒯ᵉ → 𝒮`ᵉ isᵉ
[contractible](foundation-core.contractible-types.md).ᵉ

## Definitions

### The predicate of being a terminal span on a family of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} (𝒮ᵉ : span-type-familyᵉ l3ᵉ Aᵉ)
  where

  is-terminal-span-type-familyᵉ : UUωᵉ
  is-terminal-span-type-familyᵉ =
    {lᵉ : Level} (𝒯ᵉ : span-type-familyᵉ lᵉ Aᵉ) →
    is-contrᵉ (hom-span-type-familyᵉ 𝒯ᵉ 𝒮ᵉ)
```

## See also

-ᵉ [Theᵉ universalᵉ propertyᵉ ofᵉ dependentᵉ functionᵉ types](foundation.universal-property-dependent-function-types.mdᵉ)
  isᵉ equivalentᵉ to theᵉ conditionᵉ ofᵉ beingᵉ aᵉ terminalᵉ spanᵉ ofᵉ familiesᵉ ofᵉ types.ᵉ