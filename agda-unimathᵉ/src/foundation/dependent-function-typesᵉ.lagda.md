# Dependent function types

```agda
module foundation.dependent-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.spans-families-of-typesᵉ
open import foundation.terminal-spans-families-of-typesᵉ
open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.universal-property-dependent-function-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ familyᵉ `B`ᵉ ofᵉ typesᵉ overᵉ `A`.ᵉ Aᵉ {{#conceptᵉ "dependentᵉ function"ᵉ}}
thatᵉ takesᵉ elementsᵉ `xᵉ : A`ᵉ to elementsᵉ ofᵉ typeᵉ `Bᵉ x`ᵉ isᵉ anᵉ assignmentᵉ ofᵉ anᵉ
elementᵉ `fᵉ xᵉ : Bᵉ x`ᵉ forᵉ eachᵉ `xᵉ : A`.ᵉ Inᵉ Agda,ᵉ dependentᵉ functionsᵉ canᵉ beᵉ
writtenᵉ using `λ`-abstraction,ᵉ i.e.,ᵉ using theᵉ syntax

```text
  λ xᵉ → fᵉ x.ᵉ
```

Informally,ᵉ weᵉ alsoᵉ useᵉ theᵉ notationᵉ `xᵉ ↦ᵉ fᵉ x`ᵉ forᵉ theᵉ assignmentᵉ ofᵉ valuesᵉ ofᵉ aᵉ
dependentᵉ functionᵉ `f`.ᵉ

Theᵉ typeᵉ ofᵉ dependentᵉ functionᵉ `(xᵉ : Aᵉ) → Bᵉ x`ᵉ isᵉ builtᵉ in to theᵉ kernelᵉ ofᵉ
Agda,ᵉ andᵉ doesn'tᵉ needᵉ to beᵉ introducedᵉ byᵉ us.ᵉ Theᵉ purposeᵉ ofᵉ thisᵉ fileᵉ isᵉ to
record someᵉ propertiesᵉ ofᵉ dependentᵉ functionᵉ types.ᵉ

## Definitions

### The structure of a span on a family of types on a dependent function type

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  span-type-family-Πᵉ : span-type-familyᵉ (l1ᵉ ⊔ l2ᵉ) Bᵉ
  pr1ᵉ span-type-family-Πᵉ = (xᵉ : Aᵉ) → Bᵉ xᵉ
  pr2ᵉ span-type-family-Πᵉ xᵉ fᵉ = fᵉ xᵉ
```

## Properties

### Dependent function types satisfy the universal property of dependent function types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  abstract
    universal-property-dependent-function-types-Πᵉ :
      universal-property-dependent-function-typesᵉ (span-type-family-Πᵉ Bᵉ)
    universal-property-dependent-function-types-Πᵉ Tᵉ = is-equiv-swap-Πᵉ
```

### Dependent function types are terminal spans on families of types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  abstract
    is-terminal-span-type-family-Πᵉ :
      is-terminal-span-type-familyᵉ (span-type-family-Πᵉ Bᵉ)
    is-terminal-span-type-family-Πᵉ =
      is-terminal-universal-property-dependent-function-typesᵉ
        ( span-type-family-Πᵉ Bᵉ)
        ( universal-property-dependent-function-types-Πᵉ Bᵉ)
```