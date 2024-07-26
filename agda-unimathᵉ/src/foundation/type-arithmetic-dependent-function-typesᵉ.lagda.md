# Type arithmetic with dependent function types

```agda
module foundation.type-arithmetic-dependent-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.univalenceᵉ
```

</details>

## Properties

### Unit law when the base type is contractible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : is-contrᵉ Aᵉ) (aᵉ : Aᵉ)
  where

  left-unit-law-Π-is-contrᵉ : ((aᵉ : Aᵉ) → (Bᵉ aᵉ)) ≃ᵉ Bᵉ aᵉ
  left-unit-law-Π-is-contrᵉ =
    ( left-unit-law-Πᵉ ( λ _ → Bᵉ aᵉ)) ∘eᵉ
    ( equiv-Πᵉ
      ( λ _ → Bᵉ aᵉ)
      ( terminal-mapᵉ Aᵉ ,ᵉ is-equiv-terminal-map-is-contrᵉ Cᵉ)
      ( λ aᵉ → equiv-eqᵉ (apᵉ Bᵉ ( eq-is-contrᵉ Cᵉ))))
```

### The swap function `((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → Bᵉ → UUᵉ l3ᵉ}
  where

  swap-Πᵉ : ((xᵉ : Aᵉ) (yᵉ : Bᵉ) → Cᵉ xᵉ yᵉ) → ((yᵉ : Bᵉ) (xᵉ : Aᵉ) → Cᵉ xᵉ yᵉ)
  swap-Πᵉ fᵉ yᵉ xᵉ = fᵉ xᵉ yᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → Bᵉ → UUᵉ l3ᵉ}
  where

  is-equiv-swap-Πᵉ : is-equivᵉ (swap-Πᵉ {Cᵉ = Cᵉ})
  is-equiv-swap-Πᵉ = is-equiv-is-invertibleᵉ swap-Πᵉ refl-htpyᵉ refl-htpyᵉ

  equiv-swap-Πᵉ : ((xᵉ : Aᵉ) (yᵉ : Bᵉ) → Cᵉ xᵉ yᵉ) ≃ᵉ ((yᵉ : Bᵉ) (xᵉ : Aᵉ) → Cᵉ xᵉ yᵉ)
  pr1ᵉ equiv-swap-Πᵉ = swap-Πᵉ
  pr2ᵉ equiv-swap-Πᵉ = is-equiv-swap-Πᵉ
```

## See also

-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ functionᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ functionᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ cartesianᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ coproductᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ theᵉ unitᵉ typeᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ theᵉ emptyᵉ typeᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).ᵉ
-ᵉ Inᵉ
  [`foundation.universal-property-empty-type`](foundation.universal-property-empty-type.mdᵉ)
  weᵉ showᵉ thatᵉ `empty`ᵉ isᵉ theᵉ initialᵉ type,ᵉ whichᵉ canᵉ beᵉ consideredᵉ aᵉ _leftᵉ zeroᵉ
  lawᵉ forᵉ functionᵉ typesᵉ_ (`(emptyᵉ → Aᵉ) ≃ᵉ unit`).ᵉ
-ᵉ Thatᵉ `unit`ᵉ isᵉ theᵉ terminalᵉ typeᵉ isᵉ aᵉ corollaryᵉ ofᵉ `is-contr-Π`,ᵉ whichᵉ mayᵉ beᵉ
  foundᵉ in
  [`foundation-core.contractible-types`](foundation-core.contractible-types.md).ᵉ
  Thisᵉ canᵉ beᵉ consideredᵉ aᵉ _rightᵉ zeroᵉ lawᵉ forᵉ functionᵉ typesᵉ_
  (`(Aᵉ → unitᵉ) ≃ᵉ unit`).ᵉ